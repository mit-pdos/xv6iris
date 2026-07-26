(* ====================================================================== *)
(* DevModel.v                                                             *)
(*                                                                        *)
(* Memory-mapped devices: a 16550-style UART, a (S-context) PLIC, and a   *)
(* virtio-mmio block device (the latter modelled in VirtioModel.v, which   *)
(* this file re-exports and wires into the bus decode).                    *)
(*                                                                        *)
(* This file is the OPERATIONAL device model, imported by RiscvLang.v:    *)
(*                                                                        *)
(*   - [uart_state] / [plic_state] / [dev_state]: the device-fabric state, *)
(*     stored alongside the byte memory in [mstate]/[gstate].              *)
(*   - [dev_addr]: the bus address decode.  Every physical address BELOW   *)
(*     the DRAM bank (0x8000_0000) that reaches the interpreter's          *)
(*     MemRead/MemWrite outcomes is routed to the device fabric.  (The     *)
(*     CLINT/SIG/HTIF windows are dispatched INSIDE the Sail model --      *)
(*     [within_mmio_readable] -- and never reach the interpreter.)         *)
(*   - [dev_read] / [dev_write]: one MMIO transaction.  These are PURE     *)
(*     functions of the device state: an MMIO read is serviced directly    *)
(*     by the device (possibly changing it -- e.g. reading RHR pops the    *)
(*     receive FIFO), and an MMIO write is delivered to the device as an   *)
(*     individual transaction (nothing is buffered).  Unmodelled offsets   *)
(*     and access widths return None = the machine is STUCK, so a WP      *)
(*     certifies the kernel never performs such an access.                 *)
(*   - the AUTONOMOUS transitions ([uart_tx_pop], [uart_rx_push],          *)
(*     [plic_latch], [plic_eip], and the disk's [virtio_req_step]): the    *)
(*     devices also run CONCURRENTLY with the harts.  RiscvLang.v exposes  *)
(*     these as the step relation of a separate device execution context   *)
(*     (the [DevLoop] "thread"), interleaved with the CPU steps at         *)
(*     instruction granularity.  The disk is a BUS MASTER, so its step --  *)
(*     alone among these -- is a function of, and changes, the harts' byte *)
(*     memory; that is why [dev_step] carries it.                          *)
(*                                                                        *)
(* Like RiscvModelBytes.v, this file is deliberately iris-free.            *)
(* ====================================================================== *)

From stdpp Require Import gmap.
From stdpp Require Import bitvector.definitions.

Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Export VirtioModel.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 0. Platform geometry (matches the QEMU virt board / xv6 memlayout.h).   *)
(* ---------------------------------------------------------------------- *)

Definition uart_base : Z := 0x10000000.
Definition uart_size : Z := 8.
Definition plic_base : Z := 0xc000000.
Definition plic_size : Z := 0x400000.

(* The device fabric owns every bus address below the DRAM bank.  (RAM is
   [0x8000_0000, ..); RiscvPtsto.addr_is_ram implies [dev_addr a = false].) *)
Definition dev_bound : Z := 0x80000000.
Definition dev_addr (a : Arch.pa) : bool := uint a <? dev_bound.

(* The UART's interrupt source id at the PLIC (QEMU virt: 10). *)
Definition uart_irq_id : N := 10%N.

(* Number of harts the PLIC drives (must match RiscvLang.NCPU). *)
Definition dev_ncpu : nat := 8.

Lemma dev_addr_false (a : Arch.pa) : dev_bound <= uint a -> dev_addr a = false.
Proof. intros H. unfold dev_addr. apply Z.ltb_ge. exact H. Qed.

(* ---------------------------------------------------------------------- *)
(* 1. The UART: the 16550 subset xv6 uses.                                 *)
(*                                                                        *)
(*    Offsets: 0 RHR(r)/THR(w)/DLL(dlab), 1 IER/DLM(dlab), 2 ISR(r)/FCR(w),*)
(*    3 LCR, 5 LSR(r).  The FIFOs are modelled as byte lists; [u_out] is   *)
(*    the observable trace of bytes that have LEFT the UART on the wire    *)
(*    (what a spec about console output talks about).                      *)
(* ---------------------------------------------------------------------- *)

Record uart_state := UartState {
  u_rx  : list (bv 8);   (* receive FIFO; head = next byte RHR returns *)
  u_tx  : list (bv 8);   (* transmit FIFO; head = next byte to go on the wire *)
  u_out : list (bv 8);   (* bytes already transmitted (observable output trace) *)
  u_ier : bv 8;          (* interrupt enable: bit0 rx-avail, bit1 thr-empty *)
  u_lcr : bv 8;          (* line control; bit7 = DLAB (divisor-latch access) *)
  u_fcr : bv 8;          (* FIFO control (stored; bits 1/2 clear the FIFOs) *)
  u_dll : bv 8;          (* divisor latch low *)
  u_dlm : bv 8;          (* divisor latch high *)
}.

Definition uart_fifo_depth : nat := 16%nat.

Definition byte0 : bv 8 := Z_to_bv 8 0.

(* register fields *)
Definition uart_dlab (u : uart_state) : bool := Z.testbit (bv_unsigned (u_lcr u)) 7.
Definition uart_rx_ready (u : uart_state) : bool :=
  match u_rx u with [] => false | _ => true end.
(* transmit holding register / FIFO empty (LSR bit 5, and TEMT bit 6) *)
Definition uart_thre (u : uart_state) : bool :=
  match u_tx u with [] => true | _ => false end.

(* the two interrupt conditions, and the UART's (level) interrupt output *)
Definition uart_rx_int (u : uart_state) : bool :=
  Z.testbit (bv_unsigned (u_ier u)) 0 && uart_rx_ready u.
Definition uart_tx_int (u : uart_state) : bool :=
  Z.testbit (bv_unsigned (u_ier u)) 1 && uart_thre u.
Definition uart_irq (u : uart_state) : bool := uart_rx_int u || uart_tx_int u.

(* LSR: bit0 = data ready, bit5 = THR empty, bit6 = transmitter idle.
   We model bits 5 and 6 identically (FIFO empty). *)
Definition uart_lsr (u : uart_state) : bv 8 :=
  Z_to_bv 8 ((if uart_rx_ready u then 1 else 0)
             + (if uart_thre u then 0x60 else 0)).

(* ISR: bit0 = NO interrupt pending (inverted); bits 3:1 = id (rx-avail 0b010
   at bits 2:1 -> 0x04; THRE -> 0x02); bits 7:6 = FIFOs enabled.  NOTE: we
   model the THRE interrupt as a LEVEL (pending while the FIFO is empty and
   IER bit1 is set); the real 16550 latches it and clears it on an ISR read.
   The level model is simpler and only produces MORE interrupts, which a
   correct driver (xv6's uartintr) already tolerates. *)
Definition uart_isr (u : uart_state) : bv 8 :=
  Z_to_bv 8 (0xc0 + (if uart_rx_int u then 0x04
                     else if uart_tx_int u then 0x02
                     else 0x01)).

(* one MMIO read of byte register [off] (0..7): value + successor state *)
Definition uart_read (u : uart_state) (off : Z) : option (bv 8 * uart_state) :=
  if off =? 0 then
    if uart_dlab u then Some (u_dll u, u)
    else (* RHR: pop the receive FIFO (reads as 0 when empty) *)
      match u_rx u with
      | [] => Some (byte0, u)
      | b :: rx' =>
          Some (b, UartState rx' (u_tx u) (u_out u) (u_ier u) (u_lcr u)
                             (u_fcr u) (u_dll u) (u_dlm u))
      end
  else if off =? 1 then
    if uart_dlab u then Some (u_dlm u, u) else Some (u_ier u, u)
  else if off =? 2 then Some (uart_isr u, u)
  else if off =? 3 then Some (u_lcr u, u)
  else if off =? 5 then Some (uart_lsr u, u)
  else if (off =? 4) || (off =? 6) || (off =? 7) then Some (byte0, u)
  else None.

(* one MMIO write of byte register [off] *)
Definition uart_write (u : uart_state) (off : Z) (b : bv 8) : option uart_state :=
  if off =? 0 then
    if uart_dlab u then
      Some (UartState (u_rx u) (u_tx u) (u_out u) (u_ier u) (u_lcr u)
                      (u_fcr u) b (u_dlm u))
    else (* THR: push onto the transmit FIFO (dropped if full, as in hw) *)
      if (length (u_tx u) <? uart_fifo_depth)%nat then
        Some (UartState (u_rx u) (u_tx u ++ [b]) (u_out u) (u_ier u) (u_lcr u)
                        (u_fcr u) (u_dll u) (u_dlm u))
      else Some u
  else if off =? 1 then
    if uart_dlab u then
      Some (UartState (u_rx u) (u_tx u) (u_out u) (u_ier u) (u_lcr u)
                      (u_fcr u) (u_dll u) b)
    else
      Some (UartState (u_rx u) (u_tx u) (u_out u) b (u_lcr u)
                      (u_fcr u) (u_dll u) (u_dlm u))
  else if off =? 2 then
    (* FCR: bit1 clears the rx FIFO, bit2 clears the tx FIFO *)
    Some (UartState (if Z.testbit (bv_unsigned b) 1 then [] else u_rx u)
                    (if Z.testbit (bv_unsigned b) 2 then [] else u_tx u)
                    (u_out u) (u_ier u) (u_lcr u) b (u_dll u) (u_dlm u))
  else if off =? 3 then
    Some (UartState (u_rx u) (u_tx u) (u_out u) (u_ier u) b
                    (u_fcr u) (u_dll u) (u_dlm u))
  else if (off =? 4) || (off =? 5) || (off =? 6) || (off =? 7) then Some u
  else None.

(* Reading the LSR is a pure observation: it returns the status byte and does
   NOT advance the device (unlike RHR, which pops the rx FIFO). *)
Lemma uart_read_lsr (u : uart_state) : uart_read u 5 = Some (uart_lsr u, u).
Proof. reflexivity. Qed.

(* -- MMIO totality --

   Every offset xv6 can name is serviced: no UART access in [0, uart_size)
   ever gets stuck.  A driver proof running under a contents-agnostic
   invariant cannot supply a [uart_read]/[uart_write] equation as a premise
   (it does not know the state), so it needs these to conjure the result. *)

Lemma uart_read_total (u : uart_state) (off : Z) :
  0 <= off < uart_size -> exists b u', uart_read u off = Some (b, u').
Proof.
  unfold uart_read, uart_size. intro Hoff.
  destruct (off =? 0) eqn:E0.
  { destruct (uart_dlab u); [by do 2 eexists|].
    destruct (u_rx u); by do 2 eexists. }
  destruct (off =? 1) eqn:E1.
  { destruct (uart_dlab u); by do 2 eexists. }
  destruct (off =? 2) eqn:E2. { by do 2 eexists. }
  destruct (off =? 3) eqn:E3. { by do 2 eexists. }
  destruct (off =? 5) eqn:E5. { by do 2 eexists. }
  destruct ((off =? 4) || (off =? 6) || (off =? 7)) eqn:E4.
  { by do 2 eexists. }
  exfalso.
  apply Z.eqb_neq in E0, E1, E2, E3, E5.
  apply orb_false_elim in E4 as [E4 E7]. apply orb_false_elim in E4 as [E4 E6].
  apply Z.eqb_neq in E4, E6, E7. lia.
Qed.

Lemma uart_write_total (u : uart_state) (off : Z) (b : bv 8) :
  0 <= off < uart_size -> exists u', uart_write u off b = Some u'.
Proof.
  unfold uart_write, uart_size. intro Hoff.
  destruct (off =? 0) eqn:E0.
  { destruct (uart_dlab u); [by eexists|].
    destruct (length (u_tx u) <? uart_fifo_depth)%nat; by eexists. }
  destruct (off =? 1) eqn:E1.
  { destruct (uart_dlab u); by eexists. }
  destruct (off =? 2) eqn:E2. { by eexists. }
  destruct (off =? 3) eqn:E3. { by eexists. }
  destruct ((off =? 4) || (off =? 5) || (off =? 6) || (off =? 7)) eqn:E4.
  { by eexists. }
  exfalso.
  apply Z.eqb_neq in E0, E1, E2, E3.
  apply orb_false_elim in E4 as [E4 E7]. apply orb_false_elim in E4 as [E4 E6].
  apply orb_false_elim in E4 as [E4 E5].
  apply Z.eqb_neq in E4, E5, E6, E7. lia.
Qed.

(* -- the UART's autonomous transitions (the device "thread") -- *)

(* transmit: move the head of the tx FIFO onto the wire *)
Definition uart_tx_pop (u : uart_state) : option (bv 8 * uart_state) :=
  match u_tx u with
  | [] => None
  | b :: tx' =>
      Some (b, UartState (u_rx u) tx' (u_out u ++ [b]) (u_ier u) (u_lcr u)
                         (u_fcr u) (u_dll u) (u_dlm u))
  end.

(* receive: a byte arrives from the outside world (refused when full) *)
Definition uart_rx_push (u : uart_state) (b : bv 8) : option uart_state :=
  if (length (u_rx u) <? uart_fifo_depth)%nat then
    Some (UartState (u_rx u ++ [b]) (u_tx u) (u_out u) (u_ier u) (u_lcr u)
                    (u_fcr u) (u_dll u) (u_dlm u))
  else None.

(* -- the accepted-byte trace -- *)

(* [uart_acc u] is every byte the UART has ACCEPTED for transmission: those
   already on the wire ([u_out]) followed by those still queued ([u_tx]).  It
   is the right notion for a driver's postcondition, because a driver returns
   as soon as its byte is in the tx FIFO -- the move to [u_out] is the device
   thread's own later step, so [u_out] alone is not yet observable at a
   driver's return, while [uart_acc] already is.

   The point of the concatenation is that it is STABLE under the device's
   autonomous drain: [uart_tx_pop] moves one byte from the head of [u_tx] to
   the tail of [u_out], which reassociates to the very same list.  So a CPU
   pushing to THR is the only transition that grows it (see
   [uart_write_thr_acc]), and a ghost lower bound on it is preserved by every
   device step. *)
Definition uart_acc (u : uart_state) : list (bv 8) := u_out u ++ u_tx u.

(* the drain step leaves the accepted trace completely unchanged *)
Lemma uart_tx_pop_acc (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_tx_pop u = Some (b, u') -> uart_acc u' = uart_acc u.
Proof.
  unfold uart_tx_pop, uart_acc. destruct (u_tx u) as [| b0 tx'] eqn:Htx.
  - discriminate.
  - intro H. injection H as <- <-. cbn [u_out u_tx].
    rewrite <- app_assoc. reflexivity.
Qed.

(* a byte arriving on the rx side touches neither [u_out] nor [u_tx] *)
Lemma uart_rx_push_acc (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_rx_push u b = Some u' -> uart_acc u' = uart_acc u.
Proof.
  unfold uart_rx_push, uart_acc.
  destruct (length (u_rx u) <? uart_fifo_depth)%nat; [| discriminate].
  intro H. injection H as <-. reflexivity.
Qed.

(* A THR write appends the byte to the accepted trace -- but ONLY with DLAB
   clear (else offset 0 is the divisor latch, not THR) and only with room in
   the FIFO (the model drops the byte when full, exactly as the hardware
   does).  Both premises are genuinely needed: neither is derivable from a
   contents-agnostic view of the device. *)
Lemma uart_write_thr_acc (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_dlab u = false ->
  (length (u_tx u) < uart_fifo_depth)%nat ->
  uart_write u 0 b = Some u' ->
  uart_acc u' = uart_acc u ++ [b].
Proof.
  intros Hdlab Hroom. unfold uart_write, uart_acc. cbn [Z.eqb].
  rewrite Hdlab.
  rewrite (proj2 (Nat.ltb_lt _ _) Hroom).
  intro H. injection H as <-. cbn [u_out u_tx]. rewrite app_assoc. reflexivity.
Qed.

(* Writes to IER/LCR and to the read-only/ignored offsets leave the accepted
   trace alone. *)
(* NOTE (deliberate, load-bearing): there is NO general monotonicity lemma for
   [uart_write].  An FCR write (offset 2) with bit 2 set CLEARS the tx FIFO,
   which SHRINKS [uart_acc] -- the queued bytes are discarded, never sent.  So
   any invariant holding a monotone [uart_acc] ghost forbids that write: code
   doing a FIFO-clearing FCR write cannot be verified while such an invariant
   is in force, and must run before it is allocated.  xv6's [uart_init] does
   exactly this write (FCR_FIFO_CLEAR = bits 1|2). *)

(* -- the transmitted prefix [u_out] -- *)

(* [u_out] is append-only: the drain step is the ONLY transition that touches
   it, and it only ever appends.  This is what lets an observation of "the tx
   FIFO is empty" survive later device steps: see [uart_tx_still_empty]. *)
Lemma uart_tx_pop_out (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_tx_pop u = Some (b, u') -> u_out u' = u_out u ++ [b].
Proof.
  unfold uart_tx_pop. destruct (u_tx u) as [| b0 tx'] eqn:Htx; [discriminate|].
  intro H. injection H as <- <-. reflexivity.
Qed.

Lemma uart_rx_push_out (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_rx_push u b = Some u' -> u_out u' = u_out u.
Proof.
  unfold uart_rx_push.
  destruct (length (u_rx u) <? uart_fifo_depth)%nat; [| discriminate].
  intro H. injection H as <-. reflexivity.
Qed.

(* no MMIO access transmits anything: every [uart_write] branch, and every
   [uart_read] branch, carries [u_out] through untouched *)
Lemma uart_write_out (u : uart_state) (off : Z) (b : bv 8) (u' : uart_state) :
  uart_write u off b = Some u' -> u_out u' = u_out u.
Proof.
  unfold uart_write.
  destruct (off =? 0).
  { destruct (uart_dlab u).
    - intro H; injection H as <-; reflexivity.
    - destruct (length (u_tx u) <? uart_fifo_depth)%nat;
        intro H; injection H as <-; reflexivity. }
  destruct (off =? 1).
  { destruct (uart_dlab u); intro H; injection H as <-; reflexivity. }
  destruct (off =? 2). { intro H; injection H as <-; reflexivity. }
  destruct (off =? 3). { intro H; injection H as <-; reflexivity. }
  destruct ((off =? 4) || (off =? 5) || (off =? 6) || (off =? 7)).
  { intro H; injection H as <-; reflexivity. }
  discriminate.
Qed.

(* -- DLAB (LCR bit 7) -- *)

(* No autonomous device transition touches the line control register, so DLAB
   is stable across every device step: only a CPU write to offset 3 can change
   it. *)
Lemma uart_tx_pop_dlab (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_tx_pop u = Some (b, u') -> uart_dlab u' = uart_dlab u.
Proof.
  unfold uart_tx_pop. destruct (u_tx u) as [| b0 tx'] eqn:Htx; [discriminate|].
  intro H. injection H as <- <-. reflexivity.
Qed.

Lemma uart_rx_push_dlab (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_rx_push u b = Some u' -> uart_dlab u' = uart_dlab u.
Proof.
  unfold uart_rx_push.
  destruct (length (u_rx u) <? uart_fifo_depth)%nat; [| discriminate].
  intro H. injection H as <-. reflexivity.
Qed.

(* Only a write to offset 3 (LCR) can change DLAB; in particular a THR write
   cannot, so DLAB stays frozen across a driver's data writes. *)
Lemma uart_write_lcr_0 (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_write u 0 b = Some u' -> u_lcr u' = u_lcr u.
Proof.
  unfold uart_write. cbn [Z.eqb].
  destruct (uart_dlab u).
  - intro H; injection H as <-; reflexivity.
  - destruct (length (u_tx u) <? uart_fifo_depth)%nat;
      intro H; injection H as <-; reflexivity.
Qed.

Lemma uart_write_dlab_0 (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_write u 0 b = Some u' -> uart_dlab u' = uart_dlab u.
Proof.
  intro H. unfold uart_dlab. by rewrite (uart_write_lcr_0 _ _ _ H).
Qed.

(* -- exclusive-transmitter reasoning -- *)

(* THE KEY STABILITY FACT.  Suppose at the THRE poll the FIFO was empty (so
   the accepted trace [l] had all been transmitted), and suppose that at some
   later point the accepted trace is STILL [l] -- which is exactly what an
   exclusive transmitter owner knows, since only a THR write grows it and only
   the owner may perform one.  Then the FIFO is still empty at that later
   point: the device can only have moved bytes from [u_tx] to [u_out], and
   [u_out] has already reached [l], so there is nothing left to move.

   This is what makes "polled THRE, therefore the write will not be dropped"
   sound in the presence of a concurrently draining device and other harts. *)

(* The same conclusion phrased at ONE state: if the accepted trace is [l] and
   [l] has already all been transmitted, the FIFO is empty.  This is the form a
   THR write uses -- it needs no witness of an earlier polled state, only what
   the transmitter token ([uart_acc u = l]) and the carried [uart_out_lb l]
   ([l `prefix_of` u_out u]) give at the write's OWN state. *)
Lemma uart_tx_empty_of_out (u : uart_state) (l : list (bv 8)) :
  uart_acc u = l -> l `prefix_of` u_out u -> u_tx u = [].
Proof.
  unfold uart_acc. intros Hacc [k Hk].
  assert (Hlen : (length (u_out u) + length (u_tx u) = length l)%nat).
  { rewrite <- length_app, Hacc. reflexivity. }
  rewrite Hk in Hlen. rewrite length_app in Hlen.
  assert (Htx : length (u_tx u) = 0%nat) by lia.
  by apply nil_length_inv.
Qed.

(* ---------------------------------------------------------------------- *)
(* 2. The PLIC: S-mode contexts only (context 2h+1 of hart h, as xv6 uses). *)
(*    Sources 1..31 (one 32-bit enable word); the UART is source 10.       *)
(* ---------------------------------------------------------------------- *)

Record plic_state := PlicState {
  p_prio    : N -> bv 32;    (* per-source priority (0 = never interrupts) *)
  p_pending : N -> bool;     (* gateway has forwarded a request *)
  p_claimed : N -> bool;     (* claimed (in service), completion pending *)
  p_enable  : nat -> bv 32;  (* per-hart S-context enable bits, sources 0..31 *)
  p_thresh  : nat -> bv 32;  (* per-hart S-context priority threshold *)
}.

Definition plic_nsrc : nat := 32%nat.

(* the second interrupt source this machine has (the virtio disk); the UART is
   [uart_irq_id] = 10.  Which device sits on which PLIC source is a property of
   the machine, hence here; what the KERNEL intends to do with those sources
   lives in the software layer (PlicPlan.v). *)
Definition virtio_irq_id : N := 1%N.   (* VIRTIO0_IRQ *)

(* pointwise function updates *)
Definition nupd {A} (f : N -> A) (i : N) (x : A) : N -> A :=
  fun j => if N.eqb j i then x else f j.
Definition hupd {A} (f : nat -> A) (h : nat) (x : A) : nat -> A :=
  fun k => if Nat.eqb k h then x else f k.

Definition plic_enabled (p : plic_state) (h : nat) (i : N) : bool :=
  Z.testbit (bv_unsigned (p_enable p h)) (Z.of_N i).

(* is source [i] eligible to be claimed by hart [h]'s S context? *)
Definition plic_cand (p : plic_state) (h : nat) (i : N) : bool :=
  p_pending p i && plic_enabled p h i && (0 <? bv_unsigned (p_prio p i)).

(* strictly better: higher priority, ties broken toward the lower id *)
Definition plic_better (p : plic_state) (i j : N) : bool :=
  (bv_unsigned (p_prio p j) <? bv_unsigned (p_prio p i))
  || ((bv_unsigned (p_prio p i) =? bv_unsigned (p_prio p j)) && (i <? j)%N).

Definition plic_srcs : list N := map N.of_nat (seq 1 (plic_nsrc - 1)).

Definition plic_best (p : plic_state) (h : nat) : option N :=
  fold_left (fun best i =>
               if plic_cand p h i then
                 match best with
                 | None => Some i
                 | Some j => if plic_better p i j then Some i else Some j
                 end
               else best)
            plic_srcs None.

(* claim: return (and clear pending on, mark claimed) the best source; 0 if none *)
Definition plic_claim (p : plic_state) (h : nat) : bv 32 * plic_state :=
  match plic_best p h with
  | None => (Z_to_bv 32 0, p)
  | Some i =>
      (Z_to_bv 32 (Z.of_N i),
       PlicState (p_prio p) (nupd (p_pending p) i false) (nupd (p_claimed p) i true)
                 (p_enable p) (p_thresh p))
  end.

(* complete: the context writes back the source id it finished serving *)
Definition plic_complete (p : plic_state) (i : N) : plic_state :=
  if (1 <=? Z.of_N i) && (Z.of_N i <? Z.of_nat plic_nsrc) then
    PlicState (p_prio p) (p_pending p) (nupd (p_claimed p) i false)
              (p_enable p) (p_thresh p)
  else p.

(* the external-interrupt-pending level the PLIC drives into hart [h]'s
   S context: some pending, enabled source exceeds the context threshold *)
Definition plic_eip (p : plic_state) (h : nat) : bool :=
  existsb (fun i => plic_cand p h i
                    && (bv_unsigned (p_thresh p h) <? bv_unsigned (p_prio p i)))
          plic_srcs.

(* the pending bitmap word 0 (sources 0..31), for reads of offset 0x1000 *)
Definition plic_pending_word (p : plic_state) : bv 32 :=
  Z_to_bv 32 (fold_right (fun i acc =>
                            if p_pending p (N.of_nat i)
                            then Z.lor (Z.shiftl 1 (Z.of_nat i)) acc else acc)
                         0 (seq 0 plic_nsrc)).

(* -- PLIC MMIO decode: 32-bit registers at [off] within the PLIC window -- *)

(* context sub-decodes; [None] = not that register family *)
Definition plic_senable_hart (off : Z) : option nat :=
  if (0x2080 <=? off) && ((off - 0x2080) mod 0x100 =? 0)
     && ((off - 0x2080) / 0x100 <? Z.of_nat dev_ncpu)
  then Some (Z.to_nat ((off - 0x2080) / 0x100)) else None.
Definition plic_sthresh_hart (off : Z) : option nat :=
  if (0x201000 <=? off) && ((off - 0x201000) mod 0x2000 =? 0)
     && ((off - 0x201000) / 0x2000 <? Z.of_nat dev_ncpu)
  then Some (Z.to_nat ((off - 0x201000) / 0x2000)) else None.
Definition plic_sclaim_hart (off : Z) : option nat :=
  if (0x201004 <=? off) && ((off - 0x201004) mod 0x2000 =? 0)
     && ((off - 0x201004) / 0x2000 <? Z.of_nat dev_ncpu)
  then Some (Z.to_nat ((off - 0x201004) / 0x2000)) else None.

Definition plic_read (p : plic_state) (off : Z) : option (bv 32 * plic_state) :=
  if (0 <? off) && (off <? 4 * Z.of_nat plic_nsrc) && (off mod 4 =? 0) then
    Some (p_prio p (Z.to_N (off / 4)), p)          (* source priorities *)
  else if off =? 0x1000 then Some (plic_pending_word p, p)
  else match plic_senable_hart off with
  | Some h => Some (p_enable p h, p)
  | None =>
    match plic_sthresh_hart off with
    | Some h => Some (p_thresh p h, p)
    | None =>
      match plic_sclaim_hart off with
      | Some h => Some (plic_claim p h)             (* claim: side effect *)
      | None => None
      end
    end
  end.

Definition plic_write (p : plic_state) (off : Z) (v : bv 32) : option plic_state :=
  if (0 <? off) && (off <? 4 * Z.of_nat plic_nsrc) && (off mod 4 =? 0) then
    Some (PlicState (nupd (p_prio p) (Z.to_N (off / 4)) v) (p_pending p)
                    (p_claimed p) (p_enable p) (p_thresh p))
  else match plic_senable_hart off with
  | Some h => Some (PlicState (p_prio p) (p_pending p) (p_claimed p)
                              (hupd (p_enable p) h v) (p_thresh p))
  | None =>
    match plic_sthresh_hart off with
    | Some h => Some (PlicState (p_prio p) (p_pending p) (p_claimed p)
                                (p_enable p) (hupd (p_thresh p) h v))
    | None =>
      match plic_sclaim_hart off with
      | Some _ => Some (plic_complete p (Z.to_N (bv_unsigned v)))
      | None => None
      end
    end
  end.

(* gateway: latch source [i]'s level output into its pending bit.  A level
   source is forwarded only when it is neither already pending nor claimed.
   The source is a PARAMETER: this machine has two of them (the UART and the
   virtio disk), and the gateway treats them identically -- which device
   drives which line is [dev_irq_level]'s business, in §3. *)
Definition plic_latch (p : plic_state) (i : N) : option plic_state :=
  if negb (p_pending p i) && negb (p_claimed p i) then
    Some (PlicState (p_prio p) (nupd (p_pending p) i true)
                    (p_claimed p) (p_enable p) (p_thresh p))
  else None.

(* ---------------------------------------------------------------------- *)
(* 3. The device fabric: one MMIO transaction, routed by address.           *)
(* ---------------------------------------------------------------------- *)

Record dev_state := DevState {
  duart : uart_state;
  dplic : plic_state;
  dvirtio : virtio_state;
}.

Definition set_duart (d : dev_state) (u : uart_state) : dev_state :=
  DevState u (dplic d) (dvirtio d).
Definition set_dplic (d : dev_state) (p : plic_state) : dev_state :=
  DevState (duart d) p (dvirtio d).
Definition set_dvirtio (d : dev_state) (v : virtio_state) : dev_state :=
  DevState (duart d) (dplic d) v.

Definition in_uart (a : Z) : bool := (uart_base <=? a) && (a <? uart_base + uart_size).
Definition in_plic (a : Z) : bool := (plic_base <=? a) && (a <? plic_base + plic_size).
Definition in_virtio (a : Z) : bool :=
  (virtio_base <=? a) && (a <? virtio_base + virtio_size).

(* The interrupt LEVEL each of this machine's two sources is driving.  The
   gateway ([plic_latch]) forwards exactly these; every other PLIC source id
   is permanently low, because nothing is wired to it. *)
Definition dev_irq_level (d : dev_state) (i : N) : bool :=
  if (i =? uart_irq_id)%N then uart_irq (duart d)
  else if (i =? virtio_irq_id)%N then virtio_irq (dvirtio d)
  else false.

(* An MMIO READ transaction: [n]-byte read at physical address [pa].
   Serviced directly by the device; the UART decodes 1-byte accesses, the
   PLIC 4-byte accesses.  Any other width/offset is STUCK (None). *)
Definition dev_read (d : dev_state) (pa : Arch.pa) (n : N)
  : option (bv (8 * n) * dev_state) :=
  let a := uint pa in
  if in_uart a then
    match n return option (bv (8 * n) * dev_state) with
    | 1%N => match uart_read (duart d) (a - uart_base) with
             | Some (b, u') => Some (b, set_duart d u')
             | None => None
             end
    | _ => None
    end
  else if in_plic a then
    match n return option (bv (8 * n) * dev_state) with
    | 4%N => match plic_read (dplic d) (a - plic_base) with
             | Some (w, p') => Some (w, set_dplic d p')
             | None => None
             end
    | _ => None
    end
  else if in_virtio a then
    (* virtio-mmio registers are all 32 bits wide, and none of them is
       read-sensitive: the device is left alone by a read. *)
    match n return option (bv (8 * n) * dev_state) with
    | 4%N => match virtio_read (dvirtio d) (a - virtio_base) with
             | Some w => Some (w, d)
             | None => None
             end
    | _ => None
    end
  else None.

(* An MMIO WRITE transaction: writes are sent to the device individually
   (they do not accumulate in any cache) and take effect immediately. *)
Definition dev_write (d : dev_state) (pa : Arch.pa) (n : N) (v : bv (8 * n))
  : option dev_state :=
  let a := uint pa in
  if in_uart a then
    match n return bv (8 * n) -> option dev_state with
    | 1%N => fun v => match uart_write (duart d) (a - uart_base) v with
                      | Some u' => Some (set_duart d u')
                      | None => None
                      end
    | _ => fun _ => None
    end v
  else if in_plic a then
    match n return bv (8 * n) -> option dev_state with
    | 4%N => fun v => match plic_write (dplic d) (a - plic_base) v with
                      | Some p' => Some (set_dplic d p')
                      | None => None
                      end
    | _ => fun _ => None
    end v
  else if in_virtio a then
    match n return bv (8 * n) -> option dev_state with
    | 4%N => fun v => match virtio_write (dvirtio d) (a - virtio_base) v with
                      | Some vd' => Some (set_dvirtio d vd')
                      | None => None
                      end
    | _ => fun _ => None
    end v
  else None.

(* the level the PLIC drives on hart [h]'s S-mode external interrupt pin *)
Definition dev_seip (d : dev_state) (h : nat) : bool := plic_eip (dplic d) h.

(* ---------------------------------------------------------------------- *)
(* 4. Power-on state: FIFOs empty, everything masked/zero.                  *)
(* ---------------------------------------------------------------------- *)

Definition uart0_state : uart_state :=
  UartState [] [] [] byte0 byte0 byte0 byte0 byte0.
Definition plic0_state : plic_state :=
  PlicState (fun _ => Z_to_bv 32 0) (fun _ => false) (fun _ => false)
            (fun _ => Z_to_bv 32 0) (fun _ => Z_to_bv 32 0).
Definition dev0_state : dev_state :=
  DevState uart0_state plic0_state virtio0_state.
