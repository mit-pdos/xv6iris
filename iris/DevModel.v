(* ====================================================================== *)
(* DevModel.v                                                             *)
(*                                                                        *)
(* Memory-mapped devices: TWO 16550-style UARTs, a (S-context) PLIC and a *)
(* virtio-mmio block device (the latter modelled in VirtioModel.v, which   *)
(* this file re-exports and wires into the bus decode).                    *)
(*                                                                        *)
(* This file is the OPERATIONAL device model, imported by RiscvLang.v:    *)
(*                                                                        *)
(*   - [uart_state] / [plic_state] / [dev_state]: the device-fabric state, *)
(*     stored alongside the byte memory in [mstate]/[gstate].  The board   *)
(*     has TWO 16550s, so everything about a UART is indexed by [uart_id]  *)
(*     -- the window, the PLIC source, and [dev_state]'s [duart] field,    *)
(*     which is a FUNCTION of the port.                                    *)
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
(*     [plic_latch], [plic_eip], and the disk's per-transaction steps of   *)
(*     VirtioModel section 6): the                                         *)
(*     devices also run CONCURRENTLY with the harts.  RiscvLang.v exposes  *)
(*     these as the step relations of separate device execution contexts   *)
(*     ([UartLoop i]/[DiskLoop]/[PlicLoop] -- ONE THREAD PER DEVICE, so    *)
(*     two UART threads here, each latching its own interrupt source),     *)
(*     interleaved with                                                    *)
(*     the CPU steps at instruction granularity.  The disk is a BUS        *)
(*     MASTER, so its step -- alone among these -- is a function of, and   *)
(*     changes, the harts' byte memory; that is why [disk_step] carries it.*)
(*                                                                        *)
(* Like RiscvModelBytes.v, this file is deliberately iris-free.            *)
(* ====================================================================== *)

From stdpp Require Import gmap finite.
From stdpp Require Import bitvector.definitions.

Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Export VirtioModel.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* 0. Platform geometry (matches the QEMU virt board / xv6 memlayout.h).   *)
(* ---------------------------------------------------------------------- *)

(* THE BOARD HAS TWO 16550 PORTS, and everything about a UART below is
   INDEXED BY WHICH.  [Uart0] is the one at 0x1000_0000 that every board
   profile has; [Uart1] is the second port the QEMU virt machine
   instantiates at 0x1000_a000 when a second serial backend is attached
   (`qemu-system-riscv64 -machine virt ... -serial <a> -serial <b>`;
   tools/vtest/vtest.py's `uarts=2` knob).  The two ports are IDENTICAL
   CHIPS -- the same [uart_state], the same [uart_read]/[uart_write], the
   same autonomous transitions -- and differ only in the two board facts
   below, the window they answer and the PLIC source they drive.  So
   nothing about the 16550 is written twice: the index is a parameter of
   the fabric, never of the chip.

   WHICH PORT PLAYS WHICH ROLE IS NOT THE MODEL'S BUSINESS.  The kernel
   decides that (the console on one, its own diagnostics on the other),
   and a theorem about "the console's wire" names the port it means. *)
Inductive uart_id := Uart0 | Uart1.

Global Instance uart_id_eq_dec : EqDecision uart_id.
Proof. solve_decision. Defined.
Global Instance uart_id_countable : Countable uart_id.
Proof.
  refine (inj_countable' (fun i => match i with Uart0 => 0 | Uart1 => 1 end)
                         (fun n => match n with 0 => Uart0 | _ => Uart1 end) _).
  by intros [].
Qed.
Global Program Instance uart_id_finite : Finite uart_id :=
  {| enum := [Uart0; Uart1] |}.
Next Obligation. repeat constructor; set_solver. Qed.
Next Obligation. intros []; set_solver. Qed.

(* THE BOARD FACTS, and the only two there are.  A window is [uart_size]
   bytes wide at [uart_base i]; the port raises PLIC source [uart_irq_id i].
   QEMU virt: 0x1000_0000 / source 10 and 0x1000_a000 / source 12 -- read
   off the machine's own device tree (`serial@10000000 interrupts <0xa>`,
   `serial@1000a000 interrupts <0xc>`). *)
Definition uart_base (i : uart_id) : Z :=
  match i with Uart0 => 0x10000000 | Uart1 => 0x1000a000 end.
Definition uart_size : Z := 8.
Definition plic_base : Z := 0xc000000.
Definition plic_size : Z := 0x400000.

(* The device fabric owns every bus address below the DRAM bank.  (RAM is
   [0x8000_0000, ..); RiscvPtsto.addr_is_ram implies [dev_addr a = false].) *)
Definition dev_bound : Z := 0x80000000.
Definition dev_addr (a : Arch.pa) : bool := uint a <? dev_bound.

Definition uart_irq_id (i : uart_id) : N :=
  match i with Uart0 => 10%N | Uart1 => 12%N end.

(* ...and the INVERSE, which is what the PLIC gateway needs: a source id
   names at most one port.  Stated as the decode rather than derived from
   [uart_irq_id] by search, so that [dev_irq_level] reduces on a literal. *)
Definition uart_of_irq (k : N) : option uart_id :=
  if (k =? uart_irq_id Uart0)%N then Some Uart0
  else if (k =? uart_irq_id Uart1)%N then Some Uart1
  else None.

Lemma uart_of_irq_id (i : uart_id) : uart_of_irq (uart_irq_id i) = Some i.
Proof. by destruct i. Qed.

(* ...and its converse: a source id the decode accepts really is that
   port's.  What a dispatcher on [uart_of_irq] needs to get back to the
   source the caller named. *)
Lemma uart_of_irq_eq (k : N) (i : uart_id) :
  uart_of_irq k = Some i -> k = uart_irq_id i.
Proof.
  unfold uart_of_irq.
  destruct ((k =? uart_irq_id Uart0)%N) eqn:E0.
  { intros [= <-]. by apply N.eqb_eq in E0. }
  destruct ((k =? uart_irq_id Uart1)%N) eqn:E1.
  { intros [= <-]. by apply N.eqb_eq in E1. }
  intros H. discriminate H.
Qed.

Lemma uart_irq_id_inj (i j : uart_id) : uart_irq_id i = uart_irq_id j -> i = j.
Proof. destruct i, j; by cbn. Qed.

(* Number of harts the PLIC drives (must match RiscvLang.NCPU). *)
Definition dev_ncpu : nat := 8.

Lemma dev_addr_false (a : Arch.pa) : dev_bound <= uint a -> dev_addr a = false.
Proof. intros H. unfold dev_addr. apply Z.ltb_ge. exact H. Qed.

(* ---------------------------------------------------------------------- *)
(* 1. The UART: a 16550, as the board this development runs on has one.    *)
(*                                                                        *)
(*    Offsets: 0 RHR(r)/THR(w)/DLL(dlab), 1 IER/DLM(dlab), 2 ISR(r)/FCR(w),*)
(*    3 LCR, 4 MCR, 5 LSR(r), 6 MSR(r), 7 SCR.  The FIFOs are byte lists;  *)
(*    [u_wire] is the trace of bytes that have actually left the chip on   *)
(*    SOUT -- what a spec about console output talks about -- and [u_out]  *)
(*    the trace that has left the TRANSMITTER, which is the same thing     *)
(*    except in loopback mode (see [uart_tx_pop]).                         *)
(*                                                                        *)
(*    ALL EIGHT REGISTERS ARE REAL, and five FINDINGS of the conformance    *)
(*    suite (tools/vtest) are why -- it put the model beside the machine:   *)
(*    MCR, MSR and SCR used to read as zero and swallow their writes       *)
(*    (finding 6), the ISR claimed the FIFOs were enabled before anyone    *)
(*    had enabled them (finding 7) and reported the transmit interrupt as  *)
(*    a LEVEL that a read could not acknowledge (finding 8), and RHR       *)
(*    answered 0 on an empty receive FIFO where the receive holding        *)
(*    register still holds the last byte (finding 23).  Each of those is a *)
(*    driver the development could not describe: the standard 16550        *)
(*    PRESENCE TEST is a write to the scratch register and a read-back,    *)
(*    the standard SELF TEST is MCR's loopback bit, and a driver that      *)
(*    acknowledges its transmit interrupt by reading the ISR -- rather     *)
(*    than by feeding the transmitter -- livelocked against the level.     *)
(* ---------------------------------------------------------------------- *)

Record uart_state := UartState {
  u_rx   : list (bv 8);  (* receive FIFO; head = next byte RHR returns *)
  u_tx   : list (bv 8);  (* transmit FIFO; head = next byte to go out *)
  u_out  : list (bv 8);  (* bytes the TRANSMITTER has finished with *)
  u_wire : list (bv 8);  (* ...of those, the ones that left on SOUT *)
  u_ier  : bv 8;         (* interrupt enable: bit0 rx-avail, bit1 thr-empty *)
  u_lcr  : bv 8;         (* line control; bit7 = DLAB (divisor-latch access) *)
  u_fcr  : bv 8;         (* FIFO control; bit0 enables, bits 1/2 clear *)
  u_dll  : bv 8;         (* divisor latch low *)
  u_dlm  : bv 8;         (* divisor latch high *)
  u_mcr  : bv 8;         (* modem control (bits 4:0); bit4 = LOOP *)
  u_scr  : bv 8;         (* scratch: a byte of storage with no semantics *)
  u_rbr  : bv 8;         (* receive holding register: the last byte in *)
  u_thri : bool;         (* the transmit interrupt LATCH *)
}.

(* The FIFOs are 16 deep, which is what FCR bit 0 switches ON; with the FIFOs
   disabled a real 16550 has a one-byte holding register at each end.  The
   model keeps the 16-deep lists in both modes and lets FCR bit 0 decide only
   what the ISR reports (bits 7:6), what an FCR write flushes, and what a read
   of an empty RHR answers.  The difference is invisible to a driver that
   polls, xv6 enables the FIFOs in [uartinit] before anything is transmitted,
   and the direction is the safe one: the model ACCEPTS more host input than
   the hardware does, never less. *)
Definition uart_fifo_depth : nat := 16%nat.

Definition byte0 : bv 8 := Z_to_bv 8 0.

(* -- register fields -- *)

Definition uart_dlab (u : uart_state) : bool := Z.testbit (bv_unsigned (u_lcr u)) 7.

(* FCR bit 0: the FIFOs are enabled.  Read by the ISR's bits 7:6, by the
   flush-on-toggle rule in [uart_write], and by RHR on an empty FIFO. *)
Definition uart_fifo_en (u : uart_state) : bool :=
  Z.testbit (bv_unsigned (u_fcr u)) 0.

(* MCR bit 4: LOCAL LOOPBACK.  The transmitter's output is disconnected from
   SOUT and wired to this UART's own receiver instead, and the four modem
   OUTPUTS are wired to the four modem INPUTS ([uart_msr]).  This is the
   standard way to self-test a 16550, and the only way to exercise the
   receive path on a port nobody is typing at. *)
Definition uart_loopback (u : uart_state) : bool :=
  Z.testbit (bv_unsigned (u_mcr u)) 4.

Definition uart_rx_ready (u : uart_state) : bool :=
  match u_rx u with [] => false | _ => true end.
(* transmit holding register / FIFO empty (LSR bit 5, and TEMT bit 6) *)
Definition uart_thre (u : uart_state) : bool :=
  match u_tx u with [] => true | _ => false end.

(* The two interrupt conditions, and the UART's (level) interrupt output.

   RECEIVE is a LEVEL: data ready, and IER bit 0.  (A real 16550 with the
   FIFOs on compares the queue length against FCR's trigger level and adds a
   character-TIMEOUT interrupt for a queue that never reaches it.  The model
   triggers at one byte, which IS the trigger level xv6 and every conformance
   test select -- FCR bits 7:6 clear -- and which everywhere else errs toward
   more interrupts, never fewer.)

   TRANSMIT is a LATCH, [u_thri].  It is SET when the transmitter falls idle
   -- the last queued byte leaves, or an FCR write clears the FIFO -- and
   when IER bit 1 is written while it is already idle, since there is no
   later edge to arm it then.  It is CLEARED by a THR write (the transmitter
   is busy again) and by the ISR read that REPORTS it, which is the 16550's
   acknowledgement.  It used to be the level [uart_thre] here, and that is
   finding 8: two ISR reads in a row both answered "THRE pending" where the
   machine's second read says the interrupt is gone, so a driver that
   acknowledges by reading the ISR could not be verified against the model. *)
Definition uart_rx_int (u : uart_state) : bool :=
  Z.testbit (bv_unsigned (u_ier u)) 0 && uart_rx_ready u.
Definition uart_tx_int (u : uart_state) : bool :=
  Z.testbit (bv_unsigned (u_ier u)) 1 && u_thri u.
Definition uart_irq (u : uart_state) : bool := uart_rx_int u || uart_tx_int u.

(* LSR: bit0 = data ready, bit5 = THR empty, bit6 = transmitter idle.
   We model bits 5 and 6 identically (FIFO empty). *)
Definition uart_lsr (u : uart_state) : bv 8 :=
  Z_to_bv 8 ((if uart_rx_ready u then 1 else 0)
             + (if uart_thre u then 0x60 else 0)).

(* ISR: bit0 = NO interrupt pending (inverted); bits 3:1 = the id of the
   highest-priority pending interrupt (receive 0b010 at bits 2:1 -> 0x04,
   THRE -> 0x02); bits 7:6 = the FIFOs are enabled, which is FCR bit 0 --
   and not, as it used to be here, a constant (finding 7). *)
Definition uart_isr (u : uart_state) : bv 8 :=
  Z_to_bv 8 ((if uart_fifo_en u then 0xc0 else 0)
             + (if uart_rx_int u then 0x04
                else if uart_tx_int u then 0x02
                else 0x01)).

(* ...and THIS is the read that acknowledges the transmit interrupt: the one
   whose reported id is THRE, i.e. nothing of higher priority is pending. *)
Definition uart_isr_thri (u : uart_state) : bool :=
  negb (uart_rx_int u) && uart_tx_int u.

(* MSR: the four modem inputs (bits 7:4 = DCD, RI, DSR, CTS) over the four
   DELTA bits (3:0) that a read clears.  This board's port has no modem
   cable: its inputs sit at the idle-asserted level the machine reports
   (DCD|DSR|CTS) and never move, so no delta bit can ever be set and the
   read has nothing to clear -- which is why MSR is a pure function of the
   state here rather than a field of it.  Under LOOP the inputs come from
   MCR's own outputs instead: DTR->DSR, RTS->CTS, OUT1->RI, OUT2->DCD. *)
Definition uart_msr_idle : Z := 0xb0.

Definition uart_msr (u : uart_state) : bv 8 :=
  if uart_loopback u then
    let m := bv_unsigned (u_mcr u) in
    Z_to_bv 8 (Z.lor (Z.shiftl (Z.land m 0x0c) 4)
                     (Z.lor (Z.shiftl (Z.land m 0x02) 3)
                            (Z.shiftl (Z.land m 0x01) 5)))
  else Z_to_bv 8 uart_msr_idle.

(* Every arm below spells [UartState]'s fields positionally, in the record's
   own order:
     rx  tx  out  wire  ier  lcr  fcr  dll  dlm  mcr  scr  rbr  thri
   Coq has no record-update syntax and a setter per arm would only move the
   same list somewhere else; adding a register means extending each arm here,
   and the type checker finds every one of them. *)

(* one MMIO read of byte register [off] (0..7): value + successor state *)
Definition uart_read (u : uart_state) (off : Z) : option (bv 8 * uart_state) :=
  if off =? 0 then
    if uart_dlab u then Some (u_dll u, u)
    else (* RHR: pop the receive FIFO *)
      match u_rx u with
      | [] =>
          (* DR is CLEAR.  The datasheet leaves this read undefined and the
             hardware answers out of the receive HOLDING register, which
             neither a read nor an FCR clear ever erases -- only the DR flag
             goes away.  (Finding 23: the model used to answer 0 where the
             machine hands back the last byte it received.)  With the FIFOs
             enabled the holding register is the FIFO's own output stage and
             the machine answers 0. *)
          Some ((if uart_fifo_en u then byte0 else u_rbr u), u)
      | b :: rx' =>
          Some (b, UartState rx' (u_tx u) (u_out u) (u_wire u) (u_ier u)
                             (u_lcr u) (u_fcr u) (u_dll u) (u_dlm u)
                             (u_mcr u) (u_scr u) (u_rbr u) (u_thri u))
      end
  else if off =? 1 then
    if uart_dlab u then Some (u_dlm u, u) else Some (u_ier u, u)
  else if off =? 2 then
    Some (uart_isr u,
          if uart_isr_thri u then
            UartState (u_rx u) (u_tx u) (u_out u) (u_wire u) (u_ier u)
                      (u_lcr u) (u_fcr u) (u_dll u) (u_dlm u)
                      (u_mcr u) (u_scr u) (u_rbr u) false
          else u)
  else if off =? 3 then Some (u_lcr u, u)
  else if off =? 4 then Some (u_mcr u, u)
  else if off =? 5 then Some (uart_lsr u, u)
  else if off =? 6 then Some (uart_msr u, u)
  else if off =? 7 then Some (u_scr u, u)
  else None.

(* one MMIO write of byte register [off] *)
Definition uart_write (u : uart_state) (off : Z) (b : bv 8) : option uart_state :=
  if off =? 0 then
    if uart_dlab u then
      Some (UartState (u_rx u) (u_tx u) (u_out u) (u_wire u) (u_ier u)
                      (u_lcr u) (u_fcr u) b (u_dlm u)
                      (u_mcr u) (u_scr u) (u_rbr u) (u_thri u))
    else (* THR: push onto the transmit FIFO (dropped if full, as in hw).
            The transmitter is no longer idle, so the latch drops -- and it
            drops on the DROPPED write too: the byte is lost, but the write
            happened, and the hardware disarms the interrupt either way. *)
      if (length (u_tx u) <? uart_fifo_depth)%nat then
        Some (UartState (u_rx u) (u_tx u ++ [b]) (u_out u) (u_wire u) (u_ier u)
                        (u_lcr u) (u_fcr u) (u_dll u) (u_dlm u)
                        (u_mcr u) (u_scr u) (u_rbr u) false)
      else
        Some (UartState (u_rx u) (u_tx u) (u_out u) (u_wire u) (u_ier u)
                        (u_lcr u) (u_fcr u) (u_dll u) (u_dlm u)
                        (u_mcr u) (u_scr u) (u_rbr u) false)
  else if off =? 1 then
    if uart_dlab u then
      Some (UartState (u_rx u) (u_tx u) (u_out u) (u_wire u) (u_ier u)
                      (u_lcr u) (u_fcr u) (u_dll u) b
                      (u_mcr u) (u_scr u) (u_rbr u) (u_thri u))
    else
      (* IER holds four bits.  Enabling the transmit interrupt on an ALREADY
         idle transmitter arms the latch, because no later edge would. *)
      let ier := Z_to_bv 8 (Z.land (bv_unsigned b) 0x0f) in
      Some (UartState (u_rx u) (u_tx u) (u_out u) (u_wire u) ier
                      (u_lcr u) (u_fcr u) (u_dll u) (u_dlm u)
                      (u_mcr u) (u_scr u) (u_rbr u)
                      (u_thri u || (Z.testbit (bv_unsigned ier) 1 && uart_thre u)))
  else if off =? 2 then
    (* FCR: bit 0 enables the FIFOs, bit 1 clears the receive FIFO and bit 2
       the transmit FIFO.  Bits 1 and 2 are self-clearing, so what the
       register HOLDS is 0xc9's worth.  CHANGING bit 0 flushes BOTH FIFOs,
       which is why a driver that enables them loses whatever had already
       arrived -- measured on the machine, and the reason the conformance
       suite's receive test leaves them off.  A cleared transmit FIFO is an
       idle transmitter, so the latch arms. *)
    let flush  := xorb (Z.testbit (bv_unsigned b) 0) (uart_fifo_en u) in
    let clr_rx := flush || Z.testbit (bv_unsigned b) 1 in
    let clr_tx := flush || Z.testbit (bv_unsigned b) 2 in
    Some (UartState (if clr_rx then [] else u_rx u)
                    (if clr_tx then [] else u_tx u)
                    (u_out u) (u_wire u) (u_ier u) (u_lcr u)
                    (Z_to_bv 8 (Z.land (bv_unsigned b) 0xc9))
                    (u_dll u) (u_dlm u) (u_mcr u) (u_scr u) (u_rbr u)
                    (u_thri u || clr_tx))
  else if off =? 3 then
    Some (UartState (u_rx u) (u_tx u) (u_out u) (u_wire u) (u_ier u)
                    b (u_fcr u) (u_dll u) (u_dlm u)
                    (u_mcr u) (u_scr u) (u_rbr u) (u_thri u))
  else if off =? 4 then
    (* MCR holds five bits; 7:5 read back as zero. *)
    Some (UartState (u_rx u) (u_tx u) (u_out u) (u_wire u) (u_ier u)
                    (u_lcr u) (u_fcr u) (u_dll u) (u_dlm u)
                    (Z_to_bv 8 (Z.land (bv_unsigned b) 0x1f))
                    (u_scr u) (u_rbr u) (u_thri u))
  else if off =? 7 then
    Some (UartState (u_rx u) (u_tx u) (u_out u) (u_wire u) (u_ier u)
                    (u_lcr u) (u_fcr u) (u_dll u) (u_dlm u)
                    (u_mcr u) b (u_rbr u) (u_thri u))
  else if (off =? 5) || (off =? 6) then Some u  (* LSR and MSR are read-only *)
  else None.

(* Reading the LSR is a pure observation: it returns the status byte and does
   NOT advance the device (unlike RHR, which pops the rx FIFO). *)
Lemma uart_read_lsr (u : uart_state) : uart_read u 5 = Some (uart_lsr u, u).
Proof. reflexivity. Qed.

(* Reading the ISR is NOT.  The value is always [uart_isr u], but a read that
   REPORTS the transmit interrupt is the acknowledgement of it and clears the
   latch -- so a driver that reads the ISR twice sees the interrupt go away,
   which is what the hardware does and what the level model could not do. *)

(* the read that reports something else -- or nothing -- leaves the device
   alone, which is the form a poll of the ISR uses *)

(* ...and the read that DOES report it disarms it *)

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
  destruct (off =? 4) eqn:E4. { by do 2 eexists. }
  destruct (off =? 5) eqn:E5. { by do 2 eexists. }
  destruct (off =? 6) eqn:E6. { by do 2 eexists. }
  destruct (off =? 7) eqn:E7. { by do 2 eexists. }
  exfalso.
  apply Z.eqb_neq in E0, E1, E2, E3, E4, E5, E6, E7. lia.
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
  destruct (off =? 4) eqn:E4. { by eexists. }
  destruct (off =? 7) eqn:E7. { by eexists. }
  destruct ((off =? 5) || (off =? 6)) eqn:E56. { by eexists. }
  exfalso.
  apply Z.eqb_neq in E0, E1, E2, E3, E4, E7.
  apply orb_false_elim in E56 as [E5 E6].
  apply Z.eqb_neq in E5, E6. lia.
Qed.

(* -- the UART's autonomous transitions (the device "thread") -- *)

(* The RECEIVER latching a byte, which is one event with two causes: a byte
   arriving from outside ([uart_rx_push]) and, in loopback, a byte leaving
   this UART's own transmitter ([uart_tx_pop]).  A full FIFO OVERRUNS -- the
   byte is lost -- and the holding register keeps it either way. *)
Definition uart_recv (u : uart_state) (b : bv 8) : uart_state :=
  UartState (if (length (u_rx u) <? uart_fifo_depth)%nat then u_rx u ++ [b]
             else u_rx u)
            (u_tx u) (u_out u) (u_wire u) (u_ier u) (u_lcr u) (u_fcr u)
            (u_dll u) (u_dlm u) (u_mcr u) (u_scr u) b (u_thri u).

(* The receiver touches the receive side and nothing else, so none of the
   three quantities the UART ghosts track (WpUart.v) can move under it.
   These are the shape the drain lemmas below need, since the drain's
   loopback arm ends in a [uart_recv]. *)
Lemma uart_recv_out (u : uart_state) (b : bv 8) : u_out (uart_recv u b) = u_out u.
Proof. reflexivity. Qed.
Lemma uart_recv_tx (u : uart_state) (b : bv 8) : u_tx (uart_recv u b) = u_tx u.
Proof. reflexivity. Qed.
Lemma uart_recv_lcr (u : uart_state) (b : bv 8) : u_lcr (uart_recv u b) = u_lcr u.
Proof. reflexivity. Qed.

(* transmit: the head of the tx FIFO leaves the transmitter.  It goes onto
   the wire, or -- under LOOP -- straight back into this UART's receiver,
   with SOUT held marking so the host sees nothing.  Either way the
   transmitter is one byte emptier, and an emptied transmitter arms the
   THRE latch. *)
Definition uart_tx_pop (u : uart_state) : option (bv 8 * uart_state) :=
  match u_tx u with
  | [] => None
  | b :: tx' =>
      let u' := UartState (u_rx u) tx' (u_out u ++ [b])
                          (if uart_loopback u then u_wire u else u_wire u ++ [b])
                          (u_ier u) (u_lcr u) (u_fcr u) (u_dll u) (u_dlm u)
                          (u_mcr u) (u_scr u) (u_rbr u)
                          (match tx' with [] => true | _ => u_thri u end) in
      Some (b, if uart_loopback u then uart_recv u' b else u')
  end.

(* receive: a byte arrives from the outside world.  REFUSED when the FIFO is
   full, which is flow control and not an overrun: the host is told to wait,
   exactly as the machine's front end does. *)
Definition uart_rx_push (u : uart_state) (b : bv 8) : option uart_state :=
  if (length (u_rx u) <? uart_fifo_depth)%nat then Some (uart_recv u b)
  else None.

(* -- the accepted-byte trace -- *)

(* [uart_acc u] is every byte the UART has ACCEPTED for transmission: those
   the transmitter has finished with ([u_out]) followed by those still queued
   ([u_tx]).  It
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
  - destruct (uart_loopback u); intro H; injection H as <- <-.
    + (* the loopback arm hands the byte to [uart_recv], which touches
         neither [u_out] nor [u_tx]: the accepted trace does not record where
         the byte went, only that the transmitter is done with it *)
      rewrite uart_recv_out, uart_recv_tx.
      cbn [u_out u_tx]. rewrite <- app_assoc. reflexivity.
    + cbn [u_out u_tx]. rewrite <- app_assoc. reflexivity.
Qed.

(* a byte arriving on the rx side touches neither [u_out] nor [u_tx] *)
Lemma uart_rx_push_acc (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_rx_push u b = Some u' -> uart_acc u' = uart_acc u.
Proof.
  unfold uart_rx_push, uart_recv, uart_acc.
  destruct (length (u_rx u) <? uart_fifo_depth)%nat; [| discriminate].
  intro H. injection H as <-. reflexivity.
Qed.

(* NO READ MOVES ANY OF THE THREE TRACKED TX QUANTITIES.  Only the RHR read
   advances the device at all, and it pops the RECEIVE FIFO, which appears in
   none of [uart_acc] / [u_out] / [uart_dlab].  So a driver may read any UART
   register with no transmitter token and no ghost obligation whatever --
   [uart_ghosts_stable] (WpUart.v) applies to every offset.  This is what makes
   uartintr's ISR acknowledge, its rx-ready poll and its RHR pops (uartgetc,
   which gcc inlines into it) plain observations. *)
Lemma uart_read_stable (u : uart_state) (off : Z) (b : bv 8) (u' : uart_state) :
  uart_read u off = Some (b, u') ->
  uart_acc u' = uart_acc u /\ u_out u' = u_out u /\ uart_dlab u' = uart_dlab u.
Proof.
  intro Hread. revert Hread. unfold uart_read.
  destruct (off =? 0) eqn:E0.
  { destruct (uart_dlab u) eqn:Ed.
    - intro H. inversion H. subst u'. done.
    - destruct (u_rx u) as [| c rx']; intro H; inversion H; subst u'; done. }
  destruct (off =? 1) eqn:E1.
  { destruct (uart_dlab u) eqn:Ed; intro H; inversion H; subst u'; done. }
  destruct (off =? 2) eqn:E2.
  { (* the ISR read may disarm the transmit latch, which is none of the
       three tracked quantities either *)
    destruct (uart_isr_thri u); intro H; inversion H; subst u'; done. }
  destruct (off =? 3) eqn:E3. { intro H; inversion H; subst u'; done. }
  destruct (off =? 4) eqn:E4. { intro H; inversion H; subst u'; done. }
  destruct (off =? 5) eqn:E5. { intro H; inversion H; subst u'; done. }
  destruct (off =? 6) eqn:E6. { intro H; inversion H; subst u'; done. }
  destruct (off =? 7) eqn:E7. { intro H; inversion H; subst u'; done. }
  discriminate.
Qed.

(* ---------------------------------------------------------------------- *)
(*  THE RECEIVE SIDE, as pure facts.  The UART invariant keeps a TAG COLUMN  *)
(*  aligned with [u_rx] (WpUart.v), so every transition that touches the     *)
(*  receive FIFO owes a statement here about [u_rx] -- and about             *)
(*  [uart_loopback], because the column is maintainable only with LOOP off:  *)
(*  a loopbacked byte enters this UART's own receiver with no observation,   *)
(*  hence with no tag to file beside it ([uart_tx_pop]'s loopback arm).      *)
(* ---------------------------------------------------------------------- *)

(* MCR bit 4 is the only thing loopback reads, so every write except MCR's
   leaves it alone, as does every read. *)
Lemma uart_read_rx_stable (u : uart_state) (off : Z) (b : bv 8) (u' : uart_state) :
  off <> 0 \/ uart_dlab u = true ->
  uart_read u off = Some (b, u') ->
  u_rx u' = u_rx u /\ uart_loopback u' = uart_loopback u.
Proof.
  intro Hoff. unfold uart_read.
  destruct (off =? 0) eqn:E0.
  { destruct Hoff as [Hne | Hd].
    - apply Z.eqb_eq in E0. lia.
    - rewrite Hd. intro H. injection H as <- <-. done. }
  destruct (off =? 1) eqn:E1.
  { destruct (uart_dlab u); intro H; injection H as <- <-; done. }
  destruct (off =? 2) eqn:E2.
  { destruct (uart_isr_thri u); intro H; injection H as <- <-; done. }
  destruct (off =? 3) eqn:E3. { intro H; injection H as <- <-; done. }
  destruct (off =? 4) eqn:E4. { intro H; injection H as <- <-; done. }
  destruct (off =? 5) eqn:E5. { intro H; injection H as <- <-; done. }
  destruct (off =? 6) eqn:E6. { intro H; injection H as <- <-; done. }
  destruct (off =? 7) eqn:E7. { intro H; injection H as <- <-; done. }
  discriminate.
Qed.

(* RHR with DLAB clear IS the pop, and the byte it returns is the head. *)
Lemma uart_read_rhr_pop (u : uart_state) (b : bv 8) (rx' : list (bv 8))
    (bt : bv 8) (u' : uart_state) :
  uart_dlab u = false ->
  u_rx u = b :: rx' ->
  uart_read u 0 = Some (bt, u') ->
  bt = b /\ u_rx u' = rx' /\ uart_loopback u' = uart_loopback u.
Proof.
  intros Hd Hrx. unfold uart_read. cbn [Z.eqb]. rewrite Hd, Hrx.
  intro H. injection H as <- <-. done.
Qed.

(* ...and with an EMPTY FIFO it is a pure read: the junk arm. *)
Lemma uart_read_rhr_empty (u : uart_state) (bt : bv 8) (u' : uart_state) :
  uart_dlab u = false ->
  u_rx u = [] ->
  uart_read u 0 = Some (bt, u') -> u' = u.
Proof.
  intros Hd Hrx. unfold uart_read. cbn [Z.eqb]. rewrite Hd, Hrx.
  intro H. by injection H as <- <-.
Qed.

(* Every write but FCR's and MCR's leaves the receive FIFO and LOOP alone. *)
Lemma uart_write_rx_stable (u : uart_state) (off : Z) (b : bv 8) (u' : uart_state) :
  off <> 2 -> off <> 4 ->
  uart_write u off b = Some u' ->
  u_rx u' = u_rx u /\ uart_loopback u' = uart_loopback u.
Proof.
  intros H2 H4. unfold uart_write.
  destruct (off =? 0) eqn:E0.
  { destruct (uart_dlab u); [intro H; injection H as <-; done|].
    destruct (length (u_tx u) <? uart_fifo_depth)%nat;
      intro H; injection H as <-; done. }
  destruct (off =? 1) eqn:E1.
  { destruct (uart_dlab u); intro H; injection H as <-; done. }
  destruct (off =? 2) eqn:E2. { apply Z.eqb_eq in E2. lia. }
  destruct (off =? 3) eqn:E3. { intro H; injection H as <-; done. }
  destruct (off =? 4) eqn:E4. { apply Z.eqb_eq in E4. lia. }
  destruct (off =? 7) eqn:E7. { intro H; injection H as <-; done. }
  destruct ((off =? 5) || (off =? 6)). { intro H; injection H as <-; done. }
  discriminate.
Qed.

(* THE FCR WRITE IS A POP OF EVERYTHING, or of nothing.  Bit 1 clears the
   receive FIFO outright and TOGGLING bit 0 flushes both FIFOs, so a driver
   that enables them loses whatever had already arrived -- which is exactly
   what xv6's [uartinit] does (FCR = 0x07).  Hence the receive token: this is
   the one transition besides the RHR pop that removes queued bytes. *)
Definition uart_fcr_clr_rx (u : uart_state) (b : bv 8) : bool :=
  xorb (Z.testbit (bv_unsigned b) 0) (uart_fifo_en u)
  || Z.testbit (bv_unsigned b) 1.

Lemma uart_write_fcr_rx (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_write u 2 b = Some u' ->
  u_rx u' = (if uart_fcr_clr_rx u b then [] else u_rx u)
  /\ uart_loopback u' = uart_loopback u.
Proof.
  unfold uart_write, uart_fcr_clr_rx. cbn [Z.eqb].
  intro H. injection H as <-. cbn [u_rx u_mcr]. done.
Qed.

(* An MCR write is the only thing that can turn LOOP ON, which is what the
   column's [uart_loopback u = false] clause is about; nothing in the kernel
   writes MCR, and [uart_write_rx_stable] covers every offset that is neither
   it nor FCR. *)

(* The device's own two receive-side arms. *)
Lemma uart_tx_pop_rx (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_loopback u = false ->
  uart_tx_pop u = Some (b, u') ->
  u_rx u' = u_rx u /\ uart_loopback u' = uart_loopback u.
Proof.
  intro Hlb. unfold uart_tx_pop.
  destruct (u_tx u) as [| c tx']; [discriminate|].
  rewrite Hlb. intro H. injection H as <- <-. done.
Qed.

Lemma uart_rx_push_rx (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_rx_push u b = Some u' ->
  u_rx u' = u_rx u ++ [b] /\ uart_loopback u' = uart_loopback u.
Proof.
  unfold uart_rx_push.
  destruct (length (u_rx u) <? uart_fifo_depth)%nat eqn:Hroom; [| discriminate].
  intro H. injection H as <-. cbn [u_rx uart_recv u_mcr]. rewrite Hroom. done.
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

(* NOTE (deliberate, load-bearing): there is NO general monotonicity lemma for
   [uart_write].  An FCR write (offset 2) with bit 2 set CLEARS the tx FIFO,
   which in general SHRINKS [uart_acc] -- the queued bytes are discarded, never
   sent -- so an invariant holding a monotone [uart_acc] ghost forbids it.
   xv6's [uartinit] performs exactly that write (FCR_FIFO_CLEAR = bits 1|2),
   and is verifiable anyway, because a proof that OWNS the transmitter can show
   the FIFO empty at the write ([uart_write_2_stable] below, whose [u_tx u = []]
   premise comes from [uart_tx_empty_of_out]) -- and a clear of an empty FIFO
   shrinks nothing.  What stays forbidden is a FIFO-clearing write by code that
   cannot prove the FIFO empty. *)

(* -- CONFIG WRITES: which of the three tracked quantities each offset moves --

   The three quantities the UART ghosts track are [uart_acc], [u_out] and
   [uart_dlab] (see WpUart.v's [uart_ghosts]).  A leaf-level device store hands
   its caller a [uart_write u off b = Some u'] equation and asks for the ghosts
   back at [u']; the four lemmas below are what turn that equation into
   "nothing moved" (or, for the LCR, "exactly DLAB moved"), one per offset the
   16550 init sequence writes.  Together with [uart_write_out] they cover every
   offset [uartinit] touches: 1 (IER/DLM), 0 with DLAB set (DLL), 3 (LCR) and
   2 (FCR). *)

(* DLAB is nothing but a field of the LCR, so an LCR-preserving transition
   preserves it. *)
Lemma uart_dlab_of_lcr (u u' : uart_state) :
  u_lcr u' = u_lcr u -> uart_dlab u' = uart_dlab u.
Proof. intro H. unfold uart_dlab. by rewrite H. Qed.

(* ...and the three tracked quantities are all determined by three FIELDS, so
   every per-offset lemma below reduces to reading those fields off the state
   the write produced. *)
Lemma uart_tracked_of_fields (u u' : uart_state) :
  u_out u' = u_out u -> u_tx u' = u_tx u -> u_lcr u' = u_lcr u ->
  uart_acc u' = uart_acc u /\ u_out u' = u_out u /\ uart_dlab u' = uart_dlab u.
Proof.
  intros Ho Ht Hl. unfold uart_acc.
  rewrite Ho, Ht. split_and!;
    [ reflexivity | reflexivity | exact (uart_dlab_of_lcr u u' Hl) ].
Qed.

(* Offset 1 is IER (DLAB clear) or DLM (DLAB set); neither is a FIFO nor the
   LCR, so all three tracked quantities are fixed. *)
Lemma uart_write_1_stable (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_write u 1 b = Some u' ->
  uart_acc u' = uart_acc u /\ u_out u' = u_out u /\ uart_dlab u' = uart_dlab u.
Proof.
  intro H. unfold uart_write in H. cbn [Z.eqb] in H.
  apply uart_tracked_of_fields;
    destruct (uart_dlab u); injection H as <-; reflexivity.
Qed.

(* Offset 0 with DLAB SET is the divisor latch, NOT the transmit holding
   register: it queues no byte, so it moves nothing tracked either.  (With DLAB
   clear the same offset is a THR push -- [uart_write_thr_acc].) *)
Lemma uart_write_0_dlab_stable (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_dlab u = true ->
  uart_write u 0 b = Some u' ->
  uart_acc u' = uart_acc u /\ u_out u' = u_out u /\ uart_dlab u' = uart_dlab u.
Proof.
  intros Hdlab H. unfold uart_write in H. cbn [Z.eqb] in H.
  rewrite Hdlab in H.
  apply uart_tracked_of_fields; injection H as <-; reflexivity.
Qed.

(* Offset 3 is the LCR -- the ONLY write that can move DLAB, and it moves
   nothing else.  The new DLAB is just bit 7 of the stored byte. *)
Lemma uart_write_3_stable (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_write u 3 b = Some u' ->
  uart_acc u' = uart_acc u /\ u_out u' = u_out u
  /\ uart_dlab u' = Z.testbit (bv_unsigned b) 7.
Proof.
  intro H. unfold uart_write in H. cbn [Z.eqb] in H. injection H as <-.
  unfold uart_acc, uart_dlab. cbn [u_out u_tx u_lcr].
  split_and!; reflexivity.
Qed.

(* Offset 2 is the FCR.  Bit 1 clears the RECEIVE FIFO, which appears in none
   of the three tracked quantities; bit 2 clears the TRANSMIT FIFO, which is
   why the FIFO must be provably empty -- and then the clear is the identity
   on it.  Nothing tracked moves. *)
Lemma uart_write_2_stable (u : uart_state) (b : bv 8) (u' : uart_state) :
  u_tx u = [] ->
  uart_write u 2 b = Some u' ->
  uart_acc u' = uart_acc u /\ u_out u' = u_out u /\ uart_dlab u' = uart_dlab u.
Proof.
  intros Htx H. unfold uart_write in H. cbn [Z.eqb] in H. injection H as <-.
  apply uart_tracked_of_fields; cbn [u_out u_tx u_lcr];
    [ reflexivity
    | rewrite Htx;
      match goal with |- (if ?c then _ else _) = _ => destruct c end;
      reflexivity
    | reflexivity ].
Qed.

(* -- the transmitted prefix [u_out] -- *)

(* [u_out] is append-only: the drain step is the ONLY transition that touches
   it, and it only ever appends.  This is what lets an observation of "the tx
   FIFO is empty" survive later device steps: see [uart_tx_still_empty]. *)
Lemma uart_tx_pop_out (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_tx_pop u = Some (b, u') -> u_out u' = u_out u ++ [b].
Proof.
  unfold uart_tx_pop. destruct (u_tx u) as [| b0 tx'] eqn:Htx; [discriminate|].
  destruct (uart_loopback u); intro H; injection H as <- <-.
  - by rewrite uart_recv_out.
  - reflexivity.
Qed.

Lemma uart_rx_push_out (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_rx_push u b = Some u' -> u_out u' = u_out u.
Proof.
  unfold uart_rx_push, uart_recv.
  destruct (length (u_rx u) <? uart_fifo_depth)%nat; [| discriminate].
  intro H. injection H as <-. reflexivity.
Qed.

(* -- the wire trace [u_wire] -- *)

(* What the drain step puts ON THE WIRE: the popped byte in normal mode,
   nothing under LOOP (the byte goes back into this UART's own receiver, with
   SOUT held marking).  This is the pure fact behind the language's UART
   OUTPUT OBSERVATION (RiscvLang.uart_step): the observation list of a drain
   step is exactly the wire's growth. *)

(* ... and a byte ARRIVING never touches the wire: SOUT is the transmitter's *)

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
  destruct (off =? 4). { intro H; injection H as <-; reflexivity. }
  destruct (off =? 7). { intro H; injection H as <-; reflexivity. }
  destruct ((off =? 5) || (off =? 6)).
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
  unfold uart_tx_pop, uart_dlab.
  destruct (u_tx u) as [| b0 tx'] eqn:Htx; [discriminate|].
  destruct (uart_loopback u); intro H; injection H as <- <-.
  - by rewrite uart_recv_lcr.
  - reflexivity.
Qed.

Lemma uart_rx_push_dlab (u : uart_state) (b : bv 8) (u' : uart_state) :
  uart_rx_push u b = Some u' -> uart_dlab u' = uart_dlab u.
Proof.
  unfold uart_rx_push, uart_recv.
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
(* 2. The PLIC: BOTH contexts of every hart, and all 96 of the board's     *)
(*    sources.                                                            *)
(*                                                                        *)
(*    CONTEXTS, not harts.  The interrupt controller does not know about   *)
(*    harts; it has [plic_nctx] independent CONTEXTS, each with its own    *)
(*    enable bitmap, threshold and claim register, and the board wires two *)
(*    of them to each hart: context 2h is hart h's M-mode context and      *)
(*    2h+1 its S-mode one ([plic_mctx]/[plic_sctx]).  Modelling only the   *)
(*    S half -- which is all xv6 uses -- made every M-context register a   *)
(*    STUCK access (finding 11), so an M-mode handler or a bootloader that *)
(*    parks its own context could not be described at all.                *)
(*                                                                        *)
(*    THE THRESHOLD GATES THE CLAIM, and that is finding 10: it used to    *)
(*    appear in [plic_eip] alone, so the model could hand a context the id *)
(*    of a source that context cannot see -- a value the hardware never    *)
(*    produces -- and clear a pending bit the hardware leaves standing.    *)
(*    It now lives in [plic_cand], which [plic_eip] and [plic_claim] BOTH  *)
(*    read, so the notification and the claim agree by construction.      *)
(* ---------------------------------------------------------------------- *)

Record plic_state := PlicState {
  p_prio    : N -> bv 32;         (* per-source priority (0 = never interrupts) *)
  p_pending : N -> bool;          (* gateway has forwarded a request *)
  p_claimed : N -> bool;          (* claimed (in service), completion pending *)
  p_enable  : nat -> nat -> bv 32;(* per-CONTEXT enable bitmap, 32 sources/word *)
  p_thresh  : nat -> bv 32;       (* per-CONTEXT priority threshold *)
}.

(* the disk's interrupt source; the two UARTs are [uart_irq_id Uart0] = 10
   and [uart_irq_id Uart1] = 12.  Which device sits on which PLIC source is a
   property of the machine, hence here; what the KERNEL intends to do with
   those sources lives in the software layer (PlicPlan.v). *)
Definition virtio_irq_id : N := 1%N.   (* VIRTIO0_IRQ *)

(* The board's source count: 96, so the enable and pending bitmaps are three
   32-bit words each.  Source 0 does not exist -- its priority register is
   hardwired to zero and its pending/enable bits are never set. *)
Definition plic_nsrc : nat := 96%nat.
Definition plic_nwords : nat := 3%nat.

(* Two contexts per hart, M then S. *)
Definition plic_nctx : nat := (2 * dev_ncpu)%nat.
Definition plic_mctx (h : nat) : nat := (2 * h)%nat.
Definition plic_sctx (h : nat) : nat := (2 * h + 1)%nat.

(* which enable/pending word a source lives in, and which bit of it *)
Definition plic_src_word (i : N) : nat := (N.to_nat i / 32)%nat.
Definition plic_src_bit (i : N) : Z := Z.of_N i mod 32.

(* pointwise function updates *)
Definition nupd {A} (f : N -> A) (i : N) (x : A) : N -> A :=
  fun j => if N.eqb j i then x else f j.
Definition hupd {A} (f : nat -> A) (h : nat) (x : A) : nat -> A :=
  fun k => if Nat.eqb k h then x else f k.
(* ...and the two-level one the per-context enable bitmap needs *)
Definition wupd (f : nat -> nat -> bv 32) (c w : nat) (x : bv 32)
  : nat -> nat -> bv 32 :=
  fun c' w' => if Nat.eqb c' c && Nat.eqb w' w then x else f c' w'.

Definition plic_enabled (p : plic_state) (c : nat) (i : N) : bool :=
  Z.testbit (bv_unsigned (p_enable p c (plic_src_word i))) (plic_src_bit i).

(* IS SOURCE [i] VISIBLE TO CONTEXT [c]?  Pending at the gateway, enabled in
   this context's bitmap, and of a priority STRICTLY above this context's
   threshold.  A priority-0 source can never clear a threshold of 0, so this
   subsumes the old explicit "priority 0 never interrupts" guard.

   This one predicate is the whole of the context's view: [plic_eip] asks
   whether ANY source is visible and [plic_best] which visible one wins, so
   the pin and the claim register cannot disagree (finding 10). *)
Definition plic_cand (p : plic_state) (c : nat) (i : N) : bool :=
  p_pending p i && plic_enabled p c i
  && (bv_unsigned (p_thresh p c) <? bv_unsigned (p_prio p i)).

(* strictly better: higher priority, ties broken toward the lower id *)
Definition plic_better (p : plic_state) (i j : N) : bool :=
  (bv_unsigned (p_prio p j) <? bv_unsigned (p_prio p i))
  || ((bv_unsigned (p_prio p i) =? bv_unsigned (p_prio p j)) && (i <? j)%N).

Definition plic_srcs : list N := map N.of_nat (seq 1 (plic_nsrc - 1)).

Definition plic_best (p : plic_state) (c : nat) : option N :=
  fold_left (fun best i =>
               if plic_cand p c i then
                 match best with
                 | None => Some i
                 | Some j => if plic_better p i j then Some i else Some j
                 end
               else best)
            plic_srcs None.

(* claim: return (and clear pending on, mark claimed) the best VISIBLE source;
   0 if the context can see none -- including the case where the only pending
   sources are masked by the threshold, where the hardware likewise answers 0
   and leaves them pending. *)
Definition plic_claim (p : plic_state) (c : nat) : bv 32 * plic_state :=
  match plic_best p c with
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

(* the external-interrupt-pending level the PLIC drives into context [c]:
   some source is visible to it *)
Definition plic_eip (p : plic_state) (c : nat) : bool :=
  existsb (plic_cand p c) plic_srcs.

(* the pending bitmap's word [w] (sources 32w .. 32w+31), for a read of
   offset 0x1000 + 4w *)
Definition plic_pending_word (p : plic_state) (w : nat) : bv 32 :=
  Z_to_bv 32 (fold_right (fun j acc =>
                            if p_pending p (N.of_nat (32 * w + j))
                            then Z.lor (Z.shiftl 1 (Z.of_nat j)) acc else acc)
                         0 (seq 0 32)).

(* -- PLIC MMIO decode: 32-bit registers at [off] within the PLIC window -- *)

(* SOURCE PRIORITY, one word per source at [4i].  Source 0's register exists
   (finding 12: it used to be the one hole a plain "mask every source" init
   loop fell into) but source 0 does not, so it reads zero and swallows its
   writes. *)
Definition plic_prio_src (off : Z) : option N :=
  if (0 <=? off) && (off <? 4 * Z.of_nat plic_nsrc) && (off mod 4 =? 0)
  then Some (Z.to_N (off / 4)) else None.

(* the PENDING bitmap, read-only: three words at 0x1000. *)
Definition plic_pending_widx (off : Z) : option nat :=
  if (0x1000 <=? off) && (off <? 0x1000 + 4 * Z.of_nat plic_nwords)
     && (off mod 4 =? 0)
  then Some (Z.to_nat ((off - 0x1000) / 4)) else None.

(* PER-CONTEXT ENABLE: a 0x80-byte block per context at 0x2000, of which the
   first [plic_nwords] words are real; the rest of the block is reserved. *)
Definition plic_enable_ctx (off : Z) : option (nat * nat) :=
  if (0x2000 <=? off) && (off <? 0x2000 + 0x80 * Z.of_nat plic_nctx)
     && (off mod 4 =? 0)
     && (((off - 0x2000) mod 0x80) / 4 <? Z.of_nat plic_nwords)
  then Some (Z.to_nat ((off - 0x2000) / 0x80),
             Z.to_nat (((off - 0x2000) mod 0x80) / 4))
  else None.

(* PER-CONTEXT THRESHOLD and CLAIM/COMPLETE: one 0x1000-byte page per context
   at 0x200000, threshold at +0 and claim/complete at +4. *)
Definition plic_thresh_ctx (off : Z) : option nat :=
  if (0x200000 <=? off) && ((off - 0x200000) mod 0x1000 =? 0)
     && ((off - 0x200000) / 0x1000 <? Z.of_nat plic_nctx)
  then Some (Z.to_nat ((off - 0x200000) / 0x1000)) else None.
Definition plic_claim_ctx (off : Z) : option nat :=
  if (0x200004 <=? off) && ((off - 0x200004) mod 0x1000 =? 0)
     && ((off - 0x200004) / 0x1000 <? Z.of_nat plic_nctx)
  then Some (Z.to_nat ((off - 0x200004) / 0x1000)) else None.

Definition plic_read (p : plic_state) (off : Z) : option (bv 32 * plic_state) :=
  match plic_prio_src off with
  | Some i => Some (if (i =? 0)%N then Z_to_bv 32 0 else p_prio p i, p)
  | None =>
  match plic_pending_widx off with
  | Some w => Some (plic_pending_word p w, p)
  | None =>
  match plic_enable_ctx off with
  | Some (c, w) => Some (p_enable p c w, p)
  | None =>
  match plic_thresh_ctx off with
  | Some c => Some (p_thresh p c, p)
  | None =>
  match plic_claim_ctx off with
  | Some c => Some (plic_claim p c)              (* claim: side effect *)
  | None => None
  end end end end end.

Definition plic_write (p : plic_state) (off : Z) (v : bv 32) : option plic_state :=
  match plic_prio_src off with
  | Some i =>
      (* source 0's register is hardwired zero: the write is dropped *)
      Some (if (i =? 0)%N then p
            else PlicState (nupd (p_prio p) i v) (p_pending p)
                           (p_claimed p) (p_enable p) (p_thresh p))
  | None =>
  match plic_pending_widx off with
  | Some _ => Some p          (* the pending bitmap is read-only *)
  | None =>
  match plic_enable_ctx off with
  | Some (c, w) => Some (PlicState (p_prio p) (p_pending p) (p_claimed p)
                                   (wupd (p_enable p) c w v) (p_thresh p))
  | None =>
  match plic_thresh_ctx off with
  | Some c => Some (PlicState (p_prio p) (p_pending p) (p_claimed p)
                              (p_enable p) (hupd (p_thresh p) c v))
  | None =>
  match plic_claim_ctx off with
  | Some _ => Some (plic_complete p (Z.to_N (bv_unsigned v)))
  | None => None
  end end end end end.

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

(* THE UART FIELD IS A FUNCTION OF THE PORT, exactly as the PLIC's enable
   bitmap is a function of the context: two ports are two states of one
   chip, not two records, so every fact about a 16550 is stated once and
   instantiated at [Uart0] or [Uart1]. *)
Record dev_state := DevState {
  duart : uart_id -> uart_state;
  dplic : plic_state;
  dvirtio : virtio_state;
}.

Definition uupd (f : uart_id -> uart_state) (i : uart_id) (u : uart_state)
  : uart_id -> uart_state :=
  fun j => if decide (j = i) then u else f j.

Definition set_duart (d : dev_state) (i : uart_id) (u : uart_state) : dev_state :=
  DevState (uupd (duart d) i u) (dplic d) (dvirtio d).
Definition set_dplic (d : dev_state) (p : plic_state) : dev_state :=
  DevState (duart d) p (dvirtio d).
Definition set_dvirtio (d : dev_state) (v : virtio_state) : dev_state :=
  DevState (duart d) (dplic d) v.

Lemma uupd_eq (f : uart_id -> uart_state) (i : uart_id) (u : uart_state) :
  uupd f i u i = u.
Proof. unfold uupd. by rewrite decide_True. Qed.
Lemma uupd_ne (f : uart_id -> uart_state) (i j : uart_id) (u : uart_state) :
  j <> i -> uupd f i u j = f j.
Proof. intro H. unfold uupd. by rewrite decide_False. Qed.

Lemma set_duart_eq (d : dev_state) (i : uart_id) (u : uart_state) :
  duart (set_duart d i u) i = u.
Proof. apply uupd_eq. Qed.
Lemma set_duart_ne (d : dev_state) (i j : uart_id) (u : uart_state) :
  j <> i -> duart (set_duart d i u) j = duart d j.
Proof. apply uupd_ne. Qed.

(* Each port answers its OWN window; [uart_decode] is the bus's question,
   and it is what the PLIC and virtio arms below have to be past.  The
   windows are disjoint (0x1000_0000+8 vs 0x1000_a000+8), so the decode is
   a function and not a priority. *)
Definition in_uart (i : uart_id) (a : Z) : bool :=
  (uart_base i <=? a) && (a <? uart_base i + uart_size).
Definition uart_decode (a : Z) : option uart_id :=
  if in_uart Uart0 a then Some Uart0
  else if in_uart Uart1 a then Some Uart1
  else None.

Definition in_plic (a : Z) : bool := (plic_base <=? a) && (a <? plic_base + plic_size).
Definition in_virtio (a : Z) : bool :=
  (virtio_base <=? a) && (a <? virtio_base + virtio_size).

Lemma uart_decode_in (i : uart_id) (a : Z) :
  uart_decode a = Some i -> in_uart i a = true.
Proof.
  unfold uart_decode. destruct (in_uart Uart0 a) eqn:E0.
  { intro H. by injection H as <-. }
  destruct (in_uart Uart1 a) eqn:E1; [|discriminate].
  intro H. by injection H as <-.
Qed.

(* THE TWO SHAPES A NON-UART WINDOW NEEDS.  The PLIC lies wholly below the
   first port; the virtio-mmio window lies in the GAP between the two ports.
   Every leaf about those devices discharges its "not a UART access" side
   condition through one of these. *)
Lemma uart_decode_below (a : Z) : a < uart_base Uart0 -> uart_decode a = None.
Proof.
  intro H. cbn in H.
  assert (E0 : in_uart Uart0 a = false).
  { unfold in_uart. apply andb_false_intro1, Z.leb_gt. cbn. lia. }
  assert (E1 : in_uart Uart1 a = false).
  { unfold in_uart. apply andb_false_intro1, Z.leb_gt. cbn. lia. }
  unfold uart_decode. rewrite E0. rewrite E1. reflexivity.
Qed.

Lemma uart_decode_between (a : Z) :
  uart_base Uart0 + uart_size <= a -> a < uart_base Uart1 ->
  uart_decode a = None.
Proof.
  intros H0 H1. cbn in H0, H1. unfold uart_size in H0.
  assert (E0 : in_uart Uart0 a = false).
  { unfold in_uart, uart_size. apply andb_false_intro2, Z.ltb_ge. cbn. lia. }
  assert (E1 : in_uart Uart1 a = false).
  { unfold in_uart. apply andb_false_intro1, Z.leb_gt. cbn. lia. }
  unfold uart_decode. rewrite E0. rewrite E1. reflexivity.
Qed.

Lemma uart_decode_none (a : Z) :
  uart_decode a = None -> in_uart Uart0 a = false /\ in_uart Uart1 a = false.
Proof.
  unfold uart_decode. destruct (in_uart Uart0 a); [discriminate|].
  destruct (in_uart Uart1 a); [discriminate|]. done.
Qed.

(* The interrupt LEVEL each of this machine's sources is driving.  The
   gateway ([plic_latch]) forwards exactly these; every other PLIC source id
   is permanently low, because nothing is wired to it. *)
Definition dev_irq_level (d : dev_state) (k : N) : bool :=
  match uart_of_irq k with
  | Some i => uart_irq (duart d i)
  | None => if (k =? virtio_irq_id)%N then virtio_irq (dvirtio d) else false
  end.

Lemma dev_irq_level_uart (d : dev_state) (i : uart_id) :
  dev_irq_level d (uart_irq_id i) = uart_irq (duart d i).
Proof. unfold dev_irq_level. by rewrite uart_of_irq_id. Qed.

(* THE BUS NARROWS a wide access to the UART.  Every one of the port's
   registers is a BYTE, so a 2-, 4- or 8-byte access reads (or writes) the
   ONE register its address names -- zero-extended on the way back, low byte
   taken on the way in.  It does NOT gather consecutive registers into a
   word, which is what the machine does and is worth stating, because the
   guess a reader makes is the other one.

   The model used to decode the window at width 1 and REFUSE everything else,
   which is finding 9: all eight registers sit inside one aligned doubleword,
   so `lw` of the status word is a thing real drivers do, and against the old
   model it was a STUCK machine. *)
Definition uart_dev_read (d : dev_state) (i : uart_id) (off : Z) (k : N)
  : option (bv k * dev_state) :=
  match uart_read (duart d i) off with
  | Some (b, u') => Some (Z_to_bv k (bv_unsigned b), set_duart d i u')
  | None => None
  end.

Definition uart_dev_write (d : dev_state) (i : uart_id) (off : Z) (b : bv 8)
  : option dev_state :=
  match uart_write (duart d i) off b with
  | Some u' => Some (set_duart d i u')
  | None => None
  end.

(* An MMIO READ transaction: [n]-byte read at physical address [pa].
   Serviced directly by the device; the UART decodes any width (one byte
   register, narrowed as above), the PLIC 4-byte accesses.  Any other
   width/offset is STUCK (None). *)
Definition dev_read (d : dev_state) (pa : Arch.pa) (n : N)
  : option (bv (8 * n) * dev_state) :=
  let a := uint pa in
  match uart_decode a with
  | Some i =>
    match n return option (bv (8 * n) * dev_state) with
    | 1%N => match uart_read (duart d i) (a - uart_base i) with
             | Some (b, u') => Some (b, set_duart d i u')
             | None => None
             end
    | 2%N => uart_dev_read d i (a - uart_base i) _
    | 4%N => uart_dev_read d i (a - uart_base i) _
    | 8%N => uart_dev_read d i (a - uart_base i) _
    | _ => None
    end
  | None =>
  if in_plic a then
    match n return option (bv (8 * n) * dev_state) with
    | 4%N => match plic_read (dplic d) (a - plic_base) with
             | Some (w, p') => Some (w, set_dplic d p')
             | None => None
             end
    | _ => None
    end
  else if in_virtio a then
    (* virtio-mmio registers are all 32 bits wide, and none of them is
       read-sensitive: the device is left alone by a read.  A NARROWER access
       is not an error but it is not a register read either -- the transport
       is 32-bit and the machine answers zero (finding 15: the model used to
       be STUCK, so a driver that read a status byte with [lb] had no model
       execution). *)
    match n return option (bv (8 * n) * dev_state) with
    | 4%N => match virtio_read (dvirtio d) (a - virtio_base) with
             | Some w => Some (w, d)
             | None => None
             end
    | 1%N => Some (Z_to_bv _ 0, d)
    | 2%N => Some (Z_to_bv _ 0, d)
    | _ => None
    end
  else None
  end.

(* An MMIO WRITE transaction: writes are sent to the device individually
   (they do not accumulate in any cache) and take effect immediately. *)
Definition dev_write (d : dev_state) (pa : Arch.pa) (n : N) (v : bv (8 * n))
  : option dev_state :=
  let a := uint pa in
  match uart_decode a with
  | Some i =>
    match n return bv (8 * n) -> option dev_state with
    | 1%N => fun v => match uart_write (duart d i) (a - uart_base i) v with
                      | Some u' => Some (set_duart d i u')
                      | None => None
                      end
    | 2%N => fun v => uart_dev_write d i (a - uart_base i) (Z_to_bv 8 (bv_unsigned v))
    | 4%N => fun v => uart_dev_write d i (a - uart_base i) (Z_to_bv 8 (bv_unsigned v))
    | 8%N => fun v => uart_dev_write d i (a - uart_base i) (Z_to_bv 8 (bv_unsigned v))
    | _ => fun _ => None
    end v
  | None =>
  if in_plic a then
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
    (* ...and a narrow WRITE reaches no register: it is dropped, which is
       what the machine does with it (finding 15). *)
    | 1%N => fun _ => Some d
    | 2%N => fun _ => Some d
    | _ => fun _ => None
    end v
  else None
  end.

(* The levels the PLIC drives on hart [h]'s two external-interrupt pins.  Each
   is its own CONTEXT's notification, which is why the model has both: the
   controller does not know which pin is which, it drives every context it
   has, and the board wires context 2h to hart h's M pin and 2h+1 to its S
   pin.  [RiscvLang.plic_step] has one wire arm per pin. *)
Definition dev_seip (d : dev_state) (h : nat) : bool :=
  plic_eip (dplic d) (plic_sctx h).
Definition dev_meip (d : dev_state) (h : nat) : bool :=
  plic_eip (dplic d) (plic_mctx h).

(* No CPU-side MMIO transaction moves the disk IMAGE (crash.md): reads
   advance at most the UART's rx FIFO, and the virtio window's writes go
   through [virtio_write], which never touches [v_disk] -- not even the
   reset command.  These two are what let the hart-side base rules FRAME
   [state_interp]'s durable disk conjunct. *)
Lemma dev_read_v_disk (d : dev_state) (pa : Arch.pa) (n : N)
    (w : bv (8 * n)) (d' : dev_state) :
  dev_read d pa n = Some (w, d') ->
  v_disk (dvirtio d') = v_disk (dvirtio d).
Proof.
  unfold dev_read, uart_dev_read. intros H.
  repeat (case_match; try discriminate); simplify_eq; cbn; reflexivity.
Qed.

Lemma dev_write_v_disk (d : dev_state) (pa : Arch.pa) (n : N)
    (v : bv (8 * n)) (d' : dev_state) :
  dev_write d pa n v = Some d' ->
  v_disk (dvirtio d') = v_disk (dvirtio d).
Proof.
  unfold dev_write, uart_dev_write. intros H.
  repeat (case_match; try discriminate); simplify_eq; cbn;
    eauto using virtio_write_disk.
Qed.

(* ---------------------------------------------------------------------- *)
(* 4. Power-on state: FIFOs empty, everything masked/zero.                  *)
(*                                                                         *)
(*    The two registers that are NOT zero at power-on are the board's, not  *)
(*    the chip's: this port comes up with MCR bit 3 (OUT2) asserted and the *)
(*    divisor set for 9600 baud.  A bare 16550's master reset clears both,  *)
(*    but they are what the machine this development is a model OF reports  *)
(*    -- and OUT2 in particular is the pin that would gate the interrupt    *)
(*    onto an ISA bus, which this board does not have, so nothing here      *)
(*    reads it.                                                            *)
(* ---------------------------------------------------------------------- *)

Definition uart_mcr_reset : Z := 0x08.       (* OUT2 *)
Definition uart_divisor_reset : Z := 0x0c.   (* 9600 baud in DLL, DLM = 0 *)

Definition uart0_state : uart_state :=
  UartState [] [] [] [] byte0 byte0 byte0
            (Z_to_bv 8 uart_divisor_reset) byte0
            (Z_to_bv 8 uart_mcr_reset) byte0 byte0 false.
(* BOTH PORTS COME UP THE SAME WAY: they are the same chip on the same
   board, so the power-on state is one definition read at either index. *)
Definition uarts0_state : uart_id -> uart_state := fun _ => uart0_state.
Definition plic0_state : plic_state :=
  PlicState (fun _ => Z_to_bv 32 0) (fun _ => false) (fun _ => false)
            (fun _ _ => Z_to_bv 32 0) (fun _ => Z_to_bv 32 0).
Definition dev0_state : dev_state :=
  DevState uarts0_state plic0_state virtio0_state.
