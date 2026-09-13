(* SpecUartintr.v -- the public interface of uartintr, stated independently of
   its proof.  Requires only the definitional layer -- never a whole-function
   proof file -- so every function proof can be checked in parallel.

     void uartintr(int uid);

   A 16550's interrupt handler, called from devintr().  At XV6_REV 163d39b the
   kernel drives TWO ports out of one `struct uart uarts[2]`, so the handler
   gained a PORT INDEX: the contract is parametric in [i : uart_id] and the
   only premise about [uid] is that a0 holds [uart_index i].  Everything the
   handler reaches -- the MMIO window, the sleep channel, the receive hook --
   it reaches through `&uarts[uid]`, which is why [SpecUartPutc.uart_base_word
   i] and [UartTxInv.uart_rx_word i] are premises: the base and the hook are
   LOADED from .data, not compile-time constants, and those two persistent
   VA-tier snapshots are what say what the two words hold.

   It acknowledges the interrupt (an ISR read), then does two independent
   things, both at port [i]:

     TX: if LSR says the transmitter is idle, [wakeup(u)] -- and the sleep
         channel is the ELEMENT `&uarts[uid]` now, not the departed `&tx_chan`;
     RX: drain the receive FIFO one byte at a time via uartgetc() -- which gcc
         still INLINES, so it has no symbol of its own -- and feed each byte to
         `u->rx` IF THAT HOOK IS NON-NULL.

   THE HOOK IS DECIDED PER PORT, NOT AT RUN TIME.  `uarts[0].rx` is
   [consoleintr] and `uarts[1].rx` is 0, both written by the loader and by
   nobody else, so [UartTxInv.uart_rx_word i] settles the `if (u->rx)`
   guard statically: at [Uart0] the `c.jalr` is an ordinary call to
   consoleintr, at [Uart1] the branch is provably taken and the call is dead
   code.  That is what [ui_rx_caps] below expresses -- the console's
   credential is owed only at the port that has one.

   @ KernelSyms.uartintr, 128 bytes, 47 instructions, a 32-byte frame of
   which only THREE slots are written (ra/s0/s1; s2 is no longer used and the
   lowest slot is dead, so it rides the proof existentially).

   THIS IS THE OTHER HALF OF [UartTxInv.tx_res] at port [i].  uartwrite polls
   THRE for itself, so nothing is cashed here: every read this function makes
   is ghost-free as far as the transmitter is concerned
   ([DevModel.uart_read_stable]: no UART read moves [uart_acc], the
   transmitted prefix or DLAB).  The RECEIVE side is not ghost-free -- the RHR
   read POPS the FIFO -- which is what [uart_rx_writer] is for, and it is
   needed AT BOTH PORTS: `uartgetc(u)` runs at port 1 too and discards what it
   pops, so the token is unconditional even though the console credential is
   not.

   WHAT THE CONTRACT SAYS: nothing about the output, at either port.  An
   interrupt handler's job is to leave the caller's state alone, and that is
   what is promised -- every callee-saved register, the interrupt-nesting
   level, and the register file's totality.  The rx loop is UNBOUNDED (the
   device may keep supplying bytes), so the WP is, as always, partial
   correctness.

   Callees: wakeup, and -- at the console port only -- consoleintr. *)
From Stdlib Require Import ZArith List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre lifting.
From iris.base_logic.lib Require Import invariants ghost_var.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Operators_mwords SailStdpp.Values SailStdpp.MachineWord.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvPtsto RiscvLang.
Require Import RegFile.
Require Import RiscvExtras.
Require Import FdSlots.
Require Import ProcGeom.
Require Import InstrBytes KernelText.
Require Import LockRank.
Require Import CalleeSaved.
Require Import IntrDefs.
Require Import WpNext.
Require Import CpuOwn.
Require Import SchedCtx.
Require Import DevModel.
Require Import DiskPtsto WpUart.
Require Import UartsFields.
Require Import UartTxInv.      (* [uart_rx_word]: the VA-tier `uarts[i].rx` *)
Require Import SpecUartPutc.   (* [uart_base_word]: the VA-tier `uarts[i].base` *)
Require Import SpecConsoleintr.
From Kernel Require KernelSyms.
Require Import ProcAvail.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Require Import TsoCtx.


(* ---------------------------------------------------------------------- *)
(* THE PORT-GATED HALF OF THE CREDENTIAL.                                  *)
(* ---------------------------------------------------------------------- *)
(* ONE contract, parametric in the port, that simply SAYS LESS ABOUT PORT 1
   -- not two cloned contracts.  Three of uartintr's four premises are
   port-generic and stay outside this definition ([uart_inv i], the receive
   token, [procs_inv]); only the console's is gated, because only the console
   port has a receive consumer.  [dev_inv] is the CONSOLE BUNDLE
   ([WpUart.dev_inv] = `uart_inv Uart0 ∗ plic_inv ∗ disk_inv ∗ perm_inv`), so
   it cannot even be STATED at the second port with the second port's ghost
   names -- consoleintr is what wants it, and consoleintr is unreachable at
   [Uart1].

   Persistent, so threading it costs a caller nothing. *)
Definition ui_rx_caps `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{XI : CurCtx}
    (i : uart_id) (gu : uart_names) (gv : disk_names) : iProp Σ :=
  match i with
  | Uart0 => (dev_inv gu gv ∗ console_caps gu)%I
  | Uart1 => emp%I
  end.

Global Instance ui_rx_caps_persistent `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{XI : CurCtx}
    i gu gv : Persistent (ui_rx_caps i gu gv).
Proof. destruct i; rewrite /ui_rx_caps; apply _. Qed.


(* uartintr's own frame is 4 slots; the deepest callee is consoleintr at 32
   (wakeup wants 18).  The bound is the MAXIMUM over the ports -- port 1
   reaches only wakeup -- so that one number serves both instances. *)
Notation uartintr_stack := (36%nat) (only parsing).
Definition wp_uartintr_sconf_body `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
    (i : uart_id) (gu : uart_names) (gv : disk_names)
    (gs : list gname)
    (m : regfile) (av lvl : nat) (eb : bool) (pme : mword 64) (b : bool)
    (k : nat) (hl : option (list mobs)) (lks : gset string) :=
  let pcE : mword 64 := mword_of_int KernelSyms.uartintr in
  let ret_tgt := ret_pc (m !!! Regidx (mword_of_int 1 : mword 5)) in
  (* THE PORT, AS THE ARGUMENT REGISTER HOLDS IT.  a0 is the only place the
     index appears; the prologue turns it into `&uarts[uid]` by
     `((uid*4 + uid) << 3) + uarts`, which is [uart_elt i] exactly when a0 is
     [uart_index i]. *)
  m !!! Regidx (mword_of_int 10 : mword 5) = (mword_of_int (uart_index i) : mword 64) ->
  length gs = NPROC ->
  (* the transient noff increment (wakeup's per-proc lock) stays in int range *)
  (Z.of_nat lvl + 2 < 2 ^ 31)%Z ->
  (uartintr_stack <= av)%nat ->
  (* uartintr's cone: it takes no lock of its own, and the lowest rank its
     call tree touches is "cons" (5, LockRank.v), through consoleintr; the
     THRE arm's wakeup call needs only the higher "proc" (11), which
     [locks_below_mono] recovers from this one bound.  Stated at the console's
     floor for both ports: devintr holds nothing, so the premise is free, and
     one number keeps this ONE contract. *)
  locks_below lks "cons" ->
  sie_cap_gpr KT1 m av b pme -∗
  cpu_own lvl eb pme b lks -∗
  kernel_text -∗ pc_is pcE -∗
  (* THE TWO IMMUTABLE FIELDS OF THIS ELEMENT, AT THE TIER AN S-MODE LOAD
     CONSUMES.  [uart_base_word i] is what turns the `c.ld a5,0(a5)` at +0x1e
     (and the `c.ld a4,0(s1)` the rx loop repeats) into "the register holds
     [uart_base i]"; [uart_rx_word i] is what the `c.ld a5,8(s1)` at +0x56
     reads, and it is what decides the `if (u->rx)` guard STATICALLY.

     NOT [UartsFields.uarts_pinned], which is the same pair of facts at the
     RAW PHYSICAL tier ([↦ₚ₈□]).  An S-mode load leaf consumes the
     context-tier [↦₈] and there is NO law crossing the two
     ([DiskInv.phys_win_to_mem] drops the ledger; [KMap.phys_ident_mem] lands
     at [mem_pointsto], not [ctx_pointsto]) -- only the BOOT CHAIN may cross
     them, and it already does ([BootShared.uart_base_word_of_pinned] /
     [uart_rx_word_of_pinned], both ports minted beside [uarts_pinned]).  So
     the credential a DRIVER must be handed is the VA-tier one.  Same
     correction as uartputc_sync's and uartinitone's. *)
  uart_base_word i -∗
  uart_rx_word i -∗
  (* DLAB IS OFF, AT EITHER PORT.  The RHR pop reads offset 0, and offset 0
     with DLAB set is the divisor latch, not the receive register -- so
     [WpSconfUartAccess.wp_uart_rhr_pop_s_sconf_at] takes this and uartintr
     pops AT BOTH PORTS.  At the console it is derivable from
     [ui_rx_caps Uart0]'s [console_caps] (it rides inside [is_txlock]), so
     that caller pays nothing new; at [Uart1] there is no such bundle and the
     fact has to be a premise of its own.  [uartinit] freezes it at both
     ports and hands both out ([SpecUartinit.v]'s post), so the credential
     exists; what does not yet carry it is [SpecDevintr.uart1_caps]. *)
  uart_dlab_off gu -∗
  (* THE DEVICE, PORT-GENERICALLY.  Not the [dev_inv] bundle: this function
     opens port [i]'s invariant and nothing else, and at [Uart1] the bundle
     does not exist.  A console caller projects this with
     [WpUart.dev_inv_uart]. *)
  uart_inv i gu -∗
  (* the running-thread bundle (wakeup, at both ports) *)
  procs_inv gs -∗
  (* the console's own credential -- at the console only.  See [ui_rx_caps]. *)
  ui_rx_caps i gu gv -∗
  (* THE RECEIVE TOKEN, AT BOTH PORTS.  uartintr's rx drain is the popper of
     port [i]'s receive FIFO -- uartgetc's RHR read pops one byte per
     iteration, at port 1 as much as at port 0 -- and the token is what says
     no other hart is doing the same.  What differs between the ports is what
     is DONE with the byte, not whether it is popped: at [Uart1] the hook is
     null and the byte is dropped on the floor.  devintr hands the token over
     out of plic_claim's post and takes it back for plic_complete. *)
  uart_rx_writer gu k hl -∗
  wp_next b pme (fun (CID : CpuId) =>
    ∀ mf : regfile,
      ⌜ callee_saved m mf /\ (forall r : regidx, r ∈ dom (rf_to_gmap mf)) ⌝ -∗
      sie_cap_gpr KT1 mf av b pme -∗
      cpu_own lvl eb pme b lks -∗
      pc_is ret_tgt -∗
      (∃ (k' : nat) (hl' : option (list mobs)), uart_rx_writer gu k' hl') -∗
      WP (Loop : expr riscv_lang)) -∗
  WP (Loop : expr riscv_lang).

Module Type UARTINTR.
  Parameter wp_uartintr_sconf :
    forall `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !fdslotG Σ, !irefslotG Σ, !pavG Σ, !wchG Σ} `{GEN : GenId} `{CID : CpuId} `{XI : CurCtx}
      (i : uart_id) (gu : uart_names) (gv : disk_names)
      (gs : list gname)
      (m : regfile) (av lvl : nat) (eb : bool) (pme : mword 64) (b : bool)
      (k : nat) (hl : option (list mobs)) (lks : gset string),
      wp_uartintr_sconf_body i gu gv gs m av lvl eb pme b k hl lks.
End UARTINTR.
