(* UartIrqTx.v -- the UART as an INTERRUPT SOURCE, transmit side, all the way
   into mip.  THE WHOLE CHAIN AGREES; the only divergences are the two ISR
   ones this area already had.

   Source: tools/vtest/tests/uart_irq_tx.S.  Capture: UartIrqTxGen.v.

   Four model components in series, and the first of them had never been
   driven by any test: [uart_tx_int] (IER bit 1 AND the tx FIFO empty),
   [uart_irq]/[dev_irq_level] (that level on PLIC source 10),
   [plic_latch] (the per-source gateway) and [plic_step] (the wire onto hart
   0's sig_seip).  DiskIntr.v drives the last three from source 1; nothing in
   the suite had ever raised source 10, so this is the first evidence that
   the model's UART is wired to the interrupt controller at all -- and that
   it is wired to the RIGHT source, since the test enables bit 10 alone and
   the claim has to hand back 10.

   The program is M-mode with interrupts disabled throughout, so nothing
   traps: every step is polled.  That is also what makes the model's
   deliberate PROPAGATION DELAY testable -- the gateway latch and the wire
   are the device's own steps, not side effects of the store to IER -- so
   the test spins on the PLIC pending bit rather than reading it once, and
   would still pass if the delay were longer and fail if the model had made
   the pin synchronous. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest UartIrqTxGen.
Local Open Scope Z_scope.

Definition irq_tx_run : option mstate := run_until 50000 (start uart_irq_tx_text).

(* result-region offsets, mirroring tools/vtest/tests/uart_irq_tx.S *)
Definition irq_tx_agree_offs : list nat :=
  [4;   (* progress marker: 4 = the whole program ran *)
   8;   (* LSR at rest                            0x60 *)
   12; 16;   (* PLIC pending / mip&SEIP with IER = 0        0, 0 *)
   24; 28;   (* ...and after IER bit 1 is set           0x400, 0x200 *)
   36;  (* the ISR cause with the FIFO bits masked off     2 = THRE *)
   40;  (* what the S-context claim returned              10 *)
   44; 48;   (* PLIC pending / mip after the claim            0, 0 *)
   52; 56;   (* ...and after IER bit 1 is cleared and the source completed *)
   68; 72]%nat. (* pending / mip after the two back-to-back ISR reads *)

Definition irq_tx_diverge_offs : list nat :=
  [20;  (* ISR with IER = 0 *)
   32;  (* ISR identifying THRE *)
   60;  (* ISR, IER bit 1 set again, first read *)
   64]%nat. (* ...second read, nothing in between *)

(* ---------------------------------------------------------------------- *)
(* 1. THE CHAIN AGREES, step for step.                                     *)
(*                                                                         *)
(*    ONE lemma, so the model runs once; the RHS is a [Definition] over the *)
(*    capture so naming it in [solve_vtest] does not cost a second run.     *)
(* ---------------------------------------------------------------------- *)

Definition irq_tx_expect :=
  (fun o => cap_word uart_irq_tx_qemu_result o) <$> irq_tx_agree_offs.

Lemma uart_irq_tx_agrees :
  (fun o => res_word irq_tx_run o) <$> irq_tx_agree_offs = irq_tx_expect.
Proof. solve_vtest irq_tx_expect. Qed.

(* Spelled out, because this is the answer to the question the test was
   written to ask -- does the UART raise its interrupt all the way into mip,
   on both machines?  Yes, and identically:

     +12/+16  IER = 0            pending 0,      mip&SEIP 0
     +24/+28  IER bit 1 set      pending 0x400,  mip&SEIP 0x200
     +36      the cause          2 (THRE)
     +40      the claim          10  -- the UART's source id, not the disk's
     +44/+48  after the claim    pending 0,      mip&SEIP 0
     +52/+56  condition removed
              and completed      pending 0,      mip&SEIP 0

   So [uart_tx_int], [dev_irq_level]'s source-10 wiring, [plic_latch] and
   [plic_step] are all faithful on this path.  What it rules out: the UART's
   level never reaching the gateway; reaching it on the wrong source id
   (bit 10 alone is enabled, so any other id would leave pending at 0 and
   the claim at 0); the wire not driving SEIP; the claim not clearing
   pending; and -- +52/+56 -- the line failing to DROP when IER bit 1 goes
   away, which would show up as the source re-latching after the complete. *)

(* ---------------------------------------------------------------------- *)
(* 2. What diverges: the ISR, and only the ISR.  Pinned on both sides.     *)
(* ---------------------------------------------------------------------- *)

Definition irq_tx_model_diverging : list Z := [0xc1; 0xc2; 0xc2; 0xc2].
Definition irq_tx_qemu_diverging  : list Z := [0x01; 0x02; 0x02; 0x01].

Lemma uart_irq_tx_model_diverging :
  (fun o => res_word irq_tx_run o) <$> irq_tx_diverge_offs
  = irq_tx_model_diverging.
Proof. solve_vtest irq_tx_model_diverging. Qed.

Lemma uart_irq_tx_qemu_diverging :
  (fun o => cap_word uart_irq_tx_qemu_result o) <$> irq_tx_diverge_offs
  = irq_tx_qemu_diverging.
Proof. solve_vtest irq_tx_qemu_diverging. Qed.

Lemma uart_irq_tx_really_diverges :
  irq_tx_model_diverging <> irq_tx_qemu_diverging.
Proof. discriminate. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. Both of them are UartRegs.v's, re-exhibited on the interrupt path;   *)
(*    neither is new, and neither is about the interrupt CHAIN.            *)
(*                                                                         *)
(* (a) Bits 7:6.  [uart_isr] adds 0xc0 (FIFOs enabled) unconditionally,    *)
(*     where the hardware sets those bits exactly when FCR bit 0 has been  *)
(*     set -- and this program never writes FCR, deliberately, because a   *)
(*     FIFO-enable write also flushes the FIFOs.  So every ISR field here  *)
(*     is the model's 0xc0 plus the same low nibble QEMU reports.  That is  *)
(*     why +36 exists: it is the same read masked to bits 3:0, i.e. the    *)
(*     CAUSE, and the cause agrees.  INCOMPLETENESS (UartRegs.v (d)).      *)
(*                                                                         *)
(* (b) +60 versus +64, the ISR read TWICE with nothing in between: the     *)
(*     model says 0xc2 both times, QEMU says 0x02 then 0x01.  This is the  *)
(*     LEVEL-versus-LATCH choice DevModel.v states in the comment above    *)
(*     [uart_isr], and [uart_read_isr] proves the model's read changes      *)
(*     nothing.  INCOMPLETENESS (UartRegs.v (e)): the model raises MORE     *)
(*     interrupts than the hardware, never fewer, so a driver that          *)
(*     tolerates a spurious one is fine and a driver that uses the ISR      *)
(*     read AS its acknowledgement cannot be verified.                      *)
(*                                                                         *)
(*     WHAT IS NEW HERE, and it is a POSITIVE result, is +68/+72.  QEMU's   *)
(*     ISR read drops the UART's line, and yet its PLIC still reports       *)
(*     source 10 pending and SEIP still set -- because the PLIC gateway     *)
(*     LATCHES: once forwarded, a request stays pending until it is         *)
(*     claimed, whatever the source line does afterwards.  Our [plic_latch] *)
(*     is written that way too, so the two agree even though they got there *)
(*     for different reasons (the model's line never dropped at all).  The  *)
(*     consequence worth recording: the level model does NOT cost an extra  *)
(*     PLIC-visible interrupt here, because the second one would have to be *)
(*     re-latched and the gateway refuses while the first is still pending. *)
(* ---------------------------------------------------------------------- *)
