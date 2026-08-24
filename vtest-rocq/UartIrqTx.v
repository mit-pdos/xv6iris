(* UartIrqTx.v -- the UART as an INTERRUPT SOURCE, transmit side, all the way
   into mip.  THE WHOLE CHAIN AGREES, and since the ISR became a real 16550
   ISR (findings 7 and 8) so does every field of it, including the two
   back-to-back reads at the end.

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
Definition irq_tx_offs : list nat :=
  [4;   (* progress marker: 4 = the whole program ran *)
   8;   (* LSR at rest                            0x60 *)
   12; 16;   (* PLIC pending / mip&SEIP with IER = 0        0, 0 *)
   20;  (* ISR with IER = 0                       0x01 *)
   24; 28;   (* ...and after IER bit 1 is set           0x400, 0x200 *)
   32;  (* ISR identifying THRE                   0x02 *)
   36;  (* the ISR cause with the FIFO bits masked off     2 = THRE *)
   40;  (* what the S-context claim returned              10 *)
   44; 48;   (* PLIC pending / mip after the claim            0, 0 *)
   52; 56;   (* ...and after IER bit 1 is cleared and the source completed *)
   60;  (* ISR, IER bit 1 set again, first read   0x02 *)
   64;  (* ...second read, nothing in between     0x01 *)
   68; 72]%nat. (* pending / mip after those two reads *)

(* ---------------------------------------------------------------------- *)
(* 1. THE CHAIN AGREES, step for step.                                     *)
(*                                                                         *)
(*    ONE lemma, so the model runs once; the RHS is a [Definition] over the *)
(*    capture so naming it in [solve_vtest] does not cost a second run.     *)
(* ---------------------------------------------------------------------- *)

Definition irq_tx_expect :=
  (fun o => cap_word uart_irq_tx_qemu_result o) <$> irq_tx_offs.

Lemma uart_irq_tx_agrees :
  (fun o => res_word irq_tx_run o) <$> irq_tx_offs = irq_tx_expect.
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
(* 2. The ISR fields, which is where this test used to record two           *)
(*    divergences and now records two facts.                                *)
(*                                                                          *)
(* (a) Bits 7:6.  This program never writes FCR -- deliberately, since a    *)
(*     FIFO-enable write also flushes -- so the FIFOs are OFF throughout    *)
(*     and every ISR field here reads as the bare cause: 0x01, 0x02, 0x02,  *)
(*     0x01.  The old model added 0xc0 to all four (finding 7), which is    *)
(*     why +36 exists at all: it is +32 masked to bits 3:0, i.e. the CAUSE  *)
(*     alone, which agreed even then.  Both now agree unmasked.             *)
(*                                                                          *)
(* (b) +60 versus +64, the ISR read TWICE with nothing in between: 0x02     *)
(*     then 0x01, on both machines.  The transmit interrupt is a LATCH and  *)
(*     the ISR read that reports it is what clears it (finding 8; the old   *)
(*     model said 0xc2 both times, and [uart_read_isr] proved its read      *)
(*     changed nothing -- that lemma is now [uart_read_isr_acks], which     *)
(*     proves the opposite).                                                *)
(*                                                                          *)
(*     AND THE GATEWAY IS UNMOVED BY IT, +68/+72, which was a positive      *)
(*     result before the fix and stays one after: the ISR read drops the    *)
(*     UART's line, and yet the PLIC still reports source 10 pending and    *)
(*     SEIP still set, because the gateway LATCHES -- once forwarded, a     *)
(*     request stays pending until it is claimed, whatever the source line  *)
(*     does afterwards.  [plic_latch] is written that way, and now the two  *)
(*     machines get there for the SAME reason (the model's line drops too), *)
(*     where before the fix they agreed for different ones.                 *)
(* ---------------------------------------------------------------------- *)
