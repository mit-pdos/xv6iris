(* UartIrqRx.v -- the UART as an INTERRUPT SOURCE, receive side, all the way
   into mip, and THE FIRST TEST IN THE SUITE THAT RECEIVES ANYTHING.

   Source: tools/vtest/tests/uart_irq_rx.S.  Capture: UartIrqRxGen.v.

   The host pushes one byte, 0x41, into QEMU's serial socket (the test's
   `vtest: serial_in=` directive).  On the model side that byte is NOT an
   automatic event: receiving is the only externally-driven thing in the
   whole suite, and [VSched.settle] deliberately does not invent it.  It is
   a SCHEDULE choice -- the [SUartRx] arm, i.e. [DevModel.uart_rx_push] --
   and this file makes it explicitly, before the program starts.  WHERE it
   is delivered is a witness like any other: the program spins on LSR bit 0
   until the byte is there, so any point at or before that spin gives the
   same run, and delivering it first is simply the shortest witness.

   ONE byte on purpose.  With the FIFOs disabled QEMU's 16550 accepts one
   character at a time and re-offers the next asynchronously, so a two-byte
   injection would let the drain loop see the FIFO empty and the interrupt
   re-raise afterwards -- nondeterminism with nothing to do with the
   subject.  And the FIFOs are deliberately not enabled, because a FCR write
   that flips FIFO-enable also flushes the receive FIFO and would race with
   the host's byte.

   EVERYTHING AGREES, the ISR fields included: they used to differ by
   exactly 0xc0, which was finding 7 (bits 7:6 set whether or not FCR bit 0
   had been written), and [DevModel.uart_isr] now reads that bit. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest UartIrqRxGen.
Local Open Scope Z_scope.

(* THE WITNESS: the host's byte, delivered as a device step. *)
Definition irq_rx_start : option mstate :=
  srun [SUartRx 0x41] (start uart_irq_rx_text).

Definition irq_rx_run : option mstate :=
  match irq_rx_start with Some s => run_until 50000 s | None => None end.

(* result-region offsets, mirroring tools/vtest/tests/uart_irq_rx.S *)
Definition irq_rx_offs : list nat :=
  [4;   (* progress marker: 3 = the whole program ran *)
   8;   (* LSR with the byte waiting             0x61 = DR|THRE|TEMT *)
   12; 16;   (* PLIC pending / mip&SEIP with IER = 0      0, 0 *)
   24; 28;   (* ...and after IER bit 0 is set         0x400, 0x200 *)
   36;  (* the ISR cause with the FIFO bits masked off   4 = rx available *)
   40;  (* what the S-context claim returned            10 *)
   44; 48;   (* PLIC pending / mip after the claim          0, 0 *)
   52; 56;   (* the byte out of RHR, and how many came      0x41, 1 *)
   60;  (* LSR after draining                          0x60: DR gone *)
   68; 72;   (* pending / mip after the PLIC complete      0, 0 *)
   20;  (* ISR with IER = 0                            0x01 *)
   32;  (* ISR identifying rx-available                0x04 *)
   64]%nat. (* ISR after the FIFO was drained          0x01 *)

(* ---------------------------------------------------------------------- *)
(* 1. THE CHAIN AGREES, step for step -- and so does the byte itself.      *)
(* ---------------------------------------------------------------------- *)

Definition irq_rx_expect :=
  (fun o => cap_word uart_irq_rx_qemu_result o) <$> irq_rx_offs.

Lemma uart_irq_rx_agrees :
  (fun o => res_word irq_rx_run o) <$> irq_rx_offs = irq_rx_expect.
Proof. solve_vtest irq_rx_expect. Qed.

(* Spelled out:

     +8       a byte waiting     LSR 0x61 (DR set)
     +12/+16  IER = 0            pending 0,      mip&SEIP 0
     +24/+28  IER bit 0 set      pending 0x400,  mip&SEIP 0x200
     +36      the cause          4 (received data available)
     +40      the claim          10
     +44/+48  after the claim    pending 0,      mip&SEIP 0
     +52/+56  RHR gave back      0x41, exactly once
     +60      after draining     LSR 0x60 (DR gone)
     +68/+72  after complete     pending 0,      mip&SEIP 0

   So the receive half of [uart_rx_ready], [uart_rx_int], the RHR pop in
   [uart_read] offset 0, and the same source-10 interrupt path as
   UartIrqTx.v are all faithful.  What it rules out beyond the transmit
   test: the rx interrupt firing on the WRONG IER bit (+12 shows it silent
   with IER = 0 while a byte is already waiting, so a model that ignored
   IER, or read bit 1 for it, would show pending here); RHR not popping, or
   popping more than one byte (+56); and the rx line failing to DROP when
   the FIFO empties, which +68/+72 would catch as a re-latch after the
   complete.

   It is also the only evidence in the suite that [uart_rx_push] and the
   [SUartRx] schedule arm do what the hardware does at all. *)

(* ---------------------------------------------------------------------- *)
(* 2. The ISR fields, which used to be this file's three divergences.      *)
(*                                                                        *)
(*    All three differed by exactly 0xc0: [uart_isr] set bits 7:6 (FIFOs   *)
(*    enabled) unconditionally where the hardware sets them only once FCR  *)
(*    bit 0 has been written, and this program never writes FCR (see the   *)
(*    header: a FIFO-enable write flushes the receive FIFO and would race  *)
(*    with the host's byte).  With the bits taken from the register, the   *)
(*    three read 0x01, 0x04 and 0x01 on both machines -- and +36, the same *)
(*    read masked to bits 3:0, is now redundant rather than load-bearing.  *)
(*                                                                        *)
(*    THE LATCH FIX DOES NOT REACH THIS PATH, which is worth stating       *)
(*    positively: the receive interrupt is a LEVEL on the real hardware    *)
(*    too -- it goes away when the FIFO is emptied, not when the ISR is    *)
(*    read -- so +64 (the ISR after the drain) is 0x01 for the same reason  *)
(*    on both sides, and the model's [uart_rx_int] needed no change.  Of   *)
(*    the two interrupt conditions only the transmit one was modelled with *)
(*    the wrong kind of edge, and UartIrqTx.v is where that shows.         *)
(* ---------------------------------------------------------------------- *)
