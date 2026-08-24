(* UartRegs.v -- the eight registers, and the interrupt-status semantics.
   EVERY OBSERVATION AGREES.  This file used to record five divergences
   (findings 6, 7 and 8); each of them was a modelling shortcut, and each is
   now gone from [DevModel.v] rather than from this file.

   Source: tools/vtest/tests/uart_regs.S.  Capture: UartRegsGen.v.

   Three questions in one program:

   (a) offsets 4 (MCR), 6 (MSR) and 7 (SCRATCH).  [uart_read] used to return
       [byte0] for all three and [uart_write] to accept and discard.  Not
       getting stuck was the right call -- a driver may touch them -- but a
       register that reads back zero is not a register: the standard 16550
       PRESENCE TEST is a write to the scratch register and a read-back, and
       under the old model it could not succeed.  All three are real now
       (MCR five bits of storage, MSR the port's modem inputs, SCRATCH a
       byte), and MCR's loopback bit has its own test, UartLoop.v.

   (b) the ISR (offset 2).  [uart_isr] used to be 0xc0 + (rx ? 4 : tx ? 2 :
       1): bits 7:6 (FIFOs enabled) UNCONDITIONALLY, and the transmit
       interrupt as a LEVEL.  Both are fixed: bits 7:6 are FCR bit 0, and the
       transmit interrupt is the latch [u_thri], which an ISR read clears.
       The program reads the ISR twice in a row with IER bit 1 set and looks
       at the difference; it is there, on both machines, and it is the same
       difference.

   (c) the FCR (offset 2, write): bit 1 clears the rx FIFO, bit 2 the tx
       FIFO.  A FIFO-clearing write must not break the transmitter, and does
       not: OK goes out afterwards on both machines. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list bitvector.definitions.
Require Import VTest UartRegsGen.
Local Open Scope Z_scope.

Definition regs_run : option mstate := run_until 50000 (start uart_regs_text).

(* result-region offsets, mirroring tools/vtest/tests/uart_regs.S *)
Definition regs_offs : list nat :=
  [4;   (* progress marker: 3 = the whole program ran *)
   8;   (* offset 7, SCRATCH, after storing 0x5a       0x5a *)
   12;  (* offset 4, MCR, after storing DTR|RTS           3 *)
   16;  (* offset 6, MSR                               0xb0 *)
   20;  (* ISR at reset, IER = 0, FIFOs off            0x01 *)
   24;  (* ISR after FCR = 0x07 (FIFO enable + clear)  0xc1 *)
   28;  (* ISR with IER = 0x02, FIRST read             0xc2 *)
   32;  (* ISR with IER = 0x02, SECOND read            0xc1 *)
   36;  (* IER read back                                  2 *)
   40;  (* LSR after the FIFO-clearing FCR write       0x60 *)
   44]%nat. (* LSR after OK has drained                0x60 *)

(* ---------------------------------------------------------------------- *)
(* 1. Every field, and the serial channel.                                 *)
(*                                                                         *)
(*    ONE lemma, so the model runs once: the RHS is a [Definition] over the *)
(*    capture, which [solve_vtest] can then name without a second           *)
(*    evaluation.                                                           *)
(* ---------------------------------------------------------------------- *)

Definition regs_expect :=
  ((fun o => cap_word uart_regs_qemu_result o) <$> regs_offs,
   uart_regs_qemu_serial).

Lemma uart_regs_agrees :
  ((fun o => res_word regs_run o) <$> regs_offs,
   serial_of regs_run) = regs_expect.
Proof. solve_vtest regs_expect. Qed.

(* The serial half of that is the (c) result: the transmitter still works
   after an FCR write that clears both FIFOs.  Both machines put out OK. *)

(* ---------------------------------------------------------------------- *)
(* 2. What each field rules out, now that each of them is a fact about the  *)
(*    device rather than a note about the model.                            *)
(*                                                                         *)
(* (a) SCRATCH, offset 7 (+8): 0x5a back.  A byte of storage with no        *)
(*     semantics at all, which is what makes it useful: a driver that       *)
(*     probes for its UART writes a pattern here and reads it back, and     *)
(*     against the old model that probe always failed, so a driver that     *)
(*     looks before it leaps had no model execution.  xv6 does not probe,   *)
(*     which is why nothing had noticed.                                    *)
(*                                                                         *)
(* (b) MCR, offset 4 (+12): 3 back from a store of DTR|RTS.  UartLoop.v     *)
(*     takes this further -- five bits of storage, and bit 4 with real      *)
(*     semantics.                                                           *)
(*                                                                         *)
(* (c) MSR, offset 6 (+16): 0xb0 = DCD|DSR|CTS, this port's idle modem      *)
(*     inputs.  A driver that waits for CTS before transmitting -- ordinary *)
(*     for a real serial port -- used to wait forever in the model.  The    *)
(*     four DELTA bits below them are zero and stay zero: nothing moves     *)
(*     these lines, so there is no transition to report.                    *)
(*                                                                         *)
(* (d) The ISR's FIFO bits, +20 versus +24: 0x01 before the driver's own    *)
(*     FCR write and 0xc1 after it.  Bits 7:6 mean the FIFOs are ENABLED,   *)
(*     which is true exactly when FCR bit 0 has been set; the old model      *)
(*     added 0xc0 unconditionally and so claimed FIFOs before anyone         *)
(*     enabled them.  The pair is what pins it: either field alone is passed *)
(*     by a model that hardcodes the other answer.                          *)
(*                                                                         *)
(* (e) THE LATCH, +28 versus +32: 0xc2 then 0xc1, from two ISR reads with   *)
(*     nothing in between.  This is the one DevModel.v used to predict in    *)
(*     writing.  The transmit interrupt is not a level -- it is armed when   *)
(*     the transmitter falls idle (or, as here, when IER bit 1 is written    *)
(*     while it already is) and DISARMED by the ISR read that reports it.    *)
(*     Under the old level model both reads said 0xc2, so a driver that      *)
(*     acknowledges its transmit interrupt by reading the ISR -- rather      *)
(*     than by feeding the transmitter -- livelocked and could not be        *)
(*     verified.  Note what +28 also pins: the latch is ARMED BY THE IER     *)
(*     WRITE.  The transmitter was already idle and stays idle, so there is  *)
(*     no edge afterwards; a model that only armed on the falling edge of    *)
(*     the FIFO would report 0xc1 here and never interrupt at all.          *)
(* ---------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------- *)
(* 4. The FCR clear, and the one thing the test could NOT observe.         *)
(*                                                                         *)
(*    [uart_write] at offset 2 with bit 2 set replaces [u_tx] with [], so   *)
(*    it DISCARDS bytes the driver had already pushed and the device had    *)
(*    not yet transmitted -- [uart_acc] SHRINKS, which is why DevModel.v    *)
(*    carries [uart_write_2_stable] with a [u_tx u = []] premise rather     *)
(*    than an unconditional stability lemma.  The program cannot exhibit    *)
(*    that: under [VSched.settle] the tx FIFO is drained after every        *)
(*    instruction, so it is always empty by the time the FCR store issues.  *)
(*    Stated off the model instead, at a state a longer schedule reaches.   *)
(* ---------------------------------------------------------------------- *)

Definition u_queued : uart_state :=
  match uart_write uart0_state 0 (Z_to_bv 8 0x41) with
  | Some u => u | None => uart0_state end.

Definition u_cleared : uart_state :=
  match uart_write u_queued 2 (Z_to_bv 8 0x06) with
  | Some u => u | None => u_queued end.

(* the byte was accepted... *)
Lemma uart_regs_fcr_before : bv_unsigned <$> uart_acc u_queued = [0x41].
Proof. solve_vtest ([0x41] : list Z). Qed.

(* ...and the FIFO clear threw it away, unsent. *)
Lemma uart_regs_fcr_discards : bv_unsigned <$> uart_acc u_cleared = [].
Proof. solve_vtest (@nil Z). Qed.

(* ...and so does ENABLING them, which is the other flush and the one no
   program in the suite can show either: FCR bit 0 CHANGING flushes both
   FIFOs, so a driver that turns the FIFOs on at the top of its init loses
   whatever had already arrived.  Measured on the machine -- it is why
   uart_rx.S deliberately leaves them off, see that file's header -- and
   modelled since. *)
Definition u_arrived : uart_state :=
  match uart_rx_push uart0_state (Z_to_bv 8 0x42) with
  | Some u => u | None => uart0_state end.

Definition u_fifos_on : uart_state :=
  match uart_write u_arrived 2 (Z_to_bv 8 0x01) with   (* enable, no clear bits *)
  | Some u => u | None => u_arrived end.

Lemma uart_regs_fifo_enable_flushes :
  (bv_unsigned <$> u_rx u_arrived, bv_unsigned <$> u_rx u_fifos_on)
  = ([0x42], @nil Z).
Proof. solve_vtest ([0x42] : list Z, @nil Z). Qed.
