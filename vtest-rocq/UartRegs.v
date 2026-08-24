(* UartRegs.v -- the registers the model does not really implement, and its
   interrupt-status semantics.  FIVE DIVERGENCES, all of them deliberate
   modelling choices, and all of them incompleteness.

   Source: tools/vtest/tests/uart_regs.S.  Capture: UartRegsGen.v.

   Three questions in one program:

   (a) offsets 4 (MCR), 6 (MSR) and 7 (SCRATCH).  [uart_read] returns
       [byte0] for all three and [uart_write] accepts and discards.  Not
       getting stuck is the right call -- a driver may touch them -- but the
       values are not the hardware's.

   (b) the ISR (offset 2).  [uart_isr] is 0xc0 + (rx ? 4 : tx ? 2 : 1): bits
       7:6 (FIFOs enabled) UNCONDITIONALLY, and the THRE interrupt as a
       LEVEL.  The comment above [uart_isr] in DevModel.v states the second
       choice outright -- a real 16550 LATCHES the THRE interrupt and clears
       it on an ISR read -- so this test reads the ISR twice in a row with
       IER bit 1 set and looks at the difference.  It is there.

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
Definition regs_agree_offs : list nat :=
  [4;   (* progress marker: 3 = the whole program ran *)
   24;  (* ISR after FCR = 0x07 (FIFO enable + clear both) *)
   28;  (* ISR with IER = 0x02, FIRST read *)
   36;  (* IER read back *)
   40;  (* LSR after the FIFO-clearing FCR write *)
   44]%nat. (* LSR after OK has drained *)

Definition regs_diverge_offs : list nat :=
  [8;   (* offset 7, SCRATCH *)
   12;  (* offset 4, MCR *)
   16;  (* offset 6, MSR *)
   20;  (* ISR at reset, IER = 0 *)
   32]%nat. (* ISR with IER = 0x02, SECOND read *)

(* ---------------------------------------------------------------------- *)
(* 1. What agrees -- including the serial channel.                         *)
(*                                                                         *)
(*    ONE lemma, so the model runs once: the RHS is a [Definition] over the *)
(*    capture, which [solve_vtest] can then name without a second           *)
(*    evaluation.                                                           *)
(* ---------------------------------------------------------------------- *)

Definition regs_expect :=
  ((fun o => cap_word uart_regs_qemu_result o) <$> regs_agree_offs,
   uart_regs_qemu_serial).

Lemma uart_regs_agrees :
  ((fun o => res_word regs_run o) <$> regs_agree_offs,
   serial_of regs_run) = regs_expect.
Proof. solve_vtest regs_expect. Qed.

(* The serial half of that is the (c) result: the transmitter still works
   after an FCR write that clears both FIFOs.  Both machines put out OK. *)

(* ---------------------------------------------------------------------- *)
(* 2. What does not.  Pinned on BOTH sides.                                *)
(* ---------------------------------------------------------------------- *)

Definition regs_model_diverging : list Z := [0;    0;  0;    0xc1; 0xc2].
Definition regs_qemu_diverging  : list Z := [0x5a; 3;  0xb0; 0x01; 0xc1].

Lemma uart_regs_model_diverging :
  (fun o => res_word regs_run o) <$> regs_diverge_offs = regs_model_diverging.
Proof. solve_vtest regs_model_diverging. Qed.

Lemma uart_regs_qemu_diverging :
  (fun o => cap_word uart_regs_qemu_result o) <$> regs_diverge_offs
  = regs_qemu_diverging.
Proof. solve_vtest regs_qemu_diverging. Qed.

Lemma uart_regs_really_diverges : regs_model_diverging <> regs_qemu_diverging.
Proof. discriminate. Qed.

(* ---------------------------------------------------------------------- *)
(* 3. The five divergences, classified.                                    *)
(*                                                                         *)
(* (a) SCRATCH, offset 7: 0 versus 0x5a.  INCOMPLETENESS.  The scratch      *)
(*     register is architecturally a byte of storage that reads back what   *)
(*     was written, and it exists to be used that way: the standard 16550   *)
(*     PRESENCE TEST is to write a pattern to offset 7 and read it back.    *)
(*     Under this model that test always fails, so a driver that probes for *)
(*     its UART before using it has no model execution in which it finds    *)
(*     one.  xv6 does not probe, which is why nothing has noticed.          *)
(*                                                                         *)
(* (b) MCR, offset 4: 0 versus 3.  INCOMPLETENESS, same shape -- the store  *)
(*     of DTR|RTS is accepted and discarded.  Worth knowing that the model  *)
(*     therefore has NO loopback mode (MCR bit 4), which is the other       *)
(*     standard way to test a 16550, and the only way to exercise the       *)
(*     receive path without a host that types.                              *)
(*                                                                         *)
(* (c) MSR, offset 6: 0 versus 0xb0 (DCD|DSR|CTS, QEMU's idle modem         *)
(*     status).  INCOMPLETENESS.  A driver that waits for CTS before        *)
(*     transmitting -- ordinary for a real serial port -- waits forever in  *)
(*     the model.                                                           *)
(*                                                                         *)
(* (d) The ISR at reset: 0xc1 versus 0x01.  INCOMPLETENESS, and the         *)
(*     narrowest of the five.  Bits 7:6 mean the FIFOs are ENABLED, which   *)
(*     on the hardware is true exactly when FCR bit 0 has been set;         *)
(*     [uart_isr] adds 0xc0 unconditionally, so the model claims FIFOs      *)
(*     before anyone enabled them.  Note field +24: once FCR = 0x07 has     *)
(*     been written the two agree at 0xc1, so this is only about the        *)
(*     window before the driver's own init.                                 *)
(*                                                                         *)
(* (e) The ISR read TWICE with the THRE interrupt enabled: 0xc2 twice       *)
(*     versus 0xc2 then 0xc1.  This is the one DevModel.v predicts in       *)
(*     writing.  [uart_isr] is a pure function of the state and             *)
(*     [uart_read_isr] proves the read does not advance the device, so the  *)
(*     THRE interrupt is a LEVEL that stays asserted while the FIFO is      *)
(*     empty; the hardware LATCHES it and the ISR read is what clears it,   *)
(*     which is why QEMU's second read reports no interrupt pending.        *)
(*                                                                         *)
(*     Classified INCOMPLETENESS rather than defect, and the direction      *)
(*     matters: the model produces MORE interrupts than the hardware, never *)
(*     fewer.  A driver that tolerates a spurious interrupt -- xv6's        *)
(*     uartintr, which just re-checks LSR -- is fine.  A driver that uses   *)
(*     the ISR read AS the acknowledgement, i.e. relies on the interrupt    *)
(*     going away because it read the register, livelocks in the model and  *)
(*     cannot be verified; and no proof against this model can conclude     *)
(*     anything about how MANY interrupts a real 16550 raises.  The value   *)
(*     0xc2 is not one the hardware never produces (it produces it on the   *)
(*     first read), so this is not the [used.ring.len] kind of defect.      *)
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
