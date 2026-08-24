(* UartDlab.v -- the DIVISOR-LATCH ALIASING, and it AGREES on every field.

   Source: tools/vtest/tests/uart_dlab.S.  Capture: UartDlabGen.v.

   This is the highest-value thing to pin down in the UART, because it is the
   one place where the SAME store instruction does two entirely different
   things depending on a bit written earlier.  LCR (offset 3) bit 7 is DLAB;
   while it is set, offset 0 is the divisor latch low byte rather than the
   transmit register and offset 1 is the divisor latch high byte rather than
   IER.  The model implements it in [uart_dlab] and the two DLAB branches of
   [uart_read]/[uart_write], and the device design's [un_dlab] ghost
   (claude-notes/design/device.md) exists solely to let a driver proof know
   which of the two a given store is.  If the model had the polarity or the
   aliasing wrong, every uartinit in the world would be verified against a
   device that transmits its baud divisor.

   THE SERIAL CHANNEL IS WHAT MAKES IT A REAL TEST.  Field +20 says the byte
   went into DLL; only [uart_dlab_serial] says it did NOT also go onto the
   wire.  The program stores 'N' (0x4e) to offset 0 with DLAB set and 'Y'
   (0x59) to the same offset with DLAB clear, and the entire captured serial
   output of the run is the single byte 0x59. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest UartDlabGen.
Local Open Scope Z_scope.

Definition dlab_run : option mstate := run_until 50000 (start uart_dlab_text).

(* Every observation, byte for byte:
     +4  progress marker                                     3
     +8  LCR read back after storing 0x80                    0x80
     +12 offset 0 with DLAB set  = DLL                       0x03
     +16 offset 1 with DLAB set  = DLM                       0x12
     +20 offset 0 after storing 'N' to it, DLAB set          0x4e (it is DLL)
     +24 LCR read back after storing 0x03                    0x03
     +28 offset 1 with DLAB clear = IER                      0    (the DLM
                                                                   stores did
                                                                   not land here)
     +32 offset 0 with DLAB clear = RHR, nothing received    0
     +36 LSR at the end                                      0x60             *)
Lemma uart_dlab_result : result_of dlab_run = uart_dlab_qemu_result.
Proof. solve_vtest uart_dlab_qemu_result. Qed.

(* THE ONE THAT MATTERS: 'N' was aliased away, 'Y' was transmitted, and the
   whole line is one byte. *)
Lemma uart_dlab_serial : serial_of dlab_run = uart_dlab_qemu_serial.
Proof. solve_vtest uart_dlab_qemu_serial. Qed.

(* ---------------------------------------------------------------------- *)
(* What a POSITIVE result rules out here, concretely:                      *)
(*                                                                         *)
(*  - the DLAB polarity being inverted, or read from the wrong bit of LCR   *)
(*    ([uart_dlab] is bit 7 of [u_lcr], and +8/+24 show LCR itself reading  *)
(*    back verbatim, so the test separates the LCR store from the aliasing);*)
(*  - offset 1's aliasing being missed: +16 sees the DLM back while +28     *)
(*    sees IER still 0, so a model that had written IER instead would fail  *)
(*    one of the two;                                                      *)
(*  - the divisor latch and the transmit FIFO being the same storage: +20   *)
(*    reads back the byte, and the serial lemma says it never left;         *)
(*  - the aliasing being STICKY -- clearing DLAB restores THR, which is     *)
(*    what the 'Y' at the end demonstrates;                                *)
(*  - RHR reading anything but 0 when the receive FIFO is empty (+32).      *)
(*    [uart_read] returns [byte0] there rather than getting stuck, and QEMU *)
(*    agrees; note this test is also the only evidence in the suite about   *)
(*    the RECEIVE side, because the runner gives QEMU no serial INPUT.      *)
(* ---------------------------------------------------------------------- *)
