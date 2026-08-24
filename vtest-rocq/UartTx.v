(* UartTx.v -- the 16550's TRANSMIT path, and it AGREES on every channel.

   Source: tools/vtest/tests/uart_tx.S.  Capture: UartTxGen.v.

   THE THIRD OBSERVATION CHANNEL.  A `uart` test has one the disk tests do
   not: what the host actually saw on the serial line.  vtest.py captures
   QEMU's -serial file as [uart_tx_qemu_serial], and the model side is
   [VTest.serial_of], i.e. [DevModel.uart_acc] -- [u_out ++ u_tx], every byte
   the device ACCEPTED.  So [uart_tx_serial] below is a direct test of what
   was transmitted, not merely of what the driver believed.

   WHAT THE PROGRAM DOES.  The xv6 uartputc_sync shape: poll LSR (offset 5)
   for THRE (bit 5), store the byte to THR (offset 0), repeat -- for a
   20-byte string; then one unpolled store followed immediately by an LSR
   read; then a 24-byte BURST with no polling at all.  Registers are read
   and written a BYTE at a time throughout, which is the only width the
   model's bus decodes for this window (see UartWidth.v).

   WHAT IT PINS DOWN, i.e. the ways the model could have been wrong and is
   not: [uart_write] at offset 0 with DLAB clear pushing onto the tx FIFO,
   [uart_tx_pop] moving it to the wire, [uart_lsr]'s THRE/TEMT bits (0x60
   with the FIFO empty, and both bits set together -- the model does not
   distinguish them), the LSR being a PURE read that does not disturb the
   device, and [uart_acc] being exactly the transmitted byte sequence, in
   order, with nothing lost and nothing duplicated. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list bitvector.definitions.
Require Import VTest UartTxGen.
Local Open Scope Z_scope.

Definition tx_run : option mstate := run_until 50000 (start uart_tx_text).

(* Every observation, byte for byte:
     +4  progress marker                                        4
     +8  LSR before anything was written                        0x60 (THRE|TEMT)
     +12 LSR after the whole string had drained                 0x60
     +16 bytes written by the polled loop                       20
     +20 LSR read IMMEDIATELY after a THR store, no poll        0x60
     +24 LSR after polling TEMT again                           0x60
     +28 LSR after the 24-byte unpolled burst                   0x60          *)
Lemma uart_tx_result : result_of tx_run = uart_tx_qemu_result.
Proof. solve_vtest uart_tx_qemu_result. Qed.

(* ...and the line itself: uart_tx: hello 16550, then Z, then abc..x *)
Lemma uart_tx_serial : serial_of tx_run = uart_tx_qemu_serial.
Proof. solve_vtest uart_tx_qemu_serial. Qed.

(* ---------------------------------------------------------------------- *)
(* 2. THE +20 FIELD IS THE INTERESTING ONE.                                *)
(*                                                                         *)
(*    It is an LSR read one instruction after a store to THR, with no poll  *)
(*    in between, and both machines report THRE SET.  On the model side     *)
(*    that is not a coincidence: [VSched.settle] runs after every           *)
(*    instruction and takes [SUartTx] first, so the byte has already left   *)
(*    the FIFO by the time the next instruction issues.  QEMU's 16550 with  *)
(*    the FIFO disabled writes the character through to the chardev inside  *)
(*    the store itself and puts THRE straight back, so it agrees for its    *)
(*    own reason.                                                          *)
(*                                                                         *)
(*    The model ALSO has executions in which this field reads 0x00 -- any   *)
(*    schedule that steps the hart twice before [SUartTx].  That direction  *)
(*    costs the model nothing (a test asks only whether the hardware's      *)
(*    execution is one the model allows, and it is), but it is why this     *)
(*    field could not have been used to catch a model that never cleared    *)
(*    THRE at all.                                                          *)
(* ---------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------- *)
(* 3. THE TRANSMIT FIFO'S DEPTH IS NOT OBSERVABLE FROM A TEST PROGRAM,     *)
(*    so it is stated off the model instead.                               *)
(*                                                                         *)
(*    [uart_fifo_depth] is 16 and [uart_write] at offset 0 SILENTLY DROPS   *)
(*    a byte pushed into a full FIFO -- it returns [Some u], unchanged, so  *)
(*    the driver cannot tell.  The burst phase of uart_tx.S is the shape    *)
(*    that would provoke it (24 stores to THR with no poll), and it does    *)
(*    not: under [settle] the FIFO is drained after every instruction, so   *)
(*    its length never exceeds one and all 24 bytes reach the wire, which   *)
(*    is exactly what QEMU did.  Rather than invent an observation, the     *)
(*    drop is pinned directly on [uart_write]: seventeen pushes with no     *)
(*    intervening drain, and the seventeenth is gone.                       *)
(*                                                                         *)
(*    This is the model being MORE permissive than the hardware here, not   *)
(*    less: QEMU's transmit path never lost a byte in this test, while the  *)
(*    model has runs that lose one.  It cannot make a safety proof wrong,   *)
(*    but a specification saying that every byte the driver pushed appears *)
(*    on the console is false of this model, and DevModel's [uart_acc]     *)
(*    ghost is a LOWER bound for that reason.                               *)
(* ---------------------------------------------------------------------- *)

Definition thr_push (u : uart_state) (b : Z) : uart_state :=
  match uart_write u 0 (Z_to_bv 8 b) with Some u' => u' | None => u end.

Definition thr_pushes (u : uart_state) (bs : list Z) : uart_state :=
  foldl thr_push u bs.

Definition tx_seventeen : list Z :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17].
Definition tx_kept : list Z :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16].

Lemma uart_tx_fifo_drops_the_seventeenth :
  bv_unsigned <$> uart_acc (thr_pushes uart0_state tx_seventeen) = tx_kept.
Proof. solve_vtest tx_kept. Qed.
