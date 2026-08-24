(* DiskIdentQreset.v -- THE QUEUE-RESET REGISTER.  EVERY OBSERVATION AGREES; this file used to record a
   STUCK machine.

   Source: tools/vtest/tests/disk_ident_qreset.S.  Capture: DiskIdentQresetGen.v.

   QueueReset (0x0c0) was not decoded (finding 14).  It reads 0: this device
   does not offer VIRTIO_F_RING_RESET, so no queue is ever in the reset
   state, which is exactly what the register is there to report. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentQresetGen.
Local Open Scope Z_scope.

Definition di_qreset_run : option mstate := run_until 50000 (start disk_ident_qreset_text).

(* The WHOLE result region, so nothing can hide in a field this file forgot
   to name: the model now runs the program to completion and leaves the same
   4096 bytes behind that the machine did. *)
Lemma disk_ident_qreset_result : result_of di_qreset_run = disk_ident_qreset_qemu_result.
Proof. solve_vtest disk_ident_qreset_qemu_result. Qed.

(* ---------------------------------------------------------------------- *)
(* A stuck machine was never unsoundness -- the system theorem proves xv6   *)
(* never gets stuck, so a state with no transition is never reached.  What  *)
(* it cost was COVERAGE: every driver that made this access had no model    *)
(* execution at all and could not be verified here.  That is what this      *)
(* file now measures instead.                                              *)
(* ---------------------------------------------------------------------- *)
