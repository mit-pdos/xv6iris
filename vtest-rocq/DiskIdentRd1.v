(* DiskIdentRd1.v -- A ONE-BYTE READ OF THE VIRTIO WINDOW.  EVERY OBSERVATION AGREES; this file used to record a
   STUCK machine.

   Source: tools/vtest/tests/disk_ident_rd1.S.  Capture: DiskIdentRd1Gen.v.

   The window is 32-bit, and the model used to decode width 4 alone, so a
   narrower access was a STUCK machine (finding 15).  A narrow read is not an
   error on the hardware: it reaches no register and the machine answers
   zero, which is what [DevModel.dev_read]'s virtio arm now does at widths 1
   and 2. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentRd1Gen.
Local Open Scope Z_scope.

Definition di_rd1_run : option mstate := run_until 50000 (start disk_ident_rd1_text).

(* The WHOLE result region, so nothing can hide in a field this file forgot
   to name: the model now runs the program to completion and leaves the same
   4096 bytes behind that the machine did. *)
Lemma disk_ident_rd1_result : result_of di_rd1_run = disk_ident_rd1_qemu_result.
Proof. solve_vtest disk_ident_rd1_qemu_result. Qed.

(* ---------------------------------------------------------------------- *)
(* A stuck machine was never unsoundness -- the system theorem proves xv6   *)
(* never gets stuck, so a state with no transition is never reached.  What  *)
(* it cost was COVERAGE: every driver that made this access had no model    *)
(* execution at all and could not be verified here.  That is what this      *)
(* file now measures instead.                                              *)
(* ---------------------------------------------------------------------- *)
