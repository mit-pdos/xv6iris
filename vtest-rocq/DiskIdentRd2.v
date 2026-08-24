(* DiskIdentRd2.v -- A TWO-BYTE READ OF THE VIRTIO WINDOW.  EVERY OBSERVATION AGREES; this file used to record a
   STUCK machine.

   Source: tools/vtest/tests/disk_ident_rd2.S.  Capture: DiskIdentRd2Gen.v.

   The same as the one-byte case (finding 15): the transport is 32-bit, a
   narrower read reaches no register, and the answer is zero rather than a
   machine with nowhere to go. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentRd2Gen.
Local Open Scope Z_scope.

Definition di_rd2_run : option mstate := run_until 50000 (start disk_ident_rd2_text).

(* The WHOLE result region, so nothing can hide in a field this file forgot
   to name: the model now runs the program to completion and leaves the same
   4096 bytes behind that the machine did. *)
Lemma disk_ident_rd2_result : result_of di_rd2_run = disk_ident_rd2_qemu_result.
Proof. solve_vtest disk_ident_rd2_qemu_result. Qed.

(* ---------------------------------------------------------------------- *)
(* A stuck machine was never unsoundness -- the system theorem proves xv6   *)
(* never gets stuck, so a state with no transition is never reached.  What  *)
(* it cost was COVERAGE: every driver that made this access had no model    *)
(* execution at all and could not be verified here.  That is what this      *)
(* file now measures instead.                                              *)
(* ---------------------------------------------------------------------- *)
