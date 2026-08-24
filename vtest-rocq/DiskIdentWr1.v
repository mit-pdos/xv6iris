(* DiskIdentWr1.v -- A ONE-BYTE WRITE TO THE VIRTIO WINDOW.  EVERY OBSERVATION AGREES; this file used to record a
   STUCK machine.

   Source: tools/vtest/tests/disk_ident_wr1.S.  Capture: DiskIdentWr1Gen.v.

   The write side of finding 15.  A one-byte store into the window reaches no
   register, so it is DROPPED -- and the test's point is that it is dropped
   rather than half-applied: the status register it aims at is unchanged
   afterwards, on both machines. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentWr1Gen.
Local Open Scope Z_scope.

Definition di_wr1_run : option mstate := run_until 50000 (start disk_ident_wr1_text).

(* The WHOLE result region, so nothing can hide in a field this file forgot
   to name: the model now runs the program to completion and leaves the same
   4096 bytes behind that the machine did. *)
Lemma disk_ident_wr1_result : result_of di_wr1_run = disk_ident_wr1_qemu_result.
Proof. solve_vtest disk_ident_wr1_qemu_result. Qed.

(* ---------------------------------------------------------------------- *)
(* A stuck machine was never unsoundness -- the system theorem proves xv6   *)
(* never gets stuck, so a state with no transition is never reached.  What  *)
(* it cost was COVERAGE: every driver that made this access had no model    *)
(* execution at all and could not be verified here.  That is what this      *)
(* file now measures instead.                                              *)
(* ---------------------------------------------------------------------- *)
