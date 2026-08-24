(* CoreSmoke.v -- the plumbing test.  It touches no device: what it checks is
   that ONE image, run on QEMU and on the Rocq semantics, leaves the same
   RESULT region -- the image loads at the same address, the reset register
   file agrees well enough to run, the declared stack region is usable, and
   the two sides' observation channels line up byte for byte.  If this is
   red, no device test above it means anything.

   Source: tools/vtest/tests/core_smoke.S.  Capture: CoreSmokeGen.v. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
Require Import VTest CoreSmokeGen.
Local Open Scope Z_scope.

Definition smoke_run : option mstate := run_until 200 (start core_smoke_text).

(* THE TEST: what the model left in the RESULT region is, byte for byte over
   the whole 4 KB, what QEMU left there. *)
Lemma core_smoke_result : result_of smoke_run = core_smoke_qemu_result.
Proof. solve_vtest core_smoke_qemu_result. Qed.

(* ...and it did not touch the disk, as QEMU did not. *)
Lemma core_smoke_disk : core_smoke_qemu_disk = [].
Proof. reflexivity. Qed.

(* A test that ran out of budget and one that got stuck both report [None];
   this is what tells them apart, and it is the number to raise if a future
   edit to the program makes the test go red with an empty result. *)
Lemma core_smoke_budget : budget_left 200 (start core_smoke_text) = 171%nat.
Proof. vm_cast_no_check (eq_refl 171%nat). Qed.
