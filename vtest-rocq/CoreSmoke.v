(* CoreSmoke.v -- the plumbing test.  It touches no device: what it checks is
   that ONE image, run on QEMU and on the Rocq semantics, leaves the same
   RESULT region -- the image loads at the same address, the reset register
   file agrees well enough to run, the declared stack region is usable, and
   the two sides' observation channels line up byte for byte.  If this is
   red, no device test above it means anything.

   Source: tools/vtest/tests/core_smoke.S.  Capture: CoreSmokeGen.v. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
Require Import VTest CoreSmokeGen CoreSmokeHwGen.
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
Lemma core_smoke_budget : budget_left 200 (start core_smoke_text) = 167%nat.
Proof. vm_cast_no_check (eq_refl 167%nat). Qed.

(* ====================================================================== *)
(* THE SAME QUESTION, ASKED OF REAL HARDWARE.                             *)
(*                                                                        *)
(* Capture: CoreSmokeHwGen.v, from tools/vtest/board.py and one run on a   *)
(* StarFive VisionFive 2 over JTAG.  It is a DIFFERENT IMAGE from the one  *)
(* QEMU ran -- same source, built with the board profile -- so it gets its *)
(* own start state off its own [_hw_text], and on the hart it actually ran *)
(* on.  tools/vtest/README-hw.md says what that costs.                     *)
(*                                                                        *)
(* What this particular test establishes is the PLUMBING, and on a board   *)
(* there is more of it to establish than on QEMU: that the image survives  *)
(* a JTAG load into DRAM and is fetched rather than a stale I-cache line,  *)
(* that the declared regions really were zeroed before the run, that the   *)
(* runner's register set-up leaves the hart somewhere the program can run  *)
(* from, and that reading the result region back over JTAG is the same     *)
(* observation the model makes of [gmem].  If this is red, no hardware     *)
(* test above it means anything.                                          *)
(* ====================================================================== *)

Definition smoke_hw_run : option mstate :=
  run_until 200 (start_hart core_smoke_hw_primary_hart core_smoke_hw_text).

Lemma core_smoke_hw_result_ok : result_of smoke_hw_run = core_smoke_hw_result.
Proof. solve_vtest core_smoke_hw_result. Qed.

(* the diagnostic, as on the QEMU side: this tells "the budget was too small"
   apart from "the model got stuck", and the board image is two instructions
   longer than QEMU's (the [fence.i] and the hart-slot bias) *)
Lemma core_smoke_hw_status : run_status 200 (start_hart core_smoke_hw_primary_hart
                                                        core_smoke_hw_text) = VDone.
Proof. vm_cast_no_check (eq_refl VDone). Qed.
