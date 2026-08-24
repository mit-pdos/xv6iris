(* DiskIdentQsel.v -- A PER-QUEUE WRITE WITH A FOREIGN SELECTION.  EVERY OBSERVATION AGREES; this file used to record a
   STUCK machine.

   Source: tools/vtest/tests/disk_ident_qsel.S.  Capture: DiskIdentQselGen.v.

   Queue 0 is the only queue this device has, and the model used to REFUSE
   any per-queue write made while QueueSel named another (finding 16).  The
   hardware ignores it, so the model does too -- the write is accepted and
   changes nothing.  What kept the geometry legal was never the refusal but
   [virtio_live]'s own conditions, which is where it still lives. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentQselGen.
Local Open Scope Z_scope.

Definition di_qsel_run : option mstate := run_until 50000 (start disk_ident_qsel_text).

(* The WHOLE result region, so nothing can hide in a field this file forgot
   to name: the model now runs the program to completion and leaves the same
   4096 bytes behind that the machine did. *)
Lemma disk_ident_qsel_result : result_of di_qsel_run = disk_ident_qsel_qemu_result.
Proof. solve_vtest disk_ident_qsel_qemu_result. Qed.

(* ---------------------------------------------------------------------- *)
(* A stuck machine was never unsoundness -- the system theorem proves xv6   *)
(* never gets stuck, so a state with no transition is never reached.  What  *)
(* it cost was COVERAGE: every driver that made this access had no model    *)
(* execution at all and could not be verified here.  That is what this      *)
(* file now measures instead.                                              *)
(* ---------------------------------------------------------------------- *)
