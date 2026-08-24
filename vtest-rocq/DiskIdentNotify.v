(* DiskIdentNotify.v -- A NOTIFICATION NAMING A QUEUE THAT DOES NOT EXIST.  EVERY OBSERVATION AGREES; this file used to record a
   STUCK machine.

   Source: tools/vtest/tests/disk_ident_notify.S.  Capture: DiskIdentNotifyGen.v.

   QueueNotify carries the queue number, and the model used to refuse any
   value but 0 (finding 16).  This device polls the available ring itself, so
   a notification is a hint whatever number it carries; the hardware ignores
   an unknown one and so does the model. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentNotifyGen.
Local Open Scope Z_scope.

Definition di_notify_run : option mstate := run_until 50000 (start disk_ident_notify_text).

(* The WHOLE result region, so nothing can hide in a field this file forgot
   to name: the model now runs the program to completion and leaves the same
   4096 bytes behind that the machine did. *)
Lemma disk_ident_notify_result : result_of di_notify_run = disk_ident_notify_qemu_result.
Proof. solve_vtest disk_ident_notify_qemu_result. Qed.

(* ---------------------------------------------------------------------- *)
(* A stuck machine was never unsoundness -- the system theorem proves xv6   *)
(* never gets stuck, so a state with no transition is never reached.  What  *)
(* it cost was COVERAGE: every driver that made this access had no model    *)
(* execution at all and could not be verified here.  That is what this      *)
(* file now measures instead.                                              *)
(* ---------------------------------------------------------------------- *)
