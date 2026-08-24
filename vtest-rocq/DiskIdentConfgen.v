(* DiskIdentConfgen.v -- THE CONFIGURATION GENERATION COUNTER.  EVERY OBSERVATION AGREES; this file used to record a
   STUCK machine.

   Source: tools/vtest/tests/disk_ident_confgen.S.  Capture: DiskIdentConfgenGen.v.

   ConfigGeneration (0x0fc) was not decoded at all (finding 13), so the
   read-check-reread loop a driver uses to take a consistent snapshot of the
   configuration space was a STUCK machine on its first read.  This device's
   configuration never changes under the driver's feet, so the generation is
   0 and every such loop agrees with itself immediately. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentConfgenGen.
Local Open Scope Z_scope.

Definition di_confgen_run : option mstate := run_until 50000 (start disk_ident_confgen_text).

(* The WHOLE result region, so nothing can hide in a field this file forgot
   to name: the model now runs the program to completion and leaves the same
   4096 bytes behind that the machine did. *)
Lemma disk_ident_confgen_result : result_of di_confgen_run = disk_ident_confgen_qemu_result.
Proof. solve_vtest disk_ident_confgen_qemu_result. Qed.

(* ---------------------------------------------------------------------- *)
(* A stuck machine was never unsoundness -- the system theorem proves xv6   *)
(* never gets stuck, so a state with no transition is never reached.  What  *)
(* it cost was COVERAGE: every driver that made this access had no model    *)
(* execution at all and could not be verified here.  That is what this      *)
(* file now measures instead.                                              *)
(* ---------------------------------------------------------------------- *)
