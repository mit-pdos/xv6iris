(* DiskIdentShmsel.v -- THE SHARED-MEMORY REGION REGISTERS.  EVERY OBSERVATION AGREES; this file used to record a
   STUCK machine.

   Source: tools/vtest/tests/disk_ident_shmsel.S.  Capture: DiskIdentShmselGen.v.

   SHMSel and the SHMLen/SHMBase pairs (0x0ac..0x0bc) were not decoded
   (finding 14).  This device has NO shared-memory regions, and the
   transport's way of saying so is a length of all-ones -- which is what a
   driver enumerating regions reads, for every selection. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentShmselGen.
Local Open Scope Z_scope.

Definition di_shmsel_run : option mstate := run_until 50000 (start disk_ident_shmsel_text).

(* The WHOLE result region, so nothing can hide in a field this file forgot
   to name: the model now runs the program to completion and leaves the same
   4096 bytes behind that the machine did. *)
Lemma disk_ident_shmsel_result : result_of di_shmsel_run = disk_ident_shmsel_qemu_result.
Proof. solve_vtest disk_ident_shmsel_qemu_result. Qed.

(* ---------------------------------------------------------------------- *)
(* A stuck machine was never unsoundness -- the system theorem proves xv6   *)
(* never gets stuck, so a state with no transition is never reached.  What  *)
(* it cost was COVERAGE: every driver that made this access had no model    *)
(* execution at all and could not be verified here.  That is what this      *)
(* file now measures instead.                                              *)
(* ---------------------------------------------------------------------- *)
