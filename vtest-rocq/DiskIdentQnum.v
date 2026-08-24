(* DiskIdentQnum.v -- QUEUE SIZES BEYOND THE FOURTH POWER OF TWO.  EVERY OBSERVATION AGREES; this file used to record a
   STUCK machine.

   Source: tools/vtest/tests/disk_ident_qnum.S.  Capture: DiskIdentQnumGen.v.

   [VirtioModel.vq_size_ok] used to accept {1,2,4,8} and [virtio_write] to
   answer [None] for any other QueueNum, on the grounds that the ring
   geometry divides by that number.  But 16 IS a configuration a real device
   accepts -- QEMU reports QueueNumMax = 1024 in this very program -- so the
   refusal landed on a legal driver (finding 1).  The model now advertises
   the board's 1024 and accepts any power of two up to it, so a driver that
   believes the maximum and sizes its queue accordingly has a model
   execution.  An illegal size is still refused, and that is deliberate: a
   queue whose size is not a power of two is a configuration no real device
   accepts, and refusing at the write keeps the geometry legal by
   construction. *)
From Stdlib Require Import List ZArith.
Import ListNotations.
From stdpp Require Import list.
Require Import VTest DiskIdentQnumGen.
Local Open Scope Z_scope.

Definition di_qnum_run : option mstate := run_until 50000 (start disk_ident_qnum_text).

(* The WHOLE result region, so nothing can hide in a field this file forgot
   to name: the model now runs the program to completion and leaves the same
   4096 bytes behind that the machine did. *)
Lemma disk_ident_qnum_result : result_of di_qnum_run = disk_ident_qnum_qemu_result.
Proof. solve_vtest disk_ident_qnum_qemu_result. Qed.

(* ---------------------------------------------------------------------- *)
(* A stuck machine was never unsoundness -- the system theorem proves xv6   *)
(* never gets stuck, so a state with no transition is never reached.  What  *)
(* it cost was COVERAGE: every driver that made this access had no model    *)
(* execution at all and could not be verified here.  That is what this      *)
(* file now measures instead.                                              *)
(* ---------------------------------------------------------------------- *)
