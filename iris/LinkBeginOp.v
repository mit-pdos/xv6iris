(* LinkBeginOp.v -- instantiates the begin_op proof against its callees'
   proofs (acquire / release / sleep).  Sealed, so this is the only place the
   four ever meet. *)
Require Import LinkAcquire LinkRelease LinkSleepPrepare LinkSleep ProofBeginOp.

Module BeginOp := BeginOpProof Acquire Release SleepPrepare Sleep.
