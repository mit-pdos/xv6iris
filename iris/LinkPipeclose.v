(* LinkPipeclose.v -- instantiates the Pipeclose proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet.

   Note WHICH release: the plain-lock [Release] is no use to a pipe, whose
   lock is not an [is_lock].  pipeclose takes the generic proof and, for the
   arm that frees the page, its cancelling instance. *)
Require Import LinkAcquire LinkWakeup LinkRelease LinkKfree ProofPipeclose.

Module Pipeclose := PipecloseProof AcquireGen Wakeup ReleaseGen ReleaseCancel Kfree.
