(* LinkScheduler.v -- instantiates the Scheduler proof against its callees'
   proofs (acquire, release, swtch).  Sealed, so this is the only place the
   four ever meet. *)
Require Import LinkAcquire LinkRelease LinkSwtch ProofScheduler.

Module Scheduler := SchedulerProof Acquire Release Swtch.
