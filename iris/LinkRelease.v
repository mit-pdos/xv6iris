(* LinkRelease.v -- instantiates the Release proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet.

   [ReleaseGen] is the one proof; [Release] closes the invariant again (the
   static kernel lock, what the thirteen ordinary consumers take) and
   [ReleaseCancel] destroys it and hands back the lock's storage. *)
Require Import LinkHolding LinkPushOff ProofRelease.

Module ReleaseGen := ReleaseGenProof Holding PushOff.
Module Release := ReleaseOfGen ReleaseGen.
Module ReleaseCancel := ReleaseCancelOfGen ReleaseGen.
