(* LinkRelease.v -- instantiates the Release proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import LinkHolding LinkPushOff WpSconfRelease.

Module Release := ReleaseProof Holding PushOff.
