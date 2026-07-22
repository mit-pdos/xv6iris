(* LinkAcquire.v -- instantiates the Acquire proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import LinkMycpu LinkHolding LinkPushOff WpSconfAcquire.

Module Acquire := AcquireProof Mycpu Holding PushOff.
