(* LinkPushOff.v -- instantiates the PushOff proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import LinkMycpu WpSconfPushOff.

Module PushOff := PushOffProof Mycpu.
