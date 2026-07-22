(* LinkFreerange.v -- instantiates the Freerange proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import LinkKfree WpSconfFreerange.

Module Freerange := FreerangeProof Kfree.
