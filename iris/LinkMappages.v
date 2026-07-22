(* LinkMappages.v -- instantiates the Mappages proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import LinkWalk WpSconfMappages.

Module Mappages := MappagesProof Walk.
