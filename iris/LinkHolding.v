(* LinkHolding.v -- instantiates the Holding proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import LinkMycpu WpSconfHolding.

Module Holding := HoldingProof Mycpu.
