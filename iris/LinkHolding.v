(* LinkHolding.v -- instantiates the Holding proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import LinkMycpu ProofHolding.

Module Holding := HoldingProof Mycpu.
