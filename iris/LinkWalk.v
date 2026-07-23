(* LinkWalk.v -- instantiates the Walk proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import LinkKalloc LinkMemsetArray ProofWalk.

Module Walk := WalkProof Kalloc MemsetArray.
