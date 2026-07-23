(* LinkMemset.v -- instantiates the Memset proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import ProofMemset.

Module Memset := MemsetProof.
