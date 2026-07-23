(* LinkMycpu.v -- instantiates the Mycpu proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import ProofMycpu.

Module Mycpu := MycpuProof.
