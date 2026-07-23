(* LinkKfree.v -- instantiates the Kfree proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import LinkAcquire LinkMemsetPage LinkRelease ProofKfree.

Module Kfree := KfreeProof Acquire MemsetPage Release.
