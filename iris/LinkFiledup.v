(* LinkFiledup.v -- instantiates the Filedup proof against its callees'
   proofs.  Sealed, so this is the only place the three ever meet. *)
Require Import LinkAcquire LinkRelease ProofFiledup.

Module Filedup := FiledupProof Acquire Release.
