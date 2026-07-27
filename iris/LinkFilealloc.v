(* LinkFilealloc.v -- instantiates the Filealloc proof against its callees'
   proofs.  Sealed, so this is the only place the three ever meet. *)
Require Import LinkAcquire LinkRelease ProofFilealloc.

Module Filealloc := FileallocProof Acquire Release.
