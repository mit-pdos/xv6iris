(* LinkKalloc.v -- instantiates the Kalloc proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import LinkAcquire LinkMemsetPage LinkRelease ProofKalloc.

Module Kalloc := KallocProof Acquire MemsetPage Release.
