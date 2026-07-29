(* LinkUvmalloc.v -- instantiates the Uvmalloc proof against its callees'
   proofs.  Sealed, so this is the only place the five ever meet. *)
Require Import LinkKalloc LinkMemsetPage LinkMappages LinkKfree LinkUvmdealloc.
Require Import ProofUvmalloc.

Module Uvmalloc := UvmallocProof Kalloc MemsetPage Mappages Kfree Uvmdealloc.
