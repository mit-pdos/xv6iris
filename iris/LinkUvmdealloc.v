(* LinkUvmdealloc.v -- instantiates the Uvmdealloc proof against its callee's
   proof (uvmunmap).  Sealed, so this is the only place the two ever meet. *)
Require Import LinkUvmunmap ProofUvmdealloc.

Module Uvmdealloc := UvmdeallocProof Uvmunmap.
