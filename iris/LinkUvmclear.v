(* LinkUvmclear.v -- instantiates the Uvmclear proof against its one callee's
   proof (the no-alloc walk).  Sealed, so this is the only place the two ever
   meet. *)
Require Import LinkWalkNoalloc ProofUvmclear.

Module Uvmclear := UvmclearProof WalkNoalloc.
