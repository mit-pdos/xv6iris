(* LinkGrowproc.v -- instantiates the Growproc proof against its callees'
   proofs.  Sealed, so this is the only place the three ever meet. *)
Require Import LinkMyproc LinkUvmalloc LinkUvmdealloc.
Require Import ProofGrowproc.

Module Growproc := GrowprocProof Myproc Uvmalloc Uvmdealloc.
