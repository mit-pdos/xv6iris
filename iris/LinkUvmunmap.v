(* LinkUvmunmap.v -- instantiates the Uvmunmap proof against its callees'
   proofs (the no-alloc walk and kfree).  Sealed, so this is the only place
   the three ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecWalk SpecKfree.
Require Import SpecUvmunmap.
Require Import LinkWalkNoalloc LinkKfree.
Require Import ProofUvmunmap.

Module Uvmunmap := UvmunmapProof WalkNoalloc Kfree.
