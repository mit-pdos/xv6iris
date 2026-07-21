(* LinkWalk.v -- instantiates the Walk proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecWalk SpecKalloc SpecMemset.
Require Import LinkKalloc LinkMemset WpSconfWalk.

Module Walk := WalkProof Kalloc Memset.
