(* LinkUvmalloc.v -- instantiates the Uvmalloc proof against its callees'
   proofs.  Sealed, so this is the only place the five ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecKalloc SpecMemsetPage SpecMappages SpecKfree SpecUvmdealloc.
Require Import SpecUvmalloc.
Require Import LinkKalloc LinkMemsetPage LinkMappages LinkKfree LinkUvmdealloc.
Require Import ProofUvmalloc.

Module Uvmalloc := UvmallocProof Kalloc MemsetPage Mappages Kfree Uvmdealloc.
