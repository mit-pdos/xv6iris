(* LinkKalloc.v -- instantiates the Kalloc proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecKalloc SpecAcquire SpecMemsetPage SpecRelease.
Require Import LinkAcquire LinkMemsetPage LinkRelease WpSconfKalloc.

Module Kalloc := KallocProof Acquire MemsetPage Release.
