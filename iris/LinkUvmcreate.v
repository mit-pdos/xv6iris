(* LinkUvmcreate.v -- instantiates the uvmcreate proof against its callees'
   proofs (kalloc + memset).  Sealed, so this is the only place they meet.
   The whole-function memset spec [MEMSET] is [MemsetArray]
   (LinkMemsetArray), not the [MEMSET_PARTS] module [Memset]. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecUvmcreate SpecKalloc SpecMemset.
Require Import LinkKalloc LinkMemsetArray ProofUvmcreate.

Module Uvmcreate := UvmcreateProof Kalloc MemsetArray.
