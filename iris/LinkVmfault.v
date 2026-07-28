(* LinkVmfault.v -- instantiates the Vmfault proof against its callees'
   proofs.  Sealed, so this is the only place the six ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecMyproc SpecIsmapped SpecKalloc SpecMemsetPage SpecMappages SpecKfree.
Require Import SpecVmfault.
Require Import LinkMyproc LinkIsmapped LinkKalloc LinkMemsetPage LinkMappages LinkKfree.
Require Import ProofVmfault.

Module Vmfault := VmfaultProof Myproc Ismapped Kalloc MemsetPage Mappages Kfree.
