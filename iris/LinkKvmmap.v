(* LinkKvmmap.v -- instantiates the Kvmmap proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecKvmmap SpecMappages.
Require Import LinkMappages WpSconfKvmmap.

Module Kvmmap := KvmmapProof Mappages.
