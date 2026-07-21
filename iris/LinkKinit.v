(* LinkKinit.v -- instantiates the Kinit proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecKinit SpecFreerange SpecInitlock.
Require Import LinkFreerange LinkInitlock WpSconfKinit.

Module Kinit := KinitProof Freerange Initlock.
