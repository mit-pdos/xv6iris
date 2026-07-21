(* LinkInitlock.v -- instantiates the Initlock proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecInitlock.
Require Import WpSconfInitlock.

Module Initlock := InitlockProof.
