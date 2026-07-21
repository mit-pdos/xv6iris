(* LinkFileinit.v -- instantiates the Fileinit proof against its callee's proof.
   Sealed, so this is the only place the two ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecFileinit SpecInitlock.
Require Import LinkInitlock WpSconfFileinit.

Module Fileinit := FileinitProof Initlock.
