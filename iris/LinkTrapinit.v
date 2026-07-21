(* LinkTrapinit.v -- instantiates the Trapinit proof against its callee's
   proof.  Sealed, so this is the only place the two ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecTrapinit SpecInitlock.
Require Import LinkInitlock WpSconfTrapinit.

Module Trapinit := TrapinitProof Initlock.
