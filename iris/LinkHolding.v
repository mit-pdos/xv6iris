(* LinkHolding.v -- instantiates the Holding proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecHolding SpecMycpu.
Require Import LinkMycpu WpSconfHolding.

Module Holding := HoldingProof Mycpu.
