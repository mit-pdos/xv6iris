(* LinkMycpu.v -- instantiates the Mycpu proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecMycpu.
Require Import WpSconfMycpu.

Module Mycpu := MycpuProof.
