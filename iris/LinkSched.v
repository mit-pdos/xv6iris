(* LinkSched.v -- instantiates the Sched proof against its callees' proofs
   (myproc, holding, swtch).  Sealed, so this is the only place the four meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecSched SpecMyproc SpecHolding SpecSwtch.
Require Import LinkMyproc LinkHolding WpSwtchSconf WpSconfSched.

Module Sched := SchedProof Myproc Holding SwtchProof.
