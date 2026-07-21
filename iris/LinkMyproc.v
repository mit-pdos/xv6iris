(* LinkMyproc.v -- instantiates the Myproc proof against its callee's proof
   (push_off / pop_off).  Sealed, so this is the only place the two ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecMyproc SpecPushOff.
Require Import LinkPushOff WpSconfMyproc.

Module Myproc := MyprocProof PushOff.
