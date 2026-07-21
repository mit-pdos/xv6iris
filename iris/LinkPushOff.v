(* LinkPushOff.v -- instantiates the PushOff proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecPushOff SpecMycpu.
Require Import LinkMycpu WpSconfPushOff.

Module PushOff := PushOffProof Mycpu.
