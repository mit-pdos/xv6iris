(* LinkPlicinit.v -- instantiates the Plicinit proof.  plicinit has no callees,
   so PlicinitProof takes no functor arguments; this is the sole meeting point
   of the spec and its sealed proof. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecPlicinit.
Require Import WpSconfPlicinit.

Module Plicinit := PlicinitProof.
