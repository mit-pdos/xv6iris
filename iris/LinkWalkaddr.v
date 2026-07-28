(* LinkWalkaddr.v -- instantiates the Walkaddr proof against its callee's
   proof (the no-alloc walk).  Sealed, so this is the only place the two ever
   meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecWalk SpecWalkaddr.
Require Import LinkWalkNoalloc ProofWalkaddr.

Module Walkaddr := WalkaddrProof WalkNoalloc.
