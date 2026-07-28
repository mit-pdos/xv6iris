(* LinkIsmapped.v -- instantiates the Ismapped proof against its callee's
   proof (the no-alloc walk).  Sealed, so this is the only place the two ever
   meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecWalk SpecIsmapped.
Require Import LinkWalkNoalloc ProofIsmapped.

Module Ismapped := IsmappedProof WalkNoalloc.
