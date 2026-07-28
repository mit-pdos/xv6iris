(* LinkWalkNoalloc.v -- the WALK_NOALLOC instance.  walk with alloc = 0 has no
   callees, so [WalkNoallocProof] is already a sealed instance; this file only
   gives it the uniform link name that consumers (ProofIsmapped) require. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecWalk.
Require Import ProofWalkNoalloc.

Module WalkNoalloc : WALK_NOALLOC := WalkNoallocProof.
