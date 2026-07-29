(* LinkAllocpid.v -- instantiates the allocpid proof against its callees'
   proofs (acquire + release).  Sealed, so this is the only place they meet.

   This file used to supply the contract with an [Axiom]; allocproc's cone is
   axiom-free now that allocpid is proved. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import LinkAcquire LinkRelease ProofAllocpid.

Module Allocpid := AllocpidProof Acquire Release.
