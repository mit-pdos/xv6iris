(* LinkBpin.v -- instantiates the Bpin proof against its callees' proofs.
   Sealed, so this is the only place the three ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecBpin SpecAcquire SpecRelease.
Require Import LinkAcquire LinkRelease ProofBpin.

Module Bpin := BpinProof Acquire Release.
