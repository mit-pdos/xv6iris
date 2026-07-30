(* LinkBunpin.v -- instantiates the Bunpin proof against its callees' proofs.
   Sealed, so this is the only place the three ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecBunpin SpecAcquire SpecRelease.
Require Import LinkAcquire LinkRelease ProofBunpin.

Module Bunpin := BunpinProof Acquire Release.
