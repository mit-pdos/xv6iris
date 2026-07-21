(* LinkYield.v -- instantiates the Yield proof against its callees' proofs
   (myproc / acquire / sched / release).  Sealed, so this is the only place
   the whole-function proofs ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecYield SpecMyproc SpecAcquire SpecSched SpecRelease.
Require Import LinkMyproc LinkAcquire LinkSched LinkRelease WpSconfYield.

Module Yield := YieldProof Myproc Acquire Sched Release.
