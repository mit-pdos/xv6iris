(* LinkSleep.v -- instantiates the Sleep proof against its callees' proofs
   (myproc / acquire / sched / release).  Sealed, so this is the only place
   the whole-function proofs ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecSleep SpecMyproc SpecAcquire SpecSched SpecRelease.
Require Import LinkMyproc LinkAcquire LinkSched LinkRelease WpSconfSleep.

Module Sleep := SleepProof Myproc Acquire Sched Release.
