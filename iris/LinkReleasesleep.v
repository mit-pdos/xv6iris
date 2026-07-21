(* LinkReleasesleep.v -- instantiates the Releasesleep proof against its
   callees' proofs (acquire / release / the wakeup proc[]-table loop).  Sealed,
   so this is the only place the whole-function proof meets its callees. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecReleasesleep SpecAcquire SpecRelease SpecWakeupLoop.
Require Import LinkAcquire LinkRelease LinkWakeupLoop WpSconfReleasesleep.

Module Releasesleep := ReleasesleepProof Acquire Release WakeupLoop.
