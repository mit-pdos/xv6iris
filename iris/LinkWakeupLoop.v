(* LinkWakeupLoop.v -- instantiates the WakeupLoop proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecWakeupLoop SpecMyproc SpecAcquire SpecRelease SpecWakeup.
Require Import LinkMyproc LinkAcquire LinkRelease LinkWakeup WpSconfWakeupLoop.

Module WakeupLoop := WakeupLoopProof Myproc Acquire Release Wakeup.
