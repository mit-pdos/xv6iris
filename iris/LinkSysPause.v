(* LinkSysPause.v -- sys_pause's proof, instantiated against the REAL proofs
   of the six functions it calls. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecSysPause SpecArgint SpecAcquire SpecRelease SpecMyproc SpecKilled SpecSleep.
Require Import LinkArgint LinkAcquire LinkRelease LinkMyproc LinkKilled LinkSleep ProofSysPause.

Module SysPause := SysPauseProof Argint Acquire Release Myproc Killed Sleep.
