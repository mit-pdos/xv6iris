(* LinkPipewrite.v -- instantiates the pipewrite proof against its callees'
   proofs (myproc / acquire / killed / wakeup / sleep / copyin / release).
   Sealed, so this is the only place the whole-function proofs ever meet.

   [AcquireGen] / [ReleaseGen] / [SleepGen] are the [lock_openable]-generic
   forms: the pipe's lock is a kalloc'd object's, so the licence to open it is
   the caller's END REFERENCE ([pipe_ref]) and not a static [is_lock]. *)
Require Import LinkMyproc LinkAcquire LinkKilled LinkWakeup LinkSleep LinkCopyin LinkRelease.
Require Import ProofPipewrite.

Module Pipewrite := PipewriteProof Myproc AcquireGen Killed Wakeup SleepGen Copyin ReleaseGen.
