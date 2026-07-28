(* LinkSleep.v -- instantiates the Sleep proof against its callees' proofs
   (myproc / acquire / sched / release).  Sealed, so this is the only place
   the whole-function proofs ever meet.

   [SleepGen] is the [lock_openable]-generic proof (the condition lock may be
   a kalloc'd object's, with the credential [Tk] riding the sleeper's frame);
   [Sleep] is its static-kernel-lock instance ([Tk := emp], [Dk := False]),
   which is what the ordinary consumers (acquiresleep, sys_pause) take. *)
Require Import LinkMyproc LinkAcquire LinkSched LinkRelease ProofSleep.

Module SleepGen := SleepGenProof Myproc Acquire AcquireGen Sched Release ReleaseGen.
Module Sleep := SleepOfGen SleepGen.
