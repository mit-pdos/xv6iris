(* LinkSleep.v -- instantiates the Sleep proof against its callees' proofs
   (myproc / acquire / sched / release).  Sealed, so this is the only place
   the whole-function proofs ever meet.

   The [SleepGen] / [SleepOfGen] pair is GONE with [SLEEP_GEN]: the split
   sleep protocol releases no condition lock, so nothing in sleep's contract
   is [lock_openable]-generic any more (SpecSleep.v's header).  One
   instantiation is all there is. *)
Require Import LinkMyproc LinkAcquire LinkSched LinkRelease ProofSleep.

Module Sleep := SleepProof Myproc Acquire Sched Release.
