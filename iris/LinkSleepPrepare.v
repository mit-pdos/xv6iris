(* LinkSleepPrepare.v -- instantiates the SleepPrepare proof against its
   callees' proofs (myproc / acquire / release).  Sealed, so this is the only
   place the four whole-function proofs ever meet. *)
Require Import LinkMyproc LinkAcquire LinkRelease ProofSleepPrepare.

Module SleepPrepare := SleepPrepareProof Myproc Acquire Release.
