(* LinkReleasesleep.v -- instantiates the Releasesleep proof against its
   callees' proofs (acquire / release / the wakeup proc[]-table loop).  Sealed,
   so this is the only place the whole-function proof meets its callees. *)
Require Import LinkAcquire LinkRelease LinkWakeup ProofReleasesleep.

Module Releasesleep := ReleasesleepProof Acquire Release Wakeup.
