(* LinkAcquiresleep.v -- instantiates the Acquiresleep proof against its
   callees' proofs (acquire / release / myproc / sleep_prepare / sleep).
   Sealed, so this is the only place the six ever meet. *)
Require Import LinkAcquire LinkRelease LinkMyproc LinkSleepPrepare LinkSleep ProofAcquiresleep.

Module Acquiresleep := AcquiresleepProof Acquire Release Myproc SleepPrepare Sleep.
