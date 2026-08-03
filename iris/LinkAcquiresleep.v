(* LinkAcquiresleep.v -- instantiates the Acquiresleep proof against its
   callees' proofs (acquire / release / myproc / sleep).  Sealed, so this is
   the only place the five ever meet. *)
Require Import LinkAcquire LinkRelease LinkMyproc LinkSleep ProofAcquiresleep.

Module Acquiresleep := AcquiresleepProof Acquire Release Myproc Sleep.
