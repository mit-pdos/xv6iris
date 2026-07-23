(* LinkWakeup.v -- instantiates the wakeup proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import LinkMyproc LinkAcquire LinkRelease LinkWakeupParts ProofWakeup.

Module Wakeup := WakeupProof Myproc Acquire Release WakeupParts.
