(* LinkHoldingsleep.v -- instantiates the Holdingsleep proof against its
   callees' proofs (acquire / release / myproc).  Sealed, so this is the only
   place the four ever meet. *)
Require Import LinkAcquire LinkRelease LinkMyproc ProofHoldingsleep.

Module Holdingsleep := HoldingsleepProof Acquire Release Myproc.
