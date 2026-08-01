(* LinkBrelse.v -- instantiates the Brelse proof against its callees' proofs
   (holdingsleep / releasesleep / acquire / release).  Sealed, so this is the
   only place the five ever meet. *)
Require Import LinkHoldingsleep LinkReleasesleep LinkAcquire LinkRelease ProofBrelse.

Module Brelse := BrelseProof Holdingsleep Releasesleep Acquire Release.
