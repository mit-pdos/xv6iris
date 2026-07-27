(* LinkKilled.v -- instantiates the Killed proof against its callees' proofs
   (acquire / release).  Sealed, so this is the only place the three meet. *)
Require Import LinkAcquire LinkRelease ProofKilled.

Module Killed := KilledProof Acquire Release.
