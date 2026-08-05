(* LinkSetkilled.v -- instantiates the Setkilled proof against its callees'
   proofs (acquire / release).  Sealed, so this is the only place the three
   meet. *)
Require Import LinkAcquire LinkRelease ProofSetkilled.

Module Setkilled := SetkilledProof Acquire Release.
