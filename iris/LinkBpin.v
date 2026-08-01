(* LinkBpin.v -- instantiates the Bpin proof against its callees' proofs.
   Sealed, so this is the only place the three ever meet. *)
Require Import LinkAcquire LinkRelease ProofBpin.

Module Bpin := BpinProof Acquire Release.
