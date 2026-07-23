(* LinkWakeupParts.v -- instantiates the WakeupParts proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import ProofWakeupParts.

Module WakeupParts := WakeupPartsProof.
