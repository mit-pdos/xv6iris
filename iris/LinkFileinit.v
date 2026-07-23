(* LinkFileinit.v -- instantiates the Fileinit proof against its callee's proof.
   Sealed, so this is the only place the two ever meet. *)
Require Import LinkInitlock ProofFileinit.

Module Fileinit := FileinitProof Initlock.
