(* LinkTrapinit.v -- instantiates the Trapinit proof against its callee's
   proof.  Sealed, so this is the only place the two ever meet. *)
Require Import LinkInitlock ProofTrapinit.

Module Trapinit := TrapinitProof Initlock.
