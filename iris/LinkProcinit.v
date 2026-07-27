(* LinkProcinit.v -- instantiates the procinit proof against its only callee's
   proof (initlock).  Sealed, so this is the only place the two ever meet. *)
Require Import LinkInitlock ProofProcinit.

Module Procinit := ProcinitProof Initlock.
