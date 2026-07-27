(* LinkArgint.v -- instantiates the Argint proof against its callee's proof
   (argraw).  Sealed, so this is the only place the two ever meet. *)
Require Import LinkArgraw ProofArgint.

Module Argint := ArgintProof Argraw.
