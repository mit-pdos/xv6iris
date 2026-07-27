(* LinkArgraw.v -- instantiates the Argraw proof against its callee's proof
   (myproc).  Sealed, so this is the only place the two ever meet. *)
Require Import LinkMyproc ProofArgraw.

Module Argraw := ArgrawProof Myproc.
