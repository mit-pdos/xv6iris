(* LinkPrepareReturn.v -- instantiates the prepare_return proof against its
   callee's proof (myproc).  Sealed, so this is the only place the two ever
   meet. *)
Require Import LinkMyproc ProofPrepareReturn.

Module PrepareReturn := PrepareReturnProof Myproc.
