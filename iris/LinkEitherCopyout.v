(* LinkEitherCopyout.v -- instantiates the either_copyout proof against its
   callees' proofs (myproc, copyout, memmove).  Sealed, so this is the only
   place the four ever meet. *)
Require Import LinkMyproc LinkCopyout LinkMemmove.
Require Import ProofEitherCopy.

Module EitherCopyout := EitherCopyoutProof Myproc Copyout Memmove.
