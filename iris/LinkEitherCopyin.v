(* LinkEitherCopyin.v -- instantiates the either_copyin proof against its
   callees' proofs (myproc, copyin, memmove).  Sealed, so this is the only
   place the four ever meet. *)
Require Import LinkMyproc LinkCopyin LinkMemmove.
Require Import ProofEitherCopy.

Module EitherCopyin := EitherCopyinProof Myproc Copyin Memmove.
