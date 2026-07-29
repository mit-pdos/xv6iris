(* LinkFetchaddr.v -- instantiates the Fetchaddr proof against its callees'
   proofs (myproc, copyin).  Sealed, so this is the only place the three ever
   meet. *)
Require Import LinkMyproc LinkCopyin.
Require Import ProofFetchaddr.

Module Fetchaddr := FetchaddrProof Myproc Copyin.
