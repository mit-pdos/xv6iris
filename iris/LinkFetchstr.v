(* LinkFetchstr.v -- instantiates the Fetchstr proof against its callees'
   proofs (myproc, copyinstr, strlen).  Sealed, so this is the only place the
   four ever meet. *)
Require Import LinkMyproc LinkCopyinstr LinkStrlen.
Require Import ProofFetchstr.

Module Fetchstr := FetchstrProof Myproc Copyinstr Strlen.
