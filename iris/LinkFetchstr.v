(* LinkFetchstr.v -- instantiates the Fetchstr proof against its callees'
   proofs (myproc, copyinstr, strlen).  Sealed, so this is the only place the
   four ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecMyproc SpecCopyinstr SpecStrlen.
Require Import SpecFetchstr.
Require Import LinkMyproc LinkCopyinstr LinkStrlen.
Require Import ProofFetchstr.

Module Fetchstr := FetchstrProof Myproc Copyinstr Strlen.
