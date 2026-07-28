(* LinkFetchaddr.v -- instantiates the Fetchaddr proof against its callees'
   proofs (myproc, copyin).  Sealed, so this is the only place the three ever
   meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecMyproc SpecCopyin.
Require Import SpecFetchaddr.
Require Import LinkMyproc LinkCopyin.
Require Import ProofFetchaddr.

Module Fetchaddr := FetchaddrProof Myproc Copyin.
