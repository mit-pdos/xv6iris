(* LinkArgaddr.v -- the one place argaddr's proof meets argraw's. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecArgaddr SpecArgraw.
Require Import LinkArgraw ProofArgaddr.

Module Argaddr := ArgaddrProof Argraw.
