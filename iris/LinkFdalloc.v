(* LinkFdalloc.v -- the one place fdalloc's proof meets myproc's. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecFdalloc SpecMyproc.
Require Import LinkMyproc ProofFdalloc.

Module Fdalloc := FdallocProof Myproc.
