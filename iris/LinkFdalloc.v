(* LinkFdalloc.v -- the one place fdalloc's proof meets myproc's. *)
Require Import LinkMyproc ProofFdalloc.

Module Fdalloc := FdallocProof Myproc.
