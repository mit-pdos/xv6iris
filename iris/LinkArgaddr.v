(* LinkArgaddr.v -- the one place argaddr's proof meets argraw's. *)
Require Import LinkArgraw ProofArgaddr.

Module Argaddr := ArgaddrProof Argraw.
