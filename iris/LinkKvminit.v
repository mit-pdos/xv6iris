(* LinkKvminit.v -- instantiates the kvminit proof against its sole callee's
   proof (kvmmake).  Sealed. *)
Require Import LinkKvmmake ProofKvminit.

Module Kvminit := KvminitProof Kvmmake.
