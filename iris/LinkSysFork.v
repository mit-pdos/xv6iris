(* LinkSysFork.v -- sys_fork's proof, instantiated against the REAL proof of
   its one callee.  kfork's contract has exactly one payer and this is it. *)
Require Import LinkKfork ProofSysFork.

Module SysFork := SysForkProof Kfork.
