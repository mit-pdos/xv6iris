(* LinkSysFork.v -- sys_fork's proof, instantiated against the REAL proof of
   its one callee.  kfork's contract has exactly one payer and this is it. *)
Require Import LinkKfork ProofSysFork.

(* NO GENERIC-WP ARGUMENT.  kfork's linear child-WP premise is sys_fork's
   own premise now: the forking process deposits its child continuation at
   the ecall and the trap route hands it down, so there is nothing to mint
   here.  [LinkUserinit] is the tree's one remaining mint site. *)
Module SysFork := SysForkProof Kfork.
