(* LinkSched.v -- instantiates the Sched proof against its callees' proofs
   (myproc, holding, swtch).  Sealed, so this is the only place the four meet. *)
Require Import LinkMyproc LinkHolding WpSwtchSconf ProofSched.

Module Sched := SchedProof Myproc Holding SwtchProof.
