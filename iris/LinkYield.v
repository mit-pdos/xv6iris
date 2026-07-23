(* LinkYield.v -- instantiates the Yield proof against its callees' proofs
   (myproc / acquire / sched / release).  Sealed, so this is the only place
   the whole-function proofs ever meet. *)
Require Import LinkMyproc LinkAcquire LinkSched LinkRelease ProofYield.

Module Yield := YieldProof Myproc Acquire Sched Release.
