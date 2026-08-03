(* LinkSysPause.v -- sys_pause's proof, instantiated against the REAL proofs
   of the six functions it calls. *)
Require Import LinkArgint LinkAcquire LinkRelease LinkMyproc LinkKilled LinkSleep ProofSysPause.

Module SysPause := SysPauseProof Argint Acquire Release Myproc Killed Sleep.
