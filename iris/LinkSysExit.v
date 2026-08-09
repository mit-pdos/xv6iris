(* LinkSysExit.v -- sys_exit's proof, instantiated against the REAL proofs of
   its two callees. *)
Require Import LinkArgint LinkKexit ProofSysExit.

Module SysExit := SysExitProof Argint Kexit.
