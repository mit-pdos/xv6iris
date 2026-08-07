(* LinkSysWait.v -- sys_wait's proof, instantiated against the REAL proofs of
   its two callees. *)
Require Import LinkArgaddr LinkKwait ProofSysWait.

Module SysWait := SysWaitProof Argaddr Kwait.
