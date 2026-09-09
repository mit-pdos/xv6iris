(* LinkFreeproc.v -- instantiates the freeproc proof against its callees'
   proofs: kfree for the trapframe page, proc_freepagetable for the user
   table, and acquire/release for the <pid_lock> pair around [p->pid = 0]
   (upstream ded23f2).  Sealed, so this is the only place they ever meet. *)
Require Import LinkAcquire LinkRelease LinkKfree LinkProcFreepagetable ProofFreeproc.

Module Freeproc := FreeprocProof Acquire Release Kfree ProcFreepagetable.
