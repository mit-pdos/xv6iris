(* LinkProcPagetable.v -- instantiates the proc_pagetable proof against its
   callees' proofs.  FOUR of them now: uvmcreate and mappages on the success
   path, and uvmfree + uvmunmap(fixed) in the two error tails.  Sealed, so
   this is the only place they ever meet. *)
Require Import LinkUvmcreate LinkMappages LinkUvmfree LinkUvmunmapFixed.
Require Import ProofProcPagetable.

Module ProcPagetable := ProcPagetableProof Uvmcreate Mappages Uvmfree UvmunmapFixed.
