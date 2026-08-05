(* LinkProcPagetable.v -- instantiates the proc_pagetable proof against its
   callees' proofs.  FOUR of them now: uvmcreate and mappages on the success
   path, and uvmfree + uvmunmap(fixed) in the two error tails.  Sealed, so
   this is the only place they ever meet. *)
Require Import LinkUvmcreate LinkMappages LinkUvmfree LinkUvmunmapFixed.
Require Import ProofProcPagetable.

(* the counted contract, unchanged: what allocproc's SUCCESS path uses *)
Module ProcPagetable := ProcPagetableProof Uvmcreate Mappages Uvmfree UvmunmapFixed.

(* the general one, at an arbitrary [on] -- what a caller outside the counted
   regime (allocproc's own failure tails, and anything reached from them)
   needs, since there is no way back to a count once uvmfree has resealed. *)
Module ProcPagetableGen := ProcPagetableCore Uvmcreate Mappages Uvmfree UvmunmapFixed.
