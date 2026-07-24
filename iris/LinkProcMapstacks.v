(* LinkProcMapstacks.v -- instantiates the proc_mapstacks proof against its
   callees' proofs (kalloc + kvmmap).  Sealed, so this is the only place the
   three ever meet. *)
Require Import LinkKalloc LinkKvmmap ProofProcMapstacks.

Module ProcMapstacks := ProcMapstacksProof Kalloc Kvmmap.
