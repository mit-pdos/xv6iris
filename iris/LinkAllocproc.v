(* LinkAllocproc.v -- instantiates the allocproc proof against its callees'
   proofs.  Sealed, so this is the only place they ever meet.

   Every callee is a real proof -- allocpid, acquire, release, kalloc,
   proc_pagetable and the general array memset -- so the whole cone is
   axiom-free. *)
Require Import LinkAcquire LinkRelease LinkAllocpid LinkKalloc LinkProcPagetable LinkMemsetArray.
Require Import ProofAllocproc.

Module Allocproc := AllocprocProof Acquire Release Allocpid Kalloc ProcPagetable MemsetArray.
