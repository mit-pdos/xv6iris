(* LinkAllocproc.v -- instantiates the allocproc proof against its callees'
   proofs.  Sealed, so this is the only place they ever meet.

   [Allocpid] is the one ASSUMED callee (LinkAllocpid.v supplies its contract
   with an [Axiom]); everything else -- acquire, release, kalloc,
   proc_pagetable and the general array memset -- is a real proof. *)
Require Import LinkAcquire LinkRelease LinkAllocpid LinkKalloc LinkProcPagetable LinkMemsetArray.
Require Import ProofAllocproc.

Module Allocproc := AllocprocProof Acquire Release Allocpid Kalloc ProcPagetable MemsetArray.
