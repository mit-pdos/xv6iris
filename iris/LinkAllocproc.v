(* LinkAllocproc.v -- instantiates the allocproc proof against its callees'
   proofs.  Sealed, so this is the only place they ever meet.

   Every callee is a real proof -- allocpid, acquire, release, kalloc,
   proc_pagetable, the general array memset and now freeproc -- so the whole
   cone is axiom-free.

   TWO MODULES COME OUT, and both are wanted.  [AllocprocGen] is the general
   contract: it says what allocproc does at ANY page budget, including the
   two freeproc failure tails, and it is what kfork (which has no budget)
   will call.  [Allocproc] is the counted one derived from it, whose caller's
   [K_allocproc < nb] refutes those tails; userinit uses that.  The general
   proof is elaborated ONCE and the seal is a thirty-line wrapper over it. *)
Require Import LinkAcquire LinkRelease LinkAllocpid LinkKalloc LinkProcPagetable LinkMemsetArray LinkFreeproc.
Require Import ProofAllocproc.

Module AllocprocGen :=
  AllocprocCore Acquire Release Allocpid Kalloc ProcPagetableGen MemsetArray Freeproc.
Module Allocproc := AllocprocSeal AllocprocGen.
