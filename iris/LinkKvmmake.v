(* LinkKvmmake.v -- instantiates the kvmmake proof against its callees' proofs
   (kalloc + memset + kvmmap + proc_mapstacks).  Sealed, so this is the only
   place the four ever meet.  The whole-function memset spec [MEMSET] is
   [MemsetArray] (LinkMemsetArray), not the [MEMSET_PARTS] module [Memset]. *)
Require Import LinkKalloc LinkMemsetArray LinkKvmmap LinkProcMapstacks ProofKvmmake.

Module Kvmmake := KvmmakeProof Kalloc MemsetArray Kvmmap ProcMapstacks.
