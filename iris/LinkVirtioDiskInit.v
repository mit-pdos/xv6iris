(* LinkVirtioDiskInit.v -- instantiates the virtio_disk_init proof against its
   callees' proofs (initlock + kalloc + memset).  Sealed, so this is the only
   place they ever meet.  The whole-function memset spec [MEMSET] is
   [MemsetArray] (LinkMemsetArray), not the [MEMSET_PARTS] module [Memset]. *)
Require Import LinkInitlock LinkKalloc LinkMemsetArray ProofVirtioDiskInit.

Module VirtioDiskInit := VirtioDiskInitProof Initlock Kalloc MemsetArray.
