(* LinkVirtioDiskInit.v -- instantiates the virtio_disk_init proof against its
   callees' proofs (initlock + kalloc + memset).  Sealed, so this is the only
   place they ever meet.  The whole-function memset spec [MEMSET] is
   [MemsetArray] (LinkMemsetArray), not the [MEMSET_PARTS] module [Memset].

   The contract is stated over the time-0 device invariant ([WpUart.disk_inv]
   plus the config tracker) and discharged by ProofVirtioDiskInit.v against the
   invariant-opening accessor leaves of WpVirtioDev.v. *)
Require Import LinkInitlock LinkKalloc LinkMemsetArray ProofVirtioDiskInit.

Module VirtioDiskInit := VirtioDiskInitProof Initlock Kalloc MemsetArray.
