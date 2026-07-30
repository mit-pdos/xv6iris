(* LinkVirtioDiskInit.v -- instantiates the virtio_disk_init proof against its
   callees' proofs (initlock + kalloc + memset).  Sealed, so this is the only
   place they ever meet.  The whole-function memset spec [MEMSET] is
   [MemsetArray] (LinkMemsetArray), not the [MEMSET_PARTS] module [Memset].

   The contract was ASSUMED here for one commit, while it was restated over
   the time-0 device invariant ([WpUart.disk_inv] plus the config tracker);
   ProofVirtioDiskInit.v now discharges it against the invariant-opening
   accessor leaves of WpVirtioDev.v, so the [Axiom] is gone. *)
Require Import LinkInitlock LinkKalloc LinkMemsetArray ProofVirtioDiskInit.

Module VirtioDiskInit := VirtioDiskInitProof Initlock Kalloc MemsetArray.
