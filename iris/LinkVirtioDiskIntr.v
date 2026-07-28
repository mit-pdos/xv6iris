(* LinkVirtioDiskIntr.v -- instantiates virtio_disk_intr's proof against its
   callees' proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import LinkAcquire LinkRelease LinkWakeup ProofVirtioDiskIntr.

Module VirtioDiskIntr := VirtioDiskIntrProof Acquire Release Wakeup.
