(* LinkBwrite.v -- instantiates the Bwrite proof against its callees' proofs
   (holdingsleep / virtio_disk_rw).  Sealed, so this is the only place the
   three ever meet.  virtio_disk_rw's own contract is still assumed
   (LinkVirtioDiskRw.v); bwrite consumes its INTERFACE, so this link is
   independent of that. *)
Require Import LinkHoldingsleep LinkVirtioDiskRw ProofBwrite.

Module Bwrite := BwriteProof Holdingsleep VirtioDiskRw.
