(* LinkBread.v -- instantiates the Bread proof against its callees' proofs
   (acquire / release / acquiresleep / virtio_disk_rw).  Sealed, so this is the
   only place the five ever meet.  virtio_disk_rw's own contract is still
   assumed (LinkVirtioDiskRw.v); bread consumes its INTERFACE, so this link is
   independent of that. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecBread SpecAcquire SpecRelease SpecAcquiresleep SpecVirtioDiskRw.
Require Import LinkAcquire LinkRelease LinkAcquiresleep LinkVirtioDiskRw ProofBread.

Module Bread := BreadProof Acquire Release Acquiresleep VirtioDiskRw.
