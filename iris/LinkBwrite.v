(* LinkBwrite.v -- instantiates the bwrite proof against its two callees'
   proofs (holdingsleep and virtio_disk_rw).  Sealed, so this is the only
   place the three whole-function proofs ever meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecBwrite SpecHoldingsleep SpecVirtioDiskRw.
Require Import LinkHoldingsleep LinkVirtioDiskRw ProofBwrite.

Module Bwrite := BwriteProof Holdingsleep VirtioDiskRw.
