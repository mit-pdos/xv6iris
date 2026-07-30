(* LinkBread.v -- instantiates the bread proof against its four callees'
   proofs (acquire / release / acquiresleep / virtio_disk_rw).  Sealed, so
   this is the only place the whole-function proofs ever meet.

   bget() is [static] with bread its only caller, so gcc inlined it: there is
   no separate Link file for the two scan loops or the panic arm. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecBread SpecAcquire SpecRelease SpecAcquiresleep SpecVirtioDiskRw.
Require Import LinkAcquire LinkRelease LinkAcquiresleep LinkVirtioDiskRw ProofBread.

Module Bread := BreadProof Acquire Release Acquiresleep VirtioDiskRw.
