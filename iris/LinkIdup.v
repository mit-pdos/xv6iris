(* LinkIdup.v -- instantiates the Idup proof against its callees' proofs.
   Sealed, so this is the only place the three ever meet.

   This file used to hold an [Axiom]: there was no inode model, so nothing
   about [ip->ref] or [itable.lock] was statable against real code and
   idup's contract was assumed outright.  [IcacheInv.v] supplied the model
   and [ProofIdup.v] the proof, so the axiom is gone -- which is the whole
   visible effect of this change on [tools/proof_coverage.py]. *)
Require Import LinkAcquire LinkRelease ProofIdup.

Module Idup := IdupProof Acquire Release.
