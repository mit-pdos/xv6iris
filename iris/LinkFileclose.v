(* LinkFileclose.v -- instantiates the Fileclose proof against its callees'
   proofs.  Sealed, so this is the only place the six ever meet.

   [IputCompat] is the one that is ASSUMED (LinkIputCompat.v supplies it with an
   [Axiom], the single fs-side assumption in this cone); the other five are
   real proofs.  Nothing else about fileclose rests on an assumption: the
   [f->ref < 1] panic arm is dead, so even [panic] does not appear here. *)
Require Import LinkAcquire LinkRelease LinkPipeclose LinkBeginOp LinkIputCompat
                LinkEndOp ProofFileclose.

Module Fileclose := FilecloseProof Acquire Release Pipeclose BeginOp IputCompat EndOp.
