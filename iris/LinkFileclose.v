(* LinkFileclose.v -- instantiates the Fileclose proof against its callees'
   proofs.  Sealed, so this is the only place the six ever meet.

   [Iput] is the one that is ASSUMED (LinkIput.v supplies its contract with an
   [Axiom], the single fs-side assumption in this cone); the other five are
   real proofs.  Nothing else about fileclose rests on an assumption: the
   [f->ref < 1] panic arm is dead, so even [panic] does not appear here. *)
Require Import LinkAcquire LinkRelease LinkPipeclose LinkBeginOp LinkIput
                LinkEndOp ProofFileclose.

Module Fileclose := FilecloseProof Acquire Release Pipeclose BeginOp Iput EndOp.
