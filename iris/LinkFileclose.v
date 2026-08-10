(* LinkFileclose.v -- instantiates the Fileclose proof against its callees'
   proofs.  Sealed, so this is the only place the six ever meet.

   ALL SIX ARE REAL PROOFS as of C6b: [Iput] is [LinkIput]'s, over the real
   inode cache, and the bridging axiom this file used to import is gone.
   Nothing about fileclose rests on an assumption: the [f->ref < 1] panic arm
   is dead, so even [panic] does not appear here. *)
Require Import LinkAcquire LinkRelease LinkPipeclose LinkBeginOp LinkIput
                LinkEndOp ProofFileclose.

Module Fileclose := FilecloseProof Acquire Release Pipeclose BeginOp Iput EndOp.
