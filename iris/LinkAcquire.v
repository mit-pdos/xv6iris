(* LinkAcquire.v -- instantiates the Acquire proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet.

   [AcquireGen] is the [lock_openable]-generic proof; [Acquire] is its
   static-kernel-lock instance ([Tc := emp], [Dc := False]), which is what the
   thirteen ordinary consumers take. *)
Require Import LinkMycpu LinkHolding LinkPushOff ProofAcquire.

Module AcquireGen := AcquireGenProof Mycpu Holding PushOff.
Module Acquire := AcquireOfGen AcquireGen.
