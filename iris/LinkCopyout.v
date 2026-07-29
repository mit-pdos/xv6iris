(* LinkCopyout.v -- instantiates the Copyout proof against its callees' proofs
   (walkaddr, vmfault, the no-alloc walk, memmove).  Sealed, so this is the
   only place the five ever meet. *)
Require Import LinkWalkaddr LinkVmfault LinkWalkNoalloc LinkMemmove.
Require Import ProofCopyout.

Module Copyout := CopyoutProof Walkaddr Vmfault WalkNoalloc Memmove.
