(* LinkCopyin.v -- instantiates the Copyin proof against its callees' proofs
   (walkaddr, vmfault, memmove).  Sealed, so this is the only place the four
   ever meet. *)
Require Import LinkWalkaddr LinkVmfault LinkMemmove.
Require Import ProofCopyin.

Module Copyin := CopyinProof Walkaddr Vmfault Memmove.
