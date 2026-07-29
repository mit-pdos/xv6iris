(* LinkSysSbrk.v -- instantiates the SysSbrk proof against its callees'
   proofs.  Sealed, so this is the only place the four ever meet. *)
Require Import LinkArgint LinkMyproc LinkGrowproc.
Require Import ProofSysSbrk.

Module SysSbrk := SysSbrkProof Argint Myproc Growproc.
