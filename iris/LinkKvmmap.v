(* LinkKvmmap.v -- instantiates the Kvmmap proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import LinkMappages ProofKvmmap.

Module Kvmmap := KvmmapProof Mappages.
