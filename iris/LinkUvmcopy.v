(* LinkUvmcopy.v -- instantiates the Uvmcopy proof against its six callees'
   proofs.  Sealed, so this is the only place the seven ever meet.  Note the
   uvmunmap seal: the [proc_pt] one (LinkUvmunmap.v), because uvmcopy's [err]
   path unmaps the CHILD, which is a live process page table -- unlike
   uvmfree, which runs on a bare one. *)
Require Import LinkWalkNoalloc LinkKalloc LinkMemmove LinkMappages.
Require Import LinkKfree LinkUvmunmap.
Require Import ProofUvmcopy.

Module Uvmcopy := UvmcopyProof WalkNoalloc Kalloc Memmove Mappages Kfree Uvmunmap.
