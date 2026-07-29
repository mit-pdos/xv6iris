(* LinkUvmunmapBare.v -- the BARE seal of the same uvmunmap proof, against
   the same two callees.  ProofUvmunmap.v proves the function ONCE over
   BarePt.v's [otf] axis and seals it twice; LinkUvmunmap.v instantiates the
   [Some] end (every existing caller, at [proc_pt]) and this file the [None]
   end, which is what uvmfree runs on -- proc_freepagetable has already
   dropped the trampoline and trapframe leaves. *)
Require Import LinkWalkNoalloc LinkKfree.
Require Import ProofUvmunmap.

Module UvmunmapBare := UvmunmapBareProof WalkNoalloc Kfree.
