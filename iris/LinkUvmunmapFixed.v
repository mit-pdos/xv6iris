(* LinkUvmunmapFixed.v -- the FIXED-LEAF seal of the same uvmunmap proof,
   against the same two callees.  ProofUvmunmap.v proves the function ONCE
   over BarePt.v's fixed-leaf map [fx] and its [do_free] boolean, and seals
   it three times: LinkUvmunmap.v instantiates the live end (every existing
   caller, at [proc_pt]), LinkUvmunmapBare.v the bare end (what uvmfree runs
   on), and this file the [do_free = 0] instance that MOVES a table between
   them -- proc_freepagetable's two calls, and proc_pagetable's second
   mappages failure tail. *)
Require Import LinkWalkNoalloc LinkKfree.
Require Import ProofUvmunmap.

Module UvmunmapFixed := UvmunmapFixedProof WalkNoalloc Kfree.
