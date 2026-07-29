(* LinkUvmfree.v -- instantiates the Uvmfree proof against its two callees'
   proofs.  Note WHICH uvmunmap: the BARE seal (LinkUvmunmapBare.v), because
   by the time uvmfree runs, proc_freepagetable has already dropped the
   trampoline and trapframe leaves and the table is at [BarePt.bare_pt].
   Sealed, so this is the only place the three ever meet. *)
Require Import LinkUvmunmapBare LinkFreewalk.
Require Import ProofUvmfree.

Module Uvmfree := UvmfreeProof UvmunmapBare Freewalk.
