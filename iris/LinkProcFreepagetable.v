(* LinkProcFreepagetable.v -- proc_freepagetable, instantiated against the
   two callee interfaces it needs: uvmunmap's FIXED-LEAF seal (its two
   [do_free = 0] calls, the ones that take the trampoline and the trapframe
   out of the table) and uvmfree. *)
Require Import LinkUvmunmapFixed LinkUvmfree.
Require Import ProofProcFreepagetable.

Module ProcFreepagetable := ProcFreepagetableProof UvmunmapFixed Uvmfree.
