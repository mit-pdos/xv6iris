(* LinkFreeproc.v -- instantiates the freeproc proof against its callees'
   proofs: kfree for the trapframe page, proc_freepagetable for the user
   table.  Sealed, so this is the only place the three ever meet. *)
Require Import LinkKfree LinkProcFreepagetable ProofFreeproc.

Module Freeproc := FreeprocProof Kfree ProcFreepagetable.
