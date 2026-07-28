(* LinkProcPagetable.v -- instantiates the proc_pagetable proof against its
   callees' proofs (uvmcreate + mappages).  Sealed, so this is the only place
   the three ever meet. *)
Require Import LinkUvmcreate LinkMappages ProofProcPagetable.

Module ProcPagetable := ProcPagetableProof Uvmcreate Mappages.
