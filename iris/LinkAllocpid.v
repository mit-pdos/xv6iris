(* LinkAllocpid.v -- instantiates the allocpid proof against its callees'
   proofs (acquire + release).  Sealed, so this is the only place they meet.

   allocpid is proved, so allocproc's whole cone is axiom-free. *)
Require Import LinkAcquire LinkRelease ProofAllocpid.

Module Allocpid := AllocpidProof Acquire Release.
