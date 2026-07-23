(* LinkPlicComplete.v -- instantiates the PlicComplete proof against its only
   callee's proof (cpuid).  Sealed, so this is the only place the two meet. *)
Require Import LinkCpuid ProofPlicComplete.

Module PlicComplete := PlicCompleteProof Cpuid.
