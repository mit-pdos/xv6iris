(* LinkPlicinithart.v -- instantiates the Plicinithart proof against its only
   callee's proof (cpuid).  Sealed, so this is the only place the two meet. *)
Require Import LinkCpuid ProofPlicinithart.

Module Plicinithart := PlicinithartProof Cpuid.
