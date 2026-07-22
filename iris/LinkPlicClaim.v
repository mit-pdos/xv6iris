(* LinkPlicClaim.v -- instantiates the PlicClaim proof against its only callee's
   proof (cpuid).  Sealed, so this is the only place the two meet. *)
Require Import LinkCpuid WpSconfPlicClaim.

Module PlicClaim := PlicClaimProof Cpuid.
