(* LinkPlicClaim.v -- instantiates the PlicClaim proof against its only callee's
   proof (cpuid).  Sealed, so this is the only place the two meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecPlicClaim SpecCpuid.
Require Import LinkCpuid WpSconfPlicClaim.

Module PlicClaim := PlicClaimProof Cpuid.
