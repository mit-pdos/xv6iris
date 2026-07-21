(* LinkPlicComplete.v -- instantiates the PlicComplete proof against its only
   callee's proof (cpuid).  Sealed, so this is the only place the two meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecPlicComplete SpecCpuid.
Require Import LinkCpuid WpSconfPlicComplete.

Module PlicComplete := PlicCompleteProof Cpuid.
