(* LinkPlicinithart.v -- instantiates the Plicinithart proof against its only
   callee's proof (cpuid).  Sealed, so this is the only place the two meet. *)
Require Import RiscvLang RiscvPtsto SmodeCore.
Require Import SpecPlicinithart SpecCpuid.
Require Import LinkCpuid WpSconfPlicinithart.

Module Plicinithart := PlicinithartProof Cpuid.
