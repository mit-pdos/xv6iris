(* LinkKernelvec.v -- instantiates the kernelvec proof against its only
   callee's contract ([KERNELTRAP_RETURNS], assumed -- see LinkKerneltrap.v;
   kerneltrap ITSELF is proven, this is the handler-contract shape).  Sealed,
   so this is the only place the two ever meet. *)
Require Import LinkKerneltrap ProofKernelvec.

Module Kernelvec := KernelvecProof KerneltrapRet.
