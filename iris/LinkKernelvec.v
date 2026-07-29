(* LinkKernelvec.v -- instantiates the kernelvec proof against its only
   callee's contract (kerneltrap, assumed -- see LinkKerneltrap.v).  Sealed,
   so this is the only place the two ever meet. *)
Require Import LinkKerneltrap ProofKernelvec.

Module Kernelvec := KernelvecProof Kerneltrap.
