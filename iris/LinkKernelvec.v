(* LinkKernelvec.v -- instantiates the kernelvec proof against its only
   callee's contract: [SpecKerneltrap.KERNELTRAP], the REAL one, which
   LinkKerneltrap discharges with a theorem.  Sealed, so this is the only
   place the two ever meet -- and nothing in the cone is assumed any more. *)
Require Import LinkKerneltrap ProofKernelvec.

Module Kernelvec := KernelvecProof Kerneltrap.
