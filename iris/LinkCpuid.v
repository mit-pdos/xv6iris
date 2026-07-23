(* LinkCpuid.v -- instantiates the Cpuid proof.  cpuid has no callees, so
   CpuidProof takes no functor arguments; this is the sole meeting point of
   the spec and its sealed proof. *)
Require Import ProofCpuid.

Module Cpuid := CpuidProof.
