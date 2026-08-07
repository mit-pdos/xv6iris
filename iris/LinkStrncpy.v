(* LinkStrncpy.v -- exposes the sealed whole-machine proof of strncpy.
   strncpy is a leaf, so the implementation module takes no callees. *)
Require Import ProofStrncpy.

Module Strncpy := StrncpyProof.
