(* LinkStrlen.v -- instantiates the Strlen proof.  strlen is a leaf (it calls
   nothing), so StrlenProof takes no functor arguments; the module is still
   sealed by [STRLEN] here, which is what makes the whole-function spec count
   as proven for tools/proof_coverage.py. *)
Require Import ProofStrlen.

Module Strlen := StrlenProof.
