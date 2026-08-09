(* LinkStrncmp.v -- instantiates the Strncmp proof.  strncmp is a leaf (it calls
   nothing), so StrncmpProof takes no functor arguments; the module is still
   sealed by [STRNCMP] here, which is what makes the whole-function spec count
   as proven for tools/proof_coverage.py. *)
Require Import ProofStrncmp.

Module Strncmp := StrncmpProof.
