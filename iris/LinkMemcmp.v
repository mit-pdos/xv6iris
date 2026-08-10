(* LinkMemcmp.v -- instantiates the Memcmp proof.  memcmp is a leaf (it calls
   nothing), so MemcmpProof takes no functor arguments; the module is still
   sealed by [MEMCMP] here, which is what makes the whole-function spec count
   as proven for tools/proof_coverage.py. *)
Require Import ProofMemcmp.

Module Memcmp := MemcmpProof.
