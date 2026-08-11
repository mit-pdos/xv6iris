(* LinkStati.v -- stati is a LEAF (it calls nothing), so StatiProof takes no
   functor arguments; the module is still sealed by [STATI] here, which is
   what makes the whole-function spec count as proven for
   tools/proof_coverage.py. *)
Require Import ProofStati.

Module Stati := StatiProof.
