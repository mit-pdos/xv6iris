(* LinkSafestrcpy.v -- instantiates the Safestrcpy proof.  safestrcpy is a
   leaf (it calls nothing), so SafestrcpyProof takes no functor arguments;
   the module is still sealed by [SAFESTRCPY] here, which is what makes the
   whole-function spec count as proven for tools/proof_coverage.py. *)
Require Import ProofSafestrcpy.

Module Safestrcpy := SafestrcpyProof.
