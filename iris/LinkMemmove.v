(* LinkMemmove.v -- instantiates the Memmove proof against its callees' proofs.
   Sealed, so this is the only place the two ever meet.  memmove is a leaf (it
   calls nothing), so there is nothing to pass in; the module is still sealed by
   [MEMMOVE] here, which is what makes the whole-function spec count as proven
   for tools/proof_coverage.py. *)
Require Import ProofMemmove.

Module Memmove := MemmoveProof.
