(* LinkBfree.v -- the only file where bfree's proof meets its callees'.
   All three callees (bread, log_write, brelse) are PROVEN, so bfree carries
   no caveat in tools/proof_coverage.py.  bfree's own panic is DEAD (refuted
   from the caller's byte run against the free pool, see
   ProofBfree.v), so no panic contract is instantiated here. *)
Require Import LinkBread LinkLogWrite LinkBrelse ProofBfree.

Module Bfree := BfreeProof Bread LogWrite Brelse.
