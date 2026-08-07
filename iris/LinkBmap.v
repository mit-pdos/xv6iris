(* LinkBmap.v -- the only file where bmap's proof meets its callees'.
   balloc is ASSUMED (LinkBalloc.v supplies the single Axiom instance), so
   bmap counts as proven-with-caveat in tools/proof_coverage.py. *)
Require Import LinkBalloc LinkBread LinkBrelse LinkLogWrite ProofBmap.

Module Bmap := BmapProof Balloc Bread Brelse LogWrite.
