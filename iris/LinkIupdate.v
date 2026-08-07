(* LinkIupdate.v -- the only file where iupdate's proof meets its callees'.
   All four callees (bread, memmove, log_write, brelse) are PROVEN, so
   iupdate carries no caveat in tools/proof_coverage.py. *)
Require Import LinkBread LinkMemmove LinkLogWrite LinkBrelse ProofIupdate.

Module Iupdate := IupdateProof Bread Memmove LogWrite Brelse.
