(* LinkIlock.v -- the only file where ilock's proof meets its callees'.
   All four callees (acquiresleep, bread, memmove, brelse) are PROVEN, so
   ilock carries no caveat in tools/proof_coverage.py. *)
Require Import LinkAcquiresleep LinkBread LinkMemmove LinkBrelse ProofIlock.

Module Ilock := IlockProof Acquiresleep Bread Memmove Brelse.
