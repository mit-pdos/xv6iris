(* LinkIunlock.v -- the only file where iunlock's proof meets its callees'.
   Both callees (holdingsleep, releasesleep) are PROVEN, so iunlock carries
   no caveat in tools/proof_coverage.py. *)
Require Import LinkHoldingsleep LinkReleasesleep ProofIunlock.

Module Iunlock := IunlockProof Holdingsleep Releasesleep.
