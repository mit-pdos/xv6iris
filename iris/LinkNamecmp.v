(* LinkNamecmp.v -- the only file where namecmp's proof meets its callee's.
   strncmp is PROVEN and axiom-free, so namecmp carries no caveat in
   tools/proof_coverage.py. *)
Require Import LinkStrncmp ProofNamecmp.

Module Namecmp := NamecmpProof Strncmp.
