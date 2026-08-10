(* LinkMemcpy.v -- the only file where memcpy's proof meets its callee's.
   memcpy's one callee, memmove, is PROVEN, so memcpy carries no caveat in
   tools/proof_coverage.py. *)
Require Import LinkMemmove ProofMemcpy.

Module Memcpy := MemcpyProof Memmove.
