(* LinkIunlockput.v -- the only file where iunlockput's proof meets its
   callees'.  Both callees (iunlock, iput) are PROVEN and themselves
   axiom-free, so iunlockput carries no caveat in tools/proof_coverage.py
   and this cone's assumption count stays at ZERO. *)
Require Import LinkIunlock LinkIput ProofIunlockput.

Module Iunlockput := IunlockputProof Iunlock Iput.
