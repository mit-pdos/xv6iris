(* LinkKvminithart.v -- seals the kvminithart proof.  kvminithart has no
   callees (straight-line Bare->Sv39 switch), so this instantiates the
   callee-less [KvminithartProof] module directly. *)
Require Import ProofKvminithart.

Module Kvminithart := KvminithartProof.
