(* LinkTrapinithart.v -- seals the trapinithart proof.  trapinithart has no
   callees (straight-line csrw stvec), so this instantiates the callee-less
   [TrapinithartProof] module directly. *)
Require Import ProofTrapinithart.

Module Trapinithart := TrapinithartProof.
