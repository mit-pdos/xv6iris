(* LinkPlicinit.v -- instantiates the Plicinit proof.  plicinit has no callees,
   so PlicinitProof takes no functor arguments; this is the sole meeting point
   of the spec and its sealed proof. *)
Require Import ProofPlicinit.

Module Plicinit := PlicinitProof.
