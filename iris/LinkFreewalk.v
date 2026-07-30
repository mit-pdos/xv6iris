(* LinkFreewalk.v -- instantiates the Freewalk proof against its callee's
   proof (kfree; the recursive self-call is served by the induction inside
   ProofFreewalk, not by a functor argument).  Sealed, so this is the only
   place the two ever meet. *)
Require Import LinkKfree ProofFreewalk.

Module Freewalk := FreewalkProof Kfree.
