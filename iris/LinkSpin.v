(* LinkSpin.v -- instantiates the Spin proof.  [spin] has no callees, so
   SpinProof takes no functor arguments; this is the sole meeting point of the
   spec and its sealed proof. *)
Require Import ProofSpin.

Module Spin := SpinProof.
