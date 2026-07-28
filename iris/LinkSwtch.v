(* LinkSwtch.v -- instantiates the Swtch proof.  swtch has no callees (it is a
   leaf assembly routine), so SwtchProof takes no functor arguments; this is the
   sole meeting point of the spec and its sealed proof. *)
Require Import ProofSwtch.

Module Swtch := SwtchProof.
