(* LinkEntry.v -- instantiates the M-mode boot proof.  [EntryProof] composes the
   piecemeal M-mode lemmas directly (they are plain lemmas, not spec modules),
   so it takes no functor arguments; this is the sole meeting point of the
   [ENTRY] spec and its sealed proof. *)
Require Import ProofEntry.

Module Entry := EntryProof.
