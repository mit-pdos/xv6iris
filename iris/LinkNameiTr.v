(* LinkNameiTr.v -- namei's single callee at the trace contract,
   discharged.

   [LinkNamei.v]'s shape: namei calls exactly one function, and
   [LinkNamexTr.NamexTr] is the trace walk's real proof composed with its
   own nine callees.  Nothing is assumed and namei has no panic of its own.

   So this cone's assumption count is the walk's: the five platform axioms
   plus funext. *)
Require Import LinkNamexTr.
Require Import ProofNameiTr.

Module NameiTr := NameiTrProof NamexTr.
