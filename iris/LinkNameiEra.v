(* LinkNameiEra.v -- namei's single callee at the ERA trace contract,
   discharged.

   [LinkNameiTr.v]'s shape: namei calls exactly one function, and
   [LinkNamexEra.NamexEra] is the era walk's real proof composed with its
   own nine callees.  Nothing is assumed and namei has no panic of its own.

   So this cone's assumption count is the walk's: the five platform axioms
   plus funext. *)
Require Import LinkNamexEra.
Require Import ProofNameiEra.

Module NameiEra := NameiEraProof NamexEra.
