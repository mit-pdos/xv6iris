(* LinkNameiparent.v -- nameiparent's single callee, discharged.

   nameiparent calls exactly one function, namex, and [LinkNamex.Namex] is
   that function's real proof composed with its own nine callees.  Nothing is
   assumed here and nameiparent has no panic of its own -- the
   [panic_wp_any] it takes is threaded straight into namex.

   So this cone's assumption count is namex's: the five platform axioms plus
   funext. *)
Require Import LinkNamex.
Require Import ProofNameiparent.

Module Nameiparent := NameiparentProof Namex.
