(* LinkNameiRoot.v -- namei's root corner meets namex's.

   One functor application over [LinkNamexRoot.NamexRoot], whose own cone is
   just [iget] (see [LinkNamexRoot.v]).  The walk's nine callees are
   [LinkNamex.v]'s and none of them is here. *)
Require Import LinkNamexRoot.
Require Import ProofNameiRoot.

Module NameiRoot := NameiRootProof NamexRoot.
