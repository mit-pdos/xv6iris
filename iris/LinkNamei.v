(* LinkNamei.v -- namei's single callee, discharged.

   namei calls exactly one function, namex, and [LinkNamex.Namex] is that
   function's real proof composed with its own nine callees (myproc, idup,
   iget, memmove, ilock, iunlock, iunlockput, dirlookup, iput).  Nothing is
   assumed here and namei has no panic of its own -- the [panic_wp_any] it
   takes is threaded straight into namex.

   So this cone's assumption count is namex's: the five platform axioms plus
   funext. *)
Require Import LinkNamex.
Require Import ProofNamei.

Module Namei := NameiProof Namex.
