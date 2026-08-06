(* LinkReparent.v -- instantiates the reparent proof against its one callee's
   proof (wakeup, itself proven and linked).  Sealed, so this is the only place
   the two ever meet. *)
Require Import LinkWakeup ProofReparent.

Module Reparent := ReparentProof Wakeup.
