(* LinkWakeup.v -- instantiates the Wakeup proof against its callees'
   proofs.  Sealed, so this is the only place the two ever meet. *)
Require Import WpSconfWakeup.

Module Wakeup := WakeupProof.
