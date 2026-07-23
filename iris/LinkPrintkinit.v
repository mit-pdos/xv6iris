(* LinkPrintkinit.v -- instantiates the Printkinit proof against its callee's
   proof.  Sealed, so this is the only place the two ever meet. *)
Require Import LinkInitlock ProofPrintkinit.

Module Printkinit := PrintkinitProof Initlock.
