(* LinkPrintint.v -- instantiates the Printint proof against its callee's
   proof.  Sealed, so this is the only place the two ever meet. *)
Require Import LinkConsputc ProofPrintint.

Module Printint := PrintintProof Consputc.
