(* LinkPrintint.v -- instantiates the Printint proof against its callee's
   proof.  Sealed, so this is the only place the two ever meet.

   THE CALLEE IS [prputc] AT XV6_REV 163d39b, not [consputc]: printint's digit
   loop prints to the SECOND 16550 ([SpecPrputc.v]).  consputc is still the
   console's own path and still has its own Spec/Proof/Link; nothing here
   touches them. *)
Require Import LinkPrputc ProofPrintint.

Module Printint := PrintintProof Prputc.
