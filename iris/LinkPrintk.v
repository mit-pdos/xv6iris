(* LinkPrintk.v -- instantiates the Printk proof against its callees'
   proofs.  Sealed, so this is the only place the three ever meet. *)
Require Import LinkConsputc LinkPrintint ProofPrintk.

Module Printk := PrintkProof Consputc Printint.
