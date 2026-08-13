(* LinkPrintk.v -- instantiates the Printk proof against its callees'
   proofs.  Sealed, so this is the only place the four ever meet.

   printk gained [acquire]/[release] as callees with upstream d80e61c5: the
   [panicking] flag is gone, so pr.lock is now taken unconditionally. *)
Require Import LinkConsputc LinkPrintint LinkAcquire LinkRelease ProofPrintk.

Module Printk := PrintkProof Consputc Printint Acquire Release.
