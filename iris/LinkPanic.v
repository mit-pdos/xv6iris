(* LinkPanic.v -- instantiates panic's proof against its callee's.

   panic's only callee is printk, on the one path printk now has
   ([LinkPrintk.v]'s [Printk], proven).  The placeholder credential panic
   still hands printk for acquire's "already holding" arm is a HYPOTHESIS of
   [SpecPanic.wp_panic_sconf_body], not an axiom of this link -- see
   the placeholder this replaced. *)
Require Import LinkPrintk ProofPanic.

Module Panic := PanicProof Printk.
