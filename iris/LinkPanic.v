(* LinkPanic.v -- instantiates panic's proof against its callee's.

   panic's only callee is printk, on the one path printk now has
   ([LinkPrintk.v]'s [Printk], proven).  Nothing here moved at 163d39b: the
   functor arity is the same and printk's contract lost arguments rather than
   gaining any. *)
Require Import LinkPrintk ProofPanic.

Module Panic := PanicProof Printk.
