(* LinkProcdump.v -- procdump's seal.

   Unlike every other Link file in the tree this one has nothing to
   instantiate.  procdump's only callee is printk, on its GENERAL path, and
   that contract arrives as a Coq HYPOTHESIS
   ([SpecPrintk.printk_gen_contract]) rather than as a functor argument --
   so the obligation is pushed up to whoever finally discharges it, exactly
   as [SpecPanic.panic_wp_any] is pushed, and procdump's own
   [Print Assumptions] stays at the standing platform axioms.

   See claude-notes/projects/procdump.md. *)
Require Import ProofProcdump.

Module Procdump := ProcdumpProof.
