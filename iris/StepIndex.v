(* THE STEP INDEX OF THIS DEVELOPMENT, in one place.

   On the transfinite base logic ([transfinite.base_logic], the Transfinite
   Iris core over upstream Iris's parametric layers) every [gFunctors],
   [iProp Σ], ghost-state class and program-logic lemma carries an implicit
   step-index structure [SI : sidx].  A development fixes it by ONE global
   instance, which typeclass search then supplies everywhere; two instances
   in scope would make [iProp] ambiguous, so this file is the only place that
   may declare one, and every file that mentions [gFunctors] or [iProp]
   imports it.

   [natSI] (finite indices, upstream's own [Global Existing Instance natSI]
   in [stepindex_finite]) keeps every proof of the tree as it was: [SIdxFinite
   natSI] holds, so the finite-only later laws are available.  The ordinal
   phase of the port switches this line to [ordI]
   ([transfinite.stepindex.ordinals]); local-plan/transfinite-integration.md. *)
From iris.algebra Require Import stepindex.
From iris.algebra Require Import stepindex_finite.

#[export] Instance xv6_sidx : sidx := natSI.
