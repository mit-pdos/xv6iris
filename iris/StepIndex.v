(* THE STEP INDEX OF THIS DEVELOPMENT, in one place.

   On the transfinite base logic ([transfinite.base_logic], the Transfinite
   Iris core over upstream Iris's parametric layers) every [gFunctors],
   [iProp Σ], ghost-state class and program-logic lemma carries an implicit
   step-index structure [SI : sidx].  A development fixes it by ONE global
   instance, which typeclass search then supplies everywhere; two instances
   in scope would make [iProp] ambiguous, so this file is the only place that
   may declare one, and every file that mentions [gFunctors] or [iProp]
   imports it.

   The index is the ORDINALS, [ordI] ([transfinite.stepindex.ordinals]):
   [SIdxFinite] does not hold, so the later laws that are true only at finite
   indices ([later_sep_1], [later_exist_false] and what upstream derives from
   them, e.g. destructing [▷ (P ∗ Q)] or [▷ ∃ x, P x] in the proof mode) are
   unavailable; what the ordinals give instead is the existential property
   the liveness work needs.  [iris.algebra.stepindex_finite] must NOT be
   imported anywhere: it declares [natSI] a global instance, and two [sidx]
   instances in scope make every [iProp] ambiguous.  (The finite-index state
   of the port, [natSI], is branch [transfinite] before the ordinal port;
   local-plan/port-ordinal.md.) *)
From iris.algebra Require Import stepindex.
From transfinite.stepindex Require Import ordinals.

#[export] Instance xv6_sidx : sidx := ordI.
