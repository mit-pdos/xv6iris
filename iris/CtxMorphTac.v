(* CtxMorphTac.v -- THE TRANSPORT-OBLIGATION DRIVER (A6.121, the M3
   λ-conversion).

   A λ-converted lock payload owes [TsoCtx.CtxMorph] for real, and its proof
   is entirely structural: exists / sep / big-ops / boolean branches down to
   the leaves, which are the context cells ([ctx_pointsto] and the three
   word widths) and ξ-constant parts (pure facts, ghost state, ledger cells,
   invariant handles).  Typeclass search resolves these composites in some
   files and not in others -- measured on identical goals, the difference
   being only the file the goal is stated in -- so nothing here relies on
   it: the tactic applies the structural instances BY NAME and stops at
   whatever it cannot decompose, which a caller then closes with the
   payload's own component instances (see DiskInv.v's [DiskResAt]).

   [cur_ctx] is unfolded first: a payload spelled with the ambient
   notations elaborates its cells at [@cur_ctx XI], and once [XI] is
   instantiated at the λ's binder the projection has to go before the leaf
   lemmas can see the binder.  A separate file so that the tactic can grow
   without re-certifying [TsoCtx]'s cone. *)
From iris.proofmode Require Import proofmode.
Require Import TsoCtx.

Ltac ctx_morph_leaf :=
  first [ apply ctx_morph_pointsto
        | apply ctx_morph_word
        | apply ctx_morph_word2
        | apply ctx_morph_word4
        | apply ctx_morph_const ].

Ltac ctx_morph_solve :=
  try rewrite /cur_ctx; cbv beta;
  repeat first
    [ apply ctx_morph_exist; intros ?
    | apply ctx_morph_sep
    | apply ctx_morph_big_sepL; intros ? ?
    | apply ctx_morph_big_sepM; intros ? ?
    | apply ctx_morph_if
    | ctx_morph_leaf ].
