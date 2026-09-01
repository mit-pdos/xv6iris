(* CtxMorphTac.v -- THE TRANSPORT-OBLIGATION DRIVER (A6.121, the M3
   λ-conversion; tso-flip CtxMorphTac.v).

   A λ-converted lock payload owes [TsoCtx.CtxMorph] for real, and its proof
   is entirely structural: exists / sep / big-ops / boolean branches down to
   the leaves, which are the context cells ([ctx_pointsto] and the word
   widths) and ξ-constant parts (pure facts, ghost state, invariant
   handles).

   WHY THIS IS A TACTIC AND NOT TYPECLASS SEARCH.  Three reasons, all
   structural, and all of them get WORSE as the tree grows:

   1. [CtxMorph]'s argument is a λ at every instance, so the hint
      discrimination net has no key to index on -- every one of the ~55
      [CtxMorph] instances in the tree is a WILDCARD tried on every goal,
      in priority order, each with a full higher-order unification.
   2. Search cannot be told where to STOP.  A payload component like
      [DiskInv.free_slot_res] is a transparent [Definition], so
      [ctx_morph_sep] matches THROUGH it and the search descends into a
      body the component's own instance already covers -- and if that body
      reaches one of the deliberately uncovered ξ-dependent leaves
      ([pstate_lock], [hart_at_any], [own_context]) the whole descent
      fails and backtracks over everything it just did.
   3. [ctx_morph_const], which closes the majority of leaves, is pinned at
      priority 100 by its evar guard, so it is reached only after ~54
      failing instances.

   Search is still the right answer at the CALL sites -- there the payload
   is a named constant ([disk_res_at γ …]) with a keyed, zero-premise
   instance, and it resolves in milliseconds.  It is the INSTANCE
   CONSTRUCTION, whose goal is a raw payload body, that needs this file.

   AND THE TACTIC MUST NOT IMITATE SEARCH, which is what the first version
   did.  A blind [first [apply … | apply … | …]] is hand-rolled instance
   search: it pays one failing higher-order unification per lemma per
   node.  MEASURED on DiskInv.v's four obligations (GCP VM, isolated
   [coqc -time], 2026-08-29): 161 s, of which [apply ctx_morph_exist] 30 %
   over 1268 calls at 38 ms each, and the four word/string leaves 41 %
   over 175 calls each with ZERO successes -- [ctx_morph_sep] matched the
   unsealed [ctx_word_pointsto] tower first and took every [↦₈] apart byte
   by byte.  586 leaf visits, each preceded by seven failing structural
   [apply]s.  The syntactic dispatch below takes the same four
   obligations to 0.15 s (53 steps, one [apply] each).

   THE RULES IT ENCODES:

   - DISPATCH ON THE HEAD, do not guess.  [ctx_morph_step] is a
     [lazymatch] on the goal's syntactic head, so exactly one [apply]
     runs per node and no lemma is ever unified against a node it cannot
     match.  Adding a structural instance means adding a row here, not
     lengthening a [first].
   - THE LEAVES ARE DISPATCHED TOO, which is what stops the word towers
     being decomposed: [ctx_word_pointsto] and its siblings are NOT
     sealed (each is a tower over the sealed byte fact), so a [first]
     that tries [ctx_morph_sep] before them always wins and the leaf
     lemmas become dead weight.
   - STOP AT AN UNRECOGNISED HEAD.  The default row tries only the two
     boolean guards and [ctx_morph_const] (all cheap on a small term);
     anything else is left as a goal for the caller to close with the
     payload component's own instance -- see DiskInv.v's [DiskResAt],
     whose [all: apply free_slot_res_morph] is exactly that contract.
     The first version violated its own contract here: it descended
     through the transparent component constants instead.
   - DO NOT PUT [ctx_morph_const] FIRST.  It looks free -- the body
     either mentions ξ or it does not -- and on a LEAF it is.  On a whole
     payload body it is not: the unifier tries to eliminate ξ by delta
     (every cell is spelled [ctx_pointsto (cur_ctx ξ) …]) and does not
     come back.  Measured: >10 min at 1.3 GB on [disk_res], against 161 s
     for the version that had it last.
   - [cur_ctx] is unfolded first: a payload spelled with the ambient
     notations elaborates its cells at [@cur_ctx XI], and once [XI] is
     instantiated at the λ's binder the projection has to go before the
     leaf lemmas can see the binder.  [cbv beta] then runs per STEP, not
     once, because each [apply] leaves its subgoals with a β-redex under
     the λ and the [lazymatch] has to see through it.

   A separate file so that the tactic can grow without re-certifying
   [TsoCtx]'s cone. *)

From iris.proofmode Require Import proofmode.
Require Import TsoCtx.

(* The leaf lemmas, for a caller that wants to close one by hand.  The
   tactic itself dispatches to them by head and does not use this. *)
Ltac ctx_morph_leaf :=
  first [ apply ctx_morph_pointsto
        | apply ctx_morph_word
        | apply ctx_morph_word2
        | apply ctx_morph_word4
        | apply ctx_morph_string
        | apply ctx_morph_const ].

Ltac ctx_morph_step :=
  cbv beta;
  lazymatch goal with
  (* the ξ-CONSTANT leaf, dispatched SYNTACTICALLY: a pattern metavariable
     cannot capture the binder, so this row fires exactly on bodies that do
     not mention ξ -- no delta, none of the measured unifier blowups (the
     tso-flip solver's shape) *)
  | |- CtxMorph (fun _ => ?body) => apply ctx_morph_const
  | |- CtxMorph (fun _ => bi_sep _ _)    => apply ctx_morph_sep
  | |- CtxMorph (fun _ => bi_exist _)    => apply ctx_morph_exist; intros ?
  | |- CtxMorph (fun _ => bi_or _ _)     => apply ctx_morph_or
  | |- CtxMorph (fun _ => big_opL _ _ _) => apply ctx_morph_big_sepL; intros ? ?
  | |- CtxMorph (fun _ => big_opM _ _ _) => apply ctx_morph_big_sepM; intros ? ?
  | |- CtxMorph (fun _ => big_opS _ _ _) => apply ctx_morph_big_sepS; intros ?
  | |- CtxMorph (fun _ => ctx_pointsto _ _ _ _)        => apply ctx_morph_pointsto
  | |- CtxMorph (fun _ => ctx_word_pointsto _ _ _ _)   => apply ctx_morph_word
  | |- CtxMorph (fun _ => ctx_word2_pointsto _ _ _ _)  => apply ctx_morph_word2
  | |- CtxMorph (fun _ => ctx_word4_pointsto _ _ _ _)  => apply ctx_morph_word4
  | |- CtxMorph (fun _ => ctx_string_pointsto _ _ _ _) => apply ctx_morph_string
  (* the SC-era phys rows are GONE at the cutover: a full [ctx_phys_pointsto]
     does not transport by domination under TSO (the dirty arm's fragment is
     the author's).  A payload holding phys cells states its own instance
     over the clean half ([ctx_phys_pointsto_h]) or re-shapes (the T-leg's
     per-site treatments). *)
  (* the boolean guards are a [match] on a [bool], which an Ltac1 pattern
     cannot name; they are cheap to try, and [ctx_morph_const] behind them
     is the ξ-constant leaf (pure facts, ghost state, invariant handles). *)
  | |- _ => first [ apply ctx_morph_if_then
                  | apply ctx_morph_if_else
                  (* a named ξ-dependent leaf goes to instance search,
                     where its file registers one keyed instance per name
                     (PtTreeMove's tree; the tso-flip solver's tail) *)
                  | apply _ ]
  end.

Ltac ctx_morph_solve :=
  try rewrite /cur_ctx; repeat ctx_morph_step.
