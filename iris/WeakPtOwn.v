(** * WeakPtOwn.v — PROTOTYPE: the OBJECTIVE points-to [↦o], with fractions.

    Design: [`claude-notes/design/weak-memory-sc-parity.md`] §3 / obligations
    §5.3–§5.4.  Built on [WeakViewMono]'s monotone view ghost state.

    THE IDEA, and why it is not a new axiom.  [WeakVProp] already has an
    objective points-to — [wpt_img], the [t = 0] case — and its header says
    exactly why it works and exactly why it does not generalise:

    > A byte whose latest write is the ERA-INITIAL IMAGE — timestamp 0 —
    > carries a points-to with NO receipt, because [view_byte a 0] is the
    > bottom view and every index is above it.  [...] THE CONVERSE IS FALSE
    > AND THE DISTINCTION MATTERS: a [↦w□] whose timestamp is > 0 is
    > PERSISTENT but NOT objective — a hart that has not observed that
    > timestamp cannot read the byte.

    That last sentence is the whole problem, and the fix is to stop trying to
    make the ASSERTION index-free and instead say WHICH HART has observed the
    timestamp.  [WeakVProp.wpt] spends its second conjunct on

      [⊒(view_byte a t)]   — "the index this assertion is read at covers [t]"

    which is a constraint on the assertion's own [monPred] index, and hence
    subjective by construction.  [↦o] replaces it with

      [coh_lb (γ c) a t]   — "hart [c]'s coherence floor at [a] covers [t]"

    which is a GHOST FACT ABOUT A NAMED HART.  Same content, different
    altitude: it is an [iProp], so [↦o] is an [iProp], so it is objective,
    so everything above it transplants.  And because [coh_lb] is a lower
    bound on monotone ghost state it is PERSISTENT — it survives every
    intervening step for free, with no [vwp_hold_mono] and no rebasing.

    WHAT MAKES THIS SOUND is locking discipline, and it is not proved here:
    the obligation is that a hart only ever holds a fragment for a byte its
    own floor covers, which is established at an acquire's view-raising edge
    and preserved by [ws_le] monotonicity (design §3, obligations §5.3/§5.5).
    THIS FILE ASSUMES IT, by making [coh_lb] a conjunct of [↦o] rather than a
    global invariant — which is the honest prototype: it shows what the
    points-to buys once you have coverage, and it isolates coverage as the
    one thing the acquire/release boundary must deliver.

    ON FRACTIONS (design §6 risk 1, "the case I trust least").  Sharing works
    and needs no extra machinery, because [coh_lb] is per-hart and
    persistent.  Two harts each holding [1/2] of byte [a] hold two DIFFERENT
    [coh_lb]s — one per hart — and each is separately true; there is no
    single "the view" that has to be split.  What the ← direction of the
    split DOES need is timestamp agreement, and that comes from the
    [ghost_map] element, exactly as it does for the subjective [wpt_split].
    See [wpt_own_split] and the note above it. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap.
From stdpp Require Import bitvector.definitions.
From iris.algebra Require Import auth numbers functions dfrac.
From iris.base_logic.lib Require Import iprop own ghost_map mono_nat.
From iris.bi Require Import monpred.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import proofmode monpred.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import WeakMem WeakInterp WeakLang WeakView WeakVProp WeakGhost WeakInstr.
Require Import WeakViewMono.

Section ptown.
  Context `{!riscvGS Σ, !weakGS Σ, !weakViewG Σ}.

  (** The hart whose floors these are.  In the eventual wiring this is
      [weak_view_name cpu_id], a field of [weakGS] alongside [weak_ws_name];
      as a prototype parameter it keeps the blast radius at zero while the
      statements below are already the ones that will be exported. *)
  Context (γv : wview_names).

  (* ------------------------------------------------------------------ *)
  (** ** 1. The floor, matched to [flr]

      [flr (ws_view ws) a = Nat.max (w_vrNew ws) (coh ws a)] — a byte's
      floor is the max of the hart's scalar read floor and its per-byte
      coherence floor.  So the lower-bound resource is a disjunction: EITHER
      witness suffices, and having both directions exact is what makes
      [wpt_own_of_wpt] below a true converse rather than a one-way street. *)
  Definition wflr_lb (a : Z) (t : nat) : iProp Σ :=
    (coh_lb (wvn_coh γv) a t ∨
     mono_nat_lb_own (wsn_vrNew (wvn_scal γv)) t)%I.

  Global Instance wflr_lb_persistent a t : Persistent (wflr_lb a t).
  Proof. apply _. Qed.
  Global Instance wflr_lb_timeless a t : Timeless (wflr_lb a t).
  Proof. apply _. Qed.

  Lemma wflr_lb_valid w a t :
    ws_auth γv w -∗ wflr_lb a t -∗ ⌜(t ≤ flr (ws_view w) a)%nat⌝.
  Proof.
    iIntros "[Hs Hc] [Hlb|Hlb]".
    - iDestruct (coh_lb_valid with "Hc Hlb") as %Hle.
      iPureIntro. rewrite flr_ws_view. lia.
    - iDestruct "Hs" as "(_ & _ & A3 & _ & _)".
      iDestruct (mono_nat_lb_own_valid with "A3 Hlb") as %[_ Hle].
      iPureIntro. rewrite flr_ws_view. lia.
  Qed.

  Lemma wflr_lb_get w a t :
    (t ≤ flr (ws_view w) a)%nat -> ws_auth γv w -∗ wflr_lb a t.
  Proof.
    iIntros (Hle) "[Hs Hc]". rewrite flr_ws_view in Hle.
    destruct (decide (t ≤ coh w a)%nat) as [Ht|Ht].
    - iLeft. by iApply (coh_lb_get with "Hc").
    - iRight. iDestruct "Hs" as "(_ & _ & A3 & _ & _)".
      iDestruct (mono_nat_lb_own_get with "A3") as "#L".
      iApply (mono_nat_lb_own_le with "L"). lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 2. The points-to *)

  Definition wpt_own (a : Z) (dq : dfrac) (v : bv 8) : iProp Σ :=
    (∃ t : nat, wlat_pointsto a dq t v ∗ wflr_lb a t)%I.

End ptown.

Notation "a ↦o[ γv ]{ dq } v" := (wpt_own γv a dq v)
  (at level 20, format "a  ↦o[ γv ]{ dq }  v") : bi_scope.
Notation "a ↦o[ γv ] v" := (wpt_own γv a (DfracOwn 1) v)
  (at level 20, format "a  ↦o[ γv ]  v") : bi_scope.

Section ptown_rules.
  Context `{!riscvGS Σ, !weakGS Σ, !weakViewG Σ}.
  Context (γv : wview_names).

  (* ------------------------------------------------------------------ *)
  (** ** 3. OBJECTIVITY — the one-line payoff.

      [wpt_own] is an [iProp], so its embedding is objective with no proof
      obligation at all.  Compare [WeakVProp.wpt], which is objective at NO
      fraction and NO timestamp except [t = 0] ([wpt_img]).  This is what
      "everything above the leaves transplants" cashes out to: an objective
      assertion is index-independent, so a function's proof never has to
      rebase it, never has to name a [wstate], and may put it inside an
      invariant. *)
  Global Instance wpt_own_objective a dq v :
    Objective (⎡ wpt_own γv a dq v ⎤ : vProp Σ).
  Proof. apply _. Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 4. Fractions, agreement, persistence — all in SC's shape *)

  Global Instance wpt_own_timeless a dq v : Timeless (wpt_own γv a dq v).
  Proof. apply _. Qed.

  Global Instance wpt_own_persistent a v :
    Persistent (wpt_own γv a DfracDiscarded v).
  Proof. apply _. Qed.

  Lemma wpt_own_agree a dq1 v1 dq2 v2 :
    wpt_own γv a dq1 v1 -∗ wpt_own γv a dq2 v2 -∗ ⌜v1 = v2⌝.
  Proof.
    iIntros "[%t1 [H1 _]] [%t2 [H2 _]]".
    by iDestruct (wlat_pointsto_agree with "H1 H2") as %[_ ?].
  Qed.

  Lemma wpt_own_valid_2 a dq1 v1 dq2 v2 :
    wpt_own γv a dq1 v1 -∗ wpt_own γv a dq2 v2 -∗ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    iIntros "[%t1 [H1 _]] [%t2 [H2 _]]".
    iDestruct (wlat_pointsto_valid_2 with "H1 H2") as %(? & _ & ?).
    iPureIntro. by split.
  Qed.

  Lemma wpt_own_valid a dq v : wpt_own γv a dq v -∗ ⌜✓ dq⌝.
  Proof.
    iIntros "[%t [H _]]". rewrite /wlat_pointsto.
    by iDestruct (ghost_map_elem_valid with "H") as %?.
  Qed.

  (** THE SPLIT/JOIN.  The → direction is free: the element halves and the
      floor, being persistent, is simply duplicated — the two halves may then
      travel to different harts and each keeps a floor that is true FOR ITS
      OWN HART.  The ← direction is the one with content, and it is the same
      content as the subjective [wpt_split]'s: two points-to for one byte may
      a priori carry different timestamps, and it is element agreement that
      forces them equal before the fractions can be recombined. *)
  Lemma wpt_own_split a q1 q2 v :
    wpt_own γv a (DfracOwn (q1 + q2)) v ⊣⊢
    wpt_own γv a (DfracOwn q1) v ∗ wpt_own γv a (DfracOwn q2) v.
  Proof.
    iSplit.
    - iIntros "[%t [He #Hlb]]". rewrite /wlat_pointsto.
      iDestruct "He" as "[He1 He2]".
      iSplitL "He1"; iExists t; by iFrame "Hlb".
    - iIntros "[[%t1 [H1 #L1]] [%t2 [H2 _]]]".
      iDestruct (wlat_pointsto_agree with "H1 H2") as %[<- _].
      iExists t1. iFrame "L1". rewrite /wlat_pointsto -dfrac_op_own.
      iDestruct (ghost_map_elem_combine with "H1 H2") as "[H _]".
      iExact "H".
  Qed.

  Global Instance wpt_own_fractional a v :
    Fractional (fun q => wpt_own γv a (DfracOwn q) v).
  Proof. intros q1 q2. apply wpt_own_split. Qed.

  Global Instance wpt_own_as_fractional a q v :
    AsFractional (wpt_own γv a (DfracOwn q) v)
                 (fun q => wpt_own γv a (DfracOwn q) v) q.
  Proof. split; [done|apply _]. Qed.

  Lemma wpt_own_persist a dq v :
    wpt_own γv a dq v ==∗ wpt_own γv a DfracDiscarded v.
  Proof.
    iIntros "[%t [He #Hlb]]".
    iMod (wlat_pointsto_persist with "He") as "He".
    iModIntro. iExists t. by iFrame "He Hlb".
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 5. THE DROP-IN THEOREM.

      Under the authority at the true state, [↦o] and the subjective [↦w]
      are INTERCHANGEABLE.  This is what makes the prototype cheap rather
      than a rewrite: every rule already stated over [wpt] — the whole of
      [WeakVProp], [WeakInstr], [WeakStore] — applies to [↦o] by sandwiching,
      and nothing has to be re-derived.  The two directions are exact
      because [wflr_lb] matches [flr] on the nose. *)
  Lemma wpt_own_to_wpt a dq v w :
    ws_auth γv w -∗ wpt_own γv a dq v -∗
    ws_auth γv w ∗ vwp_hold (a ↦w{dq} v) w.
  Proof.
    iIntros "Hauth [%t [He #Hlb]]".
    iDestruct (wflr_lb_valid with "Hauth Hlb") as %Hle.
    iFrame "Hauth". rewrite wpt_at. iExists t. by iFrame "He".
  Qed.

  Lemma wpt_own_of_wpt a dq v w :
    ws_auth γv w -∗ vwp_hold (a ↦w{dq} v) w -∗
    ws_auth γv w ∗ wpt_own γv a dq v.
  Proof.
    iIntros "Hauth Hpt". rewrite wpt_at. iDestruct "Hpt" as (t) "[He %Ht]".
    iDestruct (wflr_lb_get _ w a t Ht with "Hauth") as "#Hlb".
    iFrame "Hauth". iExists t. by iFrame "He".
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 6. THE READ RULE, in SC's shape.

      Compare [WeakVProp.wpt_load_rule], which is the same theorem for the
      subjective points-to:

        - it takes an extra side condition
          [flr (ws_view (wm_ws σ)) a ≤ flr (ws_view (wm_ws σ')) a],
        - it CONSUMES the points-to at [σ] and hands back a points-to at
          [σ'] — the caller must thread the rebasing,
        - and it is a [vwp_hold] statement, so the caller must name [wm_ws σ].

      Here: no side condition, no rebasing, no [wstate] in sight, and the
      conclusion is pure so the caller keeps its points-to untouched.  That
      is literally SC's [wp_load] shape.  Note also that [dq] is arbitrary —
      A FRACTIONAL objective points-to reads exactly like a full one, which
      is the thing risk 1 of the design doubted. *)
  Lemma wpt_own_load_rule (σ : wmstate) ak a dq v t' b :
    ak_coh ak = false ->
    wbyte_ok σ ak a t' b ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    ws_auth γv (wm_ws σ) -∗
    wpt_own γv a dq v -∗
    ⌜b = v⌝.
  Proof.
    iIntros (Hcoh Hok) "Hi Hauth Hpt".
    iDestruct (wpt_own_to_wpt with "Hauth Hpt") as "[Hauth Hpt]".
    iDestruct (wpt_load_rule σ σ ak a dq v t' b Hcoh Hok
                 eq_refl eq_refl (le_n _) with "Hi Hpt") as "($ & _ & _)".
  Qed.

  (** The same at the interpreter's flat-memory altitude — the form the M2
      load leaves actually consume ([WeakInstr.wpt_flat_lookup] is the
      subjective twin, and it needs a [vwp_hold] at the machine's [wm_ws]). *)
  Lemma wpt_own_flat_lookup (σ : wmstate) (a : Arch.pa) dq v :
    wlog_wf (wm_log σ) ->
    wlat_interp (wm_img σ) (wm_log σ) -∗
    wpt_own γv (pa_z a) dq v -∗
    ⌜wflat (wm_img σ) (wm_log σ) !! a = Some v⌝.
  Proof.
    iIntros (Hwf) "Hi [%t [He _]]".
    by iApply (wlat_flat_lookup σ a dq t v Hwf with "Hi He").
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 7. What "survives a step" means here.

      For the subjective points-to this is [vwp_hold_mono] and it costs a
      line at EVERY instruction — including instructions that touch no data,
      since the fetch itself raises the view.  For [↦o] there is nothing to
      do: the statement below has no proof step in it, because the floor is
      persistent monotone ghost state and the element is not view-indexed at
      all.  The [ws_le] hypothesis is not even used. *)
  Lemma wpt_own_survives_step a dq v w w' :
    ws_le w w' ->
    ws_auth γv w -∗ wpt_own γv a dq v ==∗
    ws_auth γv w' ∗ wpt_own γv a dq v.
  Proof.
    iIntros (Hle) "Hauth Hpt".
    iMod (ws_update with "Hauth") as "$"; [exact Hle|].
    by iFrame "Hpt".
  Qed.

End ptown_rules.
