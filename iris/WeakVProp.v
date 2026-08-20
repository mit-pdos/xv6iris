(** * WeakVProp.v — the weak byte points-to, the [vwp_hold] discipline, and the
      LOAD and STORE rules (M2a)

    [WeakView] gives the index and the [vProp] core; this file gives the
    surface layer's first inhabitant — the byte points-to — and the two
    memory rules, at the two altitudes the M2a design call fixes.

    ============================ THE DESIGN CALL ============================

    THE vProp LAYER IS A DISCIPLINE OVER THE BASE LOGIC FIRST, AND A
    monPred-LEVEL LIBRARY SECOND.  There is deliberately NO new [WP]
    connective here.  The reason is structural, not economical: every WP in
    this tree is [WP (Loop : expr …) {{ _, False }}] — a hart's non-returning
    fetch-execute loop — and a leaf lemma does not *state* a WP, it
    TRANSFORMS one ([WeakExec.wp_wexec_step]: give me the hart's state
    interpretation and a continuation for every admissible successor, and I
    give you back the loop's WP).  A [vProp]-level WP would therefore be a
    monPred wrapper around a connective whose only user is a rule that hands
    out an iProp-level obligation at the hart's CURRENT weak state.  So we
    make the hart's weak state the primary object instead:

        [vwp_hold P ws := monPred_at P (ws_view ws)]

    read as "[P] holds AT the hart whose weak state is [ws]".  A leaf rule is
    an iProp lemma parameterised by the hart's [ws], taking [vwp_hold P ws]
    premises and producing [vwp_hold Q ws'] conclusions with [ws_le ws ws']
    available; [vwp_hold_mono] then carries every UNTOUCHED premise across
    the step for free, which is the property that makes the discipline pay.
    The pretty monPred-level statements ([P @@ ws_view ws]-shaped, §6) are
    one-liners on top and are what the M3 lock library will quote.

    VERDICT ON THE TWO ALTITUDES (M2a): the split works, and the split point
    is [vwp_hold_mono] + [wpt_at].  [wpt_at] decodes the points-to into
    exactly "an element of the latest-write map, plus a floor inequality on
    the hart's index", after which BOTH rules are pure [WeakMem]/[WeakGhost]
    reasoning with no monPred in sight; and every frame condition of a step
    is discharged by [vwp_hold_mono] from [WeakInterp]'s own
    [wread_post_ws_le] / [wwrite_post_ws_le].  The monPred altitude is
    re-entered only at §6, in three lines.

    ======================================================================= *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import ghost_map ghost_var.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakInterp.
Require Import WeakGhost.
Require Import WeakView.
Require Import RiscvLang RiscvPtsto.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The hart index

    A hart's LOGICAL INDEX at a program point is its semantic read floor:
    the scalar pre-view [w_vrNew] joined with the per-byte coherence map
    [w_coh] (design doc, Decision 5).  That is exactly a [view], and the
    correspondence is definitional. *)

Definition ws_view (ws : wstate) : view := View (w_vrNew ws) (w_coh ws).

Lemma flr_ws_view ws a : flr (ws_view ws) a = Nat.max (w_vrNew ws) (coh ws a).
Proof. reflexivity. Qed.

(** MONOTONICITY: the machine's own per-field [ws_le] IS the index order.
    Every [WeakInterp] step lemma ([wread_post_ws_le], [wwrite_post_ws_le],
    [barrier_post_le], [wrun_ws_le]) therefore lands directly on [⊑]. *)
Lemma ws_view_mono ws ws' : ws_le ws ws' → ws_view ws ⊑ ws_view ws'.
Proof.
  intros (Hcoh & _ & _ & HrN & _ & _) a.
  rewrite !flr_ws_view. specialize (Hcoh a). lia.
Qed.

Lemma ws_view_init a : flr (ws_view ws_init) a = 0%nat.
Proof. reflexivity. Qed.

(** The floor a STORE leaves at the byte it wrote — the premise the store
    rule's post-view side condition is discharged with. *)
Lemma flr_store_post ws rl a t : (t ≤ flr (ws_view (store_post ws rl a t)) a)%nat.
Proof.
  rewrite flr_ws_view. pose proof (store_post_coh ws rl a t). lia.
Qed.

(** ... and the floor a LOAD leaves: the timestamp read is covered too. *)
Lemma flr_load_post_at ws aq vpre a t :
  (t ≤ flr (ws_view (load_post_at ws aq vpre a t)) a)%nat.
Proof.
  rewrite flr_ws_view. pose proof (load_post_at_coh ws aq vpre a t). lia.
Qed.

Section rules.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (* ==================================================================== *)
  (** ** 2. [vwp_hold] — the discipline

      "[P] holds at the hart whose weak state is [ws]".  Everything below is
      stated through it; the monPred layer is re-entered only at §6. *)

  Definition vwp_hold (P : vProp Σ) (ws : wstate) : iProp Σ :=
    monPred_at P (ws_view ws).

  Global Instance vwp_hold_ne ws : NonExpansive (λ P, vwp_hold P ws).
  Proof. rewrite /vwp_hold. solve_proper. Qed.
  Global Instance vwp_hold_proper ws : Proper ((≡) ==> (≡)) (λ P, vwp_hold P ws).
  Proof. apply (ne_proper _). Qed.
  Global Instance vwp_hold_mono' ws : Proper ((⊢) ==> (⊢)) (λ P, vwp_hold P ws).
  Proof. intros P Q HPQ. rewrite /vwp_hold. by apply HPQ. Qed.

  (** THE WORKHORSE.  A step only ever raises the hart's views, so every
      premise the step did not touch survives it with no work at all.  This
      is what makes the leaf rules below need side conditions only about the
      byte they act on. *)
  Lemma vwp_hold_mono P ws ws' :
    ws_le ws ws' → vwp_hold P ws ⊢ vwp_hold P ws'.
  Proof. intros H. rewrite /vwp_hold. by apply monPred_mono, ws_view_mono. Qed.

  (** A [vProp] entailment used INSIDE the discipline.  (The [Proper]
      instance above is the same fact; this is the [apply]-shaped form the
      rules want.) *)
  Lemma vwp_hold_ent (P Q : vProp Σ) ws :
    (P ⊢ Q) → vwp_hold P ws ⊢ vwp_hold Q ws.
  Proof. intros HPQ. rewrite /vwp_hold HPQ. done. Qed.

  (** ... and its index-level twin: an obligation stated at an index BELOW
      the hart's is an obligation at the hart.  This is the seam a future
      [vProp]-level WP would be defined over (Cosmo's [∀ V' ⊒ V]). *)
  Lemma vwp_hold_intro V P ws :
    V ⊑ ws_view ws → monPred_at P V ⊢ vwp_hold P ws.
  Proof. intros H. rewrite /vwp_hold. by apply monPred_mono. Qed.

  (** The structural laws — all definitional unfoldings of [monPred_at]. *)
  Lemma vwp_hold_sep P Q ws :
    vwp_hold (P ∗ Q) ws ⊣⊢ vwp_hold P ws ∗ vwp_hold Q ws.
  Proof. apply monPred_at_sep. Qed.
  Lemma vwp_hold_exist {A} (Φ : A → vProp Σ) ws :
    vwp_hold (∃ x, Φ x) ws ⊣⊢ ∃ x, vwp_hold (Φ x) ws.
  Proof. apply monPred_at_exist. Qed.
  Lemma vwp_hold_pure (φ : Prop) ws : vwp_hold ⌜φ⌝ ws ⊣⊢ ⌜φ⌝.
  Proof. apply monPred_at_pure. Qed.
  Lemma vwp_hold_embed (R : iProp Σ) ws : vwp_hold ⎡R⎤ ws ⊣⊢ R.
  Proof. apply monPred_at_embed. Qed.
  Lemma vwp_hold_bupd P ws : vwp_hold (|==> P) ws ⊣⊢ |==> vwp_hold P ws.
  Proof. apply monPred_at_bupd. Qed.

  (** The seen assertion at the hart IS the index inequality. *)
  Lemma vwp_hold_seen V ws : vwp_hold (⊒V) ws ⊣⊢ ⌜V ⊑ ws_view ws⌝.
  Proof. apply monPred_at_in. Qed.

  Lemma vwp_hold_seen_self ws : ⊢ vwp_hold (⊒(ws_view ws)) ws.
  Proof. rewrite vwp_hold_seen. iPureIntro. reflexivity. Qed.

  (** THE SPLIT AXIOM, transported to the discipline.  [P @@ V] is index-free
      (objective), so its value at the hart is just [P]'s value at [V]. *)
  Lemma vwp_hold_view_at P V ws : vwp_hold (P @@ V) ws ⊣⊢ monPred_at P V.
  Proof. apply monPred_at_embed. Qed.

  Lemma vwp_hold_freeze P ws : vwp_hold P ws ⊣⊢ vwp_hold (P @@ ws_view ws) ws.
  Proof. by rewrite vwp_hold_view_at. Qed.

  Lemma vwp_hold_thaw V P ws :
    V ⊑ ws_view ws → vwp_hold (P @@ V) ws ⊢ vwp_hold P ws.
  Proof. intros H. rewrite vwp_hold_view_at. by apply vwp_hold_intro. Qed.

  (* ==================================================================== *)
  (** ** 3. The byte points-to

      [a ↦w{dq} v] — "the LATEST write to byte [a] is [(t, v)] for some
      timestamp [t], AND I have observed [t]".  The first conjunct is the
      base-layer element ([WeakGhost.wlat_pointsto], objective — it is an
      embedded [iProp]); the second is the receipt that makes the assertion
      SUBJECTIVE, and is the entire difference between this and the SC
      points-to.  Mutable RAM bytes are the only subjective footprint in the
      whole design (design doc, Decision 5). *)

  Definition wpt (a : Z) (dq : dfrac) (v : bv 8) : vProp Σ :=
    (∃ t : nat, ⎡ wlat_pointsto a dq t v ⎤ ∗ ⊒(view_byte a t))%I.

  (** *** 3'. THE OWNED FORM (the φ-upgrade's C-or-D points-to)

      A byte a thread owns EXCLUSIVELY and may have plain-stored to: the value
      element at full fraction, plus a state element that is CLEAN or DIRTY —
      and, if dirty, the persistent breadcrumb naming the hart that dirtied it
      ([WeakGhost.wown_ctx]).  This is the postcondition shape of every owned
      store — it absorbs both outcomes, so no call site case-splits on the
      access class — and the only shape a plain store accepts on the way in.

      IT IS INDEXED BY THE EXECUTION CONTEXT [ξ], NOT BY A HART (φ-upgrade
      §1.6), and that is what makes it FRAME across a migration: nothing in
      the assertion changes when the thread is rescheduled, so the caller's
      resource is literally the same proposition on both sides of a yield and
      Iris's frame rule applies.  The hart that dirtied the byte is recorded
      inside, in the breadcrumb, where only the LEAF ever looks at it —
      [WeakGhost.wown_ctx_retarget] turns it back into an ordinary
      [wown_st cpu_id] out of the scheduler's migration invariant, so an
      access site's script is identical before and after the migration.

      (Stage 1.5 had this hart-indexed, with the retarget as a lemma the
      CALLER applied at the first touch after a migration.  That is the
      ergonomics this stage exists to delete.) *)
  Definition wpt_own (ξ : CtxId) (a : Z) (v : bv 8) : vProp Σ :=
    (∃ t : nat, ⎡ wlat_elem a (DfracOwn 1) t v ∗ wown_ctx ξ a t ⎤ ∗
                ⊒(view_byte a t))%I.

End rules.

Notation "a ↦w dq v" := (wpt a dq v)
  (at level 20, dq custom dfrac at level 1, format "a  ↦w dq  v") : bi_scope.

(* ====================================================================== *)
(** ** 3''. THE AMBIENT CONTEXT — [CurCtx] and the bare [↦wo] (φ-upgrade §1.7)

    [wpt_own] is indexed by the execution context, and a function's context is
    the SAME value at every one of its access sites.  Threading it as an
    explicit argument would therefore add a parameter that never varies —
    which is exactly the shape [RiscvLang.CpuId] already has for the hart, and
    this class is declared to that file's conventions, deliberately:

      - a BARE singleton class ([Class CurCtx := cur_ctx : CtxId.]) and NOTHING
        ELSE — no [Global Instance], no [Existing Instance], anywhere in the
        tree.  A context is supplied the way a hart is: by a per-lemma or
        per-section binder, so the instance is always a local hypothesis and
        is discharged into an implicit argument at [End].  ALWAYS NAME THE
        BINDER — [`{XI : CurCtx}], as [RiscvLang]'s users write
        [`{CID : CpuId}] — because an anonymous [`{CurCtx}] is auto-named [H]
        and then every [iIntros "… %H"] in the section fails with "H is
        already used" (measured, 2026-08-12);
      - the surface form is a NOTATION over the primitive, filling the class
        argument by resolution — [RiscvLang]'s [Notation Loop :=
        (LoopE gen_id cpu_id)] and [WeakStore]'s [↦w₄ₒ] / [WeakWord8]'s
        [↦w₈ₒ] are the same construction at [CpuId];
      - [Typeclasses Opaque cur_ctx] so instance search never unfolds the
        projection (it is the identity on [CtxId], so a transparent one lets a
        search see through every ambient context into the ghost names).

    WHY THE AMBIENT TRICK IS SOUND HERE AND WAS NOT FOR THE HART.  The
    explicit-CPUID refactor exists because a WP's hart is NOT invariant across
    a function: a timer trap parks the thread and any hart's scheduler may
    resume it, so an ambient [cpu_id] silently asserted "same hart before and
    after", which is false.  [ξ] has the property [cpu_id] lacks — it is
    invariant across the whole function INCLUDING the migration; that is the
    entire content of §1.6.  So the ambient reading is not just convenient,
    it is the one that states the truth: the [↦wo] before a yield and the
    [↦wo] after it are the SAME proposition because they resolve to the SAME
    instance.

    ===================== THE ONE-CONTEXT CONVENTION =====================

    THE BARE NOTATION IS FOR CODE WITH EXACTLY ONE CONTEXT IN SCOPE.  Where
    two contexts meet, SPELL BOTH EXPLICITLY as [wpt_own ξ …] — the primitive
    never went away, and an explicit-[ξ] term prints unsugared, so the two
    spellings stay visually distinct in a goal.  The places that are always
    explicit:

      - the scheduler / [WeakCtx] machinery and any yield-shaped spec
        ([WkYieldFrame]'s [wyield_park_core] / [wyield_resume_core] /
        [wwp_yield_park]): they quantify over the context they park, and an
        ambient caller passes its own in as [cur_ctx] at the call;
      - ANY LEMMA THAT WOULD JOIN THE TWO SIDES OF A TRANSFER.  [WkOwnPingPong]
        is ambient throughout only because each of its lemmas is ONE thread's
        leg — the releasing side's [ξ] and the acquiring side's are different
        contexts, and the medium between them is the lock body, whose payload
        is the context-free clean [x ↦w{1} v].  A lemma composing a release
        leg with an acquire leg has two contexts in scope and MUST spell both;
        written ambiently it would compile, silently claiming one thread
        handed the byte to itself.  That is the whole reason this paragraph
        exists;
      - the primitive rules themselves (everything in §4/§5 below), which stay
        [ξ]-explicit so that a two-context proof can use them at both.  §5b's
        [_cur] wrappers are the ambient face of the same rules.

    THE HAZARD, MEASURED (2026-08-12), because it is silent: with TWO
    [CurCtx] hypotheses in scope, [cur_ctx] resolves to the LAST-DECLARED one
    and NOTHING IS REPORTED — no warning, no ambiguity error.  A later
    [`{CurCtx}] therefore SHADOWS a section's, exactly as the explicit-CPUID
    work recorded for a later [h : CpuId] shadowing a section [CpuId].  There
    is no mechanism that can catch this; the convention is the mechanism.
    Never introduce a second [CurCtx] binder — quantify over [CtxId] and pass
    it to [wpt_own] instead. *)

Class CurCtx := cur_ctx : CtxId.

(** Instance search must not see through the projection (it is the identity
    on [CtxId]). *)
Typeclasses Opaque cur_ctx.

(** The bare owned points-to: [wpt_own] with the context filled in ambiently.
    [a ↦w{1} v] is its clean sibling; the subscripted [↦w₄ₒ] / [↦w₈ₒ] towers
    are the HART-indexed [wpt_own_h] family (§3c''), which is not this and is
    not the API. *)
Notation "a ↦wo v" := (wpt_own cur_ctx a v)
  (at level 20, format "a  ↦wo  v") : bi_scope.

Section pointsto.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** THE DECODE LEMMA, and the seam between the two altitudes: at a hart,
      the points-to is exactly "an element of the latest-write map, whose
      timestamp the hart's floor for [a] covers".  Every rule below is proved
      through this and never mentions [monPred] again. *)
  (** Stated at an ARBITRARY index, because the framing pattern (φ-upgrade
      §1.5) needs the decode at a FROZEN index: a fact a thread parks with is
      [monPred_at P V] for the parking hart's [V], and that is an objective
      [iProp] which survives the migration untouched.  [wpt_at] is the [V :=
      ws_view ws] instance and is what every existing caller uses. *)
  Lemma wpt_at_view a dq v (V : view) :
    monPred_at (a ↦w{dq} v) V ⊣⊢
      ∃ t : nat, wlat_pointsto a dq t v ∗ ⌜(t ≤ flr V a)%nat⌝.
  Proof.
    rewrite /wpt monPred_at_exist.
    setoid_rewrite monPred_at_sep. setoid_rewrite monPred_at_embed.
    setoid_rewrite monPred_at_in.
    apply bi.exist_proper => t.
    iSplit; iIntros "[He %H]"; iFrame "He"; iPureIntro; by apply view_byte_le.
  Qed.

  Lemma wpt_at a dq v ws :
    vwp_hold (a ↦w{dq} v) ws ⊣⊢
      ∃ t : nat, wlat_pointsto a dq t v ∗ ⌜(t ≤ flr (ws_view ws) a)%nat⌝.
  Proof. apply wpt_at_view. Qed.

  (** The introduction form: owning the element and covering its timestamp is
      the points-to. *)
  Lemma wpt_at_intro a dq v t ws :
    (t ≤ flr (ws_view ws) a)%nat →
    wlat_pointsto a dq t v ⊢ vwp_hold (a ↦w{dq} v) ws.
  Proof.
    intros Ht. rewrite wpt_at. iIntros "He". iExists t. by iFrame "He".
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 3a. fractions, agreement, persistence *)

  (** TIMESTAMP AGREEMENT ACROSS FRACTIONS, at the base altitude: two
      elements for the same byte agree on BOTH components.  (The timestamp
      cannot be stated at the [vProp] altitude — it is existentially bound
      there — which is precisely why this one is a base-logic lemma.) *)
  Lemma wlat_elem_agree a dq1 t1 v1 dq2 t2 v2 :
    wlat_elem a dq1 t1 v1 -∗ wlat_elem a dq2 t2 v2 -∗ ⌜t1 = t2 ∧ v1 = v2⌝.
  Proof.
    rewrite /wlat_elem. iIntros "H1 H2".
    iDestruct (ghost_map_elem_agree with "H1 H2") as %Heq.
    iPureIntro. by simplify_eq.
  Qed.

  Lemma wlat_pointsto_agree a dq1 t1 v1 dq2 t2 v2 :
    wlat_pointsto a dq1 t1 v1 -∗ wlat_pointsto a dq2 t2 v2 -∗
    ⌜t1 = t2 ∧ v1 = v2⌝.
  Proof.
    iIntros "[H1 _] [H2 _]". by iApply (wlat_elem_agree with "H1 H2").
  Qed.

  Lemma wlat_pointsto_valid_2 a dq1 t1 v1 dq2 t2 v2 :
    wlat_pointsto a dq1 t1 v1 -∗ wlat_pointsto a dq2 t2 v2 -∗
    ⌜✓ (dq1 ⋅ dq2) ∧ t1 = t2 ∧ v1 = v2⌝.
  Proof.
    rewrite /wlat_pointsto /wlat_elem. iIntros "[H1 _] [H2 _]".
    iDestruct (ghost_map_elem_valid_2 with "H1 H2") as %[Hv Heq].
    iPureIntro. split; [exact Hv|by simplify_eq].
  Qed.

  Lemma wlat_pointsto_persist a dq t v :
    wlat_pointsto a dq t v ==∗ wlat_pointsto a DfracDiscarded t v.
  Proof.
    rewrite /wlat_pointsto /wlat_elem /wclean /wcds_el. iIntros "[H1 H2]".
    iMod (ghost_map_elem_persist with "H1") as "$".
    by iMod (ghost_map_elem_persist with "H2") as "$".
  Qed.

  (** FRACTION SPLIT at the base altitude: both halves of the points-to are
      [ghost_map_elem]s, so the split is the algebra's, twice. *)
  Lemma wlat_pointsto_split a q1 q2 t v :
    wlat_pointsto a (DfracOwn (q1 + q2)) t v ⊣⊢
    wlat_pointsto a (DfracOwn q1) t v ∗ wlat_pointsto a (DfracOwn q2) t v.
  Proof.
    rewrite /wlat_pointsto /wlat_elem /wclean /wcds_el. iSplit.
    - iIntros "[[E1 E2] [C1 C2]]". iFrame.
    - iIntros "[[E1 C1] [E2 C2]]".
      iCombine "E1 E2" as "E". iCombine "C1 C2" as "C". iFrame.
  Qed.

  Global Instance wlat_pointsto_persistent a t v :
    Persistent (wlat_pointsto a DfracDiscarded t v).
  Proof. rewrite /wlat_pointsto. apply _. Qed.

  Global Instance wlat_pointsto_timeless a dq t v :
    Timeless (wlat_pointsto a dq t v).
  Proof. rewrite /wlat_pointsto. apply _. Qed.

  Global Instance wpt_persistent a v : Persistent (a ↦w□ v).
  Proof. rewrite /wpt. apply _. Qed.

  Global Instance wpt_timeless a q v : Timeless (a ↦w{# q} v).
  Proof. rewrite /wpt. apply _. Qed.

  (** VALUE AGREEMENT at the surface altitude.  NOTE the two points-to need
      NOT be at the same index for this: the conclusion is pure, so the
      statement is a [vProp] entailment and the proofmode reads both sides at
      whatever index it is instantiated at. *)
  Lemma wpt_agree a dq1 v1 dq2 v2 :
    (a ↦w{dq1} v1 ∗ a ↦w{dq2} v2 : vProp Σ) ⊢ ⌜v1 = v2⌝.
  Proof.
    constructor => V. rewrite monPred_at_sep monPred_at_pure /wpt.
    rewrite !monPred_at_exist.
    iIntros "[H1 H2]".
    iDestruct "H1" as (t1) "H1". iDestruct "H2" as (t2) "H2".
    rewrite !monPred_at_sep !monPred_at_embed.
    iDestruct "H1" as "[He1 _]". iDestruct "H2" as "[He2 _]".
    by iDestruct (wlat_pointsto_agree with "He1 He2") as %[_ ?].
  Qed.

  Lemma wpt_valid_2 a dq1 v1 dq2 v2 :
    (a ↦w{dq1} v1 ∗ a ↦w{dq2} v2 : vProp Σ) ⊢ ⌜✓ (dq1 ⋅ dq2) ∧ v1 = v2⌝.
  Proof.
    constructor => V. rewrite monPred_at_sep monPred_at_pure /wpt.
    rewrite !monPred_at_exist.
    iIntros "[H1 H2]".
    iDestruct "H1" as (t1) "H1". iDestruct "H2" as (t2) "H2".
    rewrite !monPred_at_sep !monPred_at_embed.
    iDestruct "H1" as "[He1 _]". iDestruct "H2" as "[He2 _]".
    iDestruct (wlat_pointsto_valid_2 with "He1 He2") as %(? & _ & ?).
    iPureIntro. by split.
  Qed.

  (** FRACTION SPLIT / JOIN.  Both directions hold — and the ← direction is
      not free: two points-to for the same byte may a priori carry DIFFERENT
      timestamps, and it is the element agreement above that forces them
      equal before the fractions can be combined. *)
  Lemma wpt_split a q1 q2 v :
    (a ↦w{# (q1 + q2)} v : vProp Σ) ⊣⊢ a ↦w{# q1} v ∗ a ↦w{# q2} v.
  Proof.
    constructor => V. rewrite monPred_at_sep /wpt !monPred_at_exist.
    iSplit.
    - iIntros "H". iDestruct "H" as (t) "H".
      rewrite !monPred_at_sep !monPred_at_embed.
      iDestruct "H" as "[He #Hv]". rewrite wlat_pointsto_split.
      iDestruct "He" as "[He1 He2]".
      iSplitL "He1"; iExists t; rewrite monPred_at_sep monPred_at_embed;
        by iFrame.
    - iIntros "[H1 H2]".
      iDestruct "H1" as (t1) "H1". iDestruct "H2" as (t2) "H2".
      rewrite !monPred_at_sep !monPred_at_embed.
      iDestruct "H1" as "[He1 #Hv1]". iDestruct "H2" as "[He2 _]".
      iDestruct (wlat_pointsto_agree with "He1 He2") as %[<- _].
      iExists t1. rewrite monPred_at_sep monPred_at_embed.
      rewrite wlat_pointsto_split. by iFrame.
  Qed.

  Lemma wpt_persist a dq v : (a ↦w{dq} v : vProp Σ) ⊢ |==> a ↦w□ v.
  Proof.
    constructor => V. rewrite monPred_at_bupd /wpt !monPred_at_exist.
    iIntros "H". iDestruct "H" as (t) "H".
    rewrite !monPred_at_sep !monPred_at_embed.
    iDestruct "H" as "[He #Hv]".
    iMod (wlat_pointsto_persist with "He") as "He".
    iModIntro. iExists t. rewrite monPred_at_sep monPred_at_embed. by iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 3b. THE OBJECTIVITY SPECIAL CASE — an era-image byte

      A byte whose latest write is the ERA-INITIAL IMAGE — timestamp 0, i.e.
      a byte no message has ever written: kernel text, kernel rodata, any
      write-once boot datum — carries a points-to with NO receipt, because
      [view_byte a 0] is the bottom view and every index is above it.  That
      makes it a plain embedded [iProp], hence OBJECTIVE, hence admissible
      inside an invariant and freely shareable across harts.  This is what
      will make [kernel_text] / [kernel_data_string] and the whole [↦□]
      family objective at M4.

      THE CONVERSE IS FALSE AND THE DISTINCTION MATTERS: a [↦w□] whose
      timestamp is > 0 (a byte written once and then discarded) is
      PERSISTENT but NOT objective — a hart that has not observed that
      timestamp cannot read the byte, so putting one in an invariant would
      be unsound.  Persistence and objectivity are independent here. *)

  Definition wpt_img (a : Z) (dq : dfrac) (v : bv 8) : vProp Σ :=
    ⎡ wlat_pointsto a dq 0%nat v ⎤%I.

  Global Instance wpt_img_objective a dq v : Objective (wpt_img a dq v).
  Proof. rewrite /wpt_img. apply _. Qed.

  Global Instance wpt_img_persistent a v : Persistent (wpt_img a DfracDiscarded v).
  Proof. rewrite /wpt_img. apply _. Qed.

  (** An era-image points-to IS a points-to, at every index. *)
  Lemma wpt_img_wpt a dq v : wpt_img a dq v ⊢ a ↦w{dq} v.
  Proof.
    rewrite /wpt_img /wpt. iIntros "He". iExists 0%nat. iFrame "He".
    iApply seen_byte_0.
  Qed.

  (** ... and conversely, a points-to whose element sits at timestamp 0 is
      objective — stated at the base altitude, where the timestamp is
      visible.  [wpt_at] is what connects the two. *)
  Lemma wpt_img_at a dq v ws : vwp_hold (wpt_img a dq v) ws ⊣⊢ wlat_pointsto a dq 0%nat v.
  Proof. apply monPred_at_embed. Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 3c. the algebra of the OWNED form

      [wpt_own]'s decode is [wpt_at]'s with the state element carried
      alongside; it is the shape both memory rules of §4/§5 destruct to. *)

  Lemma wpt_own_at_view ξ a v (V : view) :
    monPred_at (wpt_own ξ a v) V ⊣⊢
      ∃ t : nat, wlat_elem a (DfracOwn 1) t v ∗ wown_ctx ξ a t ∗
                 ⌜(t ≤ flr V a)%nat⌝.
  Proof.
    rewrite /wpt_own monPred_at_exist.
    setoid_rewrite monPred_at_sep. setoid_rewrite monPred_at_embed.
    setoid_rewrite monPred_at_in.
    apply bi.exist_proper => t.
    iSplit.
    - iIntros "[[He Hs] %H]". iFrame "He Hs". iPureIntro. by apply view_byte_le.
    - iIntros "(He & Hs & %H)". iFrame "He Hs". iPureIntro.
      by apply view_byte_le.
  Qed.

  Lemma wpt_own_at ξ a v ws :
    vwp_hold (wpt_own ξ a v) ws ⊣⊢
      ∃ t : nat, wlat_elem a (DfracOwn 1) t v ∗ wown_ctx ξ a t ∗
                 ⌜(t ≤ flr (ws_view ws) a)%nat⌝.
  Proof. apply wpt_own_at_view. Qed.

  Lemma wpt_own_at_intro ξ a v t ws :
    (t ≤ flr (ws_view ws) a)%nat →
    wlat_elem a (DfracOwn 1) t v -∗ wown_ctx ξ a t -∗
    vwp_hold (wpt_own ξ a v) ws.
  Proof.
    intros Ht. rewrite wpt_own_at. iIntros "He Hs". iExists t. by iFrame.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 3c''. THE HART-INDEXED BYTE FORM — [wpt_own_h], M-MODE ONLY

      Stage 1.5's owned points-to, kept under a distinguishing name for ONE
      purpose: it is what the four- and eight-byte OWNED TOWERS
      ([WeakStore.wpt4_own], [WeakWord8.wpt8_own]) and the M-mode store leaves
      built on them are stated over, and those never cross a migration — the
      M-mode boot chain runs one context per hart from reset to [wp_next], so
      indexing them by a context would buy nothing and cost a rewrite of every
      leaf in the batch-2 family.

      IT IS NOT THE API.  A resource that names a hart does not frame across a
      yield, which is the whole content of §1.6; anything that can be
      rescheduled must use [wpt_own].  The two forms do not interconvert
      except through the clean form [a ↦w{1} v], which both accept — and that
      is the honest statement of the difference. *)
  Definition wpt_own_h (c : CPU) (a : Z) (v : bv 8) : vProp Σ :=
    (∃ t : nat, ⎡ wlat_elem a (DfracOwn 1) t v ∗ wown_st c a ⎤ ∗
                ⊒(view_byte a t))%I.

  Lemma wpt_own_h_at_view c a v (V : view) :
    monPred_at (wpt_own_h c a v) V ⊣⊢
      ∃ t : nat, wlat_elem a (DfracOwn 1) t v ∗ wown_st c a ∗
                 ⌜(t ≤ flr V a)%nat⌝.
  Proof.
    rewrite /wpt_own_h monPred_at_exist.
    setoid_rewrite monPred_at_sep. setoid_rewrite monPred_at_embed.
    setoid_rewrite monPred_at_in.
    apply bi.exist_proper => t.
    iSplit.
    - iIntros "[[He Hs] %H]". iFrame "He Hs". iPureIntro. by apply view_byte_le.
    - iIntros "(He & Hs & %H)". iFrame "He Hs". iPureIntro.
      by apply view_byte_le.
  Qed.

  Lemma wpt_own_h_at c a v ws :
    vwp_hold (wpt_own_h c a v) ws ⊣⊢
      ∃ t : nat, wlat_elem a (DfracOwn 1) t v ∗ wown_st c a ∗
                 ⌜(t ≤ flr (ws_view ws) a)%nat⌝.
  Proof. apply wpt_own_h_at_view. Qed.

  Lemma wpt_own_h_at_intro c a v t ws :
    (t ≤ flr (ws_view ws) a)%nat →
    wlat_elem a (DfracOwn 1) t v -∗ wown_st c a -∗
    vwp_hold (wpt_own_h c a v) ws.
  Proof.
    intros Ht. rewrite wpt_own_h_at. iIntros "He Hs". iExists t. by iFrame.
  Qed.

  Lemma wpt_own_h_of_wpt c a v : (a ↦w v : vProp Σ) ⊢ wpt_own_h c a v.
  Proof.
    rewrite /wpt /wpt_own_h. constructor => V.
    rewrite !monPred_at_exist. apply bi.exist_mono => t.
    rewrite !monPred_at_sep !monPred_at_embed.
    iIntros "[[He Hc] $]". iFrame "He". by iApply wclean_own_st.
  Qed.

  (** A CLEAN full-fraction byte IS an owned byte, at EVERY context — a clean
      byte names no author, so there is nothing to be indexed by.  The
      converse is NOT available in general: that is the whole point of the D
      state, and recovering it is what a release's flip does. *)
  Lemma wpt_own_of_wpt ξ a v : (a ↦w v : vProp Σ) ⊢ wpt_own ξ a v.
  Proof.
    rewrite /wpt /wpt_own. constructor => V.
    rewrite !monPred_at_exist. apply bi.exist_mono => t.
    rewrite !monPred_at_sep !monPred_at_embed.
    iIntros "[[He Hc] $]". iFrame "He". by iApply wown_ctx_of_clean.
  Qed.

  Lemma wpt_own_mono ξ a v ws ws' :
    ws_le ws ws' → vwp_hold (wpt_own ξ a v) ws ⊢ vwp_hold (wpt_own ξ a v) ws'.
  Proof. apply vwp_hold_mono. Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 3c'. THE φ PAYMENT OF AN OWNED BYTE (φ-upgrade §1.6)

      Every leaf owes [nv_hart] at its post-log, one [WeakGhost.nv_byte] per
      byte of its own effect trace.  For an owned byte the obligation is paid
      HERE, and — this is the stage's whole content — by the SAME lemma
      whether or not the thread has migrated since it last wrote the byte.
      [WeakGhost.nv_ok_of_wown_ctx] does the case analysis internally: clean
      and own-dirty bytes pay directly, a byte dirtied on a hart the context
      has since left pays out of the publication coverage the migration
      invariant supplies.

      (Stage 1.5 had TWO lemmas here, [nv_ok_of_own_st] and
      [nv_free_of_own_upgrade], and the caller had to know which situation it
      was in.  That is exactly what the user's directive rules out.) *)
  Lemma nv_ok_of_wpt_own (ξ : CtxId) (c : CPU) (a : Z) (v : bv 8) (V : view)
      img (log logA : list wmsg) :
    pub_transfer logA log c →
    wlog_auth logA -∗ ctx_migr ξ c -∗ wlat_interp img log -∗
    monPred_at (wpt_own ξ a v) V -∗ ⌜nv_ok log c a⌝.
  Proof.
    intros Htr. iIntros "Hlog Hmg Hi Hpt".
    rewrite wpt_own_at_view. iDestruct "Hpt" as (t) "(Hel & Hs & _)".
    by iApply (nv_ok_of_wown_ctx ξ c a t v img log logA Htr
                 with "Hlog Hmg Hi Hel Hs").
  Qed.

  Lemma nv_ok_of_wpt_own_at (ξ : CtxId) (c : CPU) (a : Z) (v : bv 8)
      img (log : list wmsg) (ws : wstate) :
    wlog_auth log -∗ ctx_migr ξ c -∗ wlat_interp img log -∗
    vwp_hold (wpt_own ξ a v) ws -∗ ⌜nv_ok log c a⌝.
  Proof.
    iIntros "Hlog Hmg Hi Hpt".
    iApply (nv_ok_of_wpt_own ξ c a v (ws_view ws) img log log
              (pub_transfer_refl log c) with "Hlog Hmg Hi Hpt").
  Qed.


  (* ==================================================================== *)
  (** ** 4. THE LOAD RULE

      Event altitude: one byte, inside the [wp_wexec_step] callback.  What is
      being collapsed is [WeakExec.wp_wexec_step]'s ∀-over-oracles: a weak
      read of byte [a] may return ANY admissible timestamp, and the rule says
      every one of them carries the value [v] the points-to names.  The
      timestamp genuinely varies (a racy cell case-splits); the VALUE cannot.

      The pure heart is [WeakMem.readable_latest_pin] (the collapse lemma):
      [wlat_lookup] says my element IS the latest write, my index says the
      floor covers its timestamp, and [readable]'s coherence window then has
      room for exactly that one timestamp. *)

  Lemma wpt_load_rule σ σ' ak a dq v t' b :
    ak_coh ak = false →
    wbyte_ok σ ak a t' b →
    wm_img σ' = wm_img σ →
    wm_log σ' = wm_log σ →
    (flr (ws_view (wm_ws σ)) a ≤ flr (ws_view (wm_ws σ')) a)%nat →
    wlat_interp (wm_img σ) (wm_log σ) -∗ vwp_hold (a ↦w{dq} v) (wm_ws σ) -∗
    ⌜b = v⌝ ∗ wlat_interp (wm_img σ') (wm_log σ') ∗
    vwp_hold (a ↦w{dq} v) (wm_ws σ').
  Proof.
    intros Hcoh Hok Himg Hlog Hfl.
    iIntros "Hi Hpt". rewrite wpt_at. iDestruct "Hpt" as (t) "[He %Ht]".
    iDestruct (wlat_lookup with "Hi He") as %Hlat.
    destruct Hok as [Hv Hadm]. rewrite Hcoh in Hadm.
    destruct Hadm as [Hrd _].
    assert (t' = t) as ->.
    { eapply (readable_latest_pin (wimg σ) (wm_log σ) (wm_ws σ)
                (load_vpre (wm_ws σ) (ak_sync ak)) a t t').
      - exact (latest_val_latest _ _ _ _ _ Hlat).
      - rewrite flr_ws_view in Ht.
        pose proof (load_vpre_vrNew (wm_ws σ) (ak_sync ak)). lia.
      - exact Hrd. }
    assert (b = v) as ->.
    { destruct Hlat as [Hlv _]. rewrite Hv in Hlv. by simplify_eq. }
    iSplitR; [done|]. rewrite Himg Hlog. iFrame "Hi".
    rewrite wpt_at. iExists t. iFrame "He". iPureIntro. lia.
  Qed.

  (** The framing side conditions, discharged once and for all at the
      interpreter's own read post-state: a read moves neither the image nor
      the log, and only RAISES the views. *)
  Lemma wpt_load_wread σ ak a dq v pa ts t' b :
    ak_coh ak = false →
    wbyte_ok σ ak a t' b →
    wlat_interp (wm_img σ) (wm_log σ) -∗ vwp_hold (a ↦w{dq} v) (wm_ws σ) -∗
    ⌜b = v⌝ ∗
    wlat_interp (wm_img (wread_post σ ak pa ts)) (wm_log (wread_post σ ak pa ts)) ∗
    vwp_hold (a ↦w{dq} v) (wm_ws (wread_post σ ak pa ts)).
  Proof.
    intros Hcoh Hok. iApply wpt_load_rule; [exact Hcoh|exact Hok| | |].
    - apply wread_post_img.
    - apply wread_post_log.
    - apply (ws_view_mono _ _ (wread_post_ws_le σ ak pa ts) a).
  Qed.

  (** *** 4'. THE OWNED LOAD RULE — a hart reads its OWN (possibly DIRTY) byte

      [WkOwnPingPong]'s recorded gap (1).  [wpt_load_rule] goes through
      [WeakGhost.wlat_lookup], which wants the CLEAN half of the points-to; a
      hart that has just plain-stored to a byte holds [↦wo] instead and could
      not read what it wrote.  The collapse itself never needed the state
      element: [WeakGhost.wlat_lookup_elem] is stated over the bare VALUE
      element, which is what [wpt_own] carries.  So this is [wpt_load_rule]
      with one lemma name changed, and it is the rule every ported proof that
      re-reads what it just wrote will use.

      IT NEEDS NO MIGRATION MACHINERY AT ALL, and that is worth stating: a
      load moves no [wcds] state, so a byte dirtied on a hart the context has
      since left reads through this rule VERBATIM.  What the migration costs
      is the φ payment, and that is [nv_ok_of_wpt_own]'s internal case split
      (§3c'), not a caller obligation.  So the load site's script is literally
      unchanged across a yield — which is Stage 1.6's acid test. *)
  Lemma wpt_load_rule_own (ξ : CtxId) σ σ' ak a v t' b :
    ak_coh ak = false →
    wbyte_ok σ ak a t' b →
    wm_img σ' = wm_img σ →
    wm_log σ' = wm_log σ →
    (flr (ws_view (wm_ws σ)) a ≤ flr (ws_view (wm_ws σ')) a)%nat →
    wlat_interp (wm_img σ) (wm_log σ) -∗ vwp_hold (wpt_own ξ a v) (wm_ws σ) -∗
    ⌜b = v⌝ ∗ wlat_interp (wm_img σ') (wm_log σ') ∗
    vwp_hold (wpt_own ξ a v) (wm_ws σ').
  Proof.
    intros Hcoh Hok Himg Hlog Hfl.
    iIntros "Hi Hpt". rewrite wpt_own_at.
    iDestruct "Hpt" as (t) "(He & Hs & %Ht)".
    iDestruct (wlat_lookup_elem with "Hi He") as %Hlat.
    destruct Hok as [Hv Hadm]. rewrite Hcoh in Hadm.
    destruct Hadm as [Hrd _].
    assert (t' = t) as ->.
    { eapply (readable_latest_pin (wimg σ) (wm_log σ) (wm_ws σ)
                (load_vpre (wm_ws σ) (ak_sync ak)) a t t').
      - exact (latest_val_latest _ _ _ _ _ Hlat).
      - rewrite flr_ws_view in Ht.
        pose proof (load_vpre_vrNew (wm_ws σ) (ak_sync ak)). lia.
      - exact Hrd. }
    assert (b = v) as ->.
    { destruct Hlat as [Hlv _]. rewrite Hv in Hlv. by simplify_eq. }
    iSplitR; [done|]. rewrite Himg Hlog. iFrame "Hi".
    rewrite wpt_own_at. iExists t. iFrame "He Hs". iPureIntro. lia.
  Qed.

  (** The framing side conditions at the interpreter's own read post-state,
      exactly as [wpt_load_wread] discharges them for the clean form. *)
  Lemma wpt_load_wread_own (ξ : CtxId) σ ak a v pa ts t' b :
    ak_coh ak = false →
    wbyte_ok σ ak a t' b →
    wlat_interp (wm_img σ) (wm_log σ) -∗ vwp_hold (wpt_own ξ a v) (wm_ws σ) -∗
    ⌜b = v⌝ ∗
    wlat_interp (wm_img (wread_post σ ak pa ts)) (wm_log (wread_post σ ak pa ts)) ∗
    vwp_hold (wpt_own ξ a v) (wm_ws (wread_post σ ak pa ts)).
  Proof.
    intros Hcoh Hok. iApply wpt_load_rule_own; [exact Hcoh|exact Hok| | |].
    - apply wread_post_img.
    - apply wread_post_log.
    - apply (ws_view_mono _ _ (wread_post_ws_le σ ak pa ts) a).
  Qed.

  (* ==================================================================== *)
  (** ** 5. THE STORE RULE

      Event altitude: one byte.  The store appends its message at the log's
      fresh top [t' = S (length log)] (promise-free: there is no
      admissibility condition to check), the [γlat] element for [a] is
      updated to [(t', v')], and [WeakGhost.wlat_agree_store] re-establishes
      the state interpretation's tie — the [a]-side because nothing can be
      above a fresh top, every OTHER byte by [latest_val_app] because the
      message does not write it.

      The post-view premise is the honest one: the hart's floor at [a] must
      cover the new timestamp.  [flr_store_post] discharges it at the
      machine's own [store_post], and [ws_view_mono] carries it through any
      later view growth. *)

  (** THE C/D/S SPLIT (φ-upgrade §1) gives the rule TWO ENTRY FORMS, and the
      class of the message decides which applies:

        - the OWNED form, for a store that may be [WCplain] (every plain [sb]
          / [sw] / [sd]): it consumes and produces [↦wo], because a plain
          store DIRTIES its byte and only the owning hart may hold a dirty
          one.  Its side condition is [wm_ak m ≠ WCexcl] — an exclusive store
          neither dirties nor publishes, so it must not be allowed to declare
          a byte clean.
        - the CLEAN form, for a store that is not an owned store at all (an
          AMO's write half, a release): it consumes and produces [↦w{1}],
          which is what keeps a lock word — held clean inside an invariant —
          clean across an acquire and a release. *)

  (** THE OWNED STORE, Stage 1.6 shape.  Three things enter beyond the
      Stage-1.5 statement, and NONE of them is an evidence parameter a caller
      supplies per site:

        - the LOG AUTHORITY at the POST-log, which every store leaf already
          holds (it comes back inside [wmstate_rest σ']).  The retarget reads
          the foreign author's publication floor off it, and the mint reads
          the position bound;
        - [ctx_migr ξ c], the scheduler's migration invariant, which rides in
          [WeakCtx.wrunning] and is therefore threaded by the ctx conversion
          anyway;
        - nothing else.

      The case split "did this context dirty [a] on a hart it has since
      left?" happens INSIDE, in [WeakGhost.wown_ctx_retarget].  So the store
      site's script is the same before and after a yield. *)
  Lemma wpt_store_rule_own (ξ : CtxId) (c : CPU) σ σ' m a v v' :
    msg_byte m a = Some v' →
    (∀ a', a' ≠ a → msg_byte m a' = None) →
    wm_tid m = Some (fin_to_nat c) →
    wm_img σ' = wm_img σ →
    wm_log σ' = (wm_log σ ++ [m])%list →
    (S (length (wm_log σ)) ≤ flr (ws_view (wm_ws σ')) a)%nat →
    wlog_auth (wm_log σ') -∗ ctx_migr ξ c -∗
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (wpt_own ξ a v) (wm_ws σ) ==∗
    wlog_auth (wm_log σ') ∗ ctx_migr ξ c ∗
    wlat_interp (wm_img σ') (wm_log σ') ∗
    vwp_hold (wpt_own ξ a v') (wm_ws σ').
  Proof.
    intros Hma Hother Htid Himg Hlog Hfl.
    iIntros "Hlg Hmg Hi Hpt". rewrite wpt_own_at.
    iDestruct "Hpt" as (t) "(He & Hs & _)".
    (* THE RETARGET, and the log-authority offset it tolerates: the store's
       own message is [c]'s, so it publishes nothing for any other hart *)
    iMod (wown_ctx_retarget ξ c a t v (wm_img σ) (wm_log σ) (wm_log σ')
            ltac:(rewrite Hlog; by apply pub_transfer_snoc)
            with "Hlg Hmg Hi He Hs") as "(Hlg & Hmg & Hi & He & Hs)".
    (* THE MINT, at the store's own fresh top *)
    iMod (ctx_migr_mint ξ c (wm_log σ') (S (length (wm_log σ)))
            ltac:(rewrite Hlog length_app /=; lia) with "Hlg Hmg")
      as "(Hlg & Hmg & #Hbc)".
    iDestruct (ctx_wrote_byte ξ c a (S (length (wm_log σ))) with "Hbc")
      as "#Hbca".
    iFrame "Hlg Hmg".
    iDestruct "Hs" as (s) "[Hsel %Hs]".
    iDestruct "Hi" as (mm mc) "(Hauth & %Hag & Hcauth & %Hagc)".
    rewrite /wlat_elem /wcds_el.
    iDestruct (ghost_map_lookup with "Hcauth Hsel") as %Hlk.
    iMod (ghost_map_update (S (length (wm_log σ)), v') with "Hauth He")
      as "[Hauth He]".
    iMod (ghost_map_update (wcds_own_step c (wm_ak m) s) with "Hcauth Hsel")
      as "[Hcauth Hsel]".
    iModIntro. rewrite Himg Hlog. iSplitL "Hauth Hcauth".
    - iExists _, _. iFrame "Hauth Hcauth". iSplitR.
      { iPureIntro. by apply wlat_agree_store. }
      iPureIntro. intros a' s' Ha'.
      destruct (decide (a' = a)) as [->|Hne].
      + rewrite lookup_insert in Ha'. simplify_eq.
        by apply wcds_ok_store_own; [| |apply (Hagc a s Hlk)].
      + rewrite lookup_insert_ne // in Ha'.
        apply wcds_ok_app; [|by apply Hagc].
        intros m0 Hm0. apply elem_of_list_singleton in Hm0 as ->.
        by apply Hother.
    - rewrite wpt_own_at. iExists (S (length (wm_log σ))). iFrame "He".
      iSplitL "Hsel"; [|by iPureIntro].
      iApply (wown_ctx_of_own_st ξ c a (S (length (wm_log σ)))
                with "[Hsel] Hbca").
      iExists (wcds_own_step c (wm_ak m) s). iFrame "Hsel". iPureIntro.
      destruct (wm_ak m); simpl; [by right|by left|exact Hs].
  Qed.

  Lemma wpt_store_rule σ σ' m a v v' :
    msg_byte m a = Some v' →
    (∀ a', a' ≠ a → msg_byte m a' = None) →
    wm_ak m ≠ WCplain →
    wm_img σ' = wm_img σ →
    wm_log σ' = (wm_log σ ++ [m])%list →
    (S (length (wm_log σ)) ≤ flr (ws_view (wm_ws σ')) a)%nat →
    wlat_interp (wm_img σ) (wm_log σ) -∗ vwp_hold (a ↦w v) (wm_ws σ) ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗ vwp_hold (a ↦w v') (wm_ws σ').
  Proof.
    intros Hma Hother Hk Himg Hlog Hfl.
    iIntros "Hi Hpt". rewrite wpt_at. iDestruct "Hpt" as (t) "[[He Hc] _]".
    iDestruct "Hi" as (mm mc) "(Hauth & %Hag & Hcauth & %Hagc)".
    rewrite /wlat_elem.
    iMod (ghost_map_update (S (length (wm_log σ)), v') with "Hauth He")
      as "[Hauth He]".
    (* T2-0: [wcds_ok_store_nonplain] is false at a [WLock] byte, so the
       framing needs the ONE byte this message writes to be non-[WLock] —
       which the points-to's own [wclean] half says. *)
    iDestruct (ghost_map_lookup with "Hcauth Hc") as %K.
    iModIntro. rewrite Himg Hlog. iSplitL "Hauth Hcauth".
    - iExists _, _. iFrame "Hauth Hcauth". iSplitR.
      { iPureIntro. by apply wlat_agree_store. }
      iPureIntro.
      exact (wcds_agree_nonplain1 _ m mc a WClean Hk eq_refl Hother K Hagc).
    - rewrite wpt_at. iExists (S (length (wm_log σ))). by iFrame "He Hc".
  Qed.

  (** At the machine's own store post-state, the post-view premise is
      automatic. *)
  Lemma wpt_store_post σ m a v v' rl :
    msg_byte m a = Some v' →
    (∀ a', a' ≠ a → msg_byte m a' = None) →
    wm_ak m ≠ WCplain →
    wlat_interp (wm_img σ) (wm_log σ) -∗ vwp_hold (a ↦w v) (wm_ws σ) ==∗
    wlat_interp (wm_img σ) ((wm_log σ ++ [m])%list) ∗
    vwp_hold (a ↦w v')
      (store_post (wm_ws σ) rl a (S (length (wm_log σ)))).
  Proof.
    intros Hma Hother Hk.
    iApply (wpt_store_rule
              (WMState (wm_regs σ) (wm_img σ) (wm_log σ) (wm_ws σ) (wm_dev σ))
              (WMState (wm_regs σ) (wm_img σ) ((wm_log σ ++ [m])%list)
                       (store_post (wm_ws σ) rl a (S (length (wm_log σ))))
                       (wm_dev σ)));
      [exact Hma|exact Hother|exact Hk|reflexivity|reflexivity|].
    apply flr_store_post.
  Qed.

  (** The owned twin. *)
  Lemma wpt_store_post_own (ξ : CtxId) (c : CPU) σ m a v v' rl :
    msg_byte m a = Some v' →
    (∀ a', a' ≠ a → msg_byte m a' = None) →
    wm_tid m = Some (fin_to_nat c) →
    wlog_auth ((wm_log σ ++ [m])%list) -∗ ctx_migr ξ c -∗
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (wpt_own ξ a v) (wm_ws σ) ==∗
    wlog_auth ((wm_log σ ++ [m])%list) ∗ ctx_migr ξ c ∗
    wlat_interp (wm_img σ) ((wm_log σ ++ [m])%list) ∗
    vwp_hold (wpt_own ξ a v')
      (store_post (wm_ws σ) rl a (S (length (wm_log σ)))).
  Proof.
    intros Hma Hother Htid.
    iApply (wpt_store_rule_own ξ c
              (WMState (wm_regs σ) (wm_img σ) (wm_log σ) (wm_ws σ) (wm_dev σ))
              (WMState (wm_regs σ) (wm_img σ) ((wm_log σ ++ [m])%list)
                       (store_post (wm_ws σ) rl a (S (length (wm_log σ))))
                       (wm_dev σ)));
      [exact Hma|exact Hother|exact Htid|reflexivity|reflexivity|].
    apply flr_store_post.
  Qed.

End pointsto.

(* ====================================================================== *)
(** ** 5b. THE AMBIENT API (φ-upgrade §1.7)

    The rules above, with the context read out of the [CurCtx] instance
    instead of taken as an argument.  They are THIN WRAPPERS and nothing else
    — each is its primitive applied at [cur_ctx] — and the primitives stay
    exactly as they were, because a proof with two contexts in scope must be
    able to use them at both (see §3'''s convention block).

    What this buys is the property Stage 1.6 was for, at the surface: an
    access site names neither a hart nor a context, so the SAME script runs
    before and after a migration and the resource it acts on is literally the
    same proposition. *)

Section cur_ctx_api.
  Context `{!riscvGS Σ, !weakGS Σ} `{XI : CurCtx}.

  (** A clean full-fraction byte is owned by the ambient context — the
      receiving side of a transfer, in one line. *)
  Lemma wpt_own_of_wpt_cur a v : (a ↦w v : vProp Σ) ⊢ a ↦wo v.
  Proof. apply wpt_own_of_wpt. Qed.

  (** THE OWNED LOAD (§4'), ambient. *)
  Lemma wpt_load_rule_own_cur σ σ' ak a v t' b :
    ak_coh ak = false →
    wbyte_ok σ ak a t' b →
    wm_img σ' = wm_img σ →
    wm_log σ' = wm_log σ →
    (flr (ws_view (wm_ws σ)) a ≤ flr (ws_view (wm_ws σ')) a)%nat →
    wlat_interp (wm_img σ) (wm_log σ) -∗ vwp_hold (a ↦wo v) (wm_ws σ) -∗
    ⌜b = v⌝ ∗ wlat_interp (wm_img σ') (wm_log σ') ∗
    vwp_hold (a ↦wo v) (wm_ws σ').
  Proof. apply wpt_load_rule_own. Qed.

  Lemma wpt_load_wread_own_cur σ ak a v pa ts t' b :
    ak_coh ak = false →
    wbyte_ok σ ak a t' b →
    wlat_interp (wm_img σ) (wm_log σ) -∗ vwp_hold (a ↦wo v) (wm_ws σ) -∗
    ⌜b = v⌝ ∗
    wlat_interp (wm_img (wread_post σ ak pa ts)) (wm_log (wread_post σ ak pa ts)) ∗
    vwp_hold (a ↦wo v) (wm_ws (wread_post σ ak pa ts)).
  Proof. apply wpt_load_wread_own. Qed.

  (** THE OWNED STORE (§5), ambient.  The hart [c] stays explicit: it is the
      hart the STEP runs on, which the machine supplies and which genuinely
      varies — it is not the thing §1.7 makes ambient. *)
  Lemma wpt_store_rule_own_cur (c : CPU) σ σ' m a v v' :
    msg_byte m a = Some v' →
    (∀ a', a' ≠ a → msg_byte m a' = None) →
    wm_tid m = Some (fin_to_nat c) →
    wm_img σ' = wm_img σ →
    wm_log σ' = (wm_log σ ++ [m])%list →
    (S (length (wm_log σ)) ≤ flr (ws_view (wm_ws σ')) a)%nat →
    wlog_auth (wm_log σ') -∗ ctx_migr cur_ctx c -∗
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (a ↦wo v) (wm_ws σ) ==∗
    wlog_auth (wm_log σ') ∗ ctx_migr cur_ctx c ∗
    wlat_interp (wm_img σ') (wm_log σ') ∗
    vwp_hold (a ↦wo v') (wm_ws σ').
  Proof. apply wpt_store_rule_own. Qed.

  Lemma wpt_store_post_own_cur (c : CPU) σ m a v v' rl :
    msg_byte m a = Some v' →
    (∀ a', a' ≠ a → msg_byte m a' = None) →
    wm_tid m = Some (fin_to_nat c) →
    wlog_auth ((wm_log σ ++ [m])%list) -∗ ctx_migr cur_ctx c -∗
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (a ↦wo v) (wm_ws σ) ==∗
    wlog_auth ((wm_log σ ++ [m])%list) ∗ ctx_migr cur_ctx c ∗
    wlat_interp (wm_img σ) ((wm_log σ ++ [m])%list) ∗
    vwp_hold (a ↦wo v')
      (store_post (wm_ws σ) rl a (S (length (wm_log σ)))).
  Proof. apply wpt_store_post_own. Qed.

  (** THE φ PAYMENT (§3c'), ambient — the lemma every access site applies,
      migrated or not. *)
  Lemma nv_ok_of_wpt_own_cur (c : CPU) (a : Z) (v : bv 8) (V : view)
      img (log logA : list wmsg) :
    pub_transfer logA log c →
    wlog_auth logA -∗ ctx_migr cur_ctx c -∗ wlat_interp img log -∗
    monPred_at (a ↦wo v) V -∗ ⌜nv_ok log c a⌝.
  Proof. apply nv_ok_of_wpt_own. Qed.

  Lemma nv_ok_of_wpt_own_at_cur (c : CPU) (a : Z) (v : bv 8)
      img (log : list wmsg) (ws : wstate) :
    wlog_auth log -∗ ctx_migr cur_ctx c -∗ wlat_interp img log -∗
    vwp_hold (a ↦wo v) ws -∗ ⌜nv_ok log c a⌝.
  Proof. apply nv_ok_of_wpt_own_at. Qed.

End cur_ctx_api.

(* ====================================================================== *)
(** ** 6. The monPred altitude

    The DERIVED statements: the same two rules with the hart's index spelled
    as a [view] and the points-to frozen at it.  These are what the M3 lock
    library will quote — and they are three lines each, which is the point of
    the discipline. *)

Section vprop_altitude.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma vwp_hold_view_at_iff (P : vProp Σ) ws :
    vwp_hold P ws ⊣⊢ vwp_hold (P @@ ws_view ws) ws.
  Proof. apply vwp_hold_freeze. Qed.

  (** THE LOAD RULE, [vProp] altitude: at the hart's index, an owned byte
      pins the value of every admissible weak read of it. *)
  Lemma wpt_load_vprop σ ak a dq v t' b :
    ak_coh ak = false →
    wbyte_ok σ ak a t' b →
    (⎡wlat_interp (wm_img σ) (wm_log σ)⎤ ∗ (a ↦w{dq} v) @@ ws_view (wm_ws σ)
       : vProp Σ)
    ⊢ ⌜b = v⌝.
  Proof.
    intros Hcoh Hok. constructor => V.
    rewrite monPred_at_sep monPred_at_embed monPred_at_pure view_at_at.
    iIntros "[Hi Hpt]".
    by iDestruct (wpt_load_rule σ σ with "Hi Hpt") as "(% & _ & _)".
  Qed.

  (** THE STORE RULE, [vProp] altitude. *)
  Lemma wpt_store_vprop σ m a v v' rl :
    msg_byte m a = Some v' →
    (∀ a', a' ≠ a → msg_byte m a' = None) →
    wm_ak m ≠ WCplain →
    (⎡wlat_interp (wm_img σ) (wm_log σ)⎤ ∗ (a ↦w v) @@ ws_view (wm_ws σ)
       : vProp Σ)
    ⊢ |==> ⎡wlat_interp (wm_img σ) ((wm_log σ ++ [m])%list)⎤ ∗
           (a ↦w v') @@ ws_view (store_post (wm_ws σ) rl a
                                    (S (length (wm_log σ)))).
  Proof.
    intros Hma Hother Hk. constructor => V.
    rewrite monPred_at_sep monPred_at_embed view_at_at monPred_at_bupd
            monPred_at_sep monPred_at_embed view_at_at.
    iIntros "[Hi Hpt]".
    by iMod (wpt_store_post with "Hi Hpt") as "[$ $]".
  Qed.

End vprop_altitude.

(* ====================================================================== *)
(** ** 7. THE DEMO — a whole ACCESS, end to end through the interpreter

    The event rules above are per-byte.  This section runs them through
    [WeakInterp]'s own read arm at the width the machine actually uses, i.e.
    over the [wread_ok] obligation that [wrun]/[wexec] produce for ONE
    [Interface.MemRead] — an [lb]/[lh]/[lw]/[ld]-class access, at any [n].
    Owning the [n] bytes at the hart's index pins the whole assembled word.

    This is the interface-composition check M2a is for: the [vProp]
    points-to, the [vwp_hold] discipline, [WeakGhost]'s latest-write tie and
    [WeakInterp]'s admissibility predicate compose with no impedance
    mismatch, at the altitude of a real memory access.  What is NOT here is
    the instruction tower above it — see the note at the end of the file. *)

Section demo.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** One byte of an access. *)
  Lemma wpt_wread_byte σ ak pa n ts (w : bv (8 * n)) dq (b : bv 8) j :
    ak_coh ak = false →
    (j < N.to_nat n)%nat →
    wread_ok σ ak pa n ts w →
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (acc_addr pa j ↦w{dq} b) (wm_ws σ) -∗
    ⌜nth_byte w j = b⌝.
  Proof.
    intros Hcoh Hj [_ Hbytes]. iIntros "Hi Hpt".
    assert (Hjn : (N.of_nat j < n)%N) by lia.
    iDestruct (wpt_load_rule σ σ with "Hi Hpt") as "(% & _ & _)";
      [exact Hcoh|exact (Hbytes j Hjn)|reflexivity|reflexivity|lia|].
    done.
  Qed.

  (** The whole access: every byte of the returned word is the byte owned at
      that address.  [j] is a Coq-level parameter, so the "for every byte"
      reading is the ∀ in front of the lemma — no induction over the access
      width is needed, and the [wlat_interp] authority is consumed once. *)
  Lemma wpt_wread_bytes σ ak pa n ts (w : bv (8 * n)) dq (bs : list (bv 8)) j :
    ak_coh ak = false →
    length bs = N.to_nat n →
    (j < N.to_nat n)%nat →
    wread_ok σ ak pa n ts w →
    wlat_interp (wm_img σ) (wm_log σ) -∗
    ([∗ list] j' ↦ b ∈ bs, vwp_hold (acc_addr pa j' ↦w{dq} b) (wm_ws σ)) -∗
    ⌜nth_byte w j = bs !!! j⌝.
  Proof.
    intros Hcoh Hlen Hj Hok. iIntros "Hi Hbs".
    assert (Hlk : bs !! j = Some (bs !!! j)).
    { apply list_lookup_lookup_total_lt. lia. }
    iDestruct (big_sepL_lookup _ _ j _ Hlk with "Hbs") as "Hpt".
    by iApply (wpt_wread_byte σ ak pa n ts w dq _ j with "Hi Hpt").
  Qed.

  (** ... hence the READ VALUE IS DETERMINED: whatever timestamps the oracle
      chose, the word [wrun]/[wexec] returns is the little-endian assembly of
      the bytes I own.  This is the statement a real load leaf consumes. *)
  Lemma wpt_wread_word σ ak pa n ts (w : bv (8 * n)) dq (bs : list (bv 8)) :
    ak_coh ak = false →
    length bs = N.to_nat n →
    wread_ok σ ak pa n ts w →
    wlat_interp (wm_img σ) (wm_log σ) -∗
    ([∗ list] j' ↦ b ∈ bs, vwp_hold (acc_addr pa j' ↦w{dq} b) (wm_ws σ)) -∗
    ⌜w = Z_to_bv (8 * n) (assemble_bytes bs)⌝.
  Proof.
    intros Hcoh Hlen Hok. iIntros "Hi Hbs".
    iAssert (⌜∀ j, (j < N.to_nat n)%nat → nth_byte w j = bs !!! j⌝)%I
      as %Hall.
    { rewrite bi.pure_forall. iIntros (j).
      destruct (decide (j < N.to_nat n)%nat) as [Hj|Hj].
      - iDestruct (wpt_wread_bytes σ ak pa n ts w dq bs j with "Hi Hbs")
          as %Heq; [exact Hcoh|exact Hlen|exact Hj|exact Hok|].
        iPureIntro. by intros _.
      - iPureIntro. by intros ?. }
    iPureIntro. apply bv_eq_of_bytes. intros j Hj.
    assert (Hb1 : 8 * Z.of_nat (length bs) <= Z.of_N (8 * n)).
    { rewrite Hlen N2Z.inj_mul N_nat_Z. lia. }
    assert (Hb2 : (j < length bs)%nat) by (rewrite Hlen; lia).
    rewrite (nth_byte_assemble_len (8 * n) bs j Hb1 Hb2).
    apply Hall. lia.
  Qed.

  (** The STORE side of the demo: the message [WeakInterp] appends for a
      ONE-BYTE store writes exactly the byte it should, which is what
      discharges the store rule's two [msg_byte] side conditions at the real
      interpreter. *)
  Lemma wwrite_msg_byte1 tid k (pa : Arch.pa) (v : bv (8 * 1)) :
    msg_byte (wwrite_msg tid k pa 1 v) (pa_z pa) = Some (nth_byte v 0).
  Proof.
    rewrite -(acc_addr_0 pa). apply (wwrite_msg_byte tid k pa 1 v 0). simpl. lia.
  Qed.

  Lemma wwrite_msg_byte1_none tid k (pa : Arch.pa) (v : bv (8 * 1)) a :
    a ≠ pa_z pa → msg_byte (wwrite_msg tid k pa 1 v) a = None.
  Proof.
    intros Hne. rewrite /msg_byte /wwrite_msg /=.
    case_bool_decide as Hle; [|reflexivity].
    assert (Hgt : 0 < a - pa_z pa) by lia.
    rewrite lookup_ge_None_2 //. simpl. lia.
  Qed.

  (** ... so the store rule fires at the interpreter's own write post-state,
      with no side condition left for the caller beyond the value. *)
  Lemma wpt_wwrite_byte (ξ : CtxId) (c : CPU) σ ak (pa : Arch.pa)
      (v : bv (8 * 1)) (v0 : bv 8) :
    wlog_auth (wm_log (wwrite_post (Some (fin_to_nat c)) σ ak pa 1 v)) -∗
    ctx_migr ξ c -∗
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (wpt_own ξ (pa_z pa) v0) (wm_ws σ) ==∗
    wlog_auth (wm_log (wwrite_post (Some (fin_to_nat c)) σ ak pa 1 v)) ∗
    ctx_migr ξ c ∗
    wlat_interp (wm_img (wwrite_post (Some (fin_to_nat c)) σ ak pa 1 v))
                (wm_log (wwrite_post (Some (fin_to_nat c)) σ ak pa 1 v)) ∗
    vwp_hold (wpt_own ξ (pa_z pa) (nth_byte v 0))
             (wm_ws (wwrite_post (Some (fin_to_nat c)) σ ak pa 1 v)).
  Proof.
    iApply (wpt_store_rule_own ξ c σ
              (wwrite_post (Some (fin_to_nat c)) σ ak pa 1 v)
              (wwrite_msg (Some (fin_to_nat c)) (wm_class_of ak (wm_ws σ))
                          pa 1 v)).
    - apply wwrite_msg_byte1.
    - intros a' Hne. by apply wwrite_msg_byte1_none.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - rewrite /wwrite_post /store_post_run /store_post_bytes /=.
      replace (pa_z pa + Z.of_nat 0) with (pa_z pa) by lia.
      apply flr_store_post.
  Qed.

End demo.

(* ======================================================================
   WHERE THE INSTRUCTION ALTITUDE STARTS, AND WHAT IT NEEDS (M2b/M3)

   Everything above stops at the MEMORY EVENT: the [wread_ok] / [wwrite_post]
   obligations one [Interface.MemRead] / [Interface.MemWrite] produces.  A
   whole-instruction leaf ([wp_ld_…] in the shape of the SC tree's
   [WpSmode*]/[WpMmode*] leaves) additionally needs, and none of it is
   weak-memory work:

     - the FETCH of the instruction bytes as a weak read.  Kernel text has a
       single message (timestamp 0), so [wpt_img] (§3b) is exactly the
       resource that makes it deterministic — but the tree's [instr] /
       decode-bridge machinery is stated over [RiscvPtsto]'s [gen_heap]
       memory, which the weak state interpretation does not carry.  Porting
       [InstrBytes]/[WpDecodeBridge] onto [wpt_img] is the first M2b task and
       is a restatement, not a proof.
     - the [sconf]/[hw_config]/PMP/translation tower each leaf carries, which
       is entirely register-side and therefore OBJECTIVE (§3b's rationale):
       it rides along through [⎡·⎤] with no view plumbing at all.
     - [WeakExec.wexec_covers], which a leaf discharges by
       [wexec_covers_choice_free] over the concrete peeled instruction.

   The M2a conclusion is that the seam is in the right place: the two rules
   above are stated exactly against what the interpreter hands a leaf, and
   the remaining distance to a whole instruction is the SC tree's existing
   fetch/decode/config towers, not anything about views.
   ====================================================================== *)
