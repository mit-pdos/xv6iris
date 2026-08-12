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

  (** *** 3'. THE OWNED FORM — [↦wo] (the φ-upgrade's C-or-D points-to)

      A byte a hart owns EXCLUSIVELY and may have plain-stored to: the value
      element at full fraction, plus a state element that is CLEAN or DIRTY
      BY THIS HART.  This is the postcondition shape of every owned store —
      it absorbs both outcomes, so no call site case-splits on the access
      class — and the only shape a plain store accepts on the way in.

      IT IS HART-INDEXED, DELIBERATELY, and therefore does NOT survive
      [WpNext.wp_next] (see [WeakSmodeFrame]'s §5 control).  That is sound:
      an unpublished own store IS a fact about the storing hart, and a
      migrating context must publish (flip to C, §5b) before it moves.  The
      M-mode weak port never crosses a [wp_next] binder with one. *)
  Definition wpt_own (c : CPU) (a : Z) (v : bv 8) : vProp Σ :=
    (∃ t : nat, ⎡ wlat_elem a (DfracOwn 1) t v ∗ wown_st c a ⎤ ∗
                ⊒(view_byte a t))%I.

End rules.

Notation "a ↦w dq v" := (wpt a dq v)
  (at level 20, dq custom dfrac at level 1, format "a  ↦w dq  v") : bi_scope.
Notation "a ↦wo v" := (wpt_own cpu_id a v)
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

  Lemma wpt_own_at_view c a v (V : view) :
    monPred_at (wpt_own c a v) V ⊣⊢
      ∃ t : nat, wlat_elem a (DfracOwn 1) t v ∗ wown_st c a ∗
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

  Lemma wpt_own_at c a v ws :
    vwp_hold (wpt_own c a v) ws ⊣⊢
      ∃ t : nat, wlat_elem a (DfracOwn 1) t v ∗ wown_st c a ∗
                 ⌜(t ≤ flr (ws_view ws) a)%nat⌝.
  Proof. apply wpt_own_at_view. Qed.

  Lemma wpt_own_at_intro c a v t ws :
    (t ≤ flr (ws_view ws) a)%nat →
    wlat_elem a (DfracOwn 1) t v -∗ wown_st c a -∗
    vwp_hold (wpt_own c a v) ws.
  Proof.
    intros Ht. rewrite wpt_own_at. iIntros "He Hs". iExists t. by iFrame.
  Qed.

  (** A CLEAN full-fraction byte IS an owned byte.  The converse is NOT
      available in general — that is the whole point of the D state, and
      recovering it is what a release's flip ([WeakStore.wpt_own_flip]) does. *)
  Lemma wpt_own_of_wpt c a v : (a ↦w v : vProp Σ) ⊢ wpt_own c a v.
  Proof.
    rewrite /wpt /wpt_own. constructor => V.
    rewrite !monPred_at_exist. apply bi.exist_mono => t.
    rewrite !monPred_at_sep !monPred_at_embed.
    iIntros "[[He Hc] $]". iFrame "He". by iApply wclean_own_st.
  Qed.

  Lemma wpt_own_mono c a v ws ws' :
    ws_le ws ws' → vwp_hold (wpt_own c a v) ws ⊢ vwp_hold (wpt_own c a v) ws'.
  Proof. apply vwp_hold_mono. Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 3c'. THE PUBLICATION FLOOR OVER A VIEW, AND THE LAZY UPGRADE
      (φ-upgrade §1.5 — the framing pattern's ACCEPTANCE ARM)

      A thread that dirtied bytes on hart [c], parked, and resumed elsewhere
      holds its ownership facts FROZEN at the index [V] it had when it parked
      ([monPred_at P V] — objective, so it frames around the yield with
      nothing to prove).  What it gets back from the yield is ONE persistent
      token:

        [pub_covers_view c V] — "hart [c] has published everything [V] can
        see".

      STATED OVER THE VIEW, not over a position, and that is the whole trick:
      a framed [↦wo] carries [⊒(view_byte a t)], which AT THE FROZEN INDEX is
      [t ≤ flr V a] — so the timestamp side condition the position-indexed
      form would need is already in the resource, by construction.  Nothing
      at the leaf has to name a timestamp.

      The token is minted by the migration handoff's RELEASE STORE, which
      needs no view arithmetic either: its message sits at the log's fresh
      top, which dominates the parking hart's whole index by
      [WeakMem.ws_bounded]. *)

  Definition pub_covers_view (c : CPU) (V : view) : iProp Σ :=
    (∃ n : nat, pub_floor c n ∗ ⌜V ⊑ view_scl n⌝)%I.

  Global Instance pub_covers_view_persistent c V :
    Persistent (pub_covers_view c V).
  Proof. rewrite /pub_covers_view. apply _. Qed.
  Global Instance pub_covers_view_timeless c V :
    Timeless (pub_covers_view c V).
  Proof. rewrite /pub_covers_view. apply _. Qed.

  (** THE MINT, at the view altitude: a floor at [n] covers every view whose
      floors are below [n] — which, at a release store, is the parking hart's
      whole index. *)
  Lemma pub_covers_view_intro c V n :
    V ⊑ view_scl n → pub_floor c n -∗ pub_covers_view c V.
  Proof. iIntros (Hle) "H". iExists n. by iFrame "H". Qed.

  (** ... and it covers every SMALLER view for free. *)
  Lemma pub_covers_view_mono c V V' :
    V' ⊑ V → pub_covers_view c V -∗ pub_covers_view c V'.
  Proof.
    iIntros (Hle) "[%n [H %Hn]]". iExists n. iFrame "H". iPureIntro.
    by etrans.
  Qed.

  (** THE ACCEPTANCE ARM.  A byte that hart [c] left DIRTY, presented at the
      index [c] parked with, together with [c]'s publication coverage of that
      index, IS a clean full-fraction byte at ANY hart whose index dominates
      [V].  The [wcds] state element is retargeted [WDirty c → WClean] in the
      interp-open ghost section; nothing else moves.

      AFTER THIS THE ORDINARY RULES APPLY VERBATIM — that is the point, and
      the reason there is no "own load with optional evidence" and no "own
      store with optional evidence": [wpt_load_rule] collapses the load,
      [wpt_own_of_wpt] re-owns at the NEW hart, and [wpt_store_rule_own]
      re-dirties it there.  No leaf statement changes. *)
  Lemma wpt_own_upgrade (c : CPU) (a : Z) (v : bv 8) (V : view)
      img (log : list wmsg) (ws : wstate) :
    V ⊑ ws_view ws →
    wlog_auth log -∗ pub_covers_view c V -∗ wlat_interp img log -∗
    monPred_at (wpt_own c a v) V ==∗
    wlog_auth log ∗ wlat_interp img log ∗ vwp_hold (a ↦w v) ws.
  Proof.
    iIntros (HV) "Hlog [%n [#Hpf %Hn]] Hi Hpt".
    rewrite wpt_own_at_view. iDestruct "Hpt" as (t) "(Hel & Hs & %Ht)".
    assert (Htn : (t ≤ n)%nat).
    { etrans; [exact Ht|]. rewrite -(flr_scl_eq n a). apply Hn. }
    iMod (wlat_flip_pub img log c a t n v Htn with "Hlog Hpf Hi Hel Hs")
      as "(Hlog & Hi & Hel & Hcl)".
    iModIntro. iFrame "Hlog Hi".
    iApply (vwp_hold_intro V _ ws HV). rewrite wpt_at_view.
    iExists t. rewrite /wlat_pointsto. iFrame "Hel Hcl". by iPureIntro.
  Qed.

  (** THE STORE ARM, in one step: the same upgrade followed by re-owning at
      the CURRENT hart, so the byte comes out [WDirty]-able by [c'].  After
      this the ordinary [wpt_store_rule_own] / [wpt_store_post_own] apply
      verbatim — a migrated thread's first STORE to a byte it dirtied on the
      old CPU costs exactly this one lemma and no leaf change.

      (The two arms are one lemma because the [wcds] retarget is the same in
      both: [WDirty c → WClean]; whether the byte then becomes [WDirty c'] is
      decided by the store's own message class, exactly as it always was.) *)
  Lemma wpt_own_upgrade_own (c c' : CPU) (a : Z) (v : bv 8) (V : view)
      img (log : list wmsg) (ws : wstate) :
    V ⊑ ws_view ws →
    wlog_auth log -∗ pub_covers_view c V -∗ wlat_interp img log -∗
    monPred_at (wpt_own c a v) V ==∗
    wlog_auth log ∗ wlat_interp img log ∗ vwp_hold (wpt_own c' a v) ws.
  Proof.
    iIntros (HV) "Hlog #Hpf Hi Hpt".
    iMod (wpt_own_upgrade c a v V img log ws HV with "Hlog Hpf Hi Hpt")
      as "($ & $ & Hpt)".
    iModIntro. iApply (vwp_hold_ent _ _ _ (wpt_own_of_wpt c' a v)).
    iExact "Hpt".
  Qed.

  (** ... and the φ payment of the SAME arm, before any ghost step: the byte
      is foreign-dirty but PUBLISHED, so it carries no violation obligation to
      any hart at any floor.  A leaf states this where it holds the framed
      fact, exactly as [WeakGhost.nv_ok_of_own_st] is used for a byte the
      CURRENT hart dirtied. *)
  Lemma nv_free_of_own_upgrade (c : CPU) (a : Z) (v : bv 8) (V : view)
      img (log : list wmsg) :
    wlog_auth log -∗ pub_covers_view c V -∗ wlat_interp img log -∗
    monPred_at (wpt_own c a v) V -∗ ⌜nv_free log a⌝.
  Proof.
    iIntros "Hlog [%n [#Hpf %Hn]] Hi Hpt".
    rewrite wpt_own_at_view. iDestruct "Hpt" as (t) "(Hel & Hs & %Ht)".
    assert (Htn : (t ≤ n)%nat).
    { etrans; [exact Ht|]. rewrite -(flr_scl_eq n a). apply Hn. }
    by iApply (nv_free_of_own_pub img log c a t n v Htn with "Hlog Hpf Hi Hel Hs").
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

      IT IS ALSO THE GENERAL SHAPE OF §3c''s ACCEPTANCE ARM: reading a
      FOREIGN-dirty published byte is this rule after [wpt_own_upgrade] +
      [wpt_own_of_wpt] ([wpt_load_rule_pub] below composes them). *)
  Lemma wpt_load_rule_own (c : CPU) σ σ' ak a v t' b :
    ak_coh ak = false →
    wbyte_ok σ ak a t' b →
    wm_img σ' = wm_img σ →
    wm_log σ' = wm_log σ →
    (flr (ws_view (wm_ws σ)) a ≤ flr (ws_view (wm_ws σ')) a)%nat →
    wlat_interp (wm_img σ) (wm_log σ) -∗ vwp_hold (wpt_own c a v) (wm_ws σ) -∗
    ⌜b = v⌝ ∗ wlat_interp (wm_img σ') (wm_log σ') ∗
    vwp_hold (wpt_own c a v) (wm_ws σ').
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
  Lemma wpt_load_wread_own (c : CPU) σ ak a v pa ts t' b :
    ak_coh ak = false →
    wbyte_ok σ ak a t' b →
    wlat_interp (wm_img σ) (wm_log σ) -∗ vwp_hold (wpt_own c a v) (wm_ws σ) -∗
    ⌜b = v⌝ ∗
    wlat_interp (wm_img (wread_post σ ak pa ts)) (wm_log (wread_post σ ak pa ts)) ∗
    vwp_hold (wpt_own c a v) (wm_ws (wread_post σ ak pa ts)).
  Proof.
    intros Hcoh Hok. iApply wpt_load_rule_own; [exact Hcoh|exact Hok| | |].
    - apply wread_post_img.
    - apply wread_post_log.
    - apply (ws_view_mono _ _ (wread_post_ws_le σ ak pa ts) a).
  Qed.

  (** THE FOREIGN-PUBLISHED LOAD, in one step: the migrated thread's first
      read of a byte it dirtied on the OLD hart.  Everything in the conclusion
      is at the NEW hart's index, and the byte comes back OWNED there — so the
      next store is an ordinary [wpt_store_rule_own]. *)
  Lemma wpt_load_rule_pub (c c' : CPU) (V : view) σ σ' ak a v t' b :
    ak_coh ak = false →
    wbyte_ok σ ak a t' b →
    wm_img σ' = wm_img σ →
    wm_log σ' = wm_log σ →
    V ⊑ ws_view (wm_ws σ) →
    (flr (ws_view (wm_ws σ)) a ≤ flr (ws_view (wm_ws σ')) a)%nat →
    wlog_auth (wm_log σ) -∗ pub_covers_view c V -∗
    wlat_interp (wm_img σ) (wm_log σ) -∗ monPred_at (wpt_own c a v) V ==∗
    ⌜b = v⌝ ∗ wlog_auth (wm_log σ) ∗
    wlat_interp (wm_img σ') (wm_log σ') ∗
    vwp_hold (wpt_own c' a v) (wm_ws σ').
  Proof.
    intros Hcoh Hok Himg Hlog HV Hfl. iIntros "Hlog #Hpf Hi Hpt".
    iMod (wpt_own_upgrade c a v V (wm_img σ) (wm_log σ) (wm_ws σ) HV
            with "Hlog Hpf Hi Hpt") as "(Hlog & Hi & Hpt)".
    iDestruct (wpt_load_rule σ σ' ak a (DfracOwn 1) v t' b
                 Hcoh Hok Himg Hlog Hfl with "Hi Hpt") as "(%Hb & Hi & Hpt)".
    iModIntro. iFrame "Hlog Hi". iSplitR; [by iPureIntro|].
    iApply (vwp_hold_ent _ _ _ (wpt_own_of_wpt c' a v)). iExact "Hpt".
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

  Lemma wpt_store_rule_own (c : CPU) σ σ' m a v v' :
    msg_byte m a = Some v' →
    (∀ a', a' ≠ a → msg_byte m a' = None) →
    wm_tid m = Some (fin_to_nat c) →
    wm_img σ' = wm_img σ →
    wm_log σ' = (wm_log σ ++ [m])%list →
    (S (length (wm_log σ)) ≤ flr (ws_view (wm_ws σ')) a)%nat →
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (wpt_own c a v) (wm_ws σ) ==∗
    wlat_interp (wm_img σ') (wm_log σ') ∗
    vwp_hold (wpt_own c a v') (wm_ws σ').
  Proof.
    intros Hma Hother Htid Himg Hlog Hfl.
    iIntros "Hi Hpt". rewrite wpt_own_at.
    iDestruct "Hpt" as (t) "(He & Hs & _)".
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
    iModIntro. rewrite Himg Hlog. iSplitL "Hauth Hcauth".
    - iExists _, _. iFrame "Hauth Hcauth". iSplitR.
      { iPureIntro. by apply wlat_agree_store. }
      iPureIntro. intros a' s' Ha'.
      by apply wcds_ok_store_nonplain; [|apply Hagc].
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
  Lemma wpt_store_post_own (c : CPU) σ m a v v' rl :
    msg_byte m a = Some v' →
    (∀ a', a' ≠ a → msg_byte m a' = None) →
    wm_tid m = Some (fin_to_nat c) →
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (wpt_own c a v) (wm_ws σ) ==∗
    wlat_interp (wm_img σ) ((wm_log σ ++ [m])%list) ∗
    vwp_hold (wpt_own c a v')
      (store_post (wm_ws σ) rl a (S (length (wm_log σ)))).
  Proof.
    intros Hma Hother Htid.
    iApply (wpt_store_rule_own c
              (WMState (wm_regs σ) (wm_img σ) (wm_log σ) (wm_ws σ) (wm_dev σ))
              (WMState (wm_regs σ) (wm_img σ) ((wm_log σ ++ [m])%list)
                       (store_post (wm_ws σ) rl a (S (length (wm_log σ))))
                       (wm_dev σ)));
      [exact Hma|exact Hother|exact Htid|reflexivity|reflexivity|].
    apply flr_store_post.
  Qed.

End pointsto.

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
  Lemma wpt_wwrite_byte (c : CPU) σ ak (pa : Arch.pa) (v : bv (8 * 1))
      (v0 : bv 8) :
    wlat_interp (wm_img σ) (wm_log σ) -∗
    vwp_hold (wpt_own c (pa_z pa) v0) (wm_ws σ) ==∗
    wlat_interp (wm_img (wwrite_post (Some (fin_to_nat c)) σ ak pa 1 v))
                (wm_log (wwrite_post (Some (fin_to_nat c)) σ ak pa 1 v)) ∗
    vwp_hold (wpt_own c (pa_z pa) (nth_byte v 0))
             (wm_ws (wwrite_post (Some (fin_to_nat c)) σ ak pa 1 v)).
  Proof.
    iApply (wpt_store_rule_own c σ
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
