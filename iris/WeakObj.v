(** * WeakObj.v — [wobj], the OBJECTIVITY MODALITY.

    THE PROBLEM THIS SOLVES.  [WeakPtOwn.wpt_own] ("[↦o]") is objective and
    hart-relative; [WeakPtPub.wpt_pub T] is objective and hart-free, and is
    what a lock invariant can hold.  They are different propositions, so a
    composite predicate — say a file-descriptor table, an [iProp] built from
    dozens of points-to facts nested several definitions deep — cannot be
    written once and used on both sides.  You would have to write it TWICE,
    or thread a [T] through every definition, and every intermediate lemma
    with it.  That is a tax on all client code, paid for a boundary the
    client is not even reasoning about.

    THE OBSERVATION.  What you want to thread is one parameter, silently,
    through every connective.  That is exactly what [vProp] IS — a
    proposition with an implicit view parameter, whose BI connectives
    already thread it — and [monPred_at R V] instantiates it WITHOUT
    unfolding [R].  The freezing a lock does is not a rewrite of the
    payload; it is one application of [monPred_at].

    THE CONSTRUCTION.  So write the composite predicate as a [vProp] over
    ordinary [WeakVProp.wpt] leaves, and define

      [wobj R := ∃ V, view_lb V ∗ monPred_at R V]

    "[R] holds at some view I have already reached".  [view_lb] is the
    persistent, view-valued generalisation of [WeakPtOwn.wflr_lb]: a floor
    on the hart's whole view rather than on one byte.  Then:

      - [wobj R] is an [iProp], hence objective, hence invariant-admissible
        and free of any [wstate] threading — the [↦o] property, for an
        ARBITRARY [R].
      - [wobj] commutes with [∗], [∃], [⌜⌝], [∨], [▷] and [big_sepM], so a
        composite predicate needs no per-definition transport lemma; the
        structural laws below already are that transport.
      - The two boundary conversions ([wobj_release] / [wobj_acquire]) are
        ONE lemma each, for ARBITRARY [R], with no unfolding.  Compare
        [WeakPtPub]'s [wpt_own_release] / [wpt_pub_acquire], which are these
        at [R := a ↦w{dq} v].
      - [wobj_to_hold] / [wobj_of_hold] convert against [vwp_hold], so a
        leaf's frame can be carried objectively by its caller and handed to
        the unmodified leaf — again for arbitrary [R].

    AND [↦o] IS AN INSTANCE.  [wpt_own_wobj] below: [a ↦o{dq} v ⊣⊢ wobj (a
    ↦w{dq} v)].  So [WeakPtOwn] is not a separate construct after all — it
    is this modality at a single byte, and everything in [WeakPtPub]
    generalises.

    WHAT IS STILL NOT FREE.  [wobj] does NOT commute with [∀] in the useful
    direction ([∀ x, wobj (Φ x) ⊬ wobj (∀ x, Φ x)]: each [x] may hold at a
    different view, and there is no join over an infinite family).  Finite
    conjunctions and [big_sepM] over a finite map are fine, which covers
    what data-structure predicates actually use.  It also does not commute
    with [-∗] or [→] in either direction, for the same reason it does not
    for [monPred_at]. *)
From Stdlib Require Import ZArith Bool Lia.
From stdpp Require Import gmap.
From stdpp Require Import bitvector.definitions.
From iris.algebra Require Import auth numbers functions dfrac.
From iris.base_logic.lib Require Import iprop own ghost_map mono_nat.
From iris.bi Require Import monpred.
From iris.proofmode Require Import proofmode monpred.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import RiscvLang RiscvPtsto.
Require Import WeakMem WeakInterp WeakLang WeakView WeakVProp WeakGhost.
Require Import WeakViewMono WeakPtOwn WeakPtPub.

Section obj.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Context `{CID : CpuId}.
  Local Notation γv := (weak_view_name cpu_id).

  (* ------------------------------------------------------------------ *)
  (** ** 1. [view_lb] — a floor on the hart's WHOLE view.

      [WeakPtOwn.wflr_lb a t] is "[t] is below my floor at byte [a]".  A
      view is a floor at every byte at once, so its lower bound is the
      pointwise one.  Stating it as a [∀] rather than as a scalar plus a
      finite map is deliberate: [⊑] on views is itself defined through
      [flr], so this way [view_lb_valid] is literally [wflr_lb_valid] at
      every [a] and no arithmetic is repeated. *)
  Definition view_lb (V : view) : iProp Σ :=
    (∀ a : Z, wflr_lb a (flr V a))%I.

  Global Instance view_lb_persistent V : Persistent (view_lb V).
  Proof. apply _. Qed.
  Global Instance view_lb_timeless V : Timeless (view_lb V).
  Proof. apply _. Qed.

  Lemma view_lb_valid ws V :
    ws_auth γv ws -∗ view_lb V -∗ ⌜V ⊑ ws_view ws⌝.
  Proof.
    iIntros "Hauth #Hlb". iIntros (a).
    by iApply (wflr_lb_valid with "Hauth Hlb").
  Qed.

  Lemma view_lb_get ws V :
    V ⊑ ws_view ws -> ws_auth γv ws -∗ view_lb V.
  Proof.
    iIntros (Hle) "Hauth". iIntros (a).
    by iApply (wflr_lb_get with "Hauth").
  Qed.

  (** The bottom floor is free — see the third disjunct of [wflr_lb]. *)
  Lemma view_lb_bot : ⊢ view_lb view_bot.
  Proof. iIntros (a). rewrite flr_bot. iApply wflr_lb_0. Qed.

  Lemma view_lb_mono V V' : V' ⊑ V -> view_lb V -∗ view_lb V'.
  Proof.
    iIntros (Hle) "#H". iIntros (a).
    iApply (wflr_lb_le with "H"). apply Hle.
  Qed.

  (** THE JOIN, which is what makes [wobj_sep] work in the hard direction:
      two objectively-held resources are held at two different views, and
      the pair is held at their join. *)
  Lemma view_lb_join V1 V2 :
    view_lb V1 -∗ view_lb V2 -∗ view_lb (V1 ⊔ V2).
  Proof.
    iIntros "#H1 #H2". iIntros (a). rewrite flr_join.
    iApply (wflr_lb_join with "H1 H2").
  Qed.

  (** The acquirer's side of the boundary: [WeakPtPub.vrNew_lb T] IS the
      floor at the scalar view [view_scl T].  (Only this direction holds —
      see [WeakPtPub]'s WRINKLE note: [⊑] against a scalar view forgets the
      scalar, so the converse is not derivable.) *)
  Lemma view_lb_scl T : vrNew_lb T -∗ view_lb (view_scl T).
  Proof.
    iIntros "#H". iIntros (a). rewrite flr_scl_eq. iRight. by iLeft.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 2. The modality *)

  Definition wobj (R : vProp Σ) : iProp Σ :=
    (∃ V : view, view_lb V ∗ monPred_at R V)%I.

  Global Instance wobj_ne : NonExpansive wobj.
  Proof. solve_proper. Qed.
  Global Instance wobj_proper : Proper ((≡) ==> (≡)) wobj.
  Proof. solve_proper. Qed.
  Global Instance wobj_mono' : Proper ((⊢) ==> (⊢)) wobj.
  Proof.
    intros R R' HR. rewrite /wobj.
    apply bi.exist_mono => V. apply bi.sep_mono_r.
    by apply monPred_at_mono.
  Qed.

  (** The one-line payoff: the result is an [iProp], so its embedding is
      objective with no proof obligation, for ANY [R]. *)
  Global Instance wobj_objective R : Objective (⎡ wobj R ⎤ : vProp Σ).
  Proof. apply _. Qed.

  Global Instance wobj_persistent R `{!∀ V, Persistent (monPred_at R V)} :
    Persistent (wobj R).
  Proof. apply _. Qed.
  Global Instance wobj_timeless R `{!∀ V, Timeless (monPred_at R V)} :
    Timeless (wobj R).
  Proof. apply _. Qed.

  Lemma wobj_mono R R' : (R ⊢ R') -> wobj R -∗ wobj R'.
  Proof. intros HR. apply bi.entails_wand, wobj_mono', HR. Qed.

  Lemma wobj_intro ws R : ws_auth γv ws -∗ monPred_at R (ws_view ws) -∗ wobj R.
  Proof.
    iIntros "Hauth HR". iExists (ws_view ws). iFrame "HR".
    by iApply (view_lb_get with "Hauth").
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 3. THE STRUCTURAL LAWS.

      These are what make the modality worth having: a composite predicate
      is transported across the boundary by these alone, so no definition
      anywhere below has to be restated, reparameterised, or reproved. *)

  Lemma wobj_sep R R' : wobj (R ∗ R') ⊣⊢ wobj R ∗ wobj R'.
  Proof.
    iSplit.
    - iIntros "[%V [#Hlb HR]]". rewrite monPred_at_sep.
      iDestruct "HR" as "[HR HR']".
      iSplitL "HR"; iExists V; by iFrame.
    - iIntros "[[%V1 [#H1 HR]] [%V2 [#H2 HR']]]".
      iExists (V1 ⊔ V2). iSplitR.
      { iApply (view_lb_join with "H1 H2"). }
      rewrite monPred_at_sep. iSplitL "HR".
      + iApply (monPred_mono with "HR"). apply view_join_l.
      + iApply (monPred_mono with "HR'"). apply view_join_r.
  Qed.

  Lemma wobj_exist {A : Type} (Φ : A -> vProp Σ) :
    wobj (∃ x, Φ x) ⊣⊢ ∃ x, wobj (Φ x).
  Proof.
    iSplit.
    - iIntros "[%V [#Hlb HR]]". rewrite monPred_at_exist.
      iDestruct "HR" as (x) "HR". iExists x, V. by iFrame.
    - iIntros "[%x [%V [#Hlb HR]]]". iExists V. iFrame "Hlb".
      rewrite monPred_at_exist. by iExists x.
  Qed.

  Lemma wobj_pure (φ : Prop) : wobj ⌜φ⌝ ⊣⊢ ⌜φ⌝.
  Proof.
    iSplit.
    - iIntros "[%V [_ %H]]". done.
    - iIntros "%H". iExists view_bot. iSplitR; [iApply view_lb_bot|done].
  Qed.

  Lemma wobj_or R R' : wobj (R ∨ R') ⊣⊢ wobj R ∨ wobj R'.
  Proof.
    iSplit.
    - iIntros "[%V [#Hlb HR]]". rewrite monPred_at_or.
      iDestruct "HR" as "[HR|HR]"; [iLeft|iRight]; iExists V; by iFrame.
    - iIntros "[[%V [#Hlb HR]]|[%V [#Hlb HR]]]"; iExists V; iFrame "Hlb";
        rewrite monPred_at_or; [by iLeft|by iRight].
  Qed.

  Lemma wobj_embed (P : iProp Σ) : wobj ⎡ P ⎤ ⊣⊢ P.
  Proof.
    iSplit.
    - iIntros "[%V [_ HP]]". by rewrite monPred_at_embed.
    - iIntros "HP". iExists view_bot. iSplitR; [iApply view_lb_bot|].
      by rewrite monPred_at_embed.
  Qed.

  Lemma wobj_emp : wobj emp ⊣⊢ emp.
  Proof.
    iSplit.
    - by iIntros "[%V [_ H]]".
    - iIntros "H". iExists view_bot. iSplitR; [iApply view_lb_bot|done].
  Qed.

  (** [▷] passes straight out of the modality.  It does NOT pass straight
      back in: [▷ view_lb V] only gives [◇ view_lb V] (the floor is
      timeless, not later-free), so the converse carries an [◇] — which is
      free wherever an invariant is being opened, and is why this is stated
      as two lemmas rather than a [⊣⊢]. *)
  Lemma wobj_later_1 R : wobj (▷ R) ⊢ ▷ wobj R.
  Proof.
    iIntros "[%V [#Hlb HR]]". rewrite monPred_at_later.
    iNext. iExists V. by iFrame.
  Qed.

  Lemma wobj_later_2 R : ▷ wobj R ⊢ ◇ wobj (▷ R).
  Proof.
    iIntros "H". rewrite /wobj bi.later_exist.
    iDestruct "H" as (V) "H". rewrite bi.later_sep.
    iDestruct "H" as "[Hlb HR]".
    iDestruct (timeless with "Hlb") as ">#Hlb". iModIntro.
    iExists V. iFrame "Hlb". by rewrite monPred_at_later.
  Qed.

  (** THE ONE A DATA-STRUCTURE PREDICATE ACTUALLY NEEDS.  A table, a list,
      a region: all of them are [big_sepM]/[big_sepL], i.e. iterated [∗],
      and this is [wobj_sep] iterated. *)
  Lemma wobj_big_sepM {A : Type} (m : gmap Z A) (Φ : Z -> A -> vProp Σ) :
    wobj ([∗ map] k ↦ x ∈ m, Φ k x) ⊣⊢ [∗ map] k ↦ x ∈ m, wobj (Φ k x).
  Proof.
    induction m as [|k x m Hnew IH] using map_ind.
    { rewrite !big_sepM_empty. apply wobj_emp. }
    rewrite !big_sepM_insert // -IH. apply wobj_sep.
  Qed.

  Lemma wobj_big_sepL {A : Type} (l : list A) (Φ : nat -> A -> vProp Σ) :
    wobj ([∗ list] k ↦ x ∈ l, Φ k x) ⊣⊢ [∗ list] k ↦ x ∈ l, wobj (Φ k x).
  Proof.
    revert Φ. induction l as [|x l IH]; intros Φ.
    { rewrite !big_sepL_nil. apply wobj_emp. }
    rewrite !big_sepL_cons -IH. apply wobj_sep.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 4. THE BOUNDARY, for an arbitrary predicate.

      [WeakPtPub]'s two conversions, generalised off the single byte.  Note
      what did NOT change: the side conditions.  The releaser must have its
      whole view below the timestamp its store takes; the acquirer must
      have gained that timestamp as a scalar.  Those are facts about the
      lock protocol, and they are still paid exactly once per critical
      section — but now they are paid for the WHOLE payload at once
      instead of once per byte. *)
  Lemma wobj_release ws T R :
    (∀ a, (flr (ws_view ws) a ≤ T)%nat) ->
    ws_auth γv ws -∗ wobj R -∗ ws_auth γv ws ∗ monPred_at R (view_scl T).
  Proof.
    iIntros (HT) "Hauth [%V [#Hlb HR]]".
    iDestruct (view_lb_valid with "Hauth Hlb") as %Hle.
    iFrame "Hauth". iApply (monPred_mono with "HR").
    intros a. rewrite flr_scl_eq. etrans; [apply Hle|apply HT].
  Qed.

  Lemma wobj_acquire T R :
    vrNew_lb T -∗ monPred_at R (view_scl T) -∗ wobj R.
  Proof.
    iIntros "#Hlb HR". iExists (view_scl T). iFrame "HR".
    by iApply view_lb_scl.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 5. THE LEAF BRIDGE.

      A leaf takes its frame as [vwp_hold F ws] — indexed by the very
      [wstate] the caller is trying not to name.  These two convert, for
      arbitrary [F], so a caller can hold [wobj F] and still call the
      UNMODIFIED leaf.  This is what lets a leaf wrapper carry a real frame
      instead of discharging it at [⌜True⌝]. *)
  Lemma wobj_to_hold ws R :
    ws_auth γv ws -∗ wobj R -∗ ws_auth γv ws ∗ vwp_hold R ws.
  Proof.
    iIntros "Hauth [%V [#Hlb HR]]".
    iDestruct (view_lb_valid with "Hauth Hlb") as %Hle.
    iFrame "Hauth". rewrite /vwp_hold. by iApply (monPred_mono with "HR").
  Qed.

  Lemma wobj_of_hold ws R :
    ws_auth γv ws -∗ vwp_hold R ws -∗ ws_auth γv ws ∗ wobj R.
  Proof.
    iIntros "Hauth HR". rewrite /vwp_hold.
    iDestruct (view_lb_get ws (ws_view ws) with "Hauth") as "#Hlb";
      [reflexivity|].
    iFrame "Hauth". iExists (ws_view ws). by iFrame "HR".
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 6. [↦o] IS AN INSTANCE.

      [WeakPtOwn]'s objective points-to was built by hand: an element plus
      a per-byte floor.  It is [wobj] of the ordinary subjective points-to,
      so it was never a separate construct — which also means every
      structural law above applies to a predicate built out of [↦o]s. *)
  Lemma wpt_own_wobj a dq v : wobj (a ↦w{dq} v) ⊣⊢ wpt_own a dq v.
  Proof.
    iSplit.
    - iIntros "[%V [#Hlb HR]]". rewrite wpt_view_at.
      iDestruct "HR" as (t) "[He %Ht]". iExists t. iFrame "He".
      iApply (wflr_lb_le with "Hlb"). exact Ht.
    - iIntros "[%t [He #Hlb]]". iExists (view_byte a t).
      iSplitR.
      { iIntros (a'). destruct (decide (a' = a)) as [->|Hne].
        - by rewrite flr_byte_eq.
        - rewrite flr_byte_ne //. iApply wflr_lb_0. }
      rewrite wpt_view_at. iExists t. iFrame "He". iPureIntro.
      rewrite flr_byte_eq. lia.
  Qed.

  (** ... and so is [wpt_pub], on the other side of the boundary. *)
  Lemma wpt_pub_frozen_obj T a dq v :
    monPred_at (a ↦w{dq} v) (view_scl T) ⊣⊢ wpt_pub T a dq v.
  Proof. apply wpt_pub_frozen. Qed.

End obj.

(* ====================================================================== *)
(** ** 7. THE ROUND TRIP, for an arbitrary payload.

    The statement a lock's client-facing spec wants: the payload goes in
    objectively at one hart and comes out objectively at another, with no
    view crossing the boundary and no hart named inside it.

    [WeakPtPub.wpt_region_handoff] is this at [R := ] a region of
    points-to; here [R] is ANYTHING — a table, a list, a whole
    invariant's worth of nested definitions — and neither the statement
    nor the proof grows.  That is the entire point of the modality.

    Two harts are named, so this needs its own section, outside the
    ambient-[CpuId] one. *)

Section handoff.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Lemma wobj_handoff (CA CB : CpuId) (wA wB : wstate) (T : nat) R :
    (∀ a, (flr (ws_view wA) a ≤ T)%nat) ->
    (T ≤ w_vrNew wB)%nat ->
    ws_auth (weak_view_name CA) wA -∗ ws_auth (weak_view_name CB) wB -∗
    @wobj _ _ CA R -∗
    ws_auth (weak_view_name CA) wA ∗ ws_auth (weak_view_name CB) wB ∗
    @wobj _ _ CB R.
  Proof.
    iIntros (HT Hacq) "HA HB HR".
    iDestruct (@wobj_release _ _ CA _ T with "HA HR") as "[HA HR]";
      [exact HT|].
    iDestruct (@vrNew_lb_get _ _ CB _ _ Hacq with "HB") as "#Hlb".
    iFrame "HA HB". by iApply (@wobj_acquire _ _ CB with "Hlb HR").
  Qed.

End handoff.
