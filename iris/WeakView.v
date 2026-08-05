(** * WeakView.v — the view index and the [vProp] core (M2a)

    The surface layer of the design doc's Decision 5: the [biIndex] of views,
    [vProp := monPred view (iProp)], the seen-assertion [⊒V], the view-at
    modality [P @@ V], and THE SPLIT AXIOM

        [P ⊢ ∃ V, ⊒V ∗ P @@ V]        (VA-intro)
        [⊒V ∗ P @@ V ⊢ P]             (VA-elim)

    which is the soundness linchpin the whole weak-memory architecture turns
    on: an invariant may hold only OBJECTIVE assertions, and subjective
    content crosses a synchronisation edge by being frozen at a view
    ([P @@ V], objective) and thawed by the acquirer's [⊒V].

    DEPENDENCY DISCIPLINE.  This file is Sail-free and tree-free: stdpp plus
    [iris.bi.monpred] plus the proofmode.  [Z] appears only as the key type of
    the per-byte component (design doc, Decision 2: the weak-memory maps are
    keyed by [Z] = [uint] of the physical address, converted once at the
    [WeakInterp] seam), so nothing here can trip the [gmap Arch.pa _]
    Countable trap recorded in the durable notes.

    WHAT IS INHERITED FROM [iris/bi/monpred.v] AND WHAT IS ADDED.  Almost
    everything is inherited; this file adds only what the INDEX is about.

      inherited: the whole BI structure of [vProp] (incl. [BiAffine], [BiBUpd],
        [BiFUpd], [BiEmbed iProp], later-contractivity) via [monPredI]; [⊒V]'s
        persistence/absorbingness/anti-monotonicity ([monPred_in_persistent],
        [monPred_in_mono]); the [Objective] class and its instances for the
        embedding, pure, emp, ∧/∨/→/∗/-∗/∀/∃, □/<pers>/<affine>/<absorb>,
        [<obj>]/[<subj>], [|==>] and [|={E1,E2}=>]; and the proofmode support
        ([iris.proofmode.monpred]).
      added here: the [view] record, its floor/order/join lattice, the
        [biIndex] and [BiIndexBottom] instances, the [P @@ V] modality with
        its objectivity and monotonicity, and the split axiom.

    WHY [P @@ V] IS AN EMBEDDING OF [monPred_at] AND NOT [<obj>].  [<obj> P]
    is "P at EVERY index", which is far too strong to freeze a resource at one
    view.  The right object is the CONSTANT monPred at [P]'s value at [V] —
    [MonPred (λ _, P V) _] — which is literally [⎡ P V ⎤], i.e. the embedding
    [monPred_embed] applied to the projection [monPred_at].  So it is
    [Objective] by [embed_objective], with no new proof obligation, and every
    embedding lemma applies to it.  Iris does NOT provide this composition
    under a name; [view_at] below is it. *)
From stdpp Require Import gmap.
From iris.bi Require Import monpred.
From iris.base_logic.lib Require Import iprop.
From iris.proofmode Require Import proofmode monpred.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The view index

    DECIDED at M1 (design doc, Decision 5): a view is a SCALAR floor joined
    with a SPARSE per-byte map.  Why the pair: a hart's semantic read floor
    for byte [a] is [w_vrNew ⊔ coh(a)] — a scalar joined with a finite map,
    which a bare [gmap] cannot represent (its support would be infinite) and
    a bare scalar cannot either (a points-to needs a per-byte floor).  A
    points-to carries a singleton-map view; a release deposits a pure SCALAR
    view, because a timestamp below the log's length bounds every component
    of the releaser's floor.

    The order is POINTWISE ON THE FLOOR, hence a PREORDER and not a partial
    order — [View 1 ∅] and [View 1 {[a := 0]}] are equivalent but not equal.
    We deliberately do NOT quotient: [monPred] only ever needs a preorder
    ([biIndex] asks for exactly that), and a setoid index would make every
    index-level rewrite a proof obligation. *)

Record view := View { v_scl : nat; v_map : gmap Z nat }.
Add Printing Constructor view.

Global Instance view_eq_dec : EqDecision view.
Proof. solve_decision. Defined.

(** The FLOOR of view [V] at byte [a]: the scalar, joined with whatever the
    sparse map says about [a] (nothing = 0). *)
Definition flr (V : view) (a : Z) : nat :=
  Nat.max (v_scl V) (default 0%nat (v_map V !! a)).

Lemma flr_scl V a : (v_scl V ≤ flr V a)%nat.
Proof. rewrite /flr. lia. Qed.

Lemma flr_lookup V a n : v_map V !! a = Some n → (n ≤ flr V a)%nat.
Proof. rewrite /flr => ->. simpl. lia. Qed.

(** The three views this development actually builds. *)
Definition view_bot : view := View 0 ∅.
Definition view_scl (n : nat) : view := View n ∅.
Definition view_byte (a : Z) (t : nat) : view := View 0 {[a := t]}.

Lemma flr_bot a : flr view_bot a = 0%nat.
Proof. done. Qed.

Lemma flr_scl_eq n a : flr (view_scl n) a = n.
Proof. rewrite /flr /view_scl /= lookup_empty /=. lia. Qed.

Lemma flr_byte_eq a t : flr (view_byte a t) a = t.
Proof. rewrite /flr /view_byte /= lookup_singleton /=. lia. Qed.

Lemma flr_byte_ne a t a' : a' ≠ a → flr (view_byte a t) a' = 0%nat.
Proof. intros ?. rewrite /flr /view_byte /= lookup_singleton_ne //. Qed.

(* ---------------------------------------------------------------- *)
(** *** The lattice *)

Global Instance view_sqsubseteq : SqSubsetEq view :=
  λ V1 V2, ∀ a, (flr V1 a ≤ flr V2 a)%nat.

Lemma view_sqsubseteq_spec V1 V2 : V1 ⊑ V2 ↔ ∀ a, (flr V1 a ≤ flr V2 a)%nat.
Proof. done. Qed.

Global Instance view_preorder : PreOrder (⊑@{view}).
Proof.
  split.
  - intros V a. lia.
  - intros V1 V2 V3 H12 H23 a. etrans; [apply H12|apply H23].
Qed.

Global Instance view_inhabited : Inhabited view := populate view_bot.

Global Instance view_join_inst : Join view := λ V1 V2,
  View (Nat.max (v_scl V1) (v_scl V2))
       (union_with (λ n1 n2, Some (Nat.max n1 n2)) (v_map V1) (v_map V2)).

(** THE JOIN LEMMA: the floor of a join is the max of the floors, pointwise.
    Everything else about the lattice follows from it. *)
Lemma flr_join V1 V2 a : flr (V1 ⊔ V2) a = Nat.max (flr V1 a) (flr V2 a).
Proof.
  rewrite /flr /join /view_join_inst /= lookup_union_with.
  destruct (v_map V1 !! a) as [n1|], (v_map V2 !! a) as [n2|]; simpl; lia.
Qed.

Lemma view_join_l (V1 V2 : view) : V1 ⊑ V1 ⊔ V2.
Proof. intros a. rewrite flr_join. lia. Qed.

Lemma view_join_r (V1 V2 : view) : V2 ⊑ V1 ⊔ V2.
Proof. intros a. rewrite flr_join. lia. Qed.

Lemma view_join_lub (V1 V2 V : view) : V1 ⊑ V → V2 ⊑ V → V1 ⊔ V2 ⊑ V.
Proof. intros H1 H2 a. rewrite flr_join. specialize (H1 a). specialize (H2 a). lia. Qed.

(** ... hence the join IS the least upper bound, in one iff — the form the
    [⊒V1 ∗ ⊒V2 ⊣⊢ ⊒(V1 ⊔ V2)] law consumes. *)
Lemma view_join_le (V1 V2 V : view) : V1 ⊔ V2 ⊑ V ↔ V1 ⊑ V ∧ V2 ⊑ V.
Proof.
  split.
  - intros H. split; (etrans; [|exact H]); [apply view_join_l|apply view_join_r].
  - intros [H1 H2]. by apply view_join_lub.
Qed.

Global Instance view_join_mono : Proper ((⊑) ==> (⊑) ==> (⊑)) (@join view _).
Proof.
  intros V1 V1' H1 V2 V2' H2 a. rewrite !flr_join.
  specialize (H1 a). specialize (H2 a). lia.
Qed.

Lemma view_bot_le (V : view) : view_bot ⊑ V.
Proof. intros a. rewrite flr_bot. lia. Qed.

(** A singleton-byte view is below [V] exactly when [V]'s floor covers the
    timestamp — the form every points-to law is stated in. *)
Lemma view_byte_le a t (V : view) : view_byte a t ⊑ V ↔ (t ≤ flr V a)%nat.
Proof.
  split.
  - intros H. rewrite -(flr_byte_eq a t). apply H.
  - intros Ht a'. destruct (decide (a' = a)) as [->|Hne].
    + by rewrite flr_byte_eq.
    + rewrite flr_byte_ne //. lia.
Qed.

(** A byte view AT TIMESTAMP 0 is the bottom view: the era-initial image is
    visible to every agent, whatever it has observed.  This is what makes an
    era-image points-to receipt-free, hence OBJECTIVE (see [WeakVProp]'s
    [wpt_img]). *)
Lemma view_byte_0 a : view_byte a 0%nat ⊑ view_bot.
Proof.
  intros a'. rewrite flr_bot. destruct (decide (a' = a)) as [->|Hne].
  - rewrite flr_byte_eq. lia.
  - rewrite flr_byte_ne //.
Qed.

(** A scalar view is below [V] exactly when [V]'s SCALAR covers it: the
    scalar floor must be dominated at every byte, including the ones [V]'s
    map says nothing about. *)
Lemma view_scl_le n (V : view) : view_scl n ⊑ V ↔ ∀ a, (n ≤ flr V a)%nat.
Proof.
  split.
  - intros H a. rewrite -(flr_scl_eq n a). apply H.
  - intros H a. rewrite flr_scl_eq. apply H.
Qed.

(* ---------------------------------------------------------------- *)
(** *** The [biIndex] *)

Canonical Structure view_bi_index : biIndex :=
  BiIndex view view_inhabited view_sqsubseteq view_preorder.

Global Instance view_bi_index_bot : BiIndexBottom (I := view_bi_index) view_bot.
Proof. intros V. apply view_bot_le. Qed.

(* ====================================================================== *)
(** ** 2. [vProp] *)

Definition vProp (Σ : gFunctors) : Type := monPred view_bi_index (iPropI Σ).
Definition vPropO (Σ : gFunctors) : ofe := monPredO view_bi_index (iPropI Σ).
Definition vPropI (Σ : gFunctors) : bi := monPredI view_bi_index (iPropI Σ).

Bind Scope bi_scope with vProp.

(** [⊒V] — "I have observed [V]".  This is Iris's own [monPred_in], reused
    rather than hand-rolled: persistence, absorbingness and anti-monotonicity
    all come for free, and so does the proofmode's handling of it. *)
Notation "⊒ V" := (monPred_in V) (at level 20, right associativity) : bi_scope.

(** [P @@ V] — "P holds at view [V]", frozen: an OBJECTIVE assertion (see the
    header for why this, and not [<obj>]). *)
Definition view_at {Σ} (V : view) (P : vProp Σ) : vProp Σ :=
  ⎡ monPred_at P V ⎤%I.

Notation "P @@ V" := (view_at V P)
  (at level 20, right associativity, format "P  @@  V") : bi_scope.

Section view_laws.
  Context {Σ : gFunctors}.
  Implicit Types P Q : vProp Σ.
  Implicit Types V : view.

  (* ---------------------------------------------------------------- *)
  (** *** 2a. the seen assertion *)

  Global Instance seen_persistent V : Persistent (⊒V : vProp Σ).
  Proof. apply monPred_in_persistent. Qed.
  Global Instance seen_absorbing V : Absorbing (⊒V : vProp Σ).
  Proof. apply monPred_in_absorbing. Qed.

  Lemma seen_at V V' : (⊒V : vProp Σ) V' ⊣⊢ ⌜V ⊑ V'⌝.
  Proof. apply monPred_at_in. Qed.

  (** ANTI-MONOTONE: seeing more implies seeing less. *)
  Lemma seen_mono V1 V2 : V1 ⊑ V2 → (⊒V2 : vProp Σ) ⊢ ⊒V1.
  Proof. intros H. by apply monPred_in_mono. Qed.

  (** The bottom view is free. *)
  Lemma seen_bot : ⊢ (⊒view_bot : vProp Σ).
  Proof.
    constructor => V. rewrite monPred_at_emp seen_at.
    apply bi.pure_intro, view_bot_le.
  Qed.

  Lemma seen_bot_True : (⊒view_bot : vProp Σ) ⊣⊢ True.
  Proof.
    iSplit; [by iIntros "_"|iIntros "_"]. iApply seen_bot.
  Qed.

  (** JOIN: two observations are one observation of the join.  This is
      exactly [view_join_le], transported. *)
  Lemma seen_join V1 V2 : (⊒V1 ∗ ⊒V2 : vProp Σ) ⊣⊢ ⊒(V1 ⊔ V2).
  Proof.
    constructor => V. rewrite monPred_at_sep !seen_at.
    iSplit.
    - iIntros "[%H1 %H2]". iPureIntro. by apply view_join_lub.
    - iIntros "%H". apply view_join_le in H as [H1 H2]. by iSplit.
  Qed.

  (** The era-image receipt is free. *)
  Lemma seen_byte_0 a : ⊢ (⊒(view_byte a 0%nat) : vProp Σ).
  Proof.
    iApply (seen_mono _ _ (view_byte_0 a)). iApply seen_bot.
  Qed.

  Lemma seen_join_l V1 V2 : (⊒(V1 ⊔ V2) : vProp Σ) ⊢ ⊒V1.
  Proof. apply seen_mono, view_join_l. Qed.
  Lemma seen_join_r V1 V2 : (⊒(V1 ⊔ V2) : vProp Σ) ⊢ ⊒V2.
  Proof. apply seen_mono, view_join_r. Qed.

  (** The index is REFLEXIVE, so at index [V] the assertion [⊒V] is free.
      This is what lets a leaf rule at the hart's index produce its own
      seen-assertion out of nothing. *)
  Lemma seen_at_self V : ⊢ (⊒V : vProp Σ) V.
  Proof. rewrite seen_at. iPureIntro. reflexivity. Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 2b. the view-at modality *)

  Lemma view_at_unfold V P : (P @@ V)%I = ⎡ monPred_at P V ⎤%I.
  Proof. done. Qed.

  Lemma view_at_at V V' P : monPred_at (P @@ V)%I V' ⊣⊢ monPred_at P V.
  Proof. apply monPred_at_embed. Qed.

  Global Instance view_at_ne V : NonExpansive (view_at (Σ := Σ) V).
  Proof. rewrite /view_at. solve_proper. Qed.
  Global Instance view_at_proper V : Proper ((≡) ==> (≡)) (view_at (Σ := Σ) V).
  Proof. apply (ne_proper _). Qed.
  Global Instance view_at_mono' V : Proper ((⊢) ==> (⊢)) (view_at (Σ := Σ) V).
  Proof. intros P Q HPQ. rewrite /view_at. f_equiv. by apply HPQ. Qed.
  Global Instance view_at_flip_mono' V :
    Proper (flip (⊢) ==> flip (⊢)) (view_at (Σ := Σ) V).
  Proof. intros P Q HPQ. by apply view_at_mono'. Qed.

  (** OBJECTIVE BY CONSTRUCTION — the whole point of the modality. *)
  Global Instance view_at_objective V P : Objective (P @@ V).
  Proof. rewrite /view_at. apply _. Qed.

  Global Instance view_at_persistent V P :
    Persistent P → Persistent (P @@ V).
  Proof. intros ?. rewrite /view_at. apply _. Qed.
  Global Instance view_at_absorbing V P : Absorbing P → Absorbing (P @@ V).
  Proof. intros ?. rewrite /view_at. apply _. Qed.
  Global Instance view_at_affine V P : Affine P → Affine (P @@ V).
  Proof. intros ?. rewrite /view_at. apply _. Qed.
  Global Instance view_at_timeless V P : Timeless P → Timeless (P @@ V).
  Proof. intros ?. rewrite /view_at. apply _. Qed.

  (** MONOTONE in the view — every [vProp] is monotone, by construction. *)
  Lemma view_at_view_mono V1 V2 P : V1 ⊑ V2 → P @@ V1 ⊢ P @@ V2.
  Proof. intros H. rewrite /view_at. f_equiv. by apply monPred_mono. Qed.

  (** The structural laws.  [∗] and [∃] commute with [@@] because
      [monPred_at] and [⎡·⎤] both do. *)
  Lemma view_at_sep V P Q : (P ∗ Q) @@ V ⊣⊢ (P @@ V) ∗ (Q @@ V).
  Proof. rewrite /view_at monPred_at_sep embed_sep //. Qed.
  Lemma view_at_and V P Q : (P ∧ Q) @@ V ⊣⊢ (P @@ V) ∧ (Q @@ V).
  Proof. rewrite /view_at monPred_at_and embed_and //. Qed.
  Lemma view_at_or V P Q : (P ∨ Q) @@ V ⊣⊢ (P @@ V) ∨ (Q @@ V).
  Proof. rewrite /view_at monPred_at_or embed_or //. Qed.
  Lemma view_at_exist {A} V (Φ : A → vProp Σ) :
    (∃ x, Φ x) @@ V ⊣⊢ ∃ x, (Φ x) @@ V.
  Proof. rewrite /view_at monPred_at_exist embed_exist //. Qed.
  Lemma view_at_forall {A} V (Φ : A → vProp Σ) :
    (∀ x, Φ x) @@ V ⊣⊢ ∀ x, (Φ x) @@ V.
  Proof. rewrite /view_at monPred_at_forall embed_forall //. Qed.
  Lemma view_at_pure V (φ : Prop) : (⌜φ⌝ : vProp Σ) @@ V ⊣⊢ ⌜φ⌝.
  Proof. rewrite /view_at monPred_at_pure embed_pure //. Qed.
  Lemma view_at_embed V (P : iProp Σ) : (⎡P⎤ : vProp Σ) @@ V ⊣⊢ ⎡P⎤.
  Proof. rewrite /view_at monPred_at_embed //. Qed.
  Lemma view_at_bupd V P : (|==> P) @@ V ⊣⊢ |==> (P @@ V).
  Proof. rewrite /view_at monPred_at_bupd embed_bupd //. Qed.

  (** An OBJECTIVE assertion is its own view-at, at every view: freezing it
      is the identity.  This is what makes the whole "registers / devices /
      ghost state / pure facts / [↦□] ride along unchanged" claim of the
      design doc a one-line corollary at every such assertion. *)
  Lemma view_at_objective_id V P `{!Objective P} : P @@ V ⊣⊢ P.
  Proof.
    rewrite /view_at. apply (anti_symm _).
    - constructor => V'. rewrite monPred_at_embed. apply objective_at, _.
    - constructor => V'. rewrite monPred_at_embed. apply objective_at, _.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** 2c. THE SPLIT AXIOM

      The soundness linchpin.  Read together: any assertion is an objective
      payload plus a receipt for the view it was taken at, and the receipt is
      what a synchronisation edge transports.

      Both directions are Iris's [monPred_in_intro] / [monPred_in_elim] with
      the ∧ turned into a ∗ — legitimate because [⊒V] is persistent and
      [vProp] is affine (both inherited: [monPred_in_persistent],
      [monPred_bi_affine] over [iProp]). *)

  Lemma view_at_intro P : P ⊢ ∃ V, ⊒V ∗ P @@ V.
  Proof.
    constructor => V. rewrite monPred_at_exist.
    iIntros "HP". iExists V.
    rewrite monPred_at_sep seen_at view_at_at. iFrame "HP".
    iPureIntro. reflexivity.
  Qed.

  (** VA-ELIM is where the MONOTONICITY of every [vProp] is spent: the
      receipt [⊒V] says the ambient index is above [V], and [P]'s own
      [monPred_mono] carries [P]'s value at [V] up to it. *)
  Lemma view_at_elim V P : ⊒V ∗ P @@ V ⊢ P.
  Proof.
    constructor => V'. rewrite monPred_at_sep seen_at view_at_at.
    iIntros "[%HV HP]". iApply (monPred_mono P V V' HV with "HP").
  Qed.

  Lemma view_at_split P : P ⊣⊢ ∃ V, ⊒V ∗ P @@ V.
  Proof.
    apply (anti_symm _); [apply view_at_intro|].
    apply bi.exist_elim => V. apply view_at_elim.
  Qed.

  (** The two forms a leaf rule uses directly. *)
  Lemma view_at_intro_at V P : monPred_at P V ⊢ monPred_at (⊒V ∗ P @@ V) V.
  Proof.
    rewrite monPred_at_sep seen_at view_at_at.
    iIntros "H". iSplit; [iPureIntro; reflexivity|iExact "H"].
  Qed.

  Lemma view_at_elim_at V V' P : V ⊑ V' → monPred_at P V ⊢ monPred_at P V'.
  Proof. intros H. by apply monPred_mono. Qed.

End view_laws.

(* ====================================================================== *)
(** ** 3. Objectivity: what is inherited, what this file adds

    INHERITED from [monpred.v] and covering, wholesale, everything the design
    doc lists as "objective by construction":

      [embed_objective]      — ⎡P⎤ for ANY [iProp] P.  This ONE instance is
                               what makes every register/CSR assertion, every
                               device-fabric assertion, all ghost state and
                               every base-layer resource objective: they are
                               all [iProp]s embedded into [vProp].
      [pure_objective]       — ⌜φ⌝
      [emp_objective]
      [and_/or_/impl_/sep_/wand_/forall_/exists_objective]
      [persistently_/affinely_/absorbingly_/intuitionistically_objective]
      [objectively_/subjectively_objective]
      [bupd_objective], [fupd_objective]

    ADDED here: [view_at_objective] (§2b) — and nothing else is needed.  In
    particular there is no "later" instance to add ([later_objective] is in
    monpred.v) and no big-op instance ([big_sepL]/[big_sepM] over objective
    bodies are [forall]/[sep] chains, which the instances above cover). *)

Section objective_derived.
  Context {Σ : gFunctors}.

  (** An objective assertion needs no receipt: the split axiom degenerates.
      This IS the design doc's headline claim — "objective by construction ⇒
      unchanged in meaning and freely shareable" — and [embed_objective] makes
      its premise hold for EVERY embedded [iProp], i.e. for the registers, the
      devices, all ghost state, all pure facts and the whole base layer at
      once.  ([view_at_embed] above is the [⎡·⎤] instance, proved directly.) *)
  Lemma objective_no_receipt (P : vProp Σ) `{!Objective P} V :
    P ⊣⊢ P @@ V.
  Proof. by rewrite view_at_objective_id. Qed.

  (** ... hence VA-elim needs no [⊒V] at an objective assertion. *)
  Lemma objective_view_at_elim (P : vProp Σ) `{!Objective P} V :
    P @@ V ⊢ P.
  Proof. by rewrite view_at_objective_id. Qed.

End objective_derived.

(* ====================================================================== *)
(** ** 4. Proofmode smoke test

    Kept in the file deliberately: it is the check that the [monPred]
    proofmode instances FIRE through [⊒], [@@] and [⎡·⎤] — [iIntros],
    [iSplit], [iModIntro], [iDestruct]-of-an-existential, [iFrame], and a
    [Persistent] hypothesis all at once.  If a future change to the index or
    to the modality breaks the instance resolution, this fails here rather
    than deep inside a leaf proof. *)

Section smoke.
  Context {Σ : gFunctors}.
  Implicit Types P Q : vProp Σ.

  Example smoke_seen (V1 V2 : view) (R : iProp Σ) (P : vProp Σ) :
    ⊒V1 ∗ ⊒V2 ∗ ⎡R⎤ ∗ P @@ V1 ⊢
      |==> ⊒(V1 ⊔ V2) ∗ ⎡R⎤ ∗ <obj> (P @@ V1) ∗ ⊒V1.
  Proof.
    iIntros "(#H1 & #H2 & HR & HP)".
    iModIntro. iSplitR.
    { iApply seen_join. iSplit; [iExact "H1"|iExact "H2"]. }
    iFrame "HR H1". iApply objective_objectively. iExact "HP".
  Qed.

  Example smoke_split (P : vProp Σ) :
    P ⊢ ∃ V, ⊒V ∗ (P @@ V ∗ ⌜True⌝).
  Proof.
    iIntros "HP". iDestruct (view_at_intro with "HP") as (V) "[#HV HPV]".
    iExists V. iFrame "HV HPV".
  Qed.

  Example smoke_roundtrip (P : vProp Σ) :
    (∃ V, ⊒V ∗ P @@ V) ⊢ P.
  Proof.
    iIntros "H". iDestruct "H" as (V) "[#HV HP]".
    iApply (view_at_elim V). iFrame "HV HP".
  Qed.

End smoke.
