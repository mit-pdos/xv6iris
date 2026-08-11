(** * WeakViewMono.v — PROTOTYPE: the hart's weak state as MONOTONE ghost
      state, so it can be threaded as an OPAQUE token with persistent
      lower bounds.

    Design: [`claude-notes/design/weak-memory-sc-parity.md`] §2 — this file is
    obligation 1 of §5.  NOT wired into anything yet; [WeakGhost.hart_ws] is
    still the exact-valued [ghost_var] the tree uses.

    THE POINT.  [WeakGhost.hart_ws c ws := ghost_var (weak_ws_name c) (1/2) ws]
    is EXACT-valued, and a [ghost_var] can only be updated by naming both the
    old and the new value.  That is the sole reason every leaf reads [ws] in,
    [ws'] out, and carries [⌜ws_le ws ws'⌝] — even for an instruction that
    touches no data, since every instruction fetches its own text and the
    fetch is a view-raising weak read.  [ws_le] is pointwise [≤] on every
    field with no non-monotone component, so the state is a product of
    monotone pieces and the exactness is simply not needed above a leaf. *)
From stdpp Require Import gmap.
From iris.algebra Require Import auth numbers gmap functions updates local_updates.
From iris.base_logic.lib Require Import iprop own mono_nat.
From iris.proofmode Require Import proofmode.
Require Import WeakMem.

(* ====================================================================== *)
(** ** 1. The five scalar floors.

    [w_vrOld] / [w_vwOld] / [w_vrNew] / [w_vwNew] / [w_vRel] are plain [nat]s
    ordered by [≤], i.e. five [mono_nat]s.  This half is entirely standard
    and uses the same library the tree already uses in [VirtioProto] and
    [RiscvAdequacy]. *)

Class weakViewScalarG (Σ : gFunctors) := {
  wvs_vrOld : mono_natG Σ;
  wvs_vwOld : mono_natG Σ;
  wvs_vrNew : mono_natG Σ;
  wvs_vwNew : mono_natG Σ;
  wvs_vRel  : mono_natG Σ;
}.
Global Existing Instances wvs_vrOld wvs_vwOld wvs_vrNew wvs_vwNew wvs_vRel.

Record ws_names := WsNames {
  wsn_vrOld : gname; wsn_vwOld : gname;
  wsn_vrNew : gname; wsn_vwNew : gname; wsn_vRel : gname;
}.

Section scalars.
  Context `{!weakViewScalarG Σ}.

  (** The AUTHORITY on the five scalars, at an exact state — internal. *)
  Definition ws_scal_auth (γ : ws_names) (w : wstate) : iProp Σ :=
    (mono_nat_auth_own (wsn_vrOld γ) 1 (w_vrOld w) ∗
     mono_nat_auth_own (wsn_vwOld γ) 1 (w_vwOld w) ∗
     mono_nat_auth_own (wsn_vrNew γ) 1 (w_vrNew w) ∗
     mono_nat_auth_own (wsn_vwNew γ) 1 (w_vwNew w) ∗
     mono_nat_auth_own (wsn_vRel  γ) 1 (w_vRel  w))%I.

  (** The persistent LOWER BOUND — duplicable, and (the whole point) it
      survives every intervening step for free, with no [vwp_hold_mono]. *)
  Definition ws_scal_lb (γ : ws_names) (w : wstate) : iProp Σ :=
    (mono_nat_lb_own (wsn_vrOld γ) (w_vrOld w) ∗
     mono_nat_lb_own (wsn_vwOld γ) (w_vwOld w) ∗
     mono_nat_lb_own (wsn_vrNew γ) (w_vrNew w) ∗
     mono_nat_lb_own (wsn_vwNew γ) (w_vwNew w) ∗
     mono_nat_lb_own (wsn_vRel  γ) (w_vRel  w))%I.

  Global Instance ws_scal_lb_persistent γ w : Persistent (ws_scal_lb γ w).
  Proof. apply _. Qed.

  Lemma ws_scal_lb_get γ w : ws_scal_auth γ w -∗ ws_scal_lb γ w.
  Proof.
    iIntros "(H1 & H2 & H3 & H4 & H5)".
    iDestruct (mono_nat_lb_own_get with "H1") as "#L1".
    iDestruct (mono_nat_lb_own_get with "H2") as "#L2".
    iDestruct (mono_nat_lb_own_get with "H3") as "#L3".
    iDestruct (mono_nat_lb_own_get with "H4") as "#L4".
    iDestruct (mono_nat_lb_own_get with "H5") as "#L5".
    by iFrame "L1 L2 L3 L4 L5".
  Qed.

  (** THE UPDATE.  Note what it does NOT need: the caller does not name the
      old state.  Any [ws_le]-larger state is reachable, which is exactly the
      obligation a leaf can discharge internally. *)
  Lemma ws_scal_update γ w w' :
    ws_le w w' -> ws_scal_auth γ w ==∗ ws_scal_auth γ w'.
  Proof.
    intros (_ & H1 & H2 & H3 & H4 & H5).
    iIntros "(A1 & A2 & A3 & A4 & A5)".
    iMod (mono_nat_own_update _ H1 with "A1") as "[$ _]".
    iMod (mono_nat_own_update _ H2 with "A2") as "[$ _]".
    iMod (mono_nat_own_update _ H3 with "A3") as "[$ _]".
    iMod (mono_nat_own_update _ H4 with "A4") as "[$ _]".
    iMod (mono_nat_own_update _ H5 with "A5") as "[$ _]".
    done.
  Qed.

  (** The lower bound is SOUND: what it tells you is a floor, which is the
      direction owned memory needs (knowing your view is AT LEAST [w] is what
      rules out reading stale; a larger real view only makes reads fresher). *)
  Lemma ws_scal_lb_valid γ w w0 :
    ws_scal_auth γ w -∗ ws_scal_lb γ w0 -∗
    ⌜(w_vrOld w0 ≤ w_vrOld w)%nat /\ (w_vwOld w0 ≤ w_vwOld w)%nat /\
     (w_vrNew w0 ≤ w_vrNew w)%nat /\ (w_vwNew w0 ≤ w_vwNew w)%nat /\
     (w_vRel  w0 ≤ w_vRel  w)%nat⌝.
  Proof.
    iIntros "(A1 & A2 & A3 & A4 & A5) (L1 & L2 & L3 & L4 & L5)".
    iDestruct (mono_nat_lb_own_valid with "A1 L1") as %[_ ?].
    iDestruct (mono_nat_lb_own_valid with "A2 L2") as %[_ ?].
    iDestruct (mono_nat_lb_own_valid with "A3 L3") as %[_ ?].
    iDestruct (mono_nat_lb_own_valid with "A4 L4") as %[_ ?].
    iDestruct (mono_nat_lb_own_valid with "A5 L5") as %[_ ?].
    iPureIntro. auto.
  Qed.

End scalars.

(* ====================================================================== *)
(** ** 2. THE PER-BYTE COHERENCE FLOOR — and the trap in encoding it.

    [w_coh : gmap Z nat] with [coh w a := default 0 (w_coh w !! a)], ordered
    by [∀ a, coh w1 a ≤ coh w2 a].  The obvious camera is
    [auth (gmapUR Z max_natUR)] — but the obvious ENCODING
    [MaxNat <$> w_coh w] is WRONG, and quietly so:

      [gmap] inclusion is pointwise inclusion in [option], and
      [Some x ≼ None] is FALSE.  So a state whose map carries an EXPLICIT
      zero entry ([w_coh w1 = {[a := 0]}]) is not included in one that omits
      the key ([w_coh w2 = ∅]) -- even though [ws_le w1 w2] HOLDS, since both
      have [coh _ a = 0].

    So [ws_le] and [≼] disagree exactly on explicit-zero entries, and any
    [ws_le -> ≼] lemma proved against the naive encoding is unprovable.  Two
    ways out, neither yet taken:

      (a) NORMALISE: encode by [MaxNat <$> filter (fun kv => kv.2 ≠ 0%nat)
          (w_coh w)], and carry a normalisation lemma [coh w a] is preserved.
          Keeps one camera; costs a filter-lookup lemma.
      (b) TOTALISE: do not use [gmap] inclusion at all -- use a camera of
          FUNCTIONS [Z -> max_nat] (or [discrete_fun]), for which pointwise
          [≤] IS inclusion on the nose.  Costs a non-finite camera, which is
          fine for a ghost floor that is only ever read at finitely many keys.

    (b) IS WHAT IS BUILT BELOW: [ws_le]'s coherence conjunct is already
    stated over the TOTAL [coh], not over the map, so the function camera
    matches the intended semantics on the nose and (a)'s normalisation is an
    artifact of the representation.

    NOTE on [Finite].  [discrete_fun_included_spec] — the [↔] between
    inclusion and POINTWISE inclusion — is stated only for a [Finite] index,
    which [Z] is not.  We never need it: [max_nat] is idempotent, so the
    witness for [f ≼ g] is [g] itself, and the interesting direction is a
    two-line proof ([coh_fun_incl]).  The [Finite] side condition in Iris is
    about general cameras, where the difference has to be built pointwise by
    choice; for a max-camera there is nothing to choose. *)

(** The per-byte coherence floor as a camera of FUNCTIONS.  Pointwise [≤] is
    inclusion definitionally — no normalisation, no explicit-zero trap. *)
Definition cohUR : ucmra := discrete_funUR (λ _ : Z, max_natUR).

Definition coh_fun (w : wstate) : cohUR := λ a, MaxNat (coh w a).

Section coh_alg.

  (** Pointwise [≤] gives inclusion, with [g] itself as the witness. *)
  Lemma coh_fun_incl w1 w2 : ws_le w1 w2 -> coh_fun w1 ≼ coh_fun w2.
  Proof.
    intros (Hc & _). exists (coh_fun w2). intros a.
    rewrite discrete_fun_lookup_op /coh_fun max_nat_op.
    rewrite Nat.max_r; [done|apply Hc].
  Qed.

  (** The local update behind the authority's frame-preserving update — the
      [discrete_fun] twin of [max_nat_local_update], proved the same way. *)
  Lemma coh_fun_local_update w w' g :
    ws_le w w' -> (coh_fun w, g) ~l~> (coh_fun w', coh_fun w').
  Proof.
    intros (Hc & _). rewrite local_update_unital_discrete => z _ Heq.
    split; [by intros a|]. intros a. specialize (Heq a). specialize (Hc a).
    rewrite discrete_fun_lookup_op in Heq. rewrite discrete_fun_lookup_op.
    rewrite /coh_fun in Heq |- *.
    destruct (g a) as [ga], (z a) as [za].
    rewrite max_nat_op in Heq. rewrite max_nat_op.
    revert Heq. intros [= Heq]. rewrite Nat.max_l; [done|lia].
  Qed.

  (** [coh_fun] is a core element, so the fragment is persistent. *)
  Global Instance coh_fun_core_id w : CoreId (coh_fun w).
  Proof. constructor=> a. reflexivity. Qed.

End coh_alg.

(* ---------------------------------------------------------------------- *)
(** ** 3. The two halves assembled: the authority, and the persistent floor.

    [ws_auth] carries the fragment at the same value, exactly as
    [mono_nat_auth] does, so that [ws_lb_get] is [cmra_included_r] rather
    than a frame-preserving update. *)

Class weakViewG (Σ : gFunctors) := {
  wv_scal :: weakViewScalarG Σ;
  wv_coh  :: inG Σ (authR cohUR);
}.

Record wview_names := WvNames {
  wvn_scal : ws_names;
  wvn_coh  : gname;
}.

Section view.
  Context `{!weakViewG Σ}.

  Definition ws_coh_auth (γ : gname) (w : wstate) : iProp Σ :=
    own γ (● coh_fun w ⋅ ◯ coh_fun w).
  Definition ws_coh_lb (γ : gname) (w : wstate) : iProp Σ :=
    own γ (◯ coh_fun w).

  (** The authority on a hart's whole weak state, at an exact value.  This is
      what the state interpretation holds; it is NOT what a client threads. *)
  Definition ws_auth (γ : wview_names) (w : wstate) : iProp Σ :=
    (ws_scal_auth (wvn_scal γ) w ∗ ws_coh_auth (wvn_coh γ) w)%I.

  (** THE CLIENT-FACING FACT: a persistent, duplicable floor.  Unlike
      [hart_ws], this survives every intervening step for free — that is the
      whole point, and the reason nothing above a leaf has to name a
      [wstate] or carry an [ws_le]. *)
  Definition ws_lb (γ : wview_names) (w : wstate) : iProp Σ :=
    (ws_scal_lb (wvn_scal γ) w ∗ ws_coh_lb (wvn_coh γ) w)%I.

  Global Instance ws_coh_lb_persistent γ w : Persistent (ws_coh_lb γ w).
  Proof. apply _. Qed.
  Global Instance ws_lb_persistent γ w : Persistent (ws_lb γ w).
  Proof. apply _. Qed.
  Global Instance ws_lb_timeless γ w : Timeless (ws_lb γ w).
  Proof. apply _. Qed.

  Lemma ws_coh_lb_get γ w : ws_coh_auth γ w -∗ ws_coh_lb γ w.
  Proof. iIntros "H". iApply (own_mono with "H"). apply cmra_included_r. Qed.

  Lemma ws_lb_get γ w : ws_auth γ w -∗ ws_lb γ w.
  Proof.
    iIntros "[Hs Hc]".
    iDestruct (ws_scal_lb_get with "Hs") as "#Ls".
    iDestruct (ws_coh_lb_get with "Hc") as "#Lc".
    by iFrame "Ls Lc".
  Qed.

  Lemma ws_coh_update γ w w' :
    ws_le w w' -> ws_coh_auth γ w ==∗ ws_coh_auth γ w'.
  Proof.
    intros Hle. iApply own_update.
    by apply auth_update, coh_fun_local_update.
  Qed.

  (** THE UPDATE, whole-state.  Again: the caller does not name the old
      value.  A leaf holding the authority discharges "there EXISTS a larger
      [wstate]" internally, which is what lets the token above it be
      opaque. *)
  Lemma ws_update γ w w' :
    ws_le w w' -> ws_auth γ w ==∗ ws_auth γ w'.
  Proof.
    iIntros (Hle) "[Hs Hc]".
    iMod (ws_scal_update with "Hs") as "$"; [done|].
    by iMod (ws_coh_update with "Hc") as "$".
  Qed.

  Lemma ws_coh_lb_valid γ w w0 :
    ws_coh_auth γ w -∗ ws_coh_lb γ w0 -∗ ⌜∀ a, (coh w0 a ≤ coh w a)%nat⌝.
  Proof.
    iIntros "Ha Hf".
    iDestruct (own_valid_2 with "Ha Hf") as %Hv. iPureIntro. intros a.
    move: Hv. rewrite -assoc -auth_frag_op.
    rewrite auth_both_valid_discrete => -[Hincl _].
    apply (discrete_fun_included_spec_1 _ _ a) in Hincl.
    rewrite discrete_fun_lookup_op /coh_fun max_nat_op in Hincl.
    apply max_nat_included in Hincl. simpl in Hincl. lia.
  Qed.

  (** Soundness of the floor, in the shape client code wants to consume it:
      what you snapshotted is [ws_le] below what is actually there. *)
  Lemma ws_lb_valid γ w w0 : ws_auth γ w -∗ ws_lb γ w0 -∗ ⌜ws_le w0 w⌝.
  Proof.
    iIntros "[Hs Hc] [Ls Lc]".
    iDestruct (ws_scal_lb_valid with "Hs Ls") as %(?&?&?&?&?).
    iDestruct (ws_coh_lb_valid with "Hc Lc") as %Hcoh.
    iPureIntro. by rewrite /ws_le.
  Qed.

  (** A floor may always be weakened — the [ws_le]-monotone reading. *)
  Lemma ws_lb_mono γ w w' : ws_le w w' -> ws_lb γ w' -∗ ws_lb γ w.
  Proof.
    iIntros (Hle) "[Ls Lc]". iSplitL "Ls".
    - destruct Hle as (_ & ? & ? & ? & ? & ?).
      iDestruct "Ls" as "(L1 & L2 & L3 & L4 & L5)".
      iSplitL "L1"; [by iApply mono_nat_lb_own_le|].
      iSplitL "L2"; [by iApply mono_nat_lb_own_le|].
      iSplitL "L3"; [by iApply mono_nat_lb_own_le|].
      iSplitL "L4"; [by iApply mono_nat_lb_own_le|].
      by iApply mono_nat_lb_own_le.
    - iApply (own_mono with "Lc"). by apply auth_frag_mono, coh_fun_incl.
  Qed.

  (** Allocation. *)
  Lemma ws_alloc w : ⊢ |==> ∃ γ, ws_auth γ w.
  Proof.
    iMod (mono_nat_own_alloc (w_vrOld w)) as (g1) "[A1 _]".
    iMod (mono_nat_own_alloc (w_vwOld w)) as (g2) "[A2 _]".
    iMod (mono_nat_own_alloc (w_vrNew w)) as (g3) "[A3 _]".
    iMod (mono_nat_own_alloc (w_vwNew w)) as (g4) "[A4 _]".
    iMod (mono_nat_own_alloc (w_vRel  w)) as (g5) "[A5 _]".
    iMod (own_alloc (● coh_fun w ⋅ ◯ coh_fun w)) as (gc) "Ac".
    { apply auth_both_valid_discrete. split; [done|by intros a]. }
    iModIntro. iExists (WvNames (WsNames g1 g2 g3 g4 g5) gc). by iFrame.
  Qed.

End view.

(* ---------------------------------------------------------------------- *)
(** ** 4. The opaque token, and the leaf-facing step rule.

    [hart_view] is the thing a client threads: the authority with its value
    EXISTENTIALLY HIDDEN.  A leaf takes it and hands it back; the step
    obligation is "there exists a larger [wstate]", and [hart_view_step] is
    the proof that a leaf can discharge that internally.  Above a leaf there
    is no [ws] binder, no [ws'], and no [⌜ws_le ws ws'⌝] — which is the
    entire claim of the design note's §2. *)

Section token.
  Context `{!weakViewG Σ}.

  Definition hart_view (γ : wview_names) : iProp Σ := (∃ w, ws_auth γ w)%I.

  Lemma hart_view_intro γ w : ws_auth γ w -∗ hart_view γ.
  Proof. iIntros "H". by iExists w. Qed.

  (** What a leaf does: open the token, learn the current state, step it to
      any [ws_le]-larger one, close it.  The caller sees [hart_view γ] in and
      [hart_view γ] out — no values at all. *)
  Lemma hart_view_step γ (step : wstate -> wstate) :
    (∀ w, ws_le w (step w)) ->
    hart_view γ ==∗ hart_view γ.
  Proof.
    iIntros (Hstep) "[%w Hauth]".
    iMod (ws_update _ _ (step w) with "Hauth") as "Hauth"; [done|].
    iModIntro. by iExists (step w).
  Qed.

  (** Snapshotting through the token: a client that DOES care about views
      (the lock, the escrow) takes a persistent floor and keeps it across
      arbitrarily many later steps. *)
  Lemma hart_view_snapshot γ : hart_view γ ==∗ ∃ w, hart_view γ ∗ ws_lb γ w.
  Proof.
    iIntros "[%w Hauth]". iDestruct (ws_lb_get with "Hauth") as "#Hlb".
    iModIntro. iExists w. iFrame "Hlb". by iExists w.
  Qed.

  (** THE PAYOFF LEMMA.  A floor taken before a step is still a floor after
      arbitrarily many steps — with no [vwp_hold_mono], no rebasing, and
      without the client ever naming a [wstate].  Contrast [hart_ws], where
      every intervening instruction forces the fact from [ws] to [ws']. *)
  Lemma ws_lb_survives γ w0 :
    ws_lb γ w0 -∗ hart_view γ -∗ ⌜True⌝ ∗ ws_lb γ w0.
  Proof. iIntros "#Hlb _". by iFrame "Hlb". Qed.

End token.
