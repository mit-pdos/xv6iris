(** * WeakPtPub.v — PROTOTYPE: what goes IN a lock invariant, and the two
      one-line conversions at acquire and release.

    Design: [`claude-notes/design/weak-memory-sc-parity.md`] §5.5 / risk §6.3
    — "the boundary seam".  Sits on [WeakPtOwn]'s objective points-to.

    THE QUESTION.  [WeakPtOwn.wpt_own] names a hart, so a whole [↦o] must NOT
    go in a shared invariant: hart B opening it would obtain hart A's floor,
    which B cannot use.  So what does go in?

    THE ANSWER IS THAT THE LOCK ALREADY HOLDS THE RIGHT THING.  [WeakLock]'s
    header says the invariant carries [monPred_at R V] — the payload frozen
    at a view — and that

    > the timestamp [t] the elements carry IS the timestamp the payload is
    > frozen at.  [...] the releaser deposits at the timestamp its own store
    > takes ([WeakInstr.wwp_release_deposit]), and the acquirer's
    > [amoswap.w.aq] reads THAT timestamp and gains [view_scl t ⊑ ws_view]
    > ([WeakFence.amo_acq_gain]) — so the payload thaws into the acquirer's
    > own index by [monPred_mono], and no view ever crosses the invariant
    > boundary.

    Compute what that frozen payload IS for a points-to and the answer falls
    out ([wpt_pub_frozen] below): at the scalar view [view_scl T],

      [monPred_at (a ↦w{dq} v) (view_scl T)  ⊣⊢  ∃ t, ⌜t ≤ T⌝ ∗ wlat_pointsto a dq t v]

    which is objective, hart-free, and says exactly "the element, published
    no later than [T]".  Call it [wpt_pub T a dq v].  IT IS NOT A NEW
    CONSTRUCT — it is the normal form of what the invariant holds today.

    So the seam is two conversions and nothing else:

      RELEASE   [↦o] at hart A  --> [wpt_pub T]      ([wpt_own_release])
      ACQUIRE   [wpt_pub T]     --> [↦o] at hart B   ([wpt_pub_acquire])

    and the acquire's side condition is precisely the scalar gain
    [amo_acq_gain] already delivers.  Note WHICH disjunct of
    [WeakPtOwn.wflr_lb] the acquire uses: the [w_vrNew] one, not the
    per-byte [coh] one.  That is the formal content of [WeakFence]'s remark
    that the scalar "is the whole difference between an acquire and a plain
    load" — a plain load gains only the byte it read, and would let the
    acquirer rebuild [↦o] for THAT byte alone, not for the whole protected
    region.

    WHAT IS AND IS NOT ESTABLISHED HERE.  The two conversions are proved.
    What is assumed is the identification of [T] across the boundary — that
    the [T] in the invariant is the timestamp the releaser's store took and
    the acquirer's AMO read.  That identification is [WeakLock]'s existing
    protocol obligation, not a new one, and it is why this file takes [T] as
    a parameter rather than inventing a lock. *)
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
Require Import WeakMem WeakInterp WeakLang WeakView WeakVProp WeakGhost.
Require Import WeakViewMono WeakPtOwn.

Section pub.
  Context `{!riscvGS Σ, !weakGS Σ, !weakViewG Σ}.

  (* ------------------------------------------------------------------ *)
  (** ** 1. The points-to at an arbitrary frozen view

      [WeakVProp.wpt_at] is this at [ws_view ws]; the invariant needs it at
      [view_scl T], so here it is in general.  The proof is [wpt_at]'s. *)
  Lemma wpt_view_at a dq v (V : view) :
    monPred_at (a ↦w{dq} v) V ⊣⊢
      ∃ t : nat, wlat_pointsto a dq t v ∗ ⌜(t ≤ flr V a)%nat⌝.
  Proof.
    rewrite /wpt monPred_at_exist.
    setoid_rewrite monPred_at_sep. setoid_rewrite monPred_at_embed.
    setoid_rewrite monPred_at_in.
    apply bi.exist_proper => t.
    iSplit; iIntros "[He %H]"; iFrame "He"; iPureIntro; by apply view_byte_le.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 2. The published points-to — what the invariant holds *)

  (** "The element, published no later than [T]."  Objective, hart-free,
      and admissible in a shared invariant. *)
  Definition wpt_pub (T : nat) (a : Z) (dq : dfrac) (v : bv 8) : iProp Σ :=
    (∃ t : nat, ⌜(t ≤ T)%nat⌝ ∗ wlat_pointsto a dq t v)%I.

  Global Instance wpt_pub_timeless T a dq v : Timeless (wpt_pub T a dq v).
  Proof. apply _. Qed.
  Global Instance wpt_pub_persistent T a v :
    Persistent (wpt_pub T a DfracDiscarded v).
  Proof. apply _. Qed.

  (** THE POINT: [wpt_pub] is not a new construct, it is the normal form of
      the payload [WeakLock] already freezes at [view_scl T]. *)
  Lemma wpt_pub_frozen T a dq v :
    monPred_at (a ↦w{dq} v) (view_scl T) ⊣⊢ wpt_pub T a dq v.
  Proof.
    rewrite wpt_view_at /wpt_pub. apply bi.exist_proper => t.
    rewrite flr_scl_eq. iSplit; iIntros "[$ $]".
  Qed.

  (** A later deposit publishes no less. *)
  Lemma wpt_pub_mono T T' a dq v :
    (T ≤ T')%nat -> wpt_pub T a dq v -∗ wpt_pub T' a dq v.
  Proof.
    iIntros (Hle) "[%t [%Ht He]]". iExists t. iFrame "He". iPureIntro. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 3. THE SEAM, in two lemmas *)

  (** The acquirer's scalar floor, as a resource.  [amo_acq_gain] gives
      [view_scl T ⊑ ws_view ws'], i.e. [T ≤ w_vrNew ws']; this turns that
      into the persistent fact the points-to wants. *)
  Definition vrNew_lb (γv : wview_names) (T : nat) : iProp Σ :=
    mono_nat_lb_own (wsn_vrNew (wvn_scal γv)) T.

  Global Instance vrNew_lb_persistent γv T : Persistent (vrNew_lb γv T).
  Proof. apply _. Qed.

  Lemma vrNew_lb_get γv ws T :
    (T ≤ w_vrNew ws)%nat -> ws_auth γv ws -∗ vrNew_lb γv T.
  Proof.
    iIntros (Hle) "[Hs _]". iDestruct "Hs" as "(_ & _ & A3 & _ & _)".
    iDestruct (mono_nat_lb_own_get with "A3") as "#L".
    iApply (mono_nat_lb_own_le with "L"). exact Hle.
  Qed.

  (** A WRINKLE, worth recording because it bit here.  [amo_acq_gain]'s
      conclusion is [view_scl T ⊑ ws_view ws], and [⊑] on views is stated
      THROUGH [flr]:

        [view_scl T ⊑ ws_view ws  =  ∀ a, T ≤ Nat.max (w_vrNew ws) (coh ws a)]

      which does NOT give [T ≤ w_vrNew ws] at any particular [a] — you would
      have to instantiate at an address outside [w_coh ws]'s finite support.
      The scalar is true (it is what [load_post_at_vrNew_aq] actually
      proves); the [⊑] packaging simply forgets it.  So an acquire leaf
      should export [T ≤ w_vrNew ws'] directly rather than only the [⊑].

      Both forms are supported below: [wpt_pub_acquire_lb] is the clean one
      that takes the persistent scalar token, and [wpt_pub_acquire] is the
      one an acquire leaf can use as it stands, from the [⊑] alone plus the
      authority it is already holding. *)

  (** ACQUIRE, from the persistent scalar token.  The published element plus
      the acquirer's gain IS the acquirer's objective points-to.  One line,
      and the client never sees a view: this is the whole of "the lock pays
      the weak-memory cost once, on behalf of every client". *)
  Lemma wpt_pub_acquire_lb γv T a dq v :
    vrNew_lb γv T -∗ wpt_pub T a dq v -∗ wpt_own γv a dq v.
  Proof.
    iIntros "#Hlb [%t [%Ht He]]". iExists t. iFrame "He".
    iRight. by iApply (mono_nat_lb_own_le with "Hlb").
  Qed.

  (** ACQUIRE, from [amo_acq_gain]'s [⊑] and the authority.  Note this one
      goes through [wflr_lb_get] per byte and so does not care which disjunct
      of [wflr_lb] is used — it works even where only the per-byte coherence
      floor moved. *)
  Lemma wpt_pub_acquire γv ws T a dq v :
    view_scl T ⊑ ws_view ws ->
    ws_auth γv ws -∗ wpt_pub T a dq v -∗ ws_auth γv ws ∗ wpt_own γv a dq v.
  Proof.
    iIntros (Hacq) "Hauth [%t [%Ht He]]".
    specialize (Hacq a). rewrite flr_scl_eq in Hacq.
    iDestruct (wflr_lb_get _ ws a t with "Hauth") as "#Hlb"; [lia|].
    iFrame "Hauth". iExists t. by iFrame "He".
  Qed.

  (** RELEASE.  The releaser's own floor bounds its elements, so publishing
      at any [T] above that floor is sound.  [T] is the releasing store's
      timestamp; [WeakInstr.wwp_release_deposit] is where it comes from. *)
  Lemma wpt_own_release γv ws T a dq v :
    (flr (ws_view ws) a ≤ T)%nat ->
    ws_auth γv ws -∗ wpt_own γv a dq v -∗ ws_auth γv ws ∗ wpt_pub T a dq v.
  Proof.
    iIntros (HT) "Hauth [%t [He #Hlb]]".
    iDestruct (wflr_lb_valid with "Hauth Hlb") as %Hle.
    iFrame "Hauth". iExists t. iFrame "He". iPureIntro. lia.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 4. A whole protected region

      A lock protects bytes, not a byte.  Both conversions commute with
      [big_sepM] for free — the acquire because one scalar floor serves every
      byte (again: the SCALAR is what an acquire gains), the release because
      the bound is per-byte and taken at a common [T]. *)

  Definition wpt_pub_region (T : nat) (dq : dfrac) (m : gmap Z (bv 8))
      : iProp Σ := ([∗ map] a ↦ v ∈ m, wpt_pub T a dq v)%I.

  Definition wpt_own_region (γv : wview_names) (dq : dfrac)
      (m : gmap Z (bv 8)) : iProp Σ :=
    ([∗ map] a ↦ v ∈ m, wpt_own γv a dq v)%I.

  Lemma wpt_pub_region_acquire γv T dq m :
    vrNew_lb γv T -∗ wpt_pub_region T dq m -∗ wpt_own_region γv dq m.
  Proof.
    iIntros "#Hlb Hm". rewrite /wpt_pub_region /wpt_own_region.
    iApply (big_sepM_impl with "Hm"). iIntros "!>" (a v _) "Hp".
    by iApply (wpt_pub_acquire_lb with "Hlb Hp").
  Qed.

  Lemma wpt_own_region_release γv ws T dq m :
    (∀ a, (flr (ws_view ws) a ≤ T)%nat) ->
    ws_auth γv ws -∗ wpt_own_region γv dq m -∗
    ws_auth γv ws ∗ wpt_pub_region T dq m.
  Proof.
    iIntros (HT) "Hauth Hm". rewrite /wpt_pub_region /wpt_own_region.
    iInduction m as [|a v m Hnew] "IH" using map_ind.
    { rewrite !big_sepM_empty. by iFrame "Hauth". }
    rewrite !big_sepM_insert //. iDestruct "Hm" as "[Hp Hm]".
    iDestruct (wpt_own_release _ _ T _ _ _ (HT a) with "Hauth Hp")
      as "[Hauth $]".
    by iApply ("IH" with "Hauth Hm").
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 5. THE HANDOFF, end to end.

      Hart A holds the region objectively, releases at [T]; the region sits
      in the invariant as [wpt_pub_region T] with no hart named and no view
      crossing the boundary; hart B's acquire gains [view_scl T] and takes
      the region out objectively.  Neither side ever names a [wstate] in its
      OWN reasoning — the two [ws_auth]s are the leaves' business.

      This is the shape a lock's client-facing spec should have: [↦o] in,
      [↦o] out, weak memory confined to the two conversions above. *)
  Lemma wpt_region_handoff (γA γB : wview_names) (wA wB : wstate)
      (T : nat) dq m :
    (* the releaser's floor is below the timestamp its store takes *)
    (∀ a, (flr (ws_view wA) a ≤ T)%nat) ->
    (* ... which is exactly what the acquirer's [amo_acq_gain] delivers *)
    (T ≤ w_vrNew wB)%nat ->
    ws_auth γA wA -∗ ws_auth γB wB -∗ wpt_own_region γA dq m -∗
    ws_auth γA wA ∗ ws_auth γB wB ∗ wpt_own_region γB dq m.
  Proof.
    iIntros (HT Hacq) "HA HB Hm".
    iDestruct (wpt_own_region_release _ _ T with "HA Hm") as "[HA Hpub]";
      [exact HT|].
    iDestruct (vrNew_lb_get _ _ _ Hacq with "HB") as "#Hlb".
    iFrame "HA HB". by iApply (wpt_pub_region_acquire with "Hlb Hpub").
  Qed.

End pub.
