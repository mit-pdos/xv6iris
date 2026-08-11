(** * WeakPtPub.v — what goes IN a lock invariant, and the two one-line
      conversions at acquire and release.

    Design: [`claude-notes/design/weak-memory-sc-parity.md`] §5.5 / risk §6.3
    — "the boundary seam"; §9 for why the objective side is indexed by a
    CONTEXT rather than a hart.  Sits on [WeakCtx]'s [cobj].

    THE QUESTION.  An objective points-to carries a floor, and a floor is a
    statement about somebody's view — so a whole objective points-to must NOT
    go in a shared invariant: the reader opening it would obtain the
    depositor's floor, which the reader cannot use.  So what does go in?

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

    which is objective, hart-free, CONTEXT-free, and says exactly "the
    element, published no later than [T]".  Call it [wpt_pub T a dq v].  IT
    IS NOT A NEW CONSTRUCT — it is the normal form of what the invariant
    holds today.

    So the seam is two conversions and nothing else:

      RELEASE   [cobj ξA]   --> [wpt_pub T]   ([cobj_pt_release])
      ACQUIRE   [wpt_pub T] --> [cobj ξB]     ([cobj_pt_acquire])

    and the acquire's side condition is precisely the scalar gain
    [WeakFence.amo_acq_gain] already delivers, in its [⊑] packaging:
    [view_scl T ⊑ V] unfolds, by [flr_scl_eq], to [∀ a, T ≤ flr V a].

    NOTE WHAT THE ACQUIRE NEEDS, and why it is the SCALAR.  The hypothesis
    quantifies over EVERY byte, not the byte being acquired.  That is the
    formal content of [WeakFence]'s remark that the scalar "is the whole
    difference between an acquire and a plain load": a plain load gains only
    the byte it read, which would let the acquirer rebuild the points-to for
    THAT byte alone, not for a whole protected region.

    AND WHAT THE RELEASE NEEDS.  Symmetrically [∀ a, flr V a ≤ T].  This is
    strictly weaker than what the old hart-indexed release asked for (that
    lemma bounded the floor AT THE ONE ADDRESS), and the weakening is forced
    rather than incidental: [cobj ξ R] existentially quantifies the view [R]
    is held at, so the release has no footprint to bound against — it cannot
    know that [R] is a statement about [a] alone.  For a REGION the two
    coincide, since a region release quantified over all addresses anyway,
    and a region is what a lock actually protects.  Recovering the sharp
    single-byte form would mean indexing [cobj] by a footprint, which buys
    nothing a lock wants.

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
Require Import WeakViewMono WeakCtx.

Section pub.
  Context `{!riscvGS Σ, !weakGS Σ}.

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
      context-free, and admissible in a shared invariant. *)
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

  Lemma wpt_pub_unfold T a dq v :
    wpt_pub T a dq v ⊣⊢ ∃ t, wlat_pointsto a dq t v ∗ ⌜(t ≤ T)%nat⌝.
  Proof.
    rewrite /wpt_pub. apply bi.exist_proper => t. iSplit; iIntros "[$ $]".
  Qed.

  (** [wpt_pub 0] IS the era-image points-to: the element at timestamp 0,
      which is [WeakVProp.wpt_img]'s body.  So [wpt_pub] is the
      generalisation of [wpt_img] from "never written" to "published no
      later than [T]", and it is at [T = 0] — and only there — that the
      invariant's resource needs no synchronisation to localise, because a
      floor of 0 is below every view at every byte. *)
  Lemma wpt_pub_0 a dq v : wpt_pub 0 a dq v ⊣⊢ wlat_pointsto a dq 0%nat v.
  Proof.
    rewrite /wpt_pub. iSplit.
    - iIntros "[%t [%Ht He]]". assert (t = 0%nat) as -> by lia. iFrame "He".
    - iIntros "He". iExists 0%nat. by iFrame "He".
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 3. THE SEAM, in two lemmas

      Both are one line on top of [WeakCtx]'s generic [cobj_acquire] /
      [cobj_release] plus [wpt_pub_frozen]'s identification — which is the
      evidence that the seam really is generic in the payload and that a
      points-to is not a special case.  A lock whose payload is an arbitrary
      [vProp] uses [cobj_acquire]/[cobj_release] directly; these two exist
      because the points-to is the payload everyone writes first. *)

  (** ACQUIRE.  The published element plus the acquiring context's gain IS
      that context's objective points-to.  The client never sees a view:
      this is the whole of "the lock pays the weak-memory cost once, on
      behalf of every client". *)
  Lemma cobj_pt_acquire (ξ : CtxId) (V : view) (T : nat) a dq v :
    (∀ b, (T ≤ flr V b)%nat) ->
    ctx_auth ξ V -∗ wpt_pub T a dq v -∗
    ctx_auth ξ V ∗ cobj ξ (a ↦w{dq} v).
  Proof.
    iIntros (HT) "Hauth Hp". rewrite -wpt_pub_frozen.
    by iApply (cobj_acquire with "Hauth Hp").
  Qed.

  (** RELEASE.  The releasing context's own floor bounds its elements, so
      publishing at any [T] above that floor is sound.  [T] is the releasing
      store's timestamp; [WeakInstr.wwp_release_deposit] is where it comes
      from. *)
  Lemma cobj_pt_release (ξ : CtxId) (V : view) (T : nat) a dq v :
    (∀ b, (flr V b ≤ T)%nat) ->
    ctx_auth ξ V -∗ cobj ξ (a ↦w{dq} v) -∗
    ctx_auth ξ V ∗ wpt_pub T a dq v.
  Proof.
    iIntros (HT) "Hauth Hc".
    iDestruct (cobj_release with "Hauth Hc") as "[$ Hp]"; [exact HT|].
    by rewrite wpt_pub_frozen.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** 4. A whole protected region

      A lock protects bytes, not a byte.  Both conversions commute with
      [big_sepM] for free — the acquire because one scalar floor serves every
      byte (again: the SCALAR is what an acquire gains), the release because
      the bound is already stated at every address. *)

  Definition wpt_pub_region (T : nat) (dq : dfrac) (m : gmap Z (bv 8))
      : iProp Σ := ([∗ map] a ↦ v ∈ m, wpt_pub T a dq v)%I.

  Definition cobj_pt_region (ξ : CtxId) (dq : dfrac) (m : gmap Z (bv 8))
      : iProp Σ := ([∗ map] a ↦ v ∈ m, cobj ξ (a ↦w{dq} v))%I.

  Lemma cobj_pt_region_acquire ξ V T dq m :
    (∀ b, (T ≤ flr V b)%nat) ->
    ctx_auth ξ V -∗ wpt_pub_region T dq m -∗
    ctx_auth ξ V ∗ cobj_pt_region ξ dq m.
  Proof.
    iIntros (HT) "Hauth Hm".
    rewrite /wpt_pub_region /cobj_pt_region.
    iInduction m as [|a v m Hnew] "IH" using map_ind.
    { rewrite !big_sepM_empty. by iFrame "Hauth". }
    rewrite !big_sepM_insert //. iDestruct "Hm" as "[Hp Hm]".
    iDestruct (cobj_pt_acquire _ _ _ _ _ _ HT with "Hauth Hp") as "[Hauth $]".
    by iApply ("IH" with "Hauth Hm").
  Qed.

  Lemma cobj_pt_region_release ξ V T dq m :
    (∀ b, (flr V b ≤ T)%nat) ->
    ctx_auth ξ V -∗ cobj_pt_region ξ dq m -∗
    ctx_auth ξ V ∗ wpt_pub_region T dq m.
  Proof.
    iIntros (HT) "Hauth Hm".
    rewrite /wpt_pub_region /cobj_pt_region.
    iInduction m as [|a v m Hnew] "IH" using map_ind.
    { rewrite !big_sepM_empty. by iFrame "Hauth". }
    rewrite !big_sepM_insert //. iDestruct "Hm" as "[Hp Hm]".
    iDestruct (cobj_pt_release _ _ _ _ _ _ HT with "Hauth Hp") as "[Hauth $]".
    by iApply ("IH" with "Hauth Hm").
  Qed.

End pub.

(* ====================================================================== *)
(** ** 5. THE HANDOFF, end to end — THE ONLY PLACE TWO CONTEXTS ARE NAMED.

    Everywhere else the context is a parameter threaded through one
    execution.  Here it cannot be, because the whole content of the lemma is
    that the region CHANGES HANDS.

    Compare what this looked like when the objective layer was indexed by a
    HART ([WeakPtOwn], deleted): the same statement took two [CpuId]s and
    two [ws_auth]s, and asserted that "the SAME fraction of the SAME bytes
    is a DIFFERENT proposition on the two sides".  That is still true here
    of two DIFFERENT contexts — a handoff is a real transfer, not a
    re-typing — but it is no longer true of one context that MIGRATES, which
    is the case the hart index got wrong (design §9).

    Note also what has NOT survived and did not need to: the hart version
    needed both authorities present in a single step, which is exactly what
    a real handoff through an invariant denies.  Here the two halves split
    cleanly — [cobj_pt_region_release] under ξA at release time,
    [cobj_pt_region_acquire] under ξB at acquire time — and this lemma
    composes them only to state the end-to-end shape. *)

Section handoff.
  Context `{!riscvGS Σ, !weakGS Σ}.

(** Context A holds the region objectively and releases at [T]; the region
    sits in the invariant as [wpt_pub_region T], with no context named and
    no view crossing the boundary; context B's acquire gains [view_scl T]
    and takes the region out objectively.  Neither side ever names a
    [wstate] in its OWN reasoning — the [ctx_auth]s are the leaves'
    business.

    This is the shape a lock's client-facing spec should have: [cobj] in,
    [cobj] out, weak memory confined to the two conversions of §3. *)
Lemma cobj_pt_region_handoff (ξA ξB : CtxId) (VA VB : view) (T : nat) dq m :
  (* the releaser's floor is below the timestamp its store takes *)
  (∀ a, (flr VA a ≤ T)%nat) ->
  (* ... which is exactly what the acquirer's [amo_acq_gain] delivers,
     [view_scl T ⊑ VB] unfolded by [flr_scl_eq] *)
  (∀ a, (T ≤ flr VB a)%nat) ->
  ctx_auth ξA VA -∗ ctx_auth ξB VB -∗ cobj_pt_region ξA dq m -∗
  ctx_auth ξA VA ∗ ctx_auth ξB VB ∗ cobj_pt_region ξB dq m.
Proof.
  iIntros (HT Hacq) "HA HB Hm".
  iDestruct (cobj_pt_region_release _ _ T _ _ HT with "HA Hm") as "[$ Hpub]".
  by iDestruct (cobj_pt_region_acquire _ _ T _ _ Hacq with "HB Hpub")
    as "[$ $]".
Qed.

End handoff.
