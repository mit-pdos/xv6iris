(** * WeakFence.v — the fence frontier, the AMO read half, and the
      release→acquire transfer (M2b, items 1 and 2)

    Two event rules and the thing they are FOR.

    ==================== WHAT A FENCE DOES, AND WHY [∇] IS A ====================
    ==================== DISCIPLINE OPERATOR AND NOT A vProp  ====================

    [WeakInterp.barrier_post] with kind [rw,rw] sets
    [w_vrNew ⊔= w_vrOld ⊔ w_vwOld]: the hart's INDEX
    ([WeakVProp.ws_view ws = View (w_vrNew ws) (w_coh ws)]) jumps to what this
    file calls the ACQUIRE FRONTIER,

        [acq_view ws := View (w_vrNew ws ⊔ w_vrOld ws ⊔ w_vwOld ws) (w_coh ws)]

    — and it jumps to it EXACTLY: [ws_view (fence_post ws true true true sw) =
    acq_view ws] holds by [reflexivity].  So the FSL-lineage "acquire-pending"
    modality [∇ P] ("P holds at the frontier a succ-R fence will deliver") is,
    here, [monPred_at P (acq_view ws)].

    THAT CANNOT BE A [vProp] CONNECTIVE IN THIS DESIGN, and the reason is the
    index, not the proof: [WeakView]'s [biIndex] is the pair
    [(w_vrNew, w_coh)], which does not mention [w_vrOld]/[w_vwOld], so
    "the frontier" is not a function of the index — it is extra information
    about the hart.  iRC11 pays for a real [∇] by making its index a TRIPLE
    (current, acquire, release views); doing that here would be a rewrite of
    [WeakView]/[WeakVProp].  The honest minimal interface, and the one that
    matches M2a's design call ("the vProp layer is a discipline over the base
    logic first"), is to give [∇] at the [vwp_hold] altitude, where the hart's
    [wstate] is in hand: [vwp_acq P ws]. Everything the fence rule is used for
    — deliver an assertion frozen at a view the fence covers — is available
    there, and the [P @@ V] payloads it moves are ordinary objective [vProp]s.
    Upgrading the index to a triple is a deliberate deferral, recorded in the
    project notes.

    THE WRITER SIDE IS A LEMMA, NOT A MODALITY.  In the promise-free machine a
    predecessor-W fence constrains nothing (design doc, Decision 1: stores are
    never early), so a [Δ] modality would have no content.  What the M3
    handoff actually needs on the writer side is that the releasing store's
    timestamp DOMINATES the releaser's whole index — and that is
    [ws_bounded]-plus-arithmetic ([release_deposit] below), not a modality.

    ==================== THE AMO READ HALF ====================

    An [amoswap.w.aq] read is [ak_latest] ([WeakInterp]'s access-kind table),
    whose admissibility condition IS [WeakMem.latest].  Two consequences, both
    below: the value is the LATEST write — with no view hypothesis at all, so
    the rule fires off an element held in an INVARIANT ([wamo_read_latest]) —
    and the acquire's post-view carries the read timestamp into the hart's
    SCALAR floor ([amo_acq_gain]).

    ==================== WHAT THEY COMPOSE INTO ====================

    [release_acquire_transfer] : everything the releaser held at its own index
    when its store landed at timestamp [t], the acquirer holds after an
    acquire-AMO that reads [t].  [release_fence_transfer] is the same
    handoff through a plain read plus a succ-R fence (the [started]/MP shape).
    Those two are the M3 lock/escrow skeleton at the view altitude. *)
From stdpp Require Import gmap finite list.
From stdpp Require Import bitvector.definitions.
From iris.proofmode Require Import proofmode monpred.
From iris.algebra Require Import dfrac.
From iris.base_logic.lib Require Import iprop ghost_map ghost_var.
Require Import SailStdpp.Operators_mwords.
Require Import Riscv.rv64d_types.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakInterp.
Require Import WeakGhost.
Require Import WeakView.
Require Import WeakVProp.
Require Import RiscvLang RiscvPtsto.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The acquire frontier *)

(** The index a succ-R fence with pred-RW will deliver.  Spelled with exactly
    [fence_post]'s own nesting, so the fence law below is [reflexivity]. *)
Definition acq_view (ws : wstate) : view :=
  View (Nat.max (w_vrNew ws) (Nat.max (w_vrOld ws) (w_vwOld ws))) (w_coh ws).

Lemma flr_acq_view ws a :
  flr (acq_view ws) a
  = Nat.max (Nat.max (w_vrNew ws) (Nat.max (w_vrOld ws) (w_vwOld ws)))
            (coh ws a).
Proof. reflexivity. Qed.

(** The hart's index is below its own frontier ... *)
Lemma ws_view_acq_view ws : ws_view ws ⊑ acq_view ws.
Proof. intros a. rewrite flr_ws_view flr_acq_view. lia. Qed.

(** ... and a full fence puts it exactly there. *)
Lemma ws_view_fence_rw ws sw :
  ws_view (fence_post ws true true true sw) = acq_view ws.
Proof. reflexivity. Qed.

Lemma ws_view_barrier_rw_rw ws :
  ws_view (barrier_post ws Barrier_RISCV_rw_rw) = acq_view ws.
Proof. reflexivity. Qed.

Lemma ws_view_barrier_rw_r ws :
  ws_view (barrier_post ws Barrier_RISCV_rw_r) = acq_view ws.
Proof. reflexivity. Qed.

(** A weaker pred set delivers less, and that is all a leaf may claim: an
    [r,r] fence carries the READ frontier only. *)
Definition acq_view_r (ws : wstate) : view :=
  View (Nat.max (w_vrNew ws) (w_vrOld ws)) (w_coh ws).

Lemma ws_view_fence_r ws sw :
  ws_view (fence_post ws true false true sw) = acq_view_r ws.
Proof. rewrite /ws_view /fence_post /acq_view_r /=. by rewrite Nat.max_0_r. Qed.

Lemma ws_view_barrier_r_r ws :
  ws_view (barrier_post ws Barrier_RISCV_r_r) = acq_view_r ws.
Proof. apply (ws_view_fence_r ws false). Qed.

Lemma acq_view_r_acq_view ws : acq_view_r ws ⊑ acq_view ws.
Proof. intros a. rewrite /flr /acq_view_r /acq_view /=. lia. Qed.

(** THE DELIVERY FACTS.  A timestamp the hart has already READ (it is in
    [w_vrOld]) — or already WRITTEN ([w_vwOld]) — is covered by the frontier,
    hence by the hart's index after the fence.  This is the reader half of
    every fence-mediated handoff: the scalar view a release deposited is
    exactly what these produce. *)
Lemma view_scl_acq_vrOld ws t : (t ≤ w_vrOld ws)%nat → view_scl t ⊑ acq_view_r ws.
Proof. intros Ht a. rewrite flr_scl_eq /flr /acq_view_r /=. lia. Qed.

Lemma view_scl_acq_vwOld ws t : (t ≤ w_vwOld ws)%nat → view_scl t ⊑ acq_view ws.
Proof. intros Ht a. rewrite flr_scl_eq flr_acq_view. lia. Qed.

(** *** WHICH FENCE KINDS DELIVER A READ.

    The delivery lemmas were originally stated at [Barrier_RISCV_rw_rw] only,
    because that is the kind [acq_view]'s identity ([ws_view_fence_rw]) is
    about.  But the fence xv6's [main] spin loop actually executes is
    [fence r,rw] (gcc's [__ATOMIC_ACQUIRE] load fence, [kernel.asm] at
    [main+0x18]) — pred R, no W — and a scalar view a LOAD gained sits under
    [w_vrOld], which a pred-R fence already carries.
    [acq_pred_r] is that property, abstracted over the kind so no delivery
    lemma has to be duplicated per fence: it says the read frontier
    [acq_view_r] is below the hart's index after the fence. *)
Definition acq_pred_r (b : barrier_kind) : Prop :=
  ∀ ws : wstate, acq_view_r ws ⊑ ws_view (barrier_post ws b).

Lemma acq_pred_r_rw_rw : acq_pred_r Barrier_RISCV_rw_rw.
Proof. intros ws. rewrite ws_view_barrier_rw_rw. apply acq_view_r_acq_view. Qed.

Lemma acq_pred_r_rw_r : acq_pred_r Barrier_RISCV_rw_r.
Proof. intros ws. rewrite ws_view_barrier_rw_r. apply acq_view_r_acq_view. Qed.

Lemma acq_pred_r_r_rw : acq_pred_r Barrier_RISCV_r_rw.
Proof. intros ws. rewrite (ws_view_fence_r ws true). reflexivity. Qed.

Lemma acq_pred_r_r_r : acq_pred_r Barrier_RISCV_r_r.
Proof. intros ws. rewrite ws_view_barrier_r_r. reflexivity. Qed.

(** ... and the delivery itself, at any such kind. *)
Lemma view_scl_acq_pred_r (b : barrier_kind) (ws : wstate) (t : nat) :
  acq_pred_r b → (t ≤ w_vrOld ws)%nat →
  view_scl t ⊑ ws_view (barrier_post ws b).
Proof.
  intros Hb Ht. etrans; [by apply view_scl_acq_vrOld|apply Hb].
Qed.

(* ====================================================================== *)
(** ** 2. [∇] at the [vwp_hold] altitude, and the fence rule *)

Section fence.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Implicit Types P Q : vProp Σ.

  (** "[P] holds at the frontier a succ-R fence will deliver to this hart." *)
  Definition vwp_acq (P : vProp Σ) (ws : wstate) : iProp Σ :=
    monPred_at P (acq_view ws).

  Definition vwp_acq_r (P : vProp Σ) (ws : wstate) : iProp Σ :=
    monPred_at P (acq_view_r ws).

  Global Instance vwp_acq_ne ws : NonExpansive (λ P, vwp_acq P ws).
  Proof. rewrite /vwp_acq. solve_proper. Qed.
  Global Instance vwp_acq_mono' ws : Proper ((⊢) ==> (⊢)) (λ P, vwp_acq P ws).
  Proof. intros P Q HPQ. rewrite /vwp_acq. by apply HPQ. Qed.

  (** THE FENCE RULE: [∇P] before a [fence rw,rw] is [P] after it. *)
  Lemma vwp_acq_fence P ws sw :
    vwp_acq P ws ⊢ vwp_hold P (fence_post ws true true true sw).
  Proof. rewrite /vwp_acq /vwp_hold ws_view_fence_rw //. Qed.

  Lemma vwp_acq_barrier P ws :
    vwp_acq P ws ⊢ vwp_hold P (barrier_post ws Barrier_RISCV_rw_rw).
  Proof. rewrite /vwp_acq /vwp_hold ws_view_barrier_rw_rw //. Qed.

  Lemma vwp_acq_r_fence P ws sw :
    vwp_acq_r P ws ⊢ vwp_hold P (fence_post ws true false true sw).
  Proof. rewrite /vwp_acq_r /vwp_hold ws_view_fence_r //. Qed.

  Lemma vwp_acq_r_barrier P ws :
    vwp_acq_r P ws ⊢ vwp_hold P (barrier_post ws Barrier_RISCV_r_r).
  Proof. rewrite /vwp_acq_r /vwp_hold ws_view_barrier_r_r //. Qed.

  (** ... and the trivial direction: what the hart holds now, it holds at its
      frontier (so a fence never LOSES anything). *)
  Lemma vwp_hold_acq P ws : vwp_hold P ws ⊢ vwp_acq P ws.
  Proof. rewrite /vwp_hold /vwp_acq. by apply monPred_mono, ws_view_acq_view. Qed.

  Lemma vwp_acq_r_acq P ws : vwp_acq_r P ws ⊢ vwp_acq P ws.
  Proof. rewrite /vwp_acq_r /vwp_acq. by apply monPred_mono, acq_view_r_acq_view. Qed.

  (** THE INTRODUCTION FORM a leaf uses: an assertion frozen at a view the
      frontier covers is [∇]-held.  ([P @@ V] is objective, so this is where
      an invariant's payload enters.) *)
  Lemma vwp_acq_intro V P ws : V ⊑ acq_view ws → monPred_at P V ⊢ vwp_acq P ws.
  Proof. intros H. rewrite /vwp_acq. by apply monPred_mono. Qed.

  Lemma vwp_acq_r_intro V P ws :
    V ⊑ acq_view_r ws → monPred_at P V ⊢ vwp_acq_r P ws.
  Proof. intros H. rewrite /vwp_acq_r. by apply monPred_mono. Qed.

  Lemma vwp_acq_view_at P V ws : vwp_acq (P @@ V) ws ⊣⊢ monPred_at P V.
  Proof. apply monPred_at_embed. Qed.

  (** The structural laws — all [monPred_at] unfoldings, as at [vwp_hold]. *)
  Lemma vwp_acq_sep P Q ws :
    vwp_acq (P ∗ Q) ws ⊣⊢ vwp_acq P ws ∗ vwp_acq Q ws.
  Proof. apply monPred_at_sep. Qed.
  Lemma vwp_acq_exist {A} (Φ : A → vProp Σ) ws :
    vwp_acq (∃ x, Φ x) ws ⊣⊢ ∃ x, vwp_acq (Φ x) ws.
  Proof. apply monPred_at_exist. Qed.
  Lemma vwp_acq_pure (φ : Prop) ws : vwp_acq ⌜φ⌝ ws ⊣⊢ ⌜φ⌝.
  Proof. apply monPred_at_pure. Qed.
  Lemma vwp_acq_embed (R : iProp Σ) ws : vwp_acq ⎡R⎤ ws ⊣⊢ R.
  Proof. apply monPred_at_embed. Qed.

  (** THE READER-SIDE PACKAGE: an assertion deposited at the SCALAR view of a
      timestamp this hart has read is delivered by a succ-R fence.  (The
      premise [t ≤ w_vrOld ws] is what [WeakMem.load_post_vrOld_nofwd] leaves
      after reading timestamp [t].) *)
  Lemma fence_delivers_scl P ws t sw :
    (t ≤ w_vrOld ws)%nat →
    monPred_at P (view_scl t) ⊢ vwp_hold P (fence_post ws true false true sw).
  Proof.
    intros Ht. etrans; [|apply vwp_acq_r_fence].
    apply vwp_acq_r_intro. by apply view_scl_acq_vrOld.
  Qed.

End fence.

(* ====================================================================== *)
(** ** 3. The writer side: the release deposit

    [ws_bounded] (WeakMem) is the machine invariant that every view a hart
    holds is a real timestamp of the current log.  Its whole point is this:
    a store lands at [S (length log)], which therefore DOMINATES the whole of
    the releaser's index — so the releaser may freeze anything it holds at the
    single SCALAR view [view_scl (S (length log))], and that frozen assertion
    is objective, hence storable in an invariant.  This is the Decision-5
    scalar-deposit argument, as a lemma. *)

Lemma ws_bounded_view_scl ws n : ws_bounded ws n → ws_view ws ⊑ view_scl n.
Proof.
  intros Hb a. rewrite flr_ws_view flr_scl_eq. by apply ws_bounded_scl.
Qed.

Lemma ws_view_store_dom ws (log : list wmsg) :
  ws_bounded ws (length log) → ws_view ws ⊑ view_scl (S (length log)).
Proof.
  intros Hb a. rewrite flr_ws_view flr_scl_eq.
  pose proof (ws_bounded_scl ws (length log) Hb a). lia.
Qed.

Section release.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Implicit Types P : vProp Σ.

  (** THE DEPOSIT.  Everything the releaser holds becomes an OBJECTIVE
      [P @@ view_scl t] at the timestamp its store is about to take. *)
  Lemma release_deposit P ws (log : list wmsg) :
    ws_bounded ws (length log) →
    vwp_hold P ws ⊢ monPred_at P (view_scl (S (length log))).
  Proof.
    intros Hb. rewrite /vwp_hold. apply monPred_mono. by apply ws_view_store_dom.
  Qed.

  Lemma release_deposit_at P ws (log : list wmsg) :
    ws_bounded ws (length log) →
    vwp_hold P ws ⊢ vwp_hold (P @@ view_scl (S (length log))) ws.
  Proof. intros Hb. rewrite vwp_hold_view_at. by apply release_deposit. Qed.

End release.

(* ====================================================================== *)
(** ** 4. The AMO read half *)

(** THE ACQUIRE'S INDEX GAIN.  An acquire read of timestamp [t] raises the
    hart's SCALAR floor to [t] ([WeakMem.load_post_at_vrNew_aq]), so it
    delivers everything deposited at [view_scl t] — with no fence.  Note the
    scalar, not just the byte: that is the whole difference between an
    acquire and a plain load, and the reason the release deposit is a scalar
    view. *)
Lemma amo_acq_gain ws vpre a t :
  view_scl t ⊑ ws_view (load_post_at ws true vpre a t).
Proof.
  intros a'. rewrite flr_scl_eq flr_ws_view.
  pose proof (load_post_at_vrNew_aq ws vpre a t). lia.
Qed.

(** A PLAIN load gains the timestamp only at the BYTE it read (its coherence
    floor), which is what makes MP need the fence. *)
Lemma load_byte_gain ws aq vpre a t :
  view_byte a t ⊑ ws_view (load_post_at ws aq vpre a t).
Proof.
  apply view_byte_le. rewrite flr_ws_view.
  pose proof (load_post_at_coh ws aq vpre a t). lia.
Qed.

Section amo.
  Context `{!riscvGS Σ, !weakGS Σ}.

  (** THE AMO READ RULE, base altitude.  An [ak_latest] access (every
      exclusive/AMO read half — [WeakInterp]'s §3 table) must read the global
      latest write, so an element of the latest-write map pins BOTH the value
      and the timestamp — with NO hypothesis about the reader's views.  That
      is what lets the rule fire off an element held in an INVARIANT (the
      element is an [iProp], hence objective) rather than off an owned
      points-to, which is the M3-relevant form. *)
  Lemma wamo_read_latest σ ak (a : Z) (dq : dfrac) (t : nat) (v : bv 8)
      (t' : nat) (b : bv 8) :
    ak_coh ak = false →
    ak_latest ak = true →
    wbyte_ok σ ak a t' b →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    wlat_pointsto a dq t v -∗ ⌜t' = t ∧ b = v⌝.
  Proof.
    intros Hcoh Hlatk Hok. iIntros "Hi He".
    iDestruct (wlat_lookup with "Hi He") as %Hlat.
    destruct Hok as [Hv Hadm]. rewrite Hcoh in Hadm.
    destruct Hadm as [_ Hlt].
    iPureIntro.
    assert (Ht' : t' = t).
    { apply (latest_unique (wimg σ) (wm_log σ) a).
      - split; [by exists b|exact (Hlt Hlatk)].
      - exact (latest_val_latest _ _ _ _ _ Hlat). }
    split; [exact Ht'|]. destruct Hlat as [Hlv _].
    rewrite Ht' Hlv in Hv. by simplify_eq.
  Qed.

  (** ... and the owned form, at the [vProp] altitude: the AMO returns the
      value of the byte I own, and afterwards my index covers the message's
      timestamp — [amo_acq_gain] above is that second half, and it is what
      the acquire is FOR. *)
  Lemma wpt_amo_read σ ak (a : Z) (dq : dfrac) (v : bv 8) (t' : nat) (b : bv 8) :
    ak_coh ak = false →
    ak_latest ak = true →
    wbyte_ok σ ak a t' b →
    (wlat_interp (wm_img σ) (wm_log σ) : iProp Σ) -∗
    vwp_hold (a ↦w{dq} v) (wm_ws σ) -∗ ⌜b = v⌝.
  Proof.
    intros Hcoh Hlatk Hok. iIntros "Hi Hpt".
    rewrite wpt_at. iDestruct "Hpt" as (t) "[He _]".
    by iDestruct (wamo_read_latest σ ak a dq t v t' b Hcoh Hlatk Hok
                    with "Hi He") as %[_ ?].
  Qed.

  (** The post-state seen-assertion the acquire produces, in the form the
      surface layer consumes: after an acquire read of timestamp [t], the
      hart has observed the SCALAR view [view_scl t]. *)
  Lemma wpt_amo_seen ws vpre a t :
    ⊢ vwp_hold (⊒(view_scl t) : vProp Σ) (load_post_at ws true vpre a t).
  Proof. rewrite vwp_hold_seen. iPureIntro. apply amo_acq_gain. Qed.

End amo.

(* ====================================================================== *)
(** ** 5. THE HANDOFF — what M3 will quote

    Two shapes, one lemma each, both pure view arithmetic over §3 and §4. *)

Section handoff.
  Context `{!riscvGS Σ, !weakGS Σ}.
  Implicit Types P : vProp Σ.

  (** RELEASE → ACQUIRE (the spinlock).  Whatever the releasing hart held at
      its own index when its store took timestamp [S (length log)], the
      acquiring hart holds after an acquire-AMO that reads that timestamp.
      No invariant, no ghost state, no fence: this is the view content of the
      whole handoff. *)
  Lemma release_acquire_transfer P ws_r ws_a (log : list wmsg) vpre (a' : Z) :
    ws_bounded ws_r (length log) →
    vwp_hold P ws_r
    ⊢ vwp_hold P (load_post_at ws_a true vpre a' (S (length log))).
  Proof.
    intros Hb. etrans; [apply (release_deposit P ws_r log Hb)|].
    rewrite /vwp_hold. apply monPred_mono, amo_acq_gain.
  Qed.

  (** RELEASE → PLAIN READ + succ-R FENCE (the [started] escrow, MP).  The
      reader has READ the released timestamp — [t ≤ w_vrOld] is exactly what
      [WeakMem.load_post_vrOld_nofwd] gives it — and then fences. *)
  Lemma release_fence_transfer P ws_r ws_a (log : list wmsg) sw :
    ws_bounded ws_r (length log) →
    (S (length log) ≤ w_vrOld ws_a)%nat →
    vwp_hold P ws_r
    ⊢ vwp_hold P (fence_post ws_a true false true sw).
  Proof.
    intros Hb Ht. etrans; [apply (release_deposit P ws_r log Hb)|].
    by apply fence_delivers_scl.
  Qed.

End handoff.

(* ====================================================================== *)
(** ** 6. Smoke test: the MP shape, composed at the machine's own steps

    Not a theorem of record — the check that the pieces above compose over
    [WeakInterp]/[WeakMem]'s real post-state functions, with no glue.  The
    writer stores at the log's fresh top (so [store_post]); the reader reads
    that timestamp plainly ([load_post], whose [w_vrOld] then covers it) and
    fences.  What crosses is an arbitrary [P] the writer held. *)

Section mp_smoke.
  Context `{!riscvGS Σ, !weakGS Σ}.

  Example mp_transfer (P : vProp Σ) ws_w ws_r (log : list wmsg)
      (x y : Z) (rl : bool) vpre :
    ws_bounded ws_w (length log) →
    w_fwd ws_r = ∅ →
    vwp_hold P ws_w
    ⊢ vwp_hold P
        (fence_post (load_post_at ws_r false vpre y (S (length log)))
                    true false true false).
  Proof.
    intros Hb Hfwd.
    apply (release_fence_transfer P ws_w _ log); [exact Hb|].
    apply (load_post_at_vrOld_nofwd ws_r false vpre y (S (length log)) Hfwd).
  Qed.

  (** ... and the acquire variant, with no fence at all. *)
  Example mp_transfer_aq (P : vProp Σ) ws_w ws_r (log : list wmsg) (y : Z) vpre :
    ws_bounded ws_w (length log) →
    vwp_hold P ws_w
    ⊢ vwp_hold P (load_post_at ws_r true vpre y (S (length log))).
  Proof. intros Hb. by apply (release_acquire_transfer P ws_w _ log). Qed.

End mp_smoke.
