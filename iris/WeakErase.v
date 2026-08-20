(** * WeakErase.v — THE ERASURE SIMULATION (T2 carrier, A2 stage 1)

    Design: [claude-notes/design/weak-memory-srvwmo.md], the "THE T2 CARRIER
    PIPELINE (A2)" block, stage 1; worklist
    [claude-notes/projects/weak-memory-srvwmo.md] (A2).

    THE PROBLEM.  [WeakPromiseBridge]'s axiomatic projection
    ([wp_pf_step_mstep], and everything above it up to [wp_pf_bridge]) is
    gated on [lb_depfree]: the axiomatic tier steps with the
    DEPENDENCY-FREE [load_post_run]/[store_post_run], so a machine step that
    raises a view through an operand list has no [mstep] image with an equal
    post-state.  The D2 event instance FAILS that gate — its stores carry
    real [asrc]/[vsrc] and it emits the three dependency-only labels
    ([LRegW]/[LCtrl]/[LInstr]) outright — so T2 (every pf run projects to an
    sRVWMO execution) could not be stated for the instance at all.

    THE MOVE.  Erase the dependencies from the LABELS and simulate.
    [erase_lbl] blanks every operand list and sends the three
    dependency-only labels to [LSilent]; [erase_pstep] is the program LTS
    read through that map.  Every erased label is [lb_depfree] BY
    CONSTRUCTION, so the gate is discharged for free on the erased side, and
    the simulation below says the erased run exists and has the SAME LOG.
    Since the axiomatic tier only ever looks at the log (and the image, the
    program and the fabric — all preserved), that is exactly what T2 needs.

    WHY IT IS A ≤-SIMULATION AND NOT AN EQUALITY.  The erased run's agents
    are NOT in the same [wstate] as the instance's: dropping the operand
    lists lowers every dependency view to [0], and dropping [LInstr] leaves
    the erased agent's [w_ldv]/[w_res]/[w_tbank] un-reset.  What IS true is
    that every erased view is BELOW its instance counterpart ([er_ws]), and
    every side condition of the pf machine is ANTI-monotone in the views:

      - [readable]'s no-write window is [(t, vpre ⊔ coh a]] — a LOWER floor
        is a SMALLER window, hence a WEAKER condition
        ([WeakMem.writes_in_mono_hi]);
      - [read_ok_d]'s [lat] conjunct, [excl_ok] and [excl_ok_ts] are
        LOG-ONLY, and the log is equal;
      - the pf fragment has NO [fulfil_ok] at all (both write arms append at
        the fresh top), so the whole fulfil pre-view — [w_vcap], [w_vwNew],
        [rv_view] — never appears in a side condition.

    So every instance step erases, which is the direction T2 wants.

    THE FOUR COMPONENTS OF [er_ws], each with its reason:

    - [ws_le] (the monotone views: [coh], the four floors, [w_vRel],
      [w_pub], [w_vcap]) — erased ≤ instance, as above.
    - [w_relp] EQUAL.  It is a toggle, not a view, and it is moved by the
      FENCE bits and by stores — data the erasure preserves — so equality is
      maintained.  It is load-bearing twice: [w_pub]'s monotonicity needs the
      two sides to take the same branch, and the MESSAGE CLASS is a function
      of it (see [pcls_erasable]).
    - [fwd_le] (the forward bank, semantically): [fwd_view we ≤ fwd_view wi]
      pointwise.  Post-D-7 [store_post_d] banks [(t, V(asrc) ⊔ V(vsrc))], so
      the erased side banks [(t, 0)] where the instance banks [(t, vf)] —
      the TIMESTAMP column agrees (both sides store at the same fresh top),
      only the view column drops, and it drops in the sound direction.  This
      is why the A1a probe's [dep_dom] invariant is NOT needed here: the
      ≤-simulation absorbs the bank residue directly, whereas [dep_dom] was
      the machinery for the abandoned route that had to prove the residue
      ZERO.
    - [res_rel] (the reservation): instance [Some R] ⟹ erased [Some R'] with
      the SAME [rv_base] and [rv_ts] (both are label data, which the erasure
      preserves) and [rv_view R' ≤ rv_view R].  The implication is ONE-WAY on
      purpose: [LInstr] erases to [LSilent], so the instance clears [w_res]
      where the erased side keeps it.  An [LExStore] fires only where the
      INSTANCE holds a reservation, and there the erased side holds a
      matching one, which is all [PFExStore] asks.

    WHAT IS *NOT* DONE HERE.  [lb_fused] is stage 2's gate (re-fusion): the
    erasure keeps [LExLoad]/[LExStore] as they are.  Stage 3 is the existing
    projection. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem.
From xv6iris Require Import WeakAxiomatic.
From xv6iris Require Import WeakPromise.
From xv6iris Require Import WeakPromiseFact.
From xv6iris Require Import WeakPromiseBridge.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** ** 1. The label erasure *)

(** Blank every operand list; send the three dependency-only labels to
    [LSilent].  Everything else — the [aq]/[rl]/[lat] bits, the base, the
    read timestamps/values, the written data, the fence bits — is kept
    VERBATIM, which is what makes the log, the message classes and the
    axiomatic projection agree on the nose. *)
Definition erase_lbl (l : wlabel) : wlabel :=
  match l with
  | LSilent => LSilent
  | LLoad aq lat base tvs _ => LLoad aq lat base tvs []
  | LStore rl base data _ _ => LStore rl base data [] []
  | LRmw aq rl base tvs data _ _ => LRmw aq rl base tvs data [] []
  | LFence pr pw sr sw => LFence pr pw sr sw
  | LDev => LDev
  | LRegW _ _ => LSilent
  | LCtrl _ => LSilent
  | LInstr => LSilent
  | LExLoad aq base tvs _ => LExLoad aq base tvs []
  | LExStore rl base data _ _ => LExStore rl base data [] []
  end.

(** THE POINT: the gate [WeakPromiseBridge]'s projection asks for holds of
    every erased label BY CONSTRUCTION. *)
Lemma erase_lbl_depfree l : lb_depfree (erase_lbl l).
Proof. by destruct l. Qed.

(** On the dependency-free fragment the erasure is the identity, so it does
    not disturb any producer that already satisfied the gate. *)
Lemma erase_lbl_depfree_id l : lb_depfree l → erase_lbl l = l.
Proof.
  destruct l; simpl; by [|intros ->|intros [-> ->]].
Qed.

Lemma erase_lbl_idem l : erase_lbl (erase_lbl l) = erase_lbl l.
Proof. apply erase_lbl_depfree_id, erase_lbl_depfree. Qed.

(** The other two alphabet gates ride through: the [lat] bit and the
    fused/split shape are label data the erasure copies. *)
Lemma erase_lbl_lat_free l : lat_free l → lat_free (erase_lbl l).
Proof. by destruct l. Qed.

Lemma erase_lbl_fused l : lb_fused l → lb_fused (erase_lbl l).
Proof. by destruct l. Qed.

Lemma erase_lbl_ldepfree l : lb_ldepfree (erase_lbl l).
Proof. by destruct l. Qed.

(* ====================================================================== *)
(** ** 2. The state relation *)

(** The forward bank, SEMANTICALLY: what a read of timestamp [t] at byte [a]
    takes away from the bank.  Stating it at the read view rather than at the
    map means the one lemma [store_post_d_er] discharges it for every later
    consumer, and it is exactly the form [load_post_at] uses. *)
Definition fwd_le (we wi : wstate) : Prop :=
  ∀ aq a t, (fwd_view we aq a t ≤ fwd_view wi aq a t)%nat.

Global Instance fwd_le_refl : Reflexive fwd_le.
Proof. intros w aq a t. lia. Qed.

(** The reservation, ONE-WAY (see the header): wherever the INSTANCE holds a
    reservation the erased side holds one with the same base and the same
    timestamp column — the two things [PFExStore] checks — and a lower banked
    view. *)
Definition res_rel (we wi : wstate) : Prop :=
  ∀ Ri, w_res wi = Some Ri →
    ∃ Re, w_res we = Some Re ∧ rv_base Re = rv_base Ri ∧
          rv_ts Re = rv_ts Ri ∧ (rv_view Re ≤ rv_view Ri)%nat.

Global Instance res_rel_refl : Reflexive res_rel.
Proof. intros w R HR. exists R. by split_and!. Qed.

(** THE ERASURE'S STATE RELATION: [er_ws we wi] — "[we] (the ERASED agent's
    state) is below [wi] (the INSTANCE agent's)". *)
Definition er_ws (we wi : wstate) : Prop :=
  ws_le we wi ∧ w_relp we = w_relp wi ∧ fwd_le we wi ∧ res_rel we wi.

Lemma er_ws_ws_le we wi : er_ws we wi → ws_le we wi.
Proof. by intros (? & _). Qed.
Lemma er_ws_relp we wi : er_ws we wi → w_relp we = w_relp wi.
Proof. by intros (_ & ? & _). Qed.
Lemma er_ws_fwd we wi : er_ws we wi → fwd_le we wi.
Proof. by intros (_ & _ & ? & _). Qed.
Lemma er_ws_res we wi : er_ws we wi → res_rel we wi.
Proof. by intros (_ & _ & _ & ?). Qed.

Global Instance er_ws_refl : Reflexive er_ws.
Proof. intros w. by split_and!. Qed.

(** Transitive because each of its four components is: [ws_le] by its own
    instance, [w_relp] because it is an equation, and [fwd_le]/[res_rel]
    pointwise.  Stage 2 ([WeakRefuse]) composes a one-sided step of the
    instance side onto the relation with it. *)
Global Instance er_ws_trans : Transitive er_ws.
Proof.
  intros w1 w2 w3 (Hle1 & Hrp1 & Hfw1 & Hrs1) (Hle2 & Hrp2 & Hfw2 & Hrs2).
  split_and!.
  - by etrans.
  - by etrans.
  - intros aq a t. etrans; [apply Hfw1|apply Hfw2].
  - intros R3 HR3. destruct (Hrs2 R3 HR3) as (R2 & HR2 & Hb2 & Ht2 & Hv2).
    destruct (Hrs1 R2 HR2) as (R1 & HR1 & Hb1 & Ht1 & Hv1).
    exists R1. split_and!; [done|by rewrite Hb1|by rewrite Ht1|lia].
Qed.

(** The [load_vpre]/[coh] consequences the read arms consume. *)
Lemma er_ws_load_vpre_d we wi aq vae vai :
  er_ws we wi → (vae ≤ vai)%nat →
  (load_vpre_d we aq vae ≤ load_vpre_d wi aq vai)%nat.
Proof.
  intros Her Hv. pose proof (ws_le_vrNew _ _ (er_ws_ws_le _ _ Her)).
  pose proof (ws_le_vRel _ _ (er_ws_ws_le _ _ Her)).
  rewrite /load_vpre_d /load_vpre. destruct aq; lia.
Qed.

(* ---------------------------------------------------------------------- *)
(** *** Readability and the read side condition are ANTI-monotone

    THE POLARITY, spelled out because it is the crux: [readable] forbids a
    write in the window [(t, vpre ⊔ coh a]].  Lowering [vpre] or [coh]
    SHRINKS the window, so FEWER writes can block the read — the erased agent
    can read everything the instance agent can. *)
Lemma readable_er img log we wi vpe vpi a t :
  (coh we a ≤ coh wi a)%nat → (vpe ≤ vpi)%nat →
  readable img log wi vpi a t → readable img log we vpe a t.
Proof.
  intros Hc Hv [Hs Hn]. split; [done|].
  intros Hw. apply Hn. eapply writes_in_mono_hi; [|exact Hw]. lia.
Qed.

Lemma read_ok_d_er img log we wi aq lat base tvs vae vai :
  er_ws we wi → (vae ≤ vai)%nat →
  read_ok_d img log wi aq lat base tvs vai →
  read_ok_d img log we aq lat base tvs vae.
Proof.
  intros Her Hv Hr j t v Hj. destruct (Hr j t v Hj) as (H1 & H2 & H3).
  split_and!; [done| |done].
  eapply readable_er; [|exact (er_ws_load_vpre_d _ _ aq _ _ Her Hv)|exact H2].
  exact (ws_le_coh _ _ _ (er_ws_ws_le _ _ Her)).
Qed.

(* ---------------------------------------------------------------------- *)
(** *** [er_ws] is preserved by every step function

    All eight lemmas are "the two sides run the SAME update at possibly
    different dependency views"; the two one-sided ones ([_r]) are the
    divergences the erasure introduces, where the instance moves and the
    erased side does not. *)

Lemma load_post_at_er we wi aq vpe vpi a t :
  er_ws we wi → (vpe ≤ vpi)%nat →
  er_ws (load_post_at we aq vpe a t) (load_post_at wi aq vpi a t).
Proof.
  intros Her Hv.
  pose proof (er_ws_ws_le _ _ Her) as Hle.
  pose proof (er_ws_fwd _ _ Her aq a t) as Hf.
  have Hvp : (Nat.max vpe (fwd_view we aq a t)
              ≤ Nat.max vpi (fwd_view wi aq a t))%nat by lia.
  destruct Hle as (Hcoh & HrO & HwO & HrN & HwN & HrL & Hpub & Hcap).
  split_and!; [split_and!| | |].
  - intros a'.
    have Hca : ∀ x, (default 0%nat (w_coh we !! x)
                     ≤ default 0%nat (w_coh wi !! x))%nat.
    { intros x. exact (Hcoh x). }
    rewrite /load_post_at /coh /=.
    destruct (decide (a' = a)) as [->|Hne].
    + rewrite !lookup_insert /=. pose proof (Hca a). lia.
    + rewrite !lookup_insert_ne //; exact (Hca a').
  - simpl. lia.
  - simpl. lia.
  - simpl. destruct aq; lia.
  - simpl. destruct aq; lia.
  - simpl. lia.
  - simpl. lia.
  - simpl. lia.
  - exact (er_ws_relp _ _ Her).
  - exact (er_ws_fwd _ _ Her).
  - exact (er_ws_res _ _ Her).
Qed.

Lemma load_post_at_ldv_er we wi aq vpe vpi a t :
  er_ws we wi → (vpe ≤ vpi)%nat → (w_ldv we ≤ w_ldv wi)%nat →
  (w_ldv (load_post_at we aq vpe a t)
   ≤ w_ldv (load_post_at wi aq vpi a t))%nat.
Proof.
  intros Her Hv Hldv. pose proof (er_ws_fwd _ _ Her aq a t). simpl. lia.
Qed.

Lemma load_post_fold_er aq vpe vpi ats we wi :
  er_ws we wi → (vpe ≤ vpi)%nat →
  er_ws (foldl (λ w at_, load_post_at w aq vpe at_.1 at_.2) we ats)
        (foldl (λ w at_, load_post_at w aq vpi at_.1 at_.2) wi ats).
Proof.
  revert we wi. induction ats as [|at_ l IH]; intros we wi Her Hv; [done|].
  simpl. apply IH; [by apply load_post_at_er|done].
Qed.

Lemma load_post_fold_ldv_er aq vpe vpi ats we wi :
  er_ws we wi → (vpe ≤ vpi)%nat → (w_ldv we ≤ w_ldv wi)%nat →
  (w_ldv (foldl (λ w at_, load_post_at w aq vpe at_.1 at_.2) we ats)
   ≤ w_ldv (foldl (λ w at_, load_post_at w aq vpi at_.1 at_.2) wi ats))%nat.
Proof.
  revert we wi. induction ats as [|at_ l IH]; intros we wi Her Hv Hldv; [done|].
  simpl. apply IH; [by apply load_post_at_er|done|by apply load_post_at_ldv_er].
Qed.

Lemma store_post_d_er we wi rl vfe vfi a t :
  er_ws we wi → (vfe ≤ vfi)%nat →
  er_ws (store_post_d we rl vfe a t) (store_post_d wi rl vfi a t).
Proof.
  intros Her Hv.
  pose proof (er_ws_ws_le _ _ Her) as Hle.
  pose proof (er_ws_relp _ _ Her) as Hrp.
  destruct Hle as (Hcoh & HrO & HwO & HrN & HwN & HrL & Hpub & Hcap).
  split_and!; [split_and!| | |].
  - intros a'.
    have Hca : ∀ x, (default 0%nat (w_coh we !! x)
                     ≤ default 0%nat (w_coh wi !! x))%nat.
    { intros x. exact (Hcoh x). }
    rewrite /store_post_d /coh /=.
    destruct (decide (a' = a)) as [->|Hne].
    + rewrite !lookup_insert /=. pose proof (Hca a). lia.
    + rewrite !lookup_insert_ne //; exact (Hca a').
  - simpl. lia.
  - simpl. lia.
  - simpl. lia.
  - simpl. lia.
  - simpl. destruct rl; lia.
  - simpl. rewrite Hrp. destruct (w_relp wi), rl; simpl; lia.
  - simpl. lia.
  - done.
  - intros aq' a' t'. rewrite /fwd_view /store_post_d /=.
    destruct aq'; [lia|].
    destruct (decide (a' = a)) as [->|Hne].
    + rewrite !lookup_insert /=. case_bool_decide; [lia|lia].
    + rewrite !lookup_insert_ne //. exact (er_ws_fwd _ _ Her false a' t').
  - by intros Ri HR.
Qed.

Lemma store_post_fold_er rl vfe vfi t as_ we wi :
  er_ws we wi → (vfe ≤ vfi)%nat →
  er_ws (foldl (λ w a, store_post_d w rl vfe a t) we as_)
        (foldl (λ w a, store_post_d w rl vfi a t) wi as_).
Proof.
  revert we wi. induction as_ as [|a l IH]; intros we wi Her Hv; [done|].
  simpl. apply IH; [by apply store_post_d_er|done].
Qed.

Lemma ctrl_post_er we wi ve vi :
  er_ws we wi → (ve ≤ vi)%nat → er_ws (ctrl_post we ve) (ctrl_post wi vi).
Proof.
  intros Her Hv. pose proof (er_ws_ws_le _ _ Her) as Hle.
  destruct Hle as (Hcoh & HrO & HwO & HrN & HwN & HrL & Hpub & Hcap).
  split_and!; [split_and!| | |]; try (simpl; lia).
  - exact Hcoh.
  - exact (er_ws_relp _ _ Her).
  - exact (er_ws_fwd _ _ Her).
  - exact (er_ws_res _ _ Her).
Qed.

Lemma fence_post_er we wi pr pw sr sw :
  er_ws we wi → er_ws (fence_post we pr pw sr sw) (fence_post wi pr pw sr sw).
Proof.
  intros Her. pose proof (er_ws_ws_le _ _ Her) as Hle.
  pose proof (er_ws_relp _ _ Her) as Hrp.
  destruct Hle as (Hcoh & HrO & HwO & HrN & HwN & HrL & Hpub & Hcap).
  split_and!; [split_and!| | |].
  - exact Hcoh.
  - simpl. lia.
  - simpl. lia.
  - simpl. destruct sr, pr, pw; lia.
  - simpl. destruct sw, pr, pw; lia.
  - simpl. lia.
  - simpl. lia.
  - simpl. lia.
  - simpl. destruct (pw && sw)%bool; [done|exact Hrp].
  - exact (er_ws_fwd _ _ Her).
  - exact (er_ws_res _ _ Her).
Qed.

Lemma instr_post_er we wi : er_ws we wi → er_ws (instr_post we) (instr_post wi).
Proof.
  intros Her. pose proof (er_ws_ws_le _ _ Her) as Hle.
  destruct Hle as (Hcoh & HrO & HwO & HrN & HwN & HrL & Hpub & Hcap).
  split_and!; [split_and!| | |]; try (simpl; lia).
  - exact Hcoh.
  - exact (er_ws_relp _ _ Her).
  - exact (er_ws_fwd _ _ Her).
  - by intros Ri HR.
Qed.

(** THE THREE ONE-SIDED (divergence) LEMMAS: the erased side takes a
    [PFSilent] where the instance takes a dependency-only arm. *)
Lemma er_ws_regw_r we wi rd v : er_ws we wi → er_ws we (regw_post wi rd v).
Proof.
  intros Her. pose proof (er_ws_ws_le _ _ Her) as Hle.
  destruct Hle as (Hcoh & HrO & HwO & HrN & HwN & HrL & Hpub & Hcap).
  split_and!; [split_and!| | |]; try (simpl; lia).
  - exact Hcoh.
  - exact (er_ws_relp _ _ Her).
  - exact (er_ws_fwd _ _ Her).
  - exact (er_ws_res _ _ Her).
Qed.

Lemma er_ws_ctrl_r we wi v : er_ws we wi → er_ws we (ctrl_post wi v).
Proof.
  intros Her. pose proof (er_ws_ws_le _ _ Her) as Hle.
  destruct Hle as (Hcoh & HrO & HwO & HrN & HwN & HrL & Hpub & Hcap).
  split_and!; [split_and!| | |]; try (simpl; lia).
  - exact Hcoh.
  - exact (er_ws_relp _ _ Her).
  - exact (er_ws_fwd _ _ Her).
  - exact (er_ws_res _ _ Her).
Qed.

(** [LInstr] ↦ [LSilent] is the ONE place [res_rel]'s one-wayness is used:
    the instance clears its reservation and the erased side keeps whatever it
    had, which the [∀ Ri, w_res wi = Some Ri → …] shape allows. *)
Lemma er_ws_instr_r we wi : er_ws we wi → er_ws we (instr_post wi).
Proof.
  intros Her. pose proof (er_ws_ws_le _ _ Her) as Hle.
  destruct Hle as (Hcoh & HrO & HwO & HrN & HwN & HrL & Hpub & Hcap).
  split_and!; [split_and!| | |]; try (simpl; lia).
  - exact Hcoh.
  - exact (er_ws_relp _ _ Her).
  - exact (er_ws_fwd _ _ Her).
  - by intros Ri HR.
Qed.

(* ---------------------------------------------------------------------- *)
(** *** The RUN-level wrappers the machine arms actually apply *)

Lemma load_post_run_d_er we wi aq vae vai base ts :
  er_ws we wi → (vae ≤ vai)%nat →
  er_ws (load_post_run_d we aq vae base ts)
        (load_post_run_d wi aq vai base ts).
Proof.
  intros Her Hv. rewrite /load_post_run_d.
  apply ctrl_post_er; [|done].
  rewrite /load_post_bytes_d.
  apply load_post_fold_er; [done|by apply er_ws_load_vpre_d].
Qed.

Lemma store_post_run_d_er we wi rl vae vai vde vdi base n t :
  er_ws we wi → (vae ≤ vai)%nat → (vde ≤ vdi)%nat →
  er_ws (store_post_run_d we rl vae vde base n t)
        (store_post_run_d wi rl vai vdi base n t).
Proof.
  intros Her Ha Hd. rewrite /store_post_run_d.
  apply ctrl_post_er; [|done].
  rewrite /store_post_bytes_d. apply store_post_fold_er; [done|lia].
Qed.

(** The reservation's banked view.  [ldv_of] is computed from a ZEROED
    [w_ldv] ([ws_ldv0 = instr_post]), which is what makes this provable at
    all: [w_ldv] itself is NOT related by [er_ws] (the erasure drops the
    [LInstr] that resets it), but both sides' [ldv_of] start from [0]. *)
Lemma ldv_of_er we wi aq vae vai base ts :
  er_ws we wi → (vae ≤ vai)%nat →
  (ldv_of we aq vae base ts ≤ ldv_of wi aq vai base ts)%nat.
Proof.
  intros Her Hv. rewrite /ldv_of /load_post_run_d /ws_ldv0 /=.
  rewrite /load_post_bytes_d.
  apply load_post_fold_ldv_er; [by apply instr_post_er| |done].
  apply er_ws_load_vpre_d; [by apply instr_post_er|done].
Qed.

Lemma exload_post_run_d_er we wi aq vae vai base ts :
  er_ws we wi → (vae ≤ vai)%nat →
  er_ws (exload_post_run_d we aq vae base ts)
        (exload_post_run_d wi aq vai base ts).
Proof.
  intros Her Hv.
  pose proof (load_post_run_d_er we wi aq vae vai base ts Her Hv) as Hl.
  destruct Hl as (Hle & Hrp & Hfw & _).
  rewrite /exload_post_run_d. split_and!.
  - exact Hle.
  - exact Hrp.
  - exact Hfw.
  - intros Ri HR. rewrite ws_res_set_res in HR. simplify_eq.
    exists (WResv base ts (ldv_of we aq vae base ts)).
    split_and!; [by rewrite ws_res_set_res|done|done|].
    by apply ldv_of_er.
Qed.

(* ---------------------------------------------------------------------- *)
(** *** The AT-ZERO instances the machine arms actually meet

    The erased label carries [asrc = vsrc = []] and [WeakMem.srcs_view_nil]
    makes [srcs_view ws [] = 0] hold BY CONVERSION, so every erased arm asks
    for its side condition / post-state at dependency view [0].  Naming the
    specializations keeps the simulation's arms one-liners. *)

Lemma read_ok_d_er0 img log we wi aq lat base tvs vai :
  er_ws we wi → read_ok_d img log wi aq lat base tvs vai →
  read_ok_d img log we aq lat base tvs 0%nat.
Proof. intros Her Hr. eapply read_ok_d_er; [exact Her|apply Nat.le_0_l|exact Hr]. Qed.

Lemma load_post_run_d_er0 we wi aq vai base ts :
  er_ws we wi →
  er_ws (load_post_run_d we aq 0%nat base ts)
        (load_post_run_d wi aq vai base ts).
Proof. intros Her. apply load_post_run_d_er; [done|apply Nat.le_0_l]. Qed.

Lemma store_post_run_d_er0 we wi rl vai vdi base n t :
  er_ws we wi →
  er_ws (store_post_run_d we rl 0%nat 0%nat base n t)
        (store_post_run_d wi rl vai vdi base n t).
Proof.
  intros Her. apply store_post_run_d_er; [done|apply Nat.le_0_l|apply Nat.le_0_l].
Qed.

Lemma exload_post_run_d_er0 we wi aq vai base ts :
  er_ws we wi →
  er_ws (exload_post_run_d we aq 0%nat base ts)
        (exload_post_run_d wi aq vai base ts).
Proof. intros Her. apply exload_post_run_d_er; [done|apply Nat.le_0_l]. Qed.

(* ====================================================================== *)
(** ** 3. The erased machine and the configuration relation *)

Section erase.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pcls : P → wlabel → wstate → wm_class).

  (** THE ERASED PROGRAM LTS.  Carrying the original label existentially is
      what keeps the erased side a genuine LTS over the SAME program states:
      nothing about [P], [D] or the program's own transitions changes, only
      the alphabet the machine sees.  ([erase_lbl] is not injective — the
      three dependency-only labels collapse onto [LSilent] — so the erased
      LTS is a genuine abstraction and not a renaming.) *)
  Definition erase_pstep (p : P) (d : D) (l : wlabel) (p' : P) (d' : D)
      : Prop := ∃ l0, l = erase_lbl l0 ∧ pstep p d l0 p' d'.

  Lemma erase_pstep_intro p d l p' d' :
    pstep p d l p' d' → erase_pstep p d (erase_lbl l) p' d'.
  Proof. intros H. by exists l. Qed.

  (** THE GATE, DISCHARGED BY CONSTRUCTION — the whole point of stage 1. *)
  Lemma erase_pstep_depfree : pstep_depfree erase_pstep.
  Proof. intros p d l p' d' (l0 & -> & _). apply erase_lbl_depfree. Qed.

  (** The other two alphabet premises are INHERITED (not discharged): the
      erasure copies the [lat] bit and the fused/split shape. *)
  Lemma erase_pstep_lat_free :
    (∀ p d l p' d', pstep p d l p' d' → lat_free l) →
    ∀ p d l p' d', erase_pstep p d l p' d' → lat_free l.
  Proof.
    intros H p d l p' d' (l0 & -> & Hs). by apply erase_lbl_lat_free, (H p d l0 p' d').
  Qed.

  Lemma erase_pstep_fused : pstep_fused pstep → pstep_fused erase_pstep.
  Proof.
    intros H p d l p' d' (l0 & -> & Hs).
    by apply erase_lbl_fused, (H p d l0 p' d').
  Qed.

  (** THE THREE ALPHABET GATES IN ONE PLACE — the same three
      [WeakAxRealize.lbl_realizes] names on T1's side.  [lb_depfree] is
      DISCHARGED here (that is stage 1's whole content); [lat_free] and
      [lb_fused] are INHERITED from the instance, the latter only until
      stage 2 (re-fusion) removes it. *)
  Lemma erase_pstep_gates :
    (∀ p d l p' d', pstep p d l p' d' → lat_free l) → pstep_fused pstep →
    pstep_depfree erase_pstep ∧ pstep_fused erase_pstep ∧
    (∀ p d l p' d', erase_pstep p d l p' d' → lat_free l).
  Proof.
    intros Hlf Hfu. split_and!;
      [apply erase_pstep_depfree|by apply erase_pstep_fused
      |by apply erase_pstep_lat_free].
  Qed.

  (** THE MESSAGE-CLASS PREMISE.  The erased run must append the SAME
      messages, so the class the erased agent computes must be the class the
      instance agent computed — at a BLANKED label and at a DIFFERENT (lower)
      [wstate].  Layer 1's [pcls] is abstract, so this has to be a hypothesis;
      it says exactly that the class does not read the operand lists and reads
      the state only through [w_relp], which is what the event instance's
      [WeakEvInst.pcls_ev] does ([WeakInterp.wm_class_of] = the ACCESS KIND
      plus [w_relp ws], and the access kind is program data, not label data).

      It cannot be weakened to "[pcls] commutes with [erase_lbl]" alone: the
      two sides' [wstate]s genuinely differ, so the state argument has to be
      quantified too, and [w_relp] equality is the strongest thing [er_ws]
      offers about it. *)
  Definition pcls_erasable : Prop :=
    ∀ p l we wi, w_relp we = w_relp wi → pcls p (erase_lbl l) we = pcls p l wi.

  (* -------------------------------------------------------------------- *)
  (** *** The configuration relation *)

  Definition er_ag (age agi : wpagent P) : Prop :=
    pa_st age = pa_st agi ∧ pa_prom age = pa_prom agi ∧
    er_ws (pa_ws age) (pa_ws agi).

  (** [er_cfg ce c] — "[ce] (the ERASED configuration) simulates [c]".  The
      three SHARED components are EQUAL: the image, THE LOG (this is the
      conclusion T2 consumes) and the device fabric.  Per agent: the same
      program state, the same promise set (both empty on the pf fragment,
      but stated generally) and [er_ws] on the [wstate]. *)
  Definition er_cfg (ce c : wpcfg P D) : Prop :=
    pc_img ce = pc_img c ∧ pc_log ce = pc_log c ∧ pc_dev ce = pc_dev c ∧
    length (pc_ags ce) = length (pc_ags c) ∧
    (∀ i agi, pc_ags c !! i = Some agi →
       ∃ age, pc_ags ce !! i = Some age ∧ er_ag age agi).

  Lemma er_cfg_log ce c : er_cfg ce c → pc_log ce = pc_log c.
  Proof. by intros (_ & ? & _). Qed.

  Lemma er_cfg_img ce c : er_cfg ce c → pc_img ce = pc_img c.
  Proof. by intros (? & _). Qed.

  Lemma er_cfg_dev ce c : er_cfg ce c → pc_dev ce = pc_dev c.
  Proof. by intros (_ & _ & ? & _). Qed.

  Lemma er_cfg_init img d0 (ps : list P) :
    er_cfg (wp_init img d0 ps) (wp_init img d0 ps).
  Proof.
    split_and!; [done|done|done|done|].
    intros i agi Hlk. exists agi. split; [done|]. by split_and!.
  Qed.

  (** The one configuration-update lemma every arm of the simulation uses. *)
  Lemma er_cfg_upd (imge img : image) (lge lg : list wmsg) (dv : D)
      (agse ags : list (wpagent P)) i age agi st' wse wsi pr :
    imge = img → lge = lg →
    length agse = length ags →
    (∀ j agj, ags !! j = Some agj →
       ∃ agej, agse !! j = Some agej ∧ er_ag agej agj) →
    ags !! i = Some agi → agse !! i = Some age →
    er_ws wse wsi →
    er_cfg (WPCfg imge lge dv (<[i := WPAgent st' wse pr]> agse))
           (WPCfg img lg dv (<[i := WPAgent st' wsi pr]> ags)).
  Proof.
    intros -> -> Hlen Hags Hi Hie Her.
    pose proof (lookup_lt_Some _ _ _ Hi) as Hlti.
    pose proof (lookup_lt_Some _ _ _ Hie) as Hltie.
    split_and!; [done|done|done| |].
    { rewrite /= !length_insert //. }
    intros j agj Hj. simpl in Hj |- *.
    destruct (decide (j = i)) as [->|Hne].
    - rewrite list_lookup_insert in Hj; [done|]. simplify_eq/=.
      eexists. rewrite list_lookup_insert; [done|]. split; [done|].
      by split_and!.
    - rewrite list_lookup_insert_ne // in Hj.
      destruct (Hags j agj Hj) as (agej & Hlk & Hrel).
      exists agej. rewrite list_lookup_insert_ne //.
  Qed.

  (* ==================================================================== *)
  (** ** 4. THE STEP SIMULATION *)

  (** Every instance step erases.  The erased label is [erase_lbl l]; the
      erased configuration keeps the log, the image, the fabric and the
      program states, and its views stay below.

      No arm needs a side condition the erased side cannot meet: the read
      arms weaken by [read_ok_d_er], the write arms carry NO fulfil check on
      the pf fragment, [excl_ok]/[excl_ok_ts] are log-only (and the
      reservation's timestamp column is equal), and the class is pinned by
      [pcls_erasable]. *)
  Lemma erase_step i l c c' ce :
    pcls_erasable →
    er_cfg ce c → wp_pf_step pstep pcls i l c c' →
    ∃ ce', wp_pf_step erase_pstep pcls i (erase_lbl l) ce ce' ∧ er_cfg ce' c'.
  Proof.
    intros Hcls Hm Hstep.
    destruct Hm as (Himg & Hlog & Hdev & Hlen & Hags).
    destruct Hstep as
      [cfg ag st' d' Hlk Hps
      |cfg ag aq lat base tvs asrc st' d' Hlk Hps Hr
      |cfg ag rl base data asrc vsrc k st' d' Hlk Hps Hnn Hk
      |cfg ag aq rl base tvs data asrc vsrc k st' d' Hlk Hps Hnn Hlen' Hr He Hk
      |cfg ag pr pw sr sw st' d' Hlk Hps|cfg ag st' d' Hlk Hps
      |cfg ag rd srcs st' d' Hlk Hps|cfg ag srcs st' d' Hlk Hps
      |cfg ag st' d' Hlk Hps
      |cfg ag aq base tvs asrc st' d' Hlk Hps Hr
      |cfg ag rl base data asrc vsrc k R st' d'
         Hlk Hps Hnn Hres Hrb Hrlen He Hk];
      destruct (Hags i ag Hlk) as (age & Hlke & Hst & Hpr & Hws).
    - (* LSilent *)
      eexists. split.
      + apply (PFSilent _ _ _ ce age st' d' Hlke).
        rewrite Hst Hdev. by apply (erase_pstep_intro _ _ LSilent).
      + rewrite Hpr. eapply er_cfg_upd;
          [exact Himg|exact Hlog|exact Hlen|exact Hags|exact Hlk|exact Hlke
          |exact Hws].
    - (* LLoad *)
      eexists. split.
      + apply (PFLoad _ _ _ ce age aq lat base tvs [] st' d' Hlke).
        * rewrite Hst Hdev.
          by apply (erase_pstep_intro _ _ (LLoad aq lat base tvs asrc)).
        * rewrite Himg Hlog. eapply read_ok_d_er0; [exact Hws|exact Hr].
      + rewrite Hpr. eapply er_cfg_upd;
          [exact Himg|exact Hlog|exact Hlen|exact Hags|exact Hlk|exact Hlke|].
        by apply load_post_run_d_er0.
    - (* LStore: the class is pinned by [pcls_erasable] *)
      have Hkk : pcls (pa_st age) (LStore rl base data [] []) (pa_ws age) = k.
      { rewrite Hst Hk.
        by apply (Hcls (pa_st ag) (LStore rl base data asrc vsrc)),
                 (er_ws_relp _ _ Hws). }
      eexists. split.
      + apply (PFStore _ _ _ ce age rl base data [] [] k st' d' Hlke);
          [|done|by rewrite Hkk].
        rewrite Hst Hdev.
        by apply (erase_pstep_intro _ _ (LStore rl base data asrc vsrc)).
      + rewrite Hpr. eapply er_cfg_upd;
          [exact Himg| |exact Hlen|exact Hags|exact Hlk|exact Hlke|].
        * by rewrite Hlog.
        * rewrite Hlog. by apply store_post_run_d_er0.
    - (* LRmw *)
      have Hkk : pcls (pa_st age) (LRmw aq rl base tvs data [] []) (pa_ws age)
                 = k.
      { rewrite Hst Hk.
        by apply (Hcls (pa_st ag) (LRmw aq rl base tvs data asrc vsrc)),
                 (er_ws_relp _ _ Hws). }
      eexists. split.
      + apply (PFRmw _ _ _ ce age aq rl base tvs data [] [] k st' d' Hlke);
          [| |done| | |by rewrite Hkk].
        * rewrite Hst Hdev.
          by apply (erase_pstep_intro _ _ (LRmw aq rl base tvs data asrc vsrc)).
        * done.
        * rewrite Himg Hlog. eapply read_ok_d_er0; [exact Hws|exact Hr].
        * rewrite Hlog. exact He.
      + rewrite Hpr. eapply er_cfg_upd;
          [exact Himg| |exact Hlen|exact Hags|exact Hlk|exact Hlke|].
        * by rewrite Hlog.
        * rewrite Hlog. apply store_post_run_d_er0.
          by apply load_post_run_d_er0.
    - (* LFence *)
      eexists. split.
      + apply (PFFence _ _ _ ce age pr pw sr sw st' d' Hlke).
        rewrite Hst Hdev. by apply (erase_pstep_intro _ _ (LFence pr pw sr sw)).
      + rewrite Hpr. eapply er_cfg_upd;
          [exact Himg|exact Hlog|exact Hlen|exact Hags|exact Hlk|exact Hlke|].
        by apply fence_post_er.
    - (* LDev *)
      eexists. split.
      + apply (PFDev _ _ _ ce age st' d' Hlke).
        rewrite Hst Hdev. by apply (erase_pstep_intro _ _ LDev).
      + rewrite Hpr. eapply er_cfg_upd;
          [exact Himg|exact Hlog|exact Hlen|exact Hags|exact Hlk|exact Hlke
          |exact Hws].
    - (* LRegW ↦ LSilent *)
      eexists. split.
      + apply (PFSilent _ _ _ ce age st' d' Hlke).
        rewrite Hst Hdev. by apply (erase_pstep_intro _ _ (LRegW rd srcs)).
      + rewrite Hpr. eapply er_cfg_upd;
          [exact Himg|exact Hlog|exact Hlen|exact Hags|exact Hlk|exact Hlke|].
        by apply er_ws_regw_r.
    - (* LCtrl ↦ LSilent *)
      eexists. split.
      + apply (PFSilent _ _ _ ce age st' d' Hlke).
        rewrite Hst Hdev. by apply (erase_pstep_intro _ _ (LCtrl srcs)).
      + rewrite Hpr. eapply er_cfg_upd;
          [exact Himg|exact Hlog|exact Hlen|exact Hags|exact Hlk|exact Hlke|].
        by apply er_ws_ctrl_r.
    - (* LInstr ↦ LSilent: the [w_res] divergence *)
      eexists. split.
      + apply (PFSilent _ _ _ ce age st' d' Hlke).
        rewrite Hst Hdev. by apply (erase_pstep_intro _ _ LInstr).
      + rewrite Hpr. eapply er_cfg_upd;
          [exact Himg|exact Hlog|exact Hlen|exact Hags|exact Hlk|exact Hlke|].
        by apply er_ws_instr_r.
    - (* LExLoad *)
      eexists. split.
      + apply (PFExLoad _ _ _ ce age aq base tvs [] st' d' Hlke).
        * rewrite Hst Hdev.
          by apply (erase_pstep_intro _ _ (LExLoad aq base tvs asrc)).
        * rewrite Himg Hlog. eapply read_ok_d_er0; [exact Hws|exact Hr].
      + rewrite Hpr. eapply er_cfg_upd;
          [exact Himg|exact Hlog|exact Hlen|exact Hags|exact Hlk|exact Hlke|].
        by apply exload_post_run_d_er0.
    - (* LExStore: the reservation transfers with the same base and column *)
      destruct (er_ws_res _ _ Hws R Hres) as (Re & HRe & Hrbe & Hrtse & _).
      have Hkk : pcls (pa_st age) (LExStore rl base data [] []) (pa_ws age)
                 = k.
      { rewrite Hst Hk.
        by apply (Hcls (pa_st ag) (LExStore rl base data asrc vsrc)),
                 (er_ws_relp _ _ Hws). }
      eexists. split.
      + apply (PFExStore _ _ _ ce age rl base data [] [] k Re st' d' Hlke);
          [|done|exact HRe| | | |by rewrite Hkk].
        * rewrite Hst Hdev.
          by apply (erase_pstep_intro _ _ (LExStore rl base data asrc vsrc)).
        * by rewrite Hrbe.
        * by rewrite Hrtse.
        * rewrite Hrtse Hlog. exact He.
      + rewrite Hpr. eapply er_cfg_upd;
          [exact Himg| |exact Hlen|exact Hags|exact Hlk|exact Hlke|].
        * by rewrite Hlog.
        * rewrite Hlog. by apply store_post_run_d_er0.
  Qed.

  (* ==================================================================== *)
  (** ** 5. The run level and the endpoint *)

  Lemma erase_run_step ce c c' :
    pcls_erasable → er_cfg ce c → wp_pf_run pstep pcls c c' →
    ∃ ce', wp_pf_run erase_pstep pcls ce ce' ∧ er_cfg ce' c'.
  Proof.
    intros Hcls Hm (i & l & Hs).
    destruct (erase_step i l c c' ce Hcls Hm Hs) as (ce' & Hse & Hm').
    exists ce'. split; [|done]. by exists i, (erase_lbl l).
  Qed.

  Lemma erase_rtc ce c c' :
    pcls_erasable → er_cfg ce c → rtc (wp_pf_run pstep pcls) c c' →
    ∃ ce', rtc (wp_pf_run erase_pstep pcls) ce ce' ∧ er_cfg ce' c'.
  Proof.
    intros Hcls Hm Hrun. revert ce Hm.
    induction Hrun as [x|x y z Hxy _ IH]; intros ce Hm.
    { exists ce. split; [done|done]. }
    destruct (erase_run_step ce x y Hcls Hm Hxy) as (ce1 & Hs1 & Hm1).
    destruct (IH ce1 Hm1) as (ce2 & Hs2 & Hm2).
    exists ce2. split; [|done]. by econstructor.
  Qed.

  (** THE ENDPOINT (stage 1's deliverable).  Every pf run of the
      DEPENDENCY-CARRYING instance is matched, step for step, by a pf run of
      the SAME program over the erased alphabet, with the same image, THE
      SAME LOG, the same fabric and the same program states — and every
      label the erased run emits is [lb_depfree], which is the premise
      stage 3's projection is gated on. *)
  Theorem erase_run img d0 (ps : list P) c :
    pcls_erasable →
    rtc (wp_pf_run pstep pcls) (wp_init img d0 ps) c →
    ∃ ce, rtc (wp_pf_run erase_pstep pcls) (wp_init img d0 ps) ce ∧
          pc_img ce = pc_img c ∧ pc_log ce = pc_log c ∧ pc_dev ce = pc_dev c ∧
          (∀ i agi, pc_ags c !! i = Some agi →
             ∃ age, pc_ags ce !! i = Some age ∧ pa_st age = pa_st agi) ∧
          pstep_depfree erase_pstep.
  Proof.
    intros Hcls Hrun.
    destruct (erase_rtc (wp_init img d0 ps) (wp_init img d0 ps) c Hcls
                (er_cfg_init img d0 ps) Hrun) as (ce & Hrune & Hm).
    exists ce. split; [done|].
    destruct Hm as (Himg & Hlog & Hdev & _ & Hags).
    split_and!; [done|done|done| |apply erase_pstep_depfree].
    intros i agi Hlk. destruct (Hags i agi Hlk) as (age & Hlke & Hst & _).
    by exists age.
  Qed.

  (** THE STAGE-1 PAYOFF, spelled out: T2 CONTAINMENT FOR A
      DEPENDENCY-CARRYING PROGRAM.  [wp_pf_bridge] asks for [pstep_depfree],
      which the D2 event instance does NOT satisfy; composing it with the
      erasure replaces that premise by nothing at all.  What is left is the
      [lb_fused] premise, which is stage 2's (re-fusion) — so for a producer
      that emits no split labels (every instance in this tree today) the
      pipeline is already complete.

      The conclusion is stated on the LOG because that is what T2 asserts:
      the axiomatic execution's memory is literally the machine run's. *)
  Corollary erase_bridge_log img d0 (ps : list P) c :
    pcls_erasable → pstep_fused pstep →
    rtc (wp_pf_run pstep pcls) (wp_init img d0 ps) c →
    ∃ E, exec_wf E ∧ ex_img E = img ∧ ex_log E = pc_log c.
  Proof.
    intros Hcls Hfu Hrun.
    destruct (erase_rtc (wp_init img d0 ps) (wp_init img d0 ps) c Hcls
                (er_cfg_init img d0 ps) Hrun) as (ce & Hrune & Hm).
    destruct (wp_pf_bridge_log erase_pstep pcls img d0 ps ce
                erase_pstep_depfree (erase_pstep_fused Hfu) Hrune)
      as (E & HE & Himg & Hlog).
    exists E. split_and!; [done|done|]. by rewrite Hlog (er_cfg_log _ _ Hm).
  Qed.

End erase.
