(** * WeakLitmusProj.v — the litmus machine projects into the axiomatic LTS
      (M6 W4, "Projection lemmas")

    [WeakLitmus.v] is the tiny executable hart-program machine ([instr],
    [hart], [config], [lstep]); [WeakAxiomatic.v] is the canonical
    promise-free event-labelled LTS ([mstate]/[mstep], executions as
    (state list, step list) pairs).  This file is the projection

        every [rtc lstep] run of the litmus machine from an initial
        configuration projects to an [exec_wf] execution of [WeakAxiomatic]
        with the same image, the same log and per-hart [wstate]s that agree
        but for the control view (see the third bullet below).

    It is [WeakPromiseBridge.v] one machine over, and follows that file's
    structure exactly.  The differences are all simplifications:

    - the litmus machine has NO silent arm, so the projection is total: one
      [lstep] is exactly one [mstep] (no stuttering, hence no [option] in
      the step lemma);

    - every litmus access is SINGLE-BYTE, so the four arms hit [mstep]'s
      run-shaped post-states at singleton lists.  Those collapse to
      [WeakMem]'s [load_post] / [store_post] — which is what [lstep] writes
      into the hart — UP TO A RAISED CONTROL VIEW, through [Z.add_0_r] (byte
      [j] of the access lives at [base + Z.of_nat j], i.e.
      [acc_addr base 0 = base + 0]).  The control view is W-TV's
      consumption ([WeakMem.load_post_run_d]): a RUN-level access joins the
      entry state's translation bank into [w_vcap] and the per-byte
      functions do not, and the litmus machine — which has no [LInstr] to
      reset the bank with — never performs that join.  Hence [lcfg_match]
      relates the per-hart [wstate]s by [WeakMem.ws_ctrl_up] ("equal but for
      a raised [w_vcap]") rather than by equality.  Nothing on either side
      reads [w_vcap]: the axiomatic tier has no [fulfil_ok] at all, so the
      slack is invisible to every side condition, and the projection
      theorem's payload (same image, same log) is untouched;

    - the AMO's atomicity side condition in [lstep] ([log_byte … = Some vv]
      plus [¬ writes_in log a t (length log)]) IS [WeakMem.latest] unfolded,
      so [mstep]'s [rmw_latest] premise is immediate — no analogue of
      [WeakPromiseBridge]'s [own_coh] dovetail is needed here, because the
      litmus machine already states the constraint globally.

    As in [WeakPromiseBridge], the state projection [lcfg_match] is stated
    RELATIONALLY: an [mstate]'s [ms_ws] is a FUNCTION while a [config]'s
    harts are a LIST, and a functional projection would need functional
    extensionality, which this tree does not assume.

    DELTAS from the W4 spec.  (i) The step lemma is stated without the
    [option]/"projection of the arm" alternative, since no [lstep] arm
    stutters.  (ii) The initial-configuration premise is spelled
    [Forall (λ h, h_ws h = ws_init) harts0] over [Cfg img [] harts0], which
    is the shape [WeakLitmus]'s own litmus configurations already have
    (e.g. [sb_c0]); [lstep_exec_wf_sb] at the bottom checks that the theorem
    applies to them verbatim.

    DEPENDENCY-FREE like its inputs: stdpp, [WeakMem], [WeakLitmus],
    [WeakAxiomatic].  No Iris, no Sail, no [WeakPromise].

    NOTE ON NAMES.  [WeakAxiomatic]'s [lbl] constructors
    ([LLoad]/[LStore]/[LFence]/[LRmw]) are qualified below, following
    [WeakPromiseBridge]'s convention, even though [WeakLitmus]'s [instr]
    constructors ([ILoad]/…) do not actually collide with them. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakLitmus WeakAxiomatic.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** Singleton collapses of the run-shaped post-states

    [WeakMem.ws_ctrl_up_load] / [_store] / [_fence] are the collapses this
    file consumes: each says a litmus arm's per-byte post-state and the
    matching [mstep] arm's run-shaped one differ by a control raise and
    nothing else.  They are built on [load_post_run_single] /
    [store_post_run_single], which live in [WeakMem.v]. *)

(* ------------------------------------------------------------------ *)
(** ** Singleton instances of the two read side conditions *)

Lemma rd_ok_single img log ws aq a t v :
  log_byte img log t a = Some v →
  readable img log ws (load_vpre ws aq) a t →
  rd_ok img log ws aq a [t] [v].
Proof.
  intros Hb Hr. split; [done|]. intros j t' v' Ht Hv.
  destruct j as [|j]; simpl in Ht, Hv.
  - simplify_eq. rewrite /byte_rd /acc_addr Z.add_0_r. by split.
  - by rewrite lookup_nil in Ht.
Qed.

(** The instance the arms below meet: the [mstate]'s agent is the hart's
    state with a RAISED CONTROL VIEW, and [readable] — hence [rd_ok] — reads
    only [coh] and [load_vpre], neither of which sees [w_vcap]. *)
Lemma rd_ok_single_ctrl_up img log w1 w2 aq a t v :
  ws_ctrl_up w1 w2 →
  log_byte img log t a = Some v →
  readable img log w1 (load_vpre w1 aq) a t →
  rd_ok img log w2 aq a [t] [v].
Proof. intros [x ->] Hb Hr. by apply rd_ok_single. Qed.

(** [WeakLitmus]'s AMO arm carries exactly [WeakMem.latest] unfolded. *)
Lemma rmw_latest_single img log a t :
  is_Some (log_byte img log t a) →
  ¬ writes_in log a t (length log) →
  rmw_latest img log a [t].
Proof.
  intros Hs Hn j t' Ht. destruct j as [|j]; simpl in Ht.
  - simplify_eq. rewrite /acc_addr Z.add_0_r. by split.
  - by rewrite lookup_nil in Ht.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The state projection

    Same image, same log, and the [mstate]'s view function agrees with the
    hart list where the latter is defined.  Harts and agents are the SAME
    [nat] indices on both sides. *)
Definition lcfg_match (c : config) (σ : mstate) : Prop :=
  ms_img σ = c_img c ∧ ms_log σ = c_log c ∧
  (∀ i h, c_harts c !! i = Some h → ws_ctrl_up (h_ws h) (ms_ws σ i)).

(** The functional projection, for consumers who want one: it matches. *)
Definition lproj_ws (c : config) : agent → wstate :=
  λ i, match c_harts c !! i with Some h => h_ws h | None => ws_init end.
Definition lproj_st (c : config) : mstate :=
  MSt (c_img c) (c_log c) (lproj_ws c).

Lemma lcfg_match_proj c : lcfg_match c (lproj_st c).
Proof.
  split_and!; [done|done|]. intros i h Hlk.
  rewrite /= /lproj_ws Hlk. reflexivity.
Qed.

Lemma lcfg_match_log c σ : lcfg_match c σ → ms_log σ = c_log c.
Proof. by intros (_ & ? & _). Qed.

(** The one-hart-updated instance, shared by all four arms. *)
Lemma lcfg_match_upd_gen (img : image) (lg : list wmsg) (hs : list hart)
    i h prog' regs' w (f g : agent → wstate) :
  (∀ j hj, hs !! j = Some hj → ws_ctrl_up (h_ws hj) (f j)) →
  hs !! i = Some h →
  ws_ctrl_up w (g i) →
  (∀ j, j ≠ i → g j = f j) →
  lcfg_match (Cfg img lg (<[i := Hart prog' regs' w]> hs)) (MSt img lg g).
Proof.
  intros Hf Hlk Hgi Hgne. split_and!; [done|done|].
  intros j hj Hj. simpl in *.
  destruct (decide (j = i)) as [->|Hne].
  - rewrite list_lookup_insert in Hj;
      [by eapply lookup_lt_Some|by simplify_eq/=].
  - rewrite list_lookup_insert_ne // in Hj. rewrite Hgne //. by apply Hf.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The step lemma: one [lstep] is exactly one [mstep]

    The four arms match 1:1 —
      [ILoad r a aq]      ↦ [LLoad aq a [t] [v]]        ([MStepLoad])
      [IStore a v]        ↦ [LStore false a [v] WCplain] ([MStepStore])
      [IFence pr pw sr sw]↦ [LFence pr pw sr sw]        ([MStepFence])
      [IAmoSwapAq r a v]  ↦ [LRmw true false a [t] [vv] [v] WCexcl] ([MStepRmw]).
    The register file and the remaining program are simply forgotten. *)
Lemma lstep_mstep c c' σ :
  lstep c c' → lcfg_match c σ →
  ∃ (i : agent) (l : lbl) (σ' : mstate), mstep σ i l σ' ∧ lcfg_match c' σ'.
Proof.
  intros (i & h & Hlk & Himg & Harm) (Hmi & Hml & Hmw).
  destruct σ as [img lg f]. simpl in Hmi, Hml, Hmw.
  destruct c as [cimg clog chs], c' as [cimg' clog' chs'].
  simpl in Hlk, Himg, Harm, Hmi, Hml, Hmw. subst img lg cimg'.
  destruct (h_prog h) as [|[r a aq|a v|pr pw sr sw|r a v] rest]; [done| | | |].
  - (* load *)
    destruct Harm as (t & v & Hb & Hr & -> & ->).
    eexists i, (WeakAxiomatic.LLoad aq a [t] [v]), _. split.
    + apply MStepLoad. simpl.
      by apply (rd_ok_single_ctrl_up _ _ (h_ws h)); [by apply Hmw|done|done].
    + simpl. eapply (lcfg_match_upd_gen _ _ _ i h _ _ _ f); [done|done| |].
      * rewrite upd_ws_eq. by apply ws_ctrl_up_load, Hmw.
      * intros j Hne. by rewrite upd_ws_ne.
  - (* store *)
    destruct Harm as (-> & ->).
    eexists i, (WeakAxiomatic.LStore false a [v] WCplain), _. split.
    + by apply MStepStore.
    + simpl. eapply (lcfg_match_upd_gen _ _ _ i h _ _ _ f); [done|done| |].
      * rewrite upd_ws_eq. by apply ws_ctrl_up_store, Hmw.
      * intros j Hne. by rewrite upd_ws_ne.
  - (* fence *)
    destruct Harm as (-> & ->).
    eexists i, (WeakAxiomatic.LFence pr pw sr sw), _. split.
    + apply MStepFence.
    + simpl. eapply (lcfg_match_upd_gen _ _ _ i h _ _ _ f); [done|done| |].
      * rewrite upd_ws_eq. by apply ws_ctrl_up_fence, Hmw.
      * intros j Hne. by rewrite upd_ws_ne.
  - (* amoswap.aq: the atomicity conjunct IS [rmw_latest] at one byte *)
    destruct Harm as (t & vv & Hb & Hnw & Hr & -> & ->).
    eexists i, (WeakAxiomatic.LRmw true false a [t] [vv] [v] WCexcl), _. split.
    + apply MStepRmw.
      * done.
      * done.
      * simpl.
        by apply (rd_ok_single_ctrl_up _ _ (h_ws h)); [by apply Hmw|done|done].
      * simpl. apply rmw_latest_single; [by eexists|done].
    + simpl. eapply (lcfg_match_upd_gen _ _ _ i h _ _ _ f); [done|done| |].
      * rewrite upd_ws_eq. by apply ws_ctrl_up_store, ws_ctrl_up_load, Hmw.
      * intros j Hne. by rewrite upd_ws_ne.
Qed.

(* ------------------------------------------------------------------ *)
(** ** The bridge *)

(** Extending the execution by one [lstep]. *)
Lemma lbridge_step E c c' :
  exec_wf E → lcfg_match c (stt E (length (ex_tr E))) → lstep c c' →
  ∃ E', exec_wf E' ∧ ex_img E' = ex_img E ∧
        lcfg_match c' (stt E' (length (ex_tr E'))).
Proof.
  intros HE Hm Hstep.
  destruct (lstep_mstep c c' _ Hstep Hm) as (i & l & σ' & Hms & Hm').
  exists (Exec (ex_st E ++ [σ']) (ex_tr E ++ [EStep i l])).
  pose proof HE as (Hlen & _ & _).
  have Hst0 : (0 < length (ex_st E))%nat by lia.
  split_and!.
  - apply (exec_snoc E (EStep i l) σ'); [done|by simpl].
  - rewrite /ex_img /eimg /stt /=. rewrite lookup_app_l; [lia|done].
  - rewrite /stt /= length_app /=.
    rewrite lookup_app_r; [lia|].
    replace (length (ex_tr E) + 1 - length (ex_st E))%nat with 0%nat by lia.
    by simpl.
Qed.

Lemma lbridge_run c c' :
  rtc lstep c c' →
  ∀ E, exec_wf E → lcfg_match c (stt E (length (ex_tr E))) →
  ∃ E', exec_wf E' ∧ ex_img E' = ex_img E ∧
        lcfg_match c' (stt E' (length (ex_tr E'))).
Proof.
  induction 1 as [|x y z Hs _ IH]; intros E HE Hm.
  { by exists E. }
  destruct (lbridge_step E x y HE Hm Hs) as (E1 & HE1 & Himg1 & Hm1).
  destruct (IH E1 HE1 Hm1) as (E2 & HE2 & Himg2 & Hm2).
  exists E2. split_and!; [done|by rewrite Himg2|done].
Qed.

(** THE PROJECTION THEOREM (M6 W4).  Every reachable configuration of the
    litmus machine, from an initial configuration (empty log, every hart at
    [ws_init] — the shape [WeakLitmus]'s litmus configurations have), is
    matched by the final [mstate] of an [exec_wf] execution over the same
    image. *)
Theorem lstep_exec_wf (img : image) (harts0 : list hart) c :
  Forall (λ h, h_ws h = ws_init) harts0 →
  rtc lstep (Cfg img [] harts0) c →
  ∃ E, exec_wf E ∧ ex_img E = img ∧ lcfg_match c (stt E (length (ex_tr E))).
Proof.
  intros Hinit Hrun.
  set σ0 := MSt img [] (λ _ : agent, ws_init).
  have HE : exec_wf (Exec [σ0] []) by apply exec_nil.
  have Hm0 : lcfg_match (Cfg img [] harts0) (stt (Exec [σ0] []) 0%nat).
  { split_and!; [done|done|].
    intros i h Hlk. simpl. by rewrite (Forall_lookup_1 _ _ _ _ Hinit Hlk). }
  destruct (lbridge_run _ _ Hrun (Exec [σ0] []) HE Hm0) as (E & HE' & Himg & Hm).
  exists E. by split_and!.
Qed.

(** SANITY (the [wp_pf_bridge_log] analogue): the projected execution's final
    log IS the configuration's log. *)
Corollary lstep_exec_log (img : image) (harts0 : list hart) c :
  Forall (λ h, h_ws h = ws_init) harts0 →
  rtc lstep (Cfg img [] harts0) c →
  ∃ E, exec_wf E ∧ ex_img E = img ∧ ex_log E = c_log c.
Proof.
  intros Hinit Hrun.
  destruct (lstep_exec_wf img harts0 c Hinit Hrun) as (E & ? & ? & Hm).
  exists E. split_and!; [done|done|]. by apply lcfg_match_log.
Qed.

(** SANITY: the theorem applies verbatim to [WeakLitmus]'s own litmus
    configurations — here SB, whose initial config is [Cfg img0 [] [_; _]]
    with both harts at [ws_init]. *)
Corollary lstep_exec_wf_sb c :
  reach sb_c0 c →
  ∃ E, exec_wf E ∧ ex_img E = img0 ∧ ex_log E = c_log c.
Proof.
  intros Hrun.
  destruct (lstep_exec_log img0
              [Hart sb_prog0 ∅ ws_init; Hart sb_prog1 ∅ ws_init] c
              ltac:(by repeat constructor) Hrun) as (E & ? & ? & ?).
  by exists E.
Qed.
