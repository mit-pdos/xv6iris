(** * WeakAxRealize — the PROGRAM-CARRYING reverse bridge (A3(iii))

    [WeakPromiseBridge] part (E) replays an axiomatic execution as a
    promise-free run of the FULL machine, but only for a program LTS that
    admits every label ([prog_free]) — "programs are free".  xv6 is not
    free, so that form cannot compose with the real instance: T1's
    conclusion (`srvwmo_realizable`: an sRVWMO-consistent candidate yields
    an [exec_wf] execution) has to become a pf run OF A GIVEN PROGRAM
    before adequacy can be applied to it.

    This file is that generalization.  [prog_free] is replaced by a
    PER-STEP SUPPLY of program steps along the execution's trace
    ([exec_prog_ok]), and [WeakPromiseBridge.exec_cls_ok]'s fixed-[ps]
    indexing — which is an artefact of [prog_free] (under it no program
    state ever moves, so the class equation could be read at the agent's
    INITIAL state) — disappears into that supply, at the per-step program
    state where it belongs.

    NOTHING IN [WeakPromiseBridge] IS EDITED: this is a leaf file built on
    its exported lemmas.  The two [prog_free] theorems are re-derived here
    ([exec_prefix_pf_run_pf], [exec_wf_pf_run_pf]) to show they are
    corollaries; the bridge's own copies are then redundant and can be
    deleted whenever that file is quiet.

    ** The hypothesis' shape, and why it is this one

    The supply hands the machine a WLABEL [l] and a [pstep] at it; the
    axiomatic side only has its own [lbl].  Two shapes were available:

    (1) demand the step at the CANONICAL machine label
        [WeakPromiseBridge.unproj_lbl lb] (empty operand lists,
        [lat := false]), or
    (2) demand it at ANY label that PROJECTS to the execution's label,
        [proj_lbl (pcls …) l = Some lb].

    (2) is chosen, as [lbl_realizes] below.  The reasons:

    - IT IS THE EXACT INVERSE OF THE FORWARD PROJECTION.  The forward
      bridge [WeakPromiseBridge.wp_pf_step_mstep] takes [lb_depfree l] and
      [lb_fused l] and produces [proj_lbl k l = Some lb] together with the
      [mstep].  Stating the reverse direction over the same relation makes
      the two composable by name rather than by re-derivation — which
      matters because the A2 route (the ERASURE SIMULATION: blank every
      operand list, project the erased run with [wp_pf_step_mstep], whose
      [lb_depfree] premise is then discharged by construction) is what
      will feed this theorem's output back to the instance.  The
      restrictions [lbl_realizes] carries are the very same two gates, so
      "which alphabet does T1 realize an execution in" has ONE answer on
      both sides of the equivalence.

    - THE RESTRICTIONS ARE NAMED, NOT BAKED IN.  Under
      [lb_fused ∧ lat_free ∧ lb_depfree] shape (2) is EQUIVALENT to shape
      (1) — [lbl_realizes_unproj] and [lbl_realizes_intro] prove both
      directions (the latter at a label the execution actually stepped
      with, whose [rd_ok] lengths are what make the [zip] round-trip) — so
      nothing is gained TODAY.  What is gained is where
      the future relaxations land: each is the deletion of one conjunct
      from ONE definition, with the theorem statements untouched.
      * [lb_fused] is A3(iv)/R3's: an sRVWMO execution has DANGLING
        exclusive reads, and the instance emits [LExLoad]/[LExStore], so
        T1's realization must eventually be allowed to answer an axiomatic
        [LLoad]/[LRmw] with a SPLIT machine pair.  That is not a
        step-local simulation (a fused axiomatic rmw becomes two machine
        steps, and [PFExLoad]'s post-state sets [w_res], which the
        axiomatic [mstate] has no room for), hence a gate here, exactly as
        in the forward direction.
      * [lb_depfree] is A2's: with a non-empty operand list the machine's
        post-state raises [w_vcap] through [ctrl_post] and its read check
        raises the [vaddr] floor, neither of which [WeakAxiomatic.mstep]
        (which steps with the dependency-FREE [load_post_run] /
        [store_post_run]) can match under [cfg_match]'s wstate EQUALITY.
        Relaxing it is the erasure invariant's [w_fwd]/[dep_dom] work,
        i.e. the same work item the forward direction has, run backwards.
      * [lat_free] is the one gate the forward direction does not need
        (it already HAS a [read_ok_d]); the axiomatic [rd_ok] carries no
        "no writes above" evidence, so a [lat = true] load cannot be
        replayed.  The instance discharges it today
        ([WeakEvCapstone.pstep_ev_lat_free_prog], whose [lat_free_prog] is
        literally [lat_free] + [lb_fused] over the whole LTS).

    - IT ABSORBS THE CLASS PREMISE.  [proj_lbl] carries the message class
      in the [LStore]/[LRmw] arms, so [proj_lbl (pcls p l ws) l = Some lb]
      SAYS [WeakPromiseBridge.mstep_cls_ok] at the acting agent's own
      per-step program state and wstate.  The separate [exec_cls_ok]
      premise therefore does not need re-indexing — it is gone.

    DEPENDENCY-FREE like the bridge: stdpp, [WeakMem], [WeakPromise],
    [WeakPromiseFact], [WeakAxiomatic], [WeakPromiseBridge].  No Iris, no
    Sail.

    NOTE ON NAMES: [WeakPromise] and [WeakAxiomatic] both export
    [LLoad]/[LStore]/[LFence]/[LRmw]; the latter shadows the former, so
    every occurrence below is QUALIFIED. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakAxiomatic
     WeakPromiseBridge.

Local Open Scope Z_scope.

(* ================================================================== *)
Section realize.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pcls : P → wlabel → wstate → wm_class).

  Implicit Types c : wpcfg P D.

  (* ---------------------------------------------------------------- *)
  (** ** (1) The label-supply relation *)

  (** [l] REALIZES the axiomatic label [lb] for agent [i] at state [σ],
      run at the acting agent's program state [p]: it is a fused,
      lat-free, operand-free machine label whose projection — with the
      class the machine would stamp, read at [p] and the agent's own
      [wstate] — is [lb]. *)
  Definition lbl_realizes (p : P) (σ : mstate) (i : agent)
      (lb : WeakAxiomatic.lbl) (l : wlabel) : Prop :=
    lb_fused l ∧ lat_free l ∧ lb_depfree l ∧
    proj_lbl (pcls p l (ms_ws σ i)) l = Some lb.

  (** Under the three gates the relation is FUNCTIONAL, and its value is
      the canonical [unproj_lbl]; the class side condition it carries is
      exactly [mstep_cls_ok]. *)
  Lemma lbl_realizes_unproj p σ i lb l :
    lbl_realizes p σ i lb l →
    l = unproj_lbl lb ∧ mstep_cls_ok pcls p σ i lb.
  Proof.
    intros (Hfu & Hlat & Hdf & Hpr).
    destruct l; simpl in Hfu, Hlat, Hdf, Hpr; try done.
    - (* load: [lat_free] gives [lat = false], [lb_depfree] gives
         [asrc = []], and [zip] round-trips a list of pairs *)
      subst lat asrc. simplify_eq/=. by rewrite zip_fst_snd.
    - (* store: the class binder is [pcls] applied to THIS label *)
      destruct Hdf as [-> ->]. simplify_eq/=. done.
    - (* rmw *)
      destruct Hdf as [-> ->]. simplify_eq/=.
      by rewrite zip_fst_snd.
    - (* fence *) by simplify_eq/=.
  Qed.

  (** The converse, at a label the axiomatic side actually stepped with:
      the [rd_ok] lengths inside [mstep] are what make [zip] round-trip. *)
  Lemma lbl_realizes_intro p σ σ' i lb :
    mstep σ i lb σ' → mstep_cls_ok pcls p σ i lb →
    lbl_realizes p σ i lb (unproj_lbl lb).
  Proof.
    intros Hms Hck.
    have Hzip : ∀ (ts : list nat) (vs : list (bv 8)),
      length ts = length vs →
      (zip ts vs).*1 = ts ∧ (zip ts vs).*2 = vs.
    { intros ts vs Hlen. split; [apply fst_zip|apply snd_zip]; lia. }
    inversion Hms as
      [aq base ts vs Hrd Hlb Hσ'
      |rl base vs kc Hnn Hlb Hσ'
      |pr pw sr sw Hlb Hσ'
      |aq rl base ts rvs wvs kc Hnn Hlen Hrd Hlat Hlb Hσ']; subst lb;
      rewrite /lbl_realizes;
      cbn [unproj_lbl proj_lbl lb_fused lat_free lb_depfree] in Hck |- *;
      split_and!; try done.
    - (* load: the projection re-splits the zip *)
      destruct Hrd as [Hlen _]. destruct (Hzip ts vs ltac:(lia)) as [-> ->].
      done.
    - (* store: the class equation IS [mstep_cls_ok] *)
      by rewrite Hck.
    - (* rmw: both *)
      destruct Hrd as [Hlen' _]. destruct (Hzip ts rvs ltac:(lia)) as [-> ->].
      by rewrite Hck.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (2) The program-carrying hypothesis

      A per-step assignment of program states ([pst k] = the agent list
      as of trace position [k]) and of the FABRIC ([dv k]), together with
      the [pstep] that carries position [k] to [k+1].  The frame
      condition — every other agent's program state is untouched — is
      spelled as the list INSERT, which also keeps [length (pst k)]
      constant for free. *)
  Definition exec_prog_ok (pst : nat → list P) (dv : nat → D)
      (E : exec) : Prop :=
    ∀ k s, ex_tr E !! k = Some s →
      ∃ p p' l,
        pst k !! es_ag s = Some p ∧
        lbl_realizes p (stt E k) (es_ag s) (es_lb s) l ∧
        pstep p (dv k) l p' (dv (S k)) ∧
        pst (S k) = <[es_ag s := p']> (pst k).

  (* ---------------------------------------------------------------- *)
  (** ** (3) One step

      [WeakPromiseBridge.mstep_wp_pf_step] with the [prog_free] supply
      replaced by the given [pstep], and with the "program states are
      untouched" conclusion replaced by the insert. *)
  Lemma mstep_wp_pf_step_prog σ σ' i lb c ag p p' l dn :
    cfg_match c σ → pc_ags c !! i = Some ag → pa_st ag = p →
    lbl_realizes p σ i lb l →
    pstep p (pc_dev c) l p' dn →
    mstep σ i lb σ' →
    ∃ c', wp_pf_step pstep pcls i l c c' ∧ cfg_match c' σ' ∧
          pa_st <$> pc_ags c' = <[i := p']> (pa_st <$> pc_ags c) ∧
          pc_dev c' = dn.
  Proof.
    intros Hm Hlk Hag Hre Hps Hms.
    destruct (lbl_realizes_unproj p σ i lb l Hre) as [-> Hck].
    subst p. clear Hre.
    destruct σ as [img lg f].
    destruct Hm as (Himg & Hlg & Hf). simpl in Himg, Hlg, Hf.
    subst img lg.
    (* the [cfg_match] obligation is the same three lines in every arm *)
    have Hmatch : ∀ (st' : P) (w : wstate) (pr : gset nat) (lg' : list wmsg)
                    (d' : D),
      cfg_match (WPCfg (pc_img c) lg' d'
                   (<[i := WPAgent st' w pr]> (pc_ags c)))
                (MSt (pc_img c) lg' (upd_ws f i w)).
    { intros st' w pr lg' d'.
      eapply (cfg_match_upd_gen _ _ _ _ i ag st' w pr f); [done|done| |].
      - by rewrite upd_ws_eq.
      - intros j Hne. by rewrite upd_ws_ne. }
    (* the program projection moves by exactly the insert *)
    have Hst : ∀ (w : wstate) (pr : gset nat),
      pa_st <$> (<[i := WPAgent p' w pr]> (pc_ags c))
      = <[i := p']> (pa_st <$> pc_ags c).
    { intros w pr. by rewrite list_fmap_insert. }
    (* [Hck] and [Hps] are REVERTED across the inversion: [simplify_eq/=]
       would reduce [mstep_cls_ok] at the constructor and substitute the
       class binder away, which is exactly the binder each arm still has
       to name; [Hps] mentions [unproj_lbl lb], which only reduces once
       [lb] is a constructor. *)
    revert Hck Hps.
    inversion Hms as
      [aq base ts vs Hrd Hlb Hσ'
      |rl base vs kc Hnn Hlb Hσ'
      |pr pw sr sw Hlb Hσ'
      |aq rl base ts rvs wvs kc Hnn Hlen Hrd Hlat Hlb Hσ']; simplify_eq/=;
      intros Hck Hps.
    - (* load *)
      pose proof Hrd as [Hlen _].
      eexists. split_and!.
      + apply (PFLoad pstep pcls i c ag aq false base (zip ts vs) [] p'
                 dn); [done|exact Hps|].
        rewrite srcs_view_nil read_ok_d_0 -(Hf i ag Hlk).
        by apply rd_ok_read_ok.
      + rewrite srcs_view_nil load_post_run_d_0 fst_zip; [lia|].
        rewrite (Hf i ag Hlk). apply Hmatch.
      + apply Hst.
      + done.
    - (* store *)
      eexists. split_and!.
      + apply (PFStore pstep pcls i c ag rl base vs [] [] kc p' dn);
          [done|exact Hps|done|].
        rewrite -(Hf i ag Hlk). exact Hck.
      + rewrite !srcs_view_nil store_post_run_d_0 (Hf i ag Hlk). apply Hmatch.
      + apply Hst.
      + done.
    - (* fence *)
      eexists. split_and!.
      + apply (PFFence pstep pcls i c ag pr pw sr sw p' dn);
          [done|exact Hps].
      + rewrite (Hf i ag Hlk). apply Hmatch.
      + apply Hst.
      + done.
    - (* rmw *)
      pose proof Hrd as [Hlen' _].
      eexists. split_and!.
      + apply (PFRmw pstep pcls i c ag aq rl base (zip ts rvs) wvs [] []
                 kc p' dn);
          [done|exact Hps|done| | | |].
        * rewrite length_zip_with. lia.
        * rewrite srcs_view_nil read_ok_d_0 -(Hf i ag Hlk).
          by apply rd_ok_read_ok.
        * by apply (rmw_latest_excl_ok (pc_img c) _ i base ts rvs).
        * rewrite -(Hf i ag Hlk). exact Hck.
      + rewrite !srcs_view_nil load_post_run_d_0 store_post_run_d_0 fst_zip;
          [lia|].
        rewrite (Hf i ag Hlk). apply Hmatch.
      + apply Hst.
      + done.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (4) The replay

      Note what is NOT a premise any more: the agent-range side condition
      ([es_ag s < length ps]) is implied by [exec_prog_ok]'s own lookup,
      and [exec_cls_ok] is absorbed into [lbl_realizes]. *)
  Lemma exec_prefix_pf_run_prog pst dv E n :
    exec_wf E → exec_prog_ok pst dv E →
    (n ≤ length (ex_tr E))%nat →
    ∃ c, rtc (wp_pf_run pstep pcls)
             (wp_init (ex_img E) (dv 0%nat) (pst 0%nat)) c ∧
         pa_st <$> pc_ags c = pst n ∧ pc_dev c = dv n ∧
         cfg_match c (stt E n).
  Proof.
    intros HE Hpr. induction n as [|n IH]; intros Hn.
    - exists (wp_init (ex_img E) (dv 0%nat) (pst 0%nat)). split_and!.
      + done.
      + rewrite /wp_init /=. rewrite -list_fmap_compose.
        by apply list_fmap_id.
      + done.
      + split_and!.
        * done.
        * by apply (exec_log_init E HE).
        * intros i ag Hlk. rewrite list_lookup_fmap in Hlk.
          destruct (pst 0%nat !! i) as [p|]; simplify_eq/=.
          by apply (exec_ws_init E i HE).
    - destruct (IH ltac:(lia)) as (c & Hrun & Hst & Hdev & Hm).
      destruct (exec_tr_lookup E n ltac:(lia)) as [s Hs].
      pose proof (exec_step_at E n s HE Hs) as Hms.
      destruct (Hpr n s Hs) as (p & p' & l & Hp & Hre & Hps & Hnext).
      have Hex : ∃ ag, pc_ags c !! es_ag s = Some ag ∧ pa_st ag = p.
      { rewrite -Hst list_lookup_fmap in Hp.
        destruct (pc_ags c !! es_ag s) as [ag|] eqn:Hag; simplify_eq/=.
        by exists ag. }
      destruct Hex as (ag & Hag & Hagp).
      destruct (mstep_wp_pf_step_prog (stt E n) (stt E (S n)) (es_ag s)
                  (es_lb s) c ag p p' l (dv (S n)) Hm Hag Hagp Hre
                  ltac:(by rewrite Hdev) Hms)
        as (c2 & Hstep & Hm2 & Hst2 & Hdev2).
      exists c2. split_and!.
      + eapply rtc_r; [done|]. by exists (es_ag s), l.
      + by rewrite Hst2 Hst -Hnext.
      + done.
      + done.
  Qed.

  (** THE PROGRAM-CARRYING REVERSE BRIDGE.  Every [exec_wf] execution
      whose trace is carried by a run of the given program LTS is the
      projection of a promise-free run of the full machine — at the
      program states, the fabric states and the labels that run supplies. *)
  Theorem exec_wf_pf_run_prog pst dv E :
    exec_wf E → exec_prog_ok pst dv E →
    ∃ c, rtc (wp_pf_run pstep pcls)
             (wp_init (ex_img E) (dv 0%nat) (pst 0%nat)) c ∧
         pa_st <$> pc_ags c = pst (length (ex_tr E)) ∧
         pc_dev c = dv (length (ex_tr E)) ∧
         cfg_match c (stt E (length (ex_tr E))).
  Proof.
    intros HE Hpr.
    destruct (exec_prefix_pf_run_prog pst dv E (length (ex_tr E)) HE Hpr
                ltac:(lia)) as (c & ? & ? & ? & ?).
    by exists c.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** (5) The [prog_free] forms are corollaries

      [prog_free] supplies the trivial assignment: every agent keeps its
      initial program state ([<[i := p]> ps = ps] when [ps !! i = Some p]),
      the fabric never moves, and the label is the canonical one, whose
      class premise is exactly what [exec_cls_ok] states.  These two are
      [WeakPromiseBridge.exec_prefix_pf_run] / [.exec_wf_pf_run] verbatim;
      the bridge's own copies are redundant once this file lands. *)
  Lemma prog_free_exec_prog_ok ps d0 E :
    prog_free pstep → exec_wf E → exec_cls_ok pcls ps E →
    (∀ k s, ex_tr E !! k = Some s → (es_ag s < length ps)%nat) →
    exec_prog_ok (λ _, ps) (λ _, d0) E.
  Proof.
    intros Hpf HE Hck Hag k s Hs.
    destruct (lookup_lt_is_Some_2 ps (es_ag s) (Hag k s Hs)) as [p Hp].
    exists p, p, (unproj_lbl (es_lb s)). split_and!.
    - done.
    - eapply (lbl_realizes_intro p (stt E k) (stt E (S k)));
        [by eapply exec_step_at|by eapply Hck].
    - apply Hpf.
    - by rewrite list_insert_id.
  Qed.

  Lemma exec_prefix_pf_run_pf ps d0 E n :
    prog_free pstep → exec_wf E → exec_cls_ok pcls ps E →
    (∀ k s, ex_tr E !! k = Some s → (es_ag s < length ps)%nat) →
    (n ≤ length (ex_tr E))%nat →
    ∃ c, rtc (wp_pf_run pstep pcls) (wp_init (ex_img E) d0 ps) c ∧
         length (pc_ags c) = length ps ∧ pa_st <$> pc_ags c = ps ∧
         cfg_match c (stt E n).
  Proof.
    intros Hpf HE Hck Hag Hn.
    destruct (exec_prefix_pf_run_prog (λ _, ps) (λ _, d0) E n HE
                (prog_free_exec_prog_ok ps d0 E Hpf HE Hck Hag) Hn)
      as (c & Hrun & Hst & _ & Hm).
    exists c. split_and!; [done| |done|done].
    by rewrite -Hst length_fmap.
  Qed.

  Theorem exec_wf_pf_run_pf ps d0 E :
    prog_free pstep → exec_wf E → exec_cls_ok pcls ps E →
    (∀ k s, ex_tr E !! k = Some s → (es_ag s < length ps)%nat) →
    ∃ c, rtc (wp_pf_run pstep pcls) (wp_init (ex_img E) d0 ps) c ∧
         cfg_match c (stt E (length (ex_tr E))).
  Proof.
    intros Hpf HE Hck Hag.
    destruct (exec_prefix_pf_run_pf ps d0 E (length (ex_tr E)) Hpf HE Hck
                Hag ltac:(lia)) as (c & ? & _ & _ & ?).
    by exists c.
  Qed.

End realize.

Global Arguments lbl_realizes {P} _ _ _ _ _ _.
Global Arguments exec_prog_ok {P D} _ _ _ _.
