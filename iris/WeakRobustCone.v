(** * WeakRobustCone.v — THE BLOCK-CONTIGUOUS CONE REPLAY (lift stage B3)

    WHAT THIS FILE DOES.  [WeakRobustMain.bad_edge_violates] builds a
    violating promise-free configuration by replaying the minimal bad
    edge's ancestor cone in an ARBITRARY topological order.  Here the
    same exhibit is re-derived over a BLOCK-CONTIGUOUS order, and the
    run's segment structure is exported, so that a later stage can
    regroup the run into whole-instruction [WeakLang] steps.

    THE STRUCTURAL PREMISE.  A block is a maximal stretch of an agent's
    trace between two BOUNDARY states ([bnd] — instantiated at
    [WeakSailLTS] by "no in-flight micro-state").  The one premise this
    file takes about them is [Hcsl] (the trace-level form of the
    design's (P1')/(P2)): AFTER a cross-edge source, and until the next
    boundary state, the agent's events are non-memory (silent/fence).
    Together with "cross-edge TARGETS are memory events" (which is a
    theorem: an rf target reads and a [gE] target is a fulfil), this
    gives

      - at most ONE cross-edge source per block, and
      - every cross-edge target of a block is program-order
        at-or-before that block's cross source,

    which is exactly what makes the BLOCK-CONTRACTED graph acyclic: a
    contracted cycle composes back into an event-level [gdep2] cycle
    through [gpo], and the cone carries no [gdep2] cycle because
    [cone_Qinv]'s order already places every predecessor strictly
    earlier.

    THE PLUMBING.  Acyclicity of the contracted graph is fed to
    [WeakRobustLin.topo_sort] over the cone's block identifiers; the
    resulting block order is turned into a LEXICOGRAPHIC key on events
    ((block position, trace index)) and [topo_sort] is run a second time
    at the event level over that key.  The second sort is what makes the
    positional reasoning cheap: block contiguity, in-block trace order
    and the [qorder] predecessor property all read off one total order.

    THE RUN.  [WeakRobustSim.Qinv_step] does not export the underlying
    [wp_pf_step]; [qcfg_step_ex] below is its step-exporting twin (the
    same five label arms, with the step handed out instead of consumed),
    and [pf_chain] is the resulting per-event configuration chain: one
    [WeakRobustBlocks.cstep] of the processed event's agent per element
    of the order.  Combined with the block-contiguity export a later
    file can cut that chain at block boundaries and read each block off
    as a contiguous SOLO run.

    DEPENDENCY-FREE like its parents: stdpp only, no Iris, no Sail.
    [WeakAxiomatic] is imported FIRST so that [WeakPromise]'s [wlabel]
    constructors shadow its [lbl] ones. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakAxiomatic.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakPromiseBridge
                            WeakRobustTrace WeakRobustGraph WeakRobust
                            WeakRobustProv WeakRobustLin WeakRobustOrd
                            WeakRobustSim WeakRobustMain WeakRobustBlocks.

Local Open Scope Z_scope.

(* ================================================================== *)
(** * §0  TWO GENERIC LIST HELPERS

    The position of an element in a duplicate-free list, as a FUNCTION
    (every ordering argument below is spent comparing such positions). *)

(** Both lists this file positions into ([the cone's events] and [the
    cone's block identifiers]) live at [nat * nat], so no typeclass
    plumbing is needed. *)
Definition lidx (l : list (nat * nat)) (x : nat * nat) : nat :=
  match list_find (λ y, y = x) l with
  | Some (i, _) => i
  | None => length l
  end.

Lemma lidx_lookup (l : list (nat * nat)) x :
  x ∈ l → l !! lidx l x = Some x.
Proof.
  intros Hin. rewrite /lidx.
  destruct (list_find (λ y, y = x) l) as [[i y]|] eqn:Hf.
  - apply list_find_Some in Hf as (Hl & -> & _). exact Hl.
  - exfalso. rewrite list_find_None in Hf.
    by destruct (list_relations.Forall_forall (λ y, ¬ (y = x)) l) as [Hall _];
      apply (Hall Hf x Hin).
Qed.

Lemma lidx_inj (l : list (nat * nat)) x i :
  NoDup l → l !! i = Some x → lidx l x = i.
Proof.
  intros Hnd Hi.
  have Hin : x ∈ l by eapply elem_of_list_lookup_2.
  have Hl := lidx_lookup l x Hin.
  by eapply list_relations.NoDup_lookup.
Qed.

Lemma lidx_lt (l : list (nat * nat)) x :
  x ∈ l → (lidx l x < length l)%nat.
Proof. intros Hin. by eapply lookup_lt_Some, lidx_lookup. Qed.

Lemma lidx_eq_elem (l : list (nat * nat)) x y :
  x ∈ l → y ∈ l → lidx l x = lidx l y → x = y.
Proof.
  intros Hx Hy Heq.
  have H1 := lidx_lookup l x Hx. have H2 := lidx_lookup l y Hy.
  congruence.
Qed.

(** The first edge of a [tc] chain, and a decidable de Morgan step for a
    two-premise implication (both are used to take apart the contracted
    cycle). *)
Lemma tc_first {A} (R : relation A) x z : tc R x z → ∃ y, R x y.
Proof. destruct 1 as [x' y' HR|x' y' z' HR _]; by exists y'. Qed.

Lemma not_impl2 (A B C : Prop) `{!Decision A, !Decision B, !Decision C} :
  ¬ (A → B → C) → A ∧ B ∧ ¬ C.
Proof.
  intros Hn.
  destruct (decide A) as [HA|HA];
    [|exfalso; apply Hn; intros HA'; by destruct (HA HA')].
  destruct (decide B) as [HB|HB];
    [|exfalso; apply Hn; intros _ HB'; by destruct (HB HB')].
  destruct (decide C) as [HC|HC]; [exfalso; apply Hn; by auto|by auto].
Qed.

(* ================================================================== *)
(** * §1  BLOCK VOCABULARY ON ONE TRACE

    [blk_no T k] is the number of BOUNDARY STATES among the trace states
    [1 … k].  Event [k] of the trace runs from state [k] to state
    [S k], so two events of the same agent are IN THE SAME BLOCK exactly
    when [blk_no] agrees on them, i.e. when no boundary state lies
    strictly between them.  Blocks are intervals of the trace index by
    construction ([blk_no] is monotone). *)

Section blockvocab.
  Context {P D : Type}.
  Context (bnd : P → Prop).
  Context `{!∀ p, Decision (bnd p)}.

  Definition bnd_at (T : atrace P D) (j : nat) : bool :=
    match at_ags T !! j with
    | Some ag => bool_decide (bnd (pa_st ag))
    | None => false
    end.

  Fixpoint blk_no (T : atrace P D) (k : nat) : nat :=
    match k with
    | 0%nat => 0%nat
    | S k' => (blk_no T k' + if bnd_at T (S k') then 1%nat else 0%nat)%nat
    end.

  Lemma blk_no_mono T k k' : (k ≤ k')%nat → (blk_no T k ≤ blk_no T k')%nat.
  Proof.
    induction k' as [|k' IH]; intros Hle.
    - have -> : k = 0%nat by lia. done.
    - destruct (decide (k = S k')) as [->|Hne]; [done|].
      have Hk : (k ≤ k')%nat by lia.
      have := IH Hk. simpl. lia.
  Qed.

  (** Blocks are intervals: a strictly larger block number forces a
      strictly larger trace index. *)
  Lemma blk_no_lt_index T k k' :
    (blk_no T k < blk_no T k')%nat → (k < k')%nat.
  Proof.
    intros Hlt0. destruct (decide (k < k')%nat) as [?|Hge]; [done|].
    have Hle : (k' ≤ k)%nat by lia.
    have := blk_no_mono T k' k Hle. lia.
  Qed.

  (** SAME BLOCK ⟹ NO BOUNDARY STRICTLY BETWEEN. *)
  Lemma blk_no_gap T k k' m :
    blk_no T k = blk_no T k' → (k ≤ m)%nat → (S m ≤ k')%nat →
    bnd_at T (S m) = false.
  Proof.
    intros Heq H1 H2.
    destruct (bnd_at T (S m)) eqn:Hb; [exfalso|done].
    have Ha : (blk_no T k ≤ blk_no T m)%nat by apply blk_no_mono.
    have Hc : (blk_no T (S m) ≤ blk_no T k')%nat by apply blk_no_mono.
    simpl in Hc. rewrite Hb in Hc. lia.
  Qed.

  Lemma bnd_at_false T j ag :
    at_ags T !! j = Some ag → bnd_at T j = false → ¬ bnd (pa_st ag).
  Proof.
    rewrite /bnd_at. intros -> Hb. by apply bool_decide_eq_false in Hb.
  Qed.

  (** …and conversely a boundary state at [S m] separates the blocks. *)
  Lemma blk_no_bnd_lt T m :
    bnd_at T (S m) = true → (blk_no T m < blk_no T (S m))%nat.
  Proof. intros Hb. simpl. rewrite Hb. lia. Qed.

End blockvocab.

Global Arguments bnd_at {P D} _ {_} _ _.
Global Arguments blk_no {P D} _ {_} _ _.

(* ================================================================== *)
(** * §2  THE STEP-EXPORTING TWIN OF [Qinv_step]

    [WeakRobustSim.Qinv_step] establishes the invariant after one traced
    event but CONSUMES the [wp_pf_step] it builds ([qcfg_step] takes it
    as a hypothesis and only the [rtc] survives in [qcfg]).  The
    regrouping stage needs the individual steps, so the same five label
    arms are re-run here with the step HANDED OUT alongside the new
    configuration.  Nothing else changes: every side condition is
    discharged by the very lemmas [Qinv_step] uses
    ([read_ok_pf], [excl_ok_pf], [qcfg_step]). *)

Section stepout.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pcls : P → wlabel → wstate → wm_class).
  Context (pdev : P → wlabel → P → bool).
  Context (TS : ptraces P D) (img : image) (d0 : D) (ps : list P).
  Context (Hwf : ptraces_wf pstep TS).
  Context (Hwsi : ptraces_ws_init TS).
  Context (Hco : ∀ a, WeakRobustSer.co_tc TS a).
  Context (Hwfl : WeakRobustSer.writes_fulfilled TS).
  Context (Hlf : lat_free_prog pstep).
  Context (Hobl : ts_oblivious pstep).
  (** THE CLASS HALVES OF G6a (see [WeakRobustSim]'s [Section sim]):
      [wp_pf_step] pins the class of every message it appends, so the
      replay needs the recorded log to be canonically classed and [pcls]
      to be timestamp-blind. *)
  Context (Hcls : cls_canonical pcls TS).
  Context (Hclsobl : pcls_obl pcls).
  Context (Himg : pt_img TS = img).
  Context (Hnag : length (pt_trs TS) = length ps).
  Context (Hdata : ∀ p m, pt_log TS !! p = Some m → wm_data m ≠ []).
  (** the fabric scope, as in [WeakRobustSim] (G4's boundary) *)
  Context (Hdf : ∀ j T k ev, pt_trs TS !! j = Some T →
                   at_evs T !! k = Some ev → ae_dev ev = None).

  Implicit Types done : list gev.
  Implicit Types e : gev.

  (** [qcfg_step], repackaged so that the arms below can be transcribed
      from [Qinv_step] verbatim. *)
  Lemma qcfg_step_ex done e T ev ag' cf newws lb' (dv : D) :
    qorder TS done →
    nproc done e.1 = e.2 →
    pt_trs TS !! e.1 = Some T → at_evs T !! e.2 = Some ev →
    at_ags T !! S e.2 = Some ag' →
    qcfg pstep pcls TS (PDevs d0 []) img d0 ps done cf →
    newws = aev_post (pi TS (done ++ [e])) ev
              (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) →
    qfab TS (PDevs d0 []) (done ++ [e]) dv →
    wp_pf_step pstep pcls e.1 lb' cf
      (WPCfg (pc_img cf) (pf_log TS (done ++ [e])) dv
             (<[e.1 := WPAgent (pa_st ag') newws ∅]> (pc_ags cf))) →
    ∃ lb cf', wp_pf_step pstep pcls e.1 lb cf cf' ∧
              qcfg pstep pcls TS (PDevs d0 []) img d0 ps (done ++ [e]) cf'.
  Proof.
    intros Hq Hnp HT Hev Hag' Hc Hnew Hdv Hstep.
    eexists lb', _. split; [exact Hstep|].
    by eapply (qcfg_step pstep pcls TS (PDevs d0 []) img d0 ps Hwf Hwfl Hnag
                 done e T ev ag' cf newws lb' dv).
  Qed.

  (** THE STEP, EXPORTED. *)
  Lemma Qcfg_step done e cf :
    qorder TS done → qcfg pstep pcls TS (PDevs d0 []) img d0 ps done cf →
    gev_wf TS e → e ∉ done →
    (∀ e', gdep2 TS e' e → gev_wf TS e' → e' ∈ done) →
    ∃ lb cf', wp_pf_step pstep pcls e.1 lb cf cf' ∧
              qcfg pstep pcls TS (PDevs d0 []) img d0 ps (done ++ [e]) cf'.
  Proof.
    intros Hq Hc Hwfe Hnin Hpre.
    have Hnp : nproc done e.1 = e.2
      by exact (nproc_cur TS ps Hnag done e Hq Hwfe Hnin Hpre).
    have Hq' : qorder TS (done ++ [e])
      by exact (qorder_step TS ps Hnag done e Hq Hwfe Hnin Hpre).
    have Hpre3 : ∀ e', gdep3 TS (PDevs d0 []) e' e → gev_wf TS e' → e' ∈ done.
    { intros e' Hd%(gdep3_nil_gdep2 TS d0) Hw'. by apply Hpre. }
    have Hc' := Hc.
    destruct Hc' as (Hrun & Hcimg & Hclog & Hclen & Hcags & Hfab).
    destruct (proj1 (gev_wf_bounds TS e) Hwfe) as (T & HT & Hklt).
    have [ev Hev] : is_Some (at_evs T !! e.2) by apply lookup_lt_is_Some_2.
    have Hgev : gev_ev TS e = Some ev by rewrite /gev_ev HT /=.
    have Hatr : atrace_wf pstep (pt_img TS) (pt_log TS) e.1 T by apply Hwf.
    destruct (asteps_wf_step pstep (pt_img TS) (pt_log TS) e.1 (at_ags T)
                (at_evs T) e.2 ev Hatr Hev)
      as (ag & ag2 & st' & f & Hag & Hag2 & Hps & Hok & Hagn).
    destruct (qfab_step pstep TS (PDevs d0 []) ps Hnag
                (ptraces_wit_nil TS d0 Hdf)
                done e T ev ag st' cf Hnin Hpre3 HT Hev Hps Hfab)
      as (dnew & Hpure & Hfab').
    destruct (Hcags e.1 T HT) as (agn & Hagn0 & Hcflk).
    rewrite Hnp Hag in Hagn0. injection Hagn0 as <-. rewrite Hnp in Hcflk.
    have Hstpost : pa_st ag2 = st' by rewrite Hagn.
    (* π is stable on everything this event READS *)
    have Hstab : ∀ a t, gev_reads TS e a t → pi TS (done ++ [e]) t = pi TS done t.
    { intros a t Hr. apply pi_app.
      destruct (decide (t = 0%nat)) as [->|Ht]; [by right|].
      left. eapply (read_ts_in_fl pstep TS Hwf Hwfl);
        [done|exact Hpre|exact Hr|lia]. }
    have Hokc := Hok.
    destruct (ae_lb ev) as [|aq lat base tvs asrc|rl base data asrc vsrc
                            |aq rl base tvs data asrc vsrc
                            |pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc] eqn:Hlbe.
    - (* ---- LSilent ---- *)
      destruct Hok as (Hf & Hts0).
      have Hgts : gev_ts TS e = None by rewrite /gev_ts Hgev /= Hts0.
      have Hlogq : pf_log TS (done ++ [e]) = pc_log cf.
      { by rewrite Hclog /pf_log (fl_app_none TS done e Hgts). }
      eapply (qcfg_step_ex done e T ev ag2 cf
                 (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) LSilent);
        [done|done|done|done|done|done| |exact Hfab'|].
      + by rewrite /aev_post Hlbe.
      + rewrite Hstpost Hlogq.
        apply (PFSilent pstep pcls e.1 cf (WPAgent (pa_st ag)
                 (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) ∅) st'
                 dnew);
          [done|]. simpl. exact Hpure.
    - (* ---- LLoad ---- *)
      have Hlat : lat = false.
      { destruct lat; [|done]. exfalso.
        by destruct (lat_free_prog_lat pstep _ _ _ _ _ _ _ _ Hlf Hpure). }
      subst lat.
      destruct Hok as (Hro & Hf & Hts0).
      have Hgts : gev_ts TS e = None by rewrite /gev_ts Hgev /= Hts0.
      have Hlogq : pf_log TS (done ++ [e]) = pc_log cf.
      { by rewrite Hclog /pf_log (fl_app_none TS done e Hgts). }
      have Hmap : (pi TS (done ++ [e])) <$> tvs.*1 = (pi TS done) <$> tvs.*1.
      { apply list_fmap_ext. intros i t Hi.
        rewrite list_lookup_fmap in Hi.
        destruct (tvs !! i) as [[t' v]|] eqn:Htv; simplify_eq/=.
        apply (Hstab (base + Z.of_nat i)). exists (ae_lb ev).
        split; [by rewrite /gev_lb Hgev|].
        rewrite Hlbe /=. apply elem_of_tvs_reads. by exists i, v. }
      eapply (qcfg_step_ex done e T ev ag2 cf
                 (load_post_run_d (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) aq (srcs_view (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) asrc) base
                    ((tlabel_ts (pi TS done) tvs).*1))
                 (LLoad aq false base (tlabel_ts (pi TS done) tvs) asrc));
        [done|done|done|done|done|done| |exact Hfab'|].
      + by rewrite /aev_post Hlbe tlabel_ts_fst Hmap.
      + rewrite Hstpost Hlogq.
        apply (PFLoad pstep pcls e.1 cf (WPAgent (pa_st ag) (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) ∅)
                 aq false base (tlabel_ts (pi TS done) tvs) asrc st' dnew);
          [done| |].
        * simpl. eapply (proj1 Hobl (pa_st ag) (pc_dev cf) aq false base tvs);
            [by rewrite tlabel_ts_snd|]. exact Hpure.
        * simpl. rewrite Hcimg Hclog.
          eapply (read_ok_pf pstep pdev TS img ps Hwf Hwsi Hco Hwfl Himg Hnag
                    done e T ev ag (LLoad aq false base tvs asrc) base tvs
                    false);
            [done|done|done|done|done|done|exact Hlbe|done|done| |done].
          exact Hro.
    - (* ---- LStore ---- *)
      destruct Hok as (ts & kc & _ & Hlog & _ & Hf & Hts).
      have Hgts : gev_ts TS e = Some ts by rewrite /gev_ts Hgev /= Hts.
      have Hmsg : msg_at TS ts = WMsg base data (Some e.1) kc by apply msg_at_eq.
      have Hlogq : pf_log TS (done ++ [e])
                   = pc_log cf ++ [WMsg base data (Some e.1) kc].
      { by rewrite Hclog /pf_log (fl_app_some TS done e ts Hgts)
                   fmap_app /= Hmsg. }
      have Hpits : pi TS (done ++ [e]) ts = S (length (pc_log cf)).
      { rewrite Hclog fl_len. eapply (pi_mem pstep pdev TS ps Hwf Hnag); [done|].
        rewrite (fl_app_some TS done e ts Hgts) lookup_app_r; [lia|].
        by rewrite Nat.sub_diag. }
      have Hnedata : data ≠ []
        by exact (Hdata (ts - 1)%nat (WMsg base data (Some e.1) kc) Hlog).
      eapply (qcfg_step_ex done e T ev ag2 cf
                 (store_post_run_d (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) rl (srcs_view (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) asrc)
                    (srcs_view (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) vsrc) base (length data)
                    (S (length (pc_log cf))))
                 (LStore rl base data asrc vsrc));
        [done|done|done|done|done|done| |exact Hfab'|].
      + by rewrite /aev_post Hlbe Hts Hpits.
      + rewrite Hstpost Hlogq.
        apply (PFStore pstep pcls e.1 cf (WPAgent (pa_st ag) (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) ∅)
                 rl base data asrc vsrc kc st' dnew); [done| |done|].
        * simpl. exact Hpure.
        * (* THE PINNED CLASS (G6a) — as in [WeakRobustSim.Qinv_step] *)
          have Hkc : kc = pcls (pa_st ag) (ae_lb ev) (pa_ws ag).
          { exact (Hcls e.1 T e.2 ev ag ts (WMsg base data (Some e.1) kc)
                     HT Hev Hag Hts Hlog). }
          simpl. rewrite Hkc Hlbe.
          apply (proj1 Hclsobl).
          by eapply (replay_ws_relp pstep TS Hwf Hwsi e.1 e.2 T ag).
    - (* ---- LRmw ---- *)
      destruct Hok as (ts & kc & Hlen & _ & Hlog & Hro & Hex & _ & Hf & Hts).
      have Hgts : gev_ts TS e = Some ts by rewrite /gev_ts Hgev /= Hts.
      have Hmsg : msg_at TS ts = WMsg base data (Some e.1) kc by apply msg_at_eq.
      have Hlogq : pf_log TS (done ++ [e])
                   = pc_log cf ++ [WMsg base data (Some e.1) kc].
      { by rewrite Hclog /pf_log (fl_app_some TS done e ts Hgts)
                   fmap_app /= Hmsg. }
      have Hpits : pi TS (done ++ [e]) ts = S (length (pc_log cf)).
      { rewrite Hclog fl_len. eapply (pi_mem pstep pdev TS ps Hwf Hnag); [done|].
        rewrite (fl_app_some TS done e ts Hgts) lookup_app_r; [lia|].
        by rewrite Nat.sub_diag. }
      have Hnedata : data ≠ []
        by exact (Hdata (ts - 1)%nat (WMsg base data (Some e.1) kc) Hlog).
      have Hmap : (pi TS (done ++ [e])) <$> tvs.*1 = (pi TS done) <$> tvs.*1.
      { apply list_fmap_ext. intros i t Hi.
        rewrite list_lookup_fmap in Hi.
        destruct (tvs !! i) as [[t' v]|] eqn:Htv; simplify_eq/=.
        apply (Hstab (base + Z.of_nat i)). exists (ae_lb ev).
        split; [by rewrite /gev_lb Hgev|].
        rewrite Hlbe /=. apply elem_of_tvs_reads. by exists i, v. }
      eapply (qcfg_step_ex done e T ev ag2 cf
                 (store_post_run_d
                    (load_post_run_d (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) aq (srcs_view (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) asrc) base
                       ((tlabel_ts (pi TS done) tvs).*1))
                    rl (srcs_view (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) asrc) (srcs_view (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) vsrc)
                    base (length data) (S (length (pc_log cf))))
                 (LRmw aq rl base (tlabel_ts (pi TS done) tvs) data asrc vsrc));
        [done|done|done|done|done|done| |exact Hfab'|].
      + by rewrite /aev_post Hlbe Hts tlabel_ts_fst Hmap Hpits.
      + rewrite Hstpost Hlogq.
        apply (PFRmw pstep pcls e.1 cf (WPAgent (pa_st ag) (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) ∅)
                 aq rl base (tlabel_ts (pi TS done) tvs) data asrc vsrc kc st'
                 dnew);
          [done| |done| | | |].
        * simpl. eapply (proj2 Hobl (pa_st ag) (pc_dev cf) aq rl base tvs);
            [by rewrite tlabel_ts_snd|]. exact Hpure.
        * by rewrite tlabel_ts_length.
        * simpl. rewrite Hcimg Hclog.
          eapply (read_ok_pf pstep pdev TS img ps Hwf Hwsi Hco Hwfl Himg Hnag
                    done e T ev ag (LRmw aq rl base tvs data asrc vsrc) base
                    tvs false);
            [done|done|done|done|done|done|exact Hlbe|done|done| |done].
          exact Hro.
        * simpl. rewrite Hclog.
          eapply (excl_ok_pf pstep pdev TS ps Hwf Hco Hwfl Hnag
                    done e T ev ag f aq rl base tvs data asrc vsrc ts);
            [done|done|done|done|done|exact Hlbe|exact Hts|].
          by rewrite Hlbe.
        * (* THE PINNED CLASS (G6a) — as in [WeakRobustSim.Qinv_step] *)
          have Hkc : kc = pcls (pa_st ag) (ae_lb ev) (pa_ws ag).
          { exact (Hcls e.1 T e.2 ev ag ts (WMsg base data (Some e.1) kc)
                     HT Hev Hag Hts Hlog). }
          simpl. rewrite Hkc Hlbe.
          apply (proj2 Hclsobl); [by rewrite tlabel_ts_snd|].
          by eapply (replay_ws_relp pstep TS Hwf Hwsi e.1 e.2 T ag).
    - (* ---- LFence ---- *)
      destruct Hok as (Hf & Hts0).
      have Hgts : gev_ts TS e = None by rewrite /gev_ts Hgev /= Hts0.
      have Hlogq : pf_log TS (done ++ [e]) = pc_log cf.
      { by rewrite Hclog /pf_log (fl_app_none TS done e Hgts). }
      eapply (qcfg_step_ex done e T ev ag2 cf
                 (fence_post (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) pr pw sr sw)
                 (LFence pr pw sr sw));
        [done|done|done|done|done|done| |exact Hfab'|].
      + by rewrite /aev_post Hlbe.
      + rewrite Hstpost Hlogq.
        apply (PFFence pstep pcls e.1 cf (WPAgent (pa_st ag)
                 (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) ∅)
                 pr pw sr sw st' dnew); [done|]. simpl. exact Hpure.
    - (* ---- LDev: the LSilent case verbatim, at [PFDev] ---- *)
      destruct Hok as (Hf & Hts0).
      have Hgts : gev_ts TS e = None by rewrite /gev_ts Hgev /= Hts0.
      have Hlogq : pf_log TS (done ++ [e]) = pc_log cf.
      { by rewrite Hclog /pf_log (fl_app_none TS done e Hgts). }
      eapply (qcfg_step_ex done e T ev ag2 cf
                 (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) LDev);
        [done|done|done|done|done|done| |exact Hfab'|].
      + by rewrite /aev_post Hlbe.
      + rewrite Hstpost Hlogq.
        apply (PFDev pstep pcls e.1 cf (WPAgent (pa_st ag) (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) ∅) st'
                 dnew);
          [done|]. simpl. exact Hpure.
    - (* ---- LRegW ---- *)
      destruct Hok as (Hf & Hts0).
      have Hgts : gev_ts TS e = None by rewrite /gev_ts Hgev /= Hts0.
      have Hlogq : pf_log TS (done ++ [e]) = pc_log cf.
      { by rewrite Hclog /pf_log (fl_app_none TS done e Hgts). }
      eapply (qcfg_step_ex done e T ev ag2 cf
                 (regw_post (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) rdw (srcs_view (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) wsrc))
                 (LRegW rdw wsrc));
        [done|done|done|done|done|done| |exact Hfab'|].
      + by rewrite /aev_post Hlbe.
      + rewrite Hstpost Hlogq.
        apply (PFRegW pstep pcls e.1 cf (WPAgent (pa_st ag) (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) ∅)
                 rdw wsrc st' dnew);
          [done|]. simpl. exact Hpure.
    - (* ---- LCtrl ---- *)
      destruct Hok as (Hf & Hts0).
      have Hgts : gev_ts TS e = None by rewrite /gev_ts Hgev /= Hts0.
      have Hlogq : pf_log TS (done ++ [e]) = pc_log cf.
      { by rewrite Hclog /pf_log (fl_app_none TS done e Hgts). }
      eapply (qcfg_step_ex done e T ev ag2 cf
                 (ctrl_post (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) (srcs_view (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) csrc)) (LCtrl csrc));
        [done|done|done|done|done|done| |exact Hfab'|].
      + by rewrite /aev_post Hlbe.
      + rewrite Hstpost Hlogq.
        apply (PFCtrl pstep pcls e.1 cf (WPAgent (pa_st ag) (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) ∅)
                 csrc st' dnew);
          [done|]. simpl. exact Hpure.
    - (* ---- LInstr ---- *)
      destruct Hok as (Hf & Hts0).
      have Hgts : gev_ts TS e = None by rewrite /gev_ts Hgev /= Hts0.
      have Hlogq : pf_log TS (done ++ [e]) = pc_log cf.
      { by rewrite Hclog /pf_log (fl_app_none TS done e Hgts). }
      eapply (qcfg_step_ex done e T ev ag2 cf (instr_post (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init)) LInstr);
        [done|done|done|done|done|done| |exact Hfab'|].
      + by rewrite /aev_post Hlbe.
      + rewrite Hstpost Hlogq.
        apply (PFInstr pstep pcls e.1 cf (WPAgent (pa_st ag) (aevs_post (pi TS done) (take e.2 (at_evs T)) ws_init) ∅) st'
                 dnew);
          [done|]. simpl. exact Hpure.
    (* THE RMW SPLIT (S2): as in [WeakRobustSim.Qinv_step] — the pf replay
       is S4's slice, and until then the alphabet premise refutes the pair *)
    - exfalso. exact (lat_free_prog_fused pstep _ _ _ _ _ Hlf Hpure).
    - exfalso. exact (lat_free_prog_fused pstep _ _ _ _ _ Hlf Hpure).
  Qed.

End stepout.

(* ================================================================== *)
(** * §3  THE CONE'S BLOCKS

    The whole development runs in ONE section whose context mirrors
    [WeakRobustMain]'s exhibit, plus the boundary predicate [bnd] and the
    structural premise [Hcsl]. *)

Section coneblocks.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pcls : P → wlabel → wstate → wm_class).
  Context (pdev : P → wlabel → P → bool).
  Context (TS : ptraces P D) (img : image) (d0 : D) (ps : list P).
  Context (Hwf : ptraces_wf pstep TS).
  Context (Hwsi : ptraces_ws_init TS).
  Context (Hco : ∀ a, WeakRobustSer.co_tc TS a).
  Context (Hwfl : WeakRobustSer.writes_fulfilled TS).
  Context (Hlf : lat_free_prog pstep).
  Context (Hobl : ts_oblivious pstep).
  (** THE CLASS HALVES OF G6a (see [WeakRobustSim]'s [Section sim]):
      [wp_pf_step] pins the class of every message it appends, so the
      replay needs the recorded log to be canonically classed and [pcls]
      to be timestamp-blind. *)
  Context (Hcls : cls_canonical pcls TS).
  Context (Hclsobl : pcls_obl pcls).
  Context (Himg : pt_img TS = img).
  Context (Hnag : length (pt_trs TS) = length ps).
  Context (Hdata : ∀ p m, pt_log TS !! p = Some m → wm_data m ≠ []).
  Context (Hdf : ∀ j T k ev, pt_trs TS !! j = Some T →
                   at_evs T !! k = Some ev → ae_dev ev = None).
  Context (Hps0 : ∀ j T ag0, pt_trs TS !! j = Some T →
                    at_ags T !! 0%nat = Some ag0 → ps !! j = Some (pa_st ag0)).
  Context (Hfo : WeakRobustAcyc.ptraces_fwd_own TS).
  Context (Hee : WeakRobustAcyc2.ee_ok TS).
  Context (nh : nat).
  Context (Hsplit : edges_split_cyc nh TS (PDevs d0 [])).

  (** THE BOUNDARY PREDICATE and the two premises about it. *)
  Context (bnd : P → Prop).
  Context `{!∀ p, Decision (bnd p)}.
  (** initial states are at boundaries *)
  Context (Hbnd0 : ∀ i T ag0, pt_trs TS !! i = Some T →
                     at_ags T !! 0%nat = Some ag0 → bnd (pa_st ag0)).
  (** THE STRUCTURAL PREMISE (the design's (P1')/(P2), trace level):
      after a cross-edge source, and until the next boundary state, the
      agent's events are non-memory. *)
  Context (Hcsl : ∀ e1 e2, gdep2 TS e1 e2 → e1.1 ≠ e2.1 →
    ∀ T, pt_trs TS !! e1.1 = Some T →
    ∀ k' ev', (e1.2 < k')%nat → at_evs T !! k' = Some ev' →
    (∀ k'' ag'', (e1.2 < k'')%nat → (k'' ≤ k')%nat →
       at_ags T !! k'' = Some ag'' → ¬ bnd (pa_st ag'')) →
    lb_writes (ae_lb ev') = false ∧ lb_loads (ae_lb ev') = false).

  Implicit Types e : gev.

  (* ---------------------------------------------------------------- *)
  (** ** §3.1  Block identifiers *)

  (** The block NUMBER of an event: how many boundary states its agent
      passed through before it. *)
  Definition bno (e : gev) : nat :=
    match pt_trs TS !! e.1 with
    | Some T => blk_no bnd T e.2
    | None => 0%nat
    end.

  (** The block IDENTIFIER: agent and block number. *)
  Definition bid (e : gev) : nat * nat := (e.1, bno e).

  Lemma bid_agent e : (bid e).1 = e.1.
  Proof. done. Qed.

  (** SAME AGENT, SAME BLOCK ⟺ no boundary state strictly between. *)
  Lemma bid_same_gap e x T m :
    pt_trs TS !! e.1 = Some T → x.1 = e.1 → bid x = bid e →
    (e.2 ≤ m)%nat → (S m ≤ x.2)%nat → bnd_at bnd T (S m) = false.
  Proof.
    intros HT Hag Hbid Hle1 Hle2.
    have Hb : blk_no bnd T x.2 = blk_no bnd T e.2.
    { move: Hbid. rewrite /bid /bno Hag HT. by intros [= ->]. }
    by eapply (blk_no_gap bnd T e.2 x.2 m).
  Qed.

  (** SAME AGENT, DIFFERENT BLOCKS ⟹ block numbers and trace indices
      agree on their order (blocks are intervals). *)
  Lemma bno_lt_index x y : (bno x < bno y)%nat → x.1 = y.1 → (x.2 < y.2)%nat.
  Proof.
    rewrite /bno. intros Hlt Hag. rewrite Hag in Hlt.
    destruct (pt_trs TS !! y.1) as [T|]; [|lia].
    by eapply blk_no_lt_index.
  Qed.

  Lemma bno_le_of_index x y :
    x.1 = y.1 → (x.2 ≤ y.2)%nat → (bno x ≤ bno y)%nat.
  Proof.
    rewrite /bno. intros Hag Hle. rewrite Hag.
    destruct (pt_trs TS !! y.1) as [T|]; [|lia].
    by apply blk_no_mono.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** §3.2  Memory events, cross sources and cross targets *)

  (** A MEMORY event: its label appends a message or reads one. *)
  Definition is_mem e : Prop :=
    ∃ l, gev_lb TS e = Some l ∧ (lb_writes l = true ∨ lb_loads l = true).

  (** A fulfil writes. *)
  Lemma ts_writes e ts :
    gev_ts TS e = Some ts → ∃ l, gev_lb TS e = Some l ∧ lb_writes l = true.
  Proof.
    rewrite /gev_ts /gev_lb. intros Hts.
    destruct (gev_ev TS e) as [ev|] eqn:Hev; simpl in Hts; [|done].
    destruct (gev_step pstep TS e ev Hwf Hev)
      as (T & ag & ag' & st' & f & _ & _ & _ & _ & Hok & _).
    exists (ae_lb ev). split; [done|].
    destruct (lb_writes (ae_lb ev)) eqn:Hlw; [done|].
    by rewrite (lb_writes_ts_none _ _ _ _ _ _ _ Hok Hlw) in Hts.
  Qed.

  Lemma ts_mem e ts : gev_ts TS e = Some ts → is_mem e.
  Proof.
    intros Hts. destruct (ts_writes e ts Hts) as (l & Hl & Hw).
    exists l. split; [done|by left].
  Qed.

  (** A read loads. *)
  Lemma reads_loads e a t :
    gev_reads TS e a t → ∃ l, gev_lb TS e = Some l ∧ lb_loads l = true.
  Proof.
    intros (l & Hl & Hin). exists l. split; [done|].
    destruct l; simpl in Hin; try (by apply elem_of_nil in Hin); done.
  Qed.

  Lemma reads_mem e a t : gev_reads TS e a t → is_mem e.
  Proof.
    intros Hr. destruct (reads_loads e a t Hr) as (l & Hl & Hw).
    exists l. split; [done|by right].
  Qed.

  (** A CROSS SOURCE: an event with a [gdep2] edge to another agent. *)
  Definition xsrc e : Prop := ∃ v, gdep2 TS e v ∧ e.1 ≠ v.1.

  Lemma xsrc_mem e : xsrc e → is_mem e.
  Proof.
    intros (v & Hd & Hne).
    destruct (cross_edge_fulfil TS e v Hd Hne) as (ts & Hts).
    by eapply ts_mem.
  Qed.

  (** DELIVERABLE 2b: CROSS TARGETS ARE MEMORY EVENTS.  The rf arm's
      target READS the message; the [gE] arm's target is a FULFIL
      ([WeakRobustOrd.gE_at] pins [gev_ts] of both ends). *)
  Lemma cross_tgt_mem e1 e2 : gdep2 TS e1 e2 → e1.1 ≠ e2.1 → is_mem e2.
  Proof.
    intros [[Hpo|Hrf]|HE] Hne.
    - by destruct Hpo as (Hag & _).
    - destruct Hrf as (ts & a & _ & Hrd). by eapply reads_mem.
    - destruct (gE_ts_lt_ex TS e1 e2 HE) as (t1 & t2 & _ & Hts2 & _).
      by eapply ts_mem.
  Qed.

  (** DELIVERABLE 2a: CROSS SOURCES ARE BLOCK-LAST MEMORY EVENTS.  This
      is [Hcsl], read through the block vocabulary. *)
  Lemma cross_src_last e1 e2 x :
    gdep2 TS e1 e2 → e1.1 ≠ e2.1 →
    x.1 = e1.1 → (e1.2 < x.2)%nat → bid x = bid e1 → gev_wf TS x →
    ¬ is_mem x.
  Proof.
    intros Hd Hne Hag Hlt Hbid Hwfx.
    destruct (gdep2_wf TS e1 e2 Hd) as (Hwf1 & _).
    destruct (proj1 (gev_wf_bounds TS e1) Hwf1) as (T & HT & _).
    have HTx : pt_trs TS !! x.1 = Some T by rewrite Hag.
    destruct (proj1 (gev_wf_bounds TS x) Hwfx) as (T' & HT' & Hxlt).
    rewrite HTx in HT'. injection HT' as <-.
    have [ev' Hev'] : is_Some (at_evs T !! x.2) by apply lookup_lt_is_Some_2.
    have Hnob : ∀ k'' ag'', (e1.2 < k'')%nat → (k'' ≤ x.2)%nat →
                  at_ags T !! k'' = Some ag'' → ¬ bnd (pa_st ag'').
    { intros k'' ag'' H1 H2 Hlk.
      have Hk : k'' = S (k'' - 1)%nat by lia.
      rewrite Hk in Hlk |- *.
      eapply (bnd_at_false bnd T); [exact Hlk|].
      eapply (bid_same_gap e1 x T (k'' - 1)%nat HT Hag Hbid); lia. }
    destruct (Hcsl e1 e2 Hd Hne T HT x.2 ev' Hlt Hev' Hnob) as (Hw & Hl).
    intros (l & Hlb & Hor).
    have Hleq : l = ae_lb ev'.
    { move: Hlb. rewrite /gev_lb /gev_ev HTx /= Hev' /=. by intros [= ->]. }
    subst l. destruct Hor as [Hc|Hc]; by rewrite Hc in Hw Hl.
  Qed.

  (** AT MOST ONE CROSS SOURCE PER BLOCK. *)
  Lemma xsrc_unique w1 w2 :
    xsrc w1 → xsrc w2 → bid w1 = bid w2 →
    gev_wf TS w1 → gev_wf TS w2 → w1 = w2.
  Proof.
    intros Hx1 Hx2 Hbid Hw1 Hw2.
    have Hag : w1.1 = w2.1 by move: Hbid; rewrite /bid; intros [= ? ?].
    have Hkey : ∀ u v, xsrc u → bid u = bid v → v.1 = u.1 →
                  (u.2 < v.2)%nat → gev_wf TS v → is_mem v → False.
    { intros u v (z & Hd & Hne) Hb Hag' Hlt Hwfv Hm.
      by eapply (cross_src_last u z v Hd Hne Hag' Hlt (eq_sym Hb) Hwfv). }
    destruct (decide (w1.2 = w2.2)) as [Heq|Hne2].
    - destruct w1 as [a1 k1], w2 as [a2 k2]. simpl in Hag, Heq. by subst.
    - exfalso. destruct (decide (w1.2 < w2.2)%nat) as [Hlt|Hgt].
      + eapply (Hkey w1 w2 Hx1 Hbid); [done|done|done|by apply xsrc_mem].
      + eapply (Hkey w2 w1 Hx2 (eq_sym Hbid)); [done|lia|done|by apply xsrc_mem].
  Qed.

  (** A block's cross TARGETS sit program-order at-or-before its cross
      SOURCE — the composition step of the contracted-cycle argument. *)
  Lemma xtgt_le_xsrc y w :
    is_mem y → xsrc w → bid y = bid w → gev_wf TS y → (y.2 ≤ w.2)%nat.
  Proof.
    intros Hm (z & Hd & Hne) Hbid Hwfy.
    destruct (decide (y.2 ≤ w.2)%nat) as [?|Hgt]; [done|exfalso].
    have Hag : y.1 = w.1 by move: Hbid; rewrite /bid; intros [= ? ?].
    eapply (cross_src_last w z y Hd Hne Hag); [lia|by rewrite Hbid|done|done].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** §3.3  SAME-AGENT [gdep2] EDGES RESPECT PROGRAM ORDER

      [gpo] and [grf] do by [WeakRobustGraph]; the [gE] arm is exactly
      what [WeakRobustAcyc2.ee_ok] rules out (an [E] edge whose target
      precedes its source inside one agent would put the source — a
      floor LEAF — strictly above the floor). *)
  Lemma gdep2_sa_lt x y : gdep2 TS x y → x.1 = y.1 → (x.2 < y.2)%nat.
  Proof.
    intros [Hd|HE] Hag; [by eapply (gdep_same_agent_lt pstep TS)|].
    destruct HE as (r & Hat).
    destruct (WeakRobustAcyc2.gE_at_gE_ra TS r x y Hat) as (a & Hra).
    have Hra' := Hra.
    destruct Hra' as (l & ts & tstar & that & Hlb & Hin & Hleaf & Hpos &
                      Hts1 & Hts2 & Hw & Hlt).
    have Hfl : (tstar ≤ rd_floor TS r a)%nat
      by apply (lval_ge id (rd_leaves TS r a) tstar Hleaf).
    destruct (decide (x.2 < y.2)%nat) as [?|Hge]; [done|exfalso].
    destruct (decide (x.2 = y.2)) as [Heq|Hne].
    - have Hxy : x = y.
      { destruct x as [a1 k1], y as [a2 k2]. simpl in Hag, Heq. by subst. }
      rewrite Hxy Hts2 in Hts1. injection Hts1 as ->. lia.
    - have Hlt' : (y.2 < x.2)%nat by lia.
      have := Hee r a x y x tstar Hra (eq_sym Hag) Hlt' Hts1. lia.
  Qed.

  Lemma gdep2_sa_ne x y : gdep2 TS x y → x.1 = y.1 → x ≠ y.
  Proof. intros Hd Hag ->. have := gdep2_sa_lt y y Hd Hag. lia. Qed.


  (* ---------------------------------------------------------------- *)
  (** ** §3.4  Decidability of the cross-source predicate *)

  Global Instance xsrc_dec e : Decision (xsrc e).
  Proof.
    destruct (decide (Exists (λ v, gdep2 TS e v ∧ e.1 ≠ v.1) (gev_enum TS)))
      as [Hex|Hex].
    - left. apply list_relations.Exists_exists in Hex as (v & _ & Hv).
      by exists v.
    - right. intros (v & Hd & Hne). apply Hex, list_relations.Exists_exists.
      exists v. split; [|done].
      apply elem_of_gev_enum. by destruct (gdep2_wf TS e v Hd).
  Defined.

  (* ================================================================ *)
  (** * §4  THE CONE AND ITS BLOCK-CONTRACTED GRAPH

      The bad read [b2], a topological order [ord0] of its strict
      ancestor cone (what [WeakRobustMain.cone_Qinv] hands out), and the
      block relation on that cone. *)

  Context (b2 : gev).
  Context (Hb2wf : gev_wf TS b2).
  Context (Hrr : ¬ tc (gdep2 TS) b2 b2).
  (** the bad read IS a memory event (it reads the bad message) *)
  Context (Hb2mem : is_mem b2).
  Context (ord0 : list gev).
  Context (HQ0 : Qinv pstep pcls TS (PDevs d0 []) img d0 ps ord0).
  Context (Hmem0 : ∀ e, e ∈ ord0 ↔ (gev_wf TS e ∧ tc (gdep2 TS) e b2)).

  (** The cone WITH the bad read: the carrier of every ordering
      argument below. *)
  Definition cl : list gev := ord0 ++ [b2].

  Lemma ord0_wf e : e ∈ ord0 → gev_wf TS e.
  Proof. intros He. by apply Hmem0 in He as [? _]. Qed.

  Lemma ord0_tc e : e ∈ ord0 → tc (gdep2 TS) e b2.
  Proof. intros He. by apply Hmem0 in He as [_ ?]. Qed.

  Lemma b2_nin : b2 ∉ ord0.
  Proof. intros He. by apply Hrr, ord0_tc. Qed.

  Lemma b2_pre x : gdep2 TS x b2 → gev_wf TS x → x ∈ ord0.
  Proof. intros Hd Hw. apply Hmem0. split; [done|by apply tc_once]. Qed.

  Lemma ord0_dc x y : y ∈ ord0 → gdep2 TS x y → gev_wf TS x → x ∈ ord0.
  Proof.
    intros Hy Hd Hw. apply Hmem0. split; [done|].
    eapply tc_l; [exact Hd|by apply ord0_tc].
  Qed.

  Lemma elem_of_cl e : e ∈ cl ↔ (e ∈ ord0 ∨ e = b2).
  Proof.
    rewrite /cl elem_of_app elem_of_list_singleton. done.
  Qed.

  Lemma ord0_cl e : e ∈ ord0 → e ∈ cl.
  Proof. intros He. apply elem_of_cl. by left. Qed.

  Lemma b2_cl : b2 ∈ cl.
  Proof. apply elem_of_cl. by right. Qed.

  Lemma cl_wf e : e ∈ cl → gev_wf TS e.
  Proof.
    intros He. apply elem_of_cl in He as [He|He]; [by apply ord0_wf|by subst].
  Qed.

  (** …and the cone is DOWNWARD CLOSED. *)
  Lemma cl_dc x y : y ∈ cl → gdep2 TS x y → gev_wf TS x → x ∈ ord0.
  Proof.
    intros Hy Hd Hw. apply elem_of_cl in Hy as [Hy|Hy];
      [by eapply ord0_dc|subst; by apply b2_pre].
  Qed.

  Lemma cl_dc' x y : y ∈ cl → gdep2 TS x y → gev_wf TS x → x ∈ cl.
  Proof. intros ???. apply ord0_cl. by eapply cl_dc. Qed.

  (** ONE more [Qinv_step]: the cone plus the bad read is still a
      [qorder], which is all the positional lemmas need. *)
  Lemma HQcl : Qinv pstep pcls TS (PDevs d0 []) img d0 ps cl.
  Proof.
    eapply (Qinv_step pstep pcls pdev TS (PDevs d0 []) img d0 ps Hwf Hwsi Hco Hwfl
              Hlf Hobl Hcls Hclsobl Himg Hnag Hdata (ptraces_wit_nil TS d0 Hdf)
              ord0 b2 HQ0 Hb2wf b2_nin).
    intros e' Hd%(gdep3_nil_gdep2 TS d0) Hw'. by apply b2_pre.
  Qed.

  Lemma Hqcl : qorder TS cl.
  Proof. by eapply (Qinv_order pstep pcls TS (PDevs d0 []) img d0 ps), HQcl. Qed.

  Lemma ord0_nodup : NoDup ord0.
  Proof. by destruct (Qinv_order pstep pcls TS (PDevs d0 []) img d0 ps ord0 HQ0) as (? & _). Qed.

  Lemma cl_nodup : NoDup cl.
  Proof. by destruct Hqcl as (? & _). Qed.

  (* ---------------------------------------------------------------- *)
  (** ** §4.1  The event-level position, and cone acyclicity

      [qorder]'s fourth conjunct places every [gdep2] predecessor at a
      STRICTLY EARLIER position, so the position is a strictly
      increasing measure along [tc gdep2] — which is both the cone's
      acyclicity and the well-foundedness the contracted-cycle argument
      descends on. *)

  Definition Idx (e : gev) : nat := lidx cl e.

  Lemma Idx_lookup e : e ∈ cl → cl !! Idx e = Some e.
  Proof. apply lidx_lookup. Qed.

  Lemma Idx_lt e : e ∈ cl → (Idx e < length cl)%nat.
  Proof. apply lidx_lt. Qed.

  Lemma Idx_mono x y :
    x ∈ cl → y ∈ cl → tc (gdep2 TS) x y → (Idx x < Idx y)%nat.
  Proof.
    intros Hx Hy Htc.
    destruct (qorder_tc_index TS ps Hnag cl x y (Idx y) Hqcl
                (Idx_lookup y Hy) Htc)
      as (i & Hi & Hlk).
    by rewrite /Idx (lidx_inj cl x i cl_nodup Hlk).
  Qed.

  Lemma cone_acyc e : e ∈ cl → ¬ tc (gdep2 TS) e e.
  Proof. intros He Htc. have := Idx_mono e e He He Htc. lia. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** §4.2  The contracted relation [Rblk] and its acyclicity *)

  Definition Rblk (B C : nat * nat) : Prop :=
    B ≠ C ∧ ∃ x y, x ∈ cl ∧ y ∈ cl ∧ bid x = B ∧ bid y = C ∧ gdep2 TS x y.

  Global Instance Rblk_dec : RelDecision Rblk.
  Proof.
    intros B C. rewrite /Rblk. apply and_dec; [apply _|].
    destruct (decide (Exists
       (λ x, Exists (λ y, bid x = B ∧ bid y = C ∧ gdep2 TS x y) cl) cl))
      as [Hex|Hex].
    - left. apply list_relations.Exists_exists in Hex as (x & Hx & Hy).
      apply list_relations.Exists_exists in Hy as (y & Hy & Hb).
      exists x, y. by destruct Hb as (? & ? & ?).
    - right. intros (x & y & Hx & Hy & H1 & H2 & H3).
      apply Hex, list_relations.Exists_exists. exists x. split; [done|].
      apply list_relations.Exists_exists. exists y. by split.
  Defined.

  (** [oke y] — "no cross source of [y]'s block sits strictly BEFORE
      [y]".  A cross TARGET always satisfies it, and it is the property
      the chain lemma propagates. *)
  Definition oke (y : gev) : Prop :=
    Forall (λ w, bid w = bid y → xsrc w → (y.2 ≤ w.2)%nat) cl.

  Global Instance oke_dec y : Decision (oke y).
  Proof. rewrite /oke. apply _. Defined.

  Lemma oke_use y w : oke y → w ∈ cl → bid w = bid y → xsrc w → (y.2 ≤ w.2)%nat.
  Proof.
    rewrite /oke list_relations.Forall_forall. intros Hall Hw. by apply Hall.
  Qed.

  Lemma not_oke y :
    ¬ oke y → ∃ w, w ∈ cl ∧ bid w = bid y ∧ xsrc w ∧ (w.2 < y.2)%nat.
  Proof.
    rewrite /oke. intros Hno.
    apply list_relations.not_Forall_Exists in Hno; [|apply _].
    apply list_relations.Exists_exists in Hno as (w & Hw & Hnq).
    destruct (not_impl2 (bid w = bid y) (xsrc w) ((y.2 ≤ w.2)%nat) Hnq)
      as (H1 & H2 & H3).
    exists w. split_and!; [done|done|done|lia].
  Qed.

  (** A block's UNIQUE cross source is [oke]. *)
  Lemma xsrc_oke w : w ∈ cl → xsrc w → oke w.
  Proof.
    intros Hw Hx. rewrite /oke list_relations.Forall_forall.
    intros u Hu Hbu Hxu.
    have -> : u = w
      by eapply (xsrc_unique u w Hxu Hx Hbu); apply cl_wf.
    lia.
  Qed.

  (** THE ONE-EDGE STEP: from an [oke] event of [B], a contracted edge
      [B → C] is realized by a [tc gdep2] path to an [oke] event of [C].
      The two arms are exactly the two shapes an edge can have — a CROSS
      edge (whose source is [B]'s unique cross source, reachable from
      any [oke] event of [B] by [gpo], and whose target is a memory
      event, hence [oke]) and a SAME-AGENT [gpo] edge (whose source AND
      target are both freely retargetable inside their blocks). *)
  Lemma oneedge B C :
    Rblk B C →
    ∀ z, z ∈ cl → bid z = B → oke z →
    ∃ y, y ∈ cl ∧ bid y = C ∧ oke y ∧ tc (gdep2 TS) z y.
  Proof.
    intros (Hne & x & y' & Hxcl & Hycl & Hbx & Hby & Hd) z Hzcl Hbz Hokez.
    have Hzwf := cl_wf z Hzcl.
    have Hxwf := cl_wf x Hxcl. have Hywf := cl_wf y' Hycl.
    have Hzag : z.1 = x.1 by (move: Hbz; rewrite -Hbx /bid; intros [= ? ?]).
    have Hzno : bno z = bno x by (move: Hbz; rewrite -Hbx /bid; intros [= ? ?]).
    destruct (decide (x.1 = y'.1)) as [Hsa|Hcross].
    - (* ---- SAME-AGENT [gpo] edge ---- *)
      have Hbno : (bno x < bno y')%nat.
      { have Hlt := gdep2_sa_lt x y' Hd Hsa.
        have Hle : (bno x ≤ bno y')%nat by apply bno_le_of_index; [done|lia].
        destruct (decide (bno x = bno y')) as [Heq|Hnn]; [|lia].
        exfalso. apply Hne. rewrite -Hbx -Hby /bid Hsa Heq //. }
      have Hgpo : ∀ u, u ∈ cl → bid u = C → gpo TS z u.
      { intros u Hu Hbu.
        have Huag : u.1 = y'.1 by (move: Hbu; rewrite -Hby /bid; intros [= ? ?]).
        have Huno : bno u = bno y'
          by (move: Hbu; rewrite -Hby /bid; intros [= ? ?]).
        split_and!; [rewrite Hzag Hsa Huag //| |done|by apply cl_wf].
        apply bno_lt_index; [lia|rewrite Hzag Hsa Huag //]. }
      destruct (decide (oke y')) as [Hok|Hnok].
      + exists y'. split_and!; [done|done|done|].
        by apply tc_once, gpo_gdep2, Hgpo.
      + destruct (not_oke y' Hnok) as (w & Hw & Hbw & Hxw & _).
        exists w. split_and!; [done|by rewrite Hbw|by apply xsrc_oke|].
        apply tc_once, gpo_gdep2, Hgpo; [done|by rewrite Hbw].
    - (* ---- CROSS edge ---- *)
      have Hxs : xsrc x by exists y'.
      have Hzx : rtc (gdep2 TS) z x.
      { have Hle : (z.2 ≤ x.2)%nat by eapply oke_use; [exact Hokez|done|by rewrite Hbz|done].
        destruct (decide (z.2 = x.2)) as [Heq|Hnn].
        - have -> : z = x by (destruct z as [a1 k1], x as [a2 k2];
                              simpl in Hzag, Heq; by subst).
          apply rtc_refl.
        - apply rtc_once, gpo_gdep2. split_and!; [done|lia|done|done]. }
      have Hokey : oke y'.
      { destruct (decide (oke y')) as [?|Hnok]; [done|exfalso].
        destruct (not_oke y' Hnok) as (w & Hw & Hbw & Hxw & Hlt).
        have Hmemy : is_mem y' by eapply cross_tgt_mem.
        have := xtgt_le_xsrc y' w Hmemy Hxw (eq_sym Hbw) Hywf. lia. }
      exists y'. split_and!; [done|done|done|].
      by eapply tc_rtc_l; [exact Hzx|apply tc_once].
  Qed.

  (** …iterated along a contracted PATH. *)
  Lemma chain2 B C :
    tc Rblk B C →
    ∀ z, z ∈ cl → bid z = B → oke z →
    ∃ y, y ∈ cl ∧ bid y = C ∧ oke y ∧ tc (gdep2 TS) z y.
  Proof.
    induction 1 as [B C HR|B B' C HR Htc IH]; intros z Hz Hbz Hokez.
    - by eapply oneedge.
    - destruct (oneedge B B' HR z Hz Hbz Hokez)
        as (y' & Hy' & Hby' & Hoky' & Htc1).
      destruct (IH y' Hy' Hby' Hoky') as (y & Hy & Hby & Hoky & Htc2).
      exists y. split_and!; [done|done|done|by eapply tc_transitive].
  Qed.

  (** DELIVERABLE 3: THE CONTRACTED GRAPH IS ACYCLIC ON THE CONE.  A
      contracted cycle would give, from ANY [oke] event of the block, a
      [tc gdep2] path back to an [oke] event of the SAME block — and
      [Idx] strictly increases along such a path, on a finite carrier. *)
  Theorem Rblk_acyc B : ¬ tc Rblk B B.
  Proof.
    intros Htc.
    destruct (tc_first Rblk B B Htc)
      as (C & (_ & x0 & y0 & Hx0 & _ & Hbx0 & _)).
    have Hstart : ∃ z, z ∈ cl ∧ bid z = B ∧ oke z.
    { destruct (decide (oke x0)) as [Hok|Hnok]; [by exists x0|].
      destruct (not_oke x0 Hnok) as (w & Hw & Hbw & Hxw & _).
      exists w. split_and!; [done|by rewrite Hbw|by apply xsrc_oke]. }
    have Hdesc : ∀ n z, z ∈ cl → bid z = B → oke z →
                   (length cl - Idx z ≤ n)%nat → False.
    { intros n. induction n as [|n IH]; intros z Hz Hbz Hokez Hlen.
      - have := Idx_lt z Hz. lia.
      - destruct (chain2 B B Htc z Hz Hbz Hokez)
          as (y & Hy & Hby & Hoky & Htcy).
        have Hlt := Idx_mono z y Hz Hy Htcy.
        eapply (IH y Hy Hby Hoky). have := Idx_lt y Hy. lia. }
    destruct Hstart as (z & Hz & Hbz & Hokez).
    by eapply (Hdesc (length cl - Idx z)%nat z).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** §4.3  The reader's block is a SINK

      Nothing leaves [b2]'s block: a cross edge out of it would put the
      memory event [b2] strictly after a cross source of its own block
      (excluded by [Hcsl]), and a same-agent edge out of it would put
      [b2] program-order before an event of the cone, which is already
      an ancestor of [b2] — a cycle. *)
  Lemma b2blk_no_out C : ¬ Rblk (bid b2) C.
  Proof.
    intros (Hne & x & y & Hx & Hy & Hbx & Hby & Hd).
    have Hxwf := cl_wf x Hx. have Hywf := cl_wf y Hy.
    have Hagx : x.1 = b2.1 by (move: Hbx; rewrite /bid; intros [= ? ?]).
    have Hnox : bno x = bno b2 by (move: Hbx; rewrite /bid; intros [= ? ?]).
    have Hyne : y ≠ b2 by (intros ->; apply Hne; by rewrite -Hbx -Hby).
    have Hyord : y ∈ ord0
      by (apply elem_of_cl in Hy as [?|Heq]; [done|by destruct (Hyne Heq)]).
    have Htcy : tc (gdep2 TS) y b2 by apply ord0_tc.
    destruct (decide (b2.2 = x.2)) as [Heq|Hne2].
    - have Hxb2 : x = b2
        by (destruct x as [a1 k1], b2 as [a2 k2]; simpl in Hagx, Heq; by subst).
      apply Hrr. eapply tc_l; [rewrite -Hxb2; exact Hd|exact Htcy].
    - destruct (decide (b2.2 < x.2)%nat) as [Hlt|Hgt].
      + have Hxord : x ∈ ord0
          by (apply elem_of_cl in Hx as [?|Heq2]; [done|
              exfalso; apply Hne2; by rewrite Heq2]).
        apply Hrr. eapply tc_l; [|by apply ord0_tc].
        apply gpo_gdep2. split_and!; [by rewrite Hagx|lia|done|done].
      + have Hxlt : (x.2 < b2.2)%nat by lia.
        destruct (decide (x.1 = y.1)) as [Hsa|Hcross].
        * have Hbno : (bno x < bno y)%nat.
          { have Hlt2 := gdep2_sa_lt x y Hd Hsa.
            have Hle : (bno x ≤ bno y)%nat by apply bno_le_of_index; [done|lia].
            destruct (decide (bno x = bno y)) as [Heq2|Hnn]; [|lia].
            exfalso. apply Hne. rewrite -Hbx -Hby /bid Hsa Heq2 //. }
          apply Hrr. eapply tc_l; [|exact Htcy].
          apply gpo_gdep2. split_and!.
          -- rewrite -Hagx Hsa //.
          -- apply bno_lt_index; [lia|rewrite -Hagx Hsa //].
          -- done.
          -- done.
        * exfalso.
          eapply (cross_src_last x y b2 Hd Hcross);
            [by rewrite Hagx|lia|by rewrite Hbx|done|done].
  Qed.

  (** The relation actually sorted: [Rblk] plus an edge from every other
      block INTO the reader's, which forces the reader's block last. *)
  Definition Rblk' (B C : nat * nat) : Prop :=
    Rblk B C ∨ (C = bid b2 ∧ B ≠ bid b2).

  Global Instance Rblk'_dec : RelDecision Rblk'.
  Proof. intros B C. rewrite /Rblk'. apply _. Defined.

  Lemma tc_Rblk_from_b2 C : ¬ tc Rblk (bid b2) C.
  Proof.
    intros Htc. destruct (tc_first Rblk (bid b2) C Htc) as (Dblk & HR).
    by eapply b2blk_no_out.
  Qed.

  Lemma tc_Rblk'_Rblk B C : tc Rblk' B C → C ≠ bid b2 → tc Rblk B C.
  Proof.
    induction 1 as [B C HR|B B' C HR Htc IH]; intros Hne.
    - destruct HR as [HR|(Heq & _)]; [by apply tc_once|by destruct (Hne Heq)].
    - have Htc' := IH Hne.
      have HB' : B' ≠ bid b2
        by (intros Heq; rewrite Heq in Htc'; by eapply tc_Rblk_from_b2).
      destruct HR as [HR|(Heq & _)]; [by eapply tc_l|by destruct (HB' Heq)].
  Qed.

  Theorem Rblk'_acyc B : ¬ tc Rblk' B B.
  Proof.
    intros Htc. destruct (decide (B = bid b2)) as [->|Hne].
    - destruct (tc_first Rblk' (bid b2) (bid b2) Htc) as (Dblk & [HR|(_ & Hc)]);
        [by eapply b2blk_no_out|done].
    - by eapply Rblk_acyc, tc_Rblk'_Rblk.
  Qed.

  (** The cone's block identifiers. *)
  Definition bids : list (nat * nat) := remove_dups (bid <$> cl).

  Lemma elem_of_bids B : B ∈ bids ↔ ∃ e, e ∈ cl ∧ bid e = B.
  Proof.
    rewrite /bids elem_of_remove_dups elem_of_list_fmap.
    split; intros (e & ? & ?); by exists e.
  Qed.

  Lemma bids_nodup : NoDup bids.
  Proof. apply NoDup_remove_dups. Qed.


  (* ================================================================ *)
  (** * §5  THE BLOCK-CONTIGUOUS ENUMERATION

      A topological order [bord] of the cone's block identifiers under
      [Rblk'] (which [WeakRobustLin.topo_sort] supplies, by
      [Rblk'_acyc]) is turned into a LEXICOGRAPHIC key on events; a
      second [topo_sort] at the event level over that key is the
      block-contiguous enumeration. *)

  Context (bord : list (nat * nat)).
  Context (Hbordnd : NoDup bord).
  Context (Hbordmem : ∀ B, B ∈ bord ↔ B ∈ bids).
  Context (Hbordlt : ∀ i j B C, bord !! i = Some B → bord !! j = Some C →
                       Rblk' B C → (i < j)%nat).

  Definition bpos (B : nat * nat) : nat := lidx bord B.

  Lemma bid_in_bord e : e ∈ cl → bid e ∈ bord.
  Proof. intros He. apply Hbordmem, elem_of_bids. by exists e. Qed.

  Lemma bpos_lookup e : e ∈ cl → bord !! bpos (bid e) = Some (bid e).
  Proof. intros He. rewrite /bpos. by apply lidx_lookup, bid_in_bord. Qed.

  Lemma bpos_inj x y :
    x ∈ cl → y ∈ cl → bpos (bid x) = bpos (bid y) → bid x = bid y.
  Proof.
    intros Hx Hy Heq.
    eapply lidx_eq_elem; [by apply bid_in_bord|by apply bid_in_bord|exact Heq].
  Qed.

  (** THE KEY: block position, then trace index. *)
  Definition klt (x y : gev) : Prop :=
    (bpos (bid x) < bpos (bid y))%nat ∨
    (bpos (bid x) = bpos (bid y) ∧ (x.2 < y.2)%nat).

  Global Instance klt_dec x y : Decision (klt x y).
  Proof. rewrite /klt. apply _. Defined.

  Lemma klt_trans x y z : klt x y → klt y z → klt x z.
  Proof. rewrite /klt. intros [?|[??]] [?|[??]]; [left|left|left|right]; lia. Qed.

  Lemma klt_irrefl x : ¬ klt x x.
  Proof. rewrite /klt. intros [?|[??]]; lia. Qed.

  Lemma klt_total x y :
    klt x y ∨ klt y x ∨ (bpos (bid x) = bpos (bid y) ∧ x.2 = y.2).
  Proof.
    destruct (decide (bpos (bid x) < bpos (bid y))%nat) as [H1|H1];
      [by left; left|].
    destruct (decide (bpos (bid y) < bpos (bid x))%nat) as [H2|H2];
      [by right; left; left|].
    destruct (decide (x.2 < y.2)%nat) as [H3|H3];
      [left; right; split; [lia|done]|].
    destruct (decide (y.2 < x.2)%nat) as [H4|H4];
      [right; left; right; split; [lia|done]|].
    right; right. split; lia.
  Qed.

  (** DELIVERABLE 3, CONSUMED: every [gdep2] edge of the cone strictly
      increases the key.  Same block ⟹ program order ([gdep2_sa_lt]);
      different blocks ⟹ a contracted edge, hence [bord]-sorted. *)
  Lemma gdep2_klt x y : x ∈ cl → y ∈ cl → gdep2 TS x y → klt x y.
  Proof.
    intros Hx Hy Hd.
    destruct (decide (bid x = bid y)) as [Heq|Hne].
    - right. split; [by rewrite Heq|].
      apply gdep2_sa_lt; [done|]. move: Heq. rewrite /bid. by intros [= ? ?].
    - left. rewrite /bpos.
      eapply (Hbordlt (lidx bord (bid x)) (lidx bord (bid y)) (bid x) (bid y));
        [by apply lidx_lookup, bid_in_bord|by apply lidx_lookup, bid_in_bord|].
      left. split; [done|]. by exists x, y.
  Qed.

  (** …and the reader's block has the LARGEST key. *)
  Lemma bpos_b2_max e : e ∈ cl → bid e ≠ bid b2 → (bpos (bid e) < bpos (bid b2))%nat.
  Proof.
    intros He Hne. rewrite /bpos.
    eapply (Hbordlt (lidx bord (bid e)) (lidx bord (bid b2)) (bid e) (bid b2));
      [by apply lidx_lookup, bid_in_bord
      |by apply lidx_lookup, bid_in_bord, b2_cl|].
    right. by split.
  Qed.

  (** A cone event of the reader's own agent is program-order BEFORE the
      reader (otherwise the reader would precede one of its own
      ancestors). *)
  Lemma cl_b2_lt e : e ∈ ord0 → e.1 = b2.1 → (e.2 < b2.2)%nat.
  Proof.
    intros He Hag.
    have Hwfe : gev_wf TS e by apply ord0_wf.
    destruct (decide (e.2 < b2.2)%nat) as [?|Hge]; [done|exfalso].
    destruct (decide (e.2 = b2.2)) as [Heq|Hne].
    - have Hb : e = b2
        by (destruct e as [a1 k1], b2 as [a2 k2]; simpl in Hag, Heq; by subst).
      apply Hrr. have H0 := ord0_tc e He. rewrite Hb in H0. exact H0.
    - apply Hrr. eapply tc_l; [|by apply ord0_tc].
      apply gpo_gdep2. split_and!; [by rewrite Hag|lia|done|done].
  Qed.

  Lemma klt_b2 e : e ∈ ord0 → klt e b2.
  Proof.
    intros He.
    destruct (decide (bid e = bid b2)) as [Heq|Hne].
    - right. split; [by rewrite Heq|].
      apply cl_b2_lt; [done|]. move: Heq. rewrite /bid. by intros [= ? ?].
    - left. by apply bpos_b2_max; [apply ord0_cl|].
  Qed.

  (** THE EVENT-LEVEL RELATION SORTED SECOND: the key, restricted to the
      cone.  It is a strict order, hence acyclic outright. *)
  Definition Rev (x y : gev) : Prop := x ∈ ord0 ∧ y ∈ ord0 ∧ klt x y.

  Global Instance Rev_dec : RelDecision Rev.
  Proof. intros x y. rewrite /Rev. apply _. Defined.

  Lemma tc_Rev_klt x y : tc Rev x y → klt x y.
  Proof.
    induction 1 as [x y (_ & _ & Hk)|x y z (_ & _ & Hk) _ IH];
      [done|by eapply klt_trans].
  Qed.

  Lemma Rev_acyc x : ¬ tc Rev x x.
  Proof. intros Htc. by apply (klt_irrefl x), tc_Rev_klt. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** §5.1  The enumeration itself *)

  Context (done_b : list gev).
  Context (Hdnd : NoDup done_b).
  Context (Hdmem : ∀ e, e ∈ done_b ↔ e ∈ ord0).
  Context (Hdord : ∀ i j x y, done_b !! i = Some x → done_b !! j = Some y →
                     (x ∈ ord0 ∧ y ∈ ord0 ∧ klt x y) → (i < j)%nat).

  Definition done_full : list gev := done_b ++ [b2].

  Lemma done_b_ord0 e : e ∈ done_b → e ∈ ord0.
  Proof. apply Hdmem. Qed.

  Lemma done_b_cl e : e ∈ done_b → e ∈ cl.
  Proof. intros He. by apply ord0_cl, Hdmem. Qed.

  Lemma done_full_len : length done_full = S (length done_b).
  Proof. rewrite /done_full length_app /=. lia. Qed.

  Lemma done_full_last : done_full !! (length done_b) = Some b2.
  Proof.
    rewrite /done_full lookup_app_r; [lia|]. by rewrite Nat.sub_diag.
  Qed.

  Lemma done_full_lookup i x :
    done_full !! i = Some x →
    ((i < length done_b)%nat ∧ done_b !! i = Some x) ∨
    (i = length done_b ∧ x = b2).
  Proof.
    rewrite /done_full. intros Hi.
    apply lookup_app_Some in Hi as [Hi|(Hge & Hi)].
    - left. split; [by eapply lookup_lt_Some|done].
    - right. destruct (i - length done_b)%nat as [|d] eqn:Hd; simpl in Hi.
      + split; [lia|by injection Hi].
      + by rewrite lookup_nil in Hi.
  Qed.

  Lemma done_full_mem e : e ∈ done_full ↔ e ∈ cl.
  Proof.
    rewrite /done_full /cl !elem_of_app. split.
    - intros [He|He]; [left; by apply Hdmem|by right].
    - intros [He|He]; [left; by apply Hdmem|by right].
  Qed.

  Lemma done_full_cl e : e ∈ done_full → e ∈ cl.
  Proof. apply done_full_mem. Qed.

  Lemma done_full_nodup : NoDup done_full.
  Proof.
    rewrite /done_full. apply list_relations.NoDup_app. split_and!.
    - done.
    - intros x Hx Hx2. apply elem_of_list_singleton in Hx2. subst.
      by apply b2_nin, Hdmem.
    - apply NoDup_singleton.
  Qed.

  (** THE POSITIONAL ORDER: the enumeration realizes the key. *)
  Lemma done_full_klt i j x y :
    done_full !! i = Some x → done_full !! j = Some y → klt x y → (i < j)%nat.
  Proof.
    intros Hi Hj Hk.
    apply done_full_lookup in Hi as [(Hi1 & Hi2)|(Hi1 & Hi2)];
      apply done_full_lookup in Hj as [(Hj1 & Hj2)|(Hj1 & Hj2)].
    - eapply Hdord; [exact Hi2|exact Hj2|].
      split_and!; [by eapply done_b_ord0, elem_of_list_lookup_2
                  |by eapply done_b_ord0, elem_of_list_lookup_2|done].
    - lia.
    - exfalso. subst x.
      have Hy : y ∈ ord0
        by eapply done_b_ord0, elem_of_list_lookup_2; exact Hj2.
      have := klt_b2 y Hy. intros Hk2.
      by apply (klt_irrefl b2), (klt_trans b2 y b2).
    - exfalso. subst x y. by apply (klt_irrefl b2).
  Qed.

  Lemma done_full_nklt i j x y :
    done_full !! i = Some x → done_full !! j = Some y → (i < j)%nat → ¬ klt y x.
  Proof.
    intros Hi Hj Hlt Hk. have := done_full_klt j i y x Hj Hi Hk. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** §5.2  What the enumeration exports *)

  (** (a) THE [qorder] PREDECESSOR PROPERTY. *)
  Theorem done_full_pred n y :
    done_full !! n = Some y →
    ∀ x, gdep2 TS x y → gev_wf TS x →
      ∃ i, (i < n)%nat ∧ done_full !! i = Some x.
  Proof.
    intros Hn x Hd Hwx.
    have Hycl : y ∈ cl by apply done_full_cl, (elem_of_list_lookup_2 _ n).
    have Hxord : x ∈ ord0 by eapply cl_dc.
    have Hxdone : x ∈ done_b by apply Hdmem.
    apply elem_of_list_lookup in Hxdone as (i & Hi).
    have Hifull : done_full !! i = Some x
      by rewrite /done_full lookup_app_l; [by eapply lookup_lt_Some|exact Hi].
    exists i. split; [|done].
    eapply done_full_klt; [exact Hifull|exact Hn|].
    apply gdep2_klt; [by apply ord0_cl|done|done].
  Qed.

  (** (b) BLOCK CONTIGUITY: between two events of one block there is
      nothing else. *)
  Theorem done_full_contig i j k x y z :
    (i < j)%nat → (j < k)%nat →
    done_full !! i = Some x → done_full !! j = Some y → done_full !! k = Some z →
    bid x = bid z → bid y = bid x.
  Proof.
    intros Hij Hjk Hi Hj Hk Hxz.
    have Hxcl : x ∈ cl by apply done_full_cl, (elem_of_list_lookup_2 _ i).
    have Hycl : y ∈ cl by apply done_full_cl, (elem_of_list_lookup_2 _ j).
    have H1 : ¬ klt y x by eapply done_full_nklt; [exact Hi|exact Hj|lia].
    have H2 : ¬ klt z y by eapply done_full_nklt; [exact Hj|exact Hk|lia].
    have Hle1 : (bpos (bid x) ≤ bpos (bid y))%nat.
    { destruct (klt_total x y) as [Ha|[Ha|(Ha & _)]].
      - destruct Ha as [?|(? & ?)]; lia.
      - by destruct (H1 Ha).
      - lia. }
    have Hle2 : (bpos (bid y) ≤ bpos (bid z))%nat.
    { destruct (klt_total y z) as [Hm|[Hm|(Hm & _)]].
      - destruct Hm as [?|(? & ?)]; lia.
      - by destruct (H2 Hm).
      - lia. }
    rewrite Hxz in Hle1.
    have Heq : bpos (bid y) = bpos (bid x) by rewrite Hxz; lia.
    by apply bpos_inj.
  Qed.

  (** (c) IN-BLOCK ORDER IS TRACE ORDER. *)
  Theorem done_full_inblk i j x y :
    (i < j)%nat →
    done_full !! i = Some x → done_full !! j = Some y →
    bid x = bid y → (x.2 < y.2)%nat.
  Proof.
    intros Hij Hi Hj Hbid.
    have H1 : ¬ klt y x by eapply done_full_nklt; [exact Hi|exact Hj|lia].
    have Hne : x ≠ y.
    { intros ->. have := list_relations.NoDup_lookup _ i j y done_full_nodup Hi Hj.
      lia. }
    have Hag : x.1 = y.1 by move: Hbid; rewrite /bid; intros [= ? ?].
    destruct (decide (x.2 < y.2)%nat) as [?|Hge]; [done|exfalso].
    destruct (decide (x.2 = y.2)) as [Heq|Hne2].
    - apply Hne. destruct x as [a1 k1], y as [a2 k2]. simpl in Hag, Heq. by subst.
    - apply H1. right. split; [by rewrite Hbid|lia].
  Qed.

  (** (d) THE READER'S BLOCK IS LAST. *)
  Theorem done_full_reader_last i j x y :
    done_full !! i = Some x → done_full !! j = Some y →
    bid y = bid b2 → bid x ≠ bid b2 → (i < j)%nat.
  Proof.
    intros Hi Hj Hby Hbx.
    have Hxcl : x ∈ cl by apply done_full_cl, (elem_of_list_lookup_2 _ i).
    eapply done_full_klt; [exact Hi|exact Hj|].
    left. rewrite Hby. by apply bpos_b2_max.
  Qed.


  (* ================================================================ *)
  (** * §6  DRIVING THE INVARIANT, AND THE RUN'S SEGMENT STRUCTURE

      [done_full] is a valid [qorder] enumeration ([done_full_pred]), so
      [WeakRobustSim.Qinv_step] applies along it; [Qcfg_step] gives, in
      addition, the individual [wp_pf_step] of each processed event's
      agent.  The export is the resulting CONFIGURATION CHAIN: one
      configuration per prefix, consecutive ones related by a SOLO step
      ([WeakRobustBlocks.cstep]) of the processed event's agent, each
      pinned by [qcfg] at its prefix.  Combined with the block
      contiguity of [done_full] (§5.2) this is exactly "a concatenation
      of contiguous solo block runs, whose endpoints are the trace's
      agent records at block boundaries". *)

  Lemma Qinv_prefix n :
    (n ≤ length done_full)%nat → Qinv pstep pcls TS (PDevs d0 []) img d0 ps (take n done_full).
  Proof.
    induction n as [|n IH]; intros Hn.
    - rewrite take_0.
      by apply (Qinv_nil pstep pcls TS (PDevs d0 []) img d0 ps Hwf Hnag Hps0 eq_refl).
    - have [e He] : is_Some (done_full !! n) by apply lookup_lt_is_Some_2; lia.
      rewrite (take_S_r done_full n e He).
      have Hwfe : gev_wf TS e
        by (apply cl_wf, done_full_cl; by eapply elem_of_list_lookup_2).
      eapply (Qinv_step pstep pcls pdev TS (PDevs d0 []) img d0 ps Hwf Hwsi Hco Hwfl
                Hlf Hobl Hcls Hclsobl Himg Hnag Hdata (ptraces_wit_nil TS d0 Hdf)
                (take n done_full) e).
      + apply IH. lia.
      + done.
      + intros Hin. apply elem_of_take in Hin as (i & Hi & Hilt).
        have Hii : i = n
          by (eapply list_relations.NoDup_lookup;
              [apply done_full_nodup|exact Hi|exact He]).
        lia.
      + intros e' Hd%(gdep3_nil_gdep2 TS d0) Hw'.
        destruct (done_full_pred n e He e' Hd Hw') as (i & Hi & Hlk).
        apply elem_of_take. by exists i.
  Qed.

  Lemma qorder_prefix n :
    (n ≤ length done_full)%nat → qorder TS (take n done_full).
  Proof.
    intros Hn. eapply (Qinv_order pstep pcls TS (PDevs d0 []) img d0 ps). by apply Qinv_prefix.
  Qed.

  Lemma qorder_done_full : qorder TS done_full.
  Proof.
    have := qorder_prefix (length done_full) (Nat.le_refl _).
    by rewrite take_ge; [lia|].
  Qed.

  Lemma qorder_done_b : qorder TS done_b.
  Proof.
    have Hle : (length done_b ≤ length done_full)%nat by rewrite done_full_len; lia.
    have := qorder_prefix (length done_b) Hle.
    by rewrite /done_full take_app_length.
  Qed.

  Lemma qcfg_nil : qcfg pstep pcls TS (PDevs d0 []) img d0 ps [] (wp_init img d0 ps).
  Proof.
    split_and!.
    - apply rtc_refl.
    - done.
    - done.
    - by rewrite /wp_init /= length_map.
    - intros j T HT.
      have Hatr : atrace_wf pstep (pt_img TS) (pt_log TS) j T by apply Hwf.
      destruct (atrace_first_is_Some pstep (pt_img TS) (pt_log TS) j T Hatr)
        as [ag0 Hag0].
      exists ag0. rewrite nproc_nil. split; [done|].
      rewrite /wp_init /= list_lookup_fmap (Hps0 j T ag0 HT Hag0) //.
    - by apply (qfab_init TS (PDevs d0 []) d0 ps Hnag eq_refl).
  Qed.

  Lemma cstep_of_step i l c c' :
    wp_pf_step pstep pcls i l c c' → cstep pstep pcls i c c'.
  Proof.
    intros Hs. split; [by exists l|].
    by destruct (wp_pf_step_shape pstep pcls i l c c' Hs) as (_ & _ & Hms).
  Qed.

  (** THE CHAIN. *)
  Lemma pf_chain_build n :
    (n ≤ length done_full)%nat →
    ∃ cfs, length cfs = S n ∧
      cfs !! 0%nat = Some (wp_init img d0 ps) ∧
      (∀ i e c c', done_full !! i = Some e →
         cfs !! i = Some c → cfs !! S i = Some c' → cstep pstep pcls e.1 c c') ∧
      (∀ i c, cfs !! i = Some c → qcfg pstep pcls TS (PDevs d0 []) img d0 ps (take i done_full) c).
  Proof.
    induction n as [|n IH]; intros Hn.
    - exists [wp_init img d0 ps]. split_and!.
      + done.
      + done.
      + intros i e c c' He Hc Hc'.
        have Hlt : (S i < length [wp_init (P:=P) (D:=D) img d0 ps])%nat
          by eapply lookup_lt_Some.
        simpl in Hlt. lia.
      + intros i c Hc.
        have Hlt : (i < length [wp_init (P:=P) (D:=D) img d0 ps])%nat
          by eapply lookup_lt_Some.
        simpl in Hlt. have Hi0 : i = 0%nat by lia. subst i.
        simpl in Hc. injection Hc as <-. rewrite take_0. apply qcfg_nil.
    - have Hn' : (n ≤ length done_full)%nat by lia.
      destruct (IH Hn') as (cfs & Hlen & H0 & Hstep & Hq).
      have [cn Hcn] : is_Some (cfs !! n) by apply lookup_lt_is_Some_2; lia.
      have Hqn : qcfg pstep pcls TS (PDevs d0 []) img d0 ps (take n done_full) cn by apply Hq.
      have [e He] : is_Some (done_full !! n) by apply lookup_lt_is_Some_2; lia.
      have Hwfe : gev_wf TS e
        by (apply cl_wf, done_full_cl; by eapply elem_of_list_lookup_2).
      have Hqo : qorder TS (take n done_full) by apply qorder_prefix; lia.
      have Hnin : e ∉ take n done_full.
      { intros Hin. apply elem_of_take in Hin as (i & Hi & Hilt).
        have Hii : i = n
          by (eapply list_relations.NoDup_lookup;
              [apply done_full_nodup|exact Hi|exact He]).
        lia. }
      have Hpre : ∀ e', gdep2 TS e' e → gev_wf TS e' → e' ∈ take n done_full.
      { intros e' Hd Hw'.
        destruct (done_full_pred n e He e' Hd Hw') as (i & Hi & Hlk).
        apply elem_of_take. by exists i. }
      destruct (Qcfg_step pstep pcls pdev TS img d0 ps Hwf Hwsi Hco Hwfl Hlf
                  Hobl Hcls Hclsobl Himg Hnag Hdata Hdf (take n done_full) e cn
                  Hqo Hqn Hwfe Hnin Hpre)
        as (lb & cf' & Hstp & Hqcf).
      have Hl : ∀ i, (i < length cfs)%nat → (cfs ++ [cf']) !! i = cfs !! i.
      { intros i Hi. by apply lookup_app_l. }
      have Hr : (cfs ++ [cf']) !! (length cfs) = Some cf'.
      { rewrite lookup_app_r; [lia|]. by rewrite Nat.sub_diag. }
      exists (cfs ++ [cf']). split_and!.
      + rewrite length_app /=. lia.
      + rewrite Hl; [lia|done].
      + intros i e0 c c' He0 Hc Hc'.
        destruct (decide (S i < length cfs)%nat) as [Hlt|Hge].
        * rewrite (Hl i ltac:(lia)) in Hc. rewrite (Hl (S i) Hlt) in Hc'.
          by eapply Hstep.
        * have Hsi : S i = length cfs.
          { have := lookup_lt_Some _ _ _ Hc'. rewrite length_app /=. lia. }
          have Hin : i = n by lia.
          subst i. rewrite (Hl n ltac:(lia)) in Hc.
          rewrite Hcn in Hc. injection Hc as <-.
          rewrite -Hsi in Hr. rewrite Hr in Hc'. injection Hc' as <-.
          rewrite He in He0. injection He0 as <-.
          by eapply cstep_of_step.
      + intros i c Hc.
        destruct (decide (i < length cfs)%nat) as [Hlt|Hge].
        * rewrite (Hl i Hlt) in Hc. by apply Hq.
        * have Hi : i = length cfs.
          { have := lookup_lt_Some _ _ _ Hc. rewrite length_app /=. lia. }
          subst i. rewrite Hr in Hc. injection Hc as <-.
          have Hsn : length cfs = S n by lia.
          rewrite Hsn (take_S_r done_full n e He). exact Hqcf.
  Qed.


  (* ================================================================ *)
  (** * §7  THE VIOLATION AT THE BLOCK-CONTIGUOUS ORDER

      [WeakRobustMain.bad_edge_violates]' witness extraction, replayed
      verbatim at [done_full].  Nothing in it depends on WHICH
      topological order is used — only on [qorder] — which is exactly
      why the block-contiguous one serves. *)

  Theorem blocks_violates b1 :
    bad nh TS (PDevs d0 []) b1 b2 →
    ∃ cfs cf,
      (** the run, with its per-event segment structure *)
      length cfs = S (length done_full) ∧
      cfs !! 0%nat = Some (wp_init img d0 ps) ∧
      cfs !! (length done_full) = Some cf ∧
      (∀ i e c c', done_full !! i = Some e →
         cfs !! i = Some c → cfs !! S i = Some c' → cstep pstep pcls e.1 c c') ∧
      (∀ i c, cfs !! i = Some c → qcfg pstep pcls TS (PDevs d0 []) img d0 ps (take i done_full) c) ∧
      rtc (wp_pf_run pstep pcls) (wp_init img d0 ps) cf ∧
      (** the violation, in both the named and the hart-restricted form *)
      (∃ p m a, violates_at cf p m b1.1 b2.1 a) ∧
      violation_hart cls_of pub_of nh cf.
  Proof.
    intros Hbad.
    have Hbad' := Hbad.
    destruct Hbad'
      as (Hrf & Hne & Hh1 & Hh2 & (t & m & Hts1 & Hlogm & Hak) & Hnopub).
    have Hrf' := Hrf. destruct Hrf' as (t' & a & Hts1' & Hrd2).
    have Htt : t' = t by rewrite Hts1 in Hts1'; simplify_eq.
    subst t'.
    have Hb1wf : gev_wf TS b1 by eapply gev_ts_wf.
    have Htpos : (0 < t)%nat by eapply (gev_ts_pos pstep TS b1 t Hwf Hts1).
    (* ---- the run ---- *)
    destruct (pf_chain_build (length done_full) (Nat.le_refl _))
      as (cfs & Hlen & H0 & Hstepc & Hqc).
    have [cf Hcf] : is_Some (cfs !! (length done_full))
      by apply lookup_lt_is_Some_2; lia.
    have Hqcf : qcfg pstep pcls TS (PDevs d0 []) img d0 ps done_full cf.
    { have := Hqc (length done_full) cf Hcf. by rewrite take_ge; [lia|]. }
    have Hqcf' := Hqcf.
    destruct Hqcf' as (Hrun & Hcimg & Hclog & Hclen & Hcags & _).
    exists cfs, cf.
    (* ---- the bad message and its pf position ---- *)
    have Hq' : qorder TS done_full by apply qorder_done_full.
    have Hb2nin : b2 ∉ done_b by (intros Hin; by apply b2_nin, Hdmem).
    have Hpre2 : ∀ e', gdep2 TS e' b2 → gev_wf TS e' → e' ∈ done_b.
    { intros e' Hd Hw'. apply Hdmem. by apply b2_pre. }
    have Hb1ord : b1 ∈ ord0.
    { apply Hmem0. split; [done|]. apply tc_once, grf_gdep2. by exists t, a. }
    have Hb1in' : b1 ∈ done_full
      by (rewrite /done_full elem_of_app; left; by apply Hdmem).
    have Htfl : t ∈ fl TS done_full.
    { apply elem_of_fl. by exists b1. }
    destruct (pf_log_pi pstep pdev TS ps Hwf Hnag done_full t Hq' Htfl)
      as (Hp1 & Hp2 & Hp3).
    have Hmsgeq : msg_at TS t = m by apply msg_at_eq.
    destruct (gev_ts_msg pstep TS b1 t Hwf Hts1) as (base0 & data0 & kc & Hm0).
    have Hmeq : m = WMsg base0 data0 (Some b1.1) kc
      by rewrite Hlogm in Hm0; simplify_eq.
    (* ---- the reader's event and the byte it read ---- *)
    destruct (proj1 (gev_wf_bounds TS b2) Hb2wf) as (T2 & HT2 & Hklt).
    destruct (WeakRobustAcyc.gev_reads_ev TS b2 a t T2 HT2 Hrd2)
      as (ev2 & Hev2 & Hinrd).
    have Hatr2 : atrace_wf pstep (pt_img TS) (pt_log TS) b2.1 T2 by apply Hwf.
    destruct (asteps_wf_step pstep (pt_img TS) (pt_log TS) b2.1 (at_ags T2)
                (at_evs T2) b2.2 ev2 Hatr2 Hev2)
      as (ag2 & ag2' & st2 & f2 & Hag2 & Hag2' & Hps2 & Hok2 & Hagn2).
    have Hshape : ∃ (base : Z) tvs (jb : nat) (v : bv 8),
        a = base + Z.of_nat jb ∧ tvs !! jb = Some (t, v) ∧
        ((∃ aq lat asrc, ae_lb ev2 = LLoad aq lat base tvs asrc) ∨
         (∃ aq rl data asrc vsrc ts,
            ae_lb ev2 = LRmw aq rl base tvs data asrc vsrc ∧
            ae_ts ev2 = Some ts) ∨
         (* THE RMW SPLIT (S2): the exclusive read is a third reading shape *)
         (∃ aq asrc, ae_lb ev2 = LExLoad aq base tvs asrc)).
    { remember (ae_lb ev2) as l2 eqn:Hlb2.
      destruct l2 as [|aq lat base tvs asrc|rl base data asrc vsrc
                     |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc
                     |csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
        simpl in Hinrd;
        [by apply elem_of_nil in Hinrd| | by apply elem_of_nil in Hinrd
        | |by apply elem_of_nil in Hinrd|by apply elem_of_nil in Hinrd
        |by apply elem_of_nil in Hinrd|by apply elem_of_nil in Hinrd
        |by apply elem_of_nil in Hinrd
        (* THE RMW SPLIT (S2): the exclusive read is a THIRD reading
           shape; the conditional write reads nothing *)
        | |by apply elem_of_nil in Hinrd].
      - apply elem_of_tvs_reads in Hinrd as (jb & v & Htv & ->).
        exists base, tvs, jb, v.
        split_and!; [done|done|left; by exists aq, lat, asrc].
      - apply elem_of_tvs_reads in Hinrd as (jb & v & Htv & ->).
        destruct Hok2 as (ts2 & k2 & _ & _ & _ & _ & _ & _ & _ & Hts2).
        exists base, tvs, jb, v.
        split_and!;
          [done|done|right; left; by exists aq, rl, data, asrc, vsrc, ts2].
      - apply elem_of_tvs_reads in Hinrd as (jb & v & Htv & ->).
        exists xbase, xtvs, jb, v.
        split_and!; [done|done|right; right; by exists xaq, xasrc]. }
    destruct Hshape as (base & tvs & jb & v & Ha & Htv & Hlbsh).
    have Hlbv : log_byte (pt_img TS) (pt_log TS) t (base + Z.of_nat jb)
                = Some v.
    { eapply (astep_read_log_byte (pt_img TS) (pt_log TS) b2.1 ag2
                (ae_lb ev2) f2 (ae_ts ev2) base tvs jb t v Hok2); [|exact Htv].
      destruct Hlbsh
        as [(aq & lat & asrc & Hl)
           |[(aq & rl & data & asrc & vsrc & ts & Hl & _)
            |(aq & asrc & Hl)]];
        [left; by exists aq, lat, asrc
        |right; left; by exists aq, rl, data, asrc, vsrc
        |right; right; by exists aq, asrc]. }
    have Hbyte : is_Some (msg_byte m (base + Z.of_nat jb)).
    { rewrite (log_byte_pos (pt_img TS) (pt_log TS) t m _ Htpos Hlogm) in Hlbv.
      by exists v. }
    (* ---- the reader's coherence floor ---- *)
    have Hnproc2 : nproc done_full b2.1 = S b2.2.
    { rewrite /done_full (nproc_app_eq done_b b2).
      by rewrite (nproc_cur TS ps Hnag done_b b2 qorder_done_b Hb2wf Hb2nin
                    Hpre2). }
    destruct (Hcags b2.1 T2 HT2) as (agn2 & Hagn2' & Hlk2).
    rewrite Hnproc2 (take_S_r _ _ _ Hev2) aevs_post_app in Hlk2.
    have Hcoh : (pi TS done_full t ≤
                 coh (aev_post (pi TS done_full) ev2
                        (aevs_post (pi TS done_full)
                           (take b2.2 (at_evs T2)) ws_init))
                     (base + Z.of_nat jb))%nat.
    { by eapply aev_post_coh_read. }
    (* ---- the violating configuration ---- *)
    have HSp : S (pi TS done_full t - 1)%nat = pi TS done_full t by lia.
    have Hviol : violates_at cf (pi TS done_full t - 1)%nat m b1.1 b2.1
                   (base + Z.of_nat jb).
    { split_and!.
      - by rewrite Hclog Hp3 Hmsgeq.
      - by rewrite Hmeq.
      - by rewrite /cls_of Hak.
      - (* NOT PUBLISHED *)
        rewrite HSp.
        intros (p' & m' & Heq & Hlogp & Hpub).
        have Hp' : p' = (pi TS done_full t - 1)%nat by lia.
        subst p'. rewrite Hclog Hp3 Hmsgeq in Hlogp. injection Hlogp as <-.
        rewrite Hmeq /= in Hpub.
        destruct Hpub as (q & mq & Hle & Hq0 & Htidq & Hrelq).
        rewrite Hclog /pf_log list_lookup_fmap in Hq0.
        destruct (fl TS done_full !! q) as [t0|] eqn:Hfl0;
          simpl in Hq0; [|done].
        injection Hq0 as Hq0. subst mq.
        have Ht0in : t0 ∈ fl TS done_full
          by eapply elem_of_list_lookup_2, Hfl0.
        destruct (fl_msg pstep TS Hwf done_full t0 Hq' Ht0in)
          as (ep & Hepin & Hepts & Heplog & Heptid).
        have Hepag : ep.1 = b1.1
          by rewrite Heptid in Htidq; injection Htidq.
        have Hepwf : gev_wf TS ep by eapply gev_ts_wf.
        have Hpiq : pi TS done_full t0 = S q
          by eapply (pi_mem pstep pdev TS ps Hwf Hnag done_full q t0 Hq' Hfl0).
        have Hepge : (b1.2 ≤ ep.2)%nat.
        { destruct (decide (ep.2 < b1.2)%nat) as [Hlt|Hge]; [|lia]. exfalso.
          have Htcb1 : tc (gdep2 TS) ep b1
            by apply tc_once, gpo_gdep2; split_and!.
          have Hlt' := pi_lt_of_tc pstep pdev TS ps Hwf Hnag done_full
                         ep b1 t0 t Hq' Hb1in' Htcb1 Hepts Hts1.
          lia. }
        have Hepord : ep ∈ ord0.
        { rewrite /done_full elem_of_app in Hepin.
          destruct Hepin as [Hin|Hin]; [by apply Hdmem|].
          apply elem_of_list_singleton in Hin. exfalso.
          apply Hne. by rewrite -Hepag Hin. }
        apply Hnopub. exists ep. split_and!.
        + exact Hepag.
        + exact Hepge.
        + exists t0, (msg_at TS t0). split_and!;
            [exact Hepts|exact Heplog|exact Hrelq].
        + apply tc_gdep2_gdep3. by apply ord0_tc.
      - done.
      - exact Hbyte.
      - rewrite /obs_flr Hlk2 /=. lia. }
    split_and!; [lia|done|done|done|done|done| |].
    - by exists (pi TS done_full t - 1)%nat, m, (base + Z.of_nat jb).
    - destruct Hviol as (Hl & Ht & Hc & Hpb & Hn & Hb & Ho).
      exists (pi TS done_full t - 1)%nat, m, b1.1, b2.1, (base + Z.of_nat jb).
      split_and!; [done|done| |done|done|done| |done|done].
      + exists b1.1. by rewrite Hmeq.
      + by exists b2.1.
  Qed.

End coneblocks.



(* ================================================================== *)
(** * §8  THE PACKAGED THEOREM

    [WeakRobustMain.bad_edge_violates], re-derived over a
    BLOCK-CONTIGUOUS order and with the run's segment structure
    exported.  The two [topo_sort]s (blocks, then events) are performed
    here; everything else is §§3–7. *)

Section main.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pcls : P → wlabel → wstate → wm_class).
  Context (pdev : P → wlabel → P → bool).
  Context (TS : ptraces P D) (img : image) (d0 : D) (ps : list P).
  Context (Hwf : ptraces_wf pstep TS).
  Context (Hwsi : ptraces_ws_init TS).
  Context (Hco : ∀ a, WeakRobustSer.co_tc TS a).
  Context (Hwfl : WeakRobustSer.writes_fulfilled TS).
  Context (Hlf : lat_free_prog pstep).
  Context (Hobl : ts_oblivious pstep).
  (** THE CLASS HALVES OF G6a (see [WeakRobustSim]'s [Section sim]):
      [wp_pf_step] pins the class of every message it appends, so the
      replay needs the recorded log to be canonically classed and [pcls]
      to be timestamp-blind. *)
  Context (Hcls : cls_canonical pcls TS).
  Context (Hclsobl : pcls_obl pcls).
  Context (Himg : pt_img TS = img).
  Context (Hnag : length (pt_trs TS) = length ps).
  Context (Hdata : ∀ p m, pt_log TS !! p = Some m → wm_data m ≠ []).
  Context (Hdf : ∀ j T k ev, pt_trs TS !! j = Some T →
                   at_evs T !! k = Some ev → ae_dev ev = None).
  Context (Hps0 : ∀ j T ag0, pt_trs TS !! j = Some T →
                    at_ags T !! 0%nat = Some ag0 → ps !! j = Some (pa_st ag0)).
  Context (Hfo : WeakRobustAcyc.ptraces_fwd_own TS).
  Context (Hee : WeakRobustAcyc2.ee_ok TS).
  Context (nh : nat).
  Context (Hsplit : edges_split_cyc nh TS (PDevs d0 [])).
  Context (bnd : P → Prop).
  Context `{!∀ p, Decision (bnd p)}.
  Context (Hbnd0 : ∀ i T ag0, pt_trs TS !! i = Some T →
                     at_ags T !! 0%nat = Some ag0 → bnd (pa_st ag0)).
  Context (Hcsl : ∀ e1 e2, gdep2 TS e1 e2 → e1.1 ≠ e2.1 →
    ∀ T, pt_trs TS !! e1.1 = Some T →
    ∀ k' ev', (e1.2 < k')%nat → at_evs T !! k' = Some ev' →
    (∀ k'' ag'', (e1.2 < k'')%nat → (k'' ≤ k')%nat →
       at_ags T !! k'' = Some ag'' → ¬ bnd (pa_st ag'')) →
    lb_writes (ae_lb ev') = false ∧ lb_loads (ae_lb ev') = false).

  Theorem bad_edge_violates_blocks b1 b2 :
    bad nh TS (PDevs d0 []) b1 b2 → bad_min nh TS (PDevs d0 []) b2 →
    ∃ (order : list gev) (cfs : list (wpcfg P D)) (cf : wpcfg P D),
      (** (a) THE ORDER: the cone plus the bad read, duplicate-free,
              with the bad read LAST and every [gdep2] predecessor
              strictly earlier (i.e. a valid [qorder] enumeration). *)
      (∀ e, e ∈ order ↔ (gev_wf TS e ∧ (e = b2 ∨ tc (gdep2 TS) e b2))) ∧
      NoDup order ∧
      order !! (length order - 1)%nat = Some b2 ∧
      (∀ n y, order !! n = Some y → ∀ x, gdep2 TS x y → gev_wf TS x →
         ∃ i, (i < n)%nat ∧ order !! i = Some x) ∧
      (** (b) BLOCK STRUCTURE: blocks are contiguous, in-block order is
              trace order, and the READER's block comes last. *)
      (∀ i j k x y z, (i < j)%nat → (j < k)%nat →
         order !! i = Some x → order !! j = Some y → order !! k = Some z →
         bid TS bnd x = bid TS bnd z → bid TS bnd y = bid TS bnd x) ∧
      (∀ i j x y, (i < j)%nat → order !! i = Some x → order !! j = Some y →
         bid TS bnd x = bid TS bnd y → (x.2 < y.2)%nat) ∧
      (∀ i j x y, order !! i = Some x → order !! j = Some y →
         bid TS bnd y = bid TS bnd b2 → bid TS bnd x ≠ bid TS bnd b2 →
         (i < j)%nat) ∧
      (** (c) THE RUN: one configuration per prefix, consecutive ones
              related by a SOLO step of the processed event's agent. *)
      length cfs = S (length order) ∧
      cfs !! 0%nat = Some (wp_init img d0 ps) ∧
      cfs !! (length order) = Some cf ∧
      (∀ i e c c', order !! i = Some e → cfs !! i = Some c →
         cfs !! S i = Some c' → cstep pstep pcls e.1 c c') ∧
      (∀ i c, cfs !! i = Some c → qcfg pstep pcls TS (PDevs d0 []) img d0 ps (take i order) c) ∧
      rtc (wp_pf_run pstep pcls) (wp_init img d0 ps) cf ∧
      (** (d) THE VIOLATION, in both forms. *)
      (∃ p m a, violates_at cf p m b1.1 b2.1 a) ∧
      violation_hart cls_of pub_of nh cf.
  Proof.
    intros Hbad Hmin.
    have Hbad2 := Hbad.
    destruct Hbad2 as (Hrf & Hne & Hh1 & Hh2 & _ & _).
    have Hrf2 := Hrf. destruct Hrf2 as (t0 & a0 & Hts0 & Hrd0).
    have Hb2wf : gev_wf TS b2 by eapply gev_reads_wf.
    have Hb2mem : is_mem TS b2 by eapply reads_mem.
    have Hrr : ¬ tc (gdep2 TS) b2 b2.
    { intros Hc. apply (Hmin b1 b2 Hbad). by apply tc_gdep2_gdep3. }
    destruct (cone_Qinv_nil pstep pcls pdev TS img d0 ps Hwf Hwsi Hco Hwfl Hlf Hobl
                Hcls Hclsobl Himg Hnag Hdata Hps0 Hdf b2 Hb2wf Hrr
                (cone_acyc_of_min_nil pstep TS d0 nh b2 Hwf Hfo Hee Hdf
                   Hsplit Hmin))
      as (ord0 & HQ0 & Hmem0).
    destruct (topo_sort (Rblk' TS bnd b2 ord0) (bids TS bnd b2 ord0)
                (Rblk'_acyc pstep pcls pdev TS img d0 ps Hwf Hwsi Hco Hwfl Hlf
                   Hobl Hcls Hclsobl Himg
                   Hnag Hdata Hdf Hee bnd Hcsl b2 Hb2wf Hrr Hb2mem ord0 HQ0 Hmem0)
                (bids_nodup TS bnd b2 ord0))
      as (bord & Hbordnd & Hbordmem & Hbordlt).
    destruct (topo_sort (Rev TS bnd ord0 bord) ord0
                (Rev_acyc TS ps Hnag bnd ord0 bord)
                (ord0_nodup pstep pcls TS img d0 ps ord0 HQ0))
      as (done_b & Hdnd & Hdmem & Hdord).
    destruct (blocks_violates pstep pcls pdev TS img d0 ps Hwf Hwsi Hco Hwfl Hlf
                Hobl Hcls Hclsobl Himg Hnag Hdata Hdf Hps0 Hee nh bnd b2 Hb2wf Hrr
                Hb2mem ord0 HQ0 Hmem0
                bord Hbordmem Hbordlt done_b Hdnd Hdmem Hdord b1 Hbad)
      as (cfs & cf & Hlenc & Hc0 & Hcf & Hstepc & Hqc & Hrun & Hv1 & Hv2).
    exists (done_full b2 done_b), cfs, cf.
    split_and!.
    - intros e. rewrite /done_full elem_of_app elem_of_list_singleton.
      split.
      + intros [He|He].
        * apply Hdmem, Hmem0 in He as (Hw & Htc). split; [done|by right].
        * subst e. split; [done|by left].
      + intros (Hw & [Heq|Htc]); [by right|left].
        apply Hdmem, Hmem0. by split.
    - exact (done_full_nodup pstep pcls TS img d0 ps Himg b2 Hrr ord0 HQ0 Hmem0
               done_b Hdnd Hdmem).
    - rewrite (done_full_len TS ps Hnag b2 done_b).
      have -> : (S (length done_b) - 1)%nat = length done_b by lia.
      exact (done_full_last TS ps Hnag b2 done_b).
    - exact (done_full_pred pstep pcls TS img d0 ps Hwf Himg Hnag Hee bnd b2
               Hb2wf Hrr
               Hb2mem ord0 HQ0 Hmem0 bord Hbordmem Hbordlt done_b Hdmem Hdord).
    - exact (done_full_contig pstep pcls TS img d0 ps Himg Hnag bnd b2 Hb2wf Hrr
               Hb2mem
               ord0 HQ0 Hmem0 bord Hbordmem Hbordlt done_b Hdmem Hdord).
    - exact (done_full_inblk pstep pcls TS img d0 ps Himg Hnag bnd b2 Hb2wf Hrr
               Hb2mem
               ord0 HQ0 Hmem0 bord Hbordmem Hbordlt done_b Hdnd Hdmem Hdord).
    - exact (done_full_reader_last pstep pcls TS img d0 ps Himg Hnag bnd b2 Hb2wf
               Hrr
               Hb2mem ord0 HQ0 Hmem0 bord Hbordmem Hbordlt done_b Hdmem Hdord).
    - exact Hlenc.
    - exact Hc0.
    - exact Hcf.
    - exact Hstepc.
    - exact Hqc.
    - exact Hrun.
    - exact Hv1.
    - exact Hv2.
  Qed.

End main.
