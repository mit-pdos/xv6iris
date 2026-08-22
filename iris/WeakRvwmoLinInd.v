(** * WeakRvwmoLinInd.v — T2-LIN's INDUCTION SKELETON (route B, stage B2e-3)

    Design: [claude-notes/design/weak-memory-route-b.md] §4d.2 (the proof
    shape: STRONG INDUCTION ON |V| OVER CAUSAL HULLS) and §4d.4.

    WHAT THIS FILE IS.  §4d.2's theorem T2-LIN — "a conformant, RVWMO⁻(+deps)
    consistent graph has an acyclic [RacyD]" — is proved by strong induction
    on the number of events, with the induction hypothesis applied to CAUSAL
    HULLS ([WeakRvwmoHull.gx_hull]).  Everything in that shape EXCEPT the
    cycle kill itself is pure bookkeeping, and that bookkeeping is what this
    file lands:

      (1) THE MEASURE.  [gevs'] enumerates a graph's labelled row positions,
          and a hull's rows are PREFIXES of the graph's rows ([gxh_row]), so
          a cut that drops at least one event ([proper_cut]) strictly
          decreases [length (gevs' _)] ([hull_events_lt]).  The measure is
          read off [gx_prog] alone, exactly as [WeakRvwmoNorm]'s [nviol] is.

      (2) THE KILL INTERFACE.  [cycle_kill] is the obligation §4d.2(2)/(3)
          leaves open, stated so that the induction hypothesis is HANDED TO
          IT: the kill may assume every PROPER hull of the graph is already
          [RacyD]-acyclic.  [hull_realizable_of_acyclic] is the form the kill
          will actually consume — from acyclicity of a proper hull, that
          hull LINEARIZES and its linearization is a real promise-free run
          ([exec_prog_ok']), with the candidate's rows the hull's rows up to
          the normalization's write-index renaming.  That is §4d.2(1)'s
          "run [R_P] with final configuration σ_P" in machine-checked form.

      (3) THE THEOREM AND ITS COROLLARY.  [t2lin_of_cycle_kill] runs the
          induction; [t2lin_supply] composes it with [WeakRvwmoSupply.
          topo_supply] to realize the WHOLE graph.

      (4) NON-VACUITY, on both sides.  [cycle_kill] is a REAL obligation:
          the LB witness [lbgd] carries a [RacyD] cycle ([lbgd_cycle] — two
          [grf] edges and two [gpow] edges), so the premise is not vacuously
          discharged by acyclicity of every graph.  And it is not vacuously
          UNSATISFIABLE either: the message-passing probe [mpgd] — a graph
          that violates rule 14 — is [RacyD]-ACYCLIC ([mpgd_acyclic]), so the
          hypothesis "every proper hull is acyclic" is not itself absurd.

    WHAT IS *NOT* HERE: the kill.  [cycle_kill] is a definition, not a
    theorem; discharging it is B2e-3b (the certification machinery) plus
    B2e-3c (the per-site classification).  Nothing in this file assumes it.

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakDeps.
Require Import WeakLitmus.
Require Import WeakAxiomatic.
Require Import WeakAxiomatic2.
Require Import WeakAxiomatic3.
Require Import WeakRvwmoGraph.
Require Import WeakRvwmoNorm.
Require Import WeakRvwmoXchg.
Require Import WeakRvwmoLin.
Require Import WeakRvwmoRestr.
Require Import WeakRvwmoAcyc.
Require Import WeakRvwmoProbeRestr.
Require Import WeakRvwmoHull.
Require Import WeakRvwmoTopo.
Require Import WeakRvwmoProbeK1.
Require Import WeakRvwmoDec.
Require Import WeakInterp.
Require Import WeakEvLang.
Require Import WeakEvPf.
(* AFTER the axiomatic band, exactly as [WeakRvwmoConf]/[WeakRvwmoSupply] do
   it: the WLABEL constructors are the unqualified ones here, and the graph's
   are written [WeakAxiomatic.LLoad] &c. *)
Require Import WeakPromise.
Require Import WeakPromiseFact.
Require Import WeakPromiseBridge.
Require Import WeakAxRealize.
Require Import WeakEvInst.
Require Import WeakRvwmoConf.
Require Import WeakRvwmoSupply.

(* ====================================================================== *)
(** * 1. THE MEASURE: the number of row positions

    [length (gevs' G)] is the sum of the row lengths, and a hull's rows are
    prefixes — so the measure is a sum comparison, index by index. *)

Lemma sum_list_seq_le (f g : nat → nat) (N : nat) :
  (∀ i, (f i ≤ g i)%nat) →
  ∀ s, (sum_list (f <$> seq s N) ≤ sum_list (g <$> seq s N))%nat.
Proof.
  intros Hle. induction N as [|N IH]; intros s; [done|].
  csimpl. pose proof (Hle s). pose proof (IH (S s)). lia.
Qed.

Lemma sum_list_seq_lt (f g : nat → nat) (N : nat) :
  (∀ i, (f i ≤ g i)%nat) →
  ∀ s i0, (s ≤ i0)%nat → (i0 < s + N)%nat → (f i0 < g i0)%nat →
  (sum_list (f <$> seq s N) < sum_list (g <$> seq s N))%nat.
Proof.
  intros Hle. induction N as [|N IH]; intros s i0 H1 H2 H3; [lia|].
  csimpl. destruct (decide (i0 = s)) as [->|Hne].
  - pose proof (sum_list_seq_le f g N Hle (S s)). lia.
  - pose proof (IH (S s) i0 ltac:(lia) ltac:(lia) H3). pose proof (Hle s). lia.
Qed.

(** The measure, as a sum of row lengths. *)
Lemma length_gevs' G :
  length (gevs' G)
  = sum_list ((λ i, nrow G i) <$> seq 0%nat (length (gx_prog G))).
Proof.
  rewrite /gevs' length_join -list_fmap_compose. f_equal.
  apply list_fmap_ext. intros i k _. by rewrite /= length_fmap length_seq.
Qed.

(** A nonempty row is a row of an EXISTING hart. *)
Lemma nrow_lt_nharts G i :
  (0 < nrow G i)%nat → (i < length (gx_prog G))%nat.
Proof.
  rewrite /nrow. destruct (gx_prog G !! i) as [p|] eqn:E; simpl.
  - intros _. by eapply lookup_lt_Some.
  - lia.
Qed.

(** The hull's rows are the cut prefixes, renamed — so its row lengths are
    the [min]s and its hart count is unchanged. *)
Lemma gxh_nrow G cs i :
  nrow (gx_hull G cs) i = (default 0%nat (cs !! i) `min` nrow G i)%nat.
Proof. rewrite /nrow gxh_row length_fmap length_take //. Qed.

Lemma gxh_nharts_eq G cs :
  length cs = length (gx_prog G) →
  length (gx_prog (gx_hull G cs)) = length (gx_prog G).
Proof.
  intros Hlen.
  change (gx_prog (gx_hull G cs))
    with ((λ row : list WeakAxiomatic.lbl, lbl_ren (hren G cs) <$> row)
            <$> zip_with take cs (gx_prog G)).
  rewrite length_fmap length_zip_with Hlen. lia.
Qed.

(** THE CUT VOCABULARY: a hull cut that DROPS AT LEAST ONE EVENT. *)
Definition proper_cut (G : gexec) (cs : list nat) : Prop :=
  hull_ok G cs ∧ ∃ i, (default 0%nat (cs !! i) < nrow G i)%nat.

Lemma proper_cut_ok G cs : proper_cut G cs → hull_ok G cs.
Proof. by intros [? _]. Qed.

(** THE INDUCTION'S DECREASE. *)
Theorem hull_events_lt G cs :
  proper_cut G cs →
  (length (gevs' (gx_hull G cs)) < length (gevs' G))%nat.
Proof.
  intros [Hok (i0 & Hi0)]. pose proof (hull_ok_len G cs Hok) as Hlen.
  rewrite !length_gevs' (gxh_nharts_eq G cs Hlen).
  have Hle : ∀ i, (nrow (gx_hull G cs) i ≤ nrow G i)%nat.
  { intros i. rewrite gxh_nrow. lia. }
  apply (sum_list_seq_lt (λ i, nrow (gx_hull G cs) i) (λ i, nrow G i)
           (length (gx_prog G)) Hle 0%nat i0).
  - lia.
  - rewrite Nat.add_0_l. apply nrow_lt_nharts. lia.
  - rewrite gxh_nrow. lia.
Qed.

(** NON-VACUITY of [proper_cut] (hence of [hull_events_lt]): the frontier
    probe's cut [ecs = [1;0]] IS rf-closed ([WeakRvwmoHull.erg_hull_ok]) and
    drops hart 1's whole row.  This is the very cut B1a's [restr_ok] provably
    could not express ([erg_hull_beats_restr]). *)
Theorem erg_proper_cut : proper_cut erg ecs.
Proof. split; [exact erg_hull_ok|]. exists 1%nat. compute. lia. Qed.

Corollary erg_hull_events_lt :
  (length (gevs' (gx_hull erg ecs)) < length (gevs' erg))%nat.
Proof. apply hull_events_lt, erg_proper_cut. Qed.

(* ====================================================================== *)
(** * 2. THE KILL INTERFACE

    §4d.2's induction step, stated as an obligation on the graph's cycle: at
    a conformant consistent graph EVERY PROPER HULL OF WHICH IS ALREADY
    ACYCLIC, there is no [RacyD] cycle.  The third premise IS the induction
    hypothesis — the kill is free to turn it into a real promise-free run
    (via [hull_realizable_of_acyclic] below) and to read the exports at that
    run's configurations, which is exactly §4d.2(2)'s certification. *)

Definition cycle_kill (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) : Prop :=
  ∀ GD : gdexec,
    rvwmo_minus_deps_consistent GD →
    gdexec_qconf boot d0 im nh GD →
    (∀ cs, proper_cut (gd_g GD) cs →
           ∀ x, ¬ tc (RacyD (gd_hull GD cs)) x x) →
    ∀ x, tc (RacyD GD) x x → False.

(** THE FORM THE KILL CONSUMES.  From the induction hypothesis at a proper
    cut: the hull LINEARIZES and its linearization is a promise-free run of
    the real machine, with the candidate's rows the hull's rows up to the
    normalization's write-index renaming [pi].  This is §4d.2(1)'s "[P] has
    a promise-free run [R_P] at whose final configuration every export
    holds", assembled from [gdexec_qconf_hull] (conformance restricts),
    [hull_deps_consistent] (consistency restricts), [racyD_dec] +
    [normalize_of_acyclic] (acyclicity ⇒ a rule-14 form) and
    [supply_of_qconf] (the interleaving).

    It is [topo_supply]'s composition, RE-RUN so that the row equation
    survives — [topo_supply] drops it, and the kill needs to know that the
    run's events ARE the hull's events. *)
Theorem hull_realizable_of_acyclic (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) (GD : gdexec) (cs : list nat) (N : nat) :
  rvwmo_minus_deps_consistent GD →
  gdexec_qconf boot d0 im nh GD →
  proper_cut (gd_g GD) cs →
  (∀ x, ¬ tc (RacyD (gd_hull GD cs)) x x) →
  (length (gx_prog (gd_g GD)) ≤ N)%nat →
  ∃ (c : cand) (pst : nat → list pexv6) (pi : nat → nat),
    srvwmo_consistent c ∧
    cd_img c = gx_img (gd_g GD) ∧
    pst 0%nat = boot <$> seq 0 N ∧
    exec_prog_ok' pstep_ev pcls_ev pst (λ _, d0) (cand_exec c) ∧
    (∀ i, (λ s, es_lb s) <$> filter (λ s, es_ag s = i) (cd_tr c)
          = lbl_ren pi
              <$> default [] (gx_prog (gx_hull (gd_g GD) cs) !! i)).
Proof.
  intros Hcons Hq Hpc Hacy HN.
  have Hok : hull_ok (gd_g GD) cs := proper_cut_ok _ _ Hpc.
  have Hch : rvwmo_minus_deps_consistent (gd_hull GD cs)
    by apply hull_deps_consistent.
  have Hqh : gdexec_qconf boot d0 im nh (gd_hull GD cs)
    by apply gdexec_qconf_hull.
  destruct (normalize_of_acyclic (gd_hull GD cs) Hch
              (λ x y, racyD_dec (gd_hull GD cs) x y) Hacy)
    as (GD' & pi & Hcons' & H14 & Hrr & Hdeps & _).
  have Hq' : gdexec_qconf boot d0 im nh GD'
    by (eapply gdexec_qconf_ren; [exact Hrr|exact Hdeps|exact Hqh]).
  destruct Hcons' as (Hc' & _ & _).
  destruct (rule14_linearization (gd_g GD') Hc' H14)
    as (c & Hsr & Himg & Hrow & _).
  (* the rows of [GD'] are the hull's rows, renamed *)
  have Hprog : ∀ i, default [] (gx_prog (gd_g GD') !! i)
                    = lbl_ren pi
                        <$> default [] (gx_prog (gx_hull (gd_g GD) cs) !! i).
  { intros i. destruct Hrr as (_ & Hp & _).
    rewrite Hp list_lookup_fmap.
    change (gx_prog (gd_g (gd_hull GD cs)))
      with (gx_prog (gx_hull (gd_g GD) cs)).
    by destruct (gx_prog (gx_hull (gd_g GD) cs) !! i). }
  destruct (supply_of_qconf c boot d0
              (λ i, default [] (gx_prog (gd_g GD') !! i)) N)
    as (pst & Hpst0 & Hprg).
  - exact Hrow.
  - intros i Hi. apply prog_row_nil.
    rewrite (rows_rel_nharts pi (gd_g (gd_hull GD cs)) (gd_g GD') Hrr).
    change (gx_prog (gd_g (gd_hull GD cs)))
      with (gx_prog (gx_hull (gd_g GD) cs)).
    pose proof (gxh_nharts (gd_g GD) cs). lia.
  - intros i _. exact (qconf_rows boot d0 im nh GD' i Hq').
  - exists c, pst, pi. split_and!; [done| |done|done|].
    + rewrite Himg (rows_rel_img pi (gd_g (gd_hull GD cs)) (gd_g GD') Hrr).
      apply gxh_img.
    + intros i. by rewrite (Hrow i) (Hprog i).
Qed.

(* ====================================================================== *)
(** * 3. THE THEOREM: T2-LIN, by strong induction on the event count *)

Lemma t2lin_aux (boot : agent → pexv6) (d0 : dev_state) (im : image) (nh : nat) :
  cycle_kill boot d0 im nh →
  ∀ (n : nat) (GD : gdexec),
    (length (gevs' (gd_g GD)) ≤ n)%nat →
    rvwmo_minus_deps_consistent GD →
    gdexec_qconf boot d0 im nh GD →
    ∀ x, ¬ tc (RacyD GD) x x.
Proof.
  intros Hk n. induction n as [|n IH]; intros GD Hlen Hcons Hq x Hcyc.
  - (* no events at all: no cut is proper, so the hypothesis is vacuous *)
    eapply (Hk GD Hcons Hq); [|exact Hcyc].
    intros cs Hpc y Hcy.
    pose proof (hull_events_lt (gd_g GD) cs Hpc). lia.
  - eapply (Hk GD Hcons Hq); [|exact Hcyc].
    intros cs Hpc. apply (IH (gd_hull GD cs)).
    + pose proof (hull_events_lt (gd_g GD) cs Hpc). simpl. lia.
    + by apply hull_deps_consistent; [|apply Hpc].
    + by apply gdexec_qconf_hull.
Qed.

Theorem t2lin_of_cycle_kill (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) :
  cycle_kill boot d0 im nh →
  ∀ GD : gdexec,
    rvwmo_minus_deps_consistent GD →
    gdexec_qconf boot d0 im nh GD →
    ∀ x, ¬ tc (RacyD GD) x x.
Proof.
  intros Hk GD. by eapply (t2lin_aux boot d0 im nh Hk (length (gevs' (gd_g GD)))).
Qed.

(** THE COROLLARY: the whole graph is realized.  [topo_supply] at the full
    graph, with T2-LIN supplying its acyclicity premise and [racyD_dec] its
    decidability premise. *)
Theorem t2lin_supply (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) (GD : gdexec) (N : nat) :
  cycle_kill boot d0 im nh →
  rvwmo_minus_deps_consistent GD →
  gdexec_qconf boot d0 im nh GD →
  (length (gx_prog (gd_g GD)) ≤ N)%nat →
  ∃ (c : cand) (pst : nat → list pexv6),
    srvwmo_consistent c ∧
    cd_img c = gx_img (gd_g GD) ∧
    pst 0%nat = boot <$> seq 0 N ∧
    exec_prog_ok' pstep_ev pcls_ev pst (λ _, d0) (cand_exec c).
Proof.
  intros Hk Hcons Hq HN.
  eapply topo_supply;
    [exact Hcons|exact (λ x y, racyD_dec GD x y)| |exact Hq|exact HN].
  by eapply t2lin_of_cycle_kill.
Qed.

(* ====================================================================== *)
(** * 4. NON-VACUITY (i): [cycle_kill] IS A REAL OBLIGATION

    The LB witness carries a [RacyD] cycle: each hart's load is [gpow]-before
    its own store, and each load reads the OTHER hart's store ([grf]).  So the
    kill is not discharged by "no consistent graph has a cycle" — it must use
    conformance. *)

Lemma lbg_gpow_0 : gpow lbg (0%nat, 0%nat) (0%nat, 1%nat).
Proof.
  split_and!.
  - split_and!; [done|simpl; lia|by eexists|by eexists].
  - eexists. split; reflexivity.
  - reflexivity.
Qed.

Lemma lbg_gpow_1 : gpow lbg (1%nat, 0%nat) (1%nat, 1%nat).
Proof.
  split_and!.
  - split_and!; [done|simpl; lia|by eexists|by eexists].
  - eexists. split; reflexivity.
  - reflexivity.
Qed.

(** hart 1's load reads hart 0's store (write index 1). *)
Lemma lbg_grf_01 : grf lbg (0%nat, 1%nat) (1%nat, 0%nat).
Proof.
  exists 8%Z, 1%nat, WeakLitmus.b1. split.
  - exists (WeakAxiomatic.LLoad false 8 [1%nat] [WeakLitmus.b1]),
           8%Z, [1%nat], [WeakLitmus.b1], 0%nat.
    split_and!; reflexivity.
  - by vm_compute.
Qed.

(** hart 0's load reads hart 1's store (write index 2). *)
Lemma lbg_grf_10 : grf lbg (1%nat, 1%nat) (0%nat, 0%nat).
Proof.
  exists 0%Z, 2%nat, WeakLitmus.b1. split.
  - exists (WeakAxiomatic.LLoad false 0 [2%nat] [WeakLitmus.b1]),
           0%Z, [2%nat], [WeakLitmus.b1], 0%nat.
    split_and!; reflexivity.
  - by vm_compute.
Qed.

Theorem lbgd_cycle : ∃ x, tc (RacyD lbgd) x x.
Proof.
  exists (0%nat, 0%nat).
  eapply tc_l; [left; left; exact lbg_gpow_0|].
  eapply tc_l; [left; right; left; exact lbg_grf_01|].
  eapply tc_l; [left; left; exact lbg_gpow_1|].
  apply tc_once. left; right; left; exact lbg_grf_10.
Qed.

(* ====================================================================== *)
(** * 5. NON-VACUITY (ii): the hull hypothesis is not absurd

    [mpgd] — the message-passing probe, a graph that VIOLATES rule 14 — is
    nevertheless [RacyD]-acyclic.  Route: [mpg]'s [Racy] has no [gco] and no
    [gfr] edge (its two writes touch different bytes, and its only read reads
    the co-maximal write of its byte), so [Racy mpg ⊆ Rt mpg], which
    transports along the normalization orbit to the rule-14 graph [mpg']
    ([Rt_acyclic_orbit]).  This is much cheaper than an [R_acyclic] at [mpg]
    itself, which is FALSE as a route: [mpg] has no [grule14]. *)

Lemma mpg_rd (e : geid) (a : Z) (t : nat) (v : bv 8) :
  greads_byte mpg e a t v → e = (0%nat, 0%nat) ∧ a = 0%Z ∧ t = 2%nat.
Proof.
  intros (l & b & ts & vs & j & Hl & Hrd & Ht & Hv & Ha).
  destruct e as [i k]. rewrite /gx_lbl /= in Hl.
  destruct i as [|[|i]]; simpl in Hl; [| |done];
    destruct k as [|[|k]]; simplify_eq/=;
    destruct j as [|j]; simplify_eq/=;
    rewrite /acc_addr /=; naive_solver.
Qed.

Lemma mpg_no_gco w w' : ¬ gco mpg w w'.
Proof.
  intros (a & v & v' & H1 & H2 & Hlt).
  apply mpg_wr in H1. apply mpg_wr in H2.
  destruct H1 as [[-> ->]|[-> ->]]; destruct H2 as [[-> ?]|[-> ?]];
    simplify_eq; lia.
Qed.

Lemma mpg_no_gfr r w' : ¬ gfr mpg r w'.
Proof.
  intros (Hne & a & t & v & v' & Hrd & Hwb & Hlt).
  destruct (mpg_rd r a t v Hrd) as (-> & -> & ->).
  apply mpg_wr in Hwb. destruct Hwb as [[-> Hc]|[-> _]]; [done|].
  have Hw : gwix mpg (1%nat, 0%nat) = 2%nat by vm_compute.
  rewrite Hw in Hlt. lia.
Qed.

Lemma mpg_Racy_Rt x y : Racy mpg x y → Rt mpg x y.
Proof.
  intros [H|[H|[H|[H|H]]]].
  - by left.
  - by right; left.
  - by destruct (mpg_no_gco x y).
  - by destruct (mpg_no_gfr x y).
  - by right; right.
Qed.

Theorem mpgd_acyclic x : ¬ tc (RacyD mpgd) x x.
Proof.
  intros Hcyc.
  eapply (Rt_acyclic_orbit (tswap 1) mpg mpg' x mpg'_consistent mpg'_rule14
            mpg_rows_rel mpg_wperm).
  eapply tc_mono; [|exact Hcyc].
  intros a b [H|H%elem_of_nil]; [by apply mpg_Racy_Rt|done].
Qed.

(* ====================================================================== *)
(** * 6. AUDIT *)

Print Assumptions hull_events_lt.
Print Assumptions erg_hull_events_lt.
Print Assumptions hull_realizable_of_acyclic.
Print Assumptions t2lin_of_cycle_kill.
Print Assumptions t2lin_supply.
Print Assumptions lbgd_cycle.
Print Assumptions mpgd_acyclic.
