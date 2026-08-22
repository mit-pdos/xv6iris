(** * WeakRvwmoFabInd.v — B1b-2's RESIDUE: the fabric bundle's hull
    restriction and the [cycle_kill] mirror.

    Design: [claude-notes/design/weak-memory-route-b.md] §4d.4 (B1b).
    [WeakRvwmoFab] lands the fabric-order bundle ([gfexec_conf]) and its
    consistency restriction ([gf_hull_consistent]); its §8 closing comment
    enumerates FIVE obligations (O1–O5) for the CONFORMANCE restriction and
    a [cycle_kill] mirror.  This leaf discharges them:

      §1  O1/O2 — [hemitf_prefix] / [hemitf_ren] (and their [hart_conff]
          corollaries), the two-endpoint emission's stability lemmas.
      §2  O3 — [em_dev] under an item prefix: the tag-monotonicity
          induction ([hemitf_tag_lt]) plus [em_dev]'s [app] equation, giving
          [is_dev_block] agreement below the cut.
      §3  O4/O5 — [gfexec_conf_hull] (and [gfexec_conf_ren], which the
          normalization needs).
      §4  THE MIRROR — [proper_cut_F], [gf_hull_events_lt], [cycle_kill_F],
          [fconf_realize] / [hull_realizable_of_acyclic_F],
          [t2lin_of_cycle_kill_F], [t2lin_supply_F].
      §5  THE DEV-ORDER FINDING (the report's headline): the T2-1c trace
          does NOT respect the fabric order, and here is why, in both
          directions — machine-checked.
      §6  NON-VACUITY: [cycle_kill_of_F], the two skeletons related.

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
Require Import WeakRvwmoHull.
Require Import WeakRvwmoTopo.
Require Import WeakRvwmoDec.
Require Import WeakInterp.
Require Import WeakEvLang.
Require Import WeakEvPf.
Require Import WeakPromise.
Require Import WeakPromiseFact.
Require Import WeakPromiseBridge.
Require Import WeakAxRealize.
Require Import WeakEvInst.
Require Import WeakRvwmoConf.
Require Import WeakRvwmoSupply.
Require Import WeakRvwmoFab.
Require Import WeakRvwmoLinInd.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** * 1. O1/O2: THE TWO-ENDPOINT EMISSION'S STABILITY LEMMAS *)

(** ** 1.1 O2: the normalization orbit ([WeakRvwmoConf.hemit_ren]'s
    induction, verbatim at [hemitf] — the fabric endpoints are untouched). *)
Lemma hemitf_ren π dvi dvo k ws row p es pfin :
  hemitf dvi dvo k ws row p es pfin →
  ∀ ws', w_relp ws' = w_relp ws →
  hemitf dvi dvo k ws' (lbl_ren π <$> row) p (eitem_ren π <$> es) pfin.
Proof.
  induction 1 as [k ws p
                 |k ws lb row p ls pa da l p' es pfin Har Hre Hst Hem IH
                 |k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin
                  Har1 Hre Hst1 Har2 Hst2 Hem IH];
    intros ws' Hrelp.
  - apply HFnil.
  - rewrite eitem_ren_block.
    eapply HFone.
    + by apply adm_run_ren.
    + by eapply hlbl_realizes_ren.
    + destruct Hre as (_ & Hlat & Hrf & _). by apply pstep_ev_wren.
    + apply IH. by apply lbl_post_relp_ren.
  - rewrite eitem_ren_block eitem_ren_block.
    have Hshape := Hre.
    destruct Hshape as (aq & rl & base & tvs & data & asrc1 & asrc2 & vsrc2 &
                        -> & -> & Hne & Hlen & Hlb).
    eapply HFpair.
    + by apply adm_run_ren.
    + by eapply hlbl_realizes_pair_ren.
    + eapply (pstep_ev_wren π); [done|done|exact Hst1].
    + by apply adm_run_ren.
    + eapply (pstep_ev_wren π); [done|done|exact Hst2].
    + apply IH. by apply lbl_post_relp_ren.
Qed.

Lemma hart_conff_ren π i row p0 dvi dvo em :
  hart_conff i row p0 dvi dvo em →
  hart_conff i (lbl_ren π <$> row) p0 dvi dvo (em_ren π em).
Proof. intros Hem. by eapply hemitf_ren. Qed.

(** ** 1.2 TAG MONOTONICITY (the ingredient O3 names)

    Every tag in the item list of [hemitf … k0 …] is a row position of
    [row], SHIFTED BY [k0]: at least [k0], and below [k0 + length row]. *)
Lemma hemitf_tag_lt dvi dvo k ws row p es pfin it j :
  hemitf dvi dvo k ws row p es pfin → it ∈ es → it.2 = Some j →
  (k ≤ j)%nat ∧ (j - k < length row)%nat.
Proof.
  induction 1 as [k ws p
                 |k ws lb row p ls pa da l p' es pfin Har Hre Hst Hem IH
                 |k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin
                  Har1 Hre Hst1 Har2 Hst2 Hem IH];
    intros Hit Hj.
  - by apply elem_of_nil in Hit.
  - apply elem_of_app in Hit as [Hit|Hit].
    { apply elem_of_list_fmap in Hit as (l0 & -> & _). done. }
    apply elem_of_cons in Hit as [->|Hit].
    { simpl in Hj. simplify_eq. simpl. lia. }
    destruct (IH Hit Hj) as [Hle Hlt]. simpl. lia.
  - apply elem_of_app in Hit as [Hit|Hit].
    { apply elem_of_list_fmap in Hit as (l0 & -> & _). done. }
    apply elem_of_cons in Hit as [->|Hit].
    { simpl in Hj. simplify_eq. simpl. lia. }
    apply elem_of_app in Hit as [Hit|Hit].
    { apply elem_of_list_fmap in Hit as (l0 & -> & _). done. }
    apply elem_of_cons in Hit as [->|Hit].
    { simpl in Hj. simplify_eq. simpl. lia. }
    destruct (IH Hit Hj) as [Hle Hlt]. simpl. lia.
Qed.

Lemma hemitf_tag_ge dvi dvo k ws row p es pfin it j :
  hemitf dvi dvo k ws row p es pfin → it ∈ es → it.2 = Some j → (k ≤ j)%nat.
Proof. intros Hem Hit Hj. by destruct (hemitf_tag_lt _ _ _ _ _ _ _ _ _ _ Hem Hit Hj). Qed.

(** ** 1.3 O1: prefix restriction, with the DROPPED TAIL'S TAGS BOUNDED

    [WeakRvwmoConf.hemit_prefix] hands back only [es' `prefix_of` es]; O3
    needs to know that the dropped tail carries no tag BELOW the cut, so the
    decomposition is returned explicitly. *)
Lemma hemitf_prefix dvi dvo k ws row p es pfin :
  hemitf dvi dvo k ws row p es pfin →
  ∀ n, ∃ es1 es2 pfin', es = es1 ++ es2 ∧
       hemitf dvi dvo k ws (take n row) p es1 pfin' ∧
       (∀ it j, it ∈ es2 → it.2 = Some j → (k + n ≤ j)%nat).
Proof.
  intros Hem. induction Hem as [k ws p
                 |k ws lb row p ls pa da l p' es pfin Har Hre Hst Hem IH
                 |k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin
                  Har1 Hre Hst1 Har2 Hst2 Hem IH];
    intros n.
  - exists [], [], p. split_and!; [done| |].
    + rewrite take_nil. apply HFnil.
    + intros it j Hit. by apply elem_of_nil in Hit.
  - destruct n as [|n].
    { exists [], (eadm ls ++ (l, Some k) :: es), p. split_and!; [done|apply HFnil|].
      intros it j Hit Hj. rewrite Nat.add_0_r.
      eapply (hemitf_tag_ge dvi dvo k ws (lb :: row) p _ pfin it j);
        [by eapply HFone|exact Hit|exact Hj]. }
    destruct (IH n) as (es1 & es2 & pfin' & -> & Hem' & Hbnd).
    exists (eadm ls ++ (l, Some k) :: es1), es2, pfin'. split_and!.
    + by rewrite -app_assoc.
    + rewrite firstn_cons. by eapply HFone.
    + intros it j Hit Hj. have := Hbnd it j Hit Hj. lia.
  - destruct n as [|n].
    { exists [], (eadm ls1 ++ (l1, Some k) :: eadm ls2 ++ (l2, Some k) :: es), p.
      split_and!; [done|apply HFnil|].
      intros it j Hit Hj. rewrite Nat.add_0_r.
      eapply (hemitf_tag_ge dvi dvo k ws (lb :: row) p _ pfin it j);
        [by eapply HFpair|exact Hit|exact Hj]. }
    destruct (IH n) as (es1 & es2 & pfin' & -> & Hem' & Hbnd).
    exists (eadm ls1 ++ (l1, Some k) :: eadm ls2 ++ (l2, Some k) :: es1), es2,
      pfin'. split_and!.
    + by rewrite -app_assoc -app_comm_cons -app_assoc.
    + rewrite firstn_cons. by eapply HFpair.
    + intros it j Hit Hj. have := Hbnd it j Hit Hj. lia.
Qed.

(* ====================================================================== *)
(** * 2. O3: [em_dev] UNDER AN ITEM PREFIX

    [em_dev]'s recursion RESETS its pending flag at every tagged item, so a
    suffix carrying no tag [= k] contributes nothing to block [k] whatever
    the flag it is entered with — which is what makes the fold agree on a
    prefix that already contains block [k] entirely. *)

Lemma em_dev_no_tag k es :
  (∀ it, it ∈ es → it.2 ≠ Some k) → ∀ pend, em_dev pend k es = false.
Proof.
  induction es as [|it es IH]; intros Hnt pend; [done|].
  have Hrest : ∀ it', it' ∈ es → it'.2 ≠ Some k
    by (intros it' Hit'; apply Hnt, elem_of_list_further).
  destruct it as [l o]. destruct o as [j|]; simpl.
  - case_bool_decide as Hc; [|by apply IH].
    exfalso. apply (Hnt (l, Some j) (elem_of_list_here _ _)). by rewrite /= Hc.
  - by apply IH.
Qed.

Lemma em_dev_app_no_tag k es1 es2 :
  (∀ it, it ∈ es2 → it.2 ≠ Some k) →
  ∀ pend, em_dev pend k (es1 ++ es2) = em_dev pend k es1.
Proof.
  intros Hnt. induction es1 as [|it es1 IH]; intros pend; simpl.
  - by apply em_dev_no_tag.
  - destruct it as [l o]. destruct o as [j|]; simpl.
    + case_bool_decide as Hc; [|by apply IH]. by rewrite IH.
    + by apply IH.
Qed.

(** THE PREFIX RESTRICTION, with the dev blocks below the cut AGREEING. *)
Lemma hart_conff_prefix i row p0 dvi dvo em n :
  hart_conff i row p0 dvi dvo em →
  ∃ em', hart_conff i (take n row) p0 dvi dvo em' ∧
         em_items em' `prefix_of` em_items em ∧
         (∀ k, (k < n)%nat → (is_dev_block em' k ↔ is_dev_block em k)).
Proof.
  intros Hem.
  destruct (hemitf_prefix _ _ _ _ _ _ _ _ Hem n)
    as (es1 & es2 & pfin' & Heq & Hem' & Hbnd).
  exists (HEm es1 pfin'). split_and!.
  - exact Hem'.
  - rewrite /= Heq. by exists es2.
  - intros k Hk. rewrite /is_dev_block /= Heq.
    rewrite (em_dev_app_no_tag k es1 es2); [done|].
    intros it Hit Hj. have := Hbnd it k Hit Hj. lia.
Qed.

(** … and the renaming leaves them alone ([em_dev_ren]). *)
Lemma is_dev_block_ren π em k : is_dev_block (em_ren π em) k ↔ is_dev_block em k.
Proof. rewrite /is_dev_block /em_ren /= em_dev_ren //. Qed.

(** The row-position bound O4 consumes: a [row_deps] edge of an emission of
    [row] names row positions of [row] — [hart_conf_row_deps_wf]'s arithmetic
    half, at [hemitf]. *)
Lemma hart_conff_row_deps_lt i row p0 dvi dvo em jk :
  hart_conff i row p0 dvi dvo em → jk ∈ row_deps (em_items em) →
  (jk.1 < length row)%nat ∧ (jk.2 < length row)%nat.
Proof.
  intros Hem Hjk. split.
  - destruct (row_deps_src _ _ Hjk) as (it & Hit & Hpos & _).
    destruct (hemitf_tag_lt _ _ _ _ _ _ _ _ _ _ Hem Hit Hpos) as [_ H].
    rewrite Nat.sub_0_r in H. exact H.
  - destruct (row_deps_tgt _ _ Hjk) as (it & Hit & Hpos & _).
    destruct (hemitf_tag_lt _ _ _ _ _ _ _ _ _ _ Hem Hit Hpos) as [_ H].
    rewrite Nat.sub_0_r in H. exact H.
Qed.

(* ====================================================================== *)
(** * 3. O4/O5: THE CONFORMANCE RESTRICTIONS *)

(** ** 3.1 The normalization orbit (needed by §4's linearization route)

    [gf_dev] names EVENTS — hart and row position — and the orbit renames
    only the labels' ts columns, so the fabric order transports UNCHANGED
    and [is_dev_block] is renaming-blind ([is_dev_block_ren]). *)
Lemma gfexec_conf_ren π boot d0 fab GF GF' :
  rows_rel π (gd_g (gf_gd GF)) (gd_g (gf_gd GF')) →
  gd_deps (gf_gd GF') = gd_deps (gf_gd GF) →
  gf_dev GF' = gf_dev GF →
  gfexec_conf boot d0 fab GF → gfexec_conf boot d0 fab GF'.
Proof.
  intros Hrr Hdeps Hdev (H0 & Hnd & Hbnd & Hc). split_and!.
  - exact H0.
  - by rewrite Hdev.
  - intros n i k Hn. rewrite Hdev in Hn.
    destruct (Hbnd n i k Hn) as (row & Hrow & Hlt).
    exists (lbl_ren π <$> row). split.
    + by eapply rows_rel_row.
    + by rewrite length_fmap.
  - intros i row' Hrow'.
    destruct Hrr as (_ & Hprog & Hz).
    rewrite Hprog list_lookup_fmap in Hrow'.
    apply fmap_Some in Hrow' as (row & Hrow & ->).
    destruct (Hc i row Hrow) as (em & dvi & dvo & Hem & Hiff & Hpin & Hdep).
    exists (em_ren π em), dvi, dvo. split_and!.
    + by apply hart_conff_ren.
    + intros k Hk. rewrite length_fmap in Hk. rewrite Hdev is_dev_block_ren.
      by apply Hiff.
    + intros k n Hn. rewrite Hdev in Hn. by apply Hpin.
    + intros jk Hjk. rewrite Hdeps. apply Hdep.
      by rewrite /em_ren /= row_deps_ren in Hjk.
Qed.

(** ** 3.2 THE HULL: O1–O5 assembled

    [WeakRvwmoHull]'s rows are CUT-then-RENAMED, so the seam is
    [hart_conff_prefix] followed by [hart_conff_ren] — exactly
    [gdexec_qconf_hull]'s shape, with two additions: the [gf_dev]
    membership iff restricts because [is_dev_block] agrees below the cut
    (O3) and [gcut] holds exactly there (O4), and the [fab] clause is
    LITERALLY unchanged because [dclosed] makes the filtered fabric order a
    PREFIX (O5, [gf_hull_dev_lookup]). *)
Theorem gfexec_conf_hull boot d0 fab GF cs :
  gfexec_consistent GF →
  dclosed cs (gf_dev GF) →
  hull_ok (gd_g (gf_gd GF)) cs →
  gfexec_conf boot d0 fab GF →
  gfexec_conf boot d0 fab (gf_hull GF cs).
Proof.
  intros _ Hdc Hok (H0 & Hnd & Hbnd & Hc). split_and!.
  - exact H0.
  - simpl. by apply list_relations.NoDup_filter.
  - intros n i k Hn.
    have Hn' : gf_dev GF !! n = Some (i, k)
      by (eapply gf_hull_dev_lookup; [exact Hdc|exact Hn]).
    have Hcut : gcut cs (i, k) = true by (eapply gf_hull_dev_cut, Hn).
    destruct (gcut_elim cs (i, k) Hcut) as (c & Hcs & Hkc). simpl in Hcs, Hkc.
    destruct (Hbnd n i k Hn') as (row & Hrow & Hlt).
    exists (lbl_ren (hren (gd_g (gf_gd GF)) cs) <$> take c row). split.
    + change (gx_prog (gd_g (gf_gd (gf_hull GF cs))))
        with (gx_prog (gx_hull (gd_g (gf_gd GF)) cs)).
      rewrite gxh_prog_lookup Hcs /= Hrow //.
    + rewrite length_fmap length_take. lia.
  - intros i row' Hrow'.
    change (gx_prog (gd_g (gf_gd (gf_hull GF cs))))
      with (gx_prog (gx_hull (gd_g (gf_gd GF)) cs)) in Hrow'.
    rewrite gxh_prog_lookup in Hrow'.
    destruct (cs !! i) as [c|] eqn:Hcs; [|done]. simpl in Hrow'.
    destruct (gx_prog (gd_g (gf_gd GF)) !! i) as [row|] eqn:Hrow; [|done].
    simpl in Hrow'. injection Hrow' as <-.
    destruct (Hc i row Hrow) as (em & dvi & dvo & Hem & Hiff & Hpin & Hdep).
    destruct (hart_conff_prefix i row (boot i) dvi dvo em c Hem)
      as (em' & Hem' & Hpre & Hdev).
    exists (em_ren (hren (gd_g (gf_gd GF)) cs) em'), dvi, dvo. split_and!.
    + by apply hart_conff_ren.
    + intros k Hk. rewrite length_fmap length_take in Hk.
      have Hkc : (k < c)%nat by lia.
      rewrite is_dev_block_ren (Hdev k Hkc).
      rewrite (Hiff k ltac:(lia)). simpl.
      rewrite elem_of_list_filter. split.
      * intros Hin. split; [|done]. apply Is_true_true_2.
        by eapply (gcut_intro cs (i, k) c).
      * by intros [_ ?].
    + intros k n Hn. apply Hpin.
      by eapply gf_hull_dev_lookup; [exact Hdc|exact Hn].
    + intros jk Hjk.
      rewrite /em_ren /= row_deps_ren in Hjk.
      destruct (hart_conff_row_deps_lt i (take c row) (boot i) dvi dvo em' jk
                  Hem' Hjk) as [Hlt1 Hlt2].
      rewrite length_take in Hlt1. rewrite length_take in Hlt2.
      apply gd_hull_deps. split_and!.
      * apply Hdep. by eapply row_deps_prefix.
      * apply (gcut_intro cs (i, jk.1) c); [done|simpl; lia].
      * apply (gcut_intro cs (i, jk.2) c); [done|simpl; lia].
Qed.

(* ====================================================================== *)
(** * 4. THE [cycle_kill] MIRROR

    [WeakRvwmoLinInd]'s skeleton, at the fabric bundle.  The cut vocabulary
    gains one clause — [dclosed], without which neither consistency nor
    conformance restricts (that is [WeakRvwmoFab] §8's second design
    finding) — and the measure is unchanged, being about the GRAPH only. *)

Definition proper_cut_F (GF : gfexec) (cs : list nat) : Prop :=
  proper_cut (gd_g (gf_gd GF)) cs ∧ dclosed cs (gf_dev GF).

Theorem gf_hull_events_lt GF cs :
  proper_cut_F GF cs →
  (length (gevs' (gd_g (gf_gd (gf_hull GF cs))))
   < length (gevs' (gd_g (gf_gd GF))))%nat.
Proof. intros [Hpc _]. by apply hull_events_lt. Qed.

Definition cycle_kill_F (boot : agent → pexv6) (d0 : dev_state)
    (fab : nat → dev_state) : Prop :=
  ∀ GF : gfexec,
    gfexec_consistent GF →
    gfexec_conf boot d0 fab GF →
    (∀ cs, proper_cut_F GF cs →
           ∀ x, ¬ tc (RacyF (gf_hull GF cs)) x x) →
    ∀ x, tc (RacyF GF) x x → False.

(** ** 4.1 THE FORM THE KILL CONSUMES

    [hull_realizable_of_acyclic]'s composition at a MOVING fabric.  Stated
    for an arbitrary bundle (the hull instance is §4.2) because
    [t2lin_supply_F] wants exactly the same composition at the whole graph.

    *** THE ONE PLACE THE FABRIC ORDER IS NOT FREE. ***  [fconf_supply]'s
    last hypothesis — the trace visits the dev blocks in [gf_dev]'s order —
    is NOT discharged here: it is HANDED BACK as the guard
    [tr_dev_ordered].  §5 is the machine-checked account of why. *)

Definition tr_dev_ordered (GF : gfexec) (c : cand) : Prop :=
  ∀ k s, cd_tr c !! k = Some s →
    (es_ag s, tcnt (es_ag s) (take k (cd_tr c))) ∈ gf_dev GF →
    gf_dev GF !! dcnt GF (cd_tr c) k
      = Some (es_ag s, tcnt (es_ag s) (take k (cd_tr c))).

Theorem fconf_realize (boot : agent → pexv6) (d0 : dev_state)
    (fab : nat → dev_state) (GF : gfexec) (N : nat) :
  gfexec_consistent GF →
  gfexec_conf boot d0 fab GF →
  (∀ x, ¬ tc (RacyF GF) x x) →
  (length (gx_prog (gd_g (gf_gd GF))) ≤ N)%nat →
  ∃ (c : cand) (pi : nat → nat) (GF' : gfexec),
    srvwmo_consistent c ∧
    cd_img c = gx_img (gd_g (gf_gd GF)) ∧
    rows_rel pi (gd_g (gf_gd GF)) (gd_g (gf_gd GF')) ∧
    gf_dev GF' = gf_dev GF ∧
    gfexec_conf boot d0 fab GF' ∧
    (∀ i, (λ s, es_lb s) <$> filter (λ s, es_ag s = i) (cd_tr c)
          = default [] (gx_prog (gd_g (gf_gd GF')) !! i)) ∧
    (tr_dev_ordered GF' c →
     ∃ pst : nat → list pexv6,
       pst 0%nat = boot <$> seq 0 N ∧
       exec_prog_ok' pstep_ev pcls_ev pst
         (λ k, fab (dcnt GF' (cd_tr c) k)) (cand_exec c)).
Proof.
  intros Hc Hconf Hacy HN.
  have Hcons : rvwmo_minus_deps_consistent (gf_gd GF) by apply Hc.
  have HacyD : ∀ x, ¬ tc (RacyD (gf_gd GF)) x x.
  { intros x Hcyc. apply (Hacy x). eapply tc_mono; [|exact Hcyc].
    intros a b Hab. by left. }
  destruct (normalize_of_acyclic (gf_gd GF) Hcons
              (λ x y, racyD_dec (gf_gd GF) x y) HacyD)
    as (GD' & pi & Hcons' & H14 & Hrr & Hdeps & _).
  have Hconf' : gfexec_conf boot d0 fab (GFExec GD' (gf_dev GF))
    by (eapply gfexec_conf_ren; [exact Hrr|exact Hdeps|done|exact Hconf]).
  destruct Hcons' as (Hc' & _ & _).
  destruct (rule14_linearization (gd_g GD') Hc' H14)
    as (c & Hsr & Himg & Hrow & _).
  exists c, pi, (GFExec GD' (gf_dev GF)). split_and!.
  - exact Hsr.
  - rewrite Himg. by apply (rows_rel_img pi).
  - exact Hrr.
  - done.
  - exact Hconf'.
  - exact Hrow.
  - intros Hord.
    destruct (fconf_supply c boot d0 fab (GFExec GD' (gf_dev GF)) N
                Hconf' Hrow) as (pst & Hpst0 & _ & Hprg).
    + rewrite /= (rows_rel_nharts pi (gd_g (gf_gd GF)) (gd_g GD') Hrr). lia.
    + exact Hord.
    + by exists pst.
Qed.

(** ** 4.2 The hull instance — [hull_realizable_of_acyclic]'s mirror *)
Theorem hull_realizable_of_acyclic_F (boot : agent → pexv6) (d0 : dev_state)
    (fab : nat → dev_state) (GF : gfexec) (cs : list nat) (N : nat) :
  gfexec_consistent GF →
  gfexec_conf boot d0 fab GF →
  proper_cut_F GF cs →
  (∀ x, ¬ tc (RacyF (gf_hull GF cs)) x x) →
  (length (gx_prog (gd_g (gf_gd GF))) ≤ N)%nat →
  ∃ (c : cand) (pi : nat → nat) (GF' : gfexec),
    srvwmo_consistent c ∧
    cd_img c = gx_img (gd_g (gf_gd GF)) ∧
    gf_dev GF' = gf_dev (gf_hull GF cs) ∧
    gfexec_conf boot d0 fab GF' ∧
    (∀ i, (λ s, es_lb s) <$> filter (λ s, es_ag s = i) (cd_tr c)
          = lbl_ren pi
              <$> default [] (gx_prog (gx_hull (gd_g (gf_gd GF)) cs) !! i)) ∧
    (tr_dev_ordered GF' c →
     ∃ pst : nat → list pexv6,
       pst 0%nat = boot <$> seq 0 N ∧
       exec_prog_ok' pstep_ev pcls_ev pst
         (λ k, fab (dcnt GF' (cd_tr c) k)) (cand_exec c)).
Proof.
  intros Hc Hconf Hpc Hacy HN.
  have Hok : hull_ok (gd_g (gf_gd GF)) cs := proper_cut_ok _ _ (proj1 Hpc).
  have Hch : gfexec_consistent (gf_hull GF cs)
    by (apply gf_hull_consistent; [done|done|apply Hpc]).
  have Hcnf : gfexec_conf boot d0 fab (gf_hull GF cs)
    by (apply gfexec_conf_hull; [done|apply Hpc|done|done]).
  have HNh : (length (gx_prog (gd_g (gf_gd (gf_hull GF cs)))) ≤ N)%nat.
  { change (gx_prog (gd_g (gf_gd (gf_hull GF cs))))
      with (gx_prog (gx_hull (gd_g (gf_gd GF)) cs)).
    pose proof (gxh_nharts (gd_g (gf_gd GF)) cs). lia. }
  destruct (fconf_realize boot d0 fab (gf_hull GF cs) N Hch Hcnf Hacy HNh)
    as (c & pi & GF' & Hsr & Himg & Hrr & Hdev & Hconf' & Hrow & Hsup).
  exists c, pi, GF'. split_and!; [done| |done|done| |done].
  - rewrite Himg. change (gd_g (gf_gd (gf_hull GF cs)))
      with (gx_hull (gd_g (gf_gd GF)) cs). apply gxh_img.
  - intros i. rewrite (Hrow i).
    destruct Hrr as (_ & Hp & _). rewrite Hp list_lookup_fmap.
    change (gx_prog (gd_g (gf_gd (gf_hull GF cs))))
      with (gx_prog (gx_hull (gd_g (gf_gd GF)) cs)).
    by destruct (gx_prog (gx_hull (gd_g (gf_gd GF)) cs) !! i).
Qed.

(** ** 4.3 THE INDUCTION *)
Lemma t2lin_aux_F (boot : agent → pexv6) (d0 : dev_state)
    (fab : nat → dev_state) :
  cycle_kill_F boot d0 fab →
  ∀ (n : nat) (GF : gfexec),
    (length (gevs' (gd_g (gf_gd GF))) ≤ n)%nat →
    gfexec_consistent GF →
    gfexec_conf boot d0 fab GF →
    ∀ x, ¬ tc (RacyF GF) x x.
Proof.
  intros Hk n. induction n as [|n IH]; intros GF Hlen Hcons Hconf x Hcyc.
  - eapply (Hk GF Hcons Hconf); [|exact Hcyc].
    intros cs Hpc y Hcy. pose proof (gf_hull_events_lt GF cs Hpc). lia.
  - eapply (Hk GF Hcons Hconf); [|exact Hcyc].
    intros cs Hpc. apply (IH (gf_hull GF cs)).
    + pose proof (gf_hull_events_lt GF cs Hpc). lia.
    + apply gf_hull_consistent;
        [done|apply (proper_cut_ok _ _ (proj1 Hpc))|apply Hpc].
    + apply gfexec_conf_hull;
        [done|apply Hpc|apply (proper_cut_ok _ _ (proj1 Hpc))|done].
Qed.

Theorem t2lin_of_cycle_kill_F (boot : agent → pexv6) (d0 : dev_state)
    (fab : nat → dev_state) :
  cycle_kill_F boot d0 fab →
  ∀ GF : gfexec,
    gfexec_consistent GF →
    gfexec_conf boot d0 fab GF →
    ∀ x, ¬ tc (RacyF GF) x x.
Proof.
  intros Hk GF.
  by eapply (t2lin_aux_F boot d0 fab Hk (length (gevs' (gd_g (gf_gd GF))))).
Qed.

(** ** 4.4 THE COROLLARY: the whole graph is realized (modulo the guard) *)
Theorem t2lin_supply_F (boot : agent → pexv6) (d0 : dev_state)
    (fab : nat → dev_state) (GF : gfexec) (N : nat) :
  cycle_kill_F boot d0 fab →
  gfexec_consistent GF →
  gfexec_conf boot d0 fab GF →
  (length (gx_prog (gd_g (gf_gd GF))) ≤ N)%nat →
  ∃ (c : cand) (pi : nat → nat) (GF' : gfexec),
    srvwmo_consistent c ∧
    cd_img c = gx_img (gd_g (gf_gd GF)) ∧
    gf_dev GF' = gf_dev GF ∧
    gfexec_conf boot d0 fab GF' ∧
    (tr_dev_ordered GF' c →
     ∃ pst : nat → list pexv6,
       pst 0%nat = boot <$> seq 0 N ∧
       exec_prog_ok' pstep_ev pcls_ev pst
         (λ k, fab (dcnt GF' (cd_tr c) k)) (cand_exec c)).
Proof.
  intros Hk Hcons Hconf HN.
  destruct (fconf_realize boot d0 fab GF N Hcons Hconf
              (t2lin_of_cycle_kill_F boot d0 fab Hk GF Hcons Hconf) HN)
    as (c & pi & GF' & Hsr & Himg & _ & Hdev & Hconf' & _ & Hsup).
  by exists c, pi, GF'.
Qed.

(* ====================================================================== *)
(** * 5. *** THE DEV-ORDER FINDING ***

    [fconf_supply] needs the trace to visit the dev blocks in [gf_dev]'s
    order.  The T2-1c linearization ([WeakRvwmoLin.lin_cand]) does NOT
    provide that, and the reason is structural: its trace is
    [rblocks (grank G) (gevs G) _] — the events GROUPED BY RANK, where
    [grank e] is the write index ([gwix]) of the PO-NEXT WRITE at or after
    [e] IN [e]'S OWN HART (and a per-hart tail slot when there is none).
    So the trace order is:

      - inside a hart, po order ([glin_po_lt]) — fine;
      - between harts, RANK order ([glin_rank_lt]) — which for two WRITES
        IS gmo order ([glin_gmo_writes] below, the positive fragment), but
        for anything else is the gmo order of OTHER events (the po-next
        writes), or the hart index for the tails.

    A dev block hangs off an arbitrary row event — an MMIO load is the
    typical one — so [gf_dev]'s order is NOT recovered.  §5.2 exhibits it. *)

(** ** 5.1 THE POSITIVE FRAGMENT: two WRITES do come out in gmo order *)
Theorem glin_gmo_writes G w1 w2 k1 k2 :
  gwf G →
  glin_eids G !! k1 = Some w1 → glin_eids G !! k2 = Some w2 →
  w1 ∈ gwrites G → w2 ∈ gwrites G →
  gmo_lt G w1 w2 → (k1 < k2)%nat.
Proof.
  intros Hwf H1 H2 Hw1 Hw2 (_ & _ & Hpos).
  eapply glin_rank_lt; [exact H1|exact H2|].
  rewrite (grank_write G Hwf w1 Hw1) (grank_write G Hwf w2 Hw2).
  apply (gwix_gpos_lt G w1 w2); [by destruct Hwf as (? & _ & _)|done|done|done].
Qed.

(** ** 5.2 THE COUNTEREXAMPLE, on the landed LB witness

    [lbg]'s gmo is [(0,1) (1,1) (0,0) (1,0)] — both stores, then both loads
    — while its linearization's trace is [(0,0) (0,1) (1,0) (1,1)]: hart 0
    entire, then hart 1, because each load's rank is its OWN hart's store's
    write index.  So the CROSS-HART gmo pair [(1,1) → (0,0)] comes out
    REVERSED, and a fabric order that names exactly those two events —
    which the model clause [gdev_adj → gmo_lt] ACCEPTS — is not the order
    the trace realizes. *)

Definition lbf : gfexec := GFExec lbgd [(1%nat, 1%nat); (0%nat, 0%nat)].

Lemma lbg_gmo_lt_cross : gmo_lt lbg (1%nat, 1%nat) (0%nat, 0%nat).
Proof.
  split_and!.
  - apply elem_of_list_further, elem_of_list_here.
  - apply elem_of_list_further, elem_of_list_further, elem_of_list_here.
  - by vm_compute.
Qed.

(** The bundle's MODEL clause is satisfied: the fabric order is gmo-ordered. *)
Theorem lbf_consistent : gfexec_consistent lbf.
Proof.
  split; [exact lb_graph_deps_consistent|].
  intros a b (n & Ha & Hb).
  destruct n as [|[|n]]; simpl in Ha, Hb; simplify_eq.
  exact lbg_gmo_lt_cross.
Qed.

(** THE TRACE DOES NOT REALIZE IT. *)
Theorem lbf_not_dev_ordered : ¬ tr_dev_ordered lbf (lin_cand lbg).
Proof.
  intros H.
  have Hs : cd_tr (lin_cand lbg) !! 0%nat
            = Some (glin_step lbg (0%nat, 0%nat)) by reflexivity.
  have Hin : (es_ag (glin_step lbg (0%nat, 0%nat)),
              tcnt (es_ag (glin_step lbg (0%nat, 0%nat)))
                   (take 0%nat (cd_tr (lin_cand lbg)))) ∈ gf_dev lbf.
  { apply elem_of_list_further, elem_of_list_here. }
  pose proof (H 0%nat _ Hs Hin) as Heq. vm_compute in Heq. discriminate.
Qed.

(** … and in the general form: [lin_cand]'s trace REVERSES a cross-hart
    gmo pair.  (Which is not a bug: RVWMO⁻'s gmo is not a trace order —
    only its ppo/rf/co/fr fragments are, and T2-1c's segment construction
    respects exactly those.  It is precisely the fabric order, an EXTRA
    total order on a set of events of mixed kind, that it cannot carry.) *)
Theorem lin_cross_hart_gmo_reversed :
  ∃ (G : gexec) (x y : geid) (kx ky : nat),
    gmo_lt G x y ∧ x.1 ≠ y.1 ∧
    glin_eids G !! kx = Some x ∧ glin_eids G !! ky = Some y ∧ (ky < kx)%nat.
Proof.
  exists lbg, (1%nat, 1%nat), (0%nat, 0%nat), 3%nat, 0%nat.
  split_and!; [exact lbg_gmo_lt_cross|done|by vm_compute|by vm_compute|lia].
Qed.

(* ====================================================================== *)
(** * 6. NON-VACUITY: THE TWO SKELETONS ARE THE SAME SKELETON

    B1b-1's bundle embeds with [gf_dev = []] ([gfexec_conf_of_qconf]), and
    at an empty fabric order [RacyF] IS [RacyD], [gf_hull] IS [gd_hull] and
    [proper_cut_F] IS [proper_cut] — so the fabric kill obligation SUBSUMES
    the quiescent one. *)
Theorem cycle_kill_of_F (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) :
  cycle_kill_F boot d0 (λ _, d0) → cycle_kill boot d0 im nh.
Proof.
  intros HkF GD Hcons Hq Hhull x Hcyc.
  have Hc : gfexec_consistent (GFExec GD []).
  { split; [exact Hcons|]. intros a b (n & Ha & _).
    by rewrite lookup_nil in Ha. }
  eapply (HkF (GFExec GD []) Hc (gfexec_conf_of_qconf boot d0 im nh GD Hq)).
  - intros cs [Hpc _] y Hcy. apply (Hhull cs Hpc y).
    eapply tc_mono; [|exact Hcy].
    intros a b [Hab|(n & Ha & _)]; [exact Hab|by rewrite lookup_nil in Ha].
  - eapply tc_mono; [|exact Hcyc]. intros a b Hab. by left.
Qed.

(* ====================================================================== *)
(** * 7. THE AUDIT *)

Print Assumptions hemitf_ren.
Print Assumptions hemitf_prefix.
Print Assumptions hart_conff_prefix.
Print Assumptions gfexec_conf_ren.
Print Assumptions gfexec_conf_hull.
Print Assumptions gf_hull_events_lt.
Print Assumptions fconf_realize.
Print Assumptions hull_realizable_of_acyclic_F.
Print Assumptions t2lin_of_cycle_kill_F.
Print Assumptions t2lin_supply_F.
Print Assumptions glin_gmo_writes.
Print Assumptions lbf_consistent.
Print Assumptions lbf_not_dev_ordered.
Print Assumptions lin_cross_hart_gmo_reversed.
Print Assumptions cycle_kill_of_F.
