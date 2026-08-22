(** * WeakRvwmoGlue2.v — THE THREE RESIDUAL PREMISES OF [WeakRvwmoGlue]

    Design: [claude-notes/design/weak-memory-route-b.md] §4d.2 and the
    SEVENTH-PASS checkpoint item 1 of
    [claude-notes/projects/weak-memory-certification.md].

    [WeakRvwmoGlue] §9 leaves four premises open: (G-1) the L2′ per-site
    claim (the project's remaining CONTENT, untouched here), and three
    pieces of bookkeeping — (G-2) [cut_supply], (G-3) [cert_supply],
    (G-4) [boot_tie].  This leaf discharges (G-2) and (G-4) outright and
    reduces (G-3) to a single named supply, then restates the glue's
    theorem with the premise list that remains.

      §1  (G-4) THE IMAGE CLAUSE, discharged.  [WeakRvwmoSupply.
          gdexec_qconf] now carries the boot tie itself (the graph's image
          IS the booted image, its hart count is at most the booted
          program-state list's length), so [boot_tie]'s third conjunct is
          free: [boot_tie_of_qconf].

      §2  (G-2) [cut_supply], discharged — and the FINDING that goes with
          it.  The glue's [cut_supply] asks only for SOME [cut_ok] cut, and
          the ZERO CUT is one, at every graph with an event.  The
          write-closed causal past §4d.2(1) describes is therefore NOT
          needed by the interface as landed; §2.4 records precisely why the
          intended cut cannot be shown [proper_cut] in general, so that the
          choice is a recorded design decision rather than an oversight.

      §3  (G-3) [cert_supply], reduced.  [WeakRvwmoCert4.cert_cycle]
          consumes a [segs_run] and produces addressability; it produces NO
          [log_of], so it cannot by itself deliver [cert_supply].  What IS
          composable is landed here: the (P-1) bookkeeping
          ([ctrace_prefix_snoc], [cpol_ctx_snoc], [cpol_Hpres] — the
          [Ctx := cpol_ctx G W x] instantiation, (O-C)), the
          [cyc_state → run_data] bridge, and [cert_supply_of_walk], which
          turns a walk supply into [cert_supply] verbatim.  §3.5 states the
          MINIMAL ORDER CONDITION (O-A) exactly.

      §4  THE THEOREM: [cycle_kill_of_l2''] and [t2lin_of_l2''], with the
          premise list that actually remains.

      §5  NON-VACUITY, §6 the audit, §7 the ledger.

    Nothing below is [Admitted] or [Axiom]-ed.  A LEAF: nothing imports
    this file. *)
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
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre adequacy.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import RiscvLang.
Require Import RiscvAdequacy.
Require Import WeakRobust.
Require Import WeakRobustMain.
Require Import WeakLang.
Require Import WeakEvCapstone.
Require Import WeakEvAdequacy.
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
Require Import WeakRvwmoProbeK1.
Require Import WeakRvwmoLinInd.
Require Import WeakGhost.
Require Import WeakRvwmoLock.
Require Import WeakRvwmoCert.
Require Import WeakRvwmoFloor.
Require Import WeakRvwmoCert2.
Require Import WeakRvwmoCert3.
Require Import WeakRvwmoCert4.
Require Import WeakRvwmoKillArms.
Require Import WeakRvwmoGlue.

(* ====================================================================== *)
(** * 1. (G-4) THE IMAGE CLAUSE

    [WeakRvwmoSupply.gdexec_qconf] is now parameterized by the booted image
    [im] and the booted hart count [nh] and carries

      [gx_img (gd_g GD) = im]  ∧  [length (gx_prog (gd_g GD)) ≤ nh]

    beside its per-hart emission clause.  Both are free at every producer:
    [gx_hull] keeps the image verbatim and its row list is a [zip_with], so
    the hart count cannot grow; [rows_rel] keeps both exactly
    ([gdexec_qconf_hull], [gdexec_qconf_ren]).  Instantiated at the booted
    state, [WeakRvwmoGlue.boot_tie]'s third conjunct is then a projection. *)

Theorem boot_tie_of_qconf (boot : agent → pexv6) (d0 : dev_state) (N : nat)
    (σ0 : wgstate) :
  boot <$> seq 0 N = eps_init σ0 →
  d0 = wgdev σ0 →
  boot_tie boot d0 (img_z (wgimg σ0)) N N σ0.
Proof.
  intros H1 H2. split_and!; [exact H1|exact H2|].
  intros GD Hq. split.
  - exact (gdexec_qconf_img _ _ _ _ _ Hq).
  - exact (gdexec_qconf_nharts _ _ _ _ _ Hq).
Qed.

(** … so the glue's theorem loses the premise entirely. *)
Theorem cycle_kill_of_l2' (Σ : gFunctors) `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (Nm : Z → Z → namespace) (P : Z → Z → Prop)
    (boot : agent → pexv6) (d0 : dev_state) (N : nat) :
  fresh_era gen σ0 →
  boot <$> seq 0 N = eps_init σ0 →
  d0 = wgdev σ0 →
  wp_package Σ gen σ0 D →
  (∀ a base, P a base → wp_package_prot Σ gen σ0 D (Nm a base) a base) →
  cut_supply boot d0 (img_z (wgimg σ0)) N →
  cert_supply boot d0 (img_z (wgimg σ0)) N N →
  l2_claim boot d0 (img_z (wgimg σ0)) N P (bad_run gen σ0) →
  cycle_kill boot d0 (img_z (wgimg σ0)) N.
Proof.
  intros Hfr Hb1 Hb2 Hwp Hwpp Hcut Hcert Hl2.
  eapply (cycle_kill_of_l2 Σ gen σ0 D Nm P boot d0 (img_z (wgimg σ0)) N N);
    [exact Hfr|by apply boot_tie_of_qconf|exact Hwp|exact Hwpp|exact Hcut
    |exact Hcert|exact Hl2].
Qed.

(* ====================================================================== *)
(** * 2. (G-2) [cut_supply]

    [WeakRvwmoGlue.cut_supply] asks, at a graph carrying a cycle, for SOME
    [cs] with [cut_ok (gd_g GD) cs] — i.e. [hull_ok] (po- and rf-closure)
    ∧ [wcut_closed] (gmo-downward closure on writes) ∧ [proper_cut] (it
    drops an event).  It carries NO clause relating [cs] to the cycle: the
    per-segment clause §4d.2(1) describes is not in the statement the glue
    consumes, and the cut's only downstream use is to feed
    [WeakRvwmoGlue.hull_run], whose output candidate [c0] is passed to
    [cert_supply] and used there or not.

    So the honest discharge is the ZERO CUT. *)

(** ** 2.1 The zero cut *)
Definition zcut (G : gexec) : list nat := replicate (length (gx_prog G)) 0%nat.

Lemma zcut_length G : length (zcut G) = length (gx_prog G).
Proof. apply length_replicate. Qed.

Lemma gcut_zcut G e : gcut (zcut G) e = false.
Proof.
  rewrite /gcut /zcut.
  destruct (decide (e.1 < length (gx_prog G))%nat) as [Hlt|Hlt].
  - by rewrite lookup_replicate_2.
  - rewrite (lookup_ge_None_2 (replicate (length (gx_prog G)) 0%nat) e.1) //.
    rewrite length_replicate. lia.
Qed.

Lemma zcut_hull_ok G : hull_ok G (zcut G).
Proof.
  split; [apply zcut_length|].
  intros r a t v w Hc. by rewrite gcut_zcut in Hc.
Qed.

Lemma zcut_wcut_closed G : wcut_closed G (zcut G).
Proof. intros w1 w2 _ _ Hc. by rewrite gcut_zcut in Hc. Qed.

Lemma zcut_proper G i :
  (i < length (gx_prog G))%nat → (0 < nrow G i)%nat → proper_cut G (zcut G).
Proof.
  intros Hi Hn. split; [apply zcut_hull_ok|].
  exists i. by rewrite /zcut lookup_replicate_2.
Qed.

Theorem zcut_cut_ok G i :
  (i < length (gx_prog G))%nat → (0 < nrow G i)%nat → cut_ok G (zcut G).
Proof.
  intros Hi Hn. split_and!;
    [apply zcut_hull_ok|apply zcut_wcut_closed|by eapply zcut_proper].
Qed.

(** The hull at the zero cut is the EMPTY program: every row is dropped. *)
Lemma zcut_hull_rows G i :
  default [] (gx_prog (gx_hull G (zcut G)) !! i) = [].
Proof.
  rewrite gxh_row.
  destruct (decide (i < length (gx_prog G))%nat) as [Hi|Hi].
  - by rewrite /zcut lookup_replicate_2.
  - rewrite /zcut (lookup_ge_None_2 (replicate (length (gx_prog G)) 0%nat) i) //.
    rewrite length_replicate. lia.
Qed.

(** ** 2.2 A cycle names an event, hence a nonempty row *)
Lemma glbl_nrow G e l :
  gx_lbl G e = Some l →
  (e.1 < length (gx_prog G))%nat ∧ (e.2 < nrow G e.1)%nat.
Proof.
  rewrite /gx_lbl /nrow.
  destruct (gx_prog G !! e.1) as [p|] eqn:Hp; simpl; [|done].
  intros Hl. split; by eapply lookup_lt_Some.
Qed.

Lemma cycle_has_event GD z ss :
  rvwmo_minus_consistent (gd_g GD) →
  ss ≠ [] → raw_chain GD z z ss →
  ∃ i, (i < length (gx_prog (gd_g GD)))%nat ∧ (0 < nrow (gd_g GD) i)%nat.
Proof.
  intros Hcons Hne Hch. destruct ss as [|s ss]; [by destruct Hne|].
  destruct Hch as (Hx & _ & _).
  have Hmo : gmo_lt (gd_g GD) z (sg_entry s) := gcross_gmo _ _ _ Hcons Hx.
  destruct Hmo as (_ & Hin & _).
  destruct Hcons as ((_ & Hmem & _) & _).
  destruct (proj1 (Hmem (sg_entry s)) Hin) as (l & Hl & _).
  destruct (glbl_nrow (gd_g GD) (sg_entry s) l Hl) as (H1 & H2).
  exists (sg_entry s).1. split; [exact H1|lia].
Qed.

(** ** 2.3 (G-2), DISCHARGED *)
Theorem cut_supply_of_cycle (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) :
  cut_supply boot d0 im nh.
Proof.
  intros GD z ss Hcons Hq Hne Hch.
  destruct (cycle_has_event GD z ss (proj1 Hcons) Hne Hch) as (i & Hi & Hn).
  exists (zcut (gd_g GD)). by eapply zcut_cut_ok.
Qed.

(** ** 2.4 THE FINDING: why the INTENDED cut is not the one that lands

    §4d.2(1)'s cut is the write-closed CAUSAL PAST of the cycle's event set
    [K]: per hart, the prefix strictly below that hart's segment entry,
    closed under (i) po-prefixes, (ii) rf-sources ([hull_ok]) and (iii)
    gmo-predecessors of kept writes ([wcut_closed]).  The closure exists —
    it is the least fixpoint of three monotone operators on the cut vector,
    bounded by the full cut, so it is reached in at most [length (gevs' G)]
    iterations.  What CANNOT be proved in general is that it stays PROPER,
    and the obstruction is exact:

      the closure may climb ABOVE a segment entry.  Let [r] be a read of
      hart [i] at a row position strictly below hart [i]'s entry, reading
      from a write [w] of hart [j] at a position at or above hart [j]'s
      entry.  Rule (ii) then forces [w] into the cut, rule (i) forces
      hart [j]'s whole prefix through [w] — including hart [j]'s entry —
      and the induction's "the cut drops the cycle" intuition is gone.

      NO CYCLE ARGUMENT BLOCKS THE SHAPE.  One would want [r <po entry_i]
      to give an [RacyD] edge [r → entry_i], closing a cycle through
      [entry_j →po* w →rf r].  It does not: [RacyD]'s po arm is [gpow], po
      into a WRITE (rule 14 is exactly what a causal cycle may violate), so
      po into the READ [entry_i] carries no edge at all.  The shape is
      therefore constructible, and "the closure stays below the entries" is
      FALSE as a general lemma — it is a per-cycle fact about which entry
      one seeds from.

    Since [cut_ok] asks only for properness — DROP ONE EVENT — and never
    for any relation to [K], the zero cut discharges the interface and the
    closure buys nothing at it.  The moment a consumer needs the cut to
    CONTAIN the cycle's causal past (which is what would make
    [WeakRvwmoGlue.hull_run]'s [c0] a useful starting configuration for
    (G-3) rather than a formality), the properness obligation comes back
    and has to be discharged per cycle — by seeding at the gmo-MINIMAL
    backward exit and arguing that the closure of that seed misses the
    gmo-maximal write of the cycle.  That argument is not attempted here;
    it is stated in §7 as the residue of (G-2). *)

(* ====================================================================== *)
(** * 3. (G-3) [cert_supply]

    THE FINDING FIRST, because it decides the shape of everything below.
    [WeakRvwmoCert4.cert_cycle] takes a [segs_run] AS INPUT and returns
    (a) that its endpoint is a real promise-free run at the quiet fabric
    and (b)–(d) that every segment is addressable inside the final
    candidate.  It returns NOTHING about the candidate's LOG.  But
    [WeakRvwmoGlue.cert_supply]'s conclusion is
    [log_of (gd_g GD) (cd_log c (length (cd_tr c)))] — "the certified
    candidate's log IS the graph's whole write list".  So [cert_supply] is
    not a corollary of [cert_cycle]: composing them still owes the WALK
    itself (the per-segment [cert_segment'] applications) and the full-log
    fact.  What this section lands is everything on the road that is
    composable, and one named residue.

    §3.1  (P-1) [Hpres] for [Ctx := cpol_ctx G W x] — the [ctrace_prefix]
          bookkeeping under [cand_snoc], the twin of
          [WeakRvwmoFloor.gtrace_prefix_snoc] with the witness set.  This
          is (O-C)'s hard half and it is DISCHARGED, modulo one honest
          premise per step that only the read POLICY can supply
          ([cstep_cls], §3.1: the appended label is either [G]'s own at a
          non-witness position or the candidate's latest-source read at a
          witness one).  That premise is not bookkeeping and could not be:
          [Hpres] sees only [lbl_reidx lb lb'], which is precisely the
          relation that ALLOWS the read indices to differ.

    §3.2  the [cyc_state] → [run_data] bridge;
    §3.3  [cert_supply_of_walk] — [cert_supply] from a walk supply;
    §3.4  (O-A) THE MINIMAL ORDER CONDITION, stated exactly. *)

(** ** 3.1 (P-1): [ctrace_prefix] extends by one certified step *)

(** THE STEP CLASSIFICATION.  Exactly [ctrace_prefix]'s [ctp_step]
    disjunction, read at the position the snoc appends to. *)
Definition cstep_cls (G : gexec) (W : geid → Prop) (x : agent) (c : cand)
    (l : lbl) : Prop :=
  (¬ W (x, gcnt x (cd_tr c)) ∧ gx_lbl G (x, gcnt x (cd_tr c)) = Some l) ∨
  (W (x, gcnt x (cd_tr c)) ∧
   ∃ (base : Z) (n : nat) (ts0 : list nat) (vs0 : list (bv 8)),
     gx_lbl G (x, gcnt x (cd_tr c))
       = Some (WeakAxiomatic.LLoad false base ts0 vs0) ∧
     length ts0 = n ∧ l = latest_read_lbl c false base n).

Lemma latest_read_lbl_congr (c1 c2 : cand) (aq : bool) (base : Z) (n : nat) :
  cd_img c1 = cd_img c2 → cd_log_end c1 = cd_log_end c2 →
  latest_read_lbl c1 aq base n = latest_read_lbl c2 aq base n.
Proof. intros H1 H2. by rewrite /latest_read_lbl /lrd_ts /lrd_vs H1 H2. Qed.

Lemma latest_read_not_w c aq base n : lb_is_w (latest_read_lbl c aq base n) = false.
Proof. reflexivity. Qed.

Lemma cd_pre_snoc_img c s :
  cd_img (cd_pre (cand_snoc c s) (length (cd_tr c))) = cd_img c.
Proof. by rewrite cd_pre_img cand_snoc_img. Qed.

Lemma cd_pre_snoc_log c s :
  cd_log_end (cd_pre (cand_snoc c s) (length (cd_tr c))) = cd_log_end c.
Proof.
  by rewrite cd_pre_log (cand_snoc_log c s (length (cd_tr c)) (Nat.le_refl _)).
Qed.

Theorem ctrace_prefix_snoc G c ev W (x : agent) (l : lbl) :
  gwf G →
  ctrace_prefix G c ev W →
  cstep_cls G W x c l →
  (lb_is_w l = true →
     gwix G (x, gcnt x (cd_tr c)) = S (length (cd_log_end c))) →
  ctrace_prefix G (cand_snoc c (EStep x l))
    (ev_snoc c ev (x, gcnt x (cd_tr c))) W.
Proof.
  intros Hwf Hgt Hcls Hix.
  have Hte : take (length (cd_tr c)) (cd_tr c) = cd_tr c
    by (apply take_ge; lia).
  (* [G]'s label at the appended position, in the NON-witness case *)
  have Hlbl_ev : ¬ W (x, gcnt x (cd_tr c)) →
                 gx_lbl G (x, gcnt x (cd_tr c)) = Some l.
  { intros HnW. destruct Hcls as [[_ H]|[HW _]]; [exact H|by destruct (HnW HW)]. }
  (* a WITNESS label is a load, so an appended WRITE is never a witness *)
  have Hw_notW : lb_is_w l = true → ¬ W (x, gcnt x (cd_tr c)).
  { intros Hw HW. destruct Hcls as [[HnW _]|[_ (base & n & ts0 & vs0 & _ & _ & ->)]];
      [by destruct (HnW HW)|by rewrite latest_read_not_w in Hw]. }
  destruct Hgt as [Himg Hag Hpos Hstep Hwix Hlog].
  have Hlt : ∀ p s, cd_tr (cand_snoc c (EStep x l)) !! p = Some s →
    (p < length (cd_tr c))%nat →
    cd_tr c !! p = Some s ∧ ev_snoc c ev (x, gcnt x (cd_tr c)) p = ev p ∧
    take p (cd_tr (cand_snoc c (EStep x l))) = take p (cd_tr c) ∧
    cd_log (cand_snoc c (EStep x l)) p = cd_log c p ∧
    cd_pre (cand_snoc c (EStep x l)) p = cd_pre c p.
  { intros p s Hs Hp. rewrite cand_snoc_tr_lt // in Hs.
    have Htk : take p (cd_tr (cand_snoc c (EStep x l))) = take p (cd_tr c)
      by (rewrite /= take_app_le //; lia).
    split_and!; [exact Hs|by apply ev_snoc_lt|exact Htk
      |apply cand_snoc_log; rewrite /cd_end; lia|].
    rewrite /cd_pre cand_snoc_img. by rewrite Htk. }
  have Hend : ∀ p s, cd_tr (cand_snoc c (EStep x l)) !! p = Some s →
    ¬ (p < length (cd_tr c))%nat → p = length (cd_tr c) ∧ s = EStep x l.
  { intros p s Hs Hp. pose proof (lookup_lt_Some _ _ _ Hs) as Hb.
    rewrite cand_snoc_tr length_app /= in Hb.
    have Hpe : p = length (cd_tr c) by lia. subst p.
    split; [done|]. move: Hs. rewrite cand_snoc_tr
      (lookup_app_r (cd_tr c) [EStep x l] (length (cd_tr c)) (Nat.le_refl _))
      Nat.sub_diag /=. by intros [= <-]. }
  split.
  - by rewrite cand_snoc_img.
  - intros p s Hs. destruct (decide (p < length (cd_tr c))%nat) as [Hp|Hp].
    + destruct (Hlt p s Hs Hp) as (Hs' & Hev & _ & _ & _). rewrite Hev. by apply Hag.
    + destruct (Hend p s Hs Hp) as (-> & ->). by rewrite ev_snoc_end.
  - intros p s Hs. destruct (decide (p < length (cd_tr c))%nat) as [Hp|Hp].
    + destruct (Hlt p s Hs Hp) as (Hs' & Hev & Htk & _ & _).
      rewrite Hev Htk. by apply Hpos.
    + destruct (Hend p s Hs Hp) as (-> & ->).
      rewrite ev_snoc_end /= take_app_le // Hte //.
  - intros p s Hs. destruct (decide (p < length (cd_tr c))%nat) as [Hp|Hp].
    + destruct (Hlt p s Hs Hp) as (Hs' & Hev & _ & _ & Hpre).
      rewrite Hev Hpre. by apply Hstep.
    + destruct (Hend p s Hs Hp) as (-> & ->). rewrite ev_snoc_end.
      destruct Hcls as [[HnW Hl]|[HW (base & n & ts0 & vs0 & Hl & Hn & Hleq)]].
      * left. by split.
      * right. split; [exact HW|].
        exists base, n, ts0, vs0. split_and!; [exact Hl|exact Hn|].
        rewrite /= Hleq. apply latest_read_lbl_congr;
          [by rewrite cd_pre_snoc_img|by rewrite cd_pre_snoc_log].
  - intros p s Hs Hw. destruct (decide (p < length (cd_tr c))%nat) as [Hp|Hp].
    + destruct (Hlt p s Hs Hp) as (Hs' & Hev & _ & Hlg & _).
      rewrite Hev Hlg. by apply (Hwix p s Hs' Hw).
    + destruct (Hend p s Hs Hp) as (-> & ->). rewrite ev_snoc_end.
      rewrite (cand_snoc_log c (EStep x l) (length (cd_tr c)) (Nat.le_refl _)).
      by apply Hix.
  - intros t Ht Hle.
    have Hlen : length (cd_tr (cand_snoc c (EStep x l)))
              = S (length (cd_tr c)) by rewrite /= length_app /=; lia.
    have Hlg : cd_log (cand_snoc c (EStep x l))
                 (length (cd_tr (cand_snoc c (EStep x l))))
             = cd_log_end c ++ es_msg (EStep x l).
    { rewrite -(cd_log_end_snoc c (EStep x l)) /cd_log_end /cd_end Hlen //. }
    rewrite Hlg. rewrite Hlg in Hle.
    destruct (decide (t ≤ length (cd_log_end c))%nat) as [Hin|Hin].
    + destruct (Hlog t Ht ltac:(rewrite /cd_log_end /cd_end in Hin; exact Hin))
        as (w & Hw & Heq).
      exists w. split; [exact Hw|]. rewrite lookup_app_l; [|lia].
      rewrite -Heq /cd_log_end /cd_end //.
    + rewrite length_app in Hle.
      have Hwl : lb_is_w l = true.
      { destruct (lb_wr l) as [[base vs]|] eqn:Hwr.
        - by destruct l; simplify_eq/=.
        - exfalso. rewrite /es_msg /= Hwr /= in Hle. lia. }
      have Hl : gx_lbl G (x, gcnt x (cd_tr c)) = Some l
        := Hlbl_ev (Hw_notW Hwl).
      destruct (lb_is_w_wr l Hwl) as (base & vs & Hwr).
      have Hmsg : es_msg (EStep x l) = [WMsg base vs (Some x) (lb_cls l)]
        by rewrite /es_msg /= Hwr.
      rewrite Hmsg /= in Hle.
      have -> : t = S (length (cd_log_end c)) by lia.
      have Hgw : (x, gcnt x (cd_tr c)) ∈ gwrites G.
      { eapply gis_w_gwrites; [exact Hwf|by exists l|by rewrite /gis_w Hl]. }
      exists (x, gcnt x (cd_tr c)). split.
      * rewrite -(Hix Hwl). by apply gwrite_at_gwix.
      * rewrite Hmsg Nat.sub_succ Nat.sub_0_r.
        rewrite lookup_app_r; [|lia]. rewrite Nat.sub_diag /=.
        by rewrite /gwmsg Hl Hwr.
Qed.

(** The appended step is the certifying hart's, so its own position
    advances by exactly one. *)
Lemma gcnt_cand_snoc_self (c : cand) (x : agent) (l : lbl) :
  gcnt x (cd_tr (cand_snoc c (EStep x l))) = S (gcnt x (cd_tr c)).
Proof.
  rewrite cand_snoc_tr /gcnt list_basics.filter_app length_app /=.
  rewrite (filter_cons_True (λ s, es_ag s = x) (EStep x l) [] eq_refl) /=. lia.
Qed.

(** ** 3.1a [cpol_ctx] is preserved — (O-C)'s context, carried

    The two clauses of [cpol_ctx] beyond [ctrace_prefix] are about the NEXT
    position, and neither is bookkeeping: [wit_fence_ub] is (P-3) and the
    non-witness-ness of the next position is a property of the witness SET
    (its shape is fixed where the cycle fixes it, §4e).  Both enter as
    hypotheses, stated at the position they are about. *)
Theorem cpol_ctx_snoc G W (x : agent) (c : cand) (l : lbl) :
  gwf G →
  cpol_ctx G W x c →
  cstep_cls G W x c l →
  (lb_is_w l = true →
     gwix G (x, gcnt x (cd_tr c)) = S (length (cd_log_end c))) →
  (∀ ev', ctrace_prefix G (cand_snoc c (EStep x l)) ev' W →
     wit_fence_ub G (cand_snoc c (EStep x l)) ev' W
       (x, S (gcnt x (cd_tr c)))) →
  ¬ W (x, S (gcnt x (cd_tr c))) →
  cpol_ctx G W x (cand_snoc c (EStep x l)).
Proof.
  intros Hwf (ev & Hgt & _ & _) Hcls Hix Hub HnW.
  have Hgt' : ctrace_prefix G (cand_snoc c (EStep x l))
                (ev_snoc c ev (x, gcnt x (cd_tr c))) W
    := ctrace_prefix_snoc G c ev W x l Hwf Hgt Hcls Hix.
  exists (ev_snoc c ev (x, gcnt x (cd_tr c))).
  rewrite gcnt_cand_snoc_self. split_and!;
    [exact Hgt'|exact (Hub _ Hgt')|exact HnW].
Qed.

(** ** 3.1b (P-1), in [cert_segment']'s own [Hpres] shape *)
Theorem cpol_Hpres G W (x : agent) (Q : lbl → Prop) :
  gwf G →
  (* the STEP CLASSIFICATION — the read policy's own output, not
     bookkeeping: [lbl_reidx] is exactly the relation that lets the
     appended label's read indices differ from [G]'s *)
  (∀ (c0 : cand) (lb lb' : lbl),
     cpol_ctx G W x c0 → srvwmo_consistent c0 → Q lb → lbl_reidx lb lb' →
     mstep_ok (cand_last_st c0) x lb' →
     cstep_cls G W x c0 lb' ∧
     (lb_is_w lb' = true →
        gwix G (x, gcnt x (cd_tr c0)) = S (length (cd_log_end c0)))) →
  (* (P-3) [wit_fence_ub] at the next position *)
  (∀ (c0 : cand) (lb' : lbl) (ev' : nat → geid),
     ctrace_prefix G (cand_snoc c0 (EStep x lb')) ev' W →
     wit_fence_ub G (cand_snoc c0 (EStep x lb')) ev' W
       (x, S (gcnt x (cd_tr c0)))) →
  (* the witness set does not name the next position *)
  (∀ (c0 : cand), ¬ W (x, S (gcnt x (cd_tr c0)))) →
  ∀ (c0 : cand) (lb lb' : lbl),
    cpol_ctx G W x c0 → srvwmo_consistent c0 → Q lb → lbl_reidx lb lb' →
    mstep_ok (cand_last_st c0) x lb' →
    cpol_ctx G W x (cand_snoc c0 (EStep x lb')).
Proof.
  intros Hwf Hcls Hub HnW c0 lb lb' Hctx Hc HQ Hri Hok.
  destruct (Hcls c0 lb lb' Hctx Hc HQ Hri Hok) as (Hcl & Hix).
  eapply cpol_ctx_snoc;
    [exact Hwf|exact Hctx|exact Hcl|exact Hix|exact (Hub c0 lb')|apply HnW].
Qed.

(** ** 3.2 A certified configuration IS a [run_data] *)
Theorem run_data_of_cyc (boot : agent → pexv6) (d0 : dev_state) (N : nat)
    (G : gexec) (S : cyc_state) :
  cst_ok d0 S →
  cd_img (cst_c S) = gx_img G →
  cst_pst S 0%nat = boot <$> seq 0 N →
  cst_dv S 0%nat = d0 →
  run_data boot d0 N G (cst_c S) (cst_pst S) (cst_dv S).
Proof. intros (Hc & Hpo & _) Himg Hpst Hdv. by split. Qed.

(** ** 3.3 [cert_supply] from a WALK SUPPLY

    The residue, named.  Everything [cert_supply] asks for that
    [cert_cycle] does not deliver: a walk around the cycle whose endpoint
    boots from [boot]/[d0] and whose log is [G]'s whole write list. *)
Definition walk_supply (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) (N : nat) : Prop :=
  ∀ (GD : gdexec) (cs : list nat) (c0 : cand) (pst0 : nat → list pexv6)
    (z : geid) (ss : list seg),
    rvwmo_minus_deps_consistent GD → gdexec_qconf boot d0 im nh GD →
    cut_ok (gd_g GD) cs →
    run_data boot d0 N (gd_g GD) c0 pst0 (λ _, d0) →
    ss ≠ [] → raw_chain GD z z ss →
    ∃ (l : list segout) (S0 Sf : cyc_state),
      segs_run d0 l S0 Sf ∧
      cd_img (cst_c Sf) = gx_img (gd_g GD) ∧
      cst_pst Sf 0%nat = boot <$> seq 0 N ∧
      cst_dv Sf 0%nat = d0 ∧
      log_of (gd_g GD) (cd_log (cst_c Sf) (length (cd_tr (cst_c Sf)))).

Theorem cert_supply_of_walk (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) (N : nat) :
  walk_supply boot d0 im nh N → cert_supply boot d0 im nh N.
Proof.
  intros Hw GD cs c0 pst0 z ss Hcons Hq Hcut Hrd0 Hne Hch.
  destruct (Hw GD cs c0 pst0 z ss Hcons Hq Hcut Hrd0 Hne Hch)
    as (l & S0 & Sf & Hrun & Himg & Hpst & Hdv & Hlog).
  exists (cst_c Sf), (cst_pst Sf), (cst_dv Sf). split; [|exact Hlog].
  apply run_data_of_cyc; [exact (segs_run_ok d0 l S0 Sf Hrun)|done|done|done].
Qed.

(** ** 3.4 (O-A) THE MINIMAL ORDER CONDITION, exactly

    The gmo order is NOT an extra hypothesis one may impose on the walk: it
    is FORCED by the correspondence the certification carries.  A walk
    whose final candidate is a [ctrace_prefix] of [G] has its segments'
    exit writes appended in strictly increasing [gwix] — so a walk that
    visits the cycle's segments in an order whose exits are not gmo-sorted
    simply has no [ctrace_prefix], and [WeakRvwmoCert3.cpol_ctx] (hence the
    floor discharge) is unavailable at it.

    WHAT THAT COSTS THE CYCLE, precisely: nothing.  The kill reads the
    segments through [WeakRvwmoGlue.l2_claim_at], which quantifies
    per-segment ([∀ prev s, s ∈ ss → …]) and reads only the FINAL log
    ([log_of], the whole graph's write list).  So the walk is free to
    process the segments in gmo order of their exits while the CHAIN keeps
    the cycle's own order; the two orders never have to agree.  That is
    (O-A)'s first branch, and it is the cheap one. *)
Theorem walk_exits_gmo_forced (G : gexec) (d0 : dev_state)
    (l : list segout) (S0 Sf : cyc_state) (ev : nat → geid) (W : geid → Prop)
    (o1 o2 : segout) (j1 j2 : nat)
    (rl1 rl2 : bool) (b1 b2 : Z) (vs1 vs2 : list (bv 8)) (k1 k2 : wm_class) :
  segs_run d0 l S0 Sf →
  ctrace_prefix G (cst_c Sf) ev W →
  o1 ∈ l → o2 ∈ l →
  so_row o1 !! j1 = Some (WeakAxiomatic.LStore rl1 b1 vs1 k1) →
  so_row o2 !! j2 = Some (WeakAxiomatic.LStore rl2 b2 vs2 k2) →
  (so_off o1 + j1 < so_off o2 + j2)%nat →
  (gwix G (ev (so_off o1 + j1)%nat) < gwix G (ev (so_off o2 + j2)%nat))%nat.
Proof.
  intros Hrun Hgt Ho1 Ho2 Hj1 Hj2 Hlt.
  destruct (cert_cycle d0 l S0 Sf Hrun) as (_ & _ & _ & _ & Hex & _).
  pose proof (Hex o1 Ho1 j1 rl1 b1 vs1 k1 Hj1) as Hp1.
  pose proof (Hex o2 Ho2 j2 rl2 b2 vs2 k2 Hj2) as Hp2.
  by eapply (ctp_wix_gmo_mono G (cst_c Sf) ev W).
Qed.

(* ====================================================================== *)
(** * 4. THE THEOREM, WITH THE PREMISE LIST THAT REMAINS

    Compared with [WeakRvwmoGlue.cycle_kill_of_l2] this drops [boot_tie]
    (§1) and [cut_supply] (§2) outright, and replaces [cert_supply] by the
    walk supply (§3.3).  What is left, in order:

      (i)   the BOOT PLUMBING — the two equations that say [boot]/[d0] IS
            the state [σ0] boots ([fresh_era] and the two identifications);
            nothing here is a proof obligation about the kernel.

      (ii)  [l2_claim] — (G-1), the L2′ PER-SITE CLASSIFICATION.  The
            project's remaining content; a hypothesis, never an axiom.

      (iii) [walk_supply] — the certification walk.  Its content is exactly
            the per-segment [WeakRvwmoCert3.cert_segment'] applications plus
            the full-log fact, and the debts inside it are named upstream:

            (P-1) [Hpres] at [Ctx := cpol_ctx G W x] — DISCHARGED, §3.1b
                  ([cpol_Hpres]), modulo the step classification the read
                  policy itself supplies.
            (P-3) [wit_fence_ub] — a HYPOTHESIS by design
                  ([WeakRvwmoCert3] §2.1): a witness raises [w_vrOld]
                  byte-agnostically, and that reaches a later read's floor
                  only through a publishing fence, so the obligation is
                  guarded and vacuous at a witness with no such fence.  It
                  enters [cpol_Hpres] as its second premise, stated at the
                  position it is about.
            (P-4) PROGRESS — that a certified remainder REACHES its
                  instruction boundary ([WeakRvwmoCert3] §5,
                  [at_boundary]).  This is the EWPs' content and cannot be
                  a graph-side lemma; it enters wherever
                  [boundary_reconverge] is applied inside the walk.

            Neither (P-3) nor (P-4) can be hoisted ABOVE [walk_supply] as a
            free-standing premise of this theorem: both are quantified over
            the intermediate candidates the walk itself builds, which do not
            exist until the walk does.  They are listed here, at the walk,
            because that is where they are honestly stated.

      (iv)  the WP PACKAGE, in its two flavours — φ (the BAD arm) and F3″
            (the CS-chained arm's export seam). *)
Theorem cycle_kill_of_l2'' (Σ : gFunctors) `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (Nm : Z → Z → namespace) (P : Z → Z → Prop)
    (boot : agent → pexv6) (d0 : dev_state) (N : nat) :
  (* (i) the boot plumbing *)
  fresh_era gen σ0 →
  boot <$> seq 0 N = eps_init σ0 →
  d0 = wgdev σ0 →
  (* (ii) THE L2′ CLAIM *)
  l2_claim boot d0 (img_z (wgimg σ0)) N P (bad_run gen σ0) →
  (* (iii) the certification walk — carrying (P-3) and (P-4) *)
  walk_supply boot d0 (img_z (wgimg σ0)) N N →
  (* (iv) the WP package *)
  wp_package Σ gen σ0 D →
  (∀ a base, P a base → wp_package_prot Σ gen σ0 D (Nm a base) a base) →
  cycle_kill boot d0 (img_z (wgimg σ0)) N.
Proof.
  intros Hfr Hb1 Hb2 Hl2 Hwalk Hwp Hwpp.
  eapply (cycle_kill_of_l2' Σ gen σ0 D Nm P boot d0 N);
    [exact Hfr|exact Hb1|exact Hb2|exact Hwp|exact Hwpp
    |apply cut_supply_of_cycle|by apply cert_supply_of_walk|exact Hl2].
Qed.

(** … and T2-LIN itself, at the same premises. *)
Theorem t2lin_of_l2'' (Σ : gFunctors) `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (Nm : Z → Z → namespace) (P : Z → Z → Prop)
    (boot : agent → pexv6) (d0 : dev_state) (N : nat) :
  fresh_era gen σ0 →
  boot <$> seq 0 N = eps_init σ0 →
  d0 = wgdev σ0 →
  l2_claim boot d0 (img_z (wgimg σ0)) N P (bad_run gen σ0) →
  walk_supply boot d0 (img_z (wgimg σ0)) N N →
  wp_package Σ gen σ0 D →
  (∀ a base, P a base → wp_package_prot Σ gen σ0 D (Nm a base) a base) →
  ∀ GD : gdexec,
    rvwmo_minus_deps_consistent GD →
    gdexec_qconf boot d0 (img_z (wgimg σ0)) N GD →
    ∀ x, ¬ tc (RacyD GD) x x.
Proof.
  intros Hfr Hb1 Hb2 Hl2 Hwalk Hwp Hwpp.
  apply t2lin_of_cycle_kill.
  by eapply (cycle_kill_of_l2'' Σ gen σ0 D Nm P boot d0 N).
Qed.

(* ====================================================================== *)
(** * 5. NON-VACUITY *)

(** The write-closed past of LB's cycle: [lbgd] has a real [RacyD] cycle
    ([WeakRvwmoGlue.lbgd_segments]) and the cut §2 hands back is
    [ [0; 0] ] — it contains NOTHING, and the hull at it is the empty
    program.  That is the honest content of §2.4 in one witness. *)
Theorem lbgd_cut_ok : cut_ok (gd_g lbgd) (zcut (gd_g lbgd)).
Proof.
  destruct lbgd_segments as (z & ss & Hne & Hch).
  destruct (cycle_has_event lbgd z ss (proj1 lb_graph_deps_consistent) Hne Hch)
    as (i & Hi & Hn).
  by eapply zcut_cut_ok.
Qed.

Lemma lbgd_zcut_empty : zcut (gd_g lbgd) = [0%nat; 0%nat].
Proof. reflexivity. Qed.

Lemma lbgd_cut_drops_everything e : gcut (zcut (gd_g lbgd)) e = false.
Proof. apply gcut_zcut. Qed.

Lemma lbgd_hull_empty i : default [] (gx_prog (gx_hull lbg (zcut lbg)) !! i) = [].
Proof. apply zcut_hull_rows. Qed.

(* ====================================================================== *)
(** * 6. AUDIT *)

Print Assumptions boot_tie_of_qconf.
Print Assumptions cycle_kill_of_l2'.
Print Assumptions cut_supply_of_cycle.
Print Assumptions zcut_cut_ok.
Print Assumptions ctrace_prefix_snoc.
Print Assumptions cpol_ctx_snoc.
Print Assumptions cpol_Hpres.
Print Assumptions run_data_of_cyc.
Print Assumptions cert_supply_of_walk.
Print Assumptions walk_exits_gmo_forced.
Print Assumptions cycle_kill_of_l2''.
Print Assumptions t2lin_of_l2''.
Print Assumptions lbgd_cut_ok.

(* ====================================================================== *)
(** * 7. WHAT REMAINS, EXACTLY

    (G-1) [l2_claim] — untouched, and intended: L2′ proper, site class by
          site class, is the project's remaining content.

    (G-2) DISCHARGED at the interface ([cut_supply_of_cycle]).  RESIDUE, and
          it is a residue of the DESIGN, not of the proof: if a later
          consumer needs the cut to carry the cycle's causal past (so that
          [WeakRvwmoGlue.hull_run]'s [c0] is a useful starting configuration
          for the walk rather than a formality), then the closure of §2.4
          has to be built AND shown proper, and §2.4 records why the
          obvious properness argument fails — po into a READ is not an
          [RacyD] arm, so nothing stops the rf-closure of the entries'
          prefixes from climbing above another hart's entry.  The fix, when
          it is needed, is a per-cycle seed (the gmo-minimal backward exit),
          not a general lemma.

    (G-3) REDUCED to [walk_supply] (§3.3).  Landed on the way:
          [ctrace_prefix_snoc] / [cpol_ctx_snoc] / [cpol_Hpres] — (P-1) and
          the [Ctx := cpol_ctx G W x] instantiation, i.e. (O-C)'s hard half;
          [run_data_of_cyc]; [cert_supply_of_walk]; and (O-A) in
          [walk_exits_gmo_forced], which shows the gmo order is FORCED by
          [ctp_wix] and costs the cycle nothing because
          [WeakRvwmoGlue.l2_claim_at] is per-segment and reads only the
          final log.

    (G-4) DISCHARGED ([boot_tie_of_qconf]); the clause now lives in
          [WeakRvwmoSupply.gdexec_qconf] and is free at every producer. *)
