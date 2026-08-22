(** * WeakRvwmoWalk2.v — R-2's residue [walk_seg_data]: the parts that ARE
    supplied by the conformance bundle, and the OBSTRUCTION that stops the
    rest.

    Task: supply [WeakRvwmoProgress.walk_seg_data] from
    [WeakRvwmoSupply.gdexec_qconf].  Three of its four items are delivered
    here; the fourth is REFUTED, and the refutation is the finding.

    §1  THE EMISSION PER STATE (item 1), DELIVERED.  [gdexec_qconf] hands
        out one [hart_conf] emission of hart [x]'s WHOLE row; [hemit_app]
        splits it at the walk's current position [k0] and again after the
        exit write [kz], leaving exactly the [hemit] that [walk_seg_data]
        asks for, at the row fold [row_ws row k0].  §1.4 puts it in the
        residue's own "[pre ++ [store]]" shape.

    §2  THE READ/REGISTER POLICY, POINTWISE (item 2), DELIVERED.  At a
        candidate ALIGNED to the row position the block sits at, the
        log-decided classification discharges every case:
        [cert_read_in_log'] (through [cpol_read], floor free) at a read
        whose sources the log has reached, [cert_write_ok] at the store,
        [cert_fence_ok] at a fence, and [wcls_of_pfx] for the [Cls] output.
        With an EMPTY taint set the register half is [cert_block_mirror].

    §3  THE RMW POLICY (item 3), DELIVERED, in the same pointwise shape
        ([cert_block_pair] + [cert_rmw_ok]); [cpolp_of_rmwfree] is the
        RMW-free instance.

    §4  THE OLD SHAPE'S OBSTRUCTION (item 4).  [WeakRvwmoWalk.wpol_flat] quantifies over
        EVERY candidate the certification context admits, while the
        classification it must deliver is about G's label AT THAT
        CANDIDATE'S OWN POSITION.  The two cannot be reconciled: §4.1
        [wpol_pins_store] shows that a [wpol] carrying the segment's exit
        store forces that store to be [G]'s label at the position of EVERY
        context candidate, and §4.2 [wpol_exit_at_zero] instantiates it at
        the EMPTY candidate (a context candidate of every witness-free
        graph, [cpol_ctx_empty]) — so the exit write would have to be hart
        [x]'s row position 0.  §4.3 [walk_seg_data_refuted] carries that
        all the way: [walk_seg_data] is FALSE at every walk state whose
        segment's exit write is not the hart's first event.  The same
        over-quantification is in [wrow_in_log] (all row positions, not the
        segment's) and in [walk_seg_data]'s own [∀ St] over the too-weak
        [wlk_inv].  §4.4 states the corrected, position-indexed policy
        [wpol_ix] and derives it from §2 — the shape a repaired
        [cert_segment'] would consume.

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
Require Import WeakEvProv.
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
Require Import WeakRvwmoGlue2.
Require Import WeakSrvwmoLitmus.
Require Import WeakSrvwmoCapstone.
Require Import WeakRvwmoCapstone.
Require Import WeakRvwmoWalk.
Require Import WeakRvwmoProgress.
Require Import WeakRvwmoCycWit.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** * 1. THE EMISSION PER STATE, FROM THE CONFORMANCE BUNDLE

    [WeakRvwmoSupply.gdexec_qconf] says: every hart's ROW is
    [hart_conf]-emitted from [boot i] with the constant fabric [λ _, d0].
    [walk_seg_data] asks for the emission of ONE STRETCH of that row — from
    the hart's current walk position [k0] through its next write.  That is
    [hemit_app] applied twice, and nothing else: the emission SPLITS at
    every prefix, the fabric index advancing by the prefix length and the
    [wstate] index by the row fold, which at index [k0] IS [row_ws row k0]
    by definition. *)

(** [qrow] / [qrow_lbl] — hart [x]'s row as a list — now live in
    [WeakRvwmoWalk] §4.5, where the chained walk's invariant needs them. *)

(** ** 1.1 The whole row's emission *)
Theorem qconf_hemit (boot : agent → pexv6) (d0 : dev_state) (im : image)
    (nh : nat) (GD : gdexec) (x : agent) :
  gdexec_qconf boot d0 im nh GD →
  ∃ (es : list eitem) (pfin : pexv6),
    hemit (λ _, d0) 0%nat ws_init (qrow (gd_g GD) x) (boot x) es pfin.
Proof.
  intros Hq. destruct (qconf_rows boot d0 im nh GD x Hq) as (em & Hem).
  by exists (em_items em), (em_fin em).
Qed.

(** ** 1.2 … SPLIT at the walk's current position *)
Lemma hemit_drop (dv : nat → dev_state) (row : list lbl) (k0 : nat)
    (p : pexv6) (es : list eitem) (pfin : pexv6) :
  hemit dv 0%nat ws_init row p es pfin →
  (k0 ≤ length row)%nat →
  ∃ (pm : pexv6) (es2 : list eitem),
    hemit dv k0 (row_ws row k0) (drop k0 row) pm es2 pfin.
Proof.
  intros Hem Hk.
  rewrite -(take_drop k0 row) in Hem.
  destruct (hemit_app dv 0%nat ws_init (take k0 row) (drop k0 row) p es pfin Hem)
    as (pm & es1 & es2 & _ & Hem2 & _).
  exists pm, es2.
  rewrite (length_take_le row k0 Hk) /= in Hem2.
  exact Hem2.
Qed.

(** THE SEGMENT'S EMISSION.  [len] is the stretch's length; the walk takes
    [len = S kz - k0] with [kz] the exit write's row position. *)
Theorem qconf_hemit_seg (boot : agent → pexv6) (d0 : dev_state) (im : image)
    (nh : nat) (GD : gdexec) (x : agent) (k0 len : nat) :
  gdexec_qconf boot d0 im nh GD →
  (k0 ≤ length (qrow (gd_g GD) x))%nat →
  ∃ (p1 p2 : pexv6) (es : list eitem),
    hemit (λ _, d0) k0 (row_ws (qrow (gd_g GD) x) k0)
      (take len (drop k0 (qrow (gd_g GD) x))) p1 es p2.
Proof.
  intros Hq Hk.
  destruct (qconf_hemit boot d0 im nh GD x Hq) as (es & pfin & Hem).
  destruct (hemit_drop (λ _, d0) (qrow (gd_g GD) x) k0 (boot x) es pfin Hem Hk)
    as (pm & es2 & Hem2).
  rewrite -(take_drop len (drop k0 (qrow (gd_g GD) x))) in Hem2.
  destruct (hemit_app (λ _, d0) k0 (row_ws (qrow (gd_g GD) x) k0)
              (take len (drop k0 (qrow (gd_g GD) x)))
              (drop len (drop k0 (qrow (gd_g GD) x))) pm es2 pfin Hem2)
    as (pm2 & es1' & es2' & Hem3 & _ & _).
  by exists pm, pm2, es1'.
Qed.

(** ** 1.3 … in the residue's own "[pre ++ [store]]" shape *)
(** [seg_split_exit] now lives in [WeakRvwmoWalk] §4.6c. *)

Lemma seg_pre_nonwrite (G : gexec) (x : agent) (k0 kz : nat) :
  (∀ j lb, (k0 ≤ j)%nat → (j < kz)%nat → gx_lbl G (x, j) = Some lb →
     lb_is_w lb = false) →
  Forall (λ lb, lb_is_w lb = false) (take (kz - k0) (drop k0 (qrow G x))).
Proof.
  intros Hnw. apply Forall_lookup_2. intros i lb Hi.
  apply lookup_take_Some in Hi as [Hi Hlt].
  rewrite lookup_drop in Hi.
  apply (Hnw (k0 + i)%nat lb ltac:(lia) ltac:(lia)).
  by rewrite qrow_lbl.
Qed.

(** THE PACKAGE: the emission of the stretch [k0 .. kz], in the shape
    [walk_seg_data] names it. *)
Theorem qconf_seg_data (boot : agent → pexv6) (d0 : dev_state) (im : image)
    (nh : nat) (GD : gdexec) (x : agent) (k0 kz : nat) (lb : lbl) :
  gdexec_qconf boot d0 im nh GD →
  (k0 ≤ kz)%nat →
  gx_lbl (gd_g GD) (x, kz) = Some lb →
  (∀ j lb0, (k0 ≤ j)%nat → (j < kz)%nat →
     gx_lbl (gd_g GD) (x, j) = Some lb0 → lb_is_w lb0 = false) →
  ∃ (pre : list lbl) (p1 p2 : pexv6) (es : list eitem),
    Forall (λ l, lb_is_w l = false) pre ∧
    hemit (λ _, d0) k0 (row_ws (qrow (gd_g GD) x) k0) (pre ++ [lb]) p1 es p2.
Proof.
  intros Hq Hle Hkz Hnw.
  have Hkzr : qrow (gd_g GD) x !! kz = Some lb by rewrite -qrow_lbl.
  have Hk : (k0 ≤ length (qrow (gd_g GD) x))%nat.
  { pose proof (lookup_lt_Some _ _ _ Hkzr). lia. }
  destruct (qconf_hemit_seg boot d0 im nh GD x k0 (S kz - k0) Hq Hk)
    as (p1 & p2 & es & Hem).
  rewrite (seg_split_exit (qrow (gd_g GD) x) k0 kz lb Hle Hkzr) in Hem.
  exists (take (kz - k0) (drop k0 (qrow (gd_g GD) x))), p1, p2, es.
  split; [by apply seg_pre_nonwrite|exact Hem].
Qed.

(* ====================================================================== *)
(** * 2. THE READ/REGISTER POLICY — MOVED

    What was §2 here ([wsite_ok], [wsite_mstep_ok], [wblk_pol_at]) is now
    [WeakRvwmoWalk] §4.0c, where it DISCHARGES the repaired policy
    ([WeakRvwmoWalk.wpol_of_sites]) rather than only meeting it half way:
    once the policy is indexed by row position, the alignment §2 had to
    assume ([walign]) is part of the carried context [WeakRvwmoWalk.wctx],
    and the site data are read off [G] at the block's own position. *)

(* ====================================================================== *)
(** * 3. THE FUSED RMW's POLICY, POINTWISE

    [WeakRvwmoCert3.cpolp] is [wpol]'s twin for the [HEpair] block, and it
    is DISCHARGED the same way: the untainted mirror ([cert_block_pair_mirror])
    plus §4.3's admissibility ([cert_rmw_ok]), whose only real input is
    "the RMW's read sources are in the log" — which for an RMW is not an
    extra assumption but a consequence of [gatomicity] once the log's next
    entry is the RMW's own write ([cert_rmw_latest], used inside
    [cert_rmw_ok]).  [cpolp_of_rmwfree] remains the RMW-free instance. *)

(** [src_in_log_of_pfx'], [wrmw_site] and [wcpolp_at] MOVED to
    [WeakRvwmoWalk] §4.5b' — generalised in the witness set — so that the
    chained walk's own site datum [WeakRvwmoWalk.wsite_ok'] can carry the
    RMW obligation instead of excluding it with [lb_rmwfree].  What stays
    here is the alignment packaging. *)

(** [cpolp], from the RMW alignment. *)
Definition wralign (G : gexec) (n : nat) (x : agent) (Q : lbl → Prop)
    : Prop :=
  ∀ (c0 : cand) (lb : lbl),
    srvwmo_consistent c0 → cpol_ctx G (wwit G n) x c0 → Q lb →
    ¬ lb_rmwfree lb →
    cd_img c0 = gx_img G ∧ wlog_pfx G n (cd_log_end c0) ∧
    wrmw_site G n x (gcnt x (cd_tr c0)) lb.

Theorem cpolp_of_align (G : gexec) (n : nat) (x : agent) (cpu : CPU)
    (d0 : dev_state) (Q : lbl → Prop) :
  rvwmo_minus_consistent G →
  wralign G n x Q →
  cpolp x cpu d0 [] (λ _ : nat, cpol_ctx G (wwit G n) x)
    (wcls_at G (wwit G n) x) (λ _ : nat, Q).
Proof.
  intros Hcons Hal k c0 ws lb l1 l2 rds wrs m rs1 rs2 fn ib m' rs1' fn' ib'
    Hc Hctx HQ _ Hag Hblk.
  have Hrmw : ¬ lb_rmwfree lb
    := cblkp_rmw cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' Hblk.
  destruct (Hal c0 lb Hc Hctx HQ Hrmw) as (Himg & Hpfx & Hsite).
  have HnW : ¬ wwit G n (x, gcnt x (cd_tr c0)).
  { intros (aq0 & b0 & ts0 & vs0 & Hl0 & _).
    destruct Hsite as (Hl & _ & _).
    rewrite Hl0 in Hl. injection Hl as Hl'. rewrite -Hl' in Hrmw.
    exact (Hrmw I). }
  exact (wcpolp_at G (wwit G n) n x cpu d0 c0 ws lb l1 l2 rds wrs m rs1 rs2
           fn ib m' rs1' fn' ib' Hcons Himg Hpfx Hc Hctx HnW Hsite Hag Hblk).
Qed.

(* ====================================================================== *)
(** * 4. THE OBSTRUCTION: [wpol]'s UNIVERSAL CANDIDATE

    §2 proved the policy at a candidate ALIGNED to the block's row
    position.  [WeakRvwmoWalk.wpol] asks for it at EVERY candidate the
    certification context admits, and its conclusion — the classification
    [wcls_at], whose first clause is [WeakRvwmoGlue2.cstep_cls] — is about
    [G]'s label at THAT candidate's own position.  For a STORE the two
    disjuncts of [cstep_cls] collapse to one (a witness label is a load),
    and [lbl_reidx] leaves a store alone ([lbl_reidx_store]), so the policy
    PINS the store: it must be [G]'s label at every context candidate.

    That is not satisfiable for a segment of more than one block, and §4.2
    makes it concrete without needing a second candidate: the EMPTY
    candidate is a certification context of every graph whose hart [x] has
    no witness at row position 0 ([cpol_ctx_empty]), and its position is 0
    — so [wpol] forces the segment's exit write to be hart [x]'s FIRST
    event.  §4.3 carries that into [walk_seg_data] itself. *)

(** ** 4.0 Two shape facts about the emission *)

Lemma hemit_phart (d0 : dev_state) (k : nat) (ws : wstate) (row : list lbl)
    (p : pexv6) (es : list eitem) (pfin : pexv6) :
  hemit (λ _, d0) k ws row p es pfin →
  ∀ (cpu : CPU) (m : M unit) (rs : regstate) (fn : ofence) (ib : oib32),
    p = PHart cpu m rs fn ib →
    ∃ m' rs' fn' ib', pfin = PHart cpu m' rs' fn' ib'.
Proof.
  induction 1 as [k ws p
                 |k ws lb row p ls pa da l p' es pfin Har Hre Hst Hem IH
                 |k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin
                  Har1 Hre Hst1 Har2 Hst2 Hem IH];
    intros cpu m rs fn ib ->.
  - by exists m, rs, fn, ib.
  - destruct (adm_run_phart true _ _ _ ls da Har cpu m rs fn ib eq_refl)
      as (ma & rsa & fna & iba & ->).
    destruct (pstep_ev_phart cpu ma rsa fna iba da l p' _ Hst)
      as (m1 & rs1 & fn1 & ib1 & ->).
    by apply (IH cpu m1 rs1 fn1 ib1).
  - destruct (adm_run_phart true _ _ _ ls1 da Har1 cpu m rs fn ib eq_refl)
      as (ma & rsa & fna & iba & ->).
    destruct (pstep_ev_phart cpu ma rsa fna iba da l1 pm dm Hst1)
      as (mb & rsb & fnb & ibb & ->).
    destruct (adm_run_phart false _ _ dm ls2 dm2 Har2 cpu mb rsb fnb ibb eq_refl)
      as (mc & rsc & fnc & ibc & ->).
    destruct (pstep_ev_phart cpu mc rsc fnc ibc dm2 l2 p' _ Hst2)
      as (m1 & rs1 & fn1 & ib1 & ->).
    by apply (IH cpu m1 rs1 fn1 ib1).
Qed.

(** A ONE-LABEL emission IS a [cblk]. *)
Lemma hemit_single_cblk (d0 : dev_state) (k : nat) (ws : wstate) (lb : lbl)
    (cpu : CPU) (m : M unit) (rs : regstate) (fn : ofence) (ib : oib32)
    (es : list eitem) (pfin : pexv6) :
  hemit (λ _, d0) k ws [lb] (PHart cpu m rs fn ib) es pfin →
  lb_rmwfree lb →
  ∃ (l : wlabel) (rds : list wreg) (wrs : list register)
    (m' : M unit) (rs' : regstate) (fn' : ofence) (ib' : oib32),
    cblk cpu d0 ws lb l rds wrs m rs fn ib m' rs' fn' ib'.
Proof.
  intros Hem Hrmw. inversion Hem as
    [ |k' ws' lb' row' p' ls pa da l p'' es' pfin' Har Hre Hst Hem' Hk
     |k' ws' lb' row' p' ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p'' es' pfin'
      Har1 Hre Hst1 Har2 Hst2 Hem' Hk]; subst.
  - simpl in Har, Hst.
    destruct (adm_run_phart true _ _ d0 ls da Har cpu m rs fn ib eq_refl)
      as (ma & rsa & fna & iba & Hpa).
    rewrite Hpa in Har, Hre, Hst.
    destruct (pstep_ev_phart cpu ma rsa fna iba da l p'' d0 Hst)
      as (m1 & rs1 & fn1 & ib1 & Hp'').
    rewrite Hp'' in Hst.
    destruct (cblk_intro cpu d0 ws lb l ls (PHart cpu ma rsa fna iba) da
                m rs fn ib m1 rs1 fn1 ib1 Har Hre Hst) as (rds & wrs & Hblk).
    by exists l, rds, wrs, m1, rs1, fn1, ib1.
  - exfalso. destruct Hre as (aq & rl & base & tvs & data & asrc1 & asrc2 &
                              vsrc2 & _ & _ & _ & _ & ->).
    exact Hrmw.
Qed.

(** ** 4.1 [wpol] PINS the segment's exit store *)
Theorem wpol_pins_store (G : gexec) (n : nat) (x : agent) (cpu : CPU)
    (d0 : dev_state) (T : list wreg) (Q : lbl → Prop) (c0 : cand)
    (ws : wstate) (rl : bool) (base : Z) (vs : list (bv 8)) (kc : wm_class)
    (l : wlabel) (rds : list wreg) (wrs : list register) (m : M unit)
    (rs1 rs2 : regstate) (fn : ofence) (ib : oib32) (m' : M unit)
    (rs1' : regstate) (fn' : ofence) (ib' : oib32) :
  wpol_flat G (wwit G n) x cpu d0 T Q →
  srvwmo_consistent c0 →
  cpol_ctx G (wwit G n) x c0 →
  Q (WeakAxiomatic.LStore rl base vs kc) →
  w_relp (ms_ws (cand_last_st c0) x) = w_relp ws →
  dreg_agree (λ nn, nn ∉ T) rs1 rs2 →
  cblk cpu d0 ws (WeakAxiomatic.LStore rl base vs kc) l rds wrs
    m rs1 fn ib m' rs1' fn' ib' →
  gx_lbl G (x, gcnt x (cd_tr c0)) = Some (WeakAxiomatic.LStore rl base vs kc).
Proof.
  intros Hpol Hc Hctx HQ Hrelp Hag Hblk.
  destruct (Hpol c0 ws _ l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib'
              Hc Hctx HQ Hrelp Hag Hblk)
    as (lb' & l' & rds' & wrs' & rs2' & _ & _ & Hri & (Hcl & _) & _).
  have Hlb : lb' = WeakAxiomatic.LStore rl base vs kc
    := lbl_reidx_store rl base vs kc lb' Hri.
  destruct Hcl as [[_ Hl]|[_ (base0 & n0 & ts0 & vs0 & _ & _ & Heq)]].
  - by rewrite Hlb in Hl.
  - exfalso. rewrite Hlb in Heq. by rewrite /latest_read_lbl in Heq.
Qed.

(** ** 4.2 … at the EMPTY candidate, whose position is 0 *)

Lemma empty_cand_consistent (G : gexec) :
  srvwmo_consistent (Cand (gx_img G) []).
Proof.
  apply srvwmo_of_wf, cand_reachable. intros k s Hs. by destruct k.
Qed.

Lemma empty_cand_gcnt (G : gexec) (x : agent) :
  gcnt x (cd_tr (Cand (gx_img G) [])) = 0%nat.
Proof. reflexivity. Qed.

Corollary wpol_exit_at_zero (G : gexec) (n : nat) (x : agent) (cpu : CPU)
    (d0 : dev_state) (T : list wreg) (Q : lbl → Prop) (ws : wstate)
    (rl : bool) (base : Z) (vs : list (bv 8)) (kc : wm_class)
    (l : wlabel) (rds : list wreg) (wrs : list register) (m : M unit)
    (rs1 rs2 : regstate) (fn : ofence) (ib : oib32) (m' : M unit)
    (rs1' : regstate) (fn' : ofence) (ib' : oib32) :
  wpol_flat G (wwit G n) x cpu d0 T Q →
  Q (WeakAxiomatic.LStore rl base vs kc) →
  w_relp (ms_ws (cand_last_st (Cand (gx_img G) [])) x) = w_relp ws →
  dreg_agree (λ nn, nn ∉ T) rs1 rs2 →
  cblk cpu d0 ws (WeakAxiomatic.LStore rl base vs kc) l rds wrs
    m rs1 fn ib m' rs1' fn' ib' →
  gx_lbl G (x, 0%nat) = Some (WeakAxiomatic.LStore rl base vs kc).
Proof.
  intros Hpol HQ Hrelp Hag Hblk.
  rewrite -(empty_cand_gcnt G x).
  apply (wpol_pins_store G n x cpu d0 T Q _ ws rl base vs kc l rds wrs
           m rs1 rs2 fn ib m' rs1' fn' ib' Hpol (empty_cand_consistent G)
           (cpol_ctx_empty G (wwit G n) x) HQ Hrelp Hag Hblk).
Qed.

(** ** 4.3 … hence [walk_seg_data] itself pins the exit write

    [walk_seg_data] hands out, per walk state: the emission of
    [pre ++ [store]], [Forall Q] of it, and [wpol] at that [Q].  §4.0 turns
    the emission's LAST block into a [cblk] (the register agreement is
    reflexivity there — [dreg_agree_refl]), so §4.1 applies verbatim. *)
Theorem walk_seg_data_pins (boot : agent → pexv6) (d0 : dev_state) (N : nat)
    (G : gexec) :
  walk_seg_data_flat boot d0 N G →
  ∀ (St : cyc_state) (n : nat),
    wlk_inv boot d0 N G St n → (n < length (gwrites G))%nat →
  ∃ (x : agent) (rl : bool) (base : Z) (vs : list (bv 8)) (kc : wm_class)
    (ws : wstate) (w : geid),
    gwrite_at G (S n) = Some w ∧
    gmsg G w = Some (WMsg base vs (Some x) kc) ∧
    wrow_in_log' G x n ∧
    ∀ c0 : cand,
      srvwmo_consistent c0 → cpol_ctx G (wwit G n) x c0 →
      w_relp (ms_ws (cand_last_st c0) x) = w_relp ws →
      gx_lbl G (x, gcnt x (cd_tr c0))
        = Some (WeakAxiomatic.LStore rl base vs kc).
Proof.
  intros Hdata St n Hinv Hn.
  destruct (Hdata St n Hinv Hn)
    as (x & cpu & T & Q & k0 & ws0 & pre & rl & base & vs & kc & es & pfin &
        m0 & rs10 & rs20 & fn0 & ib0 & w &
        Hw & Hm & Hpre & Hem & HQ & Hctx & Hp & Hag & Hrelp & Hrow & Hpol &
        Hpolp).
  destruct (hemit_app (λ _, d0) k0 ws0 pre
              [WeakAxiomatic.LStore rl base vs kc]
              (PHart cpu m0 rs10 fn0 ib0) es pfin Hem)
    as (pm & es1 & es2 & Hem1 & Hem2 & _).
  destruct (hemit_phart d0 k0 ws0 pre _ es1 pm Hem1 cpu m0 rs10 fn0 ib0 eq_refl)
    as (m1 & rs11 & fn1 & ib1 & ->).
  destruct (hemit_single_cblk d0 (k0 + length pre)%nat
              (row_ws_aux k0 ws0 pre) (WeakAxiomatic.LStore rl base vs kc)
              cpu m1 rs11 fn1 ib1 es2 pfin Hem2 I)
    as (l & rds & wrs & m' & rs' & fn' & ib' & Hblk).
  have Hlk : (pre ++ [WeakAxiomatic.LStore rl base vs kc]) !! length pre
           = Some (WeakAxiomatic.LStore rl base vs kc)
    by apply (list_lookup_middle pre [] _ (length pre) eq_refl).
  have HQ2 : Q (WeakAxiomatic.LStore rl base vs kc)
    := Forall_lookup_1 Q _ (length pre) _ HQ Hlk.
  exists x, rl, base, vs, kc, (row_ws_aux k0 ws0 pre), w.
  split_and!; [exact Hw|exact Hm|exact Hrow|].
  intros c0 Hc Hctx0 Hrelp0.
  exact (wpol_pins_store G n x cpu d0 T Q c0 (row_ws_aux k0 ws0 pre)
           rl base vs kc l rds wrs m1 rs11 rs11 fn1 ib1 m' rs' fn' ib'
           Hpol Hc Hctx0 HQ2 Hrelp0 (dreg_agree_refl _ _) Hblk).
Qed.

(** THE FINDING, at its sharpest: at every walk state, [walk_seg_data]
    forces the segment's exit write to be its hart's row position 0.  The
    empty candidate is a certification context whenever hart [x] has no
    witness there — which the residue's own [wrow_in_log'] guarantees
    ([WeakRvwmoProgress.wrow_no_wit]) — and its position is 0.  So a walk
    state whose segment's exit write is NOT the hart's first event refutes
    [walk_seg_data]. *)
Corollary walk_seg_data_exit_at_zero (boot : agent → pexv6)
    (d0 : dev_state) (N : nat) (G : gexec) :
  walk_seg_data_flat boot d0 N G →
  ∀ (St : cyc_state) (n : nat),
    wlk_inv boot d0 N G St n → (n < length (gwrites G))%nat →
  ∃ (x : agent) (rl : bool) (base : Z) (vs : list (bv 8)) (kc : wm_class)
    (ws : wstate) (w : geid),
    gwrite_at G (S n) = Some w ∧
    gmsg G w = Some (WMsg base vs (Some x) kc) ∧
    (w_relp (ms_ws (cand_last_st (Cand (gx_img G) [])) x) = w_relp ws →
     gx_lbl G (x, 0%nat) = Some (WeakAxiomatic.LStore rl base vs kc)).
Proof.
  intros Hdata St n Hinv Hn.
  destruct (walk_seg_data_pins boot d0 N G Hdata St n Hinv Hn)
    as (x & rl & base & vs & kc & ws & w & Hw & Hm & Hrow & Hpin).
  exists x, rl, base, vs, kc, ws, w.
  split_and!; [exact Hw|exact Hm|].
  intros Hrelp0.
  rewrite -(empty_cand_gcnt G x).
  apply (Hpin (Cand (gx_img G) []) (empty_cand_consistent G)
           (cpol_ctx_empty G (wwit G n) x) Hrelp0).
Qed.

(** ** 4.4 THE REPAIR, LANDED — where it now lives

    The disease was one and the same in all three places the residue
    over-quantified — [wpol_flat]/[WeakRvwmoCert3.cert_segment']'s [Hpol']
    over ALL context candidates, [WeakRvwmoWalk.wrow_in_log]/[wnw] over ALL
    row positions, and [walk_seg_data_flat] over ALL [wlk_inv] states — and
    the cure is the same: index the policy by the ROW POSITION the iteration
    has reached, and let the carried context pin the candidate's own
    position to it.  That shape is now [WeakRvwmoWalk.wpol] (with its
    context [wctx] and its per-position segment predicate [wQ]), and §2's
    argument DISCHARGES it outright: [WeakRvwmoWalk.wpol_of_sites].
    [WeakRvwmoCert3.cert_segment'], [WeakRvwmoCert4.seg_step_of_segment] and
    [WeakRvwmoWalk.wlk_seg_of_cert] all take the indexed form; §5 below
    supplies the repaired residue's EMISSION from the conformance bundle. *)

(** … and the site hypothesis is READ OFF the graph at the walk's own
    segment: the emission's row IS [G]'s row ([qrow_lbl]), so row position
    [i] of the stretch is graph position [k0 + i]. *)
Lemma qrow_seg_lookup (G : gexec) (x : agent) (k0 len i : nat) (lb : lbl) :
  take len (drop k0 (qrow G x)) !! i = Some lb →
  gx_lbl G (x, (k0 + i)%nat) = Some lb.
Proof.
  intros Hi. apply lookup_take_Some in Hi as [Hi _].
  rewrite lookup_drop in Hi. by rewrite qrow_lbl.
Qed.

(* ====================================================================== *)
(** * 5. THE REPAIRED RESIDUE, AND WHAT THE CONFORMANCE BUNDLE SUPPLIES

    [WeakRvwmoProgress.walk_seg_data'] is the repaired residue: at every
    walk state, an EMISSION of hart [x]'s stretch through [G]'s [(n+1)]-st
    write, the SITE DATA [WeakRvwmoWalk.wQ] for that stretch, and the walk
    state's own ALIGNMENT [WeakRvwmoWalk.wctx].  §1 delivers the emission
    from [gdexec_qconf] alone.  What it does NOT deliver, and what is named
    here rather than hidden, is [wseg_supply]: which write the step is at,
    the graph-side site facts over the covered positions, the witness set's
    two side conditions, and the identification of the walk state's process
    with the emission's own ([wseg_align]). *)

(** ** 5.1 The emission of the stretch, with its PREFIX FIXED

    [qconf_seg_data] hands the prefix back existentially; the site data have
    to index into it, so this variant keeps it as the [take]/[drop] it is. *)
Theorem qconf_seg_take (boot : agent → pexv6) (d0 : dev_state) (im : image)
    (nh : nat) (GD : gdexec) (x : agent) (k0 kz : nat) (lb : lbl) :
  gdexec_qconf boot d0 im nh GD →
  (k0 ≤ kz)%nat →
  gx_lbl (gd_g GD) (x, kz) = Some lb →
  ∃ (p1 p2 : pexv6) (es : list eitem),
    hemit (λ _, d0) k0 (row_ws (qrow (gd_g GD) x) k0)
      (take (kz - k0) (drop k0 (qrow (gd_g GD) x)) ++ [lb]) p1 es p2.
Proof.
  intros Hq Hle Hkz.
  have Hkzr : qrow (gd_g GD) x !! kz = Some lb by rewrite -qrow_lbl.
  have Hk : (k0 ≤ length (qrow (gd_g GD) x))%nat.
  { pose proof (lookup_lt_Some _ _ _ Hkzr). lia. }
  destruct (qconf_hemit_seg boot d0 im nh GD x k0 (S kz - k0) Hq Hk)
    as (p1 & p2 & es & Hem).
  rewrite (seg_split_exit (qrow (gd_g GD) x) k0 kz lb Hle Hkzr) in Hem.
  by exists p1, p2, es.
Qed.

(** ** 5.2 The per-state datum the bundle does NOT supply *)

(** The walk state's process for [x] IS the emission's own starting
    process, and its release-pending bit is the row fold's. *)
Definition wseg_align (d0 : dev_state) (G : gexec) (St : cyc_state)
    (x : agent) (k0 : nat) (stretch : list lbl) : Prop :=
  ∀ (p1 : pexv6) (es : list eitem) (p2 : pexv6),
    hemit (λ _, d0) k0 (row_ws (qrow G x) k0) stretch p1 es p2 →
    ∃ (cpu : CPU) (m0 : M unit) (rs10 rs20 : regstate) (fn0 : ofence)
      (ib0 : oib32),
      p1 = PHart cpu m0 rs10 fn0 ib0 ∧
      cst_pst St (cd_end (cst_c St)) !! x = Some (PHart cpu m0 rs20 fn0 ib0) ∧
      dreg_agree (λ nn, nn ∉ []) rs10 rs20 ∧
      w_relp (ms_ws (cand_last_st (cst_c St)) x)
        = w_relp (row_ws (qrow G x) k0).

Definition wseg_supply (boot : agent → pexv6) (d0 : dev_state) (N : nat)
    (GD : gdexec) : Prop :=
  ∀ St n, wlk_inv boot d0 N (gd_g GD) St n →
    (n < length (gwrites (gd_g GD)))%nat →
  ∃ (x : agent) (k0 kz : nat),
    (* WHICH WRITE: [G]'s [(n+1)]-st, and where the hart stands now *)
    gwrite_at (gd_g GD) (S n) = Some (x, kz) ∧
    (k0 ≤ kz)%nat ∧
    gcnt x (cd_tr (cst_c St)) = k0 ∧
    (* THE SITE FACTS over the covered positions.  Note what is NOT here
       any more: [wsrc_le] — a covered position may be a WITNESS, and is
       then served by the latest-read route, which asks instead for
       [WeakRvwmoWalk.wwit_site]. *)
    (∀ k lb, (k0 ≤ k)%nat → (k < kz)%nat →
       gx_lbl (gd_g GD) (x, k) = Some lb → lb_is_w lb = false) ∧
    (∀ k lb, (k0 ≤ k)%nat → (k ≤ kz)%nat →
       gx_lbl (gd_g GD) (x, k) = Some lb → lb_rmwfree lb) ∧
    (∀ k, (k0 ≤ k)%nat → (k ≤ kz)%nat →
       wwit (gd_g GD) n (x, k) → wwit_site (gd_g GD) n x k) ∧
    (* THE WITNESS SET's side conditions *)
    cpol_ctx (gd_g GD) (wwit (gd_g GD) n) x (cst_c St) ∧
    W_poloc_closed (gd_g GD) (wwit (gd_g GD) n) ∧
    wub (gd_g GD) (wwit (gd_g GD) n) x ∧
    (* THE STATE IDENTIFICATION *)
    wseg_align d0 (gd_g GD) St x k0
      (take (kz - k0) (drop k0 (qrow (gd_g GD) x)) ++
       [default (WeakAxiomatic.LFence false false false false)
          (gx_lbl (gd_g GD) (x, kz))]).

(** ** 5.3 … and then the residue IS supplied *)
Theorem walk_seg_data_of_qconf (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh N : nat) (GD : gdexec) :
  rvwmo_minus_deps_consistent GD →
  gdexec_qconf boot d0 im nh GD →
  wseg_supply boot d0 N GD →
  walk_seg_data' boot d0 N (gd_g GD).
Proof.
  intros Hcons Hq Hsup St n Hinv Hn.
  set G := gd_g GD.
  have Hwf : gwf G by destruct Hcons as ((H & _ & _) & _ & _).
  have Hnd : NoDup (gx_gmo G) by destruct Hwf as (H & _ & _).
  destruct (Hsup St n Hinv Hn)
    as (x & k0 & kz & Hat & Hle & Hgc & Hnwr & Hrmw & Hwitd & Hctx & Hpc &
        Hub & Hal).
  destruct (gwrite_at_inv G (S n) (x, kz) Hnd Hat) as (Hmem & Hwix).
  (* the exit write's label *)
  have Hisw : gis_w G (x, kz) = true by apply gwrites_elem_of in Hmem as [_ H].
  destruct (gx_lbl G (x, kz)) as [lb|] eqn:Hlb; [|by rewrite /gis_w Hlb in Hisw].
  have Hlbw : lb_is_w lb = true by rewrite /gis_w Hlb in Hisw.
  have Hlbr : lb_rmwfree lb := Hrmw kz lb Hle (Nat.le_refl _) Hlb.
  destruct lb as [aq0 b0 ts0 vs0|rl base vs kc|pr pw sr sw
                 |aq0 rl0 b0 ts0 rv0 wv0 kc0]; try by simpl in Hlbw.
  set pre := take (kz - k0) (drop k0 (qrow G x)).
  destruct (qconf_seg_take boot d0 im nh GD x k0 kz
              (WeakAxiomatic.LStore rl base vs kc) Hq Hle Hlb)
    as (p1 & p2 & es & Hem).
  have Hemp : hemit (λ _, d0) k0 (row_ws (qrow G x) k0)
                (pre ++ [WeakAxiomatic.LStore rl base vs kc]) p1 es p2
    := Hem.
  destruct (Hal p1 es p2 ltac:(rewrite Hlb /=; exact Hemp))
    as (cpu & m0 & rs10 & rs20 & fn0 & ib0 & -> & Hp & Hag & Hrelp).
  (* the prefix's length pins [kz] *)
  have Hkzr : qrow G x !! kz = Some (WeakAxiomatic.LStore rl base vs kc)
    by rewrite -qrow_lbl.
  have Hlenpre : length pre = (kz - k0)%nat.
  { rewrite /pre length_take length_drop.
    pose proof (lookup_lt_Some _ _ _ Hkzr). lia. }
  have Hkz : (k0 + length pre)%nat = kz by lia.
  exists x, cpu, k0, (row_ws (qrow G x) k0), pre, rl, base, vs, kc, es, p2,
         m0, rs10, rs20, fn0, ib0, (x, kz).
  split_and!.
  - exact Hat.
  - by rewrite /gmsg Hlb.
  - apply Forall_lookup_2. intros i lb0 Hi.
    apply lookup_take_Some in Hi as [Hi Hlt].
    rewrite lookup_drop in Hi.
    apply (Hnwr (k0 + i)%nat lb0 ltac:(lia) ltac:(lia)).
    by rewrite qrow_lbl.
  - exact Hemp.
  - intros i lb0 Hi.
    destruct (decide (i < length pre)%nat) as [Hlt|Hlt].
    + rewrite lookup_app_l // in Hi.
      have Hl0 : gx_lbl G (x, (k0 + i)%nat) = Some lb0
        by apply (qrow_seg_lookup G x k0 (kz - k0)%nat i).
      have Hnw0 : lb_is_w lb0 = false
        := Hnwr (k0 + i)%nat lb0 ltac:(lia) ltac:(lia) Hl0.
      split_and!; [lia|lia| |].
      * split_and!; [exact Hl0|by rewrite Hnw0
                    |by apply (Hrmw (k0+i)%nat); [lia|lia|]
                    |by apply Hwitd; lia].
      * split; [by rewrite Hnw0|lia].
    + rewrite lookup_app_r in Hi; [|lia].
      have Hi0 : (i - length pre)%nat = 0%nat.
      { pose proof (lookup_lt_Some _ _ _ Hi) as Hb. simpl in Hb. lia. }
      have Hik : (k0 + i)%nat = kz by lia.
      rewrite Hi0 /= in Hi. injection Hi as <-.
      rewrite Hik. split_and!; [lia|lia| |].
      * split_and!; [exact Hlb|by intros _|exact I|by apply Hwitd; lia].
      * split; [done|by intros _].
  - split_and!; [exact Hctx|exact Hgc|].
    rewrite /wlogn (bool_decide_eq_true_2 (k0 ≤ k0 + length pre)%nat); [|lia].
    by destruct Hinv as (_ & _ & _ & _ & H).
  - exact Hp.
  - exact Hag.
  - exact Hrelp.
  - exact Hpc.
  - exact Hub.
Qed.

(** ** 5.4 THE WALK, AND THE CAPSTONE AT (R-1) PLUS [wseg_supply] *)
Theorem walk_supply_of_qconf (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh N : nat) :
  (∀ GD : gdexec,
     rvwmo_minus_deps_consistent GD → gdexec_qconf boot d0 im nh GD →
     wseg_supply boot d0 N GD) →
  walk_supply boot d0 im nh N.
Proof.
  intros Hsup. apply walk_supply_of_wp'. intros GD Hcons Hq.
  by apply (walk_seg_data_of_qconf boot d0 im nh N GD Hcons Hq), Hsup.
Qed.

Theorem xv6_rvwmo_safe_modulo_l2 (Σ : gFunctors)
    `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (Nm : Z → Z → namespace) (P : Z → Z → Prop) :
  fresh_era gen σ0 →
  wp_package Σ gen σ0 D →
  (∀ a base, P a base → wp_package_prot Σ gen σ0 D (Nm a base) a base) →
  (* (R-1) *)
  l2_claim (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) P
           (bad_run gen σ0) →
  (* (R-2), reduced to the per-state SITE/STATE datum *)
  (∀ GD : gdexec,
     rvwmo_minus_deps_consistent GD →
     gdexec_qconf (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) GD →
     wseg_supply (xboot σ0) (wgdev σ0) (xN σ0) GD) →
  ∀ GD : gdexec,
    rvwmo_minus_deps_consistent GD →
    gdexec_qconf (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) GD →
  (∀ x, ¬ tc (RacyD GD) x x) ∧
  (∃ (c : cand) (pst : nat → list pexv6) P' σ',
     srvwmo_consistent c ∧
     cd_img c = img_z (wgimg σ0) ∧
     pst 0%nat = eps_init σ0 ∧
     exec_prog_ok' pstep_ev pcls_ev pst (λ _, wgdev σ0) (cand_exec c) ∧
     rtc epf_run (ep_init gen, σ0) (P', σ') ∧
     wglog σ' = cd_log c (length (cd_tr c)) ∧
     pa_st <$> pc_ags (ecfg_of P' σ') = pst (length (cd_tr c))) ∧
  (∀ ρ, rtc epf_run (ep_init gen, σ0) ρ →
     ~ violation_hart cls_of pub_of n_disk (ecfg_of ρ.1 ρ.2)) ∧
  (∀ t2 σ2 e2,
     rtc (@erased_step weak_ev_lang) (epower_fork gen, σ0) (t2, σ2) →
     e2 ∈ t2 →
     reducible (Λ := weak_ev_lang) e2 σ2).
Proof.
  intros Hfr Hwp Hwpp Hl2 Hsup.
  apply (xv6_rvwmo_safe_modulo Σ gen σ0 D Nm P Hfr Hwp Hwpp Hl2).
  by apply walk_supply_of_qconf.
Qed.

(** ** 5.5 THE CAPSTONE AT THE CHAINED WALK — (R-2) AS A STATEMENT ABOUT
       THE GRAPH

    [xv6_rvwmo_safe_modulo_l2] above still asks, per WALK STATE, for the
    emission, the alignment and the identification of the state's process
    with the emission's ([wseg_supply]).  [WeakRvwmoWalk]'s [wlk_inv']
    CARRIES all three, so what is left is a datum about [G] alone: a frozen
    witness set [W] together with

      - [gwrow_gmo]: one hart's writes reach the log in program order (the
        walk replays a row forwards; [grule14] implies it, and the walk
        deliberately does not ask for rule 14 itself);
      - the booted harts ([x < N]) and their [PHart]-ness at a writing
        agent;
      - [W]'s two side conditions, [W_poloc_closed] and [wubA];
      - [wsite_supply]: per position, RMW-freedom and the CLASSIFICATION —
        outside [W] with its sources already in the log, or inside [W], a
        genuine witness at that position's own visit count, and carrying
        [wwit_site].

    No walk state appears in it. *)
Theorem xv6_rvwmo_safe_modulo_l2' (Σ : gFunctors)
    `{!riscvGpreS Σ, !weakGpreS Σ}
    (gen : nat) (σ0 : wgstate) (D : CPU → gset register)
    (Nm : Z → Z → namespace) (P : Z → Z → Prop) :
  fresh_era gen σ0 →
  wp_package Σ gen σ0 D →
  (∀ a base, P a base → wp_package_prot Σ gen σ0 D (Nm a base) a base) →
  (* (R-1) *)
  l2_claim (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) P
           (bad_run gen σ0) →
  (* (R-2), reduced to a per-GRAPH datum *)
  (∀ GD : gdexec,
     rvwmo_minus_deps_consistent GD →
     gdexec_qconf (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) GD →
     ∃ W : geid → Prop, wsupply (xboot σ0) (gd_g GD) W (xN σ0)) →
  ∀ GD : gdexec,
    rvwmo_minus_deps_consistent GD →
    gdexec_qconf (xboot σ0) (wgdev σ0) (img_z (wgimg σ0)) (xN σ0) GD →
  (∀ x, ¬ tc (RacyD GD) x x) ∧
  (∃ (c : cand) (pst : nat → list pexv6) P' σ',
     srvwmo_consistent c ∧
     cd_img c = img_z (wgimg σ0) ∧
     pst 0%nat = eps_init σ0 ∧
     exec_prog_ok' pstep_ev pcls_ev pst (λ _, wgdev σ0) (cand_exec c) ∧
     rtc epf_run (ep_init gen, σ0) (P', σ') ∧
     wglog σ' = cd_log c (length (cd_tr c)) ∧
     pa_st <$> pc_ags (ecfg_of P' σ') = pst (length (cd_tr c))) ∧
  (∀ ρ, rtc epf_run (ep_init gen, σ0) ρ →
     ~ violation_hart cls_of pub_of n_disk (ecfg_of ρ.1 ρ.2)) ∧
  (∀ t2 σ2 e2,
     rtc (@erased_step weak_ev_lang) (epower_fork gen, σ0) (t2, σ2) →
     e2 ∈ t2 →
     reducible (Λ := weak_ev_lang) e2 σ2).
Proof.
  intros Hfr Hwp Hwpp Hl2 Hsup.
  apply (xv6_rvwmo_safe_modulo Σ gen σ0 D Nm P Hfr Hwp Hwpp Hl2).
  by apply walk_supply_of_sites.
Qed.

(* ====================================================================== *)
(** * 6. NON-VACUITY, AND WHAT [cyg] SHOWS THE REPAIR DOES *NOT* REACH

    [WeakRvwmoCycWit.cyg] is the tree's two-hart LB graph with a real
    [RacyD] cycle, consistent and [gdexec_qconf]-conformant, on which
    [WeakRvwmoWalk]'s ENGINE runs end to end ([cyg_walk], built by hand out
    of [wlk_step_of_seg]).  This section runs the REPAIRED residue at it.

    §6.1 THE POSITIVE HALF.  The repaired site predicate [WeakRvwmoWalk.wQ]
    — the thing the old, over-quantified policy could not state — HOLDS at
    [cyg]'s second segment, with the exit store at ROW POSITION 1.  That is
    exactly the configuration [WeakRvwmoWalk2.wpol_exit_at_zero] refuted
    under the old shape, so the repair is not vacuous where it was.

    §6.2 THE WITNESS SEGMENT, NOW SERVED.  Hart 0's load draws on hart 1's
    store, which the log has not reached at [n = 0], so that read is a
    WITNESS ([cyg_wit00]).  Under the OLD shape that killed the residue:
    [WeakRvwmoCert3.cpol_ctx] asserted [¬ W] AT THE CANDIDATE'S OWN
    POSITION, so no candidate standing at a witness carried the context and
    the substituted branch of [WeakRvwmoGlue2.cstep_cls] was unreachable
    through [cert_segment'].  The split moved that clause into
    [cpol_read]'s premises, and this section runs the consequence: the
    empty candidate DOES carry the context at [cyg]'s witness
    ([cyg_ctx0]), the site datum at that position is statable
    ([cyg_wwit_site00], [cyg_wQ_seg0]), and the walk's FIRST step at [cyg]
    — the one whose read the policy must substitute — comes out of the
    GENERIC engine with no hand-built block ([cyg_step0_generic]). *)

(** ** 6.1 The repaired site data, at [cyg]'s second segment *)
Lemma cyg_wQ_seg1 (i : nat) (lb : lbl) :
  cy_row cy_B cy_A cy_ts1 !! i = Some lb →
  wQ cyg 1%nat 1%nat 0%nat 1%nat (0 + i)%nat lb.
Proof.
  destruct i as [|[|i]]; [| |by rewrite /cy_row /=]; intros [= <-].
  - (* the TRUE read: its source is write 1, which the log holds *)
    split_and!; [lia|lia| |split; [done|done]].
    split_and!.
    + reflexivity.
    + by intros H.
    + exact I.
    + intros (aq & base & ts & vs & Hl & j & t & Hj & Hlt). exfalso.
      destruct (cyg_lbl _ _ Hl) as [[He _]|[[He _]|[[_ Hl2]|[He _]]]];
        [by simplify_eq|by simplify_eq| |by simplify_eq].
      injection Hl2 as Ha Hb Hc Hd. subst.
      destruct j as [|[|[|[|j]]]]; try (by rewrite /cy_ts1 /= in Hj);
        injection Hj as <-; lia.
  - (* THE EXIT STORE, AT ROW POSITION 1 — not 0 *)
    split_and!; [lia|lia| |split; [done|done]].
    split_and!.
    + reflexivity.
    + intros _. exact cyg_wix2.
    + exact I.
    + intros (aq & base & ts & vs & Hl & _). exfalso.
      destruct (cyg_lbl _ _ Hl) as [[_ Hl2]|[[_ Hl2]|[[_ Hl2]|[_ Hl2]]]];
        by simplify_eq.
Qed.

(** … and the segment-restricted (W-4) at it. *)
Lemma cyg_wnw_seg1 : wnw_seg cyg 1%nat 1%nat 0%nat 1%nat.
Proof.
  intros k _ Hk (aq & base & ts & vs & Hl & _).
  destruct (cyg_lbl _ _ Hl) as [[He Hl2]|[[He Hl2]|[[He Hl2]|[He Hl2]]]];
    by simplify_eq.
Qed.

(** ** 6.2 THE OBSTRUCTION, GONE — [cyg]'s WITNESS SEGMENT, SERVED BY THE
       GENERIC ENGINE

    Before the split, [WeakRvwmoCert3.cpol_ctx] asserted [¬ W] AT THE
    CANDIDATE'S OWN POSITION, so the EMPTY candidate — the walk's start —
    did not carry the certification context for hart 0 (whose load is a
    witness at [n = 0], [cyg_wit00]), the substituted branch of
    [WeakRvwmoGlue2.cstep_cls] was unreachable through [cert_segment'], and
    [walk_seg_data'] was FALSE at [cyg]'s first walk state.  With the
    clause moved into [cpol_read]'s premises the empty candidate DOES carry
    the context ([cyg_ctx0]), the site datum at a witness position is
    statable ([cyg_wwit_site00] / [cyg_wQ_seg0]), and the walk's first step
    at [cyg] — the one whose read must be SUBSTITUTED — comes out of the
    generic engine with no hand-built block: [cyg_step0_generic]. *)

(** Hart 0's load IS a witness at log length 0. *)
Lemma cyg_wit00 : wwit cyg 0%nat (0%nat, 0%nat).
Proof.
  exists false, zA, cy_ts2, cy_bytes. split; [reflexivity|].
  exists 0%nat, 2%nat. split; [reflexivity|lia].
Qed.

(** … and the EMPTY candidate now DOES carry the certification context for
    hart 0.  This is the exact negation of the old [cyg_no_ctx0]. *)
Lemma cyg_ctx0 : cpol_ctx cyg (wwit cyg 0%nat) 0%nat cw_c0.
Proof. exact (cpol_ctx_empty cyg (wwit cyg 0%nat) 0%nat). Qed.

(** [cyg] carries no fence at all, so [WeakRvwmoFloor.fhook] never fires
    and (W-2) is vacuous — at EVERY witness set, witnesses and all. *)
Lemma cyg_no_fhook (r : geid) (k : nat) (pb : bool) : ¬ fhook cyg r k pb.
Proof.
  intros (kf & pr & pw & sr & sw & _ & _ & Hl & _).
  destruct (cyg_lbl _ _ Hl) as [[_ H]|[[_ H]|[[_ H]|[_ H]]]]; by simplify_eq.
Qed.

Lemma cyg_wub (n : nat) (x : agent) : wub cyg (wwit cyg n) x.
Proof.
  intros c0 lb' ev' _ p s Hs HW Hag Hfh. by destruct (cyg_no_fhook _ _ _ Hfh).
Qed.

(** (W-a) at [cyg]: its only reads are at row position 0, and [gpo] is
    strict, so nothing is po-after a witness. *)
Lemma cyg_W_poloc (n : nat) : W_poloc_closed cyg (wwit cyg n).
Proof.
  intros e1 e2 a HW Hpo _ _ (l & Hl & Hr).
  destruct (cyg_lbl e2 l Hl) as [[He _]|[[_ Hl2]|[[He _]|[_ Hl2]]]];
    [| |
     |]; [..|by rewrite Hl2 /= in Hr];
    [destruct Hpo as (_ & Hlt & _); rewrite He /= in Hlt; lia
    |by rewrite Hl2 /= in Hr
    |destruct Hpo as (_ & Hlt & _); rewrite He /= in Hlt; lia].
Qed.

(** THE WITNESS SITE DATUM at hart 0's load.  The candidate is pinned by
    the two [wctx] clauses — image [gx_img cyg], log the gmo prefix of
    length 0, i.e. EMPTY — so all three components compute. *)
Lemma cyg_wwit_site00 : wwit_site cyg 0%nat 0%nat 0%nat.
Proof.
  intros c aq base ts vs Himg Hpfx Hl.
  have Hlog : cd_log_end c = [].
  { destruct Hpfx as [Hlen _]. by apply nil_length_inv. }
  destruct (cyg_lbl _ _ Hl) as [[_ Hl2]|[[He _]|[[He _]|[He _]]]];
    [|by simplify_eq|by simplify_eq|by simplify_eq].
  injection Hl2 as Ha Hb Hc Hd. subst.
  have H4 : length cy_ts2 = 4%nat := eq_refl.
  rewrite H4. split_and!; [reflexivity| |].
  - intros j Hj. rewrite Hlog Himg.
    destruct j as [|[|[|[|j]]]]; try lia; vm_compute; by eexists.
  - rewrite /lrd_vs Hlog Himg. by vm_compute.
Qed.

(** THE SITE DATA at [cyg]'s FIRST segment — the one the old shape could
    not state: row position 0 is a WITNESS. *)
Lemma cyg_wQ_seg0 (i : nat) (lb : lbl) :
  cy_row cy_A cy_B cy_ts2 !! i = Some lb →
  wQ cyg 0%nat 0%nat 0%nat 1%nat (0 + i)%nat lb.
Proof.
  destruct i as [|[|i]]; [| |by rewrite /cy_row /=]; intros [= <-].
  - (* THE WITNESS READ, at row position 0 *)
    split_and!; [lia|lia| |split; [done|done]].
    split_and!.
    + reflexivity.
    + by intros H.
    + exact I.
    + intros _. exact cyg_wwit_site00.
  - (* the exit store, at row position 1 *)
    split_and!; [lia|lia| |split; [done|done]].
    split_and!.
    + reflexivity.
    + intros _. exact cyg_wix1.
    + exact I.
    + intros (aq & base & ts & vs & Hl & _). exfalso.
      destruct (cyg_lbl _ _ Hl) as [[_ H]|[[_ H]|[[_ H]|[_ H]]]];
        by simplify_eq.
Qed.

(** THE ACCEPTANCE TEST.  One step of [WeakRvwmoWalk]'s walk at [cyg]'s
    FIRST write, built by the GENERIC engine — [wlk_seg_of_cert] (whose
    policy is [wpol_of_sites], whose read routes are the two of §4.0c) plus
    [wlk_step_of_seg] — from the conformance bundle's own emission
    ([WeakRvwmoCycWit.cy_hart_conf]) and the site data above.  Nothing here
    builds a block or chooses a label by hand: the substituted read is the
    POLICY's choice. *)
Theorem cyg_step0_generic (cpu0 cpu1 : CPU) (rs0 rs1 : regstate)
    (d0 : dev_state) :
  wlk_step cyg d0 (cw_S0 cpu0 cpu1 rs0 rs1 d0) 0%nat.
Proof.
  destruct (wlk_seg_of_cert cyg 0%nat 0%nat cpu0 d0 0%nat 1%nat ws_init
              (cy_row cy_A cy_B cy_ts2)
              (em_items (cy_em cy_A cy_B cy_ts2 cpu0 rs0))
              (em_fin (cy_em cy_A cy_B cy_ts2 cpu0 rs0))
              (cy_m cy_A cy_B) rs0 None ib_none
              (cw_S0 cpu0 cpu1 rs0 rs1 d0) rs0
              cyg_consistent (cyg_W_poloc 0%nat) (cyg_wub 0%nat 0%nat)
              (cy_hart_conf 0%nat cy_A cy_B cy_ts2 cpu0 rs0 d0
                 cy_A_ram cy_B_ram eq_refl)
              cyg_wQ_seg0 (cw_S0_ok cpu0 cpu1 rs0 rs1 d0))
    as (St' & tradd & Hstep & _ & Himg & Hpst & Hdv).
  - split_and!; [exact cyg_ctx0|reflexivity|apply wlog_pfx_nil].
  - reflexivity.
  - apply dreg_agree_refl.
  - reflexivity.
  - eapply (wlk_step_of_seg cyg d0 _ St' 0%nat _
              [WeakAxiomatic.LLoad false zA cy_ts2 cy_bytes]
              false zB cy_bytes WCplain (0%nat, 1%nat));
      [exact Hstep|reflexivity| |exact Himg|exact Hpst|exact Hdv
      |exact cyg_at1|exact cw_gmsg1].
    by apply Forall_singleton.
Qed.


(** ** 6.3 THE ACCEPTANCE TEST: THE WHOLE WALK AT [cyg], FROM THE GENERIC
       ENGINE

    §6.2 ran ONE step at a concrete state.  With [WeakRvwmoWalk]'s chained
    invariant ([wlk_inv']) the walk runs to the end from the per-graph datum
    alone: [cyg_wsupply] names the FROZEN witness set — hart 0's load, the
    cycle's backward step, and nothing else — and
    [WeakRvwmoWalk.wlk_run'] does the rest.  Nothing below builds a
    candidate, a block, a process supply or a segment by hand; contrast
    [WeakRvwmoCycWit.cyg_walk], which builds four candidates, five process
    supplies and two [seg_step]s explicitly. *)

(** THE FROZEN SET: exactly the cycle's backward step. *)
Definition cyW : geid → Prop := λ e, e = (0%nat, 0%nat).

Lemma cyW_ne (e : geid) : e ≠ (0%nat, 0%nat) → ¬ cyW e.
Proof. by rewrite /cyW. Qed.

Lemma cyg_hart (e : geid) : is_Some (gx_lbl cyg e) → (e.1 < 2)%nat.
Proof.
  intros [l Hl].
  destruct (cyg_lbl _ _ Hl) as [[He _]|[[He _]|[[He _]|[He _]]]];
    rewrite He /=; lia.
Qed.

Lemma cyg_w_at (e : geid) (l : lbl) :
  gx_lbl cyg e = Some l → lb_is_w l = true → e.2 = 1%nat.
Proof.
  intros Hl Hw.
  destruct (cyg_lbl _ _ Hl) as [[_ Hl2]|[[He _]|[[_ Hl2]|[He _]]]];
    [by rewrite Hl2 /= in Hw|by rewrite He|by rewrite Hl2 /= in Hw
    |by rewrite He].
Qed.

Lemma cyg_W_poloc' : W_poloc_closed cyg cyW.
Proof.
  intros e1 e2 a HW Hpo _ _ (l & Hl & Hr).
  destruct (cyg_lbl e2 l Hl) as [[He _]|[[_ Hl2]|[[He _]|[_ Hl2]]]];
    [exact He|by rewrite Hl2 /= in Hr| |by rewrite Hl2 /= in Hr].
  exfalso. destruct Hpo as (Hag & _ & _). rewrite /cyW in HW.
  rewrite HW He /= in Hag. done.
Qed.

Lemma cyg_wubA : wubA cyg cyW.
Proof.
  intros c ev y _ p s Hs HW Hag Hfh. by destruct (cyg_no_fhook _ _ _ Hfh).
Qed.

(** ONE WRITE PER HART, so the order fact the walk needs holds vacuously —
    and that is the point: [cyg] REFUTES [grule14] (its cycle is built out
    of rule-14 edges), so a walk that asked for rule 14 could not run
    here. *)
Lemma cyg_gwrow : gwrow_gmo cyg.
Proof.
  intros x j k Hjk (lj & Hlj & Hwj) (lk & Hlk & Hwk). exfalso.
  have Hj1 : j = 1%nat := cyg_w_at (x, j) lj Hlj Hwj.
  have Hk1 : k = 1%nat := cyg_w_at (x, k) lk Hlk Hwk.
  lia.
Qed.

Lemma cyg_wsrc_le_store (n : nat) (e : geid) (lb : lbl) :
  gx_lbl cyg e = Some lb → lb_is_w lb = true → wsrc_le cyg n e.
Proof.
  intros Hl Hw aq base ts vs Hl2. exfalso.
  rewrite Hl2 in Hl. injection Hl as <-. by simpl in Hw.
Qed.

Lemma cyg_wsite_supply : wsite_supply cyg cyW.
Proof.
  intros n x kz p lb Hat Hp _ Hl.
  destruct n as [|[|n]].
  - (* THE FIRST WRITE: hart 0's store, at row position 1 *)
    rewrite cyg_at1 in Hat. simplify_eq.
    destruct p as [|[|p]]; [| |exfalso; simpl in Hp; lia].
    + destruct (cyg_lbl _ _ Hl) as [[_ ->]|[[He _]|[[He _]|[He _]]]];
        [|by simplify_eq|by simplify_eq|by simplify_eq].
      split; [by intros Hn; destruct (Hn I)|]. right.
      split_and!; [reflexivity|exact cyg_wit00|exact cyg_wwit_site00].
    + destruct (cyg_lbl _ _ Hl) as [[He _]|[[_ ->]|[[He _]|[He _]]]];
        [by simplify_eq| |by simplify_eq|by simplify_eq].
      split; [by intros Hn; destruct (Hn I)|]. left. split;
        [by apply cyW_ne|by apply (cyg_wsrc_le_store 0%nat _ _ Hl)].
  - (* THE SECOND WRITE: hart 1's store, at row position 1 *)
    rewrite cyg_at2 in Hat. simplify_eq.
    destruct p as [|[|p]]; [| |exfalso; simpl in Hp; lia].
    + destruct (cyg_lbl _ _ Hl) as [[He _]|[[He _]|[[_ ->]|[He _]]]];
        [by simplify_eq|by simplify_eq| |by simplify_eq].
      split; [by intros Hn; destruct (Hn I)|]. left. split; [by apply cyW_ne|].
      intros aq base ts vs Hl2 j t Hj.
      rewrite Hl2 in Hl. injection Hl as Ha Hb Hc Hd. subst.
      destruct j as [|[|[|[|j]]]]; try (by rewrite /cy_ts1 /= in Hj);
        injection Hj as <-; lia.
    + destruct (cyg_lbl _ _ Hl) as [[He _]|[[He _]|[[He _]|[_ ->]]]];
        [by simplify_eq|by simplify_eq|by simplify_eq|].
      split; [by intros Hn; destruct (Hn I)|]. left. split;
        [by apply cyW_ne|by apply (cyg_wsrc_le_store 1%nat _ _ Hl)].
  - exfalso. rewrite /gwrite_at cyg_gwrites /= in Hat. done.
Qed.

Theorem cyg_wsupply (cpu0 cpu1 : CPU) (rs0 rs1 : regstate) :
  wsupply (cy_boot cpu0 cpu1 rs0 rs1) cyg cyW 2%nat.
Proof.
  split_and!.
  - exact cyg_gwrow.
  - intros x k Hs. have Hx := cyg_hart (x, k) Hs. simpl in Hx. lia.
  - intros x k lb Hl _.
    have Hx := cyg_hart (x, k) (mk_is_Some _ _ Hl). simpl in Hx.
    destruct x as [|[|x]]; [| |lia]; by eexists _, _, _, _, _.
  - exact cyg_W_poloc'.
  - exact cyg_wubA.
  - exact cyg_wsite_supply.
Qed.

(** THE ACCEPTANCE TEST: [WeakRvwmoCycWit.cyg_walk]'s conclusion, from the
    generic engine — the invariant, the start, and the per-graph datum. *)
Theorem cyg_walk' (cpu0 cpu1 : CPU) (rs0 rs1 : regstate) (d0 : dev_state) :
  ∃ (l : list segout) (S0 Sf : cyc_state),
    segs_run d0 l S0 Sf ∧
    cd_img (cst_c Sf) = gx_img cyg ∧
    cst_pst Sf 0%nat = cy_boot cpu0 cpu1 rs0 rs1 <$> seq 0 2 ∧
    cst_dv Sf 0%nat = d0 ∧
    log_of cyg (cd_log (cst_c Sf) (length (cd_tr (cst_c Sf)))).
Proof.
  have Hwf : gwf cyg by destruct cyg_consistent as (H & _).
  have Hem0 : ∀ x, (x < 2)%nat →
                wemit d0 cyg x 0%nat (cy_boot cpu0 cpu1 rs0 rs1 x).
  { intros x _.
    exact (wemit_of_qconf (cy_boot cpu0 cpu1 rs0 rs1) d0 cy_img 2%nat cygd x
             (cyg_qconf cpu0 cpu1 rs0 rs1 d0)). }
  destruct (wlk_run' (cy_boot cpu0 cpu1 rs0 rs1) d0 2%nat cyg cyW
              (λ St n Hinv Hn,
                 wlk_step'_of_supply (cy_boot cpu0 cpu1 rs0 rs1) d0 2%nat
                   cyg cyW St n cyg_consistent (cyg_wsupply cpu0 cpu1 rs0 rs1)
                   Hinv Hn)
              2%nat 0%nat
              (wlk_start (cy_boot cpu0 cpu1 rs0 rs1) d0 2%nat cyg)
              (wlk_start_inv' (cy_boot cpu0 cpu1 rs0 rs1) d0 2%nat cyg cyW
                 Hwf Hem0)
              ltac:(by rewrite cyg_gwrites))
    as (l & Sf & Hrun & Hok & Himg & Hpst & Hdv & Hpfx).
  exists l, (wlk_start (cy_boot cpu0 cpu1 rs0 rs1) d0 2%nat cyg), Sf.
  split_and!; [exact Hrun|exact Himg|exact Hpst|exact Hdv|].
  rewrite -/(cd_end (cst_c Sf)) -/(cd_log_end (cst_c Sf)).
  by apply log_of_of_pfx.
Qed.

(* ====================================================================== *)
(** * 7. AUDIT *)

Print Assumptions qconf_hemit.
Print Assumptions qconf_hemit_seg.
Print Assumptions qconf_seg_data.
Print Assumptions src_in_log_of_pfx'.
Print Assumptions wcpolp_at.
Print Assumptions cpolp_of_align.
Print Assumptions hemit_phart.
Print Assumptions hemit_single_cblk.
Print Assumptions wpol_pins_store.
Print Assumptions wpol_exit_at_zero.
Print Assumptions walk_seg_data_pins.
Print Assumptions walk_seg_data_exit_at_zero.
Print Assumptions qconf_seg_take.
Print Assumptions cyg_wQ_seg1.
Print Assumptions cyg_wnw_seg1.
Print Assumptions cyg_ctx0.
Print Assumptions cyg_wwit_site00.
Print Assumptions cyg_wQ_seg0.
Print Assumptions cyg_step0_generic.
Print Assumptions walk_seg_data_of_qconf.
Print Assumptions walk_supply_of_qconf.
Print Assumptions xv6_rvwmo_safe_modulo_l2.
Print Assumptions xv6_rvwmo_safe_modulo_l2'.
Print Assumptions cyg_W_poloc'.
Print Assumptions cyg_wubA.
Print Assumptions cyg_gwrow.
Print Assumptions cyg_wsite_supply.
Print Assumptions cyg_wsupply.
Print Assumptions cyg_walk'.

(* ====================================================================== *)
(** * 8. THE LEDGER AFTER THIS LEAF

    DELIVERED here:

      - §1 the EMISSION per walk state, from [gdexec_qconf] alone
        ([qconf_seg_data] / [qconf_seg_take]: the row's [hart_conf]
        derivation, split at [k0] and after the exit write by [hemit_app],
        in the residue's own [pre ++ [store]] shape, with the prefix kept as
        the [take]/[drop] the site data index into).
      - §3 the RMW policy pointwise ([wcpolp_at], [cpolp_of_align]), with
        [src_in_log_of_pfx'] generalising the log-decided source fact from
        [LLoad] to [lb_rd] so it fires at an [LRmw] too.
      - §4.1–§4.3 THE REFUTATION OF THE OLD SHAPE, kept machine-checked
        against [WeakRvwmoWalk.wpol_flat] /
        [WeakRvwmoProgress.walk_seg_data_flat]: a policy quantified over
        every context candidate pins the segment's exit store to ROW
        POSITION 0.
      - §5 the REPAIRED residue supplied from the bundle
        ([walk_seg_data_of_qconf]) under one named per-state datum
        [wseg_supply], and the capstone [xv6_rvwmo_safe_modulo_l2] at
        (R-1) [l2_claim] plus that datum.

    WHAT §2 BECAME.  The read/register policy at an ALIGNED candidate moved
    into [WeakRvwmoWalk] §4.0c, where — the policy now being indexed by row
    position and the alignment being part of the carried context [wctx] —
    it DISCHARGES the policy outright ([WeakRvwmoWalk.wpol_of_sites]).  So
    (W-1) is closed, and what [walk_seg_data'] still asks per state is the
    EMISSION and the SITE DATA.

    THAT OBSTRUCTION IS FIXED (§6.2).  [WeakRvwmoCert3.cpol_ctx] no longer
    asserts [¬ W] at the candidate's own position — the clause is a PREMISE
    of [cpol_read] (the TRUE-read case), and a witness position is served
    by the latest-read route ([WeakRvwmoCert2.cert_read_witness] at
    [WeakRvwmoCert.latest_read_lbl], with the block RE-TIMESTAMPED by
    [WeakRvwmoCert2.cblk_load_retime]).  What that route costs, and where
    it is paid, is [WeakRvwmoWalk.wwit_site]: at a witness the graph's read
    must be plain, its footprint must exist at the candidate's latest
    source, and its VALUES must be the candidate's latest bytes — because
    [lbl_reidx] frees the read INDICES and nothing else.  All three are
    functions of [G] and the write count, so they are SITE data like the
    rest; at [WeakRvwmoCycWit.cyg] they compute ([cyg_wwit_site00]).

    THAT IS NOW CLOSED, in [WeakRvwmoWalk] §4.5–§4.6.  [wlk_inv'] carries
    the frozen set's [ctrace_prefix], every hart's emission state with the
    walk state's process identified with it, and the row-position boundary;
    [wlk_step'_of_supply] derives the whole per-state datum from a
    per-GRAPH one ([wsupply]).  §5.5's [xv6_rvwmo_safe_modulo_l2'] is the
    capstone at that residue, and §6.3's [cyg_walk'] is the acceptance
    test: [WeakRvwmoCycWit.cyg_walk]'s conclusion, both steps, out of the
    generic engine, with no candidate, block, process supply or segment
    built by hand.

    WHAT THE RESIDUE STILL NAMES, and why each is honest.  [wsupply] is
    [gwrow_gmo] (one hart's writes reach the log in program order — NOT
    [grule14], which [cyg] refutes), the booted-hart bounds, [W]'s two side
    conditions, and [wsite_supply] (per position: RMW-freedom and the
    classification).  RMW-freedom is the one clause that is not merely a
    choice of [W]: an [LRmw] exit needs [wcpolp_at]/[cpolp_of_align] (§3)
    wired into [wQ'], which is a separate, priced item. *)
