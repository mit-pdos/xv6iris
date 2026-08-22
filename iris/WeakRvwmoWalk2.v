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

    §4  THE OBSTRUCTION (item 4).  [WeakRvwmoWalk.wpol] quantifies over
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

(** Hart [x]'s row, as a list; [gx_lbl] is its lookup. *)
Definition qrow (G : gexec) (x : agent) : list lbl :=
  default [] (gx_prog G !! x).

Lemma qrow_lbl (G : gexec) (x : agent) (k : nat) :
  gx_lbl G (x, k) = qrow G x !! k.
Proof. rewrite /gx_lbl /qrow /=. by destruct (gx_prog G !! x). Qed.

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
Lemma seg_split_exit (row : list lbl) (k0 kz : nat) (lb : lbl) :
  (k0 ≤ kz)%nat → row !! kz = Some lb →
  take (S kz - k0) (drop k0 row) = take (kz - k0) (drop k0 row) ++ [lb].
Proof.
  intros Hle Hkz.
  have Hs : (S kz - k0)%nat = S (kz - k0)%nat by lia.
  rewrite Hs. apply take_S_r. rewrite lookup_drop.
  by replace (k0 + (kz - k0))%nat with kz by lia.
Qed.

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
(** * 2. THE READ/REGISTER POLICY, POINTWISE

    [WeakRvwmoWalk.wpol] is asked at a CANDIDATE and a LABEL; everything it
    must deliver about the label — [mstep_ok] and the classification
    [wcls_at] — is about [G]'s label AT THE CANDIDATE'S OWN POSITION
    [gcnt x (cd_tr c0)].  This section proves the policy at exactly the
    pairs where the two agree ([wsite_ok] below), which is every pair the
    certification iteration actually visits.  §4 is about the pairs it does
    not.

    The register half is free at an EMPTY taint set: [rds_ok (λ n, n ∉ [])]
    holds of every read list, so [cert_block_mirror] re-runs the block from
    the certified register file step for step and the emitted label does
    not move at all — [lbl_reidx] is [lbl_reidx_refl] and no re-timing is
    needed, because a log-decided non-witness read's sources ARE the
    candidate's. *)

(** THE SITE DATUM: [G]'s label at row position [p], the pointwise form of
    the log-decided classification ("this read's sources are in the log",
    "this write is the log's next entry"), and RMW-freedom (the fused pair
    is §3's business). *)
Definition wsite_ok (G : gexec) (n : nat) (x : agent) (p : nat) (lb : lbl)
    : Prop :=
  gx_lbl G (x, p) = Some lb ∧
  wsrc_le G n (x, p) ∧
  (lb_is_w lb = true → gwix G (x, p) = S n) ∧
  lb_rmwfree lb.

(** ** 2.1 The three [mstep_ok] routes, at an aligned candidate *)
Theorem wsite_mstep_ok (G : gexec) (n : nat) (x : agent) (c0 : cand)
    (lb : lbl) :
  rvwmo_minus_consistent G →
  W_poloc_closed G (wwit G n) →
  cd_img c0 = gx_img G →
  wlog_pfx G n (cd_log_end c0) →
  cpol_ctx G (wwit G n) x c0 →
  wsite_ok G n x (gcnt x (cd_tr c0)) lb →
  mstep_ok (cand_last_st c0) x lb.
Proof.
  intros Hcons Hpc Himg Hpfx Hctx (Hl & Hle & _ & Hrmw).
  pose proof Hcons as (Hwf & _ & Hlv & _).
  destruct lb as [aq base ts vs|rl base vs kc|pr pw sr sw|aq rl base ts rvs wvs kc].
  - (* THE IN-LOG READ: [cpol_read], with NO floor obligation *)
    apply (cpol_read G (wwit G n) x c0 aq base ts vs Hcons Hpc Hctx Hl).
    apply (src_in_log_of_pfx G n c0 (x, gcnt x (cd_tr c0)) aq base ts vs
             Hlv Himg Hpfx Hl (gshape G Hwf _ _ Hl) Hle).
  - (* THE STORE *)
    apply cert_write_ok. exact (gshape G Hwf _ _ Hl).
  - (* THE FENCE *)
    apply cert_fence_ok.
  - (* THE FUSED RMW is §3's *)
    by destruct Hrmw.
Qed.

(** ** 2.2 The policy, at an aligned candidate *)
Theorem wblk_pol_at (G : gexec) (n : nat) (x : agent) (cpu : CPU)
    (d0 : dev_state) (c0 : cand) (ws : wstate) (lb : lbl) (l : wlabel)
    (rds : list wreg) (wrs : list register) (m : M unit) (rs1 rs2 : regstate)
    (fn : ofence) (ib : oib32) (m' : M unit) (rs1' : regstate)
    (fn' : ofence) (ib' : oib32) :
  rvwmo_minus_consistent G →
  W_poloc_closed G (wwit G n) →
  cd_img c0 = gx_img G →
  wlog_pfx G n (cd_log_end c0) →
  cpol_ctx G (wwit G n) x c0 →
  wsite_ok G n x (gcnt x (cd_tr c0)) lb →
  dreg_agree (λ nn, nn ∉ []) rs1 rs2 →
  cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
  ∃ (lb' : lbl) (l' : wlabel) (rds' : list wreg) (wrs' : list register)
    (rs2' : regstate),
    cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m' rs2' fn' ib' ∧
    mstep_ok (cand_last_st c0) x lb' ∧
    lbl_reidx lb lb' ∧
    wcls_at G (wwit G n) x c0 lb' ∧
    dreg_agree (λ nn, nn ∉ []) rs1' rs2'.
Proof.
  intros Hcons Hpc Himg Hpfx Hctx Hsite Hag Hblk.
  destruct (cert_block_mirror (λ nn, nn ∉ []) cpu d0 ws lb l rds wrs
              m rs1 fn ib m' rs1' fn' ib' rs2 Hblk
              (λ nn _, not_elem_of_nil nn) Hag) as (rs2' & Hblk2 & Hag2).
  exists lb, l, rds, wrs, rs2'.
  destruct Hctx as (ev & Hgt & Hub & HnW).
  destruct Hsite as (Hl & Hle & Hix & Hrmw).
  split_and!.
  - exact Hblk2.
  - apply (wsite_mstep_ok G n x c0 lb Hcons Hpc Himg Hpfx);
      [by exists ev|by split_and!].
  - apply lbl_reidx_refl.
  - by apply (wcls_of_pfx G n x c0 lb).
  - exact Hag2.
Qed.

(** ** 2.3 [wpol], from the ALIGNMENT

    The alignment is what [WeakRvwmoWalk.wpol] does not say and cannot say:
    that the candidate it is asked at and the label it is asked about name
    the SAME row position.  §4 shows the gap is not a formality. *)
Definition walign (G : gexec) (n : nat) (x : agent) (Q : lbl → Prop)
    : Prop :=
  ∀ (c0 : cand) (lb : lbl),
    srvwmo_consistent c0 → cpol_ctx G (wwit G n) x c0 → Q lb →
    cd_img c0 = gx_img G ∧ wlog_pfx G n (cd_log_end c0) ∧
    wsite_ok G n x (gcnt x (cd_tr c0)) lb.

Theorem wpol_of_align (G : gexec) (n : nat) (x : agent) (cpu : CPU)
    (d0 : dev_state) (Q : lbl → Prop) :
  rvwmo_minus_consistent G →
  W_poloc_closed G (wwit G n) →
  walign G n x Q →
  wpol G (wwit G n) x cpu d0 [] Q.
Proof.
  intros Hcons Hpc Hal c0 ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib'
    Hc Hctx HQ _ Hag Hblk.
  destruct (Hal c0 lb Hc Hctx HQ) as (Himg & Hpfx & Hsite).
  exact (wblk_pol_at G n x cpu d0 c0 ws lb l rds wrs m rs1 rs2 fn ib m'
           rs1' fn' ib' Hcons Hpc Himg Hpfx Hctx Hsite Hag Hblk).
Qed.

(* ====================================================================== *)
(** * 3. THE FUSED RMW's POLICY, POINTWISE

    [WeakRvwmoCert3.cpolp] is [wpol]'s twin for the [HEpair] block, and it
    is DISCHARGED the same way: the untainted mirror ([cert_block_pair_mirror])
    plus §4.3's admissibility ([cert_rmw_ok]), whose only real input is
    "the RMW's read sources are in the log" — which for an RMW is not an
    extra assumption but a consequence of [gatomicity] once the log's next
    entry is the RMW's own write ([cert_rmw_latest], used inside
    [cert_rmw_ok]).  [cpolp_of_rmwfree] remains the RMW-free instance. *)

(** [src_in_log_of_pfx] does not fire at an RMW — it is stated at [LLoad].
    The same proof at [lb_rd] covers both. *)
Theorem src_in_log_of_pfx' (G : gexec) (n : nat) (c : cand) (e : geid)
    (l : lbl) (base : Z) (ts : list nat) (vs : list (bv 8)) :
  gload_value G →
  cd_img c = gx_img G →
  wlog_pfx G n (cd_log_end c) →
  gx_lbl G e = Some l →
  lb_rd l = Some (base, ts, vs) →
  length vs = length ts →
  (∀ (j : nat) t, ts !! j = Some t → (t ≤ n)%nat) →
  src_in_log c base ts vs.
Proof.
  intros Hlv Himg [Hlen Hpfx] Hl Hrd Hlenv Hle.
  split; [exact Hlenv|]. intros j t v Hj Hv.
  have Hrb : greads_byte G e (WeakAxiomatic.acc_addr base j) t v
    by (exists l, base, ts, vs, j).
  destruct (Hlv _ _ _ _ Hrb) as [Hval _].
  have Ht : (t ≤ n)%nat := Hle j t Hj.
  destruct t as [|t'].
  - by rewrite log_byte_0 Himg.
  - destruct Hval as (w & Hw & Hwb & _).
    rewrite log_byte_S.
    have Hlt : (t' < n)%nat by lia.
    rewrite -(Hpfx t' w Hlt Hw).
    destruct (gmsg G w) as [mm|] eqn:Hm.
    + rewrite /=. by apply (gmsg_byte G w _ v mm).
    + exfalso. destruct Hwb as (l0 & base' & vs' & j' & Hl0 & Hwr & _).
      by rewrite /gmsg Hl0 Hwr in Hm.
Qed.

(** THE RMW SITE DATUM. *)
Definition wrmw_site (G : gexec) (n : nat) (x : agent) (p : nat) (lb : lbl)
    : Prop :=
  gx_lbl G (x, p) = Some lb ∧
  (∀ (base : Z) (ts : list nat) (vs : list (bv 8)),
     lb_rd lb = Some (base, ts, vs) →
     ∀ (j : nat) t, ts !! j = Some t → (t ≤ n)%nat) ∧
  gwix G (x, p) = S n.

Theorem wcpolp_at (G : gexec) (n : nat) (x : agent) (cpu : CPU)
    (d0 : dev_state) (c0 : cand) (ws : wstate) (lb : lbl)
    (l1 l2 : wlabel) (rds : list wreg) (wrs : list register)
    (m : M unit) (rs1 rs2 : regstate) (fn : ofence) (ib : oib32)
    (m' : M unit) (rs1' : regstate) (fn' : ofence) (ib' : oib32) :
  rvwmo_minus_consistent G →
  cd_img c0 = gx_img G →
  wlog_pfx G n (cd_log_end c0) →
  srvwmo_consistent c0 →
  cpol_ctx G (wwit G n) x c0 →
  wrmw_site G n x (gcnt x (cd_tr c0)) lb →
  dreg_agree (λ nn, nn ∉ []) rs1 rs2 →
  cblkp cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' →
  ∃ rs2',
    cblkp cpu d0 ws lb l1 l2 rds wrs m rs2 fn ib m' rs2' fn' ib' ∧
    mstep_ok (cand_last_st c0) x lb ∧
    wcls_at G (wwit G n) x c0 lb ∧
    dreg_agree (λ nn, nn ∉ []) rs1' rs2'.
Proof.
  intros Hcons Himg Hpfx Hc Hctx (Hl & Hbnd & Hix) Hag Hblk.
  pose proof Hcons as (Hwf & _ & Hlv & _).
  destruct (cert_block_pair_mirror (λ nn, nn ∉ []) cpu d0 ws lb l1 l2 rds wrs
              m rs1 fn ib m' rs1' fn' ib' rs2 Hblk
              (λ nn _, not_elem_of_nil nn) Hag) as (rs2' & Hblk2 & Hag2).
  have Hrmw : ¬ lb_rmwfree lb
    := cblkp_rmw cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' Hblk.
  destruct lb as [aq base ts vs|rl base vs kc|pr pw sr sw
                 |aq rl base ts rvs wvs kc]; [by destruct (Hrmw I)..|].
  destruct Hctx as (ev & Hgt & Hub & HnW).
  destruct (gshape G Hwf _ _ Hl) as (Hne & Hlenw & Hlenr).
  have Hlenlog : length (cd_log_end c0) = n by (destruct Hpfx as [H _]; exact H).
  have Hsrc : src_in_log c0 base ts rvs.
  { apply (src_in_log_of_pfx' G n c0 (x, gcnt x (cd_tr c0)) _ base ts rvs
            Hlv Himg Hpfx Hl eq_refl Hlenr).
    intros j t Hj. by apply (Hbnd base ts rvs eq_refl j t). }
  exists rs2'. split_and!.
  - exact Hblk2.
  - apply (cert_rmw_ok G c0 ev (wwit G n) x aq rl base ts rvs wvs kc
             Hcons Hgt Hc Hl ltac:(by rewrite Hix Hlenlog));
      [|exact Hsrc].
    intros j t Hj. rewrite Hlenlog. by apply (Hbnd base ts rvs eq_refl j t).
  - apply (wcls_of_pfx G n x c0 _ Hpfx Hl HnW). intros _. exact Hix.
  - exact Hag2.
Qed.

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
  cpolp x cpu d0 [] (cpol_ctx G (wwit G n) x) (wcls_at G (wwit G n) x) Q.
Proof.
  intros Hcons Hal c0 ws lb l1 l2 rds wrs m rs1 rs2 fn ib m' rs1' fn' ib'
    Hc Hctx HQ _ Hag Hblk.
  have Hrmw : ¬ lb_rmwfree lb
    := cblkp_rmw cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' Hblk.
  destruct (Hal c0 lb Hc Hctx HQ Hrmw) as (Himg & Hpfx & Hsite).
  exact (wcpolp_at G n x cpu d0 c0 ws lb l1 l2 rds wrs m rs1 rs2 fn ib m'
           rs1' fn' ib' Hcons Himg Hpfx Hc Hctx Hsite Hag Hblk).
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
  wpol G (wwit G n) x cpu d0 T Q →
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
  wpol G (wwit G n) x cpu d0 T Q →
  ¬ wwit G n (x, 0%nat) →
  Q (WeakAxiomatic.LStore rl base vs kc) →
  w_relp (ms_ws (cand_last_st (Cand (gx_img G) [])) x) = w_relp ws →
  dreg_agree (λ nn, nn ∉ T) rs1 rs2 →
  cblk cpu d0 ws (WeakAxiomatic.LStore rl base vs kc) l rds wrs
    m rs1 fn ib m' rs1' fn' ib' →
  gx_lbl G (x, 0%nat) = Some (WeakAxiomatic.LStore rl base vs kc).
Proof.
  intros Hpol HnW HQ Hrelp Hag Hblk.
  rewrite -(empty_cand_gcnt G x).
  apply (wpol_pins_store G n x cpu d0 T Q _ ws rl base vs kc l rds wrs
           m rs1 rs2 fn ib m' rs1' fn' ib' Hpol (empty_cand_consistent G)
           (cpol_ctx_empty G (wwit G n) x HnW) HQ Hrelp Hag Hblk).
Qed.

(** ** 4.3 … hence [walk_seg_data] itself pins the exit write

    [walk_seg_data] hands out, per walk state: the emission of
    [pre ++ [store]], [Forall Q] of it, and [wpol] at that [Q].  §4.0 turns
    the emission's LAST block into a [cblk] (the register agreement is
    reflexivity there — [dreg_agree_refl]), so §4.1 applies verbatim. *)
Theorem walk_seg_data_pins (boot : agent → pexv6) (d0 : dev_state) (N : nat)
    (G : gexec) :
  walk_seg_data boot d0 N G →
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
  walk_seg_data boot d0 N G →
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
  have HnW : ¬ wwit G n (x, 0%nat) := wrow_no_wit G x n 0%nat Hrow.
  rewrite -(empty_cand_gcnt G x).
  apply (Hpin (Cand (gx_img G) []) (empty_cand_consistent G)
           (cpol_ctx_empty G (wwit G n) x HnW) Hrelp0).
Qed.

(** ** 4.4 THE REPAIR, stated: the POSITION-INDEXED policy

    The disease is one and the same in all three places the residue
    over-quantifies — [wpol]/[WeakRvwmoCert3.cert_segment']'s [Hpol'] over
    ALL context candidates, [WeakRvwmoWalk.wrow_in_log]/[wnw] over ALL row
    positions, and [walk_seg_data] over ALL [wlk_inv] states — and the cure
    is the same: index the policy by the ROW POSITION the iteration has
    reached, and let the invariant pin the candidate's own position to it.
    [wpol_ix] is that shape, and §2 discharges it outright. *)
Definition wpol_ix (G : gexec) (n : nat) (x : agent) (cpu : CPU)
    (d0 : dev_state) (row : list lbl) (k0 : nat) : Prop :=
  ∀ (i : nat) (lb : lbl) (c0 : cand) (ws : wstate) (l : wlabel)
    (rds : list wreg) (wrs : list register) (m : M unit)
    (rs1 rs2 : regstate) (fn : ofence) (ib : oib32) (m' : M unit)
    (rs1' : regstate) (fn' : ofence) (ib' : oib32),
    row !! i = Some lb →
    gcnt x (cd_tr c0) = (k0 + i)%nat →
    cd_img c0 = gx_img G →
    wlog_pfx G n (cd_log_end c0) →
    srvwmo_consistent c0 →
    cpol_ctx G (wwit G n) x c0 →
    dreg_agree (λ nn, nn ∉ []) rs1 rs2 →
    cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ (lb' : lbl) (l' : wlabel) (rds' : list wreg) (wrs' : list register)
      (rs2' : regstate),
      cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m' rs2' fn' ib' ∧
      mstep_ok (cand_last_st c0) x lb' ∧
      lbl_reidx lb lb' ∧
      wcls_at G (wwit G n) x c0 lb' ∧
      dreg_agree (λ nn, nn ∉ []) rs1' rs2'.

Theorem wpol_ix_of_sites (G : gexec) (n : nat) (x : agent) (cpu : CPU)
    (d0 : dev_state) (row : list lbl) (k0 : nat) :
  rvwmo_minus_consistent G →
  W_poloc_closed G (wwit G n) →
  (∀ (i : nat) (lb : lbl), row !! i = Some lb →
     wsite_ok G n x (k0 + i)%nat lb) →
  wpol_ix G n x cpu d0 row k0.
Proof.
  intros Hcons Hpc Hsite i lb c0 ws l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib'
    Hi Hpos Himg Hpfx Hc Hctx Hag Hblk.
  apply (wblk_pol_at G n x cpu d0 c0 ws lb l rds wrs m rs1 rs2 fn ib m'
           rs1' fn' ib' Hcons Hpc Himg Hpfx Hctx);
    [rewrite Hpos; by apply Hsite|exact Hag|exact Hblk].
Qed.

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
(** * 5. AUDIT *)

Print Assumptions qconf_hemit.
Print Assumptions qconf_hemit_seg.
Print Assumptions qconf_seg_data.
Print Assumptions wsite_mstep_ok.
Print Assumptions wblk_pol_at.
Print Assumptions wpol_of_align.
Print Assumptions src_in_log_of_pfx'.
Print Assumptions wcpolp_at.
Print Assumptions cpolp_of_align.
Print Assumptions hemit_phart.
Print Assumptions hemit_single_cblk.
Print Assumptions wpol_pins_store.
Print Assumptions wpol_exit_at_zero.
Print Assumptions walk_seg_data_pins.
Print Assumptions walk_seg_data_exit_at_zero.
Print Assumptions wpol_ix_of_sites.

(* ====================================================================== *)
(** * 6. THE LEDGER AFTER THIS LEAF

    DELIVERED, and reusable unchanged by a repaired interface:

      - §1 the EMISSION per walk state, from [gdexec_qconf] alone
        ([qconf_seg_data]: the row's [hart_conf] derivation, split at [k0]
        and after the exit write by [hemit_app], in the residue's own
        [pre ++ [store]] shape).  No progress argument is needed for it:
        the bundle already asserts the whole row is emitted, and
        [WeakRvwmoProgress] §1–§3 are what would be needed only to BUILD
        such a bundle, not to split one.
      - §2 the READ/REGISTER POLICY at an aligned candidate
        ([wblk_pol_at]): [cert_read_in_log'] through [cpol_read] (floor
        free, from [cpol_ctx]) at every read whose sources the log has
        reached, [cert_write_ok] at the exit store, [cert_fence_ok] at a
        fence, [wcls_of_pfx] for the classification, and
        [cert_block_mirror] for the register half at an EMPTY taint set.
      - §3 the RMW policy in the same shape ([wcpolp_at], [cpolp_of_align]),
        with [src_in_log_of_pfx'] generalising the log-decided source fact
        from [LLoad] to [lb_rd] so it fires at an [LRmw] too.

    NOT DELIVERED, and why — the finding.  [walk_seg_data] cannot be
    supplied, for a reason that is not about the kernel or the graph: it
    asks for [wpol], which quantifies over EVERY candidate the
    certification context admits while its classification output speaks
    about that candidate's OWN row position.  §4.1–§4.3 machine-check the
    consequence: a [walk_seg_data] at a walk state forces the segment's
    exit store to be [G]'s label at every context candidate, hence — at the
    empty candidate, a context of every graph where hart [x] has no witness
    at position 0, which [wrow_in_log'] itself guarantees — at ROW POSITION
    0.  Any site whose write is not its hart's first event refutes it.  The
    same over-quantification is in [wrow_in_log] (all row positions rather
    than the segment's) and in [walk_seg_data]'s [∀ St] over [wlk_inv],
    which records the log prefix but not that the state is a CERTIFIED
    prefix of [G] at all — so [cpol_ctx G (wwit G n) x (cst_c St)], a
    conjunct of the residue, is not a consequence of its own hypothesis.

    THE REPAIR, in one line: index the per-block policy by the row position
    ([wpol_ix], §4.4 — discharged here from §2), and strengthen the walk's
    invariant to pin each hart's replayed count to its row position.  That
    is a change to [WeakRvwmoCert3.cert_segment']'s [Hpol'] parameter, to
    [WeakRvwmoCert4.seg_step_of_segment], and to [WeakRvwmoWalk.wlk_inv] —
    not to anything below them, and none of §1–§3 above moves. *)
