(** * WeakRvwmoCert3.v — B2e-3b SLICE 3c(a): THE FLOOR, DISCHARGED

    Design: [claude-notes/design/weak-memory-route-b.md] §4e ("SLICE 3's
    SHAPE"), and [claude-notes/projects/weak-memory-certification.md]'s
    FOURTH-PASS checkpoint item 1.

    WHAT THIS FILE IS.  [WeakRvwmoCert2.cert_segment] certifies a hart's
    segment against a POLICY hypothesis whose read clause owes two things
    ([WeakRvwmoCert2] §7, (O-3)): [src_in_log] (bookkeeping) and
    [floor_ok] — "nothing the agent has already observed overwrites the
    named source" — which is (N-1), the one genuinely semantic debt.
    [WeakRvwmoFloor.floor_of_graph] discharges exactly that obligation, but
    only for a candidate that is a G-TRACE PREFIX: every label is G's own.
    A certified run is NOT that, because a WITNESS read carries the
    candidate log's latest bytes instead of G's.

    THE THREE DELIVERABLES.

    (1) [ctrace_prefix] (§1) and [floor_of_cgraph] / [cert_floor_ok] (§3):
        the CERTIFIED correspondence — [WeakRvwmoFloor.gtrace_prefix] with
        the label clause split in two, G's label at a true position and a
        [WeakRvwmoCert.latest_read_lbl] at a witness — and the floor
        discharge over it.  [cert_read_in_log'] is the payoff in
        [cert_segment]'s own vocabulary: at a TRUE read of hart [i] whose
        source is in the log, [mstep_ok] holds with NO [floor_ok]
        hypothesis.  [cert_segment'] (§3.4) is [cert_segment] restated with
        that policy clause discharged.

    (2) [cblkp] and [cert_block_pair] (§4) — obligation (O-1), the fused
        exclusive pair.  The RMW's read half must name the LATEST message
        ([WeakAxiomatic.rmw_latest]); [cert_rmw_latest] proves it is, from
        [gatomicity] and the log dictionary, so the pair needs no floor
        argument at all ([floor_ok_of_latest]).

    (3) [boundary_reconverge] (§5) — obligation (O-2).  After a witness the
        two runs are at different monad nodes; they re-converge at the next
        instruction BOUNDARY, which is [Interface.Ret tt] — a CONSTANT of
        the monad ([M unit] has one terminal value), so "both reach the
        boundary" already forces the nodes equal.  That both DO reach it is
        the EWPs' progress content and is an explicit hypothesis
        ([at_boundary]); the register-file half is [WeakEvProv]'s
        [taint_closure].

    ------------------------------------------------------------------------
    THE TWO SIDE CONDITIONS A WITNESS COSTS, and how each is handled.

    A witness read is a PLAIN load (never an acquire — [witness_not_aq],
    §1.4: rule 5 orders an acquire before every later memory event of its
    hart, so an acquire cannot be the backward step of a cycle) whose
    timestamps are the candidate log's latest.  It touches exactly two of
    [WeakRvwmoFloor.finv]'s six watermarks:

    (W-a) [coh a'] for each byte [a'] of its own footprint.  This is
          harmless for the floor of a LATER read of a DIFFERENT byte, and
          a later read of the SAME byte is itself a witness — that is
          [W_poloc_closed] (§1.3), stated in graph vocabulary: a same-byte
          po-later read after a witness is a witness.  Since the read
          whose floor is being discharged is TRUE (¬ [W r]), no witness of
          its hart touches its bytes.

    (W-b) [w_vrOld].  A plain load raises it BYTE-AGNOSTICALLY, and
          [w_vrOld] reaches the read floor through a [pr]/[sr] fence
          (rule 4).  So a witness is free UNLESS a publishing fence
          separates it from the read, and when one does, what is owed is
          that the log at the witness's position is gmo-below the read.
          That is [wit_fence_ub] (§2.1) — an explicit hypothesis, GUARDED
          by [WeakRvwmoFloor.fhook], so it costs nothing at a witness with
          no publishing fence after it.  (§4e's five-watermark sketch does
          not mention this arm; it is real, and it is where a witness's
          value can genuinely move a later read's floor.)

    Nothing below is [Admitted] or [Axiom]-ed. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import RiscvModelBytes.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakDeps.
Require Import WeakAxiomatic.
Require Import WeakAxiomatic2.
Require Import WeakAxiomatic3.
Require Import WeakSrvwmoLitmus.
Require Import WeakRvwmoGraph.
Require Import WeakInterp.
Require Import WeakInterpProj.
Require Import RiscvLang.
Require Import WeakLang.
Require Import WeakEvLang.
Require Import WeakEvPf.
Require Import WeakPromise.
Require Import WeakPromiseFact.
Require Import WeakPromiseBridge.
Require Import WeakAxRealize.
Require Import WeakEvInst.
Require Import WeakEvLift.
Require Import WeakEvStarted.
Require Import WeakRvwmoConf.
Require Import WeakRvwmoSupply.
Require Import WeakRvwmoConfWit.
Require Import WeakEvProv.
Require Import WeakRvwmoCert.
Require Import WeakRvwmoFloor.
Require Import WeakRvwmoCert2.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** * 1. THE CERTIFIED CORRESPONDENCE *)

(** ** 1.1 The candidate's own prefix

    A witness's label is computed at the log the candidate had WHEN THE
    WITNESS STEPPED, which is the prefix candidate's [cd_log_end]. *)
Definition cd_pre (c : cand) (p : nat) : cand := Cand (cd_img c) (take p (cd_tr c)).

Lemma cd_pre_img c p : cd_img (cd_pre c p) = cd_img c.
Proof. done. Qed.

Lemma cd_pre_log c p : cd_log_end (cd_pre c p) = cd_log c p.
Proof.
  rewrite /cd_log_end /cd_end /cd_log /=.
  have Hte : take (length (take p (cd_tr c))) (take p (cd_tr c))
           = take p (cd_tr c) by (apply take_ge; lia).
  by rewrite Hte.
Qed.

(** ** 1.2 [ctrace_prefix]

    [WeakRvwmoFloor.gtrace_prefix] with its label clause split.  The LOG
    clauses are verbatim: a witness is a READ, so it contributes no message
    and the log is still exactly the gmo prefix. *)
Record ctrace_prefix (G : gexec) (c : cand) (ev : nat → geid)
    (W : geid → Prop) : Prop := {
  ctp_img : cd_img c = gx_img G;
  ctp_ag  : ∀ p s, cd_tr c !! p = Some s → (ev p).1 = es_ag s;
  ctp_pos : ∀ p s, cd_tr c !! p = Some s →
              (ev p).2 = gcnt (es_ag s) (take p (cd_tr c));
  (* THE LABEL CLAUSE, split.  A TRUE position carries G's own label; a
     WITNESS carries the candidate's latest-source read of the SAME
     footprint, at [aq = false] ([witness_not_aq]).  The clause is ONE
     disjunction rather than two implications so that the replay's case
     split needs no [Decision (W _)]. *)
  ctp_step : ∀ p s, cd_tr c !! p = Some s →
              (¬ W (ev p) ∧ gx_lbl G (ev p) = Some (es_lb s)) ∨
              (W (ev p) ∧
               ∃ (base : Z) (n : nat) (ts0 : list nat) (vs0 : list (bv 8)),
                 gx_lbl G (ev p) = Some (WeakAxiomatic.LLoad false base ts0 vs0) ∧
                 length ts0 = n ∧
                 es_lb s = latest_read_lbl (cd_pre c p) false base n);
  ctp_wix : ∀ p s, cd_tr c !! p = Some s → lb_is_w (es_lb s) = true →
              gwix G (ev p) = S (length (cd_log c p));
  ctp_log : ∀ s : nat, (0 < s)%nat →
              (s ≤ length (cd_log c (length (cd_tr c))))%nat →
              ∃ w, gwrite_at G s = Some w ∧
                   cd_log c (length (cd_tr c)) !! (s - 1)%nat = gwmsg G w;
}.

(** A witness-free certified prefix IS a G-trace prefix, and conversely. *)
Lemma ctrace_prefix_of_gtrace G c ev :
  gtrace_prefix G c ev → ctrace_prefix G c ev (λ _, False).
Proof.
  intros [H1 H2 H3 H4 H5 H6]. split.
  - exact H1.
  - exact H2.
  - exact H3.
  - intros p s Hs. left. split; [intros HF; exact HF|by apply H4].
  - exact H5.
  - exact H6.
Qed.

Lemma gtrace_of_ctrace_prefix G c ev W :
  ctrace_prefix G c ev W → (∀ p, ¬ W (ev p)) → gtrace_prefix G c ev.
Proof.
  intros [H1 H2 H3 H4 H5 H6] Hno. split.
  - exact H1.
  - exact H2.
  - exact H3.
  - intros p s Hs. destruct (H4 p s Hs) as [[_ H]|[HW _]];
      [exact H|by destruct (Hno p)].
  - exact H5.
  - exact H6.
Qed.

(** The two implications the disjunction packs, as usable projections. *)
Lemma ctp_lbl G c ev W p s :
  ctrace_prefix G c ev W → cd_tr c !! p = Some s → ¬ W (ev p) →
  gx_lbl G (ev p) = Some (es_lb s).
Proof.
  intros [_ _ _ H4 _ _] Hs HnW.
  destruct (H4 p s Hs) as [[_ H]|[HW _]]; [exact H|by destruct (HnW HW)].
Qed.

Lemma ctp_wit G c ev W p s :
  ctrace_prefix G c ev W → cd_tr c !! p = Some s → W (ev p) →
  ∃ (base : Z) (n : nat) (ts0 : list nat) (vs0 : list (bv 8)),
    gx_lbl G (ev p) = Some (WeakAxiomatic.LLoad false base ts0 vs0) ∧
    length ts0 = n ∧
    es_lb s = latest_read_lbl (cd_pre c p) false base n.
Proof.
  intros [_ _ _ H4 _ _] Hs HW.
  destruct (H4 p s Hs) as [[HnW _]|[_ H]]; [by destruct (HnW HW)|exact H].
Qed.

Lemma ctp_ev_eq G c ev W p s :
  ctrace_prefix G c ev W → cd_tr c !! p = Some s →
  ev p = (es_ag s, gcnt (es_ag s) (take p (cd_tr c))).
Proof.
  intros [_ Hag Hpos _ _ _] Hs.
  rewrite (surjective_pairing (ev p)) (Hag p s Hs) (Hpos p s Hs) //.
Qed.

(** THE LOG DICTIONARY (both directions), verbatim from
    [WeakRvwmoFloor] — it reads only the two log clauses. *)
Lemma ctp_log_writes G c ev W :
  ctrace_prefix G c ev W →
  ∀ (s : nat) m, (0 < s)%nat →
    cd_log c (length (cd_tr c)) !! (s - 1)%nat = Some m →
    ∀ b, is_Some (msg_byte m b) →
      ∃ w v', gwrite_at G s = Some w ∧ gwrites_byte G w b v'.
Proof.
  intros Hgt s m Hs Hm b [v Hv].
  have Hle : (s ≤ length (cd_log c (length (cd_tr c))))%nat.
  { apply lookup_lt_Some in Hm. lia. }
  destruct Hgt as [_ _ _ _ _ Hlog].
  destruct (Hlog s Hs Hle) as (w & Hw & Heq).
  rewrite Hm in Heq. symmetry in Heq. rewrite /gwmsg in Heq.
  destruct (gx_lbl G w) as [l|] eqn:Hl; [|done].
  destruct (lb_wr l) as [[base vs]|] eqn:Hwr; [|done].
  injection Heq as <-. rewrite /msg_byte /= in Hv.
  case_bool_decide as Hb; [|done].
  exists w, v. split; [exact Hw|].
  exists l, base, vs, (Z.to_nat (b - base)). split_and!;
    [exact Hl|exact Hwr|exact Hv|].
  rewrite /WeakAxiomatic.acc_addr Z2Nat.id; lia.
Qed.

Lemma ctp_log_byte G c ev W :
  ctrace_prefix G c ev W →
  ∀ (s : nat) w b v, (0 < s)%nat →
    (s ≤ length (cd_log c (length (cd_tr c))))%nat →
    gwrite_at G s = Some w → gwrites_byte G w b v →
    log_byte (cd_img c) (cd_log c (length (cd_tr c))) s b = Some v.
Proof.
  intros Hgt s w b v Hs Hle Hw (l & base & vs & j & Hl & Hwr & Hj & Hb).
  destruct Hgt as [_ _ _ _ _ Hlog].
  destruct (Hlog s Hs Hle) as (w' & Hw' & Heq).
  rewrite Hw in Hw'. injection Hw' as <-.
  rewrite /gwmsg Hl Hwr in Heq.
  destruct s as [|n]; [lia|]. rewrite log_byte_S.
  replace (S n - 1)%nat with n in Heq by lia. rewrite Heq /= /msg_byte /=.
  case_bool_decide as Hba; last first.
  { exfalso. apply Hba. rewrite -Hb /WeakAxiomatic.acc_addr. lia. }
  rewrite -Hb.
  replace (Z.to_nat (WeakAxiomatic.acc_addr base j - base)) with j by (rewrite /WeakAxiomatic.acc_addr; lia).
  exact Hj.
Qed.

(** ** 1.3 [W_poloc_closed]

    THE SIDE CONDITION (W-a): after a witness, a same-byte po-later READ of
    the same hart is itself a witness.  It is poloc's own content — such a
    read cannot be certified against G's source once the earlier one was
    substituted — and it is stated purely on the GRAPH, so it is a property
    of the witness SET, checkable where the set is chosen (B2e-3c). *)
Definition W_poloc_closed (G : gexec) (W : geid → Prop) : Prop :=
  ∀ e1 e2 a, W e1 → gpo G e1 e2 → gaccesses G e1 a → gaccesses G e2 a →
             glbl_is G e2 lb_is_r → W e2.

(** ** 1.4 [witness_not_aq]

    WHY [ctp_wit] MAY WRITE [false]: an acquire read is ordered — by
    riscv.cat's rule 5, [WeakRvwmoFloor.gacq_gmo] — before EVERY later
    memory event of its own hart, so it is never the BACKWARD step of a
    cycle, which is what a witness is (§4e: the certification starts at a
    backward step [(r, z)] with [gmo_lt G z r] and [z] po-after [r]).
    [gmo_lt] is a strict position order, hence asymmetric. *)
Lemma witness_not_aq G (e z : geid) :
  gppo_gmo G → gpo G e z → WeakRvwmoGraph.gmem G z →
  glbl_is G e lb_is_r → glbl_is G e lb_aq →
  ¬ gmo_lt G z e.
Proof.
  intros Hppo Hpo Hmem Hr Haq Hlt.
  have Hlt2 : gmo_lt G e z := gacq_gmo G Hppo e z Hpo Hr Haq Hmem.
  destruct Hlt as (_ & _ & H1). destruct Hlt2 as (_ & _ & H2). lia.
Qed.

(* ====================================================================== *)
(** * 2. [cinv]: THE FLOOR INVARIANT, TOLERATING WITNESSES

    [WeakRvwmoFloor.finv] is kept VERBATIM as the invariant — [cinv] is
    [finv], and that is the point: a witness preserves it.  What the file
    adds is the WITNESS STEP ([cinv_step_wit]) beside
    [WeakRvwmoFloor.finv_step], and the replay that dispatches on the
    position's kind ([cinv_replay]). *)

Notation cinv := finv.

(** ** 2.1 [wit_fence_ub] — the side condition (W-b)

    A witness raises [w_vrOld] to the log's latest, byte-agnostically, and
    [w_vrOld] reaches a later read's floor only through a [pr]/[sr] fence
    ([WeakRvwmoFloor.fhook], rule 4).  So the obligation is GUARDED: a
    witness with no publishing fence between it and [r] owes nothing. *)
Definition wit_fence_ub (G : gexec) (c : cand) (ev : nat → geid)
    (W : geid → Prop) (r : geid) : Prop :=
  ∀ p s, cd_tr c !! p = Some s → W (ev p) → (ev p).1 = r.1 →
    fhook G r (S (ev p).2) true → gvis_ub G r (length (cd_log c p)).

(** ** 2.2 THE WITNESS STEP

    Two of the six clauses move, and each is paid for once: [coh a] does
    NOT move because the witness's footprint misses [a] (W-a, [Hdisj]), and
    [w_vrOld] moves only under [fhook] (W-b, [Hub]).  [w_vrNew] is untouched
    because a witness is PLAIN ([witness_not_aq]) — that is the whole
    content of the [aq = false] in [ctp_wit]. *)
Lemma cinv_step_wit G (Hwf : gwf G) (Hppo : gppo_gmo G) (Hlv : gload_value G)
    (r : geid) (a : Z) (Hrr : glbl_is G r lb_is_r) (Hra : gaccesses G r a)
    (k : nat) (ws : wstate) (base : Z) (ts : list nat) (vs : list (bv 8))
    (tw : nat) :
  (∀ (j : nat) t, ts !! j = Some t → WeakAxiomatic.acc_addr base j ≠ a) →
  (fhook G r (S k) true → ∀ (j : nat) t, ts !! j = Some t → gvis_ub G r t) →
  cinv G r a k ws →
  cinv G r a (S k) (lstep tw ws (WeakAxiomatic.LLoad false base ts vs)).
Proof.
  intros Hdisj Hub (Hfw & Hcoh & Hrn & Hrel & Hro & Hwo).
  have Hcl : maxcl (gvis_ub G r) := gvis_ub_maxcl G r.
  have Hvpre : gvis_ub G r (load_vpre ws false).
  { rewrite /load_vpre. apply maxcl_max; [exact Hcl|exact Hrn|apply gvis_ub_0]. }
  simpl. split_and!.
  - by apply fwd0_load_post_run.
  - apply load_run_coh; [exact Hcl|exact Hfw|exact Hcoh|exact Hvpre|].
    intros j t Hj Hja. exfalso. exact (Hdisj j t Hj Hja).
  - rewrite load_run_vrNew_plain. exact Hrn.
  - rewrite load_run_vRel. intros Hah. by apply Hrel, ahook_S.
  - intros Hfh. apply load_run_vrOld;
      [exact Hcl|exact Hfw|by apply Hro, fhook_S|exact Hvpre|].
    intros j t Hj. by apply (Hub Hfh j t).
  - rewrite load_run_vwOld. intros Hfh. by apply Hwo, fhook_S.
Qed.

(** ** 2.3 THE REPLAY

    [WeakRvwmoFloor.finv_replay] with one extra case split: a TRUE position
    steps by [finv_step] (G's own label), a WITNESS by [cinv_step_wit]. *)
Lemma cinv_replay G (Hwf : gwf G) (Hppo : gppo_gmo G) (Hlv : gload_value G)
    (r : geid) (a : Z) (Hrr : glbl_is G r lb_is_r) (Hra : gaccesses G r a)
    (c : cand) (ev : nat → geid) (W : geid → Prop) (p : nat) :
  ctrace_prefix G c ev W →
  W_poloc_closed G W →
  wit_fence_ub G c ev W r →
  ¬ W r →
  (gcnt r.1 (cd_tr c) ≤ r.2)%nat →
  (p ≤ length (cd_tr c))%nat →
  cinv G r a (gcnt r.1 (take p (cd_tr c))) (ms_ws (stt (cand_exec c) p) r.1).
Proof.
  intros Hgt Hpc Hwub HnW Hcnt.
  pose proof Hgt as Hgt0.
  destruct Hgt0 as [Himg Hagf Hposf Hstepf Hwixf Hlogf].
  induction p as [|p IH]; intros Hp.
  - have Hs0 : stt (cand_exec c) 0%nat = cand_init c
      by (apply stt_lookup; exact (replay_0 (cand_init c) (cd_tr c))).
    rewrite Hs0 take_0 /=. apply finv_init.
  - destruct (lookup_lt_is_Some_2 (cd_tr c) p ltac:(lia)) as [s Hs].
    have Hlog : ms_log (stt (cand_exec c) p) = cd_log c p.
    { rewrite -(cand_elog c p ltac:(lia)) //. }
    rewrite (cand_next c p s Hs).
    destruct (decide (es_ag s = r.1)) as [Hag|Hag]; last first.
    { rewrite (gcnt_step_ne r.1 (cd_tr c) p s Hs Hag).
      rewrite (mnext_ws_ne (stt (cand_exec c) p) (es_ag s) (es_lb s) r.1
                (λ H, Hag (eq_sym H))).
      apply IH. lia. }
    rewrite (gcnt_step_eq r.1 (cd_tr c) p s Hs Hag) Hag mnext_ws_eq.
    have Hev : ev p = (r.1, gcnt r.1 (take p (cd_tr c))).
    { rewrite (ctp_ev_eq G c ev W p s Hgt Hs) Hag //. }
    have Hklt : (gcnt r.1 (take p (cd_tr c)) < r.2)%nat.
    { have Hle := gcnt_take_le r.1 (cd_tr c) (S p).
      rewrite (gcnt_step_eq r.1 (cd_tr c) p s Hs Hag) in Hle. lia. }
    have HIH := IH ltac:(lia).
    destruct (Hstepf p s Hs) as [[HnWp Hlblp]|[HW Hwitp]]; last first.
    + (* ------------------------- A WITNESS ------------------------- *)
      destruct Hwitp as (base & n & ts0 & vs0 & Hlg & Hn & Hlb).
      have Hlen0 : length vs0 = length ts0 := gshape G Hwf _ _ Hlg.
      rewrite Hlb /latest_read_lbl.
      apply (cinv_step_wit G Hwf Hppo Hlv r a Hrr Hra);
        [| |exact HIH].
      * (* (W-a): the witness's footprint misses [a] *)
        intros j t Hj Heq.
        destruct (lrd_ts_lookup (cd_pre c p) base n j t Hj) as (Hjn & _).
        have Hjt : (j < length ts0)%nat by lia.
        destruct (lookup_lt_is_Some_2 ts0 j Hjt) as [t0 Ht0].
        destruct (lookup_lt_is_Some_2 vs0 j ltac:(lia)) as [v0 Hv0].
        have Hrbp : greads_byte G (ev p) (WeakAxiomatic.acc_addr base j) t0 v0.
        { by exists (WeakAxiomatic.LLoad false base ts0 vs0), base, ts0, vs0, j. }
        have Hacc : gaccesses G (ev p) a.
        { right. exists t0, v0. by rewrite -Heq. }
        have Hpo : gpo G (ev p) r.
        { rewrite /gpo. split_and!.
          - rewrite Hev //.
          - rewrite Hev /=. exact Hklt.
          - by exists (WeakAxiomatic.LLoad false base ts0 vs0).
          - destruct Hrr as (l' & Hl' & _). by exists l'. }
        exact (HnW (Hpc (ev p) r a HW Hpo Hacc Hra Hrr)).
      * (* (W-b): the fence-guarded log bound *)
        intros Hfh j t Hj.
        destruct (lrd_ts_lookup (cd_pre c p) base n j t Hj) as (_ & ->).
        rewrite cd_pre_log.
        apply (gvis_ub_down G r _ (length (cd_log c p)));
          [apply latest_ts_le|].
        apply (Hwub p s Hs HW);
          [rewrite Hev //|rewrite Hev /=; exact Hfh].
    + (* -------------------------- A TRUE STEP ---------------------- *)
      apply (finv_step G Hwf Hppo Hlv r a Hrr Hra
               (gcnt r.1 (take p (cd_tr c))) (es_lb s));
        [exact Hklt| | |exact HIH].
      * rewrite -Hev. exact Hlblp.
      * intros Hw. rewrite -Hev Hlog. by apply (Hwixf p s Hs Hw).
Qed.

(** ** 2.4 THE FLOOR, over a certified prefix *)
Theorem floor_of_cgraph G c ev W (i : agent) (r : geid) (a : Z) (t : nat)
    (v : bv 8) (aq : bool) :
  rvwmo_minus_consistent G →
  ctrace_prefix G c ev W →
  W_poloc_closed G W →
  wit_fence_ub G c ev W r →
  ¬ W r →
  r = (i, gcnt i (cd_tr c)) →
  greads_byte G r a t v →
  (aq = true → glbl_is G r lb_aq) →
  ¬ writes_in (cd_log c (length (cd_tr c))) a t
      (Nat.max (load_vpre (ms_ws (stt (cand_exec c) (length (cd_tr c))) i) aq)
               (coh (ms_ws (stt (cand_exec c) (length (cd_tr c))) i) a)).
Proof.
  intros (Hwf & Hppo & Hlv & _) Hgt Hpc Hwub HnW Hr Hrb Haq.
  have Hrr : glbl_is G r lb_is_r.
  { destruct Hrb as (l & base & ts & vs & j & Hl & Hrd & _).
    exists l. split; [exact Hl|]. destruct l; simplify_eq/=; done. }
  have Hra : gaccesses G r a by (right; by exists t, v).
  have Hi : r.1 = i by rewrite Hr.
  have Hk : r.2 = gcnt r.1 (cd_tr c) by rewrite Hi Hr.
  rewrite -Hi.
  have Hcl : maxcl (gvis_ub G r) := gvis_ub_maxcl G r.
  have Hrp : (r.1, r.2) = r := eq_sym (surjective_pairing r).
  have Hte : take (length (cd_tr c)) (cd_tr c) = cd_tr c
    by (apply take_ge; lia).
  have Hinv := cinv_replay G Hwf Hppo Hlv r a Hrr Hra c ev W
                 (length (cd_tr c)) Hgt Hpc Hwub HnW ltac:(lia) ltac:(lia).
  rewrite Hte -Hk in Hinv.
  destruct Hinv as (_ & Hcoh & Hrn & Hrel & _ & _).
  apply (no_writes_in_of_ub G Hwf Hlv r a t v); [exact Hrb| |].
  - by apply (ctp_log_writes G c ev W).
  - apply maxcl_max; [exact Hcl| |exact Hcoh].
    rewrite /load_vpre. apply maxcl_max; [exact Hcl|exact Hrn|].
    destruct aq; [|apply gvis_ub_0].
    apply Hrel. exists r.2. split_and!; [lia|rewrite Hrp; exact Hrr| |left].
    + rewrite Hrp. by apply Haq.
    + exact Hrp.
Qed.

(* ====================================================================== *)
(** * 3. [floor_ok], DISCHARGED — in [cert_segment]'s vocabulary *)

(** ** 3.1 The obligation itself *)
Theorem cert_floor_ok G c ev W (i : agent) (aq : bool) (base : Z)
    (ts : list nat) (vs : list (bv 8)) :
  rvwmo_minus_consistent G →
  ctrace_prefix G c ev W →
  W_poloc_closed G W →
  wit_fence_ub G c ev W (i, gcnt i (cd_tr c)) →
  ¬ W (i, gcnt i (cd_tr c)) →
  gx_lbl G (i, gcnt i (cd_tr c)) = Some (WeakAxiomatic.LLoad aq base ts vs) →
  floor_ok c i aq base ts.
Proof.
  intros Hcons Hgt Hpc Hwub HnW Hl j t Hj.
  pose proof Hcons as (Hwf & _ & _ & _).
  have Hlen : length vs = length ts := gshape G Hwf _ _ Hl.
  destruct (lookup_lt_is_Some_2 vs j
              ltac:(rewrite Hlen; by eapply lookup_lt_Some)) as [v Hv].
  apply (floor_of_cgraph G c ev W i (i, gcnt i (cd_tr c))
           (WeakAxiomatic.acc_addr base j) t v aq);
    [exact Hcons|exact Hgt|exact Hpc|exact Hwub|exact HnW|done| |].
  - by exists (WeakAxiomatic.LLoad aq base ts vs), base, ts, vs, j.
  - intros ->. by exists (WeakAxiomatic.LLoad true base ts vs).
Qed.

(** ** 3.2 [cert_read_in_log], with [floor_ok] GONE

    [WeakRvwmoCert2.cert_read_in_log] takes [src_in_log] and [floor_ok];
    this takes [src_in_log] and the certified correspondence.  It is the
    exact shape [cert_segment]'s policy needs at an in-log read. *)
Theorem cert_read_in_log' G c ev W (i : agent) (aq : bool) (base : Z)
    (ts : list nat) (vs : list (bv 8)) :
  rvwmo_minus_consistent G →
  ctrace_prefix G c ev W →
  W_poloc_closed G W →
  wit_fence_ub G c ev W (i, gcnt i (cd_tr c)) →
  ¬ W (i, gcnt i (cd_tr c)) →
  gx_lbl G (i, gcnt i (cd_tr c)) = Some (WeakAxiomatic.LLoad aq base ts vs) →
  src_in_log c base ts vs →
  mstep_ok (cand_last_st c) i (WeakAxiomatic.LLoad aq base ts vs).
Proof.
  intros Hcons Hgt Hpc Hwub HnW Hl Hsrc.
  apply cert_read_in_log; [exact Hsrc|].
  by apply (cert_floor_ok G c ev W i aq base ts vs).
Qed.

(** ** 3.3 THE CERTIFICATION CONTEXT

    What a candidate must carry for §3.2 to fire at it.  [cert_segment]
    changes the candidate at every block, so the context has to be an
    INVARIANT of the iteration — that is [cert_segment'] below. *)
Definition cpol_ctx (G : gexec) (W : geid → Prop) (x : agent) (c : cand) : Prop :=
  ∃ ev, ctrace_prefix G c ev W ∧
        wit_fence_ub G c ev W (x, gcnt x (cd_tr c)) ∧
        ¬ W (x, gcnt x (cd_tr c)).

(** The payoff, packaged: at a candidate carrying the context, an in-log
    read of [G]'s own label is admissible with NO floor obligation. *)
Corollary cpol_read (G : gexec) (W : geid → Prop) (x : agent) (c : cand)
    (aq : bool) (base : Z) (ts : list nat) (vs : list (bv 8)) :
  rvwmo_minus_consistent G → W_poloc_closed G W → cpol_ctx G W x c →
  gx_lbl G (x, gcnt x (cd_tr c)) = Some (WeakAxiomatic.LLoad aq base ts vs) →
  src_in_log c base ts vs →
  mstep_ok (cand_last_st c) x (WeakAxiomatic.LLoad aq base ts vs).
Proof.
  intros Hcons Hpc (ev & Hgt & Hwub & HnW) Hl Hsrc.
  by apply (cert_read_in_log' G c ev W x aq base ts vs).
Qed.

(** ** 3.3a [cblkp] — the [HEpair] block with its annotations exposed

    The [cblk] twin: an [adm_run true] prefix, the exclusive READ, an
    [LInstr]-free [adm_run false] middle, and the conditional WRITE.  The
    read and write lists are the four stretches' concatenation. *)
Definition cblkp (cpu : CPU) (d0 : dev_state) (ws : wstate) (lb : lbl)
    (l1 l2 : wlabel) (rds : list wreg) (wrs : list register)
    (m : M unit) (rs : regstate) (fn : ofence) (ib : oib32)
    (m' : M unit) (rs' : regstate) (fn' : ofence) (ib' : oib32) : Prop :=
  ∃ ls1 ma rsa fna iba da rdsA wrsA annA
    mm rsm fnm ibm dm rdsB wrsB annB
    ls2 mm2 rsm2 fnm2 ibm2 dm2 rdsC wrsC annC rdsD wrsD annD,
    (∀ l0, l0 ∈ ls1 → lb_admin true l0) ∧
    phrun cpu ls1 rdsA wrsA annA m rs fn ib d0 ma rsa fna iba da ∧
    hlbl_realizes_pair (PHart cpu ma rsa fna iba)
      (PHart cpu mm2 rsm2 fnm2 ibm2) ws lb l1 l2 ∧
    phrun cpu [l1] rdsB wrsB annB ma rsa fna iba da mm rsm fnm ibm dm ∧
    (∀ l0, l0 ∈ ls2 → lb_admin false l0) ∧
    phrun cpu ls2 rdsC wrsC annC mm rsm fnm ibm dm mm2 rsm2 fnm2 ibm2 dm2 ∧
    phrun cpu [l2] rdsD wrsD annD mm2 rsm2 fnm2 ibm2 dm2 m' rs' fn' ib' d0 ∧
    rds = rdsA ++ rdsB ++ rdsC ++ rdsD ∧
    wrs = wrsA ++ wrsB ++ wrsC ++ wrsD.

Lemma cblkp_intro cpu d0 ws lb l1 l2 ls1 pa da pm dm ls2 pm2 dm2
    m rs fn ib m' rs' fn' ib' :
  adm_run true (PHart cpu m rs fn ib) d0 ls1 pa da →
  hlbl_realizes_pair pa pm2 ws lb l1 l2 →
  pstep_ev pa da l1 pm dm →
  adm_run false pm dm ls2 pm2 dm2 →
  pstep_ev pm2 dm2 l2 (PHart cpu m' rs' fn' ib') d0 →
  ∃ rds wrs, cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib'.
Proof.
  intros Har1 Hre Hst1 Har2 Hst2.
  destruct (adm_run_phart true _ _ d0 ls1 da Har1 cpu m rs fn ib eq_refl)
    as (ma & rsa & fna & iba & ->).
  destruct (pstep_ev_phart cpu ma rsa fna iba da l1 pm dm Hst1)
    as (mm & rsm & fnm & ibm & ->).
  destruct (adm_run_phart false _ _ dm ls2 dm2 Har2 cpu mm rsm fnm ibm eq_refl)
    as (mm2 & rsm2 & fnm2 & ibm2 & ->).
  destruct (pevrun_phrun ls1 _ d0 _ da (adm_run_pevrun _ _ _ _ _ _ Har1)
              cpu m rs fn ib ma rsa fna iba eq_refl eq_refl)
    as (rdsA & wrsA & annA & HA).
  destruct (pevrun_phrun [l1] _ da _ dm
              (pevrun_more l1 [] _ da _ dm _ dm Hst1 (pevrun_nil _ _))
              cpu ma rsa fna iba mm rsm fnm ibm eq_refl eq_refl)
    as (rdsB & wrsB & annB & HB).
  destruct (pevrun_phrun ls2 _ dm _ dm2 (adm_run_pevrun _ _ _ _ _ _ Har2)
              cpu mm rsm fnm ibm mm2 rsm2 fnm2 ibm2 eq_refl eq_refl)
    as (rdsC & wrsC & annC & HC).
  destruct (pevrun_phrun [l2] _ dm2 _ d0
              (pevrun_more l2 [] _ dm2 _ d0 _ d0 Hst2 (pevrun_nil _ _))
              cpu mm2 rsm2 fnm2 ibm2 m' rs' fn' ib' eq_refl eq_refl)
    as (rdsD & wrsD & annD & HD).
  exists (rdsA ++ rdsB ++ rdsC ++ rdsD), (wrsA ++ wrsB ++ wrsC ++ wrsD).
  exists ls1, ma, rsa, fna, iba, da, rdsA, wrsA, annA.
  exists mm, rsm, fnm, ibm, dm, rdsB, wrsB, annB.
  exists ls2, mm2, rsm2, fnm2, ibm2, dm2, rdsC, wrsC, annC, rdsD, wrsD, annD.
  split_and!; [|exact HA|exact Hre|exact HB| |exact HC|exact HD
              |reflexivity|reflexivity].
  - by eapply adm_run_admin.
  - by eapply adm_run_admin.
Qed.

Lemma cblkp_elim cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' :
  cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' →
  ∃ ls1 pa da pm dm ls2 pm2 dm2,
    adm_run true (PHart cpu m rs fn ib) d0 ls1 pa da ∧
    hlbl_realizes_pair pa pm2 ws lb l1 l2 ∧
    pstep_ev pa da l1 pm dm ∧
    adm_run false pm dm ls2 pm2 dm2 ∧
    pstep_ev pm2 dm2 l2 (PHart cpu m' rs' fn' ib') d0.
Proof.
  intros (ls1 & ma & rsa & fna & iba & da & rdsA & wrsA & annA &
          mm & rsm & fnm & ibm & dm & rdsB & wrsB & annB &
          ls2 & mm2 & rsm2 & fnm2 & ibm2 & dm2 & rdsC & wrsC & annC &
          rdsD & wrsD & annD & Had1 & HA & Hre & HB & Had2 & HC & HD & _ & _).
  exists ls1, (PHart cpu ma rsa fna iba), da, (PHart cpu mm rsm fnm ibm), dm.
  exists ls2, (PHart cpu mm2 rsm2 fnm2 ibm2), dm2.
  split_and!.
  - apply (pevrun_adm_run true _ d0 ls1 _ da
             (phrun_pevrun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HA) Had1).
  - exact Hre.
  - apply pevrun_single_inv. by eapply phrun_pevrun.
  - apply (pevrun_adm_run false _ dm ls2 _ dm2
             (phrun_pevrun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HC) Had2).
  - apply pevrun_single_inv. by eapply phrun_pevrun.
Qed.

Lemma cblkp_relp cpu d0 ws ws' lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' :
  w_relp ws' = w_relp ws →
  cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' →
  cblkp cpu d0 ws' lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib'.
Proof.
  intros Hr (ls1 & ma & rsa & fna & iba & da & rdsA & wrsA & annA &
          mm & rsm & fnm & ibm & dm & rdsB & wrsB & annB &
          ls2 & mm2 & rsm2 & fnm2 & ibm2 & dm2 & rdsC & wrsC & annC &
          rdsD & wrsD & annD & Had1 & HA & Hre & HB & Had2 & HC & HD & -> & ->).
  exists ls1, ma, rsa, fna, iba, da, rdsA, wrsA, annA.
  exists mm, rsm, fnm, ibm, dm, rdsB, wrsB, annB.
  exists ls2, mm2, rsm2, fnm2, ibm2, dm2, rdsC, wrsC, annC, rdsD, wrsD, annD.
  split_and!; [exact Had1|exact HA| |exact HB|exact Had2|exact HC|exact HD
              |reflexivity|reflexivity].
  by eapply hlbl_realizes_pair_relp.
Qed.

(** ** 3.3b The pair block, APPENDED *)
Theorem cert_block_snoc_pair (c : cand) (x : agent) (pst : nat → list pexv6)
    (dv : nat → dev_state) cpu d0 lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' :
  srvwmo_consistent c →
  exec_prog_ok' pstep_ev pcls_ev pst dv (cand_exec c) →
  pst (cd_end c) !! x = Some (PHart cpu m rs fn ib) →
  dv (cd_end c) = d0 →
  cblkp cpu d0 (ms_ws (cand_last_st c) x) lb l1 l2 rds wrs
    m rs fn ib m' rs' fn' ib' →
  mstep_ok (cand_last_st c) x lb →
  srvwmo_consistent (cand_snoc c (EStep x lb)) ∧
  exec_prog_ok' pstep_ev pcls_ev
    (pst_snoc c pst x (PHart cpu m' rs' fn' ib')) (dv_snoc c dv d0)
    (cand_exec (cand_snoc c (EStep x lb))).
Proof.
  intros Hc Hpo Hp Hdv Hblk Hok. split; [by apply snoc_consistent|].
  destruct (cblkp_elim cpu d0 _ lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' Hblk)
    as (ls1 & pa & da & pm & dm & ls2 & pm2 & dm2 & Har1 & Hre & Hs1 & Har2 & Hs2).
  eapply (exec_prog_ok'_snoc_pair c x _ pa da ls1 l1 l2 lb pm dm ls2 pm2 dm2
            _ d0);
    [exact Hpo|exact Hp| |exact Hre|exact Hs1|exact Har2|exact Hs2].
  by rewrite Hdv.
Qed.

(** ** 3.3c THE PAIR POLICY, and the shape that RETIRES [HQrmw]

    The iteration's [HEpair] case used to be discharged by REFUTATION: [Q]
    was required [lb_rmwfree], so a fused pair could not occur.  (O-F)
    replaces that refutation by a POLICY of the pair's own — [cpolp] below,
    [Hpol']'s twin for [cblkp] — and the refutation survives as one
    instance of it ([cpolp_of_rmwfree]), so every earlier caller is
    unchanged up to that adapter.

    NOTE THE MISSING [lbl_reidx]: an RMW is never RE-INDEXED, because an RMW
    is never a WITNESS ([witness_not_aq] §1.4 — xv6's is an [amoswap.aq],
    and an acquire is gmo-before every later event of its own hart, so it
    cannot be a cycle's backward step).  The pair policy therefore hands
    back [G]'s own label, and §4.5's [cert_block_pair] is what discharges it
    at a real site. *)
Definition cpolp (x : agent) (cpu : CPU) (d0 : dev_state) (T : list wreg)
    (Ctx : cand → Prop) (Cls : cand → lbl → Prop) (Q : lbl → Prop) : Prop :=
  ∀ (c0 : cand) (ws : wstate) (lb : lbl) (l1 l2 : wlabel)
    (rds : list wreg) (wrs : list register)
    (m : M unit) (rs1 rs2 : regstate) (fn : ofence) (ib : oib32)
    (m' : M unit) (rs1' : regstate) (fn' : ofence) (ib' : oib32),
    srvwmo_consistent c0 →
    Ctx c0 →
    Q lb →
    w_relp (ms_ws (cand_last_st c0) x) = w_relp ws →
    dreg_agree (λ n, n ∉ T) rs1 rs2 →
    cblkp cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ rs2',
      cblkp cpu d0 ws lb l1 l2 rds wrs m rs2 fn ib m' rs2' fn' ib' ∧
      mstep_ok (cand_last_st c0) x lb ∧
      Cls c0 lb ∧
      dreg_agree (λ n, n ∉ T) rs1' rs2'.

(** A [cblkp] block's label IS an RMW — the pair's realization says so. *)
Lemma cblkp_rmw cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' :
  cblkp cpu d0 ws lb l1 l2 rds wrs m rs fn ib m' rs' fn' ib' →
  ¬ lb_rmwfree lb.
Proof.
  intros (ls1 & ma & rsa & fna & iba & da & rdsA & wrsA & annA &
          mm & rsm & fnm & ibm & dm & rdsB & wrsB & annB &
          ls2 & mm2 & rsm2 & fnm2 & ibm2 & dm2 & rdsC & wrsC & annC &
          rdsD & wrsD & annD & _ & _ & Hre & _ & _ & _ & _ & _ & _).
  destruct Hre as (aq & rl & base & tvs & data & asrc1 & asrc2 & vsrc2 &
                   _ & _ & _ & _ & ->).
  intros H. exact H.
Qed.

(** … so an RMW-FREE [Q] gives the pair policy vacuously: this is the OLD
    [HQrmw] refutation, packaged as a policy. *)
Lemma cpolp_of_rmwfree (x : agent) (cpu : CPU) (d0 : dev_state)
    (T : list wreg) (Ctx : cand → Prop) (Cls : cand → lbl → Prop)
    (Q : lbl → Prop) :
  (∀ lb, Q lb → lb_rmwfree lb) → cpolp x cpu d0 T Ctx Cls Q.
Proof.
  intros HQrmw c0 ws lb l1 l2 rds wrs m rs1 rs2 fn ib m' rs1' fn' ib'
    _ _ HQ _ _ Hblk.
  exfalso. exact (cblkp_rmw _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hblk (HQrmw lb HQ)).
Qed.

(** [WeakRvwmoCert2.pol_store], carrying the (trivial) classification the
    [Cls] parameter now asks for. *)
Lemma pol_store' (x : agent) (cpu : CPU) (d0 : dev_state) :
  ∀ (c0 : cand) (ws : wstate) (lb : lbl) (l : wlabel)
    (rds : list wreg) (wrs : list register)
    (m : M unit) (rs1 rs2 : regstate) (fn : ofence) (ib : oib32)
    (m' : M unit) (rs1' : regstate) (fn' : ofence) (ib' : oib32),
    srvwmo_consistent c0 →
    lb_store_ne lb →
    w_relp (ms_ws (cand_last_st c0) x) = w_relp ws →
    dreg_agree (λ n, n ∉ []) rs1 rs2 →
    cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
    ∃ lb' l' rds' wrs' rs2',
      cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m' rs2' fn' ib' ∧
      mstep_ok (cand_last_st c0) x lb' ∧
      lbl_reidx lb lb' ∧
      True ∧
      dreg_agree (λ n, n ∉ []) rs1' rs2'.
Proof.
  intros c0 ws lb l rds wrs m rs1 rs2 fn ib m' rs1' fn' ib' Hc Hlb Hrelp Hag Hblk.
  destruct (pol_store x cpu d0 c0 ws lb l rds wrs m rs1 rs2 fn ib
              m' rs1' fn' ib' Hc Hlb Hrelp Hag Hblk)
    as (lb' & l' & rds' & wrs' & rs2' & H1 & H2 & H3 & H4).
  exists lb', l', rds', wrs', rs2'.
  split_and!; [exact H1|exact H2|exact H3|exact I|exact H4].
Qed.

(** ** 3.4 [cert_segment'] — the iteration with the read policy discharged

    [WeakRvwmoCert2.cert_segment] verbatim, with TWO changes:

      - the policy [Hpol'] additionally RECEIVES a carried context [Ctx c0]
        at the candidate the iteration has reached.  Instantiated at
        [Ctx := cpol_ctx G W x] (§3.3), its read clause is discharged by
        [cpol_read] and owes NO [floor_ok] at all — that is what "(N-1)
        discharged" means here;
      - [Ctx] is carried as an extra clause of the invariant and delivered
        at the end, which costs one extra hypothesis [Hpres]: the context
        extends by one appended step.  At the intended instance [Hpres] is
        pure ctrace BOOKKEEPING — [WeakRvwmoFloor.gtrace_prefix_snoc]'s twin
        for [ctrace_prefix] — and is B2e-3c's, not a semantic debt: nothing
        in it mentions views, coherence or the floor.  At
        [Ctx := λ _, True] it is trivial and the theorem is exactly
        [WeakRvwmoCert2.cert_segment] (§6.3). *)
Section segment'.
  Context (x : agent) (cpu : CPU) (d0 : dev_state) (T : list wreg).
  Context (Q : lbl -> Prop).

  (** THE CARRIED CONTEXT, abstract.  The INTENDED instance is
      [Ctx := cpol_ctx G W x] (§3.3), at which [Hpol']'s read clause is
      [cpol_read] and owes NO [floor_ok]; [Ctx := λ _, True] recovers
      [WeakRvwmoCert2.cert_segment] verbatim (§6). *)
  Context (Ctx : cand → Prop).

  (** (W-3) THE STEP CLASSIFICATION, as a parameter.  The appended label's
      classification — [WeakRvwmoGlue2.cstep_cls] at the intended instance —
      is the READ POLICY's own output, not a fact about [lbl_reidx]: that
      relation is precisely what LETS the indices differ.  So the policy
      DELIVERS [Cls c0 lb'] and [Hpres] CONSUMES it.  At
      [Cls := λ _ _, True] nothing changes. *)
  Context (Cls : cand → lbl → Prop).

  Context (Hpres : ∀ (c0 : cand) (lb lb' : lbl),
      Ctx c0 → srvwmo_consistent c0 → Q lb → lbl_reidx lb lb' →
      mstep_ok (cand_last_st c0) x lb' →
      Cls c0 lb' →
      Ctx (cand_snoc c0 (EStep x lb'))).

  Context (Hpol' : ∀ (c0 : cand) (ws : wstate) (lb : lbl) (l : wlabel)
      (rds : list wreg) (wrs : list register)
      (m : M unit) (rs1 rs2 : regstate) (fn : ofence) (ib : oib32)
      (m' : M unit) (rs1' : regstate) (fn' : ofence) (ib' : oib32),
      srvwmo_consistent c0 →
      Ctx c0 →
      Q lb →
      w_relp (ms_ws (cand_last_st c0) x) = w_relp ws →
      dreg_agree (λ n, n ∉ T) rs1 rs2 →
      cblk cpu d0 ws lb l rds wrs m rs1 fn ib m' rs1' fn' ib' →
      ∃ lb' l' rds' wrs' rs2',
        cblk cpu d0 ws lb' l' rds' wrs' m rs2 fn ib m' rs2' fn' ib' ∧
        mstep_ok (cand_last_st c0) x lb' ∧
        lbl_reidx lb lb' ∧
        Cls c0 lb' ∧
        dreg_agree (λ n, n ∉ T) rs1' rs2').

  (** (O-F) THE PAIR POLICY (§3.3c).  This REPLACES the old [HQrmw]
      refutation; [cpolp_of_rmwfree] recovers the refutation, so an
      RMW-free [Q] costs its callers exactly one adapter. *)
  Context (Hpolp : cpolp x cpu d0 T Ctx Cls Q).

  Theorem cert_segment' k0 ws0 rowseg p es pfin :
    hemit (λ _, d0) k0 ws0 rowseg p es pfin →
    Forall Q rowseg →
    ∀ m0 rs10 fn0 ib0, p = PHart cpu m0 rs10 fn0 ib0 →
    ∀ (c : cand) (pst : nat → list pexv6) (dv : nat → dev_state)
      (rs20 : regstate),
      srvwmo_consistent c →
      Ctx c →
      exec_prog_ok' pstep_ev pcls_ev pst dv (cand_exec c) →
      pst (cd_end c) !! x = Some (PHart cpu m0 rs20 fn0 ib0) →
      dv (cd_end c) = d0 →
      dreg_agree (λ n, n ∉ T) rs10 rs20 →
      w_relp (ms_ws (cand_last_st c) x) = w_relp ws0 →
      ∃ (c' : cand) (pst' : nat → list pexv6) (dv' : nat → dev_state)
        (tradd : list estep) (m1 : M unit) (rs11 rs21 : regstate)
        (fn1 : ofence) (ib1 : oib32),
        cd_tr c' = cd_tr c ++ tradd ∧
        (∀ s, s ∈ tradd → es_ag s = x) ∧
        Forall2 lbl_reidx rowseg ((λ s, es_lb s) <$> tradd) ∧
        srvwmo_consistent c' ∧
        Ctx c' ∧
        exec_prog_ok' pstep_ev pcls_ev pst' dv' (cand_exec c') ∧
        pst' (cd_end c') !! x = Some (PHart cpu m1 rs21 fn1 ib1) ∧
        dv' (cd_end c') = d0 ∧
        pfin = PHart cpu m1 rs11 fn1 ib1 ∧
        dreg_agree (λ n, n ∉ T) rs11 rs21 ∧
        w_relp (ms_ws (cand_last_st c') x)
        = w_relp (row_ws_aux k0 ws0 rowseg) ∧
        (** (O-E) THE THREE BOOKKEEPING EQUATIONS.  The iteration extends by
            [cand_snoc]/[pst_snoc]/[dv_snoc] only, and none of those touches
            the image or index 0 — so the certified candidate carries the
            SAME image and the SAME boot state as the one it started from.
            [WeakRvwmoWalk]'s [wlk_inv] needs exactly these three. *)
        cd_img c' = cd_img c ∧
        pst' 0%nat = pst 0%nat ∧
        dv' 0%nat = dv 0%nat.
  Proof.
    induction 1 as [k ws p
                   |k ws lb row p ls pa da l p' es pfin Har Hre Hst Hem IH
                   |k ws lb row p ls1 pa da l1 pm dm ls2 pm2 dm2 l2 p' es pfin
                    Har1 Hre Hst1 Har2 Hst2 Hem IH];
      intros Hrf m0 rs10 fn0 ib0 -> c pst dv rs20 Hc Hctx Hpo Hp Hdv Hag Hrelp.
    - (* EMPTY SEGMENT *)
      exists c, pst, dv, [], m0, rs10, rs20, fn0, ib0.
      split_and!; [by rewrite app_nil_r| |constructor|exact Hc|exact Hctx
                  |exact Hpo|exact Hp|exact Hdv|reflexivity|exact Hag|exact Hrelp
                  |reflexivity|reflexivity|reflexivity].
      intros s Hs. by apply elem_of_nil in Hs.
    - (* ONE BLOCK, then the rest *)
      apply Forall_cons_1 in Hrf as [Hlb Hrf].
      destruct (adm_run_phart true _ _ d0 ls da Har cpu m0 rs10 fn0 ib0 eq_refl)
        as (ma & rsa & fna & iba & Hpa).
      rewrite Hpa in Hst Hre.
      destruct (pstep_ev_phart cpu ma rsa fna iba da l p' d0 Hst)
        as (m1 & rs11 & fn1 & ib1 & Hp').
      rewrite Hp' in Hst.
      rewrite Hpa in Har.
      destruct (cblk_intro cpu d0 ws lb l ls (PHart cpu ma rsa fna iba) da
                  m0 rs10 fn0 ib0 m1 rs11 fn1 ib1 Har Hre Hst)
        as (rds & wrs & Hblk).
      destruct (Hpol' c ws lb l rds wrs m0 rs10 rs20 fn0 ib0 m1 rs11 fn1 ib1
                  Hc Hctx Hlb Hrelp Hag Hblk)
        as (lb' & l' & rds' & wrs' & rs21 & Hblk2 & Hok & Hri & Hcl & Hag2).
      destruct (cert_block_snoc c x pst dv cpu d0 lb' l' rds' wrs'
                  m0 rs20 fn0 ib0 m1 rs21 fn1 ib1 Hc Hpo Hp Hdv
                  (cblk_relp cpu d0 ws (ms_ws (cand_last_st c) x) lb' l'
                     rds' wrs' m0 rs20 fn0 ib0 m1 rs21 fn1 ib1 Hrelp Hblk2)
                  Hok) as (Hc2 & Hpo2).
      set (c2 := cand_snoc c (EStep x lb')).
      set (pst2 := pst_snoc c pst x (PHart cpu m1 rs21 fn1 ib1)).
      set (dv2 := dv_snoc c dv d0).
      have Hctx2 : Ctx c2 := Hpres c lb lb' Hctx Hc Hlb Hri Hok Hcl.
      have Hend : cd_end c2 = S (cd_end c) by apply cd_end_snoc.
      have Hp2 : pst2 (cd_end c2) !! x = Some (PHart cpu m1 rs21 fn1 ib1).
      { rewrite Hend /pst2 (pst_snoc_gt c pst x _ (S (cd_end c)) ltac:(lia)).
        apply list_lookup_insert. exact (lookup_lt_Some _ _ _ Hp). }
      have Hdv2 : dv2 (cd_end c2) = d0.
      { rewrite Hend /dv2 (dv_snoc_gt c dv d0 (S (cd_end c)) ltac:(lia)) //. }
      have Hrelp2 : w_relp (ms_ws (cand_last_st c2) x)
                  = w_relp (lbl_post k ws lb).
      { rewrite /c2 cand_snoc_relp Hrelp (lbl_reidx_relp _ lb lb' Hri).
        by rewrite lbl_post_relp. }
      destruct (IH Hrf m1 rs11 fn1 ib1 Hp' c2 pst2 dv2 rs21
                  Hc2 Hctx2 Hpo2 Hp2 Hdv2 Hag2 Hrelp2)
        as (c' & pst' & dv' & tradd & m2 & rs12 & rs22 & fn2 & ib2 &
            Htr & Hag' & Hf2 & Hc' & Hctx' & Hpo' & Hp'' & Hdv' & Hfin & Hagf
            & Hrelpf & Himg2 & Hpst02 & Hdv02).
      exists c', pst', dv', (EStep x lb' :: tradd), m2, rs12, rs22, fn2, ib2.
      split_and!; [| |constructor; [exact Hri|exact Hf2]|exact Hc'|exact Hctx'
                   |exact Hpo'|exact Hp''|exact Hdv'|exact Hfin|exact Hagf
                   |exact Hrelpf| | | ].
      + rewrite Htr /c2 cand_snoc_tr -app_assoc //.
      + intros s Hs. apply elem_of_cons in Hs as [->|Hs]; [done|by apply Hag'].
      + rewrite Himg2 /c2 cand_snoc_img //.
      + rewrite Hpst02 /pst2
          (pst_snoc_le c pst x (PHart cpu m1 rs21 fn1 ib1) 0%nat
             (Nat.le_0_l _)) //.
      + rewrite Hdv02 /dv2 (dv_snoc_le c dv d0 0%nat (Nat.le_0_l _)) //.
    - (* (O-F) THE FUSED EXCLUSIVE PAIR, CERTIFIED — the same five moves as
         the [HEone] block, with [cblkp]/[cpolp]/[cert_block_snoc_pair] in
         place of [cblk]/[Hpol']/[cert_block_snoc], and with the appended
         label [G]'s OWN ([lbl_reidx_refl]): an RMW is never re-indexed
         because it is never a witness ([witness_not_aq]). *)
      apply Forall_cons_1 in Hrf as [Hlb Hrf].
      destruct (adm_run_phart true _ _ d0 ls1 da Har1 cpu m0 rs10 fn0 ib0 eq_refl)
        as (ma & rsa & fna & iba & Hpa).
      rewrite Hpa in Har1 Hst1 Hre.
      destruct (pstep_ev_phart cpu ma rsa fna iba da l1 pm dm Hst1)
        as (mb & rsb & fnb & ibb & Hpm).
      rewrite Hpm in Hst1 Har2.
      destruct (adm_run_phart false _ _ dm ls2 dm2 Har2 cpu mb rsb fnb ibb eq_refl)
        as (mc & rsc & fnc & ibc & Hpm2).
      rewrite Hpm2 in Har2 Hst2 Hre.
      destruct (pstep_ev_phart cpu mc rsc fnc ibc dm2 l2 p' d0 Hst2)
        as (m1 & rs11 & fn1 & ib1 & Hp').
      rewrite Hp' in Hst2.
      destruct (cblkp_intro cpu d0 ws lb l1 l2 ls1
                  (PHart cpu ma rsa fna iba) da (PHart cpu mb rsb fnb ibb) dm
                  ls2 (PHart cpu mc rsc fnc ibc) dm2
                  m0 rs10 fn0 ib0 m1 rs11 fn1 ib1 Har1 Hre Hst1 Har2 Hst2)
        as (rds & wrs & Hblk).
      destruct (Hpolp c ws lb l1 l2 rds wrs m0 rs10 rs20 fn0 ib0
                  m1 rs11 fn1 ib1 Hc Hctx Hlb Hrelp Hag Hblk)
        as (rs21 & Hblk2 & Hok & Hcl & Hag2).
      destruct (cert_block_snoc_pair c x pst dv cpu d0 lb l1 l2 rds wrs
                  m0 rs20 fn0 ib0 m1 rs21 fn1 ib1 Hc Hpo Hp Hdv
                  (cblkp_relp cpu d0 ws (ms_ws (cand_last_st c) x) lb l1 l2
                     rds wrs m0 rs20 fn0 ib0 m1 rs21 fn1 ib1 Hrelp Hblk2)
                  Hok) as (Hc2 & Hpo2).
      set (c2 := cand_snoc c (EStep x lb)).
      set (pst2 := pst_snoc c pst x (PHart cpu m1 rs21 fn1 ib1)).
      set (dv2 := dv_snoc c dv d0).
      have Hctx2 : Ctx c2
        := Hpres c lb lb Hctx Hc Hlb (lbl_reidx_refl lb) Hok Hcl.
      have Hend : cd_end c2 = S (cd_end c) by apply cd_end_snoc.
      have Hp2 : pst2 (cd_end c2) !! x = Some (PHart cpu m1 rs21 fn1 ib1).
      { rewrite Hend /pst2 (pst_snoc_gt c pst x _ (S (cd_end c)) ltac:(lia)).
        apply list_lookup_insert. exact (lookup_lt_Some _ _ _ Hp). }
      have Hdv2 : dv2 (cd_end c2) = d0.
      { rewrite Hend /dv2 (dv_snoc_gt c dv d0 (S (cd_end c)) ltac:(lia)) //. }
      have Hrelp2 : w_relp (ms_ws (cand_last_st c2) x)
                  = w_relp (lbl_post k ws lb).
      { rewrite /c2 cand_snoc_relp Hrelp. by rewrite lbl_post_relp. }
      destruct (IH Hrf m1 rs11 fn1 ib1 Hp' c2 pst2 dv2 rs21
                  Hc2 Hctx2 Hpo2 Hp2 Hdv2 Hag2 Hrelp2)
        as (c' & pst' & dv' & tradd & m2 & rs12 & rs22 & fn2 & ib2 &
            Htr & Hag' & Hf2 & Hc' & Hctx' & Hpo' & Hp'' & Hdv' & Hfin & Hagf
            & Hrelpf & Himg2 & Hpst02 & Hdv02).
      exists c', pst', dv', (EStep x lb :: tradd), m2, rs12, rs22, fn2, ib2.
      split_and!; [| |constructor; [apply lbl_reidx_refl|exact Hf2]
                   |exact Hc'|exact Hctx'
                   |exact Hpo'|exact Hp''|exact Hdv'|exact Hfin|exact Hagf
                   |exact Hrelpf| | | ].
      + rewrite Htr /c2 cand_snoc_tr -app_assoc //.
      + intros s Hs. apply elem_of_cons in Hs as [->|Hs]; [done|by apply Hag'].
      + rewrite Himg2 /c2 cand_snoc_img //.
      + rewrite Hpst02 /pst2
          (pst_snoc_le c pst x (PHart cpu m1 rs21 fn1 ib1) 0%nat
             (Nat.le_0_l _)) //.
      + rewrite Hdv02 /dv2 (dv_snoc_le c dv d0 0%nat (Nat.le_0_l _)) //.
  Qed.
End segment'.

(* ====================================================================== *)
(** * 4. OBLIGATION (O-1): THE FUSED EXCLUSIVE PAIR

    [WeakRvwmoCert2.cert_segment] discharges the [HEpair] case by REFUTATION
    ([HQrmw]).  This section supplies the block instead.

    THE ONE SEMANTIC POINT.  An appended RMW must name the LATEST message of
    every byte ([WeakAxiomatic.rmw_latest], [WeakMem.latest]) — the
    older-source freedom of a plain load is a LOAD-only freedom.  So an RMW
    could not be certified at all if its G-source were not already the log's
    latest.  It is: [cert_rmw_latest] derives exactly that from [gatomicity]
    and the log dictionary.  (And an RMW is never a WITNESS in the first
    place: xv6's is an [amoswap.aq], and [witness_not_aq] (§1.4) rules an
    acquire out of the backward step.)  Latest-ness then also pays the floor
    ([floor_ok_of_latest]), so the pair owes §2 nothing. *)

(** ** 4.1 A latest source needs no floor argument *)
Lemma floor_ok_of_latest c (i : agent) (aq : bool) (base : Z) (ts : list nat) :
  srvwmo_consistent c →
  (∀ (j : nat) t, ts !! j = Some t →
     latest (cd_img c) (cd_log_end c) (WeakAxiomatic.acc_addr base j) t) →
  floor_ok c i aq base ts.
Proof.
  intros Hc Hlat j t Hj.
  pose proof (cand_last_bounded c Hc) as Hbd.
  pose proof (Hbd i) as Hbi. rewrite cand_last_log in Hbi.
  destruct (Hlat j t Hj) as (_ & Htop).
  intros Hw. apply Htop. eapply writes_in_mono_hi; [|exact Hw].
  rewrite /cd_floor.
  pose proof (load_vpre_bounded (ms_ws (cand_last_st c) i) aq
                (length (cd_log_end c)) Hbi).
  destruct Hbi as (_ & _ & _ & _ & _ & _ & Hcoh & _).
  pose proof (Hcoh (WeakAxiomatic.acc_addr base j)). lia.
Qed.

(** ** 4.2 THE BRIDGE: an RMW's G-source IS the candidate's latest

    [gatomicity] says no same-byte write is co-BETWEEN the RMW's source and
    the RMW's own write.  Every log message in range names a graph write at
    its own [gwix] ([ctp_log_writes]), and the RMW's own [gwix] is one past
    the log's end — so a message above the source would sit strictly between
    the two, which atomicity forbids. *)
Lemma cert_rmw_latest G c ev W (e : geid) (a : Z) (t : nat) (v : bv 8) :
  rvwmo_minus_consistent G →
  ctrace_prefix G c ev W →
  greads_byte G e a t v →
  glbl_is G e lb_is_w →
  gwix G e = S (length (cd_log_end c)) →
  (t ≤ length (cd_log_end c))%nat →
  latest (cd_img c) (cd_log_end c) a t.
Proof.
  intros (Hwf & Hppo & Hlv & Hat) Hgt Hrb Hw Hix Hle.
  have Hce : cd_log_end c = cd_log c (length (cd_tr c)) := eq_refl.
  split.
  - pose proof (proj1 (Hlv _ _ _ _ Hrb)) as Hval.
    destruct t as [|n].
    + rewrite /log_byte. destruct Hgt as [Himg _ _ _ _ _].
      rewrite Himg Hval. by eexists.
    + destruct Hval as (w & Hw' & Hwb & _). exists v. rewrite Hce.
      apply (ctp_log_byte G c ev W Hgt (S n) w a v);
        [lia|rewrite -Hce; exact Hle|exact Hw'|exact Hwb].
  - intros (s & Hlo & Hhi & m & Hm & Hby).
    rewrite Hce in Hm.
    destruct (ctp_log_writes G c ev W Hgt s m ltac:(lia) Hm a Hby)
      as (w & v' & Hws & Hwb).
    have Hgwix : gwix G w = s.
    { destruct Hwf as (Hnd & _ & _). by apply (gwrite_at_inv G s w Hnd Hws). }
    apply (Hat e a t v Hrb Hw w v' Hwb).
    split; [lia|]. rewrite Hgwix Hix. lia.
Qed.

(** ** 4.3 [mstep_ok] at the RMW, with no floor obligation *)
Theorem cert_rmw_ok G c ev W (x : agent) (aq rl : bool) (base : Z)
    (ts : list nat) (rvs wvs : list (bv 8)) (kc : wm_class) :
  rvwmo_minus_consistent G →
  ctrace_prefix G c ev W →
  srvwmo_consistent c →
  gx_lbl G (x, gcnt x (cd_tr c))
    = Some (WeakAxiomatic.LRmw aq rl base ts rvs wvs kc) →
  gwix G (x, gcnt x (cd_tr c)) = S (length (cd_log_end c)) →
  (∀ (j : nat) t, ts !! j = Some t → (t ≤ length (cd_log_end c))%nat) →
  src_in_log c base ts rvs →
  mstep_ok (cand_last_st c) x
    (WeakAxiomatic.LRmw aq rl base ts rvs wvs kc).
Proof.
  intros Hcons Hgt Hc Hl Hix Hbnd Hsrc.
  pose proof Hcons as (Hwf & _ & _ & _).
  destruct (gshape G Hwf _ _ Hl) as (Hne & Hlenw & Hlenr).
  have Hisw : glbl_is G (x, gcnt x (cd_tr c)) lb_is_w
    by (exists (WeakAxiomatic.LRmw aq rl base ts rvs wvs kc)).
  have Hlat : ∀ (j : nat) t, ts !! j = Some t →
    latest (cd_img c) (cd_log_end c) (WeakAxiomatic.acc_addr base j) t.
  { intros j t Hj.
    destruct (lookup_lt_is_Some_2 rvs j
                ltac:(rewrite Hlenr; by eapply lookup_lt_Some)) as [v Hv].
    apply (cert_rmw_latest G c ev W (x, gcnt x (cd_tr c))
             (WeakAxiomatic.acc_addr base j) t v);
      [exact Hcons|exact Hgt| |exact Hisw|exact Hix|by eapply Hbnd].
    by exists (WeakAxiomatic.LRmw aq rl base ts rvs wvs kc), base, ts, rvs, j. }
  split_and!.
  - exact Hne.
  - exact Hlenw.
  - apply snoc_rd_ok, snoc_rd_adm_of; [exact Hsrc|].
    by apply floor_ok_of_latest.
  - rewrite cand_last_img cand_last_log. exact Hlat.
Qed.

(** ** 4.4 THE MIRROR, at the pair: an untainted pair block runs step for step from
    the certified register file — [WeakRvwmoCert2.cert_block_mirror]'s twin,
    off [hlbl_realizes_pair_rs]. *)
Theorem cert_block_pair_mirror (P : wreg → Prop) cpu d0 ws lb l1 l2 rds wrs
    m rs1 fn ib m' rs1' fn' ib' rs2 :
  cblkp cpu d0 ws lb l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' →
  rds_ok P rds →
  dreg_agree P rs1 rs2 →
  ∃ rs2', cblkp cpu d0 ws lb l1 l2 rds wrs m rs2 fn ib m' rs2' fn' ib' ∧
          dreg_agree P rs1' rs2'.
Proof.
  intros (ls1 & ma & rsa & fna & iba & da & rdsA & wrsA & annA &
          mm & rsm & fnm & ibm & dm & rdsB & wrsB & annB &
          ls2 & mm2 & rsm2 & fnm2 & ibm2 & dm2 & rdsC & wrsC & annC &
          rdsD & wrsD & annD & Had1 & HA & Hre & HB & Had2 & HC & HD & -> & ->)
         Hrds Hag.
  apply rds_ok_app in Hrds as [HrdsA Hrds].
  apply rds_ok_app in Hrds as [HrdsB Hrds].
  apply rds_ok_app in Hrds as [HrdsC HrdsD].
  destruct (phrun_dagree P cpu ls1 rdsA wrsA annA m rs1 fn ib d0
              ma rsa fna iba da HA HrdsA rs2 Hag) as (rsa2 & HA2 & Haga).
  destruct (phrun_dagree P cpu [l1] rdsB wrsB annB ma rsa fna iba da
              mm rsm fnm ibm dm HB HrdsB rsa2 Haga) as (rsm2' & HB2 & Hagb).
  destruct (phrun_dagree P cpu ls2 rdsC wrsC annC mm rsm fnm ibm dm
              mm2 rsm2 fnm2 ibm2 dm2 HC HrdsC rsm2' Hagb)
    as (rsm22 & HC2 & Hagc).
  destruct (phrun_dagree P cpu [l2] rdsD wrsD annD mm2 rsm2 fnm2 ibm2 dm2
              m' rs1' fn' ib' d0 HD HrdsD rsm22 Hagc) as (rs2' & HD2 & Hagd).
  exists rs2'. split; [|exact Hagd].
  exists ls1, ma, rsa2, fna, iba, da, rdsA, wrsA, annA.
  exists mm, rsm2', fnm, ibm, dm, rdsB, wrsB, annB.
  exists ls2, mm2, rsm22, fnm2, ibm2, dm2, rdsC, wrsC, annC, rdsD, wrsD, annD.
  split_and!; [exact Had1|exact HA2| |exact HB2|exact Had2|exact HC2|exact HD2
              |reflexivity|reflexivity].
  by eapply hlbl_realizes_pair_rs.
Qed.

(** ** 4.5 THE PAIR, CERTIFIED: the untainted mirror plus §4.3's admissibility.
    This is (O-1) closed — an [amoswap.aq] block is now inside the
    certification's reach, at [G]'s own label. *)
Theorem cert_block_pair (T : list wreg) G c ev W (x : agent)
    (pst : nat → list pexv6) (dv : nat → dev_state) cpu d0
    (aq rl : bool) (base : Z) (ts : list nat) (rvs wvs : list (bv 8))
    (kc : wm_class) l1 l2 rds wrs m rs1 fn ib m' rs1' fn' ib' rs2 :
  rvwmo_minus_consistent G →
  ctrace_prefix G c ev W →
  srvwmo_consistent c →
  exec_prog_ok' pstep_ev pcls_ev pst dv (cand_exec c) →
  pst (cd_end c) !! x = Some (PHart cpu m rs2 fn ib) →
  dv (cd_end c) = d0 →
  cblkp cpu d0 (ms_ws (cand_last_st c) x)
    (WeakAxiomatic.LRmw aq rl base ts rvs wvs kc) l1 l2 rds wrs
    m rs1 fn ib m' rs1' fn' ib' →
  rds_ok (λ n, n ∉ T) rds →
  dreg_agree (λ n, n ∉ T) rs1 rs2 →
  gx_lbl G (x, gcnt x (cd_tr c))
    = Some (WeakAxiomatic.LRmw aq rl base ts rvs wvs kc) →
  gwix G (x, gcnt x (cd_tr c)) = S (length (cd_log_end c)) →
  (∀ (j : nat) t, ts !! j = Some t → (t ≤ length (cd_log_end c))%nat) →
  src_in_log c base ts rvs →
  ∃ rs2',
    srvwmo_consistent
      (cand_snoc c (EStep x (WeakAxiomatic.LRmw aq rl base ts rvs wvs kc))) ∧
    exec_prog_ok' pstep_ev pcls_ev
      (pst_snoc c pst x (PHart cpu m' rs2' fn' ib')) (dv_snoc c dv d0)
      (cand_exec
         (cand_snoc c (EStep x (WeakAxiomatic.LRmw aq rl base ts rvs wvs kc)))) ∧
    dreg_agree (λ n, n ∉ T) rs1' rs2'.
Proof.
  intros Hcons Hgt Hc Hpo Hp Hdv Hblk Hrds Hag Hl Hix Hbnd Hsrc.
  destruct (cert_block_pair_mirror (λ n, n ∉ T) cpu d0
              (ms_ws (cand_last_st c) x) _ l1 l2 rds wrs
              m rs1 fn ib m' rs1' fn' ib' rs2 Hblk Hrds Hag)
    as (rs2' & Hblk2 & Hag2).
  destruct (cert_block_snoc_pair c x pst dv cpu d0 _ l1 l2 rds wrs
              m rs2 fn ib m' rs2' fn' ib' Hc Hpo Hp Hdv Hblk2
              (cert_rmw_ok G c ev W x aq rl base ts rvs wvs kc
                 Hcons Hgt Hc Hl Hix Hbnd Hsrc)) as (Hc2 & Hpo2).
  by exists rs2'.
Qed.

(* ====================================================================== *)
(** * 5. OBLIGATION (O-2): RE-CONVERGENCE AFTER A WITNESS

    After a substituted read the certified run and the emission sit at
    DIFFERENT monad nodes ([WeakRvwmoCert2.cert_block_witness]), so
    [cert_segment]'s "same node" invariant is broken.  They re-converge at
    the next instruction BOUNDARY.

    WHY THAT IS A THEOREM AND NOT A HOPE: the boundary node is
    [Interface.Ret y] with [y : unit], i.e. the CONSTANT [Interface.Ret tt]
    — [WeakEvInst.pnode_step]'s first arm — so "both runs are at a boundary"
    already forces their nodes EQUAL, with no reference to what either ran.
    And the boundary step is uniform: it emits [LInstr], resumes at
    [riscv_step tick] for a tick of the caller's choosing, writes no
    register, parks no fence, leaves the fabric alone and RESETS the channel
    to [ib_none].  So the certified run can take the same tick and the two
    are back in lockstep — same node, same fence, same channel — with their
    register files agreeing off the GROWN taint set.

    WHAT IS *NOT* PROVED HERE, deliberately: that either run REACHES a
    boundary.  That is progress — the solo run is a genuine pf run of the
    verified program, which is the EWPs' content (§4e) — and it enters as
    the explicit hypotheses [at_boundary m1'] / [at_boundary m2']. *)

Definition at_boundary (m : M unit) : Prop := ∃ y : unit, m = Interface.Ret y.

Lemma at_boundary_ret : at_boundary (Interface.Ret tt).
Proof. by exists tt. Qed.

(** THE BOUNDARY CONTINUATION IS A CONSTANT. *)
Lemma boundary_node_const m1 m2 :
  at_boundary m1 → at_boundary m2 → m1 = m2.
Proof. intros ([] & ->) ([] & ->). reflexivity. Qed.

(** Every boundary step has the same shape ... *)
Lemma boundary_step_inv (m : M unit) rs ib d l m' ors fn' d' oib :
  at_boundary m →
  pnode_step m rs ib d l m' ors fn' d' oib →
  ∃ tick : bool, l = LInstr ∧ m' = riscv_step tick ∧ ors = None ∧
                 fn' = None ∧ d' = d ∧ oib = Some ib_none.
Proof.
  intros ([] & ->) Hst. rewrite /pnode_step in Hst.
  destruct Hst as (tick & H1 & H2 & H3 & H4 & H5 & H6).
  by exists tick.
Qed.

(** ... and it always exists, at any register file, channel and fabric. *)
Lemma boundary_step_exists (m : M unit) rs ib d :
  at_boundary m →
  pnode_step m rs ib d LInstr (riscv_step true) None None d (Some ib_none).
Proof.
  intros ([] & ->). rewrite /pnode_step. by exists true.
Qed.

(** THE RE-CONVERGENCE.  The node half is [boundary_node_const]; the
    register half is [WeakEvProv.taint_closure_load] — both remainders write
    only carriers the grown taint set already holds. *)
Theorem boundary_reconverge (T : list wreg) (rd : wreg)
    cpu1 ls1 rds1 wrs1 ann1 m1 rs1 fn1 ib1 d1 m1' rs1' fn1' ib1' d1'
    cpu2 ls2 rds2 wrs2 ann2 m2 rs2 fn2 ib2 d2 m2' rs2' fn2' ib2' d2' :
  dreg_agree (λ n, n ∉ T) rs1 rs2 →
  phrun cpu1 ls1 rds1 wrs1 ann1 m1 rs1 fn1 ib1 d1 m1' rs1' fn1' ib1' d1' →
  phrun cpu2 ls2 rds2 wrs2 ann2 m2 rs2 fn2 ib2 d2 m2' rs2' fn2' ib2' d2' →
  (∀ r, r ∈ wrs1 ++ wrs2 → ∃ n, ereg_num r = Some n ∧ n ∈ rd :: T) →
  (* THE PROGRESS HYPOTHESES (the EWPs' content — NOT proved here) *)
  at_boundary m1' → at_boundary m2' →
  m1' = m2' ∧ dreg_agree (λ n, n ∉ rd :: T) rs1' rs2'.
Proof.
  intros Hag Hr1 Hr2 Hws Hb1 Hb2. split.
  - by apply boundary_node_const.
  - by eapply taint_closure_load.
Qed.

(** ... and the step that puts the two runs back in [cert_segment]'s
    invariant: the SAME successor node, the SAME parked fence ([None]) and
    the SAME channel ([ib_none]).  The parked fence at the boundary is
    [None] — a hart between instructions holds no fence — which is the one
    thing the caller supplies. *)
Corollary boundary_reconverge_run (T : list wreg) (rd : wreg)
    cpu1 ls1 rds1 wrs1 ann1 m1 rs1 fn1 ib1 d1 m1' rs1' ib1' d1'
    cpu2 ls2 rds2 wrs2 ann2 m2 rs2 fn2 ib2 d2 m2' rs2' ib2' d2' :
  dreg_agree (λ n, n ∉ T) rs1 rs2 →
  phrun cpu1 ls1 rds1 wrs1 ann1 m1 rs1 fn1 ib1 d1 m1' rs1' None ib1' d1' →
  phrun cpu2 ls2 rds2 wrs2 ann2 m2 rs2 fn2 ib2 d2 m2' rs2' None ib2' d2' →
  (∀ r, r ∈ wrs1 ++ wrs2 → ∃ n, ereg_num r = Some n ∧ n ∈ rd :: T) →
  at_boundary m1' → at_boundary m2' →
  ∃ (m0 : M unit) rdsA wrsA annA rdsB wrsB annB,
    phrun cpu1 [LInstr] rdsA wrsA annA m1' rs1' None ib1' d1'
      m0 rs1' None ib_none d1' ∧
    phrun cpu2 [LInstr] rdsB wrsB annB m2' rs2' None ib2' d2'
      m0 rs2' None ib_none d2' ∧
    dreg_agree (λ n, n ∉ rd :: T) rs1' rs2'.
Proof.
  intros Hag Hr1 Hr2 Hws Hb1 Hb2.
  destruct (boundary_reconverge T rd cpu1 ls1 rds1 wrs1 ann1 m1 rs1 fn1 ib1 d1
              m1' rs1' None ib1' d1' cpu2 ls2 rds2 wrs2 ann2 m2 rs2 fn2 ib2 d2
              m2' rs2' None ib2' d2' Hag Hr1 Hr2 Hws Hb1 Hb2) as (Hnode & Hag').
  exists (riscv_step true).
  eexists _, _, _, _, _, _. split_and!; [| |exact Hag'].
  - eapply (phrun_more cpu1 LInstr [] _ [] _ [] _ false);
      [left; split_and!; [reflexivity|by apply boundary_step_exists
                         |reflexivity|reflexivity|reflexivity]|].
    apply phrun_nil.
  - eapply (phrun_more cpu2 LInstr [] _ [] _ [] _ false);
      [left; split_and!; [reflexivity|by apply boundary_step_exists
                         |reflexivity|reflexivity|reflexivity]|].
    apply phrun_nil.
Qed.

(* ====================================================================== *)
(** * 6. NON-VACUITY

    Four inhabitations, one per moving part: the certified correspondence
    (§6.1), the floor discharge over it at a REAL graph read (§6.2), the
    segment iteration with the carried context (§6.3), and the boundary
    re-convergence at a real two-node run (§6.4). *)

(** ** 6.1 The empty candidate is a certified prefix of every graph, at
    every witness set — all seven clauses quantify over a step or an index
    that does not exist. *)
Lemma ctrace_prefix_empty G W :
  ctrace_prefix G (Cand (gx_img G) []) (λ _, (0%nat, 0%nat)) W.
Proof.
  split.
  - done.
  - by intros [|p] s Hs.
  - by intros [|p] s Hs.
  - by intros [|p] s Hs.
  - by intros [|p] s Hs.
  - intros s Hs Hle. rewrite /cd_log /= in Hle. lia.
Qed.

Lemma wit_fence_ub_empty G W r :
  wit_fence_ub G (Cand (gx_img G) []) (λ _, (0%nat, 0%nat)) W r.
Proof. by intros [|p] s Hs. Qed.

Lemma cpol_ctx_empty G W (x : agent) :
  ¬ W (x, 0%nat) → cpol_ctx G W x (Cand (gx_img G) []).
Proof.
  intros HnW. exists (λ _, (0%nat, 0%nat)). split_and!;
    [apply ctrace_prefix_empty|apply wit_fence_ub_empty|exact HnW].
Qed.

(** ** 6.2 THE FLOOR, at a real graph read

    [WeakRvwmoFloor.gtrace_snoc_read_image]'s twin: any hart's FIRST read,
    over any [rvwmo_minus_consistent] graph, has its floor obligation
    discharged by §3.1 — with a witness set in play (any [W] not containing
    the read itself). *)
Corollary cert_floor_ok_image G (i : agent) (W : geid → Prop)
    (aq : bool) (base : Z) (ts : list nat) (vs : list (bv 8)) :
  rvwmo_minus_consistent G →
  W_poloc_closed G W →
  ¬ W (i, 0%nat) →
  gx_lbl G (i, 0%nat) = Some (WeakAxiomatic.LLoad aq base ts vs) →
  floor_ok (Cand (gx_img G) []) i aq base ts.
Proof.
  intros Hcons Hpc HnW Hl.
  have Hz : gcnt i (cd_tr (Cand (gx_img G) [])) = 0%nat by done.
  apply (cert_floor_ok G (Cand (gx_img G) []) (λ _, (0%nat, 0%nat)) W i
           aq base ts vs);
    [exact Hcons|apply ctrace_prefix_empty|exact Hpc
    |apply wit_fence_ub_empty|by rewrite Hz|by rewrite Hz].
Qed.

(** ** 6.3 [cert_segment'] on the REAL [sw &started] block

    [WeakRvwmoCert2]'s witness segment, re-run through the context-carrying
    iteration at [Ctx := λ _, True] (which recovers [cert_segment] exactly,
    and is what makes the refactoring conservative). *)
Section nonvacuity3.
  Context (cpu : CPU) (rs : regstate) (ib : oib32) (d0 : dev_state).

  Notation img0 := (λ _ : Z, @None (bv 8)).

  Theorem cert_segment'_witness :
    ∃ (c' : cand) (pst' : nat → list pexv6) (dv' : nat → dev_state)
      (tradd : list estep),
      cd_tr c' = tradd ∧
      (∀ s, s ∈ tradd → es_ag s = 0%nat) ∧
      Forall2 lbl_reidx ev_row ((λ s, es_lb s) <$> tradd) ∧
      srvwmo_consistent c' ∧
      exec_prog_ok' pstep_ev pcls_ev pst' dv' (cand_exec c') ∧
      tradd !! 0%nat
      = Some (EStep 0%nat (WeakAxiomatic.LStore false (pa_z ev_flag)
                             (wbytes 4 WeakLock.lock_one) WCplain)).
  Proof.
    destruct (cert_segment' 0%nat cpu d0 [] lb_store_ne
                (λ _ : cand, True) (λ _ _, True)
                (λ c0 lb lb' _ _ _ _ _ _, I)
                (λ c0 ws lb l rds wrs m rs1 rs2 fn ib0 m' rs1' fn' ib'
                   Hc _ Hlb H1 H2 H3,
                   pol_store' 0%nat cpu d0 c0 ws lb l rds wrs m rs1 rs2 fn ib0
                     m' rs1' fn' ib' Hc Hlb H1 H2 H3)
                (cpolp_of_rmwfree 0%nat cpu d0 [] (λ _ : cand, True)
                   (λ _ _, True) lb_store_ne lb_store_ne_rmwfree)
                0%nat ws_init ev_row (ev_p0 cpu rs ib) _ _
                (nv_hemit cpu rs ib d0) nv_row_class
                ev_x2.2 rs None ib eq_refl
                (sm_c img0) (sm_pst cpu rs ib) (sm_dv d0) rs
                (sm_consistent img0) I (sm_prog0 img0 cpu rs ib d0)
                eq_refl eq_refl (dreg_agree_refl _ _)
                ltac:(by rewrite (sm_ws img0)))
      as (c' & pst' & dv' & tradd & m1 & rs11 & rs21 & fn1 & ib1 &
          Htr & Hag & Hf2 & Hc' & _ & Hpo' & _ & _ & _ & _ & _ & _ & _ & _).
    exists c', pst', dv', tradd. split_and!;
      [by rewrite Htr|exact Hag|exact Hf2|exact Hc'|exact Hpo'|].
    by apply (seg_exit_write 0%nat ev_row tradd 0%nat).
  Qed.
End nonvacuity3.

Corollary cert_segment'_nonvacuous :
  ∃ (c' : cand) (pst' : nat → list pexv6) (dv' : nat → dev_state)
    (tradd : list estep),
    tradd ≠ [] ∧ cd_tr c' = tradd ∧
    (∀ s, s ∈ tradd → es_ag s = 0%nat) ∧
    srvwmo_consistent c' ∧
    exec_prog_ok' pstep_ev pcls_ev pst' dv' (cand_exec c') ∧
    tradd !! 0%nat
    = Some (EStep 0%nat (WeakAxiomatic.LStore false (pa_z ev_flag)
                           (wbytes 4 WeakLock.lock_one) WCplain)).
Proof.
  destruct (cert_segment'_witness 0%fin ev_rs0 ib_none dev0_state)
    as (c' & pst' & dv' & tradd & Htr & Hag & _ & Hc' & Hpo' & Hlk).
  exists c', pst', dv', tradd. split_and!;
    [|exact Htr|exact Hag|exact Hc'|exact Hpo'|exact Hlk].
  intros ->. by rewrite lookup_nil in Hlk.
Qed.

(** ** 6.4 The boundary, at a real two-node run

    [WeakEvProv]'s [wit_m] fragment — a [RegRead] then a [RegWrite] — ENDS
    at [Interface.Ret tt], so it is a genuine witness for §5: two runs from
    agreeing register files reach the boundary, and §5 puts them back at one
    node, one fence and one channel. *)
Lemma wit_m_boundary (cpu : CPU) (rs : regstate) (d : dev_state) :
  ∃ ls rds wrs ann ib' rs',
    phrun cpu ls rds wrs ann wit_m rs None ib_none d
      (Interface.Ret tt) rs' None ib' d ∧
    wrs = [(R_bitvector_64 x14 : register)].
Proof.
  eexists _, _, _, _, _, _. split.
  - eapply phrun_more.
    { left. split_and!; [reflexivity| |reflexivity|reflexivity|reflexivity].
      rewrite /wit_m /pnode_step. by split_and!. }
    eapply phrun_more.
    { left. split_and!; [reflexivity| |reflexivity|reflexivity|reflexivity].
      rewrite /pnode_step. by split_and!. }
    apply phrun_nil.
  - by vm_compute.
Qed.

Corollary boundary_reconverge_nonvacuous (cpu : CPU) (rs1 rs2 : regstate)
    (d : dev_state) :
  dreg_agree (λ n, n ∉ @nil wreg) rs1 rs2 →
  ∃ (m0 : M unit) (rs1' rs2' : regstate) (ib1' ib2' : oib32)
    rdsA wrsA annA rdsB wrsB annB,
    phrun cpu [LInstr] rdsA wrsA annA (Interface.Ret tt) rs1' None ib1' d
      m0 rs1' None ib_none d ∧
    phrun cpu [LInstr] rdsB wrsB annB (Interface.Ret tt) rs2' None ib2' d
      m0 rs2' None ib_none d ∧
    dreg_agree (λ n, n ∉ [14%nat]) rs1' rs2'.
Proof.
  intros Hag.
  destruct (wit_m_boundary cpu rs1 d)
    as (ls1 & rds1 & wrs1 & ann1 & ib1' & rs1' & Hr1 & Hw1).
  destruct (wit_m_boundary cpu rs2 d)
    as (ls2 & rds2 & wrs2 & ann2 & ib2' & rs2' & Hr2 & Hw2).
  destruct (boundary_reconverge_run [] 14%nat
              cpu ls1 rds1 wrs1 ann1 wit_m rs1 None ib_none d
              (Interface.Ret tt) rs1' ib1' d
              cpu ls2 rds2 wrs2 ann2 wit_m rs2 None ib_none d
              (Interface.Ret tt) rs2' ib2' d
              Hag Hr1 Hr2
              ltac:(rewrite Hw1 Hw2; intros r Hr;
                    exists 14%nat; split; [|apply elem_of_list_here];
                    apply elem_of_app in Hr as [Hr|Hr];
                    apply elem_of_list_singleton in Hr as ->; by vm_compute)
              at_boundary_ret at_boundary_ret)
    as (m0 & rdsA & wrsA & annA & rdsB & wrsB & annB & HA & HB & Hag2).
  by exists m0, rs1', rs2', ib1', ib2', rdsA, wrsA, annA, rdsB, wrsB, annB.
Qed.

(* ====================================================================== *)
(** * 7. WHAT THIS SLICE LEAVES OPEN

    Nothing below is [Admitted]; these are the statements this file does NOT
    make, so that B2e-3c inherits an exact list.

    (P-1) [Hpres] — the ctrace bookkeeping ([cert_segment'] §3.4): that
          appending the certified label to a candidate carrying
          [cpol_ctx G W x] leaves it carrying [cpol_ctx G W x].  It is
          [WeakRvwmoFloor.gtrace_prefix_snoc] with the witness clause added
          (a witness step re-establishes [ctp_step]'s SECOND disjunct at the
          appended position, by construction of the witness label), plus the
          [gwix] side condition rule 14 supplies.  Purely structural.

    (P-2) [src_in_log] (N-2) is still the read policy's DATA, exactly as in
          [WeakRvwmoCert2]: this file removes [floor_ok] from the policy's
          read clause and nothing else.

    (P-3) [wit_fence_ub] (§2.1) is a HYPOTHESIS, not a derivation.  It is
          vacuous at a witness with no [pr]/[sr] fence between it and the
          read being certified, and vacuous outright at [W = ∅] (§6.1); a
          general discharge would come from the cycle order's own gmo facts
          when B2e-3c fixes the witness set.

    (P-4) PROGRESS (§5): that a certified remainder REACHES its boundary.
          The EWPs' content; an explicit hypothesis by design.

    NOT OPEN ANY MORE (this session):

    (O-1)/(O-F) THE FUSED EXCLUSIVE PAIR.  [cert_segment']'s [HEpair] case
          is certified in place — by [cpolp] (§3.3c), the pair's own policy
          — instead of refuted by [HQrmw].  [cpolp_of_rmwfree] recovers the
          refutation for an RMW-free [Q]; §4.5's [cert_block_pair] is what
          discharges the policy at a real site.  The appended label is
          [G]'s OWN, because an RMW is never a witness ([witness_not_aq]).

    (O-E) THE THREE BOOKKEEPING EQUATIONS are now STATED by
          [cert_segment']: the certified candidate carries the same image
          and the same index-0 process/device state as the one it started
          from.  [WeakRvwmoWalk]'s [wlk_inv] consumes exactly those.

    (W-3) THE STEP CLASSIFICATION travels with the step: [cert_segment']'s
          [Cls] parameter is DELIVERED by the read policy and CONSUMED by
          [Hpres].  It could not be otherwise — [lbl_reidx] is precisely
          the relation that lets the appended label's read indices differ
          from [G]'s, so no graph-side fact pins it. *)

(* ====================================================================== *)
(** * 8. AUDIT *)

Print Assumptions ctrace_prefix_of_gtrace.
Print Assumptions witness_not_aq.
Print Assumptions cinv_step_wit.
Print Assumptions cinv_replay.
Print Assumptions floor_of_cgraph.
Print Assumptions cert_floor_ok.
Print Assumptions cert_read_in_log'.
Print Assumptions cpol_read.
Print Assumptions cert_segment'.
Print Assumptions cblkp_rmw.
Print Assumptions cpolp_of_rmwfree.
Print Assumptions floor_ok_of_latest.
Print Assumptions cert_rmw_latest.
Print Assumptions cert_rmw_ok.
Print Assumptions cert_block_pair_mirror.
Print Assumptions cert_block_snoc_pair.
Print Assumptions cert_block_pair.
Print Assumptions boundary_node_const.
Print Assumptions boundary_reconverge.
Print Assumptions boundary_reconverge_run.
Print Assumptions cert_floor_ok_image.
Print Assumptions cert_segment'_nonvacuous.
Print Assumptions boundary_reconverge_nonvacuous.
