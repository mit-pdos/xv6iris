(** * WeakRvwmoCert.v — B2e-3b SLICE 3a: CAND EXTENSION BY A SOLO BLOCK

    Design: [claude-notes/design/weak-memory-route-b.md] §4e, "SLICE 3's
    SHAPE" and its SUB-SLICES entry (3a).

    THE OBJECT.  Slice 3 certifies a run by taking a realized candidate and
    APPENDING, one instruction block at a time, the hart's next event at the
    CURRENT log.  This file is the single-block step of that iteration, in
    both of its halves:

    (1) THE AXIOMATIC HALF — [cand_snoc] and [snoc_consistent]: appending a
        step to an sRVWMO-consistent candidate keeps it sRVWMO-consistent as
        soon as the appended label is admissible at the candidate's own last
        replay state.  The route is [WeakAxiomatic3.srvwmo_realizable] out,
        [WeakAxiomatic2.cand_reachable] back in, and
        [WeakSrvwmoLitmus.srvwmo_of_wf] to re-package: consistency of a
        candidate is EXACTLY machine-reachability, so extension is a purely
        LOCAL side condition and no global axiom (coherence, atomicity,
        [ob]-acyclicity) has to be re-established by hand.

    (2) THE PROGRAM HALF — [exec_prog_ok'_snoc] (+ its exclusive-pair twin):
        the trace-indexed supply [WeakAxRealize.exec_prog_ok'] extends by one
        position from ONE [WeakRvwmoConf.hemit]-shaped block for the acting
        agent.  This is [WeakRvwmoSupply.supply_of_qconf]'s per-position
        obligation, discharged for a single appended block instead of a whole
        interleaving; the [w_relp] bridge is the same one
        ([hlbl_realizes_relp] / [cand_ws_relp]).

    THE TWO ADMISSIBILITY QUESTIONS §4e asks (answers in §4 below).

    (i) IS A READ OF THE LATEST IN-LOG WRITE ALWAYS ADMISSIBLE?  YES, modulo
        the byte being defined at all.  [mstep]'s read side condition is
        [WeakAxiomatic.rd_ok], i.e. per byte [WeakMem.byte_rd]:
        [log_byte img log t a = Some v] AND
        [readable img log ws (load_vpre ws aq) a t].  For [t = latest_ts log a]
        the second is [WeakMem.latest_readable] — nothing above a latest
        timestamp writes [a] at all, so no floor can block it — whose only
        side condition, [Nat.max vpre (coh ws a) ≤ length log], is
        [WeakAxiomatic2.cfg_bounded] of the last state, which every REACHABLE
        candidate has ([cand_last_bounded]).  So the hypothesis that remains
        is only [latest_bytes_ok]: each byte of the footprint is written by
        the image or by some message.

    (ii) WHEN MAY AN APPENDED READ NAME AN OLDER IN-LOG WRITE?  Exactly when
        no message strictly between [t] and the agent's own floor writes that
        byte:
          ¬ writes_in (cd_log_end c) a t
              (Nat.max (load_vpre (ms_ws (cand_last_st c) i) aq)
                       (coh  (ms_ws (cand_last_st c) i) a)).
        That is the unfolding of [readable] at [load_vpre] — the coherence
        floor of the AGENT, per byte, and it is candidate vocabulary: the
        wstate [ms_ws (cand_last_st c) i] is a function of [c] alone (the
        replay fold), so [snoc_rd_adm] below needs NO machine-side view fact
        beyond what [c] already determines.  Both variants land in full.

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
Require Import WeakAxiomatic.
Require Import WeakAxiomatic2.
Require Import WeakAxiomatic3.
Require Import WeakSrvwmoLitmus.
Require Import WeakRvwmoGraph.

Local Open Scope Z_scope.

(* ====================================================================== *)
(** * 1. [cand_snoc] AND ITS LOG / [stt] CALCULUS *)

Definition cand_snoc (c : cand) (s : estep) : cand :=
  Cand (cd_img c) (cd_tr c ++ [s]).

(** The position the appended step occupies, and the state / log it is
    admitted at.  Both are functions of [c] alone. *)
Definition cd_end (c : cand) : nat := length (cd_tr c).
Definition cand_last_st (c : cand) : mstate := stt (cand_exec c) (cd_end c).
Definition cd_log_end (c : cand) : list wmsg := cd_log c (cd_end c).

Lemma cand_snoc_img c s : cd_img (cand_snoc c s) = cd_img c.
Proof. done. Qed.

Lemma cand_snoc_tr c s : cd_tr (cand_snoc c s) = cd_tr c ++ [s].
Proof. done. Qed.

Lemma cd_end_snoc c s : cd_end (cand_snoc c s) = S (cd_end c).
Proof. rewrite /cd_end /= length_app /=. lia. Qed.

Lemma cand_snoc_tr_lt c s k :
  (k < cd_end c)%nat → cd_tr (cand_snoc c s) !! k = cd_tr c !! k.
Proof. intros Hk. rewrite /= lookup_app_l //. Qed.

Lemma cand_snoc_tr_end c s : cd_tr (cand_snoc c s) !! cd_end c = Some s.
Proof.
  have Hle : (length (cd_tr c) ≤ cd_end c)%nat by rewrite /cd_end.
  rewrite /= (lookup_app_r (cd_tr c) [s] (cd_end c) Hle) /cd_end Nat.sub_diag //.
Qed.

(** The replay is a fold, so a longer trace agrees on every earlier state. *)
Lemma replay_app_le σ tr tr' k :
  (k ≤ length tr)%nat → replay σ (tr ++ tr') !! k = replay σ tr !! k.
Proof.
  revert σ k. induction tr as [|s0 tr IH]; intros σ k Hk.
  - assert (k = 0%nat) as -> by (simpl in Hk; lia). by rewrite !replay_0.
  - destruct k as [|k]; [by rewrite !replay_0|].
    rewrite /= -/replay. apply IH. simpl in Hk. lia.
Qed.

Lemma cand_snoc_stt c s k :
  (k ≤ cd_end c)%nat →
  stt (cand_exec (cand_snoc c s)) k = stt (cand_exec c) k.
Proof.
  intros Hk. rewrite /stt /cand_exec /= /cand_init /=.
  by rewrite (replay_app_le _ (cd_tr c) [s] k Hk).
Qed.

Lemma cand_snoc_last_st c s :
  stt (cand_exec (cand_snoc c s)) (cd_end c) = cand_last_st c.
Proof. by rewrite (cand_snoc_stt c s _ (Nat.le_refl _)). Qed.

Lemma cand_snoc_log c s k :
  (k ≤ cd_end c)%nat → cd_log (cand_snoc c s) k = cd_log c k.
Proof. intros Hk. rewrite /cd_log /= take_app_le //. Qed.

Lemma cd_log_end_full c : cd_log_end c = tr_msgs (cd_tr c).
Proof. apply cd_log_full. Qed.

(** THE NEW LOG = THE OLD LOG ++ THE STEP'S MESSAGES. *)
Lemma cd_log_end_snoc c s :
  cd_log_end (cand_snoc c s) = cd_log_end c ++ es_msg s.
Proof.
  rewrite !cd_log_end_full /= tr_msgs_app /=. by rewrite app_nil_r.
Qed.

(** The last state's image and log, in candidate vocabulary. *)
Lemma cand_last_img c : ms_img (cand_last_st c) = cd_img c.
Proof. rewrite /cand_last_st -/(eimg (cand_exec c) (cd_end c)). by apply cand_eimg. Qed.

Lemma cand_last_log c : ms_log (cand_last_st c) = cd_log_end c.
Proof. rewrite /cand_last_st -/(elog (cand_exec c) (cd_end c)). by apply cand_elog. Qed.

(* ====================================================================== *)
(** * 2. CONSISTENCY IS EXACTLY REACHABILITY, AND EXTENSION IS LOCAL *)

Lemma srvwmo_wf c : srvwmo_consistent c → exec_wf (cand_exec c).
Proof. intros Hc. by destruct (srvwmo_realizable c Hc) as (? & ? & ?). Qed.

(** Every step of a consistent candidate is admissible at its own replay
    state — the inverse direction of [cand_reachable]. *)
Lemma srvwmo_step_ok c k s :
  srvwmo_consistent c → cd_tr c !! k = Some s →
  mstep_ok (stt (cand_exec c) k) (es_ag s) (es_lb s).
Proof.
  intros Hc Hs. pose proof (srvwmo_wf c Hc) as Hwf.
  assert (Hs' : ex_tr (cand_exec c) !! k = Some s) by (rewrite cand_ex_tr //).
  exact (proj2 (mstep_det _ _ _ _ (exec_step_at (cand_exec c) k s Hwf Hs'))).
Qed.

(** THE EXTENSION THEOREM.  One local side condition; nothing global is
    re-proved. *)
Theorem snoc_consistent c s :
  srvwmo_consistent c →
  mstep_ok (cand_last_st c) (es_ag s) (es_lb s) →
  srvwmo_consistent (cand_snoc c s).
Proof.
  intros Hc Hok. apply srvwmo_of_wf, cand_reachable.
  intros k s' Hs'.
  pose proof (lookup_lt_Some _ _ _ Hs') as Hlt.
  rewrite cand_snoc_tr length_app /= in Hlt.
  destruct (decide (k < cd_end c)%nat) as [Hk|Hk].
  - rewrite (cand_snoc_tr_lt c s k Hk) in Hs'.
    rewrite (cand_snoc_stt c s k ltac:(lia)).
    by eapply srvwmo_step_ok.
  - assert (k = cd_end c) as -> by (rewrite /cd_end in Hlt Hk |- *; lia).
    rewrite (cand_snoc_tr_end c s) in Hs'. simplify_eq.
    by rewrite cand_snoc_last_st.
Qed.

(** Boundedness of the last state — the one machine-side fact the LATEST
    variant needs, and it comes free from reachability. *)
Lemma cand_last_bounded c : srvwmo_consistent c → cfg_bounded (cand_last_st c).
Proof.
  intros Hc. rewrite /cand_last_st. apply cand_bounded_upto.
  - rewrite /cd_end. lia.
  - intros k s Hk Hs. by eapply srvwmo_step_ok.
Qed.

(* ====================================================================== *)
(** * 3. THE APPENDED WRITE, FENCE AND RMW *)

(** WRITES ARE ALWAYS APPENDABLE.  [mstep]'s store arm has exactly one side
    condition — the message is nonempty — and rule 14 is trace order, which a
    snoc satisfies by construction. *)
Theorem snoc_write_consistent c i rl base vs kc :
  srvwmo_consistent c → vs ≠ [] →
  srvwmo_consistent (cand_snoc c (EStep i (LStore rl base vs kc))).
Proof. intros Hc Hne. by apply snoc_consistent. Qed.

Theorem snoc_fence_consistent c i pr pw sr sw :
  srvwmo_consistent c →
  srvwmo_consistent (cand_snoc c (EStep i (LFence pr pw sr sw))).
Proof. intros Hc. by apply snoc_consistent. Qed.

(* ====================================================================== *)
(** * 4. THE ADMISSIBLE READ LABEL

    §4.1 the general (older-source) condition, §4.2 the latest-source label
    and the fact that it always satisfies it. *)

(** ** 4.1 The candidate-side read-admissibility condition

    THE ANSWER TO (ii), in the candidate's own vocabulary.  [cd_floor] is the
    agent's per-byte read floor at the end of [c]: its load pre-view joined
    with its coherence floor for that byte. *)
Definition cd_floor (c : cand) (i : agent) (aq : bool) (a : Z) : nat :=
  Nat.max (load_vpre (ms_ws (cand_last_st c) i) aq)
          (coh (ms_ws (cand_last_st c) i) a).

Definition snoc_rd_adm (c : cand) (i : agent) (aq : bool) (base : Z)
    (ts : list nat) (vs : list (bv 8)) : Prop :=
  length vs = length ts ∧
  (* the named source really carries the named value ... *)
  (∀ (j : nat) t v, ts !! j = Some t → vs !! j = Some v →
     log_byte (cd_img c) (cd_log_end c) t (acc_addr base j) = Some v) ∧
  (* ... and nothing the agent has already observed overwrites it *)
  (∀ (j : nat) t, ts !! j = Some t →
     ¬ writes_in (cd_log_end c) (acc_addr base j) t
         (cd_floor c i aq (acc_addr base j))).

Lemma snoc_rd_ok c i aq base ts vs :
  snoc_rd_adm c i aq base ts vs →
  rd_ok (ms_img (cand_last_st c)) (ms_log (cand_last_st c))
        (ms_ws (cand_last_st c) i) aq base ts vs.
Proof.
  intros (Hlen & Hval & Hcoh). rewrite cand_last_img cand_last_log.
  split; [exact Hlen|]. intros j t v Hj Hv.
  split; [by eapply Hval|]. split.
  - rewrite (Hval j t v Hj Hv). by eexists.
  - exact (Hcoh j t Hj).
Qed.

(** THE OLDER-SOURCE VARIANT. *)
Theorem snoc_read_consistent c i aq base ts vs :
  srvwmo_consistent c → snoc_rd_adm c i aq base ts vs →
  srvwmo_consistent (cand_snoc c (EStep i (LLoad aq base ts vs))).
Proof. intros Hc Hadm. apply snoc_consistent; [done|]. by apply snoc_rd_ok. Qed.

(** ** 4.2 The latest-source read label

    Per byte: the index is [WeakMem.latest_ts] of the candidate's own log —
    the SAME 1-based convention the candidate uses everywhere (0 is the
    era-initial image, [S i] is log entry [i]) — and the value is that
    index's byte. *)
Definition lrd_ts (c : cand) (base : Z) (n : nat) : list nat :=
  (λ j, latest_ts (cd_log_end c) (acc_addr base j)) <$> seq 0 n.

Definition lrd_vs (c : cand) (base : Z) (n : nat) : list (bv 8) :=
  (λ j, default (bv_0 8)
          (log_byte (cd_img c) (cd_log_end c)
             (latest_ts (cd_log_end c) (acc_addr base j)) (acc_addr base j)))
  <$> seq 0 n.

Definition latest_read_lbl (c : cand) (aq : bool) (base : Z) (n : nat) : lbl :=
  LLoad aq base (lrd_ts c base n) (lrd_vs c base n).

(** The footprint's bytes exist at all — the only hypothesis (i) needs. *)
Definition latest_bytes_ok (c : cand) (base : Z) (n : nat) : Prop :=
  ∀ (j : nat), (j < n)%nat →
    is_Some (log_byte (cd_img c) (cd_log_end c)
               (latest_ts (cd_log_end c) (acc_addr base j)) (acc_addr base j)).

Lemma lrd_ts_lookup c base n j t :
  lrd_ts c base n !! j = Some t →
  (j < n)%nat ∧ t = latest_ts (cd_log_end c) (acc_addr base j).
Proof.
  rewrite /lrd_ts list_lookup_fmap. intros Heq.
  apply fmap_Some in Heq as (x & Hx & ->).
  apply lookup_seq in Hx as [-> Hlt]. by split.
Qed.

Lemma lrd_vs_lookup c base n j v :
  lrd_vs c base n !! j = Some v →
  (j < n)%nat ∧
  v = default (bv_0 8)
        (log_byte (cd_img c) (cd_log_end c)
           (latest_ts (cd_log_end c) (acc_addr base j)) (acc_addr base j)).
Proof.
  rewrite /lrd_vs list_lookup_fmap. intros Heq.
  apply fmap_Some in Heq as (x & Hx & ->).
  apply lookup_seq in Hx as [-> Hlt]. by split.
Qed.

Lemma lrd_length c base n :
  length (lrd_vs c base n) = length (lrd_ts c base n).
Proof. by rewrite /lrd_vs /lrd_ts !length_fmap. Qed.

(** THE ANSWER TO (i): the latest-source label always satisfies §4.1's
    condition, for any agent and any annotation. *)
Lemma latest_snoc_rd_adm c i aq base n :
  srvwmo_consistent c → latest_bytes_ok c base n →
  snoc_rd_adm c i aq base (lrd_ts c base n) (lrd_vs c base n).
Proof.
  intros Hc Hb. pose proof (cand_last_bounded c Hc) as Hbd.
  pose proof (Hbd i) as Hbi. rewrite cand_last_log in Hbi.
  split_and!.
  - apply lrd_length.
  - intros j t v Hj Hv.
    destruct (lrd_ts_lookup c base n j t Hj) as (_ & ->).
    destruct (lrd_vs_lookup c base n j v Hv) as (Hjn & ->).
    by destruct (Hb j Hjn) as [w Hw]; rewrite Hw.
  - intros j t Hj.
    destruct (lrd_ts_lookup c base n j t Hj) as (Hjn & ->).
    intros Hw. apply (latest_ts_top (cd_log_end c) (acc_addr base j)).
    eapply writes_in_mono_hi; [|exact Hw].
    rewrite /cd_floor.
    pose proof (load_vpre_bounded (ms_ws (cand_last_st c) i) aq
                  (length (cd_log_end c)) Hbi).
    destruct Hbi as (_ & _ & _ & _ & _ & _ & Hcoh & _).
    pose proof (Hcoh (acc_addr base j)). lia.
Qed.

Theorem snoc_latest_consistent c i aq base n :
  srvwmo_consistent c → latest_bytes_ok c base n →
  srvwmo_consistent (cand_snoc c (EStep i (latest_read_lbl c aq base n))).
Proof.
  intros Hc Hb. apply snoc_read_consistent; [done|].
  by apply latest_snoc_rd_adm.
Qed.

(** ** 4.3 The appended RMW

    ATOMICITY IS THE EXTRA DEMAND: [mstep]'s [LRmw] arm carries
    [rmw_latest], so an appended read-modify-write must name the LATEST
    message of every byte — the older-source freedom of §4.1 is a LOAD-only
    freedom. *)
Theorem snoc_rmw_consistent c i aq rl base ts rvs wvs kc :
  srvwmo_consistent c → wvs ≠ [] → length wvs = length ts →
  snoc_rd_adm c i aq base ts rvs →
  (∀ (j : nat) t, ts !! j = Some t →
     latest (cd_img c) (cd_log_end c) (acc_addr base j) t) →
  srvwmo_consistent (cand_snoc c (EStep i (LRmw aq rl base ts rvs wvs kc))).
Proof.
  intros Hc Hne Hlen Hadm Hlat. apply snoc_consistent; [done|].
  split_and!; [exact Hne|exact Hlen|by apply snoc_rd_ok|].
  rewrite cand_last_img cand_last_log. exact Hlat.
Qed.

(** ... and its latest-source instance, where atomicity is free. *)
Theorem snoc_rmw_latest_consistent c i aq rl base n wvs kc :
  srvwmo_consistent c → latest_bytes_ok c base n →
  wvs ≠ [] → length wvs = n →
  srvwmo_consistent
    (cand_snoc c (EStep i (LRmw aq rl base (lrd_ts c base n)
                             (lrd_vs c base n) wvs kc))).
Proof.
  intros Hc Hb Hne Hlen. eapply snoc_rmw_consistent; [done|done| | |].
  - rewrite /lrd_ts length_fmap length_seq. exact Hlen.
  - by apply latest_snoc_rd_adm.
  - intros j t Hj. destruct (lrd_ts_lookup c base n j t Hj) as (Hjn & ->).
    by apply latest_ts_latest, Hb.
Qed.

(* ====================================================================== *)
(** * 5. THE PROGRAM SIDE

    From here on the file is in [WeakRvwmoConf]'s import context, so the
    WLABEL constructors are the unqualified ones and the axiomatic label
    constructors are written qualified.  The requires are placed HERE, after
    §1-§4, precisely so that the candidate-level sections above can spell
    [LLoad]/[LStore]/[LRmw] plainly. *)
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
Require Import WeakRvwmoConf.
Require Import WeakRvwmoSupply.
Require Import WeakEvLift.
Require Import WeakEvStarted.
Require Import WeakRvwmoConfWit.

(** ** 5.1 The extended supply

    [pst]/[dv] are extended by ONE position: everything at or below the old
    end is unchanged, and everything above is the block's post-state.  (The
    supply is read only at [cd_end c] and [S (cd_end c)] by the new position,
    so the value at higher indices is irrelevant and chosen constant.) *)
Definition pst_snoc (c : cand) (pst : nat → list pexv6) (i : agent)
    (p' : pexv6) : nat → list pexv6 :=
  λ k, if bool_decide (k ≤ cd_end c)%nat
       then pst k else <[i := p']> (pst (cd_end c)).

Definition dv_snoc (c : cand) (dv : nat → dev_state) (d' : dev_state)
    : nat → dev_state :=
  λ k, if bool_decide (k ≤ cd_end c)%nat then dv k else d'.

Lemma pst_snoc_le c pst i p' k :
  (k ≤ cd_end c)%nat → pst_snoc c pst i p' k = pst k.
Proof. intros H. rewrite /pst_snoc bool_decide_eq_true_2 //. Qed.

Lemma pst_snoc_gt c pst i p' k :
  (cd_end c < k)%nat → pst_snoc c pst i p' k = <[i := p']> (pst (cd_end c)).
Proof. intros H. rewrite /pst_snoc bool_decide_eq_false_2 //. lia. Qed.

Lemma dv_snoc_le c dv d' k : (k ≤ cd_end c)%nat → dv_snoc c dv d' k = dv k.
Proof. intros H. rewrite /dv_snoc bool_decide_eq_true_2 //. Qed.

Lemma dv_snoc_gt c dv d' k : (cd_end c < k)%nat → dv_snoc c dv d' k = d'.
Proof. intros H. rewrite /dv_snoc bool_decide_eq_false_2 //. lia. Qed.

(** THE PROGRAM-SIDE EXTENSION THEOREM (the [HEone] block shape). *)
Theorem exec_prog_ok'_snoc c i p pa da ls l lb p' d' pst dv :
  exec_prog_ok' pstep_ev pcls_ev pst dv (cand_exec c) →
  pst (cd_end c) !! i = Some p →
  adm_run true p (dv (cd_end c)) ls pa da →
  hlbl_realizes pa (ms_ws (cand_last_st c) i) lb l →
  pstep_ev pa da l p' d' →
  exec_prog_ok' pstep_ev pcls_ev (pst_snoc c pst i p') (dv_snoc c dv d')
    (cand_exec (cand_snoc c (EStep i lb))).
Proof.
  intros Hpo Hp Hrun Hre Hst k s Hs. rewrite cand_ex_tr in Hs.
  pose proof (lookup_lt_Some _ _ _ Hs) as Hlt.
  rewrite cand_snoc_tr length_app /= in Hlt.
  destruct (decide (k < cd_end c)%nat) as [Hk|Hk].
  - rewrite (cand_snoc_tr_lt c _ k Hk) in Hs.
    destruct (Hpo k s ltac:(by rewrite cand_ex_tr))
      as (q & qa & qd & q' & H1 & H2 & H3 & H4).
    exists q, qa, qd, q'.
    rewrite (pst_snoc_le c pst i p' k ltac:(lia))
            (pst_snoc_le c pst i p' (S k) ltac:(lia))
            (dv_snoc_le c dv d' k ltac:(lia))
            (dv_snoc_le c dv d' (S k) ltac:(lia))
            (cand_snoc_stt c _ k ltac:(lia)).
    split_and!; [exact H1|exact H2|exact H3|exact H4].
  - assert (k = cd_end c) as -> by (rewrite /cd_end in Hlt Hk |- *; lia).
    rewrite (cand_snoc_tr_end c (EStep i lb)) in Hs. simplify_eq.
    exists p, pa, da, p'. simpl.
    rewrite (pst_snoc_le c pst i p' (cd_end c) ltac:(lia))
            (pst_snoc_gt c pst i p' (S (cd_end c)) ltac:(lia))
            (dv_snoc_le c dv d' (cd_end c) ltac:(lia))
            (dv_snoc_gt c dv d' (S (cd_end c)) ltac:(lia))
            cand_snoc_last_st.
    split_and!; [exact Hp|done|exact (adm_run_star _ _ _ _ _ _ Hrun)|].
    left. exists l. split; [|exact Hst]. by apply hlbl_realizes_ax.
Qed.

(** ... and the [HEpair] block shape (a fused exclusive pair). *)
Theorem exec_prog_ok'_snoc_pair c i p pa da ls1 l1 l2 lb pm dm ls2 pm2 dm2
    p' d' pst dv :
  exec_prog_ok' pstep_ev pcls_ev pst dv (cand_exec c) →
  pst (cd_end c) !! i = Some p →
  adm_run true p (dv (cd_end c)) ls1 pa da →
  hlbl_realizes_pair pa pm2 (ms_ws (cand_last_st c) i) lb l1 l2 →
  pstep_ev pa da l1 pm dm →
  adm_run false pm dm ls2 pm2 dm2 →
  pstep_ev pm2 dm2 l2 p' d' →
  exec_prog_ok' pstep_ev pcls_ev (pst_snoc c pst i p') (dv_snoc c dv d')
    (cand_exec (cand_snoc c (EStep i lb))).
Proof.
  intros Hpo Hp Hrun Hre Hs1 Hrun2 Hs2 k s Hs. rewrite cand_ex_tr in Hs.
  pose proof (lookup_lt_Some _ _ _ Hs) as Hlt.
  rewrite cand_snoc_tr length_app /= in Hlt.
  destruct (decide (k < cd_end c)%nat) as [Hk|Hk].
  - rewrite (cand_snoc_tr_lt c _ k Hk) in Hs.
    destruct (Hpo k s ltac:(by rewrite cand_ex_tr))
      as (q & qa & qd & q' & H1 & H2 & H3 & H4).
    exists q, qa, qd, q'.
    rewrite (pst_snoc_le c pst i p' k ltac:(lia))
            (pst_snoc_le c pst i p' (S k) ltac:(lia))
            (dv_snoc_le c dv d' k ltac:(lia))
            (dv_snoc_le c dv d' (S k) ltac:(lia))
            (cand_snoc_stt c _ k ltac:(lia)).
    split_and!; [exact H1|exact H2|exact H3|exact H4].
  - assert (k = cd_end c) as -> by (rewrite /cd_end in Hlt Hk |- *; lia).
    rewrite (cand_snoc_tr_end c (EStep i lb)) in Hs. simplify_eq.
    exists p, pa, da, p'. simpl.
    rewrite (pst_snoc_le c pst i p' (cd_end c) ltac:(lia))
            (pst_snoc_gt c pst i p' (S (cd_end c)) ltac:(lia))
            (dv_snoc_le c dv d' (cd_end c) ltac:(lia))
            (dv_snoc_gt c dv d' (S (cd_end c)) ltac:(lia))
            cand_snoc_last_st.
    split_and!; [exact Hp|done|exact (adm_run_star _ _ _ _ _ _ Hrun)|].
    right. exists pm, dm, pm2, dm2, l1, l2.
    split_and!; [|exact Hs1|exact (adm_run_star _ _ _ _ _ _ Hrun2)|exact Hs2].
    by apply hlbl_realizes_pair_ax.
Qed.

(** ** 5.2 THE relp BRIDGE

    [hemit] states its projection equation at the PER-HART fold [row_ws]; the
    theorems above want it at the candidate's [ms_ws].  The only thing the
    equation reads of the state is [w_relp] ([WeakRvwmoConf]'s §1), and
    [WeakRvwmoSupply.cand_ws_relp] equates the two — this is
    [supply_of_qconf]'s step, at the single position [cd_end c]. *)
Lemma cand_last_ws_relp c i :
  w_relp (ms_ws (cand_last_st c) i)
  = w_relp (row_ws (trow i (cd_tr c)) (tcnt i (cd_tr c))).
Proof.
  have Hte : take (cd_end c) (cd_tr c) = cd_tr c
    by (apply take_ge; rewrite /cd_end; lia).
  rewrite /cand_last_st (cand_ws_relp c i (cd_end c) ltac:(rewrite /cd_end; lia)).
  by rewrite Hte.
Qed.

Lemma hlbl_realizes_row_end c i p lb l :
  hlbl_realizes p (row_ws (trow i (cd_tr c)) (tcnt i (cd_tr c))) lb l →
  hlbl_realizes p (ms_ws (cand_last_st c) i) lb l.
Proof. apply hlbl_realizes_relp, cand_last_ws_relp. Qed.

Lemma hlbl_realizes_pair_row_end c i p pm lb l1 l2 :
  hlbl_realizes_pair p pm (row_ws (trow i (cd_tr c)) (tcnt i (cd_tr c))) lb l1 l2 →
  hlbl_realizes_pair p pm (ms_ws (cand_last_st c) i) lb l1 l2.
Proof. apply hlbl_realizes_pair_relp, cand_last_ws_relp. Qed.

(* ====================================================================== *)
(** * 6. SMOKE / NON-VACUITY

    A CONCRETE extension, with the real machine's block: the [sw &started]
    store of xv6's [main] ([WeakRvwmoConfWit]'s [ev_*] objects — the monad
    node, its request, the emitted wlabel and the realizing [pstep_ev] are
    all the real kernel's), appended to the empty candidate over an
    arbitrary boot image.  Both halves are instantiated: the extended
    candidate is [srvwmo_consistent], and [exec_prog_ok'] holds of the
    one-position supply.  The appended message is COMPUTED. *)

Section smoke.
  Context (img : WeakMem.image) (cpu : CPU) (rs : regstate) (ib : oib32)
          (d0 : dev_state).

  (** The candidate before the block: empty trace over [img]. *)
  Definition sm_c : cand := Cand img [].

  (** The axiomatic label of the block ([WeakRvwmoConfWit.ev_row]'s only
      element). *)
  Definition sm_lb : WeakAxiomatic.lbl :=
    WeakAxiomatic.LStore false (pa_z ev_flag)
      (wbytes 4 WeakLock.lock_one) WCplain.

  Lemma sm_consistent : srvwmo_consistent sm_c.
  Proof.
    apply srvwmo_of_wf, cand_reachable. intros k s Hs. by destruct k.
  Qed.

  Lemma sm_ws : ms_ws (cand_last_st sm_c) 0%nat = ws_init.
  Proof. done. Qed.

  Lemma sm_bytes : wbytes 4 WeakLock.lock_one ≠ [].
  Proof.
    have Hl : length (wbytes 4 WeakLock.lock_one) = 4%nat
      by apply (wbytes_length 4).
    intros H. by rewrite H /= in Hl.
  Qed.

  (** (a) THE AXIOMATIC HALF. *)
  Theorem sm_snoc_consistent :
    srvwmo_consistent (cand_snoc sm_c (EStep 0%nat sm_lb)).
  Proof. apply snoc_write_consistent; [apply sm_consistent|apply sm_bytes]. Qed.

  (** ... and the extended log, COMPUTED: one message, the real store's. *)
  Lemma sm_snoc_log :
    cd_log_end (cand_snoc sm_c (EStep 0%nat sm_lb))
    = [WMsg (pa_z ev_flag) (wbytes 4 WeakLock.lock_one) (Some 0%nat) WCplain].
  Proof. by rewrite cd_log_end_snoc. Qed.

  (** (b) THE PROGRAM HALF. *)
  Definition sm_pst : nat → list pexv6 := λ _, [ev_p0 cpu rs ib].
  Definition sm_dv : nat → dev_state := λ _, d0.

  Lemma sm_prog0 : exec_prog_ok' pstep_ev pcls_ev sm_pst sm_dv (cand_exec sm_c).
  Proof. intros k s Hs. rewrite cand_ex_tr in Hs. by destruct k. Qed.

  Theorem sm_snoc_prog :
    exec_prog_ok' pstep_ev pcls_ev
      (pst_snoc sm_c sm_pst 0%nat (ev_p1 cpu rs ib))
      (dv_snoc sm_c sm_dv d0)
      (cand_exec (cand_snoc sm_c (EStep 0%nat sm_lb))).
  Proof.
    eapply (exec_prog_ok'_snoc sm_c 0%nat (ev_p0 cpu rs ib) (ev_p0 cpu rs ib)
              d0 [] (ev_wl ib) sm_lb (ev_p1 cpu rs ib) d0 sm_pst sm_dv).
    - apply sm_prog0.
    - done.
    - apply ARnil.
    - rewrite sm_ws. apply ev_realizes.
    - apply ev_pstep.
  Qed.
End smoke.

(** The LATEST-source read is non-vacuous too: over a TOTAL image the
    latest-source label of ANY footprint is appendable, at any agent and any
    annotation — [latest_bytes_ok] is its whole content. *)
Corollary sm_latest_consistent (i : agent) (aq : bool) (base : Z) (n : nat) :
  srvwmo_consistent
    (cand_snoc (sm_c (λ _, Some (bv_0 8)))
       (EStep i (latest_read_lbl (sm_c (λ _, Some (bv_0 8))) aq base n))).
Proof.
  apply snoc_latest_consistent; [apply sm_consistent|].
  intros j Hj. rewrite /cd_log_end /cd_log /=. by eexists.
Qed.

(** THE POINT, with the objects hidden: the two extension theorems are
    JOINTLY inhabited at a real, nonempty block. *)
Corollary cand_extend_block_nonempty :
  ∃ (c : cand) (s : estep) (pst : nat → list pexv6) (dv : nat → dev_state),
    cd_tr c = [] ∧
    srvwmo_consistent (cand_snoc c s) ∧
    cd_log_end (cand_snoc c s) ≠ [] ∧
    exec_prog_ok' pstep_ev pcls_ev pst dv (cand_exec (cand_snoc c s)).
Proof.
  exists (sm_c (λ _, None)), (EStep 0%nat sm_lb),
         (pst_snoc (sm_c (λ _, None)) (sm_pst 0%fin ev_rs0 ib_none) 0%nat
            (ev_p1 0%fin ev_rs0 ib_none)),
         (dv_snoc (sm_c (λ _, None)) (sm_dv dev0_state) dev0_state).
  split_and!.
  - done.
  - apply sm_snoc_consistent.
  - rewrite (sm_snoc_log (λ _, None)). done.
  - apply sm_snoc_prog.
Qed.

(* ====================================================================== *)
(** * 7. AUDIT *)

Print Assumptions snoc_consistent.
Print Assumptions snoc_latest_consistent.
Print Assumptions snoc_read_consistent.
Print Assumptions snoc_rmw_consistent.
Print Assumptions exec_prog_ok'_snoc.
Print Assumptions exec_prog_ok'_snoc_pair.
Print Assumptions cand_extend_block_nonempty.
Print Assumptions sm_latest_consistent.
