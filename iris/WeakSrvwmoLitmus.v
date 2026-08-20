(** * WeakSrvwmoLitmus.v — the litmus suite AGAINST THE sRVWMO DEFINITION

    [WeakLitmus.v] runs the litmus programs on the OPERATIONAL machine (the
    tiny hart/config LTS) and settles each verdict by an invariant over
    reachable configurations.  This file settles the SAME verdicts against
    the MODEL: [WeakAxiomatic3]'s [srvwmo_consistent], the named
    axiomatization whose realizability theorem is T1
    ([WeakAxiomatic3.srvwmo_realizable]).

    That is a different claim, and it is the one the paper's corollary (b)
    needs ("LB must be unobservable; everything else must match riscv.cat
    verdicts", design doc §3): an operational verdict is about our
    interpreter, a verdict against [srvwmo_consistent] is about the declared
    hardware class.  A positive verdict here is a machine-checked
    sRVWMO-consistent candidate — hence, THROUGH T1, a promise-free machine
    run; a negative verdict is a machine-checked refutation of the whole
    candidate FAMILY with the outcome pinned, i.e. an axiom-level fact about
    the model that no interleaving argument is needed to believe.

    THE VERDICT TABLE is at the bottom of the file (§9), together with the
    two DELIBERATE DIVERGENCES from RVWMO that the suite exposes.

    Contents:
      §1  per-agent positions in a candidate's trace ([ag_pos] and its four
          index lemmas) — the arithmetic that lets a program's instruction
          list be matched against the steps of ONE agent inside an
          interleaved candidate trace;
      §2  THE CONFORMANCE KIT: [instr_lbl] / [conforms] / [outc], and the
          glue [srvwmo_run] (consistent + conformant ⇒ machine run of the
          program) with its contrapositive [srvwmo_no_run];
      §3  two acyclicity lemmas the suite needs and [WeakAxiomatic3] §12 does
          not have: [coh_rel_acyc_ts] and [ob_op_acyc_w].  Both DROP §12's
          "no event both reads and writes a byte" hypothesis (which excludes
          every AMO) and [ob_op_acyc_w] additionally ADMITS the [ppo_op]
          po-into-a-write arm — the RULE 14 arm, which fires in every MP
          shape and which [WeakAxiomatic3] §15(1) priced at ~150 lines.  It
          costs ~70;
      §4  reading a value back to its writer ([cand_read_writer]);
      §5  POSITIVE verdicts (SB, MP-no-fence, MP-writer-fence-only, AMO);
      §6  NEGATIVE verdicts (LB — the headline; the MP core and its three
          fenced variants; CoRR);
      §7  the two landed precedents this file does NOT redo
          ([ce_rl_true_inconsistent], [ce_rl_stale_reachable], [ce_fwd]);
      §8  what is NOT done, with prices;
      §9  THE VERDICT TABLE.

    NO [Admitted], NO [Axiom]: [Print Assumptions] on every theorem below
    reports "Closed under the global context".

    DEPENDENCY-FREE like its inputs: stdpp, [WeakMem], [WeakLitmus],
    [WeakAxiomatic]{,2,3}.  A leaf — nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakLitmus WeakAxiomatic WeakAxiomatic2
     WeakAxiomatic3.

(** The litmus vocabulary, re-declared: [WeakLitmus]'s own [ax]/[ay]/[rg1]/
    [rg2] are [Local Notation]s. *)
Notation ax := (0%Z).
Notation ay := (8%Z).
Notation rg1 := (1%nat).
Notation rg2 := (2%nat).

(** fence rw,w — the release-side writer fence; fence r,rw — the acquire-side
    reader fence.  (Same spellings as [WeakLitmus].) *)
Notation FENCE_RW_W := (IFence true true false true).
Notation FENCE_R_RW := (IFence true false true true).

(* ================================================================== *)
(** * 1. Per-agent positions in a candidate's trace

    A candidate's trace is ONE interleaved list of steps; a litmus program is
    a per-agent instruction LIST.  [ag_pos tr i k] is the number of steps of
    agent [i] strictly before position [k] — i.e. WHICH instruction of agent
    [i]'s program the step at [k] is, when the step is agent [i]'s.  Four
    facts are all the suite ever needs of it: it is monotone, it advances by
    exactly one across a step of the agent, it has a PREDECESSOR (the descent
    every negative verdict runs on), and it is INJECTIVE on the agent's own
    steps (which identifies "the j-th instruction of agent i" uniquely). *)

Fixpoint ag_count (i : agent) (tr : list estep) : nat :=
  match tr with
  | [] => 0%nat
  | s :: tr' => (if bool_decide (es_ag s = i) then 1%nat else 0%nat) + ag_count i tr'
  end.

Definition ag_pos (tr : list estep) (i : agent) (k : nat) : nat :=
  ag_count i (take k tr).

Lemma ag_count_app i l1 l2 :
  ag_count i (l1 ++ l2) = (ag_count i l1 + ag_count i l2)%nat.
Proof. induction l1 as [|s l1 IH]; simpl; [done|lia]. Qed.

Lemma ag_pos_0 tr i : ag_pos tr i 0 = 0%nat.
Proof. done. Qed.

(** The step at [k], if it belongs to agent [i], advances [i]'s position by
    one; any other step leaves it alone. *)
Lemma ag_pos_S tr i k s :
  tr !! k = Some s →
  ag_pos tr i (S k) =
    ((if bool_decide (es_ag s = i) then 1%nat else 0%nat) + ag_pos tr i k)%nat.
Proof.
  intros Hs. rewrite /ag_pos (take_S_r _ _ _ Hs) ag_count_app /=. lia.
Qed.

Lemma ag_pos_S_none tr i k :
  tr !! k = None → ag_pos tr i (S k) = ag_pos tr i k.
Proof.
  intros Hs. apply lookup_ge_None in Hs.
  by rewrite /ag_pos (take_ge tr (S k) ltac:(lia)) (take_ge tr k ltac:(lia)).
Qed.

Lemma ag_pos_mono tr i k k' :
  (k ≤ k')%nat → (ag_pos tr i k ≤ ag_pos tr i k')%nat.
Proof.
  induction 1 as [|k'' Hle IH]; [done|].
  destruct (tr !! k'') as [s|] eqn:Hs.
  - rewrite (ag_pos_S tr i k'' s Hs). lia.
  - rewrite (ag_pos_S_none tr i k'' Hs). lia.
Qed.

(** THE DESCENT.  A step at agent-position [S j] has a predecessor step of the
    same agent, strictly earlier, at agent-position [j].  This is what turns
    "the store of a two-instruction hart ran" into "the load ran first". *)
Lemma ag_pos_prev tr i k j :
  ag_pos tr i k = S j →
  ∃ k' s', (k' < k)%nat ∧ tr !! k' = Some s' ∧ es_ag s' = i ∧
           ag_pos tr i k' = j.
Proof.
  induction k as [|k IH]; intros Hpos; [by rewrite ag_pos_0 in Hpos|].
  destruct (tr !! k) as [s|] eqn:Hs; last first.
  { rewrite (ag_pos_S_none tr i k Hs) in Hpos.
    destruct (IH Hpos) as (k' & s' & ? & ? & ? & ?).
    exists k', s'. split_and!; [lia|done|done|done]. }
  rewrite (ag_pos_S tr i k s Hs) in Hpos.
  destruct (bool_decide (es_ag s = i)) eqn:Hb.
  - exists k, s. split_and!; [lia|done|by apply bool_decide_eq_true in Hb|lia].
  - rewrite /= in Hpos.
    destruct (IH ltac:(lia)) as (k' & s' & ? & ? & ? & ?).
    exists k', s'. split_and!; [lia|done|done|done].
Qed.

(** ... and the position PINS the step: two steps of one agent at the same
    agent-position are the same step. *)
Lemma ag_pos_inj tr i k k' s s' :
  tr !! k = Some s → es_ag s = i → tr !! k' = Some s' → es_ag s' = i →
  ag_pos tr i k = ag_pos tr i k' → k = k'.
Proof.
  intros Hs Hag Hs' Hag' Heq.
  destruct (decide (k = k')) as [->|Hne]; [done|exfalso].
  destruct (decide (k < k')%nat) as [Hlt|Hgt].
  - pose proof (ag_pos_mono tr i (S k) k' ltac:(lia)) as Hle.
    rewrite (ag_pos_S tr i k s Hs) bool_decide_eq_true_2 // in Hle. lia.
  - pose proof (ag_pos_mono tr i (S k') k ltac:(lia)) as Hle.
    rewrite (ag_pos_S tr i k' s' Hs') bool_decide_eq_true_2 // in Hle. lia.
Qed.

(* ================================================================== *)
(** * 2. THE CONFORMANCE KIT

    A candidate ([WeakAxiomatic2.cand]) is an image plus an interleaved list
    of labelled steps; a litmus PROGRAM is one instruction list per agent.
    [conforms] is the relation "this candidate's per-agent label sequence is
    one this program can emit": the step at trace position [k] must be the
    instruction its agent's program has at that agent's own position, with

      - a LOAD free to take ANY timestamp and ANY value (that is the whole
        point — the model, not the program, decides what a load may see);
      - a STORE, a FENCE and an AMO's write half FIXED by the program.

    The instruction vocabulary is [WeakLitmus]'s, unchanged, so the six
    operational verdicts of that file are restatable here verbatim.  Note
    what conformance does NOT say: nothing forces a program to run to
    completion (a prefix of each hart's program is enough), and nothing
    forces the interleaving.  Both are right: a litmus outcome is an
    existential over interleavings, and the negatives below quantify over
    all of them. *)

Definition instr_lbl (ins : instr) (l : lbl) : Prop :=
  match ins with
  | ILoad _ a aq => ∃ t v, l = LLoad aq a [t] [v]
  | IStore a v => l = LStore false a [v] WCplain
  | IFence pr pw sr sw => l = LFence pr pw sr sw
  | IAmoSwapAq _ a v => ∃ t vv, l = LRmw true false a [t] [vv] [v] WCexcl
  end.

Notation prog := (list (list instr)).

Definition conforms (P : prog) (c : cand) : Prop :=
  ∀ k s, cd_tr c !! k = Some s →
    ∃ p ins, P !! es_ag s = Some p ∧
             p !! ag_pos (cd_tr c) (es_ag s) k = Some ins ∧
             instr_lbl ins (es_lb s).

(** THE OUTCOME PREDICATE.  Registers do not exist at candidate level, so an
    outcome names the READ VALUE of one instruction: "the [j]-th instruction
    of agent [i] read [v] at byte [a]".  It covers loads and AMO read halves
    alike ([lb_rd] is the read footprint of either). *)
Definition outc (c : cand) (i j : nat) (a : Z) (v : bv 8) : Prop :=
  ∃ k s t, cd_tr c !! k = Some s ∧ es_ag s = i ∧
           ag_pos (cd_tr c) i k = j ∧ lb_rd (es_lb s) = Some (a, [t], [v]).

(** *** The glue, in both directions *)

(** A candidate that is sRVWMO-consistent AND conformant is a promise-free
    MACHINE RUN OF THE PROGRAM: [WeakAxiomatic3.srvwmo_realizable] (T1) turns
    consistency into [exec_wf], and the trace it realizes is literally the
    candidate's, so conformance survives unchanged. *)
Theorem srvwmo_run (img : image) (P : prog) (c : cand) :
  cd_img c = img → conforms P c → srvwmo_consistent c →
  exec_wf (cand_exec c) ∧ ex_tr (cand_exec c) = cd_tr c ∧
  ex_img (cand_exec c) = img ∧ conforms P c.
Proof.
  intros <- Hconf Hcons.
  destruct (srvwmo_realizable c Hcons) as (Hwf & Htr & Himg).
  by split_and!.
Qed.

(** The converse, which the negatives need: a machine run IS an
    sRVWMO-consistent candidate.  [cand_shape] and [cand_values] are read off
    the step relation; the eight axioms, [ax_rel_ord] and [ob]-acyclicity are
    slices 1 and 2's soundness theorems. *)
Lemma cand_shape_of_wf c : exec_wf (cand_exec c) → cand_shape c.
Proof.
  intros Hwf k s Hs.
  assert (Hs' : ex_tr (cand_exec c) !! k = Some s) by (rewrite cand_ex_tr //).
  pose proof (exec_step_at (cand_exec c) k s Hwf Hs') as Hstep.
  destruct (es_lb s) as [aq base ts vs|rl base vs kc|pr pw sr sw|
                         aq rl base ts rvs wvs kc] eqn:Hl;
    inversion Hstep; simplify_eq.
  - match goal with H : rd_ok _ _ _ _ _ _ _ |- _ => exact (proj1 H) end.
  - assumption.
  - done.
  - split_and!; [assumption|assumption|
      match goal with H : rd_ok _ _ _ _ _ _ _ |- _ => exact (proj1 H) end].
Qed.

Lemma cand_values_of_wf c : exec_wf (cand_exec c) → cand_values c.
Proof.
  intros Hwf k s base ts vs Hs Hrd j t v Hj Hv.
  pose proof (lookup_lt_Some _ _ _ Hs) as Hk.
  assert (Hs' : ex_tr (cand_exec c) !! k = Some s) by (rewrite cand_ex_tr //).
  destruct (exec_rd_ok (cand_exec c) k s base ts vs Hwf Hs' Hrd) as [_ Hall].
  destruct (Hall j t v Hj Hv) as [Hlb _].
  by rewrite (cand_eimg c k ltac:(lia)) (cand_elog c k ltac:(lia)) in Hlb.
Qed.

Theorem srvwmo_of_wf c : exec_wf (cand_exec c) → srvwmo_consistent c.
Proof.
  intros Hwf. split_and!.
  - by apply cand_shape_of_wf.
  - by apply cand_values_of_wf.
  - split_and!; [by apply promise_free_sound|by apply sound_rel_ord
                |by apply promise_free_ob_acyclic].
Qed.

(** THE CONTRAPOSITIVE, in the shape every negative verdict below is stated
    in: if NO conformant candidate with outcome [Out] is sRVWMO-consistent,
    then no promise-free machine run of the program has that outcome. *)
Theorem srvwmo_no_run (P : prog) (Out : cand → Prop) :
  (∀ c, conforms P c → Out c → ¬ srvwmo_consistent c) →
  ∀ c, conforms P c → Out c → ¬ exec_wf (cand_exec c).
Proof. intros Hno c Hconf Hout Hwf. exact (Hno c Hconf Hout (srvwmo_of_wf c Hwf)). Qed.

(* ================================================================== *)
(** * 3. Two acyclicity lemmas, generalising [WeakAxiomatic3] §12

    [coh_rel_acyc_simple] and [ob_op_acyc_simple] both assume NO EVENT BOTH
    READS AND WRITES A BYTE — which excludes every AMO — and
    [ob_op_acyc_simple] additionally assumes NO [ppo_op] EDGE AT ALL, which
    excludes every candidate in which one hart stores twice (the RULE 14 arm
    fires).  Between them that rules out MP, CoRR and the AMO shape, i.e.
    most of this suite.

    Both hypotheses come off here.  The fused-RMW case is discharged by
    [ax_atomicity] (an RMW's own write is above every write its read half is
    [fr]-before), and the rule-14 arm by [ets_lt_wr] (everything an agent has
    done sits strictly below the timestamp of a po-later store).
    [WeakAxiomatic3] §15(1) priced the [ppo_op] generalisation at ~150 lines;
    with [ets_lt_wr] factored out it is ~70 including the RMW half. *)

Lemma cand_shape_rd c k s base ts vs :
  cand_shape c → cd_tr c !! k = Some s → lb_rd (es_lb s) = Some (base, ts, vs) →
  length vs = length ts.
Proof.
  intros Hsh Hs Hrd. pose proof (Hsh k s Hs) as H.
  destruct (es_lb s); simplify_eq/=; naive_solver.
Qed.

(** [WeakAxiomatic2.lb_rd_ts_reads] without [exec_wf] — [cand_shape] is what
    that proof actually consumed. *)
Lemma cand_lb_rd_ts_reads c k s a t :
  cand_shape c → cd_tr c !! k = Some s → lb_rd_ts (es_lb s) a = Some t →
  ∃ v, reads_at (cand_exec c) k a t v.
Proof.
  intros Hsh Hs. rewrite /lb_rd_ts.
  destruct (lb_rd (es_lb s)) as [[[base ts] vs]|] eqn:Hrd; [|done].
  case_bool_decide as Hle; [|done]. intros Hj.
  pose proof (cand_shape_rd c k s base ts vs Hsh Hs Hrd) as Hlen.
  destruct (lookup_lt_is_Some_2 vs (Z.to_nat (a - base))) as [v Hv].
  { rewrite Hlen. by eapply lookup_lt_Some. }
  exists v, s, base, ts, vs, (Z.to_nat (a - base)).
  rewrite cand_ex_tr. split_and!; [done|done|done|done|rewrite /acc_addr; lia].
Qed.

(** THE RULE-14 ARITHMETIC.  Everything an agent occupies at any byte before
    position [k2] is strictly below the timestamp of a write at [k2].  This
    is the whole content of ppo rule 14 in the candidate presentation, where
    the trace order IS the global memory order. *)
Lemma ets_lt_wr c a1 e1 a2 k2 :
  cand_shape c → cand_values c →
  (∀ k1, e1 = ev_at k1 → (k1 < k2)%nat) →
  wr_b (cand_exec c) a2 (ev_at k2) →
  (ets (cand_exec c) a1 e1 < ets (cand_exec c) a2 (ev_at k2))%nat.
Proof.
  intros Hsh Hval Hlt Hw2.
  destruct (cand_wr_b_inv c a2 (ev_at k2) Hw2)
    as [[Habs _]|(k2' & s2 & m2 & Heq & Hs2 & Hm2 & _)]; [done|].
  assert (k2' = k2) as -> by (by simplify_eq).
  pose proof (lookup_lt_Some _ _ _ Hs2) as Hk2.
  rewrite (ets_wr (cand_exec c) a2 _ Hw2) (cand_ev_ts c k2 ltac:(lia)).
  destruct e1 as [|k1].
  - rewrite /ets /=. destruct (writesb (cand_exec c) a1 ev_init); simpl; lia.
  - specialize (Hlt k1 eq_refl).
    destruct (wr_b_dec (cand_exec c) a1 (ev_at k1)) as [Hw1|Hn1].
    + rewrite (ets_wr (cand_exec c) a1 _ Hw1).
      destruct (cand_wr_b_inv c a1 (ev_at k1) Hw1)
        as [[Habs _]|(k1' & s1 & m1 & Heq1 & Hs1 & Hm1 & _)]; [done|].
      assert (k1' = k1) as -> by (by simplify_eq).
      pose proof (cand_ts_mono c k1 k2 s1 m1 Hs1 Hm1 Hlt ltac:(lia)) as H.
      rewrite (cand_ev_ts c k2 ltac:(lia)) in H. lia.
    + rewrite /ets (writesb_false _ _ _ Hn1).
      destruct (cd_tr c !! k1) as [s1|] eqn:Hs1; last first.
      { rewrite cand_ex_tr Hs1 /=. lia. }
      rewrite cand_ex_tr Hs1.
      destruct (lb_rd_ts (es_lb s1) a1) as [t|] eqn:Ht; [|simpl; lia].
      simpl.
      destruct (cand_lb_rd_ts_reads c k1 s1 a1 t Hsh Hs1 Ht) as [v Hr].
      pose proof (cand_read_ts_le c Hval k1 a1 t v Hr) as Hle.
      pose proof (cd_log_len_le c k1 k2 ltac:(lia)). lia.
Qed.

(** An [fr] edge's source sits strictly below its target, EVEN WHEN THE
    SOURCE IS A FUSED RMW that writes the byte — that case is exactly
    [ax_atomicity]. *)
Lemma fr_ets_lt c a x y :
  cand_shape c → cand_values c → ax_atomicity (cand_exec c) →
  fr_b (cand_exec c) a x y →
  (ets (cand_exec c) a x < ets (cand_exec c) a y)%nat.
Proof.
  intros Hsh Hval Hatom [(w0 & Hrf0 & Hco) Hne].
  pose proof Hco as (Hw0 & Hwy & Hlt).
  pose proof Hrf0 as (_ & k & t0 & v0 & Hkeq & Hr & Hts0).
  rewrite (ets_wr (cand_exec c) a y Hwy).
  destruct (wr_b_dec (cand_exec c) a x) as [Hwx|Hnx]; last first.
  { rewrite Hkeq (ets_rd (cand_exec c) a k t0 v0 ltac:(rewrite -Hkeq //) Hr).
    lia. }
  rewrite (ets_wr (cand_exec c) a x Hwx).
  assert (HW : is_W (cand_exec c) (ev_at k)) by (rewrite -Hkeq; exact (proj1 Hwx)).
  rewrite Hkeq in Hrf0. rewrite Hkeq.
  pose proof (Hatom k a w0 y HW Hrf0 Hwy Hlt) as Hnl.
  destruct (decide (ev_ts (cand_exec c) (ev_at k) = ev_ts (cand_exec c) y))
    as [Heq|Hne']; [|lia].
  exfalso. apply Hne. rewrite Hkeq.
  exact (cand_ts_inj c (a, ev_at k) (a, y) ltac:(rewrite /=; rewrite -Hkeq //) Hwy Heq).
Qed.

Lemma coh_rel_acyc_ts c a :
  cand_shape c → cand_values c → ax_atomicity (cand_exec c) →
  (∀ e1 e2, po_loc_b (cand_exec c) a e1 e2 →
     (ets (cand_exec c) a e1 ≤ ets (cand_exec c) a e2)%nat) →
  ∀ e, ¬ tc (coh_rel (cand_exec c) a) e e.
Proof.
  intros Hsh Hval Hatom Hnpl.
  apply (tc_lexlt _ (λ e, (ets (cand_exec c) a e, ev_ix e))).
  intros x y [Hpl|[Hrf|[Hco|Hfr]]].
  - pose proof (Hnpl x y Hpl) as Hle.
    pose proof (po_ix (cand_exec c) x y (proj1 Hpl)).
    rewrite /lexlt /=.
    destruct (decide (ets (cand_exec c) a x = ets (cand_exec c) a y));
      [right; split; [done|lia]|left; lia].
  - pose proof Hrf as (Hw & k & t & v & Hkeq & Hr & Hts).
    destruct (wr_b_dec (cand_exec c) a y) as [Hwy|Hny].
    + left. rewrite /=. rewrite Hkeq. rewrite Hkeq in Hwy.
      eapply (ets_lt_wr c a x a k Hsh Hval); [|exact Hwy].
      intros k1 ->.
      pose proof (cand_rf_ix c a (ev_at k1) k Hval ltac:(rewrite -Hkeq //)).
      simpl in *. lia.
    + rewrite /lexlt /= (ets_wr (cand_exec c) a x Hw) Hts Hkeq
              (ets_rd (cand_exec c) a k t v ltac:(rewrite -Hkeq //) Hr).
      right. split; [done|].
      apply (cand_rf_ix c a x k Hval). by rewrite -Hkeq.
  - destruct Hco as (Hw1 & Hw2 & Hlt).
    rewrite (ets_wr (cand_exec c) a x Hw1) (ets_wr (cand_exec c) a y Hw2).
    by left.
  - left. exact (fr_ets_lt c a x y Hsh Hval Hatom Hfr).
Qed.

Lemma ob_op_acyc_w c :
  cand_shape c → cand_values c → ax_atomicity (cand_exec c) →
  (∀ o1 o2, ppo_op (cand_exec c) o1 o2 →
     po (cand_exec c) o1.2 o2.2 ∧ wr_b (cand_exec c) o2.1 o2.2) →
  ∀ o, ¬ tc (ob_op (cand_exec c)) o o.
Proof.
  intros Hsh Hval Hatom Hppo.
  apply (tc_kless _ (λ o, (ets (cand_exec c) o.1 o.2,
                           ophase (cand_exec c) o.1 o.2, ev_ix o.2, o.1))).
  intros [a1 e1] [a2 e2] [Hp|[[Ha Hrf]|[[Ha Hco]|[Ha Hfr]]]].
  - destruct (Hppo _ _ Hp) as [Hpo Hw2]. simpl in *.
    destruct Hpo as (k1 & k2 & s1 & s2 & -> & -> & Hlt & _).
    left. simpl.
    apply (ets_lt_wr c a1 (ev_at k1) a2 k2 Hsh Hval); [|exact Hw2].
    intros k' Heq. by simplify_eq.
  - simpl in Ha; subst a2. simpl in Hrf.
    pose proof Hrf as (Hw & k & t & v & Hkeq & Hr & Hts).
    destruct (wr_b_dec (cand_exec c) a1 e2) as [Hwy|Hny].
    + left. simpl. rewrite Hkeq. rewrite Hkeq in Hwy.
      apply (ets_lt_wr c a1 e1 a1 k Hsh Hval); [|exact Hwy].
      intros k1 ->.
      pose proof (cand_rf_ix c a1 (ev_at k1) k Hval ltac:(rewrite -Hkeq //)).
      simpl in *. lia.
    + rewrite /kless /= (ets_wr (cand_exec c) a1 e1 Hw)
              (ophase_wr (cand_exec c) a1 e1 Hw)
              (ophase_nwr (cand_exec c) a1 e2 Hny) Hts Hkeq
              (ets_rd (cand_exec c) a1 k t v ltac:(rewrite -Hkeq //) Hr).
      right. split; [done|]. left. lia.
  - simpl in Ha; subst a2. simpl in Hco. destruct Hco as (Hw1 & Hw2 & Hlt).
    rewrite /kless /= (ets_wr (cand_exec c) a1 e1 Hw1)
            (ets_wr (cand_exec c) a1 e2 Hw2).
    by left.
  - simpl in Ha; subst a2. simpl in Hfr.
    left. simpl. exact (fr_ets_lt c a1 e1 e2 Hsh Hval Hatom Hfr).
Qed.

(* ================================================================== *)
(** * 4. Reading a value back to its writer *)

(** The single-byte read of a candidate step, as a [reads_at] and as a log
    equation. *)
Lemma cand_reads_at1 c k s a t v :
  cd_tr c !! k = Some s → lb_rd (es_lb s) = Some (a, [t], [v]) →
  reads_at (cand_exec c) k a t v.
Proof.
  intros Hs Hrd. exists s, a, [t], [v], 0%nat.
  rewrite cand_ex_tr. split_and!; [done|done|done|done|rewrite /acc_addr; lia].
Qed.

Lemma cand_read_log c k s a t v :
  cand_values c → cd_tr c !! k = Some s → lb_rd (es_lb s) = Some (a, [t], [v]) →
  log_byte (cd_img c) (cd_log c k) t a = Some v.
Proof.
  intros Hval Hs Hrd.
  pose proof (Hval k s a [t] [v] Hs Hrd 0%nat t v eq_refl eq_refl) as H.
  by rewrite /acc_addr Z.add_0_r in H.
Qed.

(** THE DESCENT STEP of every negative verdict: a non-initial value read at
    byte [a] came from a WRITE STEP of the candidate, strictly earlier, whose
    message carries that value at that byte and whose event timestamp is the
    one that was read. *)
Lemma cand_read_writer c k t a v :
  (k ≤ length (cd_tr c))%nat → t ≠ 0%nat →
  log_byte (cd_img c) (cd_log c k) t a = Some v →
  ∃ k' s m, (k' < k)%nat ∧ cd_tr c !! k' = Some s ∧ es_wmsg s = Some m ∧
            msg_byte m a = Some v ∧ ev_ts (cand_exec c) (ev_at k') = t.
Proof.
  intros Hk Ht Hlb.
  pose proof (log_byte_bounded (cd_img c) (cd_log c k) t a
                (mk_is_Some _ _ Hlb)) as Hb.
  destruct (cand_ts_writer c k t Hk ltac:(lia) Hb)
    as (k' & s & m & Hlt & Hs & Hm & Hts).
  exists k', s, m. split_and!; [done|done|done| |done].
  rewrite -(cand_log_byte_wr c k' s m k a Hs Hm ltac:(lia)) Hts. exact Hlb.
Qed.

(* ================================================================== *)
(** * 5. POSITIVE verdicts

    A positive verdict exhibits a CONCRETE candidate — image [img0], a
    four-or-five-step interleaved trace — proves it [srvwmo_consistent] by
    DISCHARGING THE AXIOMS DIRECTLY (not by running the machine: the point
    is a verdict against the definition; §2's [srvwmo_run] turns it into a
    machine run as a corollary), and reads the outcome off the trace.

    The discharge is factored through [cand_plain_ok]: for a candidate with
    no [sr]-covering fence, no acquire-to-po-later edge, no release write
    and no same-byte program order, the whole of [cand_axiomatic_ok]
    reduces to [ax_atomicity] — five conjuncts are free ([WeakAxiomatic3]
    §12), [ax_ord]/[ax_rel_ord] are vacuous, and the two acyclicity
    conjuncts close by §3's lemmas with vacuous side conditions.  All four
    suite candidates fit: [acq_po] is refuted by LABELS for the three
    fence-free/relaxed shapes and by AGENT GEOMETRY for the AMO, whose
    acquire is its hart's only step. *)

(** *** The vacuity kit *)

Lemma cand_no_fence_ord c :
  (∀ k s, cd_tr c !! k = Some s → ∀ pr pw sw, es_lb s ≠ LFence pr pw true sw) →
  ∀ k1 k2 pr pw sw, ¬ fence_between (cand_exec c) k1 k2 pr pw true sw.
Proof.
  intros Hnf k1 k2 pr pw sw
    (kf & sf & s1 & s2 & _ & _ & _ & Hsf & _ & _ & _ & Hlf).
  rewrite cand_ex_tr in Hsf. exact (Hnf kf sf Hsf pr pw sw Hlf).
Qed.

Lemma cand_no_aq_acq c :
  (∀ k s, cd_tr c !! k = Some s →
     lb_is_r (es_lb s) = true → lb_aq (es_lb s) = false) →
  ∀ e1 e2, ¬ acq_po (cand_exec c) e1 e2.
Proof.
  intros Hnaq e1 e2 (k1 & k2 & s1 & s2 & -> & -> & Hlt & Hs1 & Hs2 & Hag & Hr & Haq).
  rewrite cand_ex_tr in Hs1. rewrite (Hnaq k1 s1 Hs1 Hr) in Haq. done.
Qed.

(** The AMO's discharger: an acquire whose hart takes no other step is in no
    [acq_po] edge — the edge needs a po-later step of the SAME agent. *)
Lemma cand_no_pair_acq c :
  (∀ k1 k2 s1 s2, cd_tr c !! k1 = Some s1 → cd_tr c !! k2 = Some s2 →
     (k1 < k2)%nat → es_ag s1 ≠ es_ag s2) →
  ∀ e1 e2, ¬ acq_po (cand_exec c) e1 e2.
Proof.
  intros Hnp e1 e2 (k1 & k2 & s1 & s2 & -> & -> & Hlt & Hs1 & Hs2 & Hag & _).
  rewrite cand_ex_tr in Hs1. rewrite cand_ex_tr in Hs2.
  exact (Hnp k1 k2 s1 s2 Hs1 Hs2 Hlt Hag).
Qed.

Lemma cand_no_ord c :
  (∀ k s, cd_tr c !! k = Some s → ∀ pr pw sw, es_lb s ≠ LFence pr pw true sw) →
  (∀ e1 e2, ¬ acq_po (cand_exec c) e1 e2) →
  ∀ e1 e2, ¬ ord_pw (cand_exec c) e1 e2 ∧ ¬ ord_pr (cand_exec c) e1 e2.
Proof.
  intros Hnf Hnacq e1 e2. split.
  - intros (k1 & k2 & pr & sw & _ & _ & Hfb).
    by eapply (cand_no_fence_ord c Hnf).
  - intros [(k1 & k2 & pw & sw & _ & _ & Hfb)|Hacq];
      [by eapply (cand_no_fence_ord c Hnf)|by eapply Hnacq].
Qed.

Lemma cand_no_rl_rel_acq c :
  (∀ k s, cd_tr c !! k = Some s → lb_rl (es_lb s) = false) →
  ∀ e1 e2, ¬ rel_acq_po (cand_exec c) e1 e2.
Proof.
  intros Hnrl e1 e2
    (k1 & k2 & s1 & s2 & -> & -> & Hlt & Hs1 & Hs2 & Hag & Hw & Hrl & _).
  rewrite cand_ex_tr in Hs1. rewrite (Hnrl k1 s1 Hs1) in Hrl. done.
Qed.

Lemma cand_no_rl_rel_ord c :
  (∀ k s, cd_tr c !! k = Some s → lb_rl (es_lb s) = false) →
  ∀ e1 e2, ¬ rel_ord (cand_exec c) e1 e2.
Proof.
  intros Hnrl e1 e2 [Hr|(em & Hr & _ & _)]; by eapply (cand_no_rl_rel_acq c Hnrl).
Qed.

Lemma lb_rd_is_r l base ts vs : lb_rd l = Some (base, ts, vs) → lb_is_r l = true.
Proof. by destruct l. Qed.

(** [ax_atomicity] for free when no step both reads and writes. *)
Lemma cand_rw_disjoint_atomicity c :
  (∀ k s, cd_tr c !! k = Some s →
     lb_is_w (es_lb s) = false ∨ lb_is_r (es_lb s) = false) →
  ax_atomicity (cand_exec c).
Proof.
  intros Hrw kr a w0 w HW Hrf0 _ _.
  destruct Hrf0 as (_ & k & t & v & Hkeq & Hr & _).
  assert (k = kr) as -> by (by simplify_eq).
  destruct Hr as (s & base & ts & vs & j & Hs & Hrd & _).
  rewrite cand_ex_tr in Hs.
  destruct HW as (s' & Hs' & Hw'). rewrite cand_ex_tr in Hs'.
  assert (s' = s) as -> by (rewrite Hs in Hs'; by simplify_eq).
  destruct (Hrw kr s Hs) as [Hnw|Hnr].
  - by rewrite Hw' in Hnw.
  - by rewrite (lb_rd_is_r _ _ _ _ Hrd) in Hnr.
Qed.

(** Single-byte access inversion: which byte a candidate event touches. *)
Lemma cand_wr_b_at c a k :
  wr_b (cand_exec c) a (ev_at k) →
  ∃ s m, cd_tr c !! k = Some s ∧ es_wmsg s = Some m ∧ is_Some (msg_byte m a).
Proof.
  intros Hw. destruct (cand_wr_b_inv c a (ev_at k) Hw)
    as [[? _]|(k' & s & m & Heq & Hs & Hm & Hb)]; [done|].
  assert (k' = k) as -> by (by simplify_eq). by exists s, m.
Qed.

Lemma cand_rd_b_at c a k :
  rd_b (cand_exec c) a (ev_at k) →
  ∃ s base ts vs j, cd_tr c !! k = Some s ∧
    lb_rd (es_lb s) = Some (base, ts, vs) ∧ (j < length ts)%nat ∧
    acc_addr base j = a.
Proof.
  intros (k' & t & v & Heq & (s & base & ts & vs & j & Hs & Hrd & Hj & Hv & Ha)).
  assert (k' = k) as -> by (by simplify_eq).
  rewrite cand_ex_tr in Hs.
  exists s, base, ts, vs, j. split_and!; [done|done|by eapply lookup_lt_Some|done].
Qed.

(** THE KIT: everything but [ax_atomicity] and the four vacuity facts is
    free.  [ppo_op] collapses to its rule-14 arm ([po] into a write), which
    is exactly what §3's [ob_op_acyc_w] admits. *)
Lemma cand_plain_ok c :
  cand_shape c → cand_values c →
  (∀ k s, cd_tr c !! k = Some s → ∀ pr pw sw, es_lb s ≠ LFence pr pw true sw) →
  (∀ e1 e2, ¬ acq_po (cand_exec c) e1 e2) →
  (∀ k s, cd_tr c !! k = Some s → lb_rl (es_lb s) = false) →
  ax_atomicity (cand_exec c) →
  (∀ a e1 e2, ¬ po_loc_b (cand_exec c) a e1 e2) →
  srvwmo_consistent c.
Proof.
  intros Hsh Hval Hnf Hnacq Hnrl Hatom Hnpl.
  assert (Hnppo : ∀ o1 o2, ppo_op (cand_exec c) o1 o2 →
            po (cand_exec c) o1.2 o2.2 ∧ wr_b (cand_exec c) o2.1 o2.2).
  { intros o1 o2 [[Hpo Hw2]|[[Ha Hpl]|[[Hord _]|[(Hord & _ & _)|[Hrel _]]]]].
    - by split.
    - by destruct (Hnpl o1.1 o1.2 o2.2).
    - by destruct (cand_no_ord c Hnf Hnacq o1.2 o2.2) as [H _]; destruct (H Hord).
    - by destruct (cand_no_ord c Hnf Hnacq o1.2 o2.2) as [_ H]; destruct (H Hord).
    - by destruct (cand_no_rl_rel_acq c Hnrl o1.2 o2.2 Hrel). }
  split_and!; [done|done|]. split_and!.
  - split_and!.
    + by apply cand_rf_total.
    + apply cand_rf_functional.
    + by apply cand_rf_value.
    + intros a e. apply (coh_rel_acyc_ts c a Hsh Hval Hatom).
      intros e1 e2 Hpl. by destruct (Hnpl a e1 e2).
    + exact Hatom.
    + intros e1 k2 s2 a w t Hs2 Hcase Hfr.
      destruct (cand_no_ord c Hnf Hnacq e1 (ev_at k2)) as [Hpw Hpr].
      by destruct Hcase as [[Hord _]|[Hord _]].
    + by apply cand_no_thin_air.
    + apply cand_po_ww_gmo.
  - intros e1 k2 s2 a w t Hs2 Hro Hpub Hfr.
    by destruct (cand_no_rl_rel_ord c Hnrl e1 (ev_at k2) Hro).
  - by apply (ob_op_acyc_w c Hsh Hval Hatom Hnppo).
Qed.

(** *** SB: both harts read 0 — ALLOWED (matches RVWMO and the machine).

    Interleaving: both stores first, both loads read the era-initial image
    (timestamp 0) — each hart's own load floor covers only its own byte. *)

Definition sb_P : prog := [sb_prog0; sb_prog1].
Definition sb_tr : list estep :=
  [EStep 0 (LStore false ax [b1] WCplain);
   EStep 1 (LStore false ay [b1] WCplain);
   EStep 0 (LLoad false ay [0%nat] [b0]);
   EStep 1 (LLoad false ax [0%nat] [b0])].
Definition sb_cd : cand := Cand img0 sb_tr.

Lemma sb_tr_inv k s :
  cd_tr sb_cd !! k = Some s →
  (k = 0%nat ∧ s = EStep 0 (LStore false ax [b1] WCplain)) ∨
  (k = 1%nat ∧ s = EStep 1 (LStore false ay [b1] WCplain)) ∨
  (k = 2%nat ∧ s = EStep 0 (LLoad false ay [0%nat] [b0])) ∨
  (k = 3%nat ∧ s = EStep 1 (LLoad false ax [0%nat] [b0])).
Proof. intros Hs. destruct k as [|[|[|[|k]]]]; simplify_eq/=; auto. Qed.

Lemma sb_shape : cand_shape sb_cd.
Proof. intros k s Hs. by destruct k as [|[|[|[|k]]]]; simplify_eq/=. Qed.

Lemma sb_values : cand_values sb_cd.
Proof.
  intros k s base ts vs Hs Hrd j t v Hj Hv.
  destruct k as [|[|[|[|k]]]]; simplify_eq/=;
    destruct j as [|j]; simplify_eq/=; by vm_compute.
Qed.

Lemma sb_no_poloc a e1 e2 : ¬ po_loc_b (cand_exec sb_cd) a e1 e2.
Proof.
  intros ((k1 & k2 & s1 & s2 & -> & -> & Hlt & Hs1 & Hs2 & Hag) & Hacc1 & Hacc2).
  rewrite cand_ex_tr in Hs1. rewrite cand_ex_tr in Hs2.
  (* the byte an SB event accesses: ax at steps 0/3, ay at steps 1/2 *)
  assert (Hbyte : ∀ k a', acc_b (cand_exec sb_cd) a' (ev_at k) →
            ((k = 0%nat ∨ k = 3%nat) ∧ a' = ax) ∨
            ((k = 1%nat ∨ k = 2%nat) ∧ a' = ay)).
  { intros k a' [Hw|Hr].
    - destruct (cand_wr_b_at _ _ _ Hw) as (s' & m & Hs' & Hm & Hb).
      destruct (sb_tr_inv k s' Hs') as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]];
        rewrite /es_wmsg /= in Hm; simplify_eq;
        pose proof (msg_byte_single _ _ _ _ _ Hb).
      + left. split; [by left|done].
      + right. split; [by left|done].
    - destruct (cand_rd_b_at _ _ _ Hr)
        as (s' & base & ts & vs & j & Hs' & Hrd & Hj & Ha).
      destruct (sb_tr_inv k s' Hs') as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]];
        rewrite /= in Hrd; simplify_eq;
        destruct j as [|j]; simpl in Hj; try lia.
      + right. split; [by right|rewrite /acc_addr /=; lia].
      + left. split; [by right|rewrite /acc_addr /=; lia]. }
  destruct (Hbyte k1 a Hacc1) as [[Hk1 Ha1]|[Hk1 Ha1]];
    destruct (Hbyte k2 a Hacc2) as [[Hk2 Ha2]|[Hk2 Ha2]]; subst; try lia;
    destruct Hk1 as [->| ->]; destruct Hk2 as [->| ->]; try lia;
    simplify_eq/=; lia.
Qed.

Lemma sb_ok : srvwmo_consistent sb_cd.
Proof.
  apply cand_plain_ok.
  - exact sb_shape.
  - exact sb_values.
  - intros k s Hs pr pw sw.
    by destruct (sb_tr_inv k s Hs) as [[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]].
  - apply cand_no_aq_acq. intros k s Hs Hr.
    by destruct (sb_tr_inv k s Hs) as [[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]].
  - intros k s Hs.
    by destruct (sb_tr_inv k s Hs) as [[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]].
  - apply cand_rw_disjoint_atomicity. intros k s Hs.
    destruct (sb_tr_inv k s Hs) as [[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]];
      [by right|by right|by left|by left].
  - exact sb_no_poloc.
Qed.

Lemma sb_conf : conforms sb_P sb_cd.
Proof.
  intros k s Hs.
  destruct (sb_tr_inv k s Hs) as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]].
  - by exists sb_prog0, (IStore ax b1).
  - by exists sb_prog1, (IStore ay b1).
  - exists sb_prog0, (ILoad rg1 ay false). split_and!; [done|done|].
    by exists 0%nat, b0.
  - exists sb_prog1, (ILoad rg2 ax false). split_and!; [done|done|].
    by exists 0%nat, b0.
Qed.

Definition sb_out00 (c : cand) : Prop := outc c 0 1 ay b0 ∧ outc c 1 1 ax b0.

(** THE VERDICT: the definition admits the 0/0 outcome (and T1 then realizes
    it on the machine — [srvwmo_run] applies to this witness). *)
Theorem sb_00_allowed :
  ∃ c, cd_img c = img0 ∧ conforms sb_P c ∧ sb_out00 c ∧ srvwmo_consistent c.
Proof.
  exists sb_cd. split_and!; [done|exact sb_conf| |exact sb_ok].
  split.
  - exists 2%nat, (EStep 0 (LLoad false ay [0%nat] [b0])), 0%nat.
    by split_and!.
  - exists 3%nat, (EStep 1 (LLoad false ax [0%nat] [b0])), 0%nat.
    by split_and!.
Qed.

(* ================================================================== *)
(** *** MP with no fences — the weak outcome is ALLOWED

    Hart 0 stores [ax] then [ay]; hart 1 loads [ay] (sees the flag, [b1])
    then loads [ax] (sees the STALE data, [b0]).  Nothing orders hart 1's two
    relaxed loads, so the second may take the era-initial timestamp 0 even
    though the first took timestamp 2.  RVWMO allows this (no fence on
    either side) and so does the operational machine; the model agrees. *)

Definition mpn_P : prog := [mp_w_nofence; mp_r_nofence].
Definition mpn_tr : list estep :=
  [EStep 0 (LStore false ax [b1] WCplain);
   EStep 0 (LStore false ay [b1] WCplain);
   EStep 1 (LLoad false ay [2%nat] [b1]);
   EStep 1 (LLoad false ax [0%nat] [b0])].
Definition mpn_cd : cand := Cand img0 mpn_tr.

Lemma mpn_tr_inv k s :
  cd_tr mpn_cd !! k = Some s →
  (k = 0%nat ∧ s = EStep 0 (LStore false ax [b1] WCplain)) ∨
  (k = 1%nat ∧ s = EStep 0 (LStore false ay [b1] WCplain)) ∨
  (k = 2%nat ∧ s = EStep 1 (LLoad false ay [2%nat] [b1])) ∨
  (k = 3%nat ∧ s = EStep 1 (LLoad false ax [0%nat] [b0])).
Proof. intros Hs. destruct k as [|[|[|[|k]]]]; simplify_eq/=; auto. Qed.

Lemma mpn_shape : cand_shape mpn_cd.
Proof. intros k s Hs. by destruct k as [|[|[|[|k]]]]; simplify_eq/=. Qed.

(** The flag read takes t = 2 (the [ay] store's own message); the data read
    takes t = 0, i.e. the era-initial image. *)
Lemma mpn_values : cand_values mpn_cd.
Proof.
  intros k s base ts vs Hs Hrd j t v Hj Hv.
  destruct k as [|[|[|[|k]]]]; simplify_eq/=;
    destruct j as [|j]; simplify_eq/=; by vm_compute.
Qed.

Lemma mpn_no_poloc a e1 e2 : ¬ po_loc_b (cand_exec mpn_cd) a e1 e2.
Proof.
  intros ((k1 & k2 & s1 & s2 & -> & -> & Hlt & Hs1 & Hs2 & Hag) & Hacc1 & Hacc2).
  rewrite cand_ex_tr in Hs1. rewrite cand_ex_tr in Hs2.
  (* the byte an MP event accesses: ax at steps 0/3, ay at steps 1/2 — so the
     two same-agent po pairs (0,1) and (2,3) are at DIFFERENT bytes, and the
     two same-byte pairs (0,3) and (1,2) are on different agents *)
  assert (Hbyte : ∀ k a', acc_b (cand_exec mpn_cd) a' (ev_at k) →
            ((k = 0%nat ∨ k = 3%nat) ∧ a' = ax) ∨
            ((k = 1%nat ∨ k = 2%nat) ∧ a' = ay)).
  { intros k a' [Hw|Hr].
    - destruct (cand_wr_b_at _ _ _ Hw) as (s' & m & Hs' & Hm & Hb).
      destruct (mpn_tr_inv k s' Hs') as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]];
        rewrite /es_wmsg /= in Hm; simplify_eq;
        pose proof (msg_byte_single _ _ _ _ _ Hb).
      + left. split; [by left|done].
      + right. split; [by left|done].
    - destruct (cand_rd_b_at _ _ _ Hr)
        as (s' & base & ts & vs & j & Hs' & Hrd & Hj & Ha).
      destruct (mpn_tr_inv k s' Hs') as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]];
        rewrite /= in Hrd; simplify_eq;
        destruct j as [|j]; simpl in Hj; try lia.
      + right. split; [by right|rewrite /acc_addr /=; lia].
      + left. split; [by right|rewrite /acc_addr /=; lia]. }
  destruct (Hbyte k1 a Hacc1) as [[Hk1 Ha1]|[Hk1 Ha1]];
    destruct (Hbyte k2 a Hacc2) as [[Hk2 Ha2]|[Hk2 Ha2]]; subst; try lia;
    destruct Hk1 as [->| ->]; destruct Hk2 as [->| ->]; try lia;
    simplify_eq/=; lia.
Qed.

Lemma mpn_ok : srvwmo_consistent mpn_cd.
Proof.
  apply cand_plain_ok.
  - exact mpn_shape.
  - exact mpn_values.
  - intros k s Hs pr pw sw.
    by destruct (mpn_tr_inv k s Hs) as [[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]].
  - apply cand_no_aq_acq. intros k s Hs Hr.
    by destruct (mpn_tr_inv k s Hs) as [[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]].
  - intros k s Hs.
    by destruct (mpn_tr_inv k s Hs) as [[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]].
  - apply cand_rw_disjoint_atomicity. intros k s Hs.
    destruct (mpn_tr_inv k s Hs) as [[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]];
      [by right|by right|by left|by left].
  - exact mpn_no_poloc.
Qed.

Lemma mpn_conf : conforms mpn_P mpn_cd.
Proof.
  intros k s Hs.
  destruct (mpn_tr_inv k s Hs) as [[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]].
  - by exists mp_w_nofence, (IStore ax b1).
  - by exists mp_w_nofence, (IStore ay b1).
  - exists mp_r_nofence, (ILoad rg1 ay false). split_and!; [done|done|].
    by exists 2%nat, b1.
  - exists mp_r_nofence, (ILoad rg2 ax false). split_and!; [done|done|].
    by exists 0%nat, b0.
Qed.

Definition mpn_out (c : cand) : Prop := outc c 1 0 ay b1 ∧ outc c 1 1 ax b0.

(** THE VERDICT: flag seen, data stale — sRVWMO-consistent. *)
Theorem mpn_weak_allowed :
  ∃ c, cd_img c = img0 ∧ conforms mpn_P c ∧ mpn_out c ∧ srvwmo_consistent c.
Proof.
  exists mpn_cd. split_and!; [done|exact mpn_conf| |exact mpn_ok].
  split.
  - exists 2%nat, (EStep 1 (LLoad false ay [2%nat] [b1])), 2%nat.
    by split_and!.
  - exists 3%nat, (EStep 1 (LLoad false ax [0%nat] [b0])), 0%nat.
    by split_and!.
Qed.

(* ================================================================== *)
(** *** MP with ONLY the writer fence (fence rw,w) — still ALLOWED

    Hart 0 now separates its two stores with [FENCE_RW_W], so the flag store
    cannot be reordered before the data store.  That fixes nothing on the
    READER side: hart 1's two loads are plain and unordered, so the data load
    may still take timestamp 0 after the flag load took timestamp 2.  RVWMO
    requires fences on BOTH sides for MP; the model reproduces that, and the
    operational machine allows the same run. *)

Definition mpw_P : prog := [mp_w_fenced; mp_r_nofence].
Definition mpw_tr : list estep :=
  [EStep 0 (LStore false ax [b1] WCplain);
   EStep 0 (LFence true true false true);
   EStep 0 (LStore false ay [b1] WCplain);
   EStep 1 (LLoad false ay [2%nat] [b1]);
   EStep 1 (LLoad false ax [0%nat] [b0])].
Definition mpw_cd : cand := Cand img0 mpw_tr.

Lemma mpw_tr_inv k s :
  cd_tr mpw_cd !! k = Some s →
  (k = 0%nat ∧ s = EStep 0 (LStore false ax [b1] WCplain)) ∨
  (k = 1%nat ∧ s = EStep 0 (LFence true true false true)) ∨
  (k = 2%nat ∧ s = EStep 0 (LStore false ay [b1] WCplain)) ∨
  (k = 3%nat ∧ s = EStep 1 (LLoad false ay [2%nat] [b1])) ∨
  (k = 4%nat ∧ s = EStep 1 (LLoad false ax [0%nat] [b0])).
Proof. intros Hs. destruct k as [|[|[|[|[|k]]]]]; simplify_eq/=; auto 10. Qed.

Lemma mpw_shape : cand_shape mpw_cd.
Proof. intros k s Hs. by destruct k as [|[|[|[|[|k]]]]]; simplify_eq/=. Qed.

(** The fence appends no message, so the [ay] store — agent-0 position 2 —
    still has timestamp 2, which is what the flag load reads. *)
Lemma mpw_values : cand_values mpw_cd.
Proof.
  intros k s base ts vs Hs Hrd j t v Hj Hv.
  destruct k as [|[|[|[|[|k]]]]]; simplify_eq/=;
    destruct j as [|j]; simplify_eq/=; by vm_compute.
Qed.

Lemma mpw_no_poloc a e1 e2 : ¬ po_loc_b (cand_exec mpw_cd) a e1 e2.
Proof.
  intros ((k1 & k2 & s1 & s2 & -> & -> & Hlt & Hs1 & Hs2 & Hag) & Hacc1 & Hacc2).
  rewrite cand_ex_tr in Hs1. rewrite cand_ex_tr in Hs2.
  (* ax at steps 0/4, ay at steps 2/3; the fence at step 1 accesses no byte
     (its [es_wmsg] and its [lb_rd] are both [None]) *)
  assert (Hbyte : ∀ k a', acc_b (cand_exec mpw_cd) a' (ev_at k) →
            ((k = 0%nat ∨ k = 4%nat) ∧ a' = ax) ∨
            ((k = 2%nat ∨ k = 3%nat) ∧ a' = ay)).
  { intros k a' [Hw|Hr].
    - destruct (cand_wr_b_at _ _ _ Hw) as (s' & m & Hs' & Hm & Hb).
      destruct (mpw_tr_inv k s' Hs')
        as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]];
        rewrite /es_wmsg /= in Hm; simplify_eq;
        pose proof (msg_byte_single _ _ _ _ _ Hb).
      + left. split; [by left|done].
      + right. split; [by left|done].
    - destruct (cand_rd_b_at _ _ _ Hr)
        as (s' & base & ts & vs & j & Hs' & Hrd & Hj & Ha).
      destruct (mpw_tr_inv k s' Hs')
        as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]];
        rewrite /= in Hrd; simplify_eq;
        destruct j as [|j]; simpl in Hj; try lia.
      + right. split; [by right|rewrite /acc_addr /=; lia].
      + left. split; [by right|rewrite /acc_addr /=; lia]. }
  destruct (Hbyte k1 a Hacc1) as [[Hk1 Ha1]|[Hk1 Ha1]];
    destruct (Hbyte k2 a Hacc2) as [[Hk2 Ha2]|[Hk2 Ha2]]; subst; try lia;
    destruct Hk1 as [->| ->]; destruct Hk2 as [->| ->]; try lia;
    simplify_eq/=; lia.
Qed.

Lemma mpw_ok : srvwmo_consistent mpw_cd.
Proof.
  apply cand_plain_ok.
  - exact mpw_shape.
  - exact mpw_values.
  - (* the writer fence is [rw,w]: its successor-READ bit is false, so it is
       not an [sr]-covering fence and [ord] stays vacuous *)
    intros k s Hs pr pw sw.
    by destruct (mpw_tr_inv k s Hs)
      as [[_ ->]|[[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]]].
  - apply cand_no_aq_acq. intros k s Hs Hr.
    by destruct (mpw_tr_inv k s Hs)
      as [[_ ->]|[[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]]].
  - intros k s Hs.
    by destruct (mpw_tr_inv k s Hs)
      as [[_ ->]|[[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]]].
  - apply cand_rw_disjoint_atomicity. intros k s Hs.
    destruct (mpw_tr_inv k s Hs)
      as [[_ ->]|[[_ ->]|[[_ ->]|[[_ ->]|[_ ->]]]]];
      [by right|by right|by right|by left|by left].
  - exact mpw_no_poloc.
Qed.

Lemma mpw_conf : conforms mpw_P mpw_cd.
Proof.
  intros k s Hs.
  destruct (mpw_tr_inv k s Hs)
    as [[-> ->]|[[-> ->]|[[-> ->]|[[-> ->]|[-> ->]]]]].
  - by exists mp_w_fenced, (IStore ax b1).
  - by exists mp_w_fenced, FENCE_RW_W.
  - by exists mp_w_fenced, (IStore ay b1).
  - exists mp_r_nofence, (ILoad rg1 ay false). split_and!; [done|done|].
    by exists 2%nat, b1.
  - exists mp_r_nofence, (ILoad rg2 ax false). split_and!; [done|done|].
    by exists 0%nat, b0.
Qed.

Definition mpw_out (c : cand) : Prop := outc c 1 0 ay b1 ∧ outc c 1 1 ax b0.

(** THE VERDICT: the release-side fence alone does NOT forbid the MP
    outcome. *)
Theorem mpw_weak_allowed :
  ∃ c, cd_img c = img0 ∧ conforms mpw_P c ∧ mpw_out c ∧ srvwmo_consistent c.
Proof.
  exists mpw_cd. split_and!; [done|exact mpw_conf| |exact mpw_ok].
  split.
  - exists 3%nat, (EStep 1 (LLoad false ay [2%nat] [b1])), 2%nat.
    by split_and!.
  - exists 4%nat, (EStep 1 (LLoad false ax [0%nat] [b0])), 0%nat.
    by split_and!.
Qed.

(* ================================================================== *)
(** *** AMO — amoswap.aq reads the globally-latest value

    Hart 0 stores [b1] to [ax]; hart 1 then runs [amoswap.aq] on [ax],
    reading [b1] (timestamp 1, the store's own message) and writing [b2].
    This is the only candidate in the suite whose step both READS and WRITES
    a byte, so [ax_atomicity] is not free here — it is discharged directly
    from the arithmetic of the two timestamps (the read half took t = 1, the
    RMW's own write is t = 2, and no write can sit strictly between).
    Matches RVWMO (an AMO reads the co-latest write) and the machine's
    [IAmoSwapAq] arm. *)

Definition amo_P : prog := [[IStore ax b1]; [IAmoSwapAq rg1 ax b2]].
Definition amo_tr : list estep :=
  [EStep 0 (LStore false ax [b1] WCplain);
   EStep 1 (LRmw true false ax [1%nat] [b1] [b2] WCexcl)].
Definition amo_cd : cand := Cand img0 amo_tr.

Lemma amo_tr_inv k s :
  cd_tr amo_cd !! k = Some s →
  (k = 0%nat ∧ s = EStep 0 (LStore false ax [b1] WCplain)) ∨
  (k = 1%nat ∧ s = EStep 1 (LRmw true false ax [1%nat] [b1] [b2] WCexcl)).
Proof. intros Hs. destruct k as [|[|k]]; simplify_eq/=; auto. Qed.

Lemma amo_shape : cand_shape amo_cd.
Proof.
  intros k s Hs. destruct k as [|[|k]]; simplify_eq/=; [done|by split_and!].
Qed.

Lemma amo_values : cand_values amo_cd.
Proof.
  intros k s base ts vs Hs Hrd j t v Hj Hv.
  destruct k as [|[|k]]; simplify_eq/=;
    destruct j as [|j]; simplify_eq/=; by vm_compute.
Qed.

(** The two steps belong to DIFFERENT agents, so this candidate has no
    program order at all — which kills [po_loc_b] and [acq_po] alike (the
    AMO's [.aq] would otherwise be an [acq_po] source). *)
Lemma amo_no_po e1 e2 : ¬ po (cand_exec amo_cd) e1 e2.
Proof.
  intros (k1 & k2 & s1 & s2 & -> & -> & Hlt & Hs1 & Hs2 & Hag).
  rewrite cand_ex_tr in Hs1. rewrite cand_ex_tr in Hs2.
  destruct (amo_tr_inv k1 s1 Hs1) as [[-> ->]|[-> ->]];
    destruct (amo_tr_inv k2 s2 Hs2) as [[-> ->]|[-> ->]];
    simplify_eq/=; lia.
Qed.

Lemma amo_no_poloc a e1 e2 : ¬ po_loc_b (cand_exec amo_cd) a e1 e2.
Proof. intros [Hpo _]. exact (amo_no_po _ _ Hpo). Qed.

(** THE one non-templated obligation: no write of [ax] falls between the
    RMW's read half (timestamp 1) and its write half (timestamp 2). *)
Lemma amo_atomicity : ax_atomicity (cand_exec amo_cd).
Proof.
  intros kr a w0 w HW Hrf0 Hw Hgt Hlt.
  destruct Hrf0 as (_ & k & t & v & Hkeq & Hr & Hts0).
  assert (k = kr) as -> by (by simplify_eq).
  destruct Hr as (s & base & ts & vs & j & Hs & Hrd & Hj & Hv & Ha).
  rewrite cand_ex_tr in Hs.
  destruct (amo_tr_inv kr s Hs) as [[-> ->]|[-> ->]];
    rewrite /= in Hrd; simplify_eq.
  (* the read half took t = 1; the RMW's own event timestamp computes to 2,
     so no write of [ax] can sit strictly between them *)
  destruct j as [|j]; simplify_eq/=. lia.
Qed.

Lemma amo_ok : srvwmo_consistent amo_cd.
Proof.
  apply cand_plain_ok.
  - exact amo_shape.
  - exact amo_values.
  - intros k s Hs pr pw sw.
    by destruct (amo_tr_inv k s Hs) as [[_ ->]|[_ ->]].
  - apply cand_no_pair_acq. intros k1 k2 s1 s2 Hs1 Hs2 Hlt.
    destruct (amo_tr_inv k1 s1 Hs1) as [[-> ->]|[-> ->]];
      destruct (amo_tr_inv k2 s2 Hs2) as [[-> ->]|[-> ->]];
      simplify_eq/=; lia.
  - intros k s Hs.
    by destruct (amo_tr_inv k s Hs) as [[_ ->]|[_ ->]].
  - exact amo_atomicity.
  - exact amo_no_poloc.
Qed.

Lemma amo_conf : conforms amo_P amo_cd.
Proof.
  intros k s Hs.
  destruct (amo_tr_inv k s Hs) as [[-> ->]|[-> ->]].
  - by exists [IStore ax b1], (IStore ax b1).
  - exists [IAmoSwapAq rg1 ax b2], (IAmoSwapAq rg1 ax b2).
    split_and!; [done|done|]. by exists 1%nat, b1.
Qed.

Definition amo_out (c : cand) : Prop := outc c 1 0 ax b1.

(** THE VERDICT: the acquire AMO reads the store's value — allowed, with the
    fused-RMW arm of the model (and [ax_atomicity]) genuinely exercised. *)
Theorem amo_latest_allowed :
  ∃ c, cd_img c = img0 ∧ conforms amo_P c ∧ amo_out c ∧ srvwmo_consistent c.
Proof.
  exists amo_cd. split_and!; [done|exact amo_conf| |exact amo_ok].
  exists 1%nat, (EStep 1 (LRmw true false ax [1%nat] [b1] [b2] WCexcl)), 1%nat.
  by split_and!.
Qed.
(* ================================================================== *)
(** * 6. NEGATIVE verdicts

    A negative verdict quantifies over EVERY candidate: no conformant
    candidate over [img0] with the outcome is sRVWMO-consistent.  Through
    [srvwmo_of_wf] that immediately covers the machine as well.  The
    engine is §4's descent ([cand_read_writer]): a non-initial value read
    names its writer STEP, conformance names the writer's INSTRUCTION, and
    §1's [ag_pos] arithmetic names the po-earlier steps of the same hart.

    [outc_writer] packages the descent; [outc_initial] is its complement
    (a read of a value NO instruction ever writes must read timestamp 0,
    the era-initial image). *)

Lemma outc_writer c i j a v :
  cand_values c → outc c i j a v → cd_img c a ≠ Some v →
  ∃ k s t k' s' m,
    cd_tr c !! k = Some s ∧ es_ag s = i ∧ ag_pos (cd_tr c) i k = j ∧
    lb_rd (es_lb s) = Some (a, [t], [v]) ∧
    (k' < k)%nat ∧ cd_tr c !! k' = Some s' ∧ es_wmsg s' = Some m ∧
    msg_byte m a = Some v ∧ ev_ts (cand_exec c) (ev_at k') = t.
Proof.
  intros Hval (k & s & t & Hs & Hag & Hpos & Hrd) Hni.
  pose proof (cand_read_log c k s a t v Hval Hs Hrd) as Hlb.
  assert (Ht : t ≠ 0%nat).
  { intros ->. rewrite log_byte_0 in Hlb. done. }
  pose proof (lookup_lt_Some _ _ _ Hs) as Hk.
  destruct (cand_read_writer c k t a v ltac:(lia) Ht Hlb)
    as (k' & s' & m & Hlt & Hs' & Hm & Hb & Hts).
  by exists k, s, t, k', s', m.
Qed.

Lemma outc_initial c i j a v :
  cand_values c → outc c i j a v →
  (∀ k' s' m, cd_tr c !! k' = Some s' → es_wmsg s' = Some m →
     msg_byte m a ≠ Some v) →
  ∃ k s, cd_tr c !! k = Some s ∧ es_ag s = i ∧ ag_pos (cd_tr c) i k = j ∧
         lb_rd (es_lb s) = Some (a, [0%nat], [v]) ∧ cd_img c a = Some v.
Proof.
  intros Hval (k & s & t & Hs & Hag & Hpos & Hrd) Hno.
  pose proof (cand_read_log c k s a t v Hval Hs Hrd) as Hlb.
  pose proof (lookup_lt_Some _ _ _ Hs) as Hk.
  destruct (decide (t = 0%nat)) as [->|Ht].
  - exists k, s. rewrite log_byte_0 in Hlb. by split_and!.
  - exfalso.
    destruct (cand_read_writer c k t a v ltac:(lia) Ht Hlb)
      as (k' & s' & m & _ & Hs' & Hm & Hb & _).
    exact (Hno k' s' m Hs' Hm Hb).
Qed.

(** *** LB — THE HEADLINE: forbidden, and forbidden by the LOAD-VALUE
    axiom alone.

    RVWMO ALLOWS this outcome (a promising machine certifies the stores
    early); sRVWMO forbids it, and the refutation below never consults an
    ordering axiom: [cand_values] — reads take their value from the log
    PREFIX — already makes the four steps' trace positions cyclic.  That
    is the honest mechanized form of "no-thin-air is definitional in the
    candidate presentation" (the [ax_no_thin_air] conjunct is FREE for
    every value-consistent candidate, [WeakAxiomatic3.cand_no_thin_air]);
    it is DIVERGENCE (1) of §9's table. *)

Definition lb_P : prog :=
  [[ILoad rg1 ax false; IStore ay b1]; [ILoad rg2 ay false; IStore ax b1]].
Definition lb_out (c : cand) : Prop := outc c 0 0 ax b1 ∧ outc c 1 0 ay b1.

(** Which steps of an [lb_P]-conformant candidate write, and what. *)
Lemma lb_wmsg_inv c k s m :
  conforms lb_P c → cd_tr c !! k = Some s → es_wmsg s = Some m →
  (es_ag s = 0%nat ∧ ag_pos (cd_tr c) 0%nat k = 1%nat ∧
   m = WMsg ay [b1] (Some 0%nat) WCplain) ∨
  (es_ag s = 1%nat ∧ ag_pos (cd_tr c) 1%nat k = 1%nat ∧
   m = WMsg ax [b1] (Some 1%nat) WCplain).
Proof.
  intros Hconf Hs Hm.
  destruct (Hconf k s Hs) as (p & ins & Hp & Hins & Hil).
  destruct (es_ag s) as [|[|n]] eqn:Hag; simplify_eq/=.
  - destruct (ag_pos (cd_tr c) 0%nat k) as [|[|j]] eqn:Hpos; simplify_eq/=.
    + destruct Hil as (t0 & v0 & Hlbl). rewrite /es_wmsg Hlbl /= in Hm. done.
    + rewrite /instr_lbl in Hil. rewrite /es_wmsg Hil Hag /= in Hm.
      simplify_eq. by left.
  - destruct (ag_pos (cd_tr c) 1%nat k) as [|[|j]] eqn:Hpos; simplify_eq/=.
    + destruct Hil as (t0 & v0 & Hlbl). rewrite /es_wmsg Hlbl /= in Hm. done.
    + rewrite /instr_lbl in Hil. rewrite /es_wmsg Hil Hag /= in Hm.
      simplify_eq. by right.
Qed.

Theorem lb_values_forbidden c :
  cd_img c = img0 → conforms lb_P c → lb_out c → ¬ cand_values c.
Proof.
  intros Himg Hconf (Hout0 & Hout1) Hval.
  (* hart 0's read of x = 1 and its writer *)
  destruct (outc_writer c 0 0 ax b1 Hval Hout0) as
    (krx & srx & tx & kwx & swx & mx &
     Hsrx & Hagrx & Hposrx & _ & Hltx & Hswx & Hmx & Hbx & _).
  { rewrite Himg img0_x. intros Heq. apply b0_ne_b1. by simplify_eq. }
  (* hart 1's read of y = 1 and its writer *)
  destruct (outc_writer c 1 0 ay b1 Hval Hout1) as
    (kry & sry & ty & kwy & swy & my &
     Hsry & Hagry & Hposry & _ & Hlty & Hswy & Hmy & Hby & _).
  { rewrite Himg img0_y. intros Heq. apply b0_ne_b1. by simplify_eq. }
  (* the writer of x is hart 1's SECOND instruction *)
  destruct (lb_wmsg_inv c kwx swx mx Hconf Hswx Hmx)
    as [(_ & _ & ->)|(Hagwx & Hposwx & _)].
  { pose proof (msg_byte_single _ _ _ _ _ (mk_is_Some _ _ Hbx)). lia. }
  (* the writer of y is hart 0's SECOND instruction *)
  destruct (lb_wmsg_inv c kwy swy my Hconf Hswy Hmy)
    as [(Hagwy & Hposwy & _)|(_ & _ & ->)]; last first.
  { pose proof (msg_byte_single _ _ _ _ _ (mk_is_Some _ _ Hby)). lia. }
  (* descend from each store to its hart's first instruction — the reads *)
  destruct (ag_pos_prev (cd_tr c) 1%nat kwx 0%nat Hposwx)
    as (k1 & s1 & Hk1 & Hs1 & Hag1 & Hpos1).
  destruct (ag_pos_prev (cd_tr c) 0%nat kwy 0%nat Hposwy)
    as (k0 & s0 & Hk0 & Hs0 & Hag0 & Hpos0).
  (* ... and identify them with the outcome's read steps *)
  pose proof (ag_pos_inj (cd_tr c) 1%nat k1 kry s1 sry Hs1 Hag1 Hsry Hagry
                ltac:(lia)) as ->.
  pose proof (ag_pos_inj (cd_tr c) 0%nat k0 krx s0 srx Hs0 Hag0 Hsrx Hagrx
                ltac:(lia)) as ->.
  (* krx < kwy < kry < kwx < krx *)
  lia.
Qed.

Theorem lb_forbidden_model c :
  cd_img c = img0 → conforms lb_P c → lb_out c → ¬ srvwmo_consistent c.
Proof.
  intros Himg Hconf Hout (Hsh & Hval & Hax).
  exact (lb_values_forbidden c Himg Hconf Hout Hval).
Qed.

Theorem lb_forbidden_machine c :
  cd_img c = img0 → conforms lb_P c → lb_out c → ¬ exec_wf (cand_exec c).
Proof.
  intros Himg Hconf Hout Hwf.
  exact (lb_forbidden_model c Himg Hconf Hout (srvwmo_of_wf c Hwf)).
Qed.
(* ================================================================== *)
(** *** The shared kit for the remaining negatives *)

(** The three litmus bytes are pairwise distinct, at [option] level. *)
Lemma bs_01 : Some b0 ≠ Some b1.
Proof. intros H. apply b0_ne_b1. congruence. Qed.
Lemma bs_02 : Some b0 ≠ Some b2.
Proof. intros H. apply b0_ne_b2. congruence. Qed.
Lemma bs_10 : Some b1 ≠ Some b0.
Proof. intros H. apply b0_ne_b1. congruence. Qed.
Lemma bs_12 : Some b1 ≠ Some b2.
Proof. intros H. apply b1_ne_b2. congruence. Qed.
Lemma bs_21 : Some b2 ≠ Some b1.
Proof. intros H. apply b1_ne_b2. congruence. Qed.

(** The single-byte messages this file's programs append. *)
Lemma mbx1_x : msg_byte (WMsg ax [b1] (Some 0%nat) WCplain) ax = Some b1.
Proof. rewrite WeakLitmus.msg_byte_single //. Qed.
Lemma mby1_x : msg_byte (WMsg ay [b1] (Some 0%nat) WCplain) ax = None.
Proof. rewrite WeakLitmus.msg_byte_single //. Qed.
Lemma mbx2_x : msg_byte (WMsg ax [b2] (Some 0%nat) WCplain) ax = Some b2.
Proof. rewrite WeakLitmus.msg_byte_single //. Qed.

(** Two steps of DIFFERENT agents are different events. *)
Lemma ev_at_ne c k1 k2 s1 s2 (i j : agent) :
  cd_tr c !! k1 = Some s1 → cd_tr c !! k2 = Some s2 →
  es_ag s1 = i → es_ag s2 = j → i ≠ j → ev_at k1 ≠ ev_at k2.
Proof.
  intros Hs1 Hs2 Ha1 Ha2 Hij Heq.
  assert (k1 = k2) as Hk by congruence.
  rewrite Hk Hs2 in Hs1. injection Hs1 as Hs1. apply Hij. congruence.
Qed.

(** *** Pinning a step's LABEL from conformance

    [conforms] says the step at [k] runs the instruction its agent's program
    has at that agent's own position.  Read in the direction the verdicts
    need — position and agent KNOWN, instruction read off the program — it
    pins the label. *)
Lemma conf_pin (P : prog) c k s (i j : nat) ins :
  conforms P c → cd_tr c !! k = Some s → es_ag s = i →
  ag_pos (cd_tr c) i k = j →
  (P !! i ≫= (λ p, p !! j)) = Some ins → instr_lbl ins (es_lb s).
Proof.
  intros Hconf Hs Hag Hpos Hpi.
  destruct (Hconf k s Hs) as (p & ins' & Hp & Hins & Hil).
  rewrite Hag in Hp. rewrite Hag Hpos in Hins.
  rewrite Hp /= in Hpi.
  assert (ins' = ins) as -> by congruence.
  exact Hil.
Qed.

Lemma conf_store (P : prog) c k s (i j : nat) a v :
  conforms P c → cd_tr c !! k = Some s → es_ag s = i →
  ag_pos (cd_tr c) i k = j →
  (P !! i ≫= (λ p, p !! j)) = Some (IStore a v) →
  es_lb s = LStore false a [v] WCplain ∧
  es_wmsg s = Some (WMsg a [v] (Some i) WCplain).
Proof.
  intros Hconf Hs Hag Hpos Hpi.
  pose proof (conf_pin P c k s i j (IStore a v) Hconf Hs Hag Hpos Hpi) as Hil.
  rewrite /instr_lbl in Hil.
  split; [exact Hil|]. by rewrite /es_wmsg Hil Hag.
Qed.

Lemma conf_fence (P : prog) c k s (i j : nat) pr pw sr sw :
  conforms P c → cd_tr c !! k = Some s → es_ag s = i →
  ag_pos (cd_tr c) i k = j →
  (P !! i ≫= (λ p, p !! j)) = Some (IFence pr pw sr sw) →
  es_lb s = LFence pr pw sr sw.
Proof.
  intros Hconf Hs Hag Hpos Hpi.
  pose proof (conf_pin P c k s i j (IFence pr pw sr sw)
                Hconf Hs Hag Hpos Hpi) as Hil.
  by rewrite /instr_lbl in Hil.
Qed.

Lemma conf_load (P : prog) c k s (i j : nat) r a aq :
  conforms P c → cd_tr c !! k = Some s → es_ag s = i →
  ag_pos (cd_tr c) i k = j →
  (P !! i ≫= (λ p, p !! j)) = Some (ILoad r a aq) →
  ∃ t v, es_lb s = LLoad aq a [t] [v].
Proof.
  intros Hconf Hs Hag Hpos Hpi.
  pose proof (conf_pin P c k s i j (ILoad r a aq) Hconf Hs Hag Hpos Hpi) as Hil.
  by rewrite /instr_lbl in Hil.
Qed.

(* ================================================================== *)
(** *** MP with both fences — forbidden, by [ax_ord]

    <<
      hart 0                     hart 1
        x := 1                     r1 := y     (reads 1)
        fence rw,w                 fence r,rw
        y := 1                     r2 := x     (reads 0 — FORBIDDEN)
    >>

    The reader's fence covers [r,rw], so [ord_pr] holds between its two loads
    and [ax_ord] applies to the [fr] edge out of the stale data read.  MATCHES
    RVWMO (this is the canonical MP-with-fences verdict). *)

Definition mpf_P : prog :=
  [[IStore ax b1; FENCE_RW_W; IStore ay b1];
   [ILoad rg1 ay false; FENCE_R_RW; ILoad rg2 ax false]].
Definition mpf_out (c : cand) : Prop := outc c 1 0 ay b1 ∧ outc c 1 2 ax b0.

(** The only writing steps are hart 0's two stores. *)
Lemma mpf_wmsg_inv c k s m :
  conforms mpf_P c → cd_tr c !! k = Some s → es_wmsg s = Some m →
  (es_ag s = 0%nat ∧ ag_pos (cd_tr c) 0%nat k = 0%nat ∧
   m = WMsg ax [b1] (Some 0%nat) WCplain) ∨
  (es_ag s = 0%nat ∧ ag_pos (cd_tr c) 0%nat k = 2%nat ∧
   m = WMsg ay [b1] (Some 0%nat) WCplain).
Proof.
  intros Hconf Hs Hm.
  destruct (Hconf k s Hs) as (p & ins & Hp & Hins & Hil).
  destruct (es_ag s) as [|[|n]] eqn:Hag; simplify_eq/=.
  - destruct (ag_pos (cd_tr c) 0%nat k) as [|[|[|j]]] eqn:Hpos; simplify_eq/=.
    + rewrite /instr_lbl in Hil. rewrite /es_wmsg Hil Hag /= in Hm.
      simplify_eq. by left.
    + rewrite /instr_lbl in Hil. rewrite /es_wmsg Hil /= in Hm. done.
    + rewrite /instr_lbl in Hil. rewrite /es_wmsg Hil Hag /= in Hm.
      simplify_eq. by right.
  - destruct (ag_pos (cd_tr c) 1%nat k) as [|[|[|j]]] eqn:Hpos; simplify_eq/=.
    + destruct Hil as (t0 & v0 & Hlbl). rewrite /es_wmsg Hlbl /= in Hm. done.
    + rewrite /instr_lbl in Hil. rewrite /es_wmsg Hil /= in Hm. done.
    + destruct Hil as (t0 & v0 & Hlbl). rewrite /es_wmsg Hlbl /= in Hm. done.
Qed.

Theorem mpf_forbidden_model c :
  cd_img c = img0 → conforms mpf_P c → mpf_out c → ¬ srvwmo_consistent c.
Proof.
  intros Himg Hconf (Houty & Houtx)
    (Hsh & Hval & ((Hrft & Hrff & Hrfv & Hcoh & Hatom & Hord & Hnta & Hpoww)
                   & Hrel & Hob)).
  (* the reader's flag read, and the step that wrote the flag *)
  destruct (outc_writer c 1%nat 0%nat ay b1 Hval Houty) as
    (kry & sry & ty & kwy & swy & my &
     Hsry & Hagry & Hposry & Hrdy & Hltwy & Hswy & Hmy & Hby & Htsy).
  { rewrite Himg img0_y. exact bs_01. }
  (* it is hart 0's THIRD instruction — the store to y *)
  destruct (mpf_wmsg_inv c kwy swy my Hconf Hswy Hmy)
    as [(_ & _ & ->)|(Hagwy & Hposwy & _)].
  { pose proof (msg_byte_single _ _ _ _ _ (mk_is_Some _ _ Hby)). lia. }
  (* the reader's data read is INITIAL: no instruction writes b0 at x *)
  destruct (outc_initial c 1%nat 2%nat ax b0 Hval Houtx) as
    (krx & srx & Hsrx & Hagrx & Hposrx & Hrdx & Himgx).
  { intros k' s' m' Hs' Hm' Hb'.
    destruct (mpf_wmsg_inv c k' s' m' Hconf Hs' Hm') as [(_ & _ & ->)|(_ & _ & ->)].
    - rewrite mbx1_x in Hb'. exact (bs_10 Hb').
    - rewrite mby1_x in Hb'. done. }
  (* WRITER SIDE: descend y-store ↦ fence ↦ x-store, then trace-order the
     two timestamps *)
  destruct (ag_pos_prev (cd_tr c) 0%nat kwy 1%nat Hposwy)
    as (kwf & swf & Hltwf & Hswf & Hagwf & Hposwf).
  destruct (ag_pos_prev (cd_tr c) 0%nat kwf 0%nat Hposwf)
    as (kwx & swx & Hltwx & Hswx & Hagwx & Hposwx).
  destruct (conf_store mpf_P c kwx swx 0%nat 0%nat ax b1
              Hconf Hswx Hagwx Hposwx eq_refl) as [_ Hmwx].
  pose proof (lookup_lt_Some _ _ _ Hsry) as Hlenry.
  pose proof (cand_ts_mono c kwx kwy swx (WMsg ax [b1] (Some 0%nat) WCplain)
                Hswx Hmwx ltac:(lia) ltac:(lia)) as Htsx.
  (* READER SIDE: the fence sits between the two loads *)
  destruct (ag_pos_prev (cd_tr c) 1%nat krx 1%nat Hposrx)
    as (kf & sf & Hltf & Hsf & Hagf & Hposf).
  pose proof (conf_fence mpf_P c kf sf 1%nat 1%nat true false true true
                Hconf Hsf Hagf Hposf eq_refl) as Hlf.
  destruct (ag_pos_prev (cd_tr c) 1%nat kf 0%nat Hposf)
    as (kr0 & sr0 & Hltr0 & Hsr0 & Hagr0 & Hposr0).
  pose proof (ag_pos_inj (cd_tr c) 1%nat kr0 kry sr0 sry Hsr0 Hagr0 Hsry Hagry
                ltac:(lia)) as Hkr0.
  assert (Hfb : fence_between (cand_exec c) kry krx true false true true).
  { exists kf, sf, sry, srx. split_and!.
    - lia.
    - lia.
    - by rewrite cand_ex_tr.
    - by rewrite cand_ex_tr.
    - by rewrite cand_ex_tr.
    - congruence.
    - congruence.
    - exact Hlf. }
  assert (Hordpr : ord_pr (cand_exec c) (ev_at kry) (ev_at krx)).
  { left. exists kry, krx, false, true. split_and!; [done|done|exact Hfb]. }
  (* the flag read publishes ty: its rf edge is EXTERNAL *)
  assert (Hrfy : rf_b (cand_exec c) ay (ev_at kwy) (ev_at kry)).
  { split.
    - exact (cand_wr_b c kwy swy my ay Hswy Hmy (mk_is_Some _ _ Hby)).
    - exists kry, ty, b1. split_and!;
        [done|exact (cand_reads_at1 c kry sry ay ty b1 Hsry Hrdy)|exact Htsy]. }
  assert (Hpubr : pub_r (cand_exec c) (ev_at kry) ty).
  { exists kry, sry, ay, b1. split_and!.
    - done.
    - by rewrite cand_ex_tr.
    - exact (cand_reads_at1 c kry sry ay ty b1 Hsry Hrdy).
    - right. exists (ev_at kwy). split; [exact Hrfy|].
      exists swy. split; [by rewrite cand_ex_tr|]. rewrite Hagwy Hagry. lia. }
  (* the stale data read is fr-before the data store *)
  assert (Hfr : fr_b (cand_exec c) ax (ev_at krx) (ev_at kwx)).
  { split.
    - exists ev_init. split.
      + split; [exact (cand_wr_b_init c ax (mk_is_Some _ _ Himgx))|].
        exists krx, 0%nat, b0. split_and!;
          [done|exact (cand_reads_at1 c krx srx ax 0%nat b0 Hsrx Hrdx)|done].
      + split_and!.
        * exact (cand_wr_b_init c ax (mk_is_Some _ _ Himgx)).
        * exact (cand_wr_b c kwx swx _ ax Hswx Hmwx (mk_is_Some _ _ mbx1_x)).
        * rewrite /ev_ts /=. lia.
    - exact (ev_at_ne c krx kwx srx swx 1%nat 0%nat Hsrx Hswx Hagrx Hagwx
               ltac:(lia)). }
  pose proof (Hord (ev_at kry) krx srx ax (ev_at kwx) ty
                ltac:(by rewrite cand_ex_tr) (or_intror (conj Hordpr Hpubr)) Hfr)
    as Hlt.
  lia.
Qed.

Theorem mpf_forbidden_machine c :
  cd_img c = img0 → conforms mpf_P c → mpf_out c → ¬ exec_wf (cand_exec c).
Proof.
  intros Himg Hconf Hout Hwf.
  exact (mpf_forbidden_model c Himg Hconf Hout (srvwmo_of_wf c Hwf)).
Qed.

(* ================================================================== *)
(** *** MP with a writer fence and an ACQUIRE load — forbidden, by [ax_ord]

    <<
      hart 0                     hart 1
        x := 1                     r1 := y.aq  (reads 1)
        fence rw,w                 r2 := x     (reads 0 — FORBIDDEN)
        y := 1
    >>

    Same proof, with the reader's ordering edge coming from [acq_po] instead
    of a fence — the acquire load is [lb_aq]-marked, so every po-later step of
    its hart is [ord_pr]-after it.  MATCHES RVWMO. *)

Definition mpa_P : prog :=
  [[IStore ax b1; FENCE_RW_W; IStore ay b1];
   [ILoad rg1 ay true; ILoad rg2 ax false]].
Definition mpa_out (c : cand) : Prop := outc c 1 0 ay b1 ∧ outc c 1 1 ax b0.

Lemma mpa_wmsg_inv c k s m :
  conforms mpa_P c → cd_tr c !! k = Some s → es_wmsg s = Some m →
  (es_ag s = 0%nat ∧ ag_pos (cd_tr c) 0%nat k = 0%nat ∧
   m = WMsg ax [b1] (Some 0%nat) WCplain) ∨
  (es_ag s = 0%nat ∧ ag_pos (cd_tr c) 0%nat k = 2%nat ∧
   m = WMsg ay [b1] (Some 0%nat) WCplain).
Proof.
  intros Hconf Hs Hm.
  destruct (Hconf k s Hs) as (p & ins & Hp & Hins & Hil).
  destruct (es_ag s) as [|[|n]] eqn:Hag; simplify_eq/=.
  - destruct (ag_pos (cd_tr c) 0%nat k) as [|[|[|j]]] eqn:Hpos; simplify_eq/=.
    + rewrite /instr_lbl in Hil. rewrite /es_wmsg Hil Hag /= in Hm.
      simplify_eq. by left.
    + rewrite /instr_lbl in Hil. rewrite /es_wmsg Hil /= in Hm. done.
    + rewrite /instr_lbl in Hil. rewrite /es_wmsg Hil Hag /= in Hm.
      simplify_eq. by right.
  - destruct (ag_pos (cd_tr c) 1%nat k) as [|[|j]] eqn:Hpos; simplify_eq/=;
      destruct Hil as (t0 & v0 & Hlbl); rewrite /es_wmsg Hlbl /= in Hm; done.
Qed.

Theorem mpa_forbidden_model c :
  cd_img c = img0 → conforms mpa_P c → mpa_out c → ¬ srvwmo_consistent c.
Proof.
  intros Himg Hconf (Houty & Houtx)
    (Hsh & Hval & ((Hrft & Hrff & Hrfv & Hcoh & Hatom & Hord & Hnta & Hpoww)
                   & Hrel & Hob)).
  destruct (outc_writer c 1%nat 0%nat ay b1 Hval Houty) as
    (kry & sry & ty & kwy & swy & my &
     Hsry & Hagry & Hposry & Hrdy & Hltwy & Hswy & Hmy & Hby & Htsy).
  { rewrite Himg img0_y. exact bs_01. }
  destruct (mpa_wmsg_inv c kwy swy my Hconf Hswy Hmy)
    as [(_ & _ & ->)|(Hagwy & Hposwy & _)].
  { pose proof (msg_byte_single _ _ _ _ _ (mk_is_Some _ _ Hby)). lia. }
  destruct (outc_initial c 1%nat 1%nat ax b0 Hval Houtx) as
    (krx & srx & Hsrx & Hagrx & Hposrx & Hrdx & Himgx).
  { intros k' s' m' Hs' Hm' Hb'.
    destruct (mpa_wmsg_inv c k' s' m' Hconf Hs' Hm') as [(_ & _ & ->)|(_ & _ & ->)].
    - rewrite mbx1_x in Hb'. exact (bs_10 Hb').
    - rewrite mby1_x in Hb'. done. }
  (* WRITER SIDE — as in §1 *)
  destruct (ag_pos_prev (cd_tr c) 0%nat kwy 1%nat Hposwy)
    as (kwf & swf & Hltwf & Hswf & Hagwf & Hposwf).
  destruct (ag_pos_prev (cd_tr c) 0%nat kwf 0%nat Hposwf)
    as (kwx & swx & Hltwx & Hswx & Hagwx & Hposwx).
  destruct (conf_store mpa_P c kwx swx 0%nat 0%nat ax b1
              Hconf Hswx Hagwx Hposwx eq_refl) as [_ Hmwx].
  pose proof (lookup_lt_Some _ _ _ Hsry) as Hlenry.
  pose proof (cand_ts_mono c kwx kwy swx (WMsg ax [b1] (Some 0%nat) WCplain)
                Hswx Hmwx ltac:(lia) ltac:(lia)) as Htsx.
  (* READER SIDE: the acquire load is po-before the data load *)
  destruct (ag_pos_prev (cd_tr c) 1%nat krx 0%nat Hposrx)
    as (kr0 & sr0 & Hltr0 & Hsr0 & Hagr0 & Hposr0).
  pose proof (ag_pos_inj (cd_tr c) 1%nat kr0 kry sr0 sry Hsr0 Hagr0 Hsry Hagry
                ltac:(lia)) as Hkr0.
  destruct (conf_load mpa_P c kry sry 1%nat 0%nat rg1 ay true
              Hconf Hsry Hagry Hposry eq_refl) as (t0 & v0 & Hlry).
  assert (Hacq : acq_po (cand_exec c) (ev_at kry) (ev_at krx)).
  { exists kry, krx, sry, srx. split_and!.
    - done.
    - done.
    - lia.
    - by rewrite cand_ex_tr.
    - by rewrite cand_ex_tr.
    - congruence.
    - by rewrite Hlry.
    - by rewrite Hlry. }
  assert (Hordpr : ord_pr (cand_exec c) (ev_at kry) (ev_at krx))
    by exact (or_intror Hacq).
  assert (Hrfy : rf_b (cand_exec c) ay (ev_at kwy) (ev_at kry)).
  { split.
    - exact (cand_wr_b c kwy swy my ay Hswy Hmy (mk_is_Some _ _ Hby)).
    - exists kry, ty, b1. split_and!;
        [done|exact (cand_reads_at1 c kry sry ay ty b1 Hsry Hrdy)|exact Htsy]. }
  assert (Hpubr : pub_r (cand_exec c) (ev_at kry) ty).
  { exists kry, sry, ay, b1. split_and!.
    - done.
    - by rewrite cand_ex_tr.
    - exact (cand_reads_at1 c kry sry ay ty b1 Hsry Hrdy).
    - left. by rewrite Hlry. }
  assert (Hfr : fr_b (cand_exec c) ax (ev_at krx) (ev_at kwx)).
  { split.
    - exists ev_init. split.
      + split; [exact (cand_wr_b_init c ax (mk_is_Some _ _ Himgx))|].
        exists krx, 0%nat, b0. split_and!;
          [done|exact (cand_reads_at1 c krx srx ax 0%nat b0 Hsrx Hrdx)|done].
      + split_and!.
        * exact (cand_wr_b_init c ax (mk_is_Some _ _ Himgx)).
        * exact (cand_wr_b c kwx swx _ ax Hswx Hmwx (mk_is_Some _ _ mbx1_x)).
        * rewrite /ev_ts /=. lia.
    - exact (ev_at_ne c krx kwx srx swx 1%nat 0%nat Hsrx Hswx Hagrx Hagwx
               ltac:(lia)). }
  pose proof (Hord (ev_at kry) krx srx ax (ev_at kwx) ty
                ltac:(by rewrite cand_ex_tr) (or_intror (conj Hordpr Hpubr)) Hfr)
    as Hlt.
  lia.
Qed.

Theorem mpa_forbidden_machine c :
  cd_img c = img0 → conforms mpa_P c → mpa_out c → ¬ exec_wf (cand_exec c).
Proof.
  intros Himg Hconf Hout Hwf.
  exact (mpa_forbidden_model c Himg Hconf Hout (srvwmo_of_wf c Hwf)).
Qed.

(* ================================================================== *)
(** *** MP with the READER fence only — forbidden, and this DIVERGES

    <<
      hart 0                     hart 1
        x := 1                     r1 := y     (reads 1)
        y := 1                     fence r,rw
                                   r2 := x     (reads 0 — FORBIDDEN HERE)
    >>

    RVWMO ALLOWS this outcome: with no [fence rw,w] between the writer's two
    stores nothing orders them in the global memory order, so the flag may
    become visible first.  sRVWMO FORBIDS it — DIVERGENCE (2) of
    [WeakSrvwmoLitmus] §9's table.  The culprit is the promise-free
    strengthening [ax_po_ww_gmo] (ppo rule 14 in the candidate presentation):
    a candidate's trace order IS its global memory order, so the writer's two
    stores are gmo-ordered by po alone.  Mechanically the proof below is §1's
    with ONE descent on the writer side instead of two — the writer's fence
    was never used. *)

Definition mpg_P : prog :=
  [[IStore ax b1; IStore ay b1];
   [ILoad rg1 ay false; FENCE_R_RW; ILoad rg2 ax false]].
Definition mpg_out (c : cand) : Prop := outc c 1 0 ay b1 ∧ outc c 1 2 ax b0.

Lemma mpg_wmsg_inv c k s m :
  conforms mpg_P c → cd_tr c !! k = Some s → es_wmsg s = Some m →
  (es_ag s = 0%nat ∧ ag_pos (cd_tr c) 0%nat k = 0%nat ∧
   m = WMsg ax [b1] (Some 0%nat) WCplain) ∨
  (es_ag s = 0%nat ∧ ag_pos (cd_tr c) 0%nat k = 1%nat ∧
   m = WMsg ay [b1] (Some 0%nat) WCplain).
Proof.
  intros Hconf Hs Hm.
  destruct (Hconf k s Hs) as (p & ins & Hp & Hins & Hil).
  destruct (es_ag s) as [|[|n]] eqn:Hag; simplify_eq/=.
  - destruct (ag_pos (cd_tr c) 0%nat k) as [|[|j]] eqn:Hpos; simplify_eq/=.
    + rewrite /instr_lbl in Hil. rewrite /es_wmsg Hil Hag /= in Hm.
      simplify_eq. by left.
    + rewrite /instr_lbl in Hil. rewrite /es_wmsg Hil Hag /= in Hm.
      simplify_eq. by right.
  - destruct (ag_pos (cd_tr c) 1%nat k) as [|[|[|j]]] eqn:Hpos; simplify_eq/=.
    + destruct Hil as (t0 & v0 & Hlbl). rewrite /es_wmsg Hlbl /= in Hm. done.
    + rewrite /instr_lbl in Hil. rewrite /es_wmsg Hil /= in Hm. done.
    + destruct Hil as (t0 & v0 & Hlbl). rewrite /es_wmsg Hlbl /= in Hm. done.
Qed.

Theorem mpg_forbidden_model c :
  cd_img c = img0 → conforms mpg_P c → mpg_out c → ¬ srvwmo_consistent c.
Proof.
  intros Himg Hconf (Houty & Houtx)
    (Hsh & Hval & ((Hrft & Hrff & Hrfv & Hcoh & Hatom & Hord & Hnta & Hpoww)
                   & Hrel & Hob)).
  destruct (outc_writer c 1%nat 0%nat ay b1 Hval Houty) as
    (kry & sry & ty & kwy & swy & my &
     Hsry & Hagry & Hposry & Hrdy & Hltwy & Hswy & Hmy & Hby & Htsy).
  { rewrite Himg img0_y. exact bs_01. }
  destruct (mpg_wmsg_inv c kwy swy my Hconf Hswy Hmy)
    as [(_ & _ & ->)|(Hagwy & Hposwy & _)].
  { pose proof (msg_byte_single _ _ _ _ _ (mk_is_Some _ _ Hby)). lia. }
  destruct (outc_initial c 1%nat 2%nat ax b0 Hval Houtx) as
    (krx & srx & Hsrx & Hagrx & Hposrx & Hrdx & Himgx).
  { intros k' s' m' Hs' Hm' Hb'.
    destruct (mpg_wmsg_inv c k' s' m' Hconf Hs' Hm') as [(_ & _ & ->)|(_ & _ & ->)].
    - rewrite mbx1_x in Hb'. exact (bs_10 Hb').
    - rewrite mby1_x in Hb'. done. }
  (* WRITER SIDE: ONE descent — no fence to step over *)
  destruct (ag_pos_prev (cd_tr c) 0%nat kwy 0%nat Hposwy)
    as (kwx & swx & Hltwx & Hswx & Hagwx & Hposwx).
  destruct (conf_store mpg_P c kwx swx 0%nat 0%nat ax b1
              Hconf Hswx Hagwx Hposwx eq_refl) as [_ Hmwx].
  pose proof (lookup_lt_Some _ _ _ Hsry) as Hlenry.
  pose proof (cand_ts_mono c kwx kwy swx (WMsg ax [b1] (Some 0%nat) WCplain)
                Hswx Hmwx ltac:(lia) ltac:(lia)) as Htsx.
  (* READER SIDE — as in §1 *)
  destruct (ag_pos_prev (cd_tr c) 1%nat krx 1%nat Hposrx)
    as (kf & sf & Hltf & Hsf & Hagf & Hposf).
  pose proof (conf_fence mpg_P c kf sf 1%nat 1%nat true false true true
                Hconf Hsf Hagf Hposf eq_refl) as Hlf.
  destruct (ag_pos_prev (cd_tr c) 1%nat kf 0%nat Hposf)
    as (kr0 & sr0 & Hltr0 & Hsr0 & Hagr0 & Hposr0).
  pose proof (ag_pos_inj (cd_tr c) 1%nat kr0 kry sr0 sry Hsr0 Hagr0 Hsry Hagry
                ltac:(lia)) as Hkr0.
  assert (Hfb : fence_between (cand_exec c) kry krx true false true true).
  { exists kf, sf, sry, srx. split_and!.
    - lia.
    - lia.
    - by rewrite cand_ex_tr.
    - by rewrite cand_ex_tr.
    - by rewrite cand_ex_tr.
    - congruence.
    - congruence.
    - exact Hlf. }
  assert (Hordpr : ord_pr (cand_exec c) (ev_at kry) (ev_at krx)).
  { left. exists kry, krx, false, true. split_and!; [done|done|exact Hfb]. }
  assert (Hrfy : rf_b (cand_exec c) ay (ev_at kwy) (ev_at kry)).
  { split.
    - exact (cand_wr_b c kwy swy my ay Hswy Hmy (mk_is_Some _ _ Hby)).
    - exists kry, ty, b1. split_and!;
        [done|exact (cand_reads_at1 c kry sry ay ty b1 Hsry Hrdy)|exact Htsy]. }
  assert (Hpubr : pub_r (cand_exec c) (ev_at kry) ty).
  { exists kry, sry, ay, b1. split_and!.
    - done.
    - by rewrite cand_ex_tr.
    - exact (cand_reads_at1 c kry sry ay ty b1 Hsry Hrdy).
    - right. exists (ev_at kwy). split; [exact Hrfy|].
      exists swy. split; [by rewrite cand_ex_tr|]. rewrite Hagwy Hagry. lia. }
  assert (Hfr : fr_b (cand_exec c) ax (ev_at krx) (ev_at kwx)).
  { split.
    - exists ev_init. split.
      + split; [exact (cand_wr_b_init c ax (mk_is_Some _ _ Himgx))|].
        exists krx, 0%nat, b0. split_and!;
          [done|exact (cand_reads_at1 c krx srx ax 0%nat b0 Hsrx Hrdx)|done].
      + split_and!.
        * exact (cand_wr_b_init c ax (mk_is_Some _ _ Himgx)).
        * exact (cand_wr_b c kwx swx _ ax Hswx Hmwx (mk_is_Some _ _ mbx1_x)).
        * rewrite /ev_ts /=. lia.
    - exact (ev_at_ne c krx kwx srx swx 1%nat 0%nat Hsrx Hswx Hagrx Hagwx
               ltac:(lia)). }
  pose proof (Hord (ev_at kry) krx srx ax (ev_at kwx) ty
                ltac:(by rewrite cand_ex_tr) (or_intror (conj Hordpr Hpubr)) Hfr)
    as Hlt.
  lia.
Qed.

Theorem mpg_forbidden_machine c :
  cd_img c = img0 → conforms mpg_P c → mpg_out c → ¬ exec_wf (cand_exec c).
Proof.
  intros Himg Hconf Hout Hwf.
  exact (mpg_forbidden_model c Himg Hconf Hout (srvwmo_of_wf c Hwf)).
Qed.

(* ================================================================== *)
(** *** CoRR — forbidden, by [ax_coherence]

    <<
      hart 0                     hart 1
        x := 1                     r1 := x     (reads 2)
        x := 2                     r2 := x     (reads 1 — FORBIDDEN)
    >>

    One hart reads the NEW value and then the OLD one.  No ordering axiom is
    needed: per-byte coherence ([ax_coherence], SC-per-location) already
    forbids the cycle

      r1 --po-loc--> r2 --fr--> (x:=2) --rf--> r1

    where the [fr] edge is [r2] reading [x:=1] while [x:=1] is [co]-before
    [x:=2] (their trace order, [cand_ts_mono]).  MATCHES RVWMO. *)

Definition corr_P : prog :=
  [[IStore ax b1; IStore ax b2];
   [ILoad rg1 ax false; ILoad rg2 ax false]].
Definition corr_out (c : cand) : Prop := outc c 1 0 ax b2 ∧ outc c 1 1 ax b1.

Lemma corr_wmsg_inv c k s m :
  conforms corr_P c → cd_tr c !! k = Some s → es_wmsg s = Some m →
  (es_ag s = 0%nat ∧ ag_pos (cd_tr c) 0%nat k = 0%nat ∧
   m = WMsg ax [b1] (Some 0%nat) WCplain) ∨
  (es_ag s = 0%nat ∧ ag_pos (cd_tr c) 0%nat k = 1%nat ∧
   m = WMsg ax [b2] (Some 0%nat) WCplain).
Proof.
  intros Hconf Hs Hm.
  destruct (Hconf k s Hs) as (p & ins & Hp & Hins & Hil).
  destruct (es_ag s) as [|[|n]] eqn:Hag; simplify_eq/=.
  - destruct (ag_pos (cd_tr c) 0%nat k) as [|[|j]] eqn:Hpos; simplify_eq/=.
    + rewrite /instr_lbl in Hil. rewrite /es_wmsg Hil Hag /= in Hm.
      simplify_eq. by left.
    + rewrite /instr_lbl in Hil. rewrite /es_wmsg Hil Hag /= in Hm.
      simplify_eq. by right.
  - destruct (ag_pos (cd_tr c) 1%nat k) as [|[|j]] eqn:Hpos; simplify_eq/=;
      destruct Hil as (t0 & v0 & Hlbl); rewrite /es_wmsg Hlbl /= in Hm; done.
Qed.

Theorem corr_forbidden_model c :
  cd_img c = img0 → conforms corr_P c → corr_out c → ¬ srvwmo_consistent c.
Proof.
  intros Himg Hconf (Hout2 & Hout1)
    (Hsh & Hval & ((Hrft & Hrff & Hrfv & Hcoh & Hatom & Hord & Hnta & Hpoww)
                   & Hrel & Hob)).
  (* the read of 2 comes from the SECOND store *)
  destruct (outc_writer c 1%nat 0%nat ax b2 Hval Hout2) as
    (kr2 & sr2 & t2 & kw2 & sw2 & m2 &
     Hsr2 & Hagr2 & Hposr2 & Hrd2 & Hlt2 & Hsw2 & Hmw2 & Hb2 & Hts2).
  { rewrite Himg img0_x. exact bs_02. }
  destruct (corr_wmsg_inv c kw2 sw2 m2 Hconf Hsw2 Hmw2)
    as [(_ & _ & ->)|(Hagw2 & Hposw2 & ->)].
  { rewrite mbx1_x in Hb2. exact (bs_12 Hb2). }
  (* the read of 1 comes from the FIRST store *)
  destruct (outc_writer c 1%nat 1%nat ax b1 Hval Hout1) as
    (kr1 & sr1 & t1 & kw1 & sw1 & m1 &
     Hsr1 & Hagr1 & Hposr1 & Hrd1 & Hlt1 & Hsw1 & Hmw1 & Hb1 & Hts1).
  { rewrite Himg img0_x. exact bs_01. }
  destruct (corr_wmsg_inv c kw1 sw1 m1 Hconf Hsw1 Hmw1)
    as [(Hagw1 & Hposw1 & ->)|(_ & _ & ->)]; last first.
  { rewrite mbx2_x in Hb1. exact (bs_21 Hb1). }
  (* the reader's two loads, and the writer's two stores, in trace order *)
  destruct (ag_pos_prev (cd_tr c) 1%nat kr1 0%nat Hposr1)
    as (kr0 & sr0 & Hltr0 & Hsr0 & Hagr0 & Hposr0).
  pose proof (ag_pos_inj (cd_tr c) 1%nat kr0 kr2 sr0 sr2 Hsr0 Hagr0 Hsr2 Hagr2
                ltac:(lia)) as Hkr0.
  destruct (ag_pos_prev (cd_tr c) 0%nat kw2 0%nat Hposw2)
    as (kw0 & sw0 & Hltw0 & Hsw0 & Hagw0 & Hposw0).
  pose proof (ag_pos_inj (cd_tr c) 0%nat kw0 kw1 sw0 sw1 Hsw0 Hagw0 Hsw1 Hagw1
                ltac:(lia)) as Hkw0.
  pose proof (lookup_lt_Some _ _ _ Hsr2) as Hlen2.
  pose proof (cand_ts_mono c kw1 kw2 sw1 (WMsg ax [b1] (Some 0%nat) WCplain)
                Hsw1 Hmw1 ltac:(lia) ltac:(lia)) as Htslt.
  (* the three edges of the coherence cycle *)
  assert (Hpl : po_loc_b (cand_exec c) ax (ev_at kr2) (ev_at kr1)).
  { split_and!.
    - exists kr2, kr1, sr2, sr1. split_and!;
        [done|done|lia|by rewrite cand_ex_tr|by rewrite cand_ex_tr|congruence].
    - right. exists kr2, t2, b2.
      split; [done|exact (cand_reads_at1 c kr2 sr2 ax t2 b2 Hsr2 Hrd2)].
    - right. exists kr1, t1, b1.
      split; [done|exact (cand_reads_at1 c kr1 sr1 ax t1 b1 Hsr1 Hrd1)]. }
  assert (Hfr : fr_b (cand_exec c) ax (ev_at kr1) (ev_at kw2)).
  { split.
    - exists (ev_at kw1). split.
      + split.
        * exact (cand_wr_b c kw1 sw1 _ ax Hsw1 Hmw1 (mk_is_Some _ _ Hb1)).
        * exists kr1, t1, b1. split_and!;
            [done|exact (cand_reads_at1 c kr1 sr1 ax t1 b1 Hsr1 Hrd1)|exact Hts1].
      + split_and!.
        * exact (cand_wr_b c kw1 sw1 _ ax Hsw1 Hmw1 (mk_is_Some _ _ Hb1)).
        * exact (cand_wr_b c kw2 sw2 _ ax Hsw2 Hmw2 (mk_is_Some _ _ Hb2)).
        * exact Htslt.
    - exact (ev_at_ne c kr1 kw2 sr1 sw2 1%nat 0%nat Hsr1 Hsw2 Hagr1 Hagw2
               ltac:(lia)). }
  assert (Hrf : rf_b (cand_exec c) ax (ev_at kw2) (ev_at kr2)).
  { split.
    - exact (cand_wr_b c kw2 sw2 _ ax Hsw2 Hmw2 (mk_is_Some _ _ Hb2)).
    - exists kr2, t2, b2. split_and!;
        [done|exact (cand_reads_at1 c kr2 sr2 ax t2 b2 Hsr2 Hrd2)|exact Hts2]. }
  apply (Hcoh ax (ev_at kr2)).
  eapply tc_l; [left; exact Hpl|].
  eapply tc_l; [right; right; right; exact Hfr|].
  apply tc_once. right. left. exact Hrf.
Qed.

Theorem corr_forbidden_machine c :
  cd_img c = img0 → conforms corr_P c → corr_out c → ¬ exec_wf (cand_exec c).
Proof.
  intros Himg Hconf Hout Hwf.
  exact (corr_forbidden_model c Himg Hconf Hout (srvwmo_of_wf c Hwf)).
Qed.

(* ================================================================== *)
(** * 7. The two precedents this file does NOT redo

    Two verdict-grade facts about the model were already machine-checked in
    [WeakAxiomatic3] §13, as the counterexamples that PINNED the definition;
    they are cited rather than restated:

    - RELEASE→ACQUIRE (ppo rule 7): the three-step witness with a release
      store po-before an acquire load.  [ce_rl_true_inconsistent] is the
      NEGATIVE verdict (the stale acquire read is sRVWMO-inconsistent — the
      [ax_rel_ord]/[rel_acq_po] arm is exactly what kills it), and
      [ce_rl_stale_reachable] is the POSITIVE twin with the [.rl] bit
      dropped: same trace, plain store, stale read allowed and
      machine-reachable.  Together they are rule 7's non-vacuity witness.

    - OWN-STORE FORWARDING: [ce_fwd] — a plain load reading the agent's own
      po-earlier store "early" — is machine-reachable ([ce_fwd_reachable])
      and refuted the old [cand_pub_clean] premise ([ce_fwd_not_pub_clean]);
      post-A3(ii) it is simply a consistent candidate, i.e. the positive
      forwarding verdict. *)

(* ================================================================== *)
(** * 8. What is NOT done, with prices

    - IRIW (operationally forbidden: [WeakLitmus.iriw_forbidden], both
      readers fenced [rw,rw]).  The axiomatic refutation needs the one piece
      none of the six negatives above use: comparing the two independent
      writes' positions in the trace (gmo totality on writes, free here),
      then the two readers' [ax_ord] instances point in opposite directions.
      No new machinery — the [outc_writer] descent and the [ax_ord]
      application of the MP template, twice, under a case split on which
      store logged first.  ~150 lines.

    - SB-FENCED, both directions.  Its fences are [rw,rw], i.e. [sr = true],
      so [cand_plain_ok] does NOT apply and both verdicts leave the kit: the
      POSITIVE ((0,1) reachable — [WeakLitmus.sb_fenced_01_reachable]) needs
      a real [ax_ord] discharge for a concrete candidate (~60 lines); the
      NEGATIVE ((0,0) forbidden — which [WeakLitmus] asserts in prose but
      does not prove operationally either) is the MP template symmetrized
      (~120 lines).

    - The ATOMICITY negative: an AMO whose read half takes a NON-latest
      timestamp is inconsistent ([ax_atomicity] kills it — the model twin of
      [WeakLitmus.amo_latest_unique]).  The §5 AMO candidate plus one
      interposed store.  ~50 lines.

    - SPLIT-EXCLUSIVE shapes ([LExLoad]/[LExStore], dangling reservations)
      are not in this file's alphabet at all: the axiomatic model keeps
      exclusives FUSED (the projection re-fuses; a dangling exclusive read
      projects as a plain load), so the split tier's litmus story belongs to
      the R-track, not here. *)

(* ================================================================== *)
(** * 9. THE VERDICT TABLE

    Every verdict below is against [srvwmo_consistent] — the DEFINITION; the
    last column is [WeakLitmus]'s operational verdict on the same program,
    and every row agrees with it, as T1/T2 say it must.

      shape                    outcome           sRVWMO     RVWMO      here / operational ([WeakLitmus])
      ----------------------------------------------------------------------------------------------------
      SB, no fences            r1=0 ∧ r2=0       allowed    allowed    [sb_00_allowed]       / [sb_00_reachable]
      MP, no fences            flag=1 ∧ data=0   allowed    allowed    [mpn_weak_allowed]    / [mp_nofence_weak_reachable]
      MP, writer fence only    flag=1 ∧ data=0   allowed    allowed    [mpw_weak_allowed]    / [mp_wfence_weak_reachable]
      AMO (amoswap.aq)         reads the latest  allowed    allowed    [amo_latest_allowed]  / [amo_swap_reachable]
      MP, both fences          flag=1 ∧ data=0   FORBIDDEN  forbidden  [mpf_forbidden_model] / [mp_fenced_forbidden]
      MP, wr fence + acquire   flag=1 ∧ data=0   FORBIDDEN  forbidden  [mpa_forbidden_model] / [mp_acquire_forbidden]
      MP, READER fence only    flag=1 ∧ data=0   FORBIDDEN  ALLOWED    [mpg_forbidden_model] / [mp_reader_fence_only_forbidden]
      CoRR                     r1=new ∧ r2=old   FORBIDDEN  forbidden  [corr_forbidden_model] / [corr_forbidden]
      LB                       r1=1 ∧ r2=1       FORBIDDEN  ALLOWED    [lb_forbidden_model]  / [lb_forbidden]

    THE TWO DELIBERATE DIVERGENCES from RVWMO, both bought by ppo rule 14
    (stores are never early):

    (1) LB is FORBIDDEN — and the refutation ([lb_values_forbidden]) never
        consults an ordering axiom: the LOAD-VALUE axiom alone (reads take
        their value from the log PREFIX) makes the outcome's four trace
        positions cyclic.  In the candidate presentation no-thin-air is
        definitional ([cand_no_thin_air] is free for every value-consistent
        candidate).  This is the design doc's "LB must be unobservable",
        mechanized.

    (2) MP with ONLY a reader fence is FORBIDDEN — rule 14 puts the writer's
        two stores in gmo order with no fence between them (the candidate's
        trace order IS gmo on writes: [ax_po_ww_gmo]), so the reader-side
        ordering alone completes the forbidden cycle; RVWMO allows the stale
        read here.  NOTE what this does to the design doc §3 corollary (b)
        slogan ("LB unobservable, everything else matches riscv.cat"): rule
        14 narrows the hardware class by MORE than LB — reader-fence-only MP
        is a second observable difference, exactly the in-order-store-
        visibility strengthening the design's §1 declares.  This suite is
        the honest record of both. *)
