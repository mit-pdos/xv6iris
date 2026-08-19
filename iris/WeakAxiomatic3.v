(** * WeakAxiomatic3.v — the completeness residue: VIEW DOMINATION

    W4 SLICE 3 of the M6 robustness effort
    ([claude-notes/projects/weak-memory-m6.md]).  Slice 2 ([WeakAxiomatic2.v])
    built the global memory order over OPERATIONS, proved [ob]-acyclicity, and
    landed the replay construction ([cand_reachable]) together with
    completeness for the SC fragment ([sc_cand_reachable]).  Its §9(1) left ONE
    lemma open — VIEW DOMINATION — and stated
    [promise_free_complete] in full checkable form on top of it.

    THIS FILE'S RESULTS:

    (1) THE COMPLETENESS THEOREM.  Every candidate that is
        PUBLICATION-CLEAN ([cand_pub_clean] below) and satisfies
        [cand_axiomatic_ok] is machine-reachable — every stale read allowed,
        which is where all the weak-memory content of completeness lives, and
        a strict generalisation of slice 2's [sc_cand_reachable] (that
        fragment has no stale reads at all).  The proof is the view-domination
        induction §9(1) asked for, one conjunct per view component.

    (2) THE NAMED TOP LEVEL (§14): [srvwmo_consistent] and
        [srvwmo_realizable], with the ppo residue table of the settled
        axiomatization next to them.

    ONE PREMISE, AND WHY IT IS THE ONLY ONE.  A premise here marks a place
    where THE MACHINE IS STRONGER THAN THE MODELLED [ppo] — free for
    SOUNDNESS, fatal for COMPLETENESS.  Slice 1 §7(3) and slice 2 §6(b)
    recorded two such seams; both are now closed at the source, and only the
    proof-side residue of the second remains as a hypothesis:

    (a) THE RELEASE/ACQUIRE SEAM — CLOSED BY STRENGTHENING THE MODEL.
        [store_post] raises [w_vRel] on a [.rl] store and [load_vpre] joins
        [w_vRel] on an [.aq] load, so a release store orders every later
        acquire load of the SAME agent with no fence at all.  That pair is
        RVWMO ppo rule 7, and it now IS in the model:
        [WeakAxiomatic2.rel_acq_po] is [ppo_op]'s fifth arm and
        [WeakAxiomatic2.ax_rel_ord] is the ordering axiom it generates (a
        conjunct of [cand_axiomatic_ok]).  §13's witness — agent 1 stores
        byte [y]; agent 0 stores byte [x] with [rl]; agent 0 acquire-loads
        [y] and reads timestamp 0 — used to be machine-blocked yet
        axiomatically consistent, which is what made completeness FALSE and
        forced the old [cand_rl_free] premise; it is now axiomatically
        INCONSISTENT ([ce_rl_true_inconsistent]) and the premise is gone.

    (b) THE FORWARD-BANK SEAM — CLOSED BY WEAKENING THE MACHINE (D-7,
        2026-08-17).  [store_post] used to bank [w_vwNew], and [fwd_view]
        handed that BANKED view to a plain read of the agent's own store,
        whence [w_vrOld] and then, past a [pr,sr] fence, [w_vrNew] — a path
        no single [ord] edge covers ([ord_pw]/[ord_pr] both require [sr],
        the bank's source needs [sw]).  It now banks PARM's dependency-free
        [FwdItem] view [0], so a forwarded plain read contributes
        [max vpre 0 = vpre] and the witness of §15(1) no longer blocks.

        [cand_pub_clean] SURVIVES AS A PROOF-SIDE PREMISE ONLY: the induction
        below uses it at every read (via [cand_pub_clean_pub_r]) to obtain
        [pub_r], and dropping it needs §8's [w_vrOld]/[w_vrNew] conjuncts
        re-proved for a forwarded read, whose contribution is now the
        pre-view rather than its timestamp.  That re-proof is not attempted
        here, so the theorem below is weaker than it now needs to be — not
        wrong.

    Slice 2's definitions are used verbatim; nothing here weakens any of them.
    DEPENDENCY-FREE like its parents: stdpp + [WeakMem] + [WeakAxiomatic] +
    [WeakAxiomatic2].  No [Axiom], no [Admitted].

    ------------------------------------------------------------------------
    THE SHAPE OF THE INDUCTION, AND HOW IT DIFFERS FROM §9(1)'s SKETCH

    §9(1) proposed to dominate the floor by the POSITION [opos] of one
    [ppo_op]-predecessor operation.  That formulation does not survive
    contact: a read operation's [opos] contains its [evpre], and a write below
    that [evpre] need not be [ob]-before it (§6's discussion), so "≤ opos o"
    is not enough to close the cycle.  What the assembly actually needs is the
    conclusion the dominator was a means to, stated directly:

<<
      frdom_b E i k a n  :=  every future step of agent [i] whose [fr] edge at
                             byte [a] points at a write [w] has n < ev_ts w.
>>

    This is closed under [Nat.max], monotone in [k], and is EXACTLY what
    [readable] needs.  It is derived, per component, from the LOCAL axioms:
    [ax_coherence] for the per-byte [coh] conjunct, and [ax_ord] for the
    [w_vrNew] conjunct via an intermediate "there is an [ord] edge from a
    publication ≥ n to every future step" invariant ([ord_dom]).  The
    transitivity worry §9(1) records is real but does NOT force a path
    closure: [fence_between] and [acq_po] are MONOTONE IN THE TARGET, so a
    view value delivered through any chain of fences is still delivered by a
    SINGLE [ord] edge from the original publication.  That is why [ax_ord] —
    a one-edge axiom — suffices, and why [ob]-acyclicity is not needed here at
    all (the [ob]-acyclicity conjunct of [cand_axiomatic_ok] is never used
    below; §6 records that as a finding). *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakAxiomatic WeakAxiomatic2.

Local Open Scope Z_scope.

(* ================================================================== *)
(** * 1. The candidate's own log calculus

    Everything slice 2 proves about [cand_exec] goes through [exec_wf], which
    is precisely what completeness may not assume.  These are the same facts
    for a candidate as DATA: [cd_log] is [tr_msgs] of a prefix, so it grows by
    [es_msg] at each step and by nothing else. *)

Lemma tr_msgs_app (l1 l2 : list estep) :
  tr_msgs (l1 ++ l2) = tr_msgs l1 ++ tr_msgs l2.
Proof. induction l1 as [|s l IH]; [done|]. by rewrite /= IH app_assoc. Qed.

Lemma cd_log_S c k s :
  cd_tr c !! k = Some s → cd_log c (S k) = cd_log c k ++ es_msg s.
Proof.
  intros Hs. rewrite /cd_log (take_S_r _ _ _ Hs) tr_msgs_app /=.
  by rewrite app_nil_r.
Qed.

Lemma cd_log_split c k k' :
  (k ≤ k')%nat → ∃ l, cd_log c k' = cd_log c k ++ l.
Proof.
  intros Hle. exists (tr_msgs (take (k' - k) (drop k (cd_tr c)))).
  rewrite /cd_log -tr_msgs_app take_take_drop.
  by replace (k + (k' - k))%nat with k' by lia.
Qed.

Lemma cd_log_len_le c k k' :
  (k ≤ k')%nat → (length (cd_log c k) ≤ length (cd_log c k'))%nat.
Proof.
  intros Hle. destruct (cd_log_split c k k' Hle) as [l ->].
  rewrite length_app. lia.
Qed.

(** The log at the very end of the candidate. *)
Lemma cd_log_full c : cd_log c (length (cd_tr c)) = tr_msgs (cd_tr c).
Proof. by rewrite /cd_log take_ge. Qed.

(* ================================================================== *)
(** * 2. Truncation: the replay of a prefix IS the prefix of the replay

    The completeness induction has, at stage [n], discharged [mstep_ok] for
    every step BELOW [n] — which by slice 2's [cand_reachable] is exactly
    [exec_wf] of the TRUNCATED candidate.  So the whole of [WeakAxiomatic] and
    [WeakAxiomatic2]'s machinery is available on the prefix, and this section
    is the dictionary between the two executions. *)

Definition ctake (c : cand) (n : nat) : cand := Cand (cd_img c) (take n (cd_tr c)).

Lemma replay_take σ tr n : replay σ (take n tr) = take (S n) (replay σ tr).
Proof.
  revert σ n. induction tr as [|s tr IH]; intros σ n.
  - by destruct n.
  - destruct n as [|n]; [done|]. by rewrite /= IH.
Qed.

Lemma ctake_init c n : cand_init (ctake c n) = cand_init c.
Proof. done. Qed.

Lemma ctake_st c n :
  ex_st (cand_exec (ctake c n)) = take (S n) (ex_st (cand_exec c)).
Proof. rewrite /cand_exec /= -replay_take //. Qed.

Lemma ctake_stt c n k :
  (k ≤ n)%nat → stt (cand_exec (ctake c n)) k = stt (cand_exec c) k.
Proof. intros Hk. rewrite /stt ctake_st lookup_take //. lia. Qed.

Lemma ctake_ews c n k i :
  (k ≤ n)%nat → ews (cand_exec (ctake c n)) k i = ews (cand_exec c) k i.
Proof. intros Hk. by rewrite /ews ctake_stt. Qed.

Lemma ctake_elog c n k :
  (k ≤ n)%nat → elog (cand_exec (ctake c n)) k = elog (cand_exec c) k.
Proof. intros Hk. by rewrite /elog ctake_stt. Qed.

Lemma ctake_ev_ts c n k :
  (k ≤ n)%nat →
  ev_ts (cand_exec (ctake c n)) (ev_at k) = ev_ts (cand_exec c) (ev_at k).
Proof. intros Hk. by rewrite !ev_ts_at ctake_elog. Qed.

Lemma ctake_tr c n k :
  (k < n)%nat → ex_tr (cand_exec (ctake c n)) !! k = cd_tr c !! k.
Proof. intros Hk. rewrite /= lookup_take //. Qed.

Lemma ctake_tr_len c n :
  (n ≤ length (cd_tr c))%nat → length (ex_tr (cand_exec (ctake c n))) = n.
Proof. intros Hn. rewrite /= length_take. lia. Qed.

Lemma ctake_img c n : ex_img (cand_exec (ctake c n)) = ex_img (cand_exec c).
Proof.
  rewrite /ex_img /eimg !ctake_stt; [lia|]. done.
Qed.

Lemma cand_ex_log c : ex_log (cand_exec c) = cd_log c (length (cd_tr c)).
Proof. rewrite /ex_log (cand_elog c (length (cd_tr c))) //. Qed.

Lemma cand_ex_tr c : ex_tr (cand_exec c) = cd_tr c.
Proof. done. Qed.

Lemma cand_ex_img c : ex_img (cand_exec c) = cd_img c.
Proof. rewrite /ex_img (cand_eimg c 0%nat ltac:(lia)) //. Qed.

Lemma ctake_ex_log c n :
  (n ≤ length (cd_tr c))%nat → ex_log (cand_exec (ctake c n)) = cd_log c n.
Proof.
  intros Hn. rewrite cand_ex_log /cd_log /= take_take.
  rewrite (ctake_tr_len c n Hn) /=. by replace (n `min` n)%nat with n by lia.
Qed.

(** The final logs of the two executions are related by an append, which is
    what makes [ev_writes] — the one relation stated over the FINAL log —
    transfer. *)
Lemma ctake_log_split c n :
  (n ≤ length (cd_tr c))%nat →
  ∃ l, ex_log (cand_exec c) = ex_log (cand_exec (ctake c n)) ++ l.
Proof.
  intros Hn. rewrite (ctake_ex_log c n Hn) cand_ex_log.
  by apply cd_log_split.
Qed.

(* ================================================================== *)
(** * 3. Write events of a candidate, without [exec_wf]

    [WeakAxiomatic]'s [ts_writer] / [ev_ts_inj] / [exec_msg_at] are all stated
    under [exec_wf].  Completeness may not assume it, so here they are again
    for a candidate as data: the message a step appends is a function of the
    step, and [cd_log] grows by exactly that. *)

Definition es_wmsg (s : estep) : option wmsg :=
  match lb_wr (es_lb s) with
  | Some (base, vs) => Some (WMsg base vs (Some (es_ag s)) (lb_cls (es_lb s)))
  | None => None
  end.

Lemma es_msg_wmsg s :
  es_msg s = match es_wmsg s with Some m => [m] | None => [] end.
Proof. rewrite /es_msg /es_wmsg. by destruct (lb_wr (es_lb s)) as [[??]|]. Qed.

Lemma es_wmsg_is_w s m : es_wmsg s = Some m → lb_is_w (es_lb s) = true.
Proof.
  rewrite /es_wmsg. destruct (lb_wr (es_lb s)) as [[b v]|] eqn:Hw; [|done].
  intros _. by eapply lb_wr_is_w.
Qed.

Lemma es_wmsg_none s : es_wmsg s = None → lb_is_w (es_lb s) = false.
Proof. rewrite /es_wmsg. by destruct (es_lb s). Qed.

(** The timestamp of step [k], read off the candidate. *)
Lemma cand_ev_ts c k :
  (k ≤ length (cd_tr c))%nat →
  ev_ts (cand_exec c) (ev_at k) = S (length (cd_log c k)).
Proof. intros Hk. by rewrite ev_ts_at (cand_elog c k Hk). Qed.

Lemma cand_ts_len c k s m :
  cd_tr c !! k = Some s → es_wmsg s = Some m →
  ev_ts (cand_exec c) (ev_at k) = length (cd_log c (S k)).
Proof.
  intros Hs Hm. pose proof (lookup_lt_Some _ _ _ Hs) as Hk.
  rewrite (cand_ev_ts c k ltac:(lia)) (cd_log_S c k s Hs) es_msg_wmsg Hm.
  rewrite length_app /=. lia.
Qed.

(** A write step's message sits at its own timestamp in every later log. *)
Lemma cand_log_byte_wr c k s m k' a :
  cd_tr c !! k = Some s → es_wmsg s = Some m → (S k ≤ k')%nat →
  log_byte (cd_img c) (cd_log c k') (ev_ts (cand_exec c) (ev_at k)) a
  = msg_byte m a.
Proof.
  intros Hs Hm Hk'. pose proof (lookup_lt_Some _ _ _ Hs) as Hk.
  rewrite (cand_ev_ts c k ltac:(lia)) log_byte_S.
  destruct (cd_log_split c (S k) k' Hk') as [l Hl].
  rewrite Hl (cd_log_S c k s Hs) es_msg_wmsg Hm -app_assoc.
  rewrite lookup_app_r; [lia|]. by rewrite Nat.sub_diag /=.
Qed.

Lemma cand_wr_b c k s m a :
  cd_tr c !! k = Some s → es_wmsg s = Some m → is_Some (msg_byte m a) →
  wr_b (cand_exec c) a (ev_at k).
Proof.
  intros Hs Hm Hb. pose proof (lookup_lt_Some _ _ _ Hs) as Hk.
  split.
  - exists s. split; [exact Hs|by eapply es_wmsg_is_w].
  - rewrite /ev_writes cand_ex_img cand_ex_log
            (cand_log_byte_wr c k s m (length (cd_tr c)) a Hs Hm ltac:(lia)).
    exact Hb.
Qed.

Lemma cand_wr_b_inv c a e :
  wr_b (cand_exec c) a e →
  (e = ev_init ∧ is_Some (cd_img c a)) ∨
  ∃ k s m, e = ev_at k ∧ cd_tr c !! k = Some s ∧ es_wmsg s = Some m ∧
           is_Some (msg_byte m a).
Proof.
  intros [HW Hwr]. destruct e as [|k].
  - left. split; [done|].
    rewrite /ev_writes /= cand_ex_img in Hwr.
    exact Hwr.
  - destruct HW as (s & Hs & Hw). rewrite cand_ex_tr in Hs.
    pose proof (lookup_lt_Some _ _ _ Hs) as Hk.
    right. destruct (es_wmsg s) as [m|] eqn:Hm; last first.
    { by rewrite (es_wmsg_none s Hm) in Hw. }
    exists k, s, m. split_and!; [done|done|done|].
    assert (Hk' : (S k ≤ length (cd_tr c))%nat) by lia.
    rewrite /ev_writes cand_ex_img cand_ex_log
            (cand_log_byte_wr c k s m (length (cd_tr c)) a Hs Hm Hk') in Hwr.
    exact Hwr.
Qed.

(** Timestamps of write steps increase strictly with execution position. *)
Lemma cand_ts_le_log c k1 k2 s1 m1 :
  cd_tr c !! k1 = Some s1 → es_wmsg s1 = Some m1 → (k1 < k2)%nat →
  (ev_ts (cand_exec c) (ev_at k1) ≤ length (cd_log c k2))%nat.
Proof.
  intros Hs Hm Hlt. rewrite (cand_ts_len c k1 s1 m1 Hs Hm).
  apply cd_log_len_le. lia.
Qed.

Lemma cand_ts_mono c k1 k2 s1 m1 :
  cd_tr c !! k1 = Some s1 → es_wmsg s1 = Some m1 → (k1 < k2)%nat →
  (k2 ≤ length (cd_tr c))%nat →
  (ev_ts (cand_exec c) (ev_at k1) < ev_ts (cand_exec c) (ev_at k2))%nat.
Proof.
  intros Hs Hm Hlt Hk2. rewrite (cand_ev_ts c k2 Hk2).
  pose proof (cand_ts_le_log c k1 k2 s1 m1 Hs Hm Hlt). lia.
Qed.

Lemma cand_ts_inj c e1 e2 :
  wr_b (cand_exec c) e1.1 e1.2 → wr_b (cand_exec c) e2.1 e2.2 →
  ev_ts (cand_exec c) e1.2 = ev_ts (cand_exec c) e2.2 → e1.2 = e2.2.
Proof.
  destruct e1 as [a1 f1], e2 as [a2 f2]. simpl.
  intros Hw1 Hw2 Hts.
  destruct (cand_wr_b_inv c a1 f1 Hw1) as [[-> _]|(k1 & s1 & m1 & -> & Hs1 & Hm1 & _)];
    destruct (cand_wr_b_inv c a2 f2 Hw2) as [[-> _]|(k2 & s2 & m2 & -> & Hs2 & Hm2 & _)];
    [done| | |].
  - pose proof (lookup_lt_Some _ _ _ Hs2) as Hk2.
    rewrite (cand_ev_ts c k2 ltac:(lia)) /= in Hts. lia.
  - pose proof (lookup_lt_Some _ _ _ Hs1) as Hk1.
    rewrite (cand_ev_ts c k1 ltac:(lia)) /= in Hts. lia.
  - pose proof (lookup_lt_Some _ _ _ Hs1) as Hk1.
    pose proof (lookup_lt_Some _ _ _ Hs2) as Hk2.
    destruct (decide (k1 = k2)) as [->|Hne]; [done|exfalso].
    destruct (decide (k1 < k2)%nat) as [Hlt|Hgt].
    + pose proof (cand_ts_mono c k1 k2 s1 m1 Hs1 Hm1 Hlt ltac:(lia)). lia.
    + pose proof (cand_ts_mono c k2 k1 s2 m2 Hs2 Hm2 ltac:(lia) ltac:(lia)). lia.
Qed.

(** Every non-zero timestamp present in a prefix log belongs to a write step
    of that prefix — the candidate-level [ts_writer]. *)
Lemma cand_ts_writer c n t :
  (n ≤ length (cd_tr c))%nat → (0 < t)%nat → (t ≤ length (cd_log c n))%nat →
  ∃ k s m, (k < n)%nat ∧ cd_tr c !! k = Some s ∧ es_wmsg s = Some m ∧
           ev_ts (cand_exec c) (ev_at k) = t.
Proof.
  induction n as [|n IH]; intros Hn Ht Hlen.
  { rewrite /cd_log take_0 /= in Hlen. lia. }
  destruct (lookup_lt_is_Some_2 (cd_tr c) n ltac:(lia)) as [s Hs].
  rewrite (cd_log_S c n s Hs) es_msg_wmsg length_app in Hlen.
  destruct (es_wmsg s) as [m|] eqn:Hm; last first.
  { rewrite /= Nat.add_0_r in Hlen.
    destruct (IH ltac:(lia) Ht Hlen) as (k & s' & m' & ? & ? & ? & ?).
    exists k, s', m'. split_and!; [lia|done|done|done]. }
  rewrite /= in Hlen.
  destruct (decide (t ≤ length (cd_log c n))%nat) as [Hle|Hgt].
  - destruct (IH ltac:(lia) Ht Hle) as (k & s' & m' & ? & ? & ? & ?).
    exists k, s', m'. split_and!; [lia|done|done|done].
  - exists n, s, m. split_and!; [lia|done|done|].
    rewrite (cand_ev_ts c n ltac:(lia)). lia.
Qed.

(** ... hence a write inside a [writes_in] window is a genuine write EVENT
    with its timestamp in that window.  This is the bridge from [readable]'s
    failure to an [fr] edge. *)
Lemma cand_writes_in_wr c n a lo hi :
  (n ≤ length (cd_tr c))%nat → writes_in (cd_log c n) a lo hi →
  ∃ w, wr_b (cand_exec c) a w ∧ (lo < ev_ts (cand_exec c) w)%nat ∧
       (ev_ts (cand_exec c) w ≤ hi)%nat.
Proof.
  intros Hn Hw.
  apply (writes_in_log_byte (cd_img c)) in Hw as (t & Hlo & Hhi & Hs).
  pose proof (log_byte_bounded (cd_img c) (cd_log c n) t a Hs) as Htlen.
  destruct (cand_ts_writer c n t Hn ltac:(lia) Htlen)
    as (k & s & m & Hk & Hs' & Hm & Hts).
  exists (ev_at k). split_and!; [|lia|lia].
  eapply (cand_wr_b c k s m a Hs' Hm).
  rewrite -(cand_log_byte_wr c k s m n a Hs' Hm ltac:(lia)) Hts. exact Hs.
Qed.

(* ================================================================== *)
(** * 4. The domination vocabulary

    Three predicates, one per "stage" a published timestamp passes through in
    the machine:

    - [frdom_b E i k a n] — the CONCLUSION shape: no future step of agent [i]
      has an [fr] edge at byte [a] to a write at or below [n].  This is what
      [readable] needs, and the only shape the final assembly consumes.
    - [ord_dom E i k n] — DELIVERED: some publication ≥ n is [ord]-before
      EVERY future step of agent [i].  Turns into [frdom] by [ax_ord].  This
      is the invariant of [w_vrNew] (and, when [aq], of the load pre-view).
    - [rsrc] / [wsrc] / [relsrc] — PENDING: some read (resp. write, resp.
      RELEASE write) publication ≥ n sits po-before [k] in agent [i].  These
      are the invariants of [w_vrOld], [w_vwOld] and [w_vRel]; a fence with
      the matching pred bit and [sr] promotes the first two to [ord_dom],
      which is exactly [fence_post]'s [v1] join, and an ACQUIRE READ promotes
      the third (RVWMO ppo rule 7 then rule 5 — [relsrc_acq]), which is
      exactly [load_post_at]'s [aq] arm absorbing [load_vpre] into
      [w_vrNew].

    [ord_dom] is stated with the target quantified — that is the technical
    heart: [fence_between] and [acq_po] are monotone in the target, so
    delivery to one future step is delivery to all of them, and the
    "transitive fence delivery" §9(1) warns about never needs a path
    closure. *)

Definition frdom_b (E : exec) (i : agent) (k : nat) (a : Z) (n : nat) : Prop :=
  ∀ k2 s2 w, (k ≤ k2)%nat → ex_tr E !! k2 = Some s2 → es_ag s2 = i →
    fr_b E a (ev_at k2) w → (n < ev_ts E w)%nat.

Definition frdom (E : exec) (i : agent) (k : nat) (n : nat) : Prop :=
  ∀ a, frdom_b E i k a n.

Definition ord_dom (E : exec) (i : agent) (k : nat) (n : nat) : Prop :=
  (n = 0)%nat ∨
  ∀ k2 s2, (k ≤ k2)%nat → ex_tr E !! k2 = Some s2 → es_ag s2 = i →
    ∃ e1 t, (n ≤ t)%nat ∧
      ((ord_pw E e1 (ev_at k2) ∧ pub_w E e1 t) ∨
       (ord_pr E e1 (ev_at k2) ∧ pub_r E e1 t) ∨
       (rel_ord E e1 (ev_at k2) ∧ pub_w E e1 t)).

Definition rsrc (E : exec) (i : agent) (k : nat) (n : nat) : Prop :=
  (n = 0)%nat ∨
  ∃ k1 s1 t, (k1 < k)%nat ∧ ex_tr E !! k1 = Some s1 ∧ es_ag s1 = i ∧
             pub_r E (ev_at k1) t ∧ (n ≤ t)%nat.

Definition wsrc (E : exec) (i : agent) (k : nat) (n : nat) : Prop :=
  (n = 0)%nat ∨
  ∃ k1 s1 t, (k1 < k)%nat ∧ ex_tr E !! k1 = Some s1 ∧ es_ag s1 = i ∧
             pub_w E (ev_at k1) t ∧ (n ≤ t)%nat.

(** [w_vRel]'s invariant: a po-earlier RELEASE write published it. *)
Definition relsrc (E : exec) (i : agent) (k : nat) (n : nat) : Prop :=
  (n = 0)%nat ∨
  ∃ k1 s1 t, (k1 < k)%nat ∧ ex_tr E !! k1 = Some s1 ∧ es_ag s1 = i ∧
             lb_is_w (es_lb s1) = true ∧ lb_rl (es_lb s1) = true ∧
             pub_w E (ev_at k1) t ∧ (n ≤ t)%nat.

(** [w_vrOld]'s invariant: either already delivered, or pending. *)
Definition rdom (E : exec) (i : agent) (k : nat) (n : nat) : Prop :=
  ord_dom E i k n ∨ rsrc E i k n.

(** *** Closure properties *)

Lemma frdom_b_0 E i k a : frdom_b E i k a 0.
Proof.
  intros k2 s2 w _ _ _ ((w0 & _ & (_ & _ & Hlt)) & _). lia.
Qed.

Lemma frdom_0 E i k : frdom E i k 0.
Proof. intros a. apply frdom_b_0. Qed.

Lemma frdom_b_le E i k a n n' :
  (n' ≤ n)%nat → frdom_b E i k a n → frdom_b E i k a n'.
Proof.
  intros Hle Hd k2 s2 w H1 H2 H3 H4. pose proof (Hd k2 s2 w H1 H2 H3 H4). lia.
Qed.

Lemma frdom_b_wk E i k k' a n :
  (k ≤ k')%nat → frdom_b E i k a n → frdom_b E i k' a n.
Proof.
  intros Hle Hd k2 s2 w H1 H2 H3 H4. eapply (Hd k2 s2 w); [lia|done|done|done].
Qed.

Lemma frdom_wk E i k k' n : (k ≤ k')%nat → frdom E i k n → frdom E i k' n.
Proof. intros Hle Hd a. by eapply frdom_b_wk. Qed.

Lemma frdom_b_max E i k a n1 n2 :
  frdom_b E i k a n1 → frdom_b E i k a n2 → frdom_b E i k a (Nat.max n1 n2).
Proof.
  intros H1 H2 k2 s2 w G1 G2 G3 G4.
  pose proof (H1 k2 s2 w G1 G2 G3 G4); pose proof (H2 k2 s2 w G1 G2 G3 G4). lia.
Qed.

Lemma frdom_max E i k n1 n2 :
  frdom E i k n1 → frdom E i k n2 → frdom E i k (Nat.max n1 n2).
Proof. intros H1 H2 a. by apply frdom_b_max. Qed.

Lemma ord_dom_le E i k n n' :
  (n' ≤ n)%nat → ord_dom E i k n → ord_dom E i k n'.
Proof.
  intros Hle [->|Hd]; [left; lia|].
  destruct (decide (n' = 0)%nat) as [->|?]; [by left|]. right.
  intros k2 s2 ???. destruct (Hd k2 s2) as (e1 & t & ? & ?); [done|done|done|].
  exists e1, t. split; [lia|done].
Qed.

Lemma ord_dom_wk E i k k' n :
  (k ≤ k')%nat → ord_dom E i k n → ord_dom E i k' n.
Proof.
  intros Hle [->|Hd]; [by left|]. right. intros k2 s2 ???.
  eapply Hd; [lia|done|done].
Qed.

Lemma ord_dom_max E i k n1 n2 :
  ord_dom E i k n1 → ord_dom E i k n2 → ord_dom E i k (Nat.max n1 n2).
Proof.
  intros H1 H2. destruct (decide (n1 ≤ n2)%nat) as [Hle|Hgt].
  - rewrite (Nat.max_r _ _ Hle) //.
  - rewrite Nat.max_l; [lia|done].
Qed.

Lemma rsrc_le E i k n n' : (n' ≤ n)%nat → rsrc E i k n → rsrc E i k n'.
Proof.
  intros Hle [->|(k1 & s1 & t & ?&?&?&?&?)]; [left; lia|].
  right. exists k1, s1, t. split_and!; [done|done|done|done|lia].
Qed.

Lemma rsrc_wk E i k k' n : (k ≤ k')%nat → rsrc E i k n → rsrc E i k' n.
Proof.
  intros Hle [->|(k1 & s1 & t & ?&?&?&?&?)]; [by left|].
  right. exists k1, s1, t. split_and!; [lia|done|done|done|done].
Qed.

Lemma wsrc_le E i k n n' : (n' ≤ n)%nat → wsrc E i k n → wsrc E i k n'.
Proof.
  intros Hle [->|(k1 & s1 & t & ?&?&?&?&?)]; [left; lia|].
  right. exists k1, s1, t. split_and!; [done|done|done|done|lia].
Qed.

Lemma wsrc_wk E i k k' n : (k ≤ k')%nat → wsrc E i k n → wsrc E i k' n.
Proof.
  intros Hle [->|(k1 & s1 & t & ?&?&?&?&?)]; [by left|].
  right. exists k1, s1, t. split_and!; [lia|done|done|done|done].
Qed.

Lemma wsrc_max E i k n1 n2 :
  wsrc E i k n1 → wsrc E i k n2 → wsrc E i k (Nat.max n1 n2).
Proof.
  intros H1 H2. destruct (decide (n1 ≤ n2)%nat) as [Hle|Hgt].
  - rewrite (Nat.max_r _ _ Hle) //.
  - rewrite Nat.max_l; [lia|done].
Qed.

Lemma relsrc_le E i k n n' : (n' ≤ n)%nat → relsrc E i k n → relsrc E i k n'.
Proof.
  intros Hle [->|(k1 & s1 & t & ?&?&?&?&?&?&?)]; [left; lia|].
  right. exists k1, s1, t. split_and!; [done|done|done|done|done|done|lia].
Qed.

Lemma relsrc_wk E i k k' n : (k ≤ k')%nat → relsrc E i k n → relsrc E i k' n.
Proof.
  intros Hle [->|(k1 & s1 & t & ?&?&?&?&?&?&?)]; [by left|].
  right. exists k1, s1, t. split_and!; [lia|done|done|done|done|done|done].
Qed.

Lemma relsrc_max E i k n1 n2 :
  relsrc E i k n1 → relsrc E i k n2 → relsrc E i k (Nat.max n1 n2).
Proof.
  intros H1 H2. destruct (decide (n1 ≤ n2)%nat) as [Hle|Hgt].
  - rewrite (Nat.max_r _ _ Hle) //.
  - rewrite Nat.max_l; [lia|done].
Qed.

Lemma rdom_le E i k n n' : (n' ≤ n)%nat → rdom E i k n → rdom E i k n'.
Proof.
  intros Hle [H|H]; [left; by eapply ord_dom_le|right; by eapply rsrc_le].
Qed.

Lemma rdom_wk E i k k' n : (k ≤ k')%nat → rdom E i k n → rdom E i k' n.
Proof.
  intros Hle [H|H]; [left; by eapply ord_dom_wk|right; by eapply rsrc_wk].
Qed.

Lemma rdom_max E i k n1 n2 :
  rdom E i k n1 → rdom E i k n2 → rdom E i k (Nat.max n1 n2).
Proof.
  intros H1 H2. destruct (decide (n1 ≤ n2)%nat) as [Hle|Hgt].
  - rewrite (Nat.max_r _ _ Hle) //.
  - rewrite Nat.max_l; [lia|done].
Qed.

(** *** The two derivations: delivery becomes domination, pending becomes
    delivery. *)

(** [ax_ord] — the LOCAL ordering axiom — is exactly the step from "an [ord]
    edge carries a publication ≥ n" to "no [fr] successor sits at or below
    n". *)
Lemma ord_dom_frdom E i k n :
  ax_ord E → ax_rel_ord E → ord_dom E i k n → frdom E i k n.
Proof.
  intros Hax Hrax [->|Hd] a; [apply frdom_b_0|].
  intros k2 s2 w Hk Hs2 Hag Hfr.
  destruct (Hd k2 s2 Hk Hs2 Hag) as (e1 & t & Hle & Hcase).
  destruct Hcase as [Hc|[Hc|[Hro Hpub]]].
  - pose proof (Hax e1 k2 s2 a w t Hs2 (or_introl Hc) Hfr). lia.
  - pose proof (Hax e1 k2 s2 a w t Hs2 (or_intror Hc) Hfr). lia.
  - pose proof (Hrax e1 k2 s2 a w t Hs2 Hro Hpub Hfr). lia.
Qed.

(** A [pr,sr] fence promotes a pending READ publication to a delivered one:
    the fence sits strictly between the source and every later step, which is
    literally [fence_between]. *)
Lemma rsrc_fence E i kf sf pw sw n :
  ex_tr E !! kf = Some sf → es_ag sf = i →
  es_lb sf = LFence true pw true sw →
  rsrc E i kf n → ord_dom E i (S kf) n.
Proof.
  intros Hsf Hag Hlf [->|(k1 & s1 & t & Hlt & Hs1 & Hag1 & Hpub & Hle)];
    [by left|].
  right. intros k2 s2 Hk2 Hs2 Hag2. exists (ev_at k1), t. split; [exact Hle|].
  right; left. split; [|exact Hpub]. left.
  exists k1, k2, pw, sw. split_and!; [done|done|].
  exists kf, sf, s1, s2.
  split_and!; [lia|lia|done|done|done|congruence|congruence|done].
Qed.

(** ... and a [pw,sr] fence does the same for a pending WRITE publication. *)
Lemma wsrc_fence E i kf sf pr sw n :
  ex_tr E !! kf = Some sf → es_ag sf = i →
  es_lb sf = LFence pr true true sw →
  wsrc E i kf n → ord_dom E i (S kf) n.
Proof.
  intros Hsf Hag Hlf [->|(k1 & s1 & t & Hlt & Hs1 & Hag1 & Hpub & Hle)];
    [by left|].
  right. intros k2 s2 Hk2 Hs2 Hag2. exists (ev_at k1), t. split; [exact Hle|].
  left. split; [|exact Hpub].
  exists k1, k2, pr, sw. split_and!; [done|done|].
  exists kf, sf, s1, s2.
  split_and!; [lia|lia|done|done|done|congruence|congruence|done].
Qed.

(** An ACQUIRE read delivers its own publication with no fence at all
    ([acq_po]). *)
Lemma acq_ord_dom E i k1 s1 t :
  ex_tr E !! k1 = Some s1 → es_ag s1 = i →
  lb_is_r (es_lb s1) = true → lb_aq (es_lb s1) = true →
  pub_r E (ev_at k1) t → ord_dom E i (S k1) t.
Proof.
  intros Hs1 Hag Hisr Haq Hpub. right. intros k2 s2 Hk2 Hs2 Hag2.
  exists (ev_at k1), t. split; [lia|]. right; left. split; [|exact Hpub].
  right. exists k1, k2, s1, s2. split_and!; [done|done|lia|done|done| |done|done].
  congruence.
Qed.

(** An ACQUIRE READ promotes a pending RELEASE publication to a delivered one:
    RVWMO ppo rule 7 puts the release write before the acquire read, rule 5
    ([acq_po]) puts the acquire read before every later step, and
    [WeakAxiomatic2.rel_ord] is exactly that two-edge chain.  On the machine
    it is [load_post_at]'s [aq] arm: the acquire absorbs [load_vpre] — and
    hence [w_vRel] — into [w_vrNew], from where it is monotone forever.
    The read must actually READ a byte; an empty acquire load moves no view,
    and correspondingly builds no [rel_ord] edge. *)
Lemma relsrc_acq E i k s n :
  ex_tr E !! k = Some s → es_ag s = i →
  lb_is_r (es_lb s) = true → lb_aq (es_lb s) = true →
  (∃ a, rd_b E a (ev_at k)) →
  relsrc E i k n → ord_dom E i (S k) n.
Proof.
  intros Hs Hag Hisr Haq Hrd
         [->|(k1 & s1 & t & Hlt & Hs1 & Hag1 & Hw1 & Hrl1 & Hpub & Hle)];
    [by left|].
  right. intros k2 s2 Hk2 Hs2 Hag2. exists (ev_at k1), t. split; [exact Hle|].
  right; right. split; [|exact Hpub]. right. exists (ev_at k). split_and!.
  - exists k1, k, s1, s.
    split_and!; [done|done|lia|done|done|congruence|done|done|done|done].
  - exact Hrd.
  - exists k, k2, s, s2.
    split_and!; [done|done|lia|done|done|congruence|done|done].
Qed.

(** The same promotion AT the acquire read itself — where the value is still
    in [w_vRel] and only [load_vpre] joins it, so there is no [ord_dom] to
    state and the [fr] bound is read straight off [ax_rel_ord]. *)
Lemma relsrc_frdom_at E i k s n :
  ax_rel_ord E → ex_tr E !! k = Some s → es_ag s = i →
  lb_is_r (es_lb s) = true → lb_aq (es_lb s) = true →
  relsrc E i k n → ∀ a w, fr_b E a (ev_at k) w → (n < ev_ts E w)%nat.
Proof.
  intros Hax Hs Hag Hisr Haq
         [->|(k1 & s1 & t & Hlt & Hs1 & Hag1 & Hw1 & Hrl1 & Hpub & Hle)] a w Hfr.
  - destruct Hfr as ((w0 & _ & (_ & _ & Hlt0)) & _). lia.
  - assert (Hra : rel_acq_po E (ev_at k1) (ev_at k)).
    { exists k1, k, s1, s.
      split_and!; [done|done|lia|done|done|congruence|done|done|done|done]. }
    pose proof (Hax (ev_at k1) k s a w t Hs (or_introl Hra) Hpub Hfr). lia.
Qed.

(* ================================================================== *)
(** * 5. Upper bounds for the step functions — LIFTED

    [maxcl] and the whole family of upper-bound fold lemmas this section used
    to prove locally ([coh_load_post_at_eq]/[_ne], [coh_store_post_eq]/[_ne],
    [load_fold_vwOld] / [load_fold_vRel] / [load_fold_vrNew_plain],
    [load_fold_coh] / [load_fold_vrOld] / [load_fold_vrNew],
    [store_fold_vrOld] / [store_fold_vrNew] / [store_fold_vRel_norl] /
    [store_fold_vwOld] / [store_fold_coh], and [fence_post_vrNew_pred]) now
    live in [WeakMem.v] next to [ws_bounded]'s preservation lemmas — the W4
    lift batch, exactly as this file's §15(3) asked.  Nothing is restated
    here; the uses below are against [WeakMem]'s copies.

    ONE addition owes the same lift: the release channel's upper bound.
    [store_fold_vRel_norl] (in [WeakMem]) says a non-release store leaves
    [w_vRel] alone; this is its [.rl] companion, in [store_fold_vwOld]'s
    conditional shape.  It belongs next to that one and is proved here only
    because this slice may not edit [WeakMem.v]. *)

Lemma store_fold_vRel P rl t as_ ws :
  maxcl P → P (w_vRel ws) → (rl = true → P t) →
  P (w_vRel (foldl (λ w a, store_post w rl a t) ws as_)).
Proof.
  intros Hcl. revert ws. induction as_ as [|a l IH]; intros ws Hc Ht; [exact Hc|].
  simpl. apply IH; [|exact Ht]. rewrite /store_post /=.
  destruct rl; [|exact Hc]. apply maxcl_max; [done|exact Hc|by apply Ht].
Qed.

(* ================================================================== *)
(** * 6. The one remaining premise, and the state calculus

    [cand_pub_clean] is the last side condition of the completeness theorem.
    It is stated over the candidate's own data and relations — no machine
    notion — so it is a checkable hypothesis of the same kind as
    [cand_axiomatic_ok].  (Its predecessor [cand_rl_free] is GONE: the model
    now carries RVWMO ppo rule 7 as [WeakAxiomatic2.rel_acq_po] /
    [ax_rel_ord], so a release store is an ordering source rather than an
    excluded shape — see §13.) *)

(** Every byte read is ACQUIRE or EXTERNALLY sourced — i.e. exactly the side
    condition of [pub_r], per byte.  Equivalently: no read is forwarded from
    the reader's own store, which is what keeps the banked [w_vwNew] out of
    every view component. *)
Definition cand_pub_clean (c : cand) : Prop :=
  ∀ k s a t v, cd_tr c !! k = Some s → reads_at (cand_exec c) k a t v →
    lb_aq (es_lb s) = true ∨
    ∃ w, rf_b (cand_exec c) a w (ev_at k) ∧ ext_w (cand_exec c) w (es_ag s).

Lemma cand_pub_clean_pub_r c k s a t v :
  cand_pub_clean c → cd_tr c !! k = Some s → reads_at (cand_exec c) k a t v →
  pub_r (cand_exec c) (ev_at k) t.
Proof.
  intros Hpc Hs Hr. exists k, s, a, v. split_and!; [done|done|done|].
  by eapply Hpc.
Qed.

(** *** How one step moves the per-agent state *)

Lemma cand_ws_ne c k s i :
  cd_tr c !! k = Some s → i ≠ es_ag s →
  ews (cand_exec c) (S k) i = ews (cand_exec c) k i.
Proof.
  intros Hs Hne. rewrite /ews (cand_next c k s Hs) (mnext_ws_ne _ _ _ i Hne) //.
Qed.

Lemma cand_ws_load c k s aq base ts vs :
  cd_tr c !! k = Some s → es_lb s = LLoad aq base ts vs →
  ews (cand_exec c) (S k) (es_ag s)
  = load_post_run (ews (cand_exec c) k (es_ag s)) aq base ts.
Proof. intros Hs Hl. rewrite /ews (cand_next c k s Hs) Hl /= upd_ws_eq //. Qed.

Lemma cand_ws_store c k s rl base vs kc :
  cd_tr c !! k = Some s → es_lb s = LStore rl base vs kc →
  ews (cand_exec c) (S k) (es_ag s)
  = store_post_run (ews (cand_exec c) k (es_ag s)) rl base (length vs)
      (ev_ts (cand_exec c) (ev_at k)).
Proof. intros Hs Hl. rewrite /ews (cand_next c k s Hs) Hl /= upd_ws_eq //. Qed.

Lemma cand_ws_fence c k s pr pw sr sw :
  cd_tr c !! k = Some s → es_lb s = LFence pr pw sr sw →
  ews (cand_exec c) (S k) (es_ag s)
  = fence_post (ews (cand_exec c) k (es_ag s)) pr pw sr sw.
Proof. intros Hs Hl. rewrite /ews (cand_next c k s Hs) Hl /= upd_ws_eq //. Qed.

Lemma cand_ws_rmw c k s aq rl base ts rvs wvs kc :
  cd_tr c !! k = Some s → es_lb s = LRmw aq rl base ts rvs wvs kc →
  ews (cand_exec c) (S k) (es_ag s)
  = store_post_run (load_post_run (ews (cand_exec c) k (es_ag s)) aq base ts)
      rl base (length wvs) (ev_ts (cand_exec c) (ev_at k)).
Proof. intros Hs Hl. rewrite /ews (cand_next c k s Hs) Hl /= upd_ws_eq //. Qed.

Lemma cand_stt_init c : stt (cand_exec c) 0%nat = cand_init c.
Proof.
  apply stt_lookup. change (ex_st (cand_exec c)) with (replay (cand_init c) (cd_tr c)).
  apply replay_0.
Qed.

Lemma cand_ws_init c i : ews (cand_exec c) 0%nat i = ws_init.
Proof. rewrite /ews cand_stt_init //. Qed.

(** *** The byte/timestamp pairs a multi-byte access folds over *)

Lemma elem_of_zip_seq (base : Z) (ts : list nat) p :
  p ∈ zip_with (λ j t, (base + Z.of_nat j, t)) (seq 0 (length ts)) ts →
  ∃ j : nat, ts !! j = Some p.2 ∧ p.1 = acc_addr base j.
Proof.
  intros Hin. apply elem_of_list_lookup in Hin as [j Hj].
  rewrite lookup_zip_with in Hj.
  destruct (seq 0 (length ts) !! j) as [x|] eqn:Hx; [|done].
  destruct (ts !! j) as [t|] eqn:Ht; [|done]. simpl in Hj. simplify_eq/=.
  apply lookup_seq in Hx as [-> _]. exists j. by rewrite /acc_addr.
Qed.

Lemma elem_of_map_seq (base : Z) (n : nat) (a : Z) :
  a ∈ map (λ j : nat, base + Z.of_nat j) (seq 0 n) →
  ∃ j : nat, (j < n)%nat ∧ a = acc_addr base j.
Proof.
  intros Hin. apply elem_of_list_fmap in Hin as (j & -> & Hj).
  apply elem_of_seq in Hj. exists j. split; [lia|by rewrite /acc_addr].
Qed.

(** *** [wr_b] for the virtual init event, and transfer to a truncation *)

Lemma cand_wr_b_init c a :
  is_Some (cd_img c a) → wr_b (cand_exec c) a ev_init.
Proof. intros Hs. split; [done|]. rewrite /ev_writes /= cand_ex_img //. Qed.

Lemma ctake_reads_at c n k a t v :
  (k < n)%nat → reads_at (cand_exec c) k a t v →
  reads_at (cand_exec (ctake c n)) k a t v.
Proof.
  intros Hk (s & base & ts & vs & j & Hs & Hrd & Hj & Hv & Ha).
  exists s, base, ts, vs, j. split_and!; [|done|done|done|done].
  rewrite (ctake_tr c n k Hk). by rewrite cand_ex_tr in Hs.
Qed.

Lemma ctake_wr_b c n a k :
  (k < n)%nat → wr_b (cand_exec c) a (ev_at k) →
  wr_b (cand_exec (ctake c n)) a (ev_at k).
Proof.
  intros Hk Hw.
  destruct (cand_wr_b_inv c a (ev_at k) Hw)
    as [[Habs _]|(k' & s & m & Heq & Hs & Hm & Hb)]; [done|].
  assert (k' = k) as -> by (by simplify_eq).
  apply (cand_wr_b (ctake c n) k s m a); [|exact Hm|exact Hb].
  rewrite /ctake /= lookup_take //.
Qed.

Lemma ctake_wr_b_init c n a :
  wr_b (cand_exec c) a ev_init → wr_b (cand_exec (ctake c n)) a ev_init.
Proof.
  intros Hw.
  destruct (cand_wr_b_inv c a ev_init Hw) as [[_ Hs]|(?&?&?&Habs&_)]; [|done].
  by apply cand_wr_b_init.
Qed.

(* ================================================================== *)
(** * 7. The coherence conjunct: a touched byte's timestamp dominates

    The [coh] component is justified by [ax_coherence] alone: if a future step
    of the same agent had an [fr] edge at byte [a] to a write AT OR BELOW a
    timestamp this agent already touched at [a], the four per-byte relations
    close a cycle — [po_loc] to the future step, [fr] to the write, then [co]
    and/or [rf] back.  This is the [coh] half of view domination. *)

Section candidate.
Context (c : cand).
Local Notation E := (cand_exec c).
Context (Hval : cand_values c).
Context (Hrft : ax_rf_total E).
Context (Hcohax : ax_coherence E).
Context (Hordax : ax_ord E).
Context (Hrelax : ax_rel_ord E).

Lemma cand_read_ts_le k a t v :
  reads_at E k a t v → (t ≤ length (cd_log c k))%nat.
Proof.
  intros (s & base & ts & vs & j & Hs & Hrd & Hj & Hv & ->).
  rewrite cand_ex_tr in Hs.
  pose proof (Hval k s base ts vs Hs Hrd j t v Hj Hv) as Hlb.
  apply (log_byte_bounded (cd_img c) (cd_log c k) t (acc_addr base j)).
  by eexists.
Qed.

(** A write whose timestamp is already in the log at step [k] is a step
    strictly before [k]. *)
Lemma cand_wr_lt k a k' :
  wr_b E a (ev_at k') →
  (ev_ts E (ev_at k') ≤ length (cd_log c k))%nat → (k' < k)%nat.
Proof.
  intros Hw Hle.
  destruct (cand_wr_b_inv c a (ev_at k') Hw)
    as [[Habs _]|(k'' & s & m & Heq & Hs & Hm & _)]; [done|].
  assert (k'' = k') as -> by (by simplify_eq).
  pose proof (lookup_lt_Some _ _ _ Hs) as Hk'.
  destruct (decide (k' < k)%nat) as [?|Hge]; [done|exfalso].
  rewrite (cand_ev_ts c k' ltac:(lia)) in Hle.
  pose proof (cd_log_len_le c k k' ltac:(lia)). lia.
Qed.

Lemma touch_frdom k1 s1 a t1 :
  cd_tr c !! k1 = Some s1 →
  ((∃ v, reads_at E k1 a t1 v) ∨
   (wr_b E a (ev_at k1) ∧ t1 = ev_ts E (ev_at k1))) →
  frdom_b E (es_ag s1) (S k1) a t1.
Proof.
  intros Hs1 Htouch k2 s2 w Hk Hs2 Hag Hfr.
  destruct (decide (t1 < ev_ts E w)%nat) as [?|Hge]; [done|exfalso].
  pose proof Hfr as Hfr'.
  destruct Hfr' as ((w0 & Hrf0 & Hco0) & Hne).
  pose proof Hco0 as (Hw0 & Hw & Hlt0).
  (* the future step reads [a], the earlier one accesses it *)
  assert (Hacc2 : acc_b E a (ev_at k2)).
  { right. destruct Hrf0 as (_ & k & t & v & Hkeq & Hr & _).
    exists k, t, v. by split. }
  assert (Hacc1 : acc_b E a (ev_at k1)).
  { destruct Htouch as [[v1 Hr1]|[Hw1 _]]; [right; by exists k1, t1, v1|by left]. }
  assert (Hpl : po_loc_b E a (ev_at k1) (ev_at k2)).
  { split; [|by split].
    exists k1, k2, s1, s2. split_and!; [done|done|lia| |done|congruence].
    by rewrite cand_ex_tr. }
  apply (Hcohax a (ev_at k1)).
  eapply tc_l with (ev_at k2); [by left|].
  destruct Htouch as [[v1 Hr1]|[Hw1 Ht1]].
  - (* the earlier access READ [a] at [t1] *)
    destruct (Hrft k1 a t1 v1 Hr1) as [w1 Hrf1].
    assert (Hts1 : ev_ts E w1 = t1).
    { destruct Hrf1 as (_ & k & t & v & Hkeq & Hr & Hts).
      assert (k = k1) as -> by (by simplify_eq).
      destruct (reads_at_det E k1 a t v t1 v1 Hr Hr1) as [-> _]. exact Hts. }
    destruct (decide (ev_ts E w = t1)) as [Heq|Hne'].
    + (* [w] IS the source the earlier read took *)
      eapply tc_l with w; [by right; right; right|].
      apply tc_once. right; left. split; [exact Hw|].
      exists k1, t1, v1. by split_and!.
    + eapply tc_l with w; [by right; right; right|].
      eapply tc_l with w1; [right; right; left|].
      { split_and!; [exact Hw|exact (proj1 Hrf1)|lia]. }
      apply tc_once. by right; left.
  - (* the earlier access WROTE [a] at its own timestamp *)
    destruct (decide (ev_ts E w = ev_ts E (ev_at k1))) as [Heq|Hne'].
    + assert (w = ev_at k1) as ->.
      { exact (cand_ts_inj c (a, w) (a, ev_at k1) Hw Hw1 Heq). }
      apply tc_once. by right; right; right.
    + eapply tc_l with w; [by right; right; right|].
      apply tc_once. right; right; left.
      split_and!; [exact Hw|exact Hw1|lia].
Qed.

(* ================================================================== *)
(** * 8. THE VIEW-DOMINATION INVARIANT

    One conjunct per view component, in the shape §4 fixed.  [w_vwNew] and the
    forward bank carry NO conjunct: under [cand_pub_clean] the bank is never
    consulted ([fwd_view] is the identity on every timestamp actually read),
    so no banked view ever reaches a floor — which is precisely the leak the
    premise closes.  (Post-D-7 the bank holds [0], so a consulted bank would
    contribute nothing either; the premise is belt-and-braces here — see the
    header's (b').) *)

Definition invw (k : nat) (i : agent) (ws : wstate) : Prop :=
  (∀ a, frdom_b E i k a (coh ws a)) ∧
  ord_dom E i k (w_vrNew ws) ∧
  rdom E i k (w_vrOld ws) ∧
  wsrc E i k (w_vwOld ws) ∧
  relsrc E i k (w_vRel ws).

Definition inv (k : nat) (i : agent) : Prop := invw k i (ews E k i).

Lemma invw_wk k k' i ws : (k ≤ k')%nat → invw k i ws → invw k' i ws.
Proof.
  intros Hle (Hc & Hrn & Hro & Hwo & Hrel). split_and!.
  - intros a. by eapply frdom_b_wk.
  - by eapply ord_dom_wk.
  - by eapply rdom_wk.
  - by eapply wsrc_wk.
  - by eapply relsrc_wk.
Qed.

Lemma maxcl_frdom_b i k a : maxcl (frdom_b E i k a).
Proof. split; [apply frdom_b_0|intros ??; apply frdom_b_max]. Qed.
Lemma maxcl_ord_dom i k : maxcl (ord_dom E i k).
Proof. split; [by left|intros ??; apply ord_dom_max]. Qed.
Lemma maxcl_rdom i k : maxcl (rdom E i k).
Proof. split; [left; by left|intros ??; apply rdom_max]. Qed.
Lemma maxcl_wsrc i k : maxcl (wsrc E i k).
Proof. split; [by left|intros ??; apply wsrc_max]. Qed.
Lemma maxcl_relsrc i k : maxcl (relsrc E i k).
Proof. split; [by left|intros ??; apply relsrc_max]. Qed.

(** The value a read of byte [acc_addr base j] returns. *)
Lemma cand_read_of k s base ts vs (j : nat) t :
  cd_tr c !! k = Some s → lb_rd (es_lb s) = Some (base, ts, vs) →
  length vs = length ts → ts !! j = Some t →
  ∃ v, reads_at E k (acc_addr base j) t v.
Proof.
  intros Hs Hrd Hlen Hj.
  destruct (lookup_lt_is_Some_2 vs j) as [v Hv].
  { rewrite Hlen. by eapply lookup_lt_Some. }
  exists v, s, base, ts, vs, j. split_and!; [|done|done|done|done].
  by rewrite cand_ex_tr.
Qed.

Lemma msg_byte_in_range base vs tid k (j : nat) :
  (j < length vs)%nat →
  is_Some (msg_byte (WMsg base vs tid k) (acc_addr base j)).
Proof.
  intros Hj. rewrite /msg_byte /= bool_decide_eq_true_2; [rewrite /acc_addr; lia|].
  replace (Z.to_nat (acc_addr base j - base)) with j by (rewrite /acc_addr; lia).
  by apply lookup_lt_is_Some_2.
Qed.

(** *** The load arm *)

Lemma inv_load_fold k s base ts vs aq i :
  cand_pub_clean c →
  cd_tr c !! k = Some s → es_ag s = i →
  lb_rd (es_lb s) = Some (base, ts, vs) → length vs = length ts →
  lb_aq (es_lb s) = aq →
  (∀ a t v, reads_at E k a t v → fwd_view (ews E k i) aq a t = t) →
  inv k i →
  invw (S k) i (load_post_run (ews E k i) aq base ts).
Proof.
  intros Hpc Hs Hag Hrd Hlen Haq Hnf Hinv.
  pose proof Hinv as (Hc & Hrn & Hro & Hwo & Hrel).
  set (ws := ews E k i).
  (* AN EMPTY READ MOVES NOTHING — and builds no [rel_ord] edge either, which
     is why the release delivery below may assume the load reads a byte. *)
  destruct (decide (ts = [])) as [->|Hnil].
  { assert (load_post_run ws aq base [] = ws) as ->
      by rewrite /load_post_run /load_post_bytes //.
    eapply invw_wk; [|exact Hinv]. lia. }
  set (ats := zip_with (λ (j : nat) (t : nat), (base + Z.of_nat j, t))
                       (seq 0 (length ts)) ts).
  (* THE RELEASE CHANNEL.  An [.aq] load's pre-view joins [w_vRel], and the
     load itself is the [rel_ord] edge that delivers it — RVWMO ppo rule 7. *)
  assert (Hrdb : ∃ a, rd_b E a (ev_at k)).
  { destruct ts as [|t0 ts']; [by destruct (Hnil eq_refl)|].
    destruct (cand_read_of k s base (t0 :: ts') vs 0%nat t0 Hs Hrd Hlen eq_refl)
      as [v Hr].
    exists (acc_addr base 0%nat), k, t0, v. by split. }
  assert (Hreldel : ord_dom E i (S k) (if aq then w_vRel ws else 0%nat)).
  { destruct aq; [|by left].
    eapply (relsrc_acq E i k s); [by rewrite cand_ex_tr|exact Hag
                                 |by eapply lb_rd_is_r|exact Haq|exact Hrdb|].
    exact Hrel. }
  (* per-byte facts *)
  assert (Hread : ∀ p, p ∈ ats → ∃ v, reads_at E k p.1 p.2 v).
  { intros p Hp. destruct (elem_of_zip_seq base ts p Hp) as (j & Hj & ->).
    by eapply cand_read_of. }
  assert (Hfv : ∀ p, p ∈ ats → fwd_view ws aq p.1 p.2 = p.2).
  { intros p Hp. destruct (Hread p Hp) as [v Hr]. by eapply Hnf. }
  assert (Hpub : ∀ p, p ∈ ats → pub_r E (ev_at k) p.2).
  { intros p Hp. destruct (Hread p Hp) as [v Hr].
    by eapply cand_pub_clean_pub_r. }
  assert (Hfrd : ∀ p, p ∈ ats → frdom_b E i (S k) p.1 p.2).
  { intros p Hp. destruct (Hread p Hp) as [v Hr].
    rewrite -Hag. apply (touch_frdom k s p.1 p.2 Hs). left. by exists v. }
  assert (Hrs : ∀ p, p ∈ ats → rsrc E i (S k) p.2).
  { intros p Hp. right. exists k, s, p.2.
    split_and!; [lia|by rewrite cand_ex_tr|done|by apply Hpub|lia]. }
  (* the five conjuncts *)
  rewrite /load_post_run /load_post_bytes -/ws -/ats.
  split_and!.
  - intros a. apply load_fold_coh; [apply maxcl_frdom_b|exact Hfv| | |].
    + eapply frdom_b_wk; [|apply Hc]. lia.
    + rewrite /load_vpre. apply maxcl_max; [apply maxcl_frdom_b| |].
      * eapply ord_dom_frdom; [exact Hordax|exact Hrelax|].
        eapply ord_dom_wk; [|exact Hrn]. lia.
      * eapply ord_dom_frdom; [exact Hordax|exact Hrelax|exact Hreldel].
    + intros p Hp Heq. rewrite -Heq. by apply Hfrd.
  - destruct aq; last first.
    { rewrite load_fold_vrNew_plain. eapply ord_dom_wk; [|exact Hrn]. lia. }
    apply load_fold_vrNew; [apply maxcl_ord_dom|exact Hfv| | |].
    + eapply ord_dom_wk; [|exact Hrn]. lia.
    + rewrite /load_vpre. apply maxcl_max; [apply maxcl_ord_dom| |].
      * eapply ord_dom_wk; [|exact Hrn]. lia.
      * exact Hreldel.
    + intros p Hp. rewrite -Hag.
      apply (acq_ord_dom E (es_ag s) k s p.2);
        [by rewrite cand_ex_tr|done|by eapply lb_rd_is_r|by rewrite Haq|].
      by apply Hpub.
  - apply load_fold_vrOld; [apply maxcl_rdom|exact Hfv| | |].
    + eapply rdom_wk; [|exact Hro]. lia.
    + rewrite /load_vpre. apply maxcl_max; [apply maxcl_rdom| |].
      * left. eapply ord_dom_wk; [|exact Hrn]. lia.
      * left. exact Hreldel.
    + intros p Hp. right. by apply Hrs.
  - rewrite load_fold_vwOld. eapply wsrc_wk; [|exact Hwo]. lia.
  - rewrite load_fold_vRel. eapply relsrc_wk; [|exact Hrel]. lia.
Qed.

Context (Hshape : cand_shape c).
Context (Hatom : ax_atomicity E).

(** *** The store arm

    A store publishes its own timestamp ([pub_w]), which is what [w_vwOld]
    records (pending), and raises [coh] on exactly the bytes it writes — where
    the write event itself is the [po_loc] predecessor.  A RELEASE store does
    one thing more: it publishes on the release channel too ([relsrc]), which
    the next acquire read of this agent will cash in. *)

Lemma inv_store_fold k s base vs rl i ws :
  cd_tr c !! k = Some s → es_ag s = i →
  lb_wr (es_lb s) = Some (base, vs) → lb_rl (es_lb s) = rl →
  invw (S k) i ws →
  invw (S k) i (store_post_run ws rl base (length vs)
                  (ev_ts E (ev_at k))).
Proof.
  intros Hs Hag Hwr Hrlb (Hc & Hrn & Hro & Hwo & Hrel).
  assert (Hm : es_wmsg s = Some (WMsg base vs (Some (es_ag s)) (lb_cls (es_lb s)))).
  { rewrite /es_wmsg Hwr //. }
  assert (HW : is_W E (ev_at k)).
  { exists s. split; [by rewrite cand_ex_tr|by eapply lb_wr_is_w]. }
  assert (Hpw : pub_w E (ev_at k) (ev_ts E (ev_at k))).
  { split_and!; [exact HW|by eexists|done]. }
  assert (HwsT : wsrc E i (S k) (ev_ts E (ev_at k))).
  { right. exists k, s, (ev_ts E (ev_at k)).
    split_and!; [lia|by rewrite cand_ex_tr|done|exact Hpw|lia]. }
  rewrite /store_post_run /store_post_bytes. split_and!.
  - intros a. apply store_fold_coh; [apply maxcl_frdom_b|apply Hc|].
    intros Hin. destruct (elem_of_map_seq base (length vs) a Hin) as (j & Hj & ->).
    rewrite -Hag. apply (touch_frdom k s _ _ Hs). right. split; [|done].
    apply (cand_wr_b c k s _ _ Hs Hm). by apply msg_byte_in_range.
  - by rewrite store_fold_vrNew.
  - by rewrite store_fold_vrOld.
  - apply store_fold_vwOld; [apply maxcl_wsrc|exact Hwo|exact HwsT].
  - apply store_fold_vRel; [apply maxcl_relsrc|exact Hrel|].
    intros ->. right. exists k, s, (ev_ts E (ev_at k)).
    split_and!; [lia|by rewrite cand_ex_tr|exact Hag
                |by eapply lb_wr_is_w|exact Hrlb|exact Hpw|lia].
Qed.

(** *** The fence arm — where PENDING becomes DELIVERED *)

Lemma coh_fence_post ws pr pw sr sw a :
  coh (fence_post ws pr pw sr sw) a = coh ws a.
Proof. done. Qed.

Lemma inv_fence k s pr pw sr sw i :
  cd_tr c !! k = Some s → es_ag s = i → es_lb s = LFence pr pw sr sw →
  inv k i → invw (S k) i (fence_post (ews E k i) pr pw sr sw).
Proof.
  intros Hs Hag Hl (Hc & Hrn & Hro & Hwo & Hrel). split_and!.
  - intros a. rewrite coh_fence_post. eapply frdom_b_wk; [|apply Hc]. lia.
  - apply fence_post_vrNew_pred; [apply maxcl_ord_dom| | |].
    + eapply ord_dom_wk; [|exact Hrn]. lia.
    + intros -> ->. destruct Hro as [Hd|Hp].
      * eapply ord_dom_wk; [|exact Hd]. lia.
      * eapply (rsrc_fence E i k s pw sw); [by rewrite cand_ex_tr|done| |exact Hp].
        by rewrite Hl.
    + intros -> ->.
      eapply (wsrc_fence E i k s pr sw); [by rewrite cand_ex_tr|done| |exact Hwo].
      by rewrite Hl.
  - rewrite /fence_post /=. eapply rdom_wk; [|exact Hro]. lia.
  - rewrite /fence_post /=. eapply wsrc_wk; [|exact Hwo]. lia.
  - rewrite /fence_post /=. eapply relsrc_wk; [|exact Hrel]. lia.
Qed.

(** *** One step of the invariant, all four label arms *)

Lemma inv_step k s i :
  cand_pub_clean c →
  cd_tr c !! k = Some s →
  (∀ a t v, reads_at E k a t v →
     fwd_view (ews E k (es_ag s)) (lb_aq (es_lb s)) a t = t) →
  inv k i → inv (S k) i.
Proof.
  intros Hpc Hs Hnf Hinv.
  destruct (decide (i = es_ag s)) as [->|Hne]; last first.
  { rewrite /inv (cand_ws_ne c k s i Hs Hne). eapply invw_wk; [|exact Hinv]. lia. }
  pose proof (Hshape k s Hs) as Hsh.
  rewrite /inv.
  destruct (es_lb s) as [aq base ts vs|rl base vs kc|pr pw sr sw|
                         aq rl base ts rvs wvs kc] eqn:Hl; simpl in Hsh.
  - (* load *)
    rewrite (cand_ws_load c k s aq base ts vs Hs Hl).
    apply (inv_load_fold k s base ts vs aq (es_ag s) Hpc Hs eq_refl);
      [by rewrite Hl|exact Hsh|by rewrite Hl| |exact Hinv].
    intros a t v Hr. exact (Hnf a t v Hr).
  - (* store *)
    rewrite (cand_ws_store c k s rl base vs kc Hs Hl).
    apply (inv_store_fold k s base vs rl (es_ag s));
      [done|done|by rewrite Hl|by rewrite Hl|].
    eapply invw_wk; [|exact Hinv]. lia.
  - (* fence *)
    rewrite (cand_ws_fence c k s pr pw sr sw Hs Hl).
    by apply (inv_fence k s pr pw sr sw (es_ag s)).
  - (* rmw: the load fold, then the store fold on top of it *)
    rewrite (cand_ws_rmw c k s aq rl base ts rvs wvs kc Hs Hl).
    destruct Hsh as (Hne0 & Hlenw & Hlenr).
    apply (inv_store_fold k s base wvs rl (es_ag s));
      [done|done|by rewrite Hl|by rewrite Hl|].
    apply (inv_load_fold k s base ts rvs aq (es_ag s) Hpc Hs eq_refl);
      [by rewrite Hl|exact Hlenr|by rewrite Hl| |exact Hinv].
    intros a t v Hr. exact (Hnf a t v Hr).
Qed.

(* ================================================================== *)
(** * 9. No read is forwarded — the one place the truncation is needed

    [pub_r_fwd_view] (slice 1) says an acquire or externally-sourced read
    takes its own timestamp rather than a banked view; it is proved from the
    forward-bank invariant [exec_fwd_ok], which needs [exec_wf].  At stage [n]
    of the completeness induction that is available for the TRUNCATED
    candidate, and the states of the two executions agree below [n]. *)

Lemma ctake_wf n :
  (n ≤ length (cd_tr c))%nat →
  (∀ k s, (k < n)%nat → cd_tr c !! k = Some s →
     mstep_ok (stt E k) (es_ag s) (es_lb s)) →
  exec_wf (cand_exec (ctake c n)).
Proof.
  intros Hn Hok. apply (cand_reachable (ctake c n)).
  intros k s Hs.
  assert (Hk : (k < n)%nat).
  { pose proof (lookup_lt_Some _ _ _ Hs) as Hlt.
    rewrite /ctake /= length_take in Hlt. lia. }
  rewrite (ctake_stt c n k ltac:(lia)).
  rewrite /ctake /= (lookup_take (cd_tr c) n k Hk) in Hs.
  by apply Hok.
Qed.

Lemma cand_nofwd n k s a t v :
  (n ≤ length (cd_tr c))%nat →
  (∀ k' s', (k' < n)%nat → cd_tr c !! k' = Some s' →
     mstep_ok (stt E k') (es_ag s') (es_lb s')) →
  cand_pub_clean c →
  (k < n)%nat → cd_tr c !! k = Some s → reads_at E k a t v →
  fwd_view (ews E k (es_ag s)) (lb_aq (es_lb s)) a t = t.
Proof.
  intros Hn Hok Hpc Hk Hs Hr.
  pose proof (ctake_wf n Hn Hok) as Hwf.
  rewrite -(ctake_ews c n k (es_ag s) ltac:(lia)).
  apply (pub_r_fwd_view (cand_exec (ctake c n)) k s a t v Hwf).
  - rewrite (ctake_tr c n k Hk) //.
  - by apply ctake_reads_at.
  - destruct (Hpc k s a t v Hs Hr) as [Haq|(w & Hrf & Hext)]; [by left|].
    right. exists w.
    (* the source's timestamp IS the timestamp read *)
    assert (Hts : ev_ts E w = t).
    { destruct Hrf as (_ & k0 & t0 & v0 & Hkeq & Hr0 & Hts0).
      assert (k0 = k) as -> by (by simplify_eq).
      destruct (reads_at_det E k a t0 v0 t v Hr0 Hr) as [-> _]. exact Hts0. }
    assert (Htlen : (t ≤ length (cd_log c k))%nat) by (by eapply cand_read_ts_le).
    destruct w as [|k'].
    + split.
      * split; [by apply ctake_wr_b_init, (proj1 Hrf)|].
        exists k, t, v. split_and!; [done|by apply ctake_reads_at|].
        rewrite /ev_ts. rewrite /ev_ts in Hts. lia.
      * done.
    + assert (Hk' : (k' < k)%nat).
      { apply (cand_wr_lt k a k'); [exact (proj1 Hrf)|lia]. }
      split.
      * split; [by apply ctake_wr_b, (proj1 Hrf); lia|].
        exists k, t, v. split_and!; [done|by apply ctake_reads_at|].
        rewrite (ctake_ev_ts c n k' ltac:(lia)) //.
      * destruct Hext as (s'' & Hs'' & Hne). exists s''. split; [|exact Hne].
        rewrite cand_ex_tr in Hs''. rewrite (ctake_tr c n k' ltac:(lia)) //.
Qed.

(* ================================================================== *)
(** * 10. THE VIEW-DOMINATION LEMMA, and the discharge of [readable]

    [inv_upto] is the view-domination lemma proper: at every point of the
    replay, every view component of every agent is dominated in the sense of
    §4.  [cand_rd_ok] is what §9(1) said it was for — the [readable] side
    condition, by the [fr]-cycle argument. *)

Lemma inv_upto n :
  (n ≤ length (cd_tr c))%nat →
  cand_pub_clean c →
  (∀ k s, (k < n)%nat → cd_tr c !! k = Some s →
     mstep_ok (stt E k) (es_ag s) (es_lb s)) →
  ∀ k i, (k ≤ n)%nat → inv k i.
Proof.
  intros Hn Hpc Hok k. induction k as [|k IH]; intros i Hk.
  - rewrite /inv /invw (cand_ws_init c i). split_and!.
    + intros a. rewrite coh_init. apply frdom_b_0.
    + by left.
    + left; by left.
    + by left.
    + by left.
  - destruct (lookup_lt_is_Some_2 (cd_tr c) k ltac:(lia)) as [s Hs].
    eapply (inv_step k s i Hpc Hs); [|apply IH; lia].
    intros a t v Hr. eapply (cand_nofwd n k s a t v Hn Hok Hpc); [lia|done|done].
Qed.

(** The read at step [n] is admissible: a write inside [readable]'s forbidden
    window would give an [fr] edge from this very step to a write AT OR BELOW
    the floor — which is exactly what the invariant forbids. *)
Lemma cand_rd_ok n s base ts vs :
  (n ≤ length (cd_tr c))%nat →
  cand_pub_clean c →
  (∀ k s', (k < n)%nat → cd_tr c !! k = Some s' →
     mstep_ok (stt E k) (es_ag s') (es_lb s')) →
  cd_tr c !! n = Some s → lb_rd (es_lb s) = Some (base, ts, vs) →
  length vs = length ts →
  rd_ok (ms_img (stt E n)) (ms_log (stt E n)) (ms_ws (stt E n) (es_ag s))
        (lb_aq (es_lb s)) base ts vs.
Proof.
  intros Hn Hpc Hok Hs Hrd Hlen.
  pose proof (lookup_lt_Some _ _ _ Hs) as Hnlt.
  assert (Himg : ms_img (stt E n) = cd_img c) by (by apply (cand_eimg c n)).
  assert (Hlog : ms_log (stt E n) = cd_log c n) by (by apply (cand_elog c n)).
  pose proof (cand_bounded_upto c n ltac:(lia) Hok) as Hb.
  pose proof (Hb (es_ag s)) as Hbnd. rewrite Hlog in Hbnd.
  pose proof (inv_upto n ltac:(lia) Hpc Hok n (es_ag s) ltac:(lia)) as Hinv.
  rewrite /inv /invw /ews in Hinv.
  destruct Hinv as (Hc & Hrn & _ & _ & Hrel).
  split; [exact Hlen|]. intros j t v Hj Hv.
  set (a := acc_addr base j) in *.
  set (ws := ms_ws (stt E n) (es_ag s)) in *.
  assert (Hr : reads_at E n a t v).
  { exists s, base, ts, vs, j. split_and!; [|done|done|done|done].
    by rewrite cand_ex_tr. }
  assert (Hlb : log_byte (cd_img c) (cd_log c n) t a = Some v)
    by (by eapply Hval).
  (* the floor is a real timestamp, and it is dominated *)
  assert (Hfloor : (Nat.max (load_vpre ws (lb_aq (es_lb s))) (coh ws a)
                    ≤ length (cd_log c n))%nat).
  { pose proof (load_vpre_bounded ws (lb_aq (es_lb s)) _ Hbnd).
    destruct Hbnd as (_ & _ & _ & _ & _ & _ & Hcoh' & _). pose proof (Hcoh' a). lia. }
  rewrite Himg Hlog. split; [exact Hlb|]. split; [by eexists|].
  intros Hw.
  destruct (cand_writes_in_wr c n a t
              (Nat.max (load_vpre ws (lb_aq (es_lb s))) (coh ws a))
              ltac:(lia) Hw) as (w & Hwb & Hgt & Hle).
  (* the [fr] edge from this step to [w] *)
  destruct (Hrft n a t v Hr) as [w0 Hrf0].
  assert (Hts0 : ev_ts E w0 = t).
  { destruct Hrf0 as (_ & k0 & t0 & v0 & Hkeq & Hr0 & Hts0).
    assert (k0 = n) as -> by (by simplify_eq).
    destruct (reads_at_det E n a t0 v0 t v Hr0 Hr) as [-> _]. exact Hts0. }
  assert (Hne : ev_at n ≠ w).
  { intros <-. rewrite (cand_ev_ts c n ltac:(lia)) in Hle. lia. }
  assert (Hfr : fr_b E a (ev_at n) w).
  { split; [|exact Hne]. exists w0. split; [exact Hrf0|].
    split_and!; [exact (proj1 Hrf0)|exact Hwb|lia]. }
  (* ... contradicted by the three dominating conjuncts: [coh], [w_vrNew],
     and — for an ACQUIRE read — the release channel [w_vRel], whose
     dominator is the rule-7 edge from the po-earlier release store. *)
  pose proof (Hc a n s w ltac:(lia) ltac:(by rewrite cand_ex_tr) eq_refl Hfr).
  pose proof (ord_dom_frdom E (es_ag s) n (w_vrNew ws) Hordax Hrelax Hrn a n s w
                ltac:(lia) ltac:(by rewrite cand_ex_tr) eq_refl Hfr).
  assert (Hvpre : (load_vpre ws (lb_aq (es_lb s)) < ev_ts E w)%nat).
  { rewrite /load_vpre. destruct (lb_aq (es_lb s)) eqn:Haq; [|lia].
    pose proof (relsrc_frdom_at E (es_ag s) n s (w_vRel ws) Hrelax
                  ltac:(by rewrite cand_ex_tr) eq_refl
                  ltac:(by eapply lb_rd_is_r) Haq Hrel a w Hfr). lia. }
  lia.
Qed.

(** The RMW's atomicity side condition is [ax_atomicity], read at the one
    place it bites: the RMW's own write sits at the log's top, so "no write
    between the read half and the write half" IS "the read half is latest". *)
Lemma cand_rmw_latest n s base ts vs :
  (n ≤ length (cd_tr c))%nat →
  (∀ k s', (k < n)%nat → cd_tr c !! k = Some s' →
     mstep_ok (stt E k) (es_ag s') (es_lb s')) →
  cd_tr c !! n = Some s → lb_rd (es_lb s) = Some (base, ts, vs) →
  lb_is_w (es_lb s) = true → length vs = length ts →
  rmw_latest (ms_img (stt E n)) (ms_log (stt E n)) base ts.
Proof.
  intros Hn Hok Hs Hrd Hisw Hlen.
  pose proof (lookup_lt_Some _ _ _ Hs) as Hnlt.
  assert (Himg : ms_img (stt E n) = cd_img c) by (by apply (cand_eimg c n)).
  assert (Hlog : ms_log (stt E n) = cd_log c n) by (by apply (cand_elog c n)).
  assert (HW : is_W E (ev_at n)).
  { exists s. split; [by rewrite cand_ex_tr|exact Hisw]. }
  intros j t Hj.
  destruct (lookup_lt_is_Some_2 vs j) as [v Hv].
  { rewrite Hlen. by eapply lookup_lt_Some. }
  assert (Hr : reads_at E n (acc_addr base j) t v).
  { exists s, base, ts, vs, j. split_and!; [|done|done|done|done].
    by rewrite cand_ex_tr. }
  assert (Hlb : log_byte (cd_img c) (cd_log c n) t (acc_addr base j) = Some v)
    by (by eapply Hval).
  rewrite Himg Hlog. split; [by eexists|]. intros Hw.
  destruct (cand_writes_in_wr c n (acc_addr base j) t (length (cd_log c n))
              ltac:(lia) Hw) as (w & Hwb & Hgt & Hle).
  destruct (Hrft n (acc_addr base j) t v Hr) as [w0 Hrf0].
  assert (Hts0 : ev_ts E w0 = t).
  { destruct Hrf0 as (_ & k0 & t0 & v0 & Hkeq & Hr0 & Hts0).
    assert (k0 = n) as -> by (by simplify_eq).
    destruct (reads_at_det E n (acc_addr base j) t0 v0 t v Hr0 Hr) as [-> _].
    exact Hts0. }
  apply (Hatom n (acc_addr base j) w0 w HW Hrf0 Hwb ltac:(lia)).
  rewrite (cand_ev_ts c n ltac:(lia)). lia.
Qed.

(** *** Every step is admissible *)

Lemma cand_mstep_ok_at n s :
  (n ≤ length (cd_tr c))%nat →
  cand_pub_clean c →
  (∀ k s', (k < n)%nat → cd_tr c !! k = Some s' →
     mstep_ok (stt E k) (es_ag s') (es_lb s')) →
  cd_tr c !! n = Some s → mstep_ok (stt E n) (es_ag s) (es_lb s).
Proof.
  intros Hn Hpc Hok Hs. pose proof (Hshape n s Hs) as Hsh.
  destruct (es_lb s) as [aq base ts vs|rl base vs kc|pr pw sr sw|
                         aq rl base ts rvs wvs kc] eqn:Hl; simpl in Hsh |- *.
  - pose proof (cand_rd_ok n s base ts vs Hn Hpc Hok Hs
                  ltac:(by rewrite Hl) Hsh) as HH.
    rewrite Hl /= in HH. exact HH.
  - exact Hsh.
  - done.
  - destruct Hsh as (Hne0 & Hlenw & Hlenr). split_and!.
    + exact Hne0.
    + exact Hlenw.
    + pose proof (cand_rd_ok n s base ts rvs Hn Hpc Hok Hs
                    ltac:(by rewrite Hl) Hlenr) as HH.
      rewrite Hl /= in HH. exact HH.
    + eapply (cand_rmw_latest n s base ts rvs Hn Hok Hs);
        [by rewrite Hl|by rewrite Hl|exact Hlenr].
Qed.

Lemma cand_mstep_ok :
  cand_pub_clean c →
  ∀ n k s, (k < n)%nat → cd_tr c !! k = Some s →
    mstep_ok (stt E k) (es_ag s) (es_lb s).
Proof.
  intros Hpc n. induction n as [|n IH]; intros k s Hk Hs; [lia|].
  destruct (decide (k < n)%nat) as [Hlt|Hge]; [by eapply IH|].
  assert (k = n) as -> by lia.
  pose proof (lookup_lt_Some _ _ _ Hs) as Hnlt.
  eapply (cand_mstep_ok_at n s ltac:(lia) Hpc); [|exact Hs].
  intros k' s' Hk' Hs'. by eapply IH.
Qed.

(** ================================================================ *)
(** ** THE THEOREM (for this section's hypotheses) *)

Theorem complete_clean :
  cand_pub_clean c →
  exec_wf E ∧ ex_tr E = cd_tr c ∧ ex_img E = cd_img c.
Proof.
  intros Hpc. apply cand_reachable. intros k s Hs.
  eapply (cand_mstep_ok Hpc (S k) k s ltac:(lia) Hs).
Qed.

End candidate.

(* ================================================================== *)
(** * 11. §9(1)'s statement, and the theorem this file proves

    [cand_axiomatic_ok] is slice 2 §9(1)'s, plus the rule-7 axiom the
    release→acquire arm contributes ([WeakAxiomatic2.ax_rel_ord]; sound by
    [sound_rel_ord], so it costs the soundness direction nothing). *)

Definition cand_axiomatic_ok (c : cand) : Prop :=
  axiomatic_ok (cand_exec c) ∧ ax_rel_ord (cand_exec c) ∧
  (∀ o, ¬ tc (ob_op (cand_exec c)) o o).

(** THE COMPLETENESS THEOREM OF THIS SLICE.  §9(1)'s
    [promise_free_complete] with the ONE premise §15(1) still forces. *)
Theorem promise_free_complete_clean c :
  cand_shape c → cand_values c →
  cand_pub_clean c →
  cand_axiomatic_ok c →
  exec_wf (cand_exec c) ∧
  ex_tr (cand_exec c) = cd_tr c ∧ ex_img (cand_exec c) = cd_img c.
Proof.
  intros Hsh Hval Hpc
    ((Hrft & _ & _ & Hcohax & Hatom & Hordax & _ & _) & Hrelax & _).
  exact (complete_clean c Hval Hrft Hcohax Hordax Hrelax Hsh Hatom Hpc).
Qed.

(** ... and the same theorem with the hypothesis pared down to what the proof
    actually uses.  FINDING: [ob]-acyclicity is NOT needed — five LOCAL axioms
    are ([ax_rf_total], [ax_coherence], [ax_ord], [ax_rel_ord],
    [ax_atomicity]); the other four conjuncts of [axiomatic_ok] and the whole
    [ob] conjunct are unused.
    Slice 2 §9(1) expected the opposite ("completeness genuinely needs the
    global axiom").  The reason it does not is recorded in the header: the
    [fence_between] / [acq_po] witnesses are monotone in the target, so a view
    value delivered through a CHAIN of fences is still delivered by a single
    [ord] edge from the original publication, which is all [ax_ord] needs. *)
Theorem promise_free_complete_local c :
  cand_shape c → cand_values c →
  cand_pub_clean c →
  ax_rf_total (cand_exec c) → ax_coherence (cand_exec c) →
  ax_ord (cand_exec c) → ax_rel_ord (cand_exec c) → ax_atomicity (cand_exec c) →
  exec_wf (cand_exec c) ∧
  ex_tr (cand_exec c) = cd_tr c ∧ ex_img (cand_exec c) = cd_img c.
Proof.
  intros Hsh Hval Hpc Hrft Hcohax Hordax Hrelax Hatom.
  exact (complete_clean c Hval Hrft Hcohax Hordax Hrelax Hsh Hatom Hpc).
Qed.

(* ================================================================== *)
(** * 12. Which axioms a candidate satisfies for free

    Before the counterexamples: FIVE of [axiomatic_ok]'s eight conjuncts hold
    of ANY value-consistent candidate, with no hypothesis at all.  So the
    content of [cand_axiomatic_ok] is exactly [ax_coherence], [ax_atomicity],
    [ax_ord] and [ob]-acyclicity — which is what the counterexamples have to
    check, and it is also why they are checkable at all. *)

Lemma cand_rf_total c : cand_values c → ax_rf_total (cand_exec c).
Proof.
  intros Hval k a t v Hr. pose proof Hr as Hr'.
  destruct Hr' as (s & base & ts & vs & j & Hs & Hrd & Hj & Hv & Ha).
  rewrite cand_ex_tr in Hs.
  pose proof (Hval k s base ts vs Hs Hrd j t v Hj Hv) as Hlb. rewrite -Ha in Hlb.
  pose proof (lookup_lt_Some _ _ _ Hs) as Hk.
  destruct t as [|i].
  - exists ev_init. split.
    + apply cand_wr_b_init. rewrite log_byte_0 in Hlb. by eexists.
    + exists k, 0%nat, v. by split_and!.
  - pose proof (log_byte_bounded _ _ _ _ (mk_is_Some _ _ Hlb)) as Htlen.
    destruct (cand_ts_writer c k (S i) ltac:(lia) ltac:(lia) Htlen)
      as (k' & s' & m & Hk' & Hs' & Hm & Hts).
    exists (ev_at k'). split.
    + apply (cand_wr_b c k' s' m a Hs' Hm).
      rewrite -(cand_log_byte_wr c k' s' m k a Hs' Hm ltac:(lia)) Hts.
      by eexists.
    + exists k, (S i), v. by split_and!.
Qed.

Lemma cand_rf_functional c : ax_rf_functional (cand_exec c).
Proof.
  intros a w1 w2 r H1 H2.
  pose proof H1 as (Hw1 & k1 & t1 & v1 & -> & Hr1 & Hts1).
  pose proof H2 as (Hw2 & k2 & t2 & v2 & Hkeq & Hr2 & Hts2).
  assert (k2 = k1) as -> by (by simplify_eq).
  destruct (reads_at_det (cand_exec c) k1 a t1 v1 t2 v2 Hr1 Hr2) as [-> _].
  exact (cand_ts_inj c (a, w1) (a, w2) Hw1 Hw2 ltac:(rewrite /= Hts1 Hts2 //)).
Qed.

Lemma cand_rf_value c : cand_values c → ax_rf_value (cand_exec c).
Proof.
  intros Hval k a w t v Hr Hrf.
  pose proof Hrf as (Hw & k0 & t0 & v0 & Hkeq & Hr0 & Hts).
  assert (k0 = k) as -> by (by simplify_eq).
  destruct (reads_at_det (cand_exec c) k a t0 v0 t v Hr0 Hr) as [Heqt Heqv].
  rewrite Heqt in Hts.
  pose proof Hr as (s & base & ts & vs & j & Hs & Hrd & Hj & Hv & Ha).
  rewrite cand_ex_tr in Hs. pose proof (lookup_lt_Some _ _ _ Hs) as Hk.
  pose proof (Hval k s base ts vs Hs Hrd j t v Hj Hv) as Hlb. rewrite -Ha in Hlb.
  pose proof (log_byte_bounded _ _ _ _ (mk_is_Some _ _ Hlb)) as Htlen.
  rewrite Hts cand_ex_img cand_ex_log.
  destruct (cd_log_split c k (length (cd_tr c)) ltac:(lia)) as [l ->].
  rewrite log_byte_app //.
Qed.

Lemma cand_rf_ix c a w k :
  cand_values c → rf_b (cand_exec c) a w (ev_at k) →
  (ev_ix w < ev_ix (ev_at k))%nat.
Proof.
  intros Hval Hrf. pose proof Hrf as (Hw & k0 & t & v & Hkeq & Hr & Hts).
  assert (k0 = k) as -> by (by simplify_eq).
  destruct w as [|k']; [simpl; lia|].
  pose proof (cand_read_ts_le c Hval k a t v Hr) as Htlen.
  pose proof (cand_wr_lt c k a k' Hw ltac:(lia)). simpl. lia.
Qed.

Lemma cand_no_thin_air c : cand_values c → ax_no_thin_air (cand_exec c).
Proof.
  intros Hval. rewrite /ax_no_thin_air.
  apply (tc_nat_lt _ ev_ix). intros x y [Hpo|(a & Hrf)].
  - by apply (po_ix (cand_exec c)).
  - destruct Hrf as (Hw & k & t & v & -> & Hr & Hts).
    apply (cand_rf_ix c a x k Hval). by split; [|exists k, t, v].
Qed.

Lemma cand_po_ww_gmo c : ax_po_ww_gmo (cand_exec c).
Proof.
  intros e1 e2 (k1 & k2 & s1 & s2 & -> & -> & Hlt & Hs1 & Hs2 & Hag) HW1 HW2.
  split_and!; [exact HW1|exact HW2|].
  rewrite cand_ex_tr in Hs1. rewrite cand_ex_tr in Hs2.
  destruct HW1 as (s & Hs & Hw). rewrite cand_ex_tr in Hs.
  assert (s = s1) as -> by (rewrite Hs1 in Hs; by simplify_eq).
  destruct (es_wmsg s1) as [m|] eqn:Hm; [|by rewrite (es_wmsg_none s1 Hm) in Hw].
  apply (cand_ts_mono c k1 k2 s1 m Hs1 Hm Hlt).
  by pose proof (lookup_lt_Some _ _ _ Hs2); lia.
Qed.

(** Two acyclicity lemmas for the SIMPLE shape the counterexamples have: no
    same-byte program order, no event that both reads and writes a byte, and
    (for [ob]) no [ppo_op] edge at all.  Then the naive "a read sits at the
    timestamp it read" placement already embeds every edge, so both
    acyclicity obligations reduce to arithmetic. *)

Lemma coh_rel_acyc_simple c a :
  cand_values c →
  (∀ e1 e2, ¬ po_loc_b (cand_exec c) a e1 e2) →
  (∀ e, wr_b (cand_exec c) a e → ¬ rd_b (cand_exec c) a e) →
  ∀ e, ¬ tc (coh_rel (cand_exec c) a) e e.
Proof.
  intros Hval Hnpl Hnrw.
  apply (tc_lexlt _ (λ e, (ets (cand_exec c) a e, ev_ix e))).
  intros x y [Hpl|[Hrf|[Hco|Hfr]]].
  - by destruct (Hnpl x y Hpl).
  - pose proof Hrf as (Hw & k & t & v & Hkeq & Hr & Hts).
    assert (Hnw : ¬ wr_b (cand_exec c) a y).
    { rewrite Hkeq. intros Hwx. apply (Hnrw _ Hwx). by exists k, t, v. }
    rewrite /lexlt /= (ets_wr (cand_exec c) a x Hw) Hts Hkeq
            (ets_rd (cand_exec c) a k t v ltac:(rewrite -Hkeq //) Hr).
    right. split; [done|].
    apply (cand_rf_ix c a x k Hval). by split; [|exists k, t, v].
  - destruct Hco as (Hw1 & Hw2 & Hlt).
    rewrite (ets_wr (cand_exec c) a x Hw1) (ets_wr (cand_exec c) a y Hw2).
    by left.
  - destruct Hfr as ((w0 & Hrf0 & (Hw0 & Hw2 & Hlt)) & Hne).
    pose proof Hrf0 as (_ & k & t & v & Hkeq & Hr & Hts0).
    assert (Hnw : ¬ wr_b (cand_exec c) a x).
    { rewrite Hkeq. intros Hwx. apply (Hnrw _ Hwx). by exists k, t, v. }
    rewrite (ets_wr (cand_exec c) a y Hw2) Hkeq
            (ets_rd (cand_exec c) a k t v ltac:(rewrite -Hkeq //) Hr).
    left. simpl. lia.
Qed.

Lemma ob_op_acyc_simple c :
  cand_values c →
  (∀ o1 o2, ¬ ppo_op (cand_exec c) o1 o2) →
  (∀ a e, wr_b (cand_exec c) a e → ¬ rd_b (cand_exec c) a e) →
  ∀ o, ¬ tc (ob_op (cand_exec c)) o o.
Proof.
  intros Hval Hnppo Hnrw.
  apply (tc_kless _ (λ o, (ets (cand_exec c) o.1 o.2,
                           ophase (cand_exec c) o.1 o.2, ev_ix o.2, o.1))).
  intros [a1 e1] [a2 e2] [Hppo|[[Ha Hrf]|[[Ha Hco]|[Ha Hfr]]]];
    [by destruct (Hnppo _ _ Hppo)| | |]; simpl in Ha; subst a2.
  - simpl in Hrf. pose proof Hrf as (Hw & k & t & v & Hkeq & Hr & Hts).
    assert (Hnw : ¬ wr_b (cand_exec c) a1 e2).
    { rewrite Hkeq. intros Hwx. apply (Hnrw _ _ Hwx). by exists k, t, v. }
    rewrite /kless /= (ets_wr (cand_exec c) a1 e1 Hw)
            (ophase_wr (cand_exec c) a1 e1 Hw)
            (ophase_nwr (cand_exec c) a1 e2 Hnw) Hkeq
            (ets_rd (cand_exec c) a1 k t v ltac:(rewrite -Hkeq //) Hr).
    right. split; [done|]. left. lia.
  - simpl in Hco. destruct Hco as (Hw1 & Hw2 & Hlt).
    rewrite /kless /= (ets_wr (cand_exec c) a1 e1 Hw1)
            (ets_wr (cand_exec c) a1 e2 Hw2).
    by left.
  - simpl in Hfr. destruct Hfr as ((w0 & Hrf0 & (Hw0 & Hw2 & Hlt)) & Hne).
    pose proof Hrf0 as (_ & k & t & v & Hkeq & Hr & Hts0).
    assert (Hnw : ¬ wr_b (cand_exec c) a1 e1).
    { rewrite Hkeq. intros Hwx. apply (Hnrw _ _ Hwx). by exists k, t, v. }
    rewrite /kless /= (ets_wr (cand_exec c) a1 e2 Hw2) Hkeq
            (ets_rd (cand_exec c) a1 k t v ltac:(rewrite -Hkeq //) Hr).
    left. lia.
Qed.

(* ================================================================== *)
(** * 13. THE RELEASE/ACQUIRE WITNESS, on both sides of the model

    Three steps, two bytes, no fence:

      ts 1 : agent 1 stores byte 0
      ts 2 : agent 0 stores byte 1, [rl] iff the section's [rl] is set
      then : agent 0 ACQUIRE-loads byte 0 and reads timestamp 0 (the image)

    [rl = true] — MACHINE-BLOCKED AND AXIOMATICALLY INCONSISTENT.  The
    machine refuses the third step ([ce_rl_blocked]): [store_post] put
    timestamp 2 into agent 0's [w_vRel], an acquire's [load_vpre] joins it
    ([ce_rl_floor]: the floor is 2), and timestamp 1 writes byte 0 inside the
    window (0,2].  The model refuses it too ([ce_rl_true_inconsistent]): the
    release store is [rel_acq_po]-before the acquire load (RVWMO ppo rule 7),
    the acquire load is [fr]-before agent 1's store of byte 0, and that store
    sits at timestamp 1 BELOW the release store's timestamp 2 — which is what
    [ax_rel_ord] forbids.  This candidate is exactly why the arm exists: with
    [ppo_op] lacking it, the same trace passed every axiom while the machine
    blocked it, and completeness was false ([cand_rl_free] used to be the
    premise that excluded it).

    [rl = false] — MACHINE-REACHABLE ([ce_rl_stale_reachable], via §11's
    theorem) and not an SC candidate: agent 0 reads a value timestamp 1 has
    already overwritten.  Nothing in the trace changes but the annotation, so
    the pair is also the non-vacuity witness for the arm.

    Note the return leg of the inconsistency: [fr] then the TIMESTAMP order
    on writes, not an [ob_op] edge — agent 1's store is an [ob_op] sink here.
    That is why the arm's axiomatic content is [ax_rel_ord] and not a cycle
    in [ob_op] (whose acyclicity this candidate still satisfies). *)

Section ce_rl.
Context (rl : bool) (v : bv 8).

Definition ce_rl_tr : list estep :=
  [EStep 1 (LStore false 0 [v] WCplain);
   EStep 0 (LStore rl 1 [v] WCplain);
   EStep 0 (LLoad true 0 [0]%nat [v])].

Definition ce_rl : cand := Cand (λ _, Some v) ce_rl_tr.

Lemma ce_rl_shape : cand_shape ce_rl.
Proof.
  intros k s Hs. rewrite /ce_rl /ce_rl_tr /= in Hs.
  by destruct k as [|[|[|k]]]; simplify_eq/=.
Qed.

Lemma ce_rl_values : cand_values ce_rl.
Proof.
  intros k s base ts vs Hs Hrd j t v' Hj Hv'.
  rewrite /ce_rl /ce_rl_tr /= in Hs.
  destruct k as [|[|[|k]]]; simplify_eq/=; try done.
  by destruct j as [|j]; simplify_eq/=.
Qed.

Lemma ce_rl_pub_clean : cand_pub_clean ce_rl.
Proof.
  intros k s a t v' Hs Hr.
  destruct Hr as (s' & base & ts & vs & j & Hs' & Hrd & Hj & Hv & Ha).
  rewrite /ce_rl /ce_rl_tr /= in Hs, Hs'.
  destruct k as [|[|[|k]]]; simplify_eq/=; try done. by left.
Qed.

End ce_rl.

(** The machine's refusal, computed. *)
Lemma ce_rl_blocked (v : bv 8) : ¬ exec_wf (cand_exec (ce_rl true v)).
Proof.
  intros Hwf.
  pose proof (exec_step_at (cand_exec (ce_rl true v)) 2%nat
                (EStep 0 (LLoad true 0 [0]%nat [v])) Hwf eq_refl) as Hstep.
  destruct (mstep_det _ _ _ _ Hstep) as [_ Hok].
  destruct Hok as [_ Hall].
  destruct (Hall 0%nat 0%nat v eq_refl eq_refl) as [_ [_ Hnw]].
  apply Hnw.
  (* the state after the first two steps, computed from the replay *)
  rewrite (cand_next (ce_rl true v) 1%nat (EStep 0 (LStore true 1 [v] WCplain)) eq_refl)
          (cand_next (ce_rl true v) 0%nat (EStep 1 (LStore false 0 [v] WCplain)) eq_refl)
          cand_stt_init /=.
  rewrite upd_ws_eq (upd_ws_ne _ 1%nat _ 0%nat ltac:(lia)) /=.
  rewrite /store_post_run /store_post_bytes /= /acc_addr /=.
  rewrite /load_vpre /store_post /coh /= lookup_insert_ne; [lia|].
  rewrite lookup_empty /=.
  exists 1%nat. split_and!; [lia|lia|]. eexists. split; [done|].
  rewrite /msg_byte /=. by eexists.
Qed.

Section ce_rl_ax.
Context (rl : bool) (v : bv 8).

Lemma msg_byte_single (b : Z) tid k (a : Z) :
  is_Some (msg_byte (WMsg b [v] tid k) a) → a = b.
Proof.
  rewrite /msg_byte /=. case_bool_decide as Hle; [|by intros []].
  intros [w Hw]. destruct (Z.to_nat (a - b)) as [|n] eqn:Hn; [lia|].
  by simplify_eq/=.
Qed.

Lemma ce_rl_tr_inv k s :
  cd_tr (ce_rl rl v) !! k = Some s →
  (k = 0%nat ∧ s = EStep 1 (LStore false 0 [v] WCplain)) ∨
  (k = 1%nat ∧ s = EStep 0 (LStore rl 1 [v] WCplain)) ∨
  (k = 2%nat ∧ s = EStep 0 (LLoad true 0 [0]%nat [v])).
Proof.
  intros Hs. rewrite /ce_rl /ce_rl_tr /= in Hs.
  destruct k as [|[|[|k]]]; simplify_eq/=; auto.
Qed.

Lemma ce_rl_no_fence e1 e2 :
  ¬ ord_pw (cand_exec (ce_rl rl v)) e1 e2 ∧ ¬ ord_pr (cand_exec (ce_rl rl v)) e1 e2.
Proof.
  assert (Hnf : ∀ k1 k2 pr pw sr sw,
            ¬ fence_between (cand_exec (ce_rl rl v)) k1 k2 pr pw sr sw).
  { intros k1 k2 pr pw sr sw (kf & sf & ? & ? & ? & ? & ? & Hsf & ? & ? & ? & Hlf).
    rewrite cand_ex_tr in Hsf.
    destruct (ce_rl_tr_inv kf sf Hsf) as [[_ ->]|[[_ ->]|[_ ->]]];
      by rewrite /= in Hlf. }
  split.
  - intros (k1 & k2 & pr & sw & _ & _ & Hfb). by eapply Hnf.
  - intros [(k1 & k2 & pw & sw & _ & _ & Hfb)
           |(k1 & k2 & s1 & s2 & -> & -> & Hlt & Hs1 & Hs2 & Hag & Hisr & Haq)];
      [by eapply Hnf|].
    rewrite cand_ex_tr in Hs1. rewrite cand_ex_tr in Hs2.
    destruct (ce_rl_tr_inv k1 s1 Hs1) as [[-> ->]|[[-> ->]|[-> ->]]];
      destruct (ce_rl_tr_inv k2 s2 Hs2) as [[-> ->]|[[-> ->]|[-> ->]]];
      rewrite /= in Hag, Hisr, Haq |- *; try lia; try done.
Qed.

Lemma ce_rl_po e1 e2 :
  po (cand_exec (ce_rl rl v)) e1 e2 → e1 = ev_at 1%nat ∧ e2 = ev_at 2%nat.
Proof.
  intros (k1 & k2 & s1 & s2 & -> & -> & Hlt & Hs1 & Hs2 & Hag).
  rewrite cand_ex_tr in Hs1. rewrite cand_ex_tr in Hs2.
  destruct (ce_rl_tr_inv k1 s1 Hs1) as [[-> ->]|[[-> ->]|[-> ->]]];
    destruct (ce_rl_tr_inv k2 s2 Hs2) as [[-> ->]|[[-> ->]|[-> ->]]];
    rewrite /= in Hag |- *; (try lia); by simplify_eq.
Qed.

Lemma ce_rl_rd_b a e :
  rd_b (cand_exec (ce_rl rl v)) a e → e = ev_at 2%nat ∧ a = 0.
Proof.
  intros (k & t & v' & -> & (s & base & ts & vs & j & Hs & Hrd & Hj & Hv & Ha)).
  rewrite cand_ex_tr in Hs.
  destruct (ce_rl_tr_inv k s Hs) as [[-> ->]|[[-> ->]|[-> ->]]];
    rewrite /= in Hrd; simplify_eq.
  destruct j as [|j]; simplify_eq/=;
    try (split; [done|rewrite /acc_addr; lia]); done.
Qed.

Lemma ce_rl_wr2 a : ¬ wr_b (cand_exec (ce_rl rl v)) a (ev_at 2%nat).
Proof.
  intros [(s & Hs & Hw) _]. rewrite cand_ex_tr in Hs.
  destruct (ce_rl_tr_inv 2%nat s Hs) as [[Habs _]|[[Habs _]|[_ ->]]];
    [lia|lia|by rewrite /= in Hw].
Qed.

Lemma ce_rl_wr1 a : wr_b (cand_exec (ce_rl rl v)) a (ev_at 1%nat) → a = 1.
Proof.
  intros Hw. destruct (cand_wr_b_inv (ce_rl rl v) a (ev_at 1%nat) Hw)
    as [[Habs _]|(k & s & m & Heq & Hs & Hm & Hb)]; [done|].
  assert (k = 1%nat) as -> by (by simplify_eq).
  destruct (ce_rl_tr_inv 1%nat s Hs) as [[Habs _]|[[_ ->]|[Habs _]]];
    [lia| |lia].
  rewrite /es_wmsg /= in Hm. simplify_eq.
  by apply (msg_byte_single 1 (Some 0%nat) WCplain).
Qed.

(** No same-byte program order, and no event both reads and writes a byte. *)
Lemma ce_rl_no_poloc a e1 e2 : ¬ po_loc_b (cand_exec (ce_rl rl v)) a e1 e2.
Proof.
  intros (Hpo & Hacc1 & Hacc2).
  destruct (ce_rl_po e1 e2 Hpo) as [-> ->].
  assert (a = 0) as ->.
  { destruct Hacc2 as [Hw|Hr]; [by destruct (ce_rl_wr2 a Hw)|].
    by destruct (ce_rl_rd_b a (ev_at 2%nat) Hr) as [_ ->]. }
  destruct Hacc1 as [Hw|Hr].
  - pose proof (ce_rl_wr1 0 Hw). lia.
  - by destruct (ce_rl_rd_b 0 (ev_at 1%nat) Hr) as [Habs _].
Qed.

Lemma ce_rl_no_rw a e :
  wr_b (cand_exec (ce_rl rl v)) a e → ¬ rd_b (cand_exec (ce_rl rl v)) a e.
Proof.
  intros Hw Hr. destruct (ce_rl_rd_b a e Hr) as [-> _].
  by apply (ce_rl_wr2 a).
Qed.

(** With no [.rl] anywhere in the trace there is no rule-7 edge, hence no
    [rel_ord] edge at all. *)
Lemma ce_rl_no_rel_acq e1 e2 :
  rl = false → ¬ rel_acq_po (cand_exec (ce_rl rl v)) e1 e2.
Proof.
  intros Hrl (k1 & k2 & s1 & s2 & -> & -> & Hlt & Hs1 & Hs2 & Hag & _ & Hrl1 & _).
  rewrite cand_ex_tr in Hs1.
  destruct (ce_rl_tr_inv k1 s1 Hs1) as [[-> ->]|[[-> ->]|[-> ->]]];
    rewrite /= in Hrl1; congruence.
Qed.

Lemma ce_rl_no_rel_ord e1 e2 :
  rl = false → ¬ rel_ord (cand_exec (ce_rl rl v)) e1 e2.
Proof.
  intros Hrl [H|(em & H & _ & _)]; by apply (ce_rl_no_rel_acq _ _ Hrl H).
Qed.

Lemma ce_rl_no_ppo : rl = false → ∀ o1 o2, ¬ ppo_op (cand_exec (ce_rl rl v)) o1 o2.
Proof.
  intros Hrl o1 o2 [[Hpo Hw2]|[[Ha Hpl]|[[Hord _]|[(Hord & _ & _)|[Hrel _]]]]].
  - destruct (ce_rl_po _ _ Hpo) as [_ Heq]. rewrite Heq in Hw2.
    by apply (ce_rl_wr2 o2.1).
  - by apply (ce_rl_no_poloc o1.1 o1.2 o2.2).
  - by destruct (ce_rl_no_fence o1.2 o2.2) as [H _].
  - by destruct (ce_rl_no_fence o1.2 o2.2) as [_ H].
  - by apply (ce_rl_no_rel_acq o1.2 o2.2 Hrl Hrel).
Qed.

End ce_rl_ax.

Section ce_rl_final.
Context (rl : bool) (v : bv 8).

Lemma ce_rl_notW2 : ¬ is_W (cand_exec (ce_rl rl v)) (ev_at 2%nat).
Proof.
  intros (s & Hs & Hw). rewrite cand_ex_tr in Hs.
  destruct (ce_rl_tr_inv rl v 2%nat s Hs) as [[Habs _]|[[Habs _]|[_ ->]]];
    [lia|lia|by rewrite /= in Hw].
Qed.

Lemma ce_rl_ax_coherence : ax_coherence (cand_exec (ce_rl rl v)).
Proof.
  intros a e. apply (coh_rel_acyc_simple (ce_rl rl v) a (ce_rl_values rl v));
    [apply ce_rl_no_poloc|apply ce_rl_no_rw].
Qed.

Lemma ce_rl_ax_atomicity : ax_atomicity (cand_exec (ce_rl rl v)).
Proof.
  intros kr a w0 w HW Hrf0 _ _.
  destruct Hrf0 as (_ & k & t & v' & Hkeq & Hr & _).
  assert (k = kr) as -> by (by simplify_eq).
  destruct (ce_rl_rd_b rl v a (ev_at kr) ltac:(by exists kr, t, v')) as [Heq _].
  assert (kr = 2%nat) as -> by (by simplify_eq).
  by destruct (ce_rl_notW2 HW).
Qed.

Lemma ce_rl_ax_ord : ax_ord (cand_exec (ce_rl rl v)).
Proof.
  intros e1 k2 s2 a w t Hs2 Hcase Hfr.
  destruct (ce_rl_no_fence rl v e1 (ev_at k2)) as [Hpw Hpr].
  by destruct Hcase as [[Hord _]|[Hord _]].
Qed.

Lemma ce_rl_ax_rel_ord : rl = false → ax_rel_ord (cand_exec (ce_rl rl v)).
Proof.
  intros Hrl e1 k2 s2 a w t Hs2 Hro _ _.
  by destruct (ce_rl_no_rel_ord rl v e1 (ev_at k2) Hrl Hro).
Qed.

Theorem ce_rl_axiomatic_ok : rl = false → cand_axiomatic_ok (ce_rl rl v).
Proof.
  intros Hrl. split_and!.
  - split_and!.
    + by apply cand_rf_total, ce_rl_values.
    + apply cand_rf_functional.
    + by apply cand_rf_value, ce_rl_values.
    + apply ce_rl_ax_coherence.
    + apply ce_rl_ax_atomicity.
    + apply ce_rl_ax_ord.
    + by apply cand_no_thin_air, ce_rl_values.
    + apply cand_po_ww_gmo.
  - by apply ce_rl_ax_rel_ord.
  - apply (ob_op_acyc_simple (ce_rl rl v) (ce_rl_values rl v));
      [by apply ce_rl_no_ppo|apply ce_rl_no_rw].
Qed.

(** The floor the machine computes at the acquire load: [w_vRel] = 2. *)
Lemma ce_rl_floor :
  Nat.max (load_vpre (ms_ws (stt (cand_exec (ce_rl true v)) 2%nat) 0%nat) true)
          (coh (ms_ws (stt (cand_exec (ce_rl true v)) 2%nat) 0%nat) 0) = 2%nat.
Proof.
  rewrite (cand_next (ce_rl true v) 1%nat (EStep 0 (LStore true 1 [v] WCplain)) eq_refl)
          (cand_next (ce_rl true v) 0%nat (EStep 1 (LStore false 0 [v] WCplain)) eq_refl)
          cand_stt_init /=.
  rewrite upd_ws_eq (upd_ws_ne _ 1%nat _ 0%nat ltac:(lia)) /=.
  rewrite /store_post_run /store_post_bytes /= /acc_addr /=.
  rewrite /load_vpre /store_post /coh /= lookup_insert_ne; [lia|].
  by rewrite lookup_empty /=.
Qed.

End ce_rl_final.

(** An operation of the virtual init event always sits at position 0. *)
Lemma opos_init E a : opos E a ev_init = 0%nat.
Proof.
  rewrite /opos /ets /evpre. by destruct (writesb E a ev_init).
Qed.

(** ================================================================ *)
(** ** THE WITNESS, ON THE MODEL SIDE

    [ce_rl true v] fails [cand_axiomatic_ok] — the machine's refusal
    ([ce_rl_blocked]) is now the model's refusal too.  The offending
    configuration, spelled out: the release store [ev_at 1] (timestamp 2) is
    [rel_acq_po]-before the acquire load [ev_at 2] (rule 7), the acquire load
    is [fr]-before agent 1's store [ev_at 0] of byte 0 (it read the image at
    timestamp 0, and [ev_at 0] wrote that byte at timestamp 1), and
    [1 < 2] — so [ax_rel_ord] is violated. *)
Section ce_rl_true.
Context (v : bv 8).
Local Notation Ec := (cand_exec (ce_rl true v)).

Theorem ce_rl_true_inconsistent : ¬ cand_axiomatic_ok (ce_rl true v).
Proof.
  intros (_ & Hrelax & _).
  (* the two writes of byte 0: the image, and agent 1's store at timestamp 1 *)
  assert (Hwi : wr_b Ec 0 ev_init) by (apply cand_wr_b_init; by eexists).
  assert (Hw0 : wr_b Ec 0 (ev_at 0%nat)).
  { apply (cand_wr_b (ce_rl true v) 0%nat (EStep 1 (LStore false 0 [v] WCplain))
             (WMsg 0 [v] (Some 1%nat) WCplain) 0 eq_refl eq_refl).
    rewrite /msg_byte /=. by eexists. }
  assert (Hts0 : ev_ts Ec (ev_at 0%nat) = 1%nat).
  { rewrite (cand_ev_ts (ce_rl true v) 0%nat ltac:(simpl; lia))
            /cd_log /ce_rl /ce_rl_tr //. }
  assert (Hts1 : ev_ts Ec (ev_at 1%nat) = 2%nat).
  { rewrite (cand_ev_ts (ce_rl true v) 1%nat ltac:(simpl; lia))
            /cd_log /ce_rl /ce_rl_tr //. }
  (* the acquire load reads the image, and so is [fr]-before that store *)
  assert (Hr : reads_at Ec 2%nat 0 0%nat v).
  { exists (EStep 0 (LLoad true 0 [0]%nat [v])), 0, [0]%nat, [v], 0%nat.
    split_and!; [done|done|done|done|rewrite /acc_addr; lia]. }
  assert (Hfr : fr_b Ec 0 (ev_at 2%nat) (ev_at 0%nat)).
  { split; [|done]. exists ev_init. split.
    - split; [exact Hwi|]. exists 2%nat, 0%nat, v. by split_and!.
    - split_and!; [exact Hwi|exact Hw0|rewrite Hts0 /ev_ts /=; lia]. }
  (* the rule-7 edge, and the release store's publication *)
  assert (Hra : rel_acq_po Ec (ev_at 1%nat) (ev_at 2%nat)).
  { exists 1%nat, 2%nat, (EStep 0 (LStore true 1 [v] WCplain)),
           (EStep 0 (LLoad true 0 [0]%nat [v])).
    split_and!; [done|done|lia|done|done|done|done|done|done|done]. }
  assert (Hpub : pub_w Ec (ev_at 1%nat) (ev_ts Ec (ev_at 1%nat))).
  { split_and!; [|by eexists|done].
    exists (EStep 0 (LStore true 1 [v] WCplain)). by split. }
  pose proof (Hrelax (ev_at 1%nat) 2%nat (EStep 0 (LLoad true 0 [0]%nat [v]))
                0 (ev_at 0%nat) (ev_ts Ec (ev_at 1%nat)) eq_refl
                (or_introl Hra) Hpub Hfr).
  lia.
Qed.

End ce_rl_true.

(** ================================================================ *)
(** ** NON-VACUITY: the same trace WITHOUT the release annotation is
    machine-reachable BY THE THEOREM OF §11 — and it is not an SC candidate,
    so §11 is a strict generalisation of slice 2's [sc_cand_reachable]: agent
    0 reads the era-initial image of byte 0 although timestamp 1 has already
    overwritten it. *)
Theorem ce_rl_stale_reachable (v : bv 8) :
  exec_wf (cand_exec (ce_rl false v)) ∧ ¬ cand_latest (ce_rl false v).
Proof.
  split.
  - eapply promise_free_complete_clean.
    + apply ce_rl_shape.
    + apply ce_rl_values.
    + apply ce_rl_pub_clean.
    + by apply ce_rl_axiomatic_ok.
  - intros Hlat.
    destruct (Hlat 2%nat (EStep 0 (LLoad true 0 [0]%nat [v])) 0 [0]%nat [v]
                eq_refl eq_refl 0%nat 0%nat eq_refl) as [_ Hnw].
    apply Hnw. rewrite /cd_log /ce_rl /ce_rl_tr /acc_addr /=.
    exists 1%nat. split_and!; [lia|lia|]. eexists. split; [done|].
    rewrite /msg_byte /=. by eexists.
Qed.

(* ================================================================== *)
(** * 14. THE NAMED TOP LEVEL: sRVWMO

    sRVWMO is RVWMO with ONE ordering rule added — [ax_po_ww_gmo]'s
    generalisation "po ∩ (M × W) ⊆ gmo", stores are never early — and with
    its ppo fragment restricted to what the promise-free machine actually
    enforces.  [srvwmo_consistent] is that model, over a candidate; the
    realizability theorem is T1, the direction tier-1 safety consumes.

    THE ppo RESIDUE TABLE (design doc "SETTLED AXIOMATIZATION", 2026-08-19).
    sRVWMO's ppo = RVWMO rules 1–5, 7, 14.  Where each of the others went:

<<
      rule                             status here
      -----------------------------------------------------------------
      1–3  same-address pairs          IN   [po_loc_b] / [ax_coherence]
      4    fence pred/succ             IN   [ord_pw] / [ord_pr] / [ax_ord]
      5    acquire annotation on a     IN   [acq_po] (inside [ord_pr])
      7    RCsc pair (rl before aq)    IN   [rel_acq_po] / [ax_rel_ord]
                                            — this slice's arm; the machine's
                                            form is unconditional, which
                                            coincides with rule 7 under
                                            RISC-V's all-RCsc annotations
      14   b is a store (NEW)          IN   [ppo_op]'s first arm, in full
      -----------------------------------------------------------------
      6    release annotation on b     OMITTED: the machine does not enforce
                                       it; its only non-redundant corner is a
                                       release-annotated LOAD ([lr.rl]), which
                                       no ISA-sane code emits
      8    LR/SC pair                  REDUNDANT under 14 (right end a store)
      10, 11, 13                       REDUNDANT under 14 (right end a store)
      9  (store half)                  REDUNDANT under 14
      9  (LOAD half: addr-dependent    OMITTED **BECAUSE OF D-8**, not by
          loads)                       vacuity — [read_ok_d]'s [vaddr] floor
                                       IS a live binding site; the xv6
                                       instance's loads carry [asrc = []], so
                                       the site is unreachable.  IF D-8 IS
                                       EVER DROPPED, RULE 9's LOAD HALF COMES
                                       STRAIGHT BACK INTO THE DEFINITION.
      12   forwarding pipeline         OMITTED via the [dep_dom] domination
                                       argument (every dependency view is
                                       dominated by [w_vrOld] at every
                                       pf-reachable state), which must LAND
                                       separately
>>

    Exclusive pairs stay FUSED in this presentation: the projection re-fuses a
    split machine pair (value-exact inside [excl_ok]'s window), and a DANGLING
    exclusive read projects as a plain load with no atomicity obligation. *)

Definition srvwmo_consistent (c : cand) : Prop :=
  cand_shape c ∧ cand_values c ∧ cand_axiomatic_ok c.

(** T1 FOR THIS FRAGMENT: an sRVWMO-consistent candidate is realized by the
    promise-free machine, with the same trace and the same image.  The single
    remaining premise is [cand_pub_clean]; deleting it is task A3(ii) (re-prove
    §8's [w_vrOld]/[w_vrNew] conjuncts for a FORWARDED read, whose
    contribution post-D-7 is the pre-view rather than its timestamp, plus the
    ~150-line generalisation §15(1) prices). *)
Theorem srvwmo_realizable c :
  srvwmo_consistent c →
  cand_pub_clean c →            (* A3(ii) deletes this *)
  exec_wf (cand_exec c) ∧
  ex_tr (cand_exec c) = cd_tr c ∧ ex_img (cand_exec c) = cd_img c.
Proof.
  intros (Hsh & Hval & Hax) Hpc. by apply promise_free_complete_clean.
Qed.

(* ================================================================== *)
(** * 15. WHAT THIS SLICE DOES NOT DO

    As in slices 1 and 2, everything that does not close is a comment, not an
    [Axiom]: [Print Assumptions] on [srvwmo_realizable],
    [promise_free_complete_clean], [promise_free_complete_local],
    [ce_rl_true_inconsistent] and [ce_rl_stale_reachable] all report "Closed
    under the global context".

    ------------------------------------------------------------------
    (1) COUNTEREXAMPLE (b) — THE FORWARD-BANK LEAK — is ARGUED HERE AND NOT
    MACHINE-CHECKED.  It is what forces the one surviving premise,
    [cand_pub_clean], and it is a genuinely different leak from §13's: it
    survives a release-free trace.  The witness, in this file's vocabulary:

<<
      Definition ce_fwd_tr : list estep :=
        [EStep 1 (LStore false 0 [v] WCplain);              (* ts 1: foreign write of byte 0 *)
         EStep 0 (LStore false 1 [v] WCplain);              (* ts 2: own write of byte 1 *)
         EStep 0 (LFence false true false true);    (* fence pw,sw : vwNew := 2 *)
         EStep 0 (LStore false 2 [v] WCplain);              (* ts 3: banks fwd[2] = (3, 2) *)
         EStep 0 (LLoad false 2 [3]%nat [v]);       (* FORWARDED: vrOld := 2 *)
         EStep 0 (LFence true false true false);    (* fence pr,sr : vrNew := 2 *)
         EStep 0 (LLoad false 0 [0]%nat [v])].      (* blocked: 1 ∈ (0,2] writes byte 0 *)

      Definition ce_fwd : cand := Cand (λ _, Some v) ce_fwd_tr.
>>

    MACHINE SIDE (the same computation as [ce_rl_blocked], one step longer):
    [w_vwOld = 2] after step 1; the [pw,sw] fence lifts it to [w_vwNew = 2];
    step 3 banks [(3, w_vwNew) = (3, 2)] at byte 2; step 4 reads its own
    timestamp 3, so [fwd_view] returns the BANKED 2 and [w_vrOld] becomes 2;
    the [pr,sr] fence lifts that to [w_vrNew = 2]; step 6's floor is therefore
    2 and timestamp 1 writes byte 0 inside (0,2] — [readable] fails.

    THIS WITNESS IS DEAD AS OF D-7 (2026-08-17).  [store_post] banks [(3, 0)],
    not [(3, 2)]: step 4's [fwd_view] returns 0, [w_vrOld] stays 0, the
    [pr,sr] fence lifts nothing, and step 6's floor is 0 — the machine ALLOWS
    the trace, matching the axiomatic side computed just below.  So there is
    no known counterexample forcing [cand_pub_clean] any more; it survives as
    a premise the PROOF uses, not one the STATEMENT needs.  See the header's
    (b') for what removing it would cost.

    AXIOMATIC SIDE (why no axiom catches it):
    - [ord_pw] needs a fence with [pw ∧ sr]: step 2 has [sr = false], step 5
      has [pw = false].  So there is NO [ord_pw] edge at all.
    - [ord_pr] edges DO exist (step 5 has [pr ∧ sr]), but the [ppo_op] arm and
      [ax_ord] both require [pub_r] of the SOURCE, and the only read that
      could carry the value — step 4 — is internally sourced and not acquire,
      so [pub_r] fails.  This is slice 1 §7(3)'s recorded [rfi] exclusion.
    - [ax_coherence]: agent 0 touches byte 2 twice (steps 3 and 4) with the
      SAME timestamp 3, so the [po_loc] edge is [ets]-flat and [ev_ix]-rising;
      every other byte is touched at most once per agent.  Acyclic.
    - [ob]: the only [fr] edge is (byte 0, step 6) -> (byte 0, step 0), and
      step 0 is an [ob]-SINK (nothing reads timestamp 1, nothing [co]-follows
      it).  Acyclic.
    - [ax_atomicity] is vacuous (no RMW); the [rf] axioms, [ax_no_thin_air]
      and [ax_po_ww_gmo] are free by §12.

    WHAT A MECHANISATION WOULD COST, and why it was not done here: §13's
    acyclicity shortcuts do NOT apply — [ppo_op] is non-empty for this witness
    (the po-into-a-write arm fires, and there is a [po_loc] pair), so
    [ob_op_acyc_simple] and [coh_rel_acyc_simple] must be generalised to
    "every [ppo_op] edge is [po] into a write, or [po_loc] with equal [ets]"
    before they can discharge it.  That generalisation is the honest ~150-line
    residue of this file; the machine side and the [ord]-emptiness side are
    each a ten-line computation of the shape already landed in §13.

    ------------------------------------------------------------------
    (2) WHY ONE PREMISE REMAINS, AND WHERE THE OTHER WENT.  A premise here
    marks a place where THE MACHINE IS STRONGER THAN THE MODELLED [ppo] — the
    polarity that is free for soundness and fatal for completeness.  Both
    original leaks are now closed AT THE SOURCE rather than by a premise:

    - the RELEASE/ACQUIRE leak, by STRENGTHENING THE MODEL: [ppo_op] carries
      RVWMO ppo rule 7 ([rel_acq_po]) and [cand_axiomatic_ok] carries the
      ordering axiom it generates ([ax_rel_ord], sound by
      [WeakAxiomatic2.sound_rel_ord]).  §13's witness moved sides
      ([ce_rl_true_inconsistent]) and [cand_rl_free] is gone.
    - the FORWARD-BANK leak, by WEAKENING THE MACHINE: D-7 (2026-08-17) makes
      [store_post] bank [0] instead of [w_vwNew], for the independent reason
      that the old fence floor was a behaviour-REDUCING deviation from RVWMO
      ppo 12.  The witness in (1) no longer blocks.

    [cand_pub_clean] therefore survives as a PROOF-side premise only: §8's
    [w_vrOld]/[w_vrNew] conjuncts are still stated for a read whose
    contribution IS its timestamp, and a forwarded read now contributes the
    pre-view instead.  Re-proving those two conjuncts is the whole cost of
    deleting it (task A3(ii)), together with (1)'s generalisation if the
    witness is to be mechanised rather than argued.

    ------------------------------------------------------------------
    (3) OWED LIFTS (for W4's batch), all proved here against [.vo]s this slice
    may not edit: [maxcl] and the upper-bound fold lemmas of §5
    ([load_fold_coh] / [load_fold_vrOld] / [load_fold_vrNew] /
    [store_fold_coh] / [store_fold_vwOld] / [fence_post_vrNew_pred], plus the
    five "this step does not touch that component" equalities) belong in
    [WeakMem.v] next to [ws_bounded]'s preservation lemmas — they are the
    missing THIRD kind of step-function fact (monotone / bounded / DOMINATED).
    §5's own [store_fold_vRel] — the release channel's bound, proved here for
    the same reason — belongs there too, next to [store_fold_vRel_norl].
    §1–§3's candidate-level log calculus ([tr_msgs_app], [cd_log_S],
    [cd_log_split], [cand_ev_ts], [cand_ts_writer], [cand_ts_inj],
    [cand_wr_b] / [cand_wr_b_inv]) belongs in [WeakAxiomatic2.v] next to
    [cand_exec], and §12's five free-axiom lemmas next to [sc_cand_reachable]:
    they say that [cand_values] alone buys five of [axiomatic_ok]'s eight
    conjuncts, which sharpens what a consumer of the characterization has to
    check. *)
