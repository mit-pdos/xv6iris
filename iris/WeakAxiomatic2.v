(** * WeakAxiomatic2.v — the global memory order, and [ob]-acyclicity

    W4 SLICE 2 of the M6 robustness effort
    ([claude-notes/projects/weak-memory-m6.md]).  Slice 1 ([WeakAxiomatic.v])
    built the event-labelled machine, the relations, the ppo fragment, and the
    SOUNDNESS direction in LOCAL form ([ax_ord]).  This file builds the object
    slice 1 said it could not: a GLOBAL MEMORY ORDER in which every read is
    placed, and derives from it the global external axiom
    [acyclic(ppo ∪ rf ∪ co ∪ fr)].

    DELIBERATELY DEPENDENCY-FREE, like its parent: stdpp + [WeakMem] +
    [WeakAxiomatic], nothing else.  No Iris, no Sail.  No [Axiom], no
    [Admitted]: everything that does not close is a commented conjecture.

    ------------------------------------------------------------------------
    THE HEADLINE DESIGN DECISION, AND WHY SLICE 1's §7 SPEC HAD TO MOVE

    Slice 1's §7 conjectured [ax_external] over EVENTS:

<<
      Definition ob (E : exec) : relation ev := λ x y,
        ppo E x y ∨ rfe E x y ∨ co E x y ∨ fr E x y.
      Conjecture ax_external : forall E, exec_wf E -> forall e, ~ tc (ob E) e e.
>>

    THAT STATEMENT IS FALSE for this model, and the counterexample is not
    exotic: it is a two-byte load.  Take three messages and one load,

      ts 1 : agent 0 stores byte [b]          (message [WMsg (base+1) [v1] _])
      ts 2 : agent 0 stores bytes [a],[b]     (message [WMsg base [v2;v2'] _])
      ts 3 : agent 1 stores byte [a]          (message [WMsg base [v3] _])
      then : agent 2 executes ONE load of the two bytes [a],[b] at [base],
             reading [a] from ts 3 and [b] from ts 1.

    Both byte reads are admissible: agent 2 has never touched either byte, so
    its floor [Nat.max vpre (coh a)] is 0 and [readable]'s forbidden window
    [(t, 0]] is empty for both.  But now, at EVENT granularity,

      ts3 --rfe--> load        (byte [a], and agent 1 ≠ agent 2)
      load --fr--> ts2         (byte [b]: the load read ts 1, and ts 2 > 1)
      ts2  --co--> ts3         (byte [a]: both write [a], 2 < 3)

    — a three-edge [ob] cycle.  It is an artefact of collapsing a multi-byte
    access into one event: RVWMO's global memory order is a total order over
    MEMORY OPERATIONS, and the operations of one misaligned/multi-byte access
    are distinct, mutually unordered operations (RVWMO §A.3: "a misaligned
    load or store may be decomposed into multiple memory operations", and
    program order relates instructions, hence never two operations of the same
    instruction).  The cycle above passes through the load TWICE, once per
    byte, and RVWMO's [ob] has no edge joining the two.

    SO: THE GLOBAL MEMORY ORDER OF THIS FILE IS A TOTAL ORDER ON OPERATIONS
    [mop := (byte, event)], not on events, and [ob] is stated there.  The
    per-byte relations ([rf_b], [co_b], [fr_b]) are already byte-indexed in
    slice 1 and lift with no change; the ppo fragment lifts by relating ALL
    operations of the source event to all operations of the target (which is
    what RVWMO does — ppo is an instruction-level relation lifted to the
    operations of those instructions), except at one seam recorded in §6.

    ------------------------------------------------------------------------
    WHERE EACH OPERATION SITS ([opos] below), AND WHY NOT AT ITS TIMESTAMP

    A WRITE operation sits at its message's timestamp: that is [gmo] and there
    is no choice.  For a READ operation the naive choice — the timestamp it
    read — is WRONG, and the reason is worth recording because it is the whole
    content of the construction.  Consider one agent doing

        load x (reads timestamp 7) ; fence r,r ; load y (reads timestamp 3)

    which is perfectly legal (nothing wrote [y] between 3 and 7).  ppo orders
    the two loads, so the second must sit LATER in the global order — but its
    timestamp is smaller.  The read's position is therefore not its timestamp
    but its VIEW: the machine's own [load_vpre] joined with the timestamp it
    read,

        opos(a, r) = max (timestamp r read at byte a) (load_vpre at r).

    This is sound exactly because [readable] is stated over the window
    [(t, Nat.max vpre (coh a)]]: the next write to [a] in coherence order is
    ABOVE the whole window, hence above [opos] — which is what keeps the read
    before its [fr] successors ([fr_gmo] below).  And it is complete for ppo
    because [ord_vrNew] (slice 1) says an ordering edge delivers the source's
    publication into the target's [w_vrNew], which [load_vpre] dominates.

    Ties are broken by (write before read at the same position), then by
    execution position, then by byte address — making the order TOTAL and the
    key INJECTIVE on operations. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakAxiomatic.

Local Open Scope Z_scope.

(* ================================================================== *)
(** * 1. Two missing [WeakMem] fold lemmas

    As in slice 1's "Missing [WeakMem] fold lemmas" section: these belong in
    [WeakMem.v] and are here because this slice may not edit it (sibling
    agents build against its [.vo]).  They are owed to the W4 lift batch. *)

(** An ACQUIRE load's own pre-view lands under its post-[w_vrNew] — the
    [w_vrNew] sibling of [WeakMem.load_post_at_vrNew_aq], but for [vpre]
    rather than for the timestamp.  Needed because [load_vpre] of an acquire
    joins [w_vRel], which is NOT below [w_vrNew] before the step. *)
Local Lemma load_post_fold_vrNew_aq_vpre vpre ats ws p :
  p ∈ ats →
  (vpre ≤ w_vrNew (foldl (λ w at_, load_post_at w true vpre at_.1 at_.2) ws ats))%nat.
Proof.
  revert ws. induction ats as [|q l IH]; intros ws Hin.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin]; [|by apply IH].
  simpl. etrans; [|apply ws_le_vrNew,
    (load_post_fold_le true vpre l (load_post_at ws true vpre p.1 p.2))].
  rewrite /load_post_at /=. lia.
Qed.

Lemma load_post_run_vrNew_aq_vpre ws base ts (j : nat) t :
  ts !! j = Some t →
  (load_vpre ws true ≤ w_vrNew (load_post_run ws true base ts))%nat.
Proof.
  intros Ht. pose proof (lookup_lt_Some _ _ _ Ht) as Hj.
  rewrite /load_post_run /load_post_bytes.
  apply (load_post_fold_vrNew_aq_vpre _ _ _ (acc_addr base j, t)).
  apply elem_of_list_lookup_2 with j.
  rewrite lookup_zip_with (lookup_seq_lt 0 (length ts) j Hj) Ht //.
Qed.

(** The [Forall] shape [load_post_run_bounded] wants, from an [rd_ok]. *)
Lemma rd_ok_ts_bounded img log ws aq base ts vs :
  rd_ok img log ws aq base ts vs →
  Forall (λ t, (t ≤ length log)%nat) ts.
Proof.
  intros [Hlen Hall]. apply Forall_lookup_2. intros j t Hj.
  destruct (lookup_lt_is_Some_2 vs j) as [v Hv].
  { rewrite Hlen. by eapply lookup_lt_Some. }
  destruct (Hall j t v Hj Hv) as [Hb _].
  eapply log_byte_bounded. by eexists.
Qed.

(* ================================================================== *)
(** * 2. The machine invariant along a run: every view is a real timestamp

    [WeakMem.ws_bounded] instantiated at the execution's own log.  Slice 1
    never needed it (its measures were all timestamps read off the trace);
    slice 2 does, because the read's position [opos] contains [load_vpre],
    and "the position of a read is below the log" is what makes a later write
    strictly above it. *)

Lemma exec_ws_bounded E k i :
  exec_wf E → (k ≤ length (ex_tr E))%nat →
  ws_bounded (ews E k i) (length (elog E k)).
Proof.
  intros Hwf. induction k as [|k IH]; intros Hk.
  { rewrite (exec_ws_init E i Hwf). apply ws_bounded_init. }
  destruct (exec_tr_lookup E k ltac:(lia)) as [s Hs].
  pose proof (exec_step_at E k s Hwf Hs) as Hstep.
  pose proof (IH ltac:(lia)) as Hb.
  pose proof (exec_log_len_le E k (S k) Hwf ltac:(lia) ltac:(lia)) as Hlen.
  destruct (decide (i = es_ag s)) as [->|Hne]; last first.
  { rewrite /ews (mstep_ws_ne _ _ _ _ i Hstep Hne).
    eapply ws_bounded_mono; [exact Hb|exact Hlen]. }
  destruct (es_lb s) as [aq base ts vs|rl base vs|pr pw sr sw|aq rl base ts rvs wvs]
    eqn:Hl.
  - (* load *)
    rewrite (exec_ws_load E k s aq base ts vs Hwf Hs Hl).
    pose proof (exec_rd_ok E k s base ts vs Hwf Hs ltac:(by rewrite Hl)) as Hrd.
    eapply ws_bounded_mono; [|exact Hlen].
    apply load_post_run_bounded; [exact Hb|].
    by eapply rd_ok_ts_bounded.
  - (* store *)
    rewrite (exec_ws_store E k s rl base vs Hwf Hs Hl).
    assert (Hts : ev_ts E (ev_at k) = length (elog E (S k))).
    { symmetry. by apply (ev_ts_next E k s Hwf Hs); rewrite Hl. }
    apply (store_post_run_bounded _ _ _ _ _ (length (elog E k)));
      [exact Hb|rewrite Hts; lia|exact Hlen].
  - (* fence *)
    rewrite (exec_ws_fence E k s pr pw sr sw Hwf Hs Hl).
    eapply ws_bounded_mono; [|exact Hlen]. by apply fence_post_bounded.
  - (* rmw *)
    rewrite (exec_ws_rmw E k s aq rl base ts rvs wvs Hwf Hs Hl).
    pose proof (exec_rd_ok E k s base ts rvs Hwf Hs ltac:(by rewrite Hl)) as Hrd.
    assert (Hts : ev_ts E (ev_at k) = length (elog E (S k))).
    { symmetry. by apply (ev_ts_next E k s Hwf Hs); rewrite Hl. }
    apply (store_post_run_bounded _ _ _ _ _ (length (elog E k)));
      [|rewrite Hts; lia|exact Hlen].
    apply load_post_run_bounded; [exact Hb|].
    by eapply rd_ok_ts_bounded.
Qed.

(* ================================================================== *)
(** * 3. [evpre]: the load pre-view an event ran at

    A total function on events (junk off the run, like slice 1's [stt]).  For
    a read event it is exactly the [load_vpre] its [readable] side conditions
    were checked against. *)

Definition evpre (E : exec) (e : ev) : nat :=
  match e with
  | ev_init => 0%nat
  | ev_at k =>
      match ex_tr E !! k with
      | Some s => load_vpre (ews E k (es_ag s)) (lb_aq (es_lb s))
      | None => 0%nat
      end
  end.

Lemma evpre_at E k s :
  ex_tr E !! k = Some s →
  evpre E (ev_at k) = load_vpre (ews E k (es_ag s)) (lb_aq (es_lb s)).
Proof. by move=> /= ->. Qed.

(** Bounded, like every other view. *)
Lemma evpre_le_log E k :
  exec_wf E → (k ≤ length (ex_tr E))%nat →
  (evpre E (ev_at k) ≤ length (elog E k))%nat.
Proof.
  intros Hwf Hk. rewrite /evpre. destruct (ex_tr E !! k) as [s|] eqn:Hs; [|lia].
  apply load_vpre_bounded. by apply exec_ws_bounded.
Qed.

(** A READ's pre-view is under the agent's [w_vrNew] IMMEDIATELY AFTER the
    step.  For a plain read this is trivial ([load_vpre] IS [w_vrNew] there);
    for an ACQUIRE it is the content of [load_post_at]'s [aq] arm, and it is
    what makes the pre-view monotone along an agent's program even though
    [load_vpre] joins the (non-monotone-looking) [w_vRel]. *)
Lemma evpre_le_vrNew_post E k s a t v :
  exec_wf E → ex_tr E !! k = Some s → reads_at E k a t v →
  (evpre E (ev_at k) ≤ w_vrNew (ews E (S k) (es_ag s)))%nat.
Proof.
  intros Hwf Hs Hr. rewrite (evpre_at E k s Hs).
  destruct Hr as (s' & base & ts & vs & j & Hs' & Hrd & Hj & Hv & Ha).
  assert (s' = s) as -> by (rewrite Hs in Hs'; by simplify_eq).
  destruct (lb_aq (es_lb s)) eqn:Haq; last first.
  { rewrite /load_vpre /= Nat.max_0_r.
    apply ws_le_vrNew, (exec_ws_le E k (S k) (es_ag s) Hwf ltac:(lia)).
    pose proof (lookup_lt_Some _ _ _ Hs). lia. }
  destruct (lb_rd_cases _ _ _ _ Hrd) as (aq & Haq' & [Hl|(rl & wvs & Hl)]);
    rewrite Haq in Haq'; subst aq.
  - rewrite (exec_ws_load E k s true base ts vs Hwf Hs Hl).
    by apply (load_post_run_vrNew_aq_vpre _ _ _ j t).
  - rewrite (exec_ws_rmw E k s true rl base ts vs wvs Hwf Hs Hl).
    etrans; [by apply (load_post_run_vrNew_aq_vpre _ base ts j t)|].
    apply ws_le_vrNew, store_post_run_le.
Qed.

(** ... hence the pre-view is monotone along one agent's program order. *)
Lemma evpre_mono E k1 k2 s1 s2 a t v :
  exec_wf E → (k1 < k2)%nat →
  ex_tr E !! k1 = Some s1 → ex_tr E !! k2 = Some s2 → es_ag s1 = es_ag s2 →
  reads_at E k1 a t v →
  (evpre E (ev_at k1) ≤ evpre E (ev_at k2))%nat.
Proof.
  intros Hwf Hlt Hs1 Hs2 Hag Hr.
  pose proof (lookup_lt_Some _ _ _ Hs2) as Hk2.
  etrans; [by eapply evpre_le_vrNew_post|].
  rewrite (evpre_at E k2 s2 Hs2) -Hag.
  etrans; [apply ws_le_vrNew,
    (exec_ws_le E (S k1) k2 (es_ag s1) Hwf ltac:(lia) ltac:(lia))|].
  rewrite Hag. apply load_vpre_vrNew.
Qed.

(** The other half of the same fact: a publication delivered into the target's
    [w_vrNew] is under the target's pre-view. *)
Lemma vrNew_le_evpre E k s :
  ex_tr E !! k = Some s →
  (w_vrNew (ews E k (es_ag s)) ≤ evpre E (ev_at k))%nat.
Proof. intros Hs. rewrite (evpre_at E k s Hs). apply load_vpre_vrNew. Qed.

(* ================================================================== *)
(** * 4. The global memory order

    An OPERATION [mop] is a pair (byte, event): the access event [e] performs
    at byte [a].  A write event has one operation per byte of its message, a
    load one per byte read, a fused RMW ONE operation per byte (its read half
    and its write half collapse — see §6's note, where atomicity is what makes
    that sound), and a fence none.  [gmo_op] is a total order on ALL pairs;
    only the pairs with [acc_b E a e] are genuine operations, and the extra
    junk pairs cost nothing (a bigger order, the same theorems). *)

Definition mop : Type := (Z * ev)%type.

(** The lexicographic key type and its order: position, then
    (writes before reads at the same position), then execution position, then
    byte address.  The last two components exist only to make the key
    INJECTIVE, hence the order total. *)
Definition kless (p q : nat * nat * nat * Z) : Prop :=
  (p.1.1.1 < q.1.1.1)%nat ∨
  (p.1.1.1 = q.1.1.1 ∧
   ((p.1.1.2 < q.1.1.2)%nat ∨
    (p.1.1.2 = q.1.1.2 ∧
     ((p.1.2 < q.1.2)%nat ∨ (p.1.2 = q.1.2 ∧ (p.2 < q.2)))))).

Lemma kless_trans p q r : kless p q → kless q r → kless p r.
Proof. rewrite /kless. lia. Qed.

Lemma kless_irrefl p : ¬ kless p p.
Proof. rewrite /kless. lia. Qed.

Lemma kless_total p q : kless p q ∨ p = q ∨ kless q p.
Proof.
  destruct p as [[[a b] c] d], q as [[[a' b'] c'] d']. rewrite /kless /=.
  destruct (decide (a = a')) as [->|Hne]; last first.
  { destruct (decide (a < a')%nat); [left|right;right]; lia. }
  destruct (decide (b = b')) as [->|Hne']; last first.
  { destruct (decide (b < b')%nat); [left|right;right]; lia. }
  destruct (decide (c = c')) as [->|Hne'']; last first.
  { destruct (decide (c < c')%nat); [left|right;right]; lia. }
  destruct (decide (d = d')) as [->|Hne''']; last first.
  { destruct (decide (d < d')%Z); [left|right;right]; lia. }
  by right; left.
Qed.

Lemma tc_kless {A} (R : relation A) (f : A → nat * nat * nat * Z) :
  (∀ x y, R x y → kless (f x) (f y)) → ∀ x, ¬ tc R x x.
Proof.
  intros Hf x Hc.
  assert (Hall : ∀ y z, tc R y z → kless (f y) (f z)).
  { intros y z Hyz. induction Hyz as [y z Hr|y z u Hr _ IH];
      [by apply Hf|]. eapply kless_trans; [by apply Hf|exact IH]. }
  by apply (kless_irrefl (f x)), Hall.
Qed.

(** THE POSITION OF AN OPERATION.  A write sits at its own timestamp; a read
    sits at its timestamp JOINED WITH THE VIEW IT RAN AT (see the header). *)
Definition opos (E : exec) (a : Z) (e : ev) : nat :=
  if writesb E a e then ev_ts E e else Nat.max (ets E a e) (evpre E e).

Definition ophase (E : exec) (a : Z) (e : ev) : nat :=
  if writesb E a e then 0%nat else 1%nat.

Definition okey (E : exec) (o : mop) : nat * nat * nat * Z :=
  (opos E o.1 o.2, ophase E o.1 o.2, ev_ix o.2, o.1).

Definition gmo_op (E : exec) : relation mop := λ o1 o2, kless (okey E o1) (okey E o2).

(** *** The order's structural properties *)

Lemma gmo_op_trans E o1 o2 o3 : gmo_op E o1 o2 → gmo_op E o2 o3 → gmo_op E o1 o3.
Proof. apply kless_trans. Qed.

Lemma gmo_op_irrefl E o : ¬ gmo_op E o o.
Proof. apply kless_irrefl. Qed.

Lemma ev_ix_inj e1 e2 : ev_ix e1 = ev_ix e2 → e1 = e2.
Proof. destruct e1, e2; simpl; congruence. Qed.

Lemma okey_inj E o1 o2 : okey E o1 = okey E o2 → o1 = o2.
Proof.
  destruct o1 as [a1 e1], o2 as [a2 e2]. rewrite /okey /=.
  intros Heq. injection Heq. intros -> Hix _ _.
  by rewrite (ev_ix_inj e1 e2 Hix).
Qed.

Lemma gmo_op_total E o1 o2 : gmo_op E o1 o2 ∨ o1 = o2 ∨ gmo_op E o2 o1.
Proof.
  rewrite /gmo_op. destruct (kless_total (okey E o1) (okey E o2)) as [?|[Heq|?]];
    [by left| |by right; right].
  right; left. exact (okey_inj E o1 o2 Heq).
Qed.

(** *** Reading [opos] and [ophase] off an event *)

(** [wr_b] is decidable (via slice 1's boolean [writesb]) — used to split
    every edge proof into its write and read arms. *)
Lemma wr_b_dec E a e : wr_b E a e ∨ ¬ wr_b E a e.
Proof.
  destruct (writesb E a e) eqn:Hb.
  - left. by apply writesb_spec.
  - right. intros H. by rewrite (proj2 (writesb_spec E a e) H) in Hb.
Qed.

Lemma opos_wr E a e : wr_b E a e → opos E a e = ev_ts E e.
Proof. intros H. rewrite /opos (proj2 (writesb_spec E a e) H) //. Qed.

Lemma ophase_wr E a e : wr_b E a e → ophase E a e = 0%nat.
Proof. intros H. rewrite /ophase (proj2 (writesb_spec E a e) H) //. Qed.

Lemma opos_nwr E a e :
  ¬ wr_b E a e → opos E a e = Nat.max (ets E a e) (evpre E e).
Proof. intros H. rewrite /opos (writesb_false E a e H) //. Qed.

Lemma ophase_nwr E a e : ¬ wr_b E a e → ophase E a e = 1%nat.
Proof. intros H. rewrite /ophase (writesb_false E a e H) //. Qed.

(** A read operation's position is at least the timestamp it read. *)
Lemma opos_rd_ge E a k t v :
  ¬ wr_b E a (ev_at k) → reads_at E k a t v → (t ≤ opos E a (ev_at k))%nat.
Proof.
  intros Hn Hr. rewrite (opos_nwr E a _ Hn) (ets_rd E a k t v Hn Hr). lia.
Qed.

(** A [lb_rd_ts] hit IS a read of that byte — the converse direction of
    [reads_at_lb_rd_ts], needed to bound [ets] on a non-writing event. *)
Lemma lb_rd_ts_reads E k s a t :
  exec_wf E → ex_tr E !! k = Some s → lb_rd_ts (es_lb s) a = Some t →
  ∃ v, reads_at E k a t v.
Proof.
  intros Hwf Hs. rewrite /lb_rd_ts.
  destruct (lb_rd (es_lb s)) as [[[base ts] vs]|] eqn:Hrd; [|done].
  case_bool_decide as Hle; [|done]. intros Hj.
  destruct (exec_rd_ok E k s base ts vs Hwf Hs Hrd) as [Hlen _].
  destruct (lookup_lt_is_Some_2 vs (Z.to_nat (a - base))) as [v Hv].
  { rewrite Hlen. by eapply lookup_lt_Some. }
  exists v, s, base, ts, vs, (Z.to_nat (a - base)).
  split_and!; [done|done|done|done|rewrite /acc_addr; lia].
Qed.

(** Positions are inside the log: an operation of step [k] sits at or below
    the log length just AFTER the step (exactly at it, for a write). *)
Lemma ets_le_log E a k :
  exec_wf E → (k < length (ex_tr E))%nat → ¬ wr_b E a (ev_at k) →
  (ets E a (ev_at k) ≤ length (elog E k))%nat.
Proof.
  intros Hwf Hk Hn. rewrite /ets (writesb_false E a _ Hn).
  destruct (ex_tr E !! k) as [s|] eqn:Hs; [|lia].
  destruct (lb_rd_ts (es_lb s) a) as [t|] eqn:Ht; [|simpl; lia].
  destruct (lb_rd_ts_reads E k s a t Hwf Hs Ht) as [v Hr]. simpl.
  by eapply reads_at_ts_le.
Qed.

Lemma opos_le_log E a k :
  exec_wf E → (k < length (ex_tr E))%nat → ¬ wr_b E a (ev_at k) →
  (opos E a (ev_at k) ≤ length (elog E k))%nat.
Proof.
  intros Hwf Hk Hn. rewrite (opos_nwr E a _ Hn).
  pose proof (ets_le_log E a k Hwf Hk Hn).
  pose proof (evpre_le_log E k Hwf ltac:(lia)). lia.
Qed.

Lemma opos_le_next E a k :
  exec_wf E → (k < length (ex_tr E))%nat →
  (opos E a (ev_at k) ≤ length (elog E (S k)))%nat.
Proof.
  intros Hwf Hk.
  destruct (wr_b_dec E a (ev_at k)) as [Hw|Hn]; last first.
  { pose proof (opos_le_log E a k Hwf Hk Hn).
    pose proof (exec_log_len_le E k (S k) Hwf ltac:(lia) ltac:(lia)). lia. }
  rewrite (opos_wr E a _ Hw). destruct Hw as [HW _]. destruct HW as (s & Hs & Hlw).
  rewrite (ev_ts_next E k s Hwf Hs Hlw). lia.
Qed.

(** A write's position is strictly above everything the log held before it. *)
Lemma opos_wr_gt E a2 k2 :
  exec_wf E → wr_b E a2 (ev_at k2) →
  (length (elog E k2) < opos E a2 (ev_at k2))%nat.
Proof.
  intros Hwf Hw. rewrite (opos_wr E a2 _ Hw) ev_ts_at. lia.
Qed.

(* ================================================================== *)
(** * 5. The characteristic properties of the order

    [co] / [rf] / [fr] all point forward in [gmo_op], and nothing writes the
    same byte between an [rf] edge's endpoints.  These are the four properties
    an RVWMO global memory order is required to have (RVWMO's load-value axiom
    is precisely the [rf] pair of them). *)

(** The three shapes in which an edge is discharged. *)
Lemma gmo_op_lt E a1 e1 a2 e2 :
  (opos E a1 e1 < opos E a2 e2)%nat → gmo_op E (a1, e1) (a2, e2).
Proof. intros H. rewrite /gmo_op /okey /kless /=. by left. Qed.

Lemma gmo_op_wr_rd E a1 e1 a2 e2 :
  (opos E a1 e1 ≤ opos E a2 e2)%nat → wr_b E a1 e1 → ¬ wr_b E a2 e2 →
  gmo_op E (a1, e1) (a2, e2).
Proof.
  intros Hle Hw Hn. rewrite /gmo_op /okey /kless /=.
  rewrite (ophase_wr E a1 e1 Hw) (ophase_nwr E a2 e2 Hn).
  destruct (decide (opos E a1 e1 = opos E a2 e2)) as [Heq|Hne];
    [right; split; [exact Heq|left; lia]|left; lia].
Qed.

Lemma gmo_op_ix E a1 e1 a2 e2 :
  (opos E a1 e1 ≤ opos E a2 e2)%nat → ophase E a1 e1 = ophase E a2 e2 →
  (ev_ix e1 < ev_ix e2)%nat → gmo_op E (a1, e1) (a2, e2).
Proof.
  intros Hle Hph Hix. rewrite /gmo_op /okey /kless /=.
  destruct (decide (opos E a1 e1 = opos E a2 e2)) as [Heq|Hne]; [|left; lia].
  right. split; [exact Heq|]. right. split; [exact Hph|]. by left.
Qed.

(** (i) WRITES AGREE WITH [gmo]: on the writes of one byte, the order IS
    coherence order — in both directions. *)
Lemma co_gmo E a w1 w2 : co_b E a w1 w2 → gmo_op E (a, w1) (a, w2).
Proof.
  intros (Hw1 & Hw2 & Hlt). apply gmo_op_lt.
  by rewrite (opos_wr E a w1 Hw1) (opos_wr E a w2 Hw2).
Qed.

Lemma gmo_co E a w1 w2 :
  exec_wf E → wr_b E a w1 → wr_b E a w2 →
  gmo_op E (a, w1) (a, w2) → co_b E a w1 w2.
Proof.
  intros Hwf Hw1 Hw2 Hg. split_and!; [exact Hw1|exact Hw2|].
  rewrite /gmo_op /okey /kless /= (opos_wr E a w1 Hw1) (opos_wr E a w2 Hw2)
          (ophase_wr E a w1 Hw1) (ophase_wr E a w2 Hw2) in Hg.
  destruct Hg as [Hlt|(Heq & [Hlt|(_ & [Hix|(Hix & Ha)])])]; [exact Hlt| | |].
  - lia.
  - exfalso. rewrite (ev_ts_inj E w1 w2 Hwf (proj1 Hw1) (proj1 Hw2) Heq) in Hix.
    lia.
  - exfalso. lia.
Qed.

(** (ii) AN [rf] SOURCE PRECEDES ITS READER. *)
Lemma rf_gmo E a w r : exec_wf E → rf_b E a w r → gmo_op E (a, w) (a, r).
Proof.
  intros Hwf Hrf. pose proof Hrf as [Hw (k & t & v & -> & Hr & Hts)].
  destruct (wr_b_dec E a (ev_at k)) as [Hwr|Hn].
  - apply gmo_op_lt.
    rewrite (opos_wr E a w Hw) (opos_wr E a _ Hwr) Hts ev_ts_at.
    pose proof (reads_at_ts_le E k a t v Hwf Hr). lia.
  - apply gmo_op_wr_rd; [|exact Hw|exact Hn].
    rewrite (opos_wr E a w Hw) Hts. by eapply opos_rd_ge.
Qed.

(** (iii) A READ IS BEFORE EVERY [co]-LATER WRITE OF ITS BYTE.

    THE HEART OF THE CONSTRUCTION.  For a plain read this is [readable]'s
    window argument: the read's position is inside [(t, max vpre (coh a)]]'s
    closure, and a write to [a] above [t] cannot be in that window, so it is
    above the position.  For an RMW (whose read and write halves are ONE
    operation, sitting at the write timestamp) it is instead the ATOMICITY
    axiom that pushes the [co]-later write above it. *)
Lemma read_gap E k s a t v w :
  exec_wf E → ex_tr E !! k = Some s → reads_at E k a t v →
  wr_b E a w → (t < ev_ts E w)%nat →
  (Nat.max t (evpre E (ev_at k)) < ev_ts E w)%nat.
Proof.
  intros Hwf Hs Hr Hw Hgt.
  pose proof (lookup_lt_Some _ _ _ Hs) as Hk.
  destruct (reads_at_byte_rd E k a t v Hwf Hr) as (s' & Hs' & [_ Hread]).
  assert (s' = s) as -> by (rewrite Hs in Hs'; by simplify_eq).
  destruct Hread as [_ Hnw].
  rewrite (evpre_at E k s Hs).
  destruct (decide (ev_ts E w ≤
                    load_vpre (ews E k (es_ag s)) (lb_aq (es_lb s)))%nat)
    as [Hle|Hgt']; [|lia]. exfalso.
  pose proof (evpre_le_log E k Hwf ltac:(lia)) as Hbnd.
  rewrite (evpre_at E k s Hs) in Hbnd.
  apply Hnw. apply (writes_in_log_byte (eimg E k)). exists (ev_ts E w).
  split_and!; [lia|lia|].
  rewrite -(log_byte_final E k (ev_ts E w) a Hwf ltac:(lia) ltac:(lia)).
  exact (proj2 Hw).
Qed.

Lemma fr_gmo E a r w : exec_wf E → fr_b E a r w → gmo_op E (a, r) (a, w).
Proof.
  intros Hwf [(w0 & Hrf & Hco) Hne].
  pose proof Hco as (Hw0 & Hw & Hlt).
  pose proof Hrf as [_ (k & t & v & -> & Hr & Hts)].
  destruct (wr_b_dec E a (ev_at k)) as [Hwr|Hn].
  - (* the reader is an RMW: atomicity leaves no room *)
    apply gmo_op_lt. rewrite (opos_wr E a _ Hwr) (opos_wr E a w Hw).
    assert (Hnl : ¬ (ev_ts E w < ev_ts E (ev_at k))%nat).
    { apply (sound_atomicity E Hwf k a w0 w (proj1 Hwr) Hrf Hw). lia. }
    destruct (decide (ev_ts E w = ev_ts E (ev_at k))) as [Heq|Hne']; [|lia].
    exfalso. apply Hne.
    exact (ev_ts_inj E (ev_at k) w Hwf (proj1 Hwr) (proj1 Hw) (eq_sym Heq)).
  - (* a plain read: [readable]'s window *)
    apply gmo_op_lt.
    rewrite (opos_nwr E a _ Hn) (ets_rd E a k t v Hn Hr) (opos_wr E a w Hw).
    destruct Hr as (s & base & ts & vs & j & Hs & Hrd & Hj & Hv & Ha).
    eapply (read_gap E k s a t v w Hwf Hs); [by exists s, base, ts, vs, j|
      exact Hw|lia].
Qed.

(** (iv) NO WRITE OF THE SAME BYTE SITS BETWEEN AN [rf] EDGE'S ENDPOINTS.
    With (ii) and (iii) this is exactly RVWMO's load-value axiom, transcribed
    to the constructed order. *)
Lemma rf_gmo_tight E a w r w' :
  exec_wf E → rf_b E a w r → wr_b E a w' →
  ¬ (gmo_op E (a, w) (a, w') ∧ gmo_op E (a, w') (a, r)).
Proof.
  intros Hwf Hrf Hw' [H1 H2].
  destruct (decide (r = w')) as [->|Hne].
  { by apply (gmo_op_irrefl E (a, w')). }
  apply (gmo_op_irrefl E (a, w')).
  eapply gmo_op_trans; [exact H2|].
  apply (fr_gmo E a r w' Hwf). split; [|exact Hne].
  exists w. split; [exact Hrf|].
  apply (gmo_co E a w w' Hwf (proj1 Hrf) Hw' H1).
Qed.

(* ================================================================== *)
(** * 6. [ob]-acyclicity

    The preserved program order, lifted to operations.  Four arms:

    - [po] INTO A WRITE operation.  In a promise-free machine a store always
      appends at the log's top, so it is above everything its agent has
      already done — no fence needed.  This SUBSUMES RVWMO's ppo rules whose
      successor is a store (rules 1–3 with [b] a store, and rule 4's succ-W
      cases), which is why the fence bits below only mention succ-R.
    - [po_loc] on ONE byte (RVWMO ppo rules 1–3): slice 1's [po_loc_b].
    - a FENCE with pred-W, succ-R between a WRITE operation and the target
      (slice 1's [ord_pw]); the source publishes its own timestamp.
    - a FENCE with pred-R, succ-R, or an ACQUIRE (slice 1's [ord_pr]),
      from a READ operation whose timestamp is PUBLISHED ([pub_r]).

    TWO RECORDED SEAMS, both inherited from slice 1's ppo fragment rather than
    introduced here:

    (a) the [ord_pr] arm requires the source operation NOT to write its byte.
        The excluded case is a fused RMW's operation at a byte it writes: our
        operation sits at the RMW's WRITE timestamp, while a pred-R fence
        publishes only its READ half's timestamp, so claiming the edge would
        be unsound for this order.  (RVWMO orders the RMW's read operation,
        which our fusion has no separate name for.  Slice 1's [ax_ord] makes
        the same restriction — its conclusion is about the published [t].)

    (b) [pub_r] excludes an INTERNAL (forwarded) rf source and there is no
        release-successor arm: slice 1's §7(3) gaps, unchanged here. *)

Lemma ord_pw_shape E e1 e2 :
  ord_pw E e1 e2 →
  ∃ k1 k2 s1 s2, e1 = ev_at k1 ∧ e2 = ev_at k2 ∧ (k1 < k2)%nat ∧
    ex_tr E !! k1 = Some s1 ∧ ex_tr E !! k2 = Some s2 ∧ es_ag s1 = es_ag s2.
Proof.
  intros (k1 & k2 & pr & sw & -> & -> &
          (kf & sf & s1 & s2 & Hlt1 & Hlt2 & Hs1 & Hsf & Hs2 & Hag1 & Hag2 & _)).
  exists k1, k2, s1, s2. split_and!; [done|done|lia|done|done|congruence].
Qed.

Lemma ord_pr_shape E e1 e2 :
  ord_pr E e1 e2 →
  ∃ k1 k2 s1 s2, e1 = ev_at k1 ∧ e2 = ev_at k2 ∧ (k1 < k2)%nat ∧
    ex_tr E !! k1 = Some s1 ∧ ex_tr E !! k2 = Some s2 ∧ es_ag s1 = es_ag s2.
Proof.
  intros [(k1 & k2 & pw & sw & -> & -> &
           (kf & sf & s1 & s2 & Hlt1 & Hlt2 & Hs1 & Hsf & Hs2 & Hag1 & Hag2 & _))
         |(k1 & k2 & s1 & s2 & -> & -> & Hlt & Hs1 & Hs2 & Hag & _ & _)].
  - exists k1, k2, s1, s2. split_and!; [done|done|lia|done|done|congruence].
  - exists k1, k2, s1, s2. by split_and!.
Qed.

(** *** The four ppo arms embed *)

Lemma ppo_w_gmo E a1 e1 a2 e2 :
  exec_wf E → po E e1 e2 → wr_b E a2 e2 → gmo_op E (a1, e1) (a2, e2).
Proof.
  intros Hwf (k1 & k2 & s1 & s2 & -> & -> & Hlt & Hs1 & Hs2 & Hag) Hw2.
  pose proof (lookup_lt_Some _ _ _ Hs1) as Hk1.
  pose proof (lookup_lt_Some _ _ _ Hs2) as Hk2.
  apply gmo_op_lt.
  pose proof (opos_le_next E a1 k1 Hwf ltac:(lia)).
  pose proof (exec_log_len_le E (S k1) k2 Hwf ltac:(lia) ltac:(lia)).
  pose proof (opos_wr_gt E a2 k2 Hwf Hw2). lia.
Qed.

Lemma ppo_loc_gmo E a e1 e2 :
  exec_wf E → po_loc_b E a e1 e2 → gmo_op E (a, e1) (a, e2).
Proof.
  intros Hwf (Hpo & Hacc1 & Hacc2).
  destruct (wr_b_dec E a e2) as [Hw2|Hn2]; [by eapply ppo_w_gmo|].
  pose proof Hpo as (k1 & k2 & s1 & s2 & -> & -> & Hlt & Hs1 & Hs2 & Hag).
  pose proof (touches_mono E k1 k2 s1 s2 a (ets E a (ev_at k1))
                (ets E a (ev_at k2)) Hwf Hlt Hs1 Hs2 Hag
                (acc_touches E a k1 Hacc1) (acc_touches E a k2 Hacc2)) as Hts.
  destruct (wr_b_dec E a (ev_at k1)) as [Hw1|Hn1].
  - apply gmo_op_wr_rd; [|exact Hw1|exact Hn2].
    rewrite (opos_wr E a _ Hw1) -(ets_wr E a _ Hw1) (opos_nwr E a _ Hn2). lia.
  - apply gmo_op_ix;
      [|by rewrite (ophase_nwr E a _ Hn1) (ophase_nwr E a _ Hn2)|simpl; lia].
    rewrite (opos_nwr E a _ Hn1) (opos_nwr E a _ Hn2).
    destruct Hacc1 as [Hw|(k & t1 & v1 & Hk & Hr1)]; [by destruct (Hn1 Hw)|].
    assert (k = k1) as -> by (by simplify_eq).
    pose proof (evpre_mono E k1 k2 s1 s2 a t1 v1 Hwf Hlt Hs1 Hs2 Hag Hr1). lia.
Qed.

Lemma ppo_ord_pw_gmo E a1 e1 a2 e2 :
  exec_wf E → ord_pw E e1 e2 → wr_b E a1 e1 → gmo_op E (a1, e1) (a2, e2).
Proof.
  intros Hwf Hord Hw1.
  pose proof (ord_pw_shape E e1 e2 Hord)
    as (k1 & k2 & s1 & s2 & -> & -> & Hlt & Hs1 & Hs2 & Hag).
  pose proof (lookup_lt_Some _ _ _ Hs2) as Hk2.
  assert (Hpub : pub_w E (ev_at k1) (ev_ts E (ev_at k1))).
  { split_and!; [exact (proj1 Hw1)|by eexists|done]. }
  pose proof (ord_vrNew E (ev_at k1) (ev_ts E (ev_at k1)) k2 s2 Hwf Hs2
                (or_introl (conj Hord Hpub))) as Hvr.
  pose proof (exec_ws_bounded E k2 (es_ag s2) Hwf ltac:(lia))
    as (_ & _ & Hrn & _ & _ & _ & _).
  destruct (wr_b_dec E a2 (ev_at k2)) as [Hw2|Hn2].
  - apply gmo_op_lt.
    rewrite (opos_wr E a1 _ Hw1) (opos_wr E a2 _ Hw2) (ev_ts_at E k2). lia.
  - apply gmo_op_wr_rd; [|exact Hw1|exact Hn2].
    rewrite (opos_wr E a1 _ Hw1) (opos_nwr E a2 _ Hn2).
    pose proof (vrNew_le_evpre E k2 s2 Hs2). lia.
Qed.

Lemma ppo_ord_pr_gmo E a1 e1 a2 e2 :
  exec_wf E → ord_pr E e1 e2 → ¬ wr_b E a1 e1 → pub_r E e1 (ets E a1 e1) →
  gmo_op E (a1, e1) (a2, e2).
Proof.
  intros Hwf Hord Hn1 Hpub.
  pose proof (ord_pr_shape E e1 e2 Hord)
    as (k1 & k2 & s1 & s2 & -> & -> & Hlt & Hs1 & Hs2 & Hag).
  pose proof (lookup_lt_Some _ _ _ Hs2) as Hk2.
  pose proof (ord_vrNew E (ev_at k1) (ets E a1 (ev_at k1)) k2 s2 Hwf Hs2
                (or_intror (conj Hord Hpub))) as Hvr.
  assert (Hep : (evpre E (ev_at k1) ≤ w_vrNew (ews E k2 (es_ag s2)))%nat).
  { destruct Hpub as (k & s & a & v & Hk & Hs & Hr & _).
    assert (k = k1) as -> by (by simplify_eq).
    assert (s = s1) as -> by (rewrite Hs1 in Hs; by simplify_eq).
    etrans; [by eapply evpre_le_vrNew_post|].
    rewrite -Hag. apply ws_le_vrNew,
      (exec_ws_le E (S k1) k2 (es_ag s1) Hwf ltac:(lia) ltac:(lia)). }
  pose proof (exec_ws_bounded E k2 (es_ag s2) Hwf ltac:(lia))
    as (_ & _ & Hrn & _ & _ & _ & _).
  destruct (wr_b_dec E a2 (ev_at k2)) as [Hw2|Hn2].
  - apply gmo_op_lt.
    rewrite (opos_nwr E a1 _ Hn1) (opos_wr E a2 _ Hw2) (ev_ts_at E k2). lia.
  - apply gmo_op_ix;
      [|by rewrite (ophase_nwr E a1 _ Hn1) (ophase_nwr E a2 _ Hn2)|simpl; lia].
    rewrite (opos_nwr E a1 _ Hn1) (opos_nwr E a2 _ Hn2).
    pose proof (vrNew_le_evpre E k2 s2 Hs2). lia.
Qed.

(** *** [ob] and the theorem *)

Definition ppo_op (E : exec) : relation mop := λ o1 o2,
  (po E o1.2 o2.2 ∧ wr_b E o2.1 o2.2)
  ∨ (o1.1 = o2.1 ∧ po_loc_b E o1.1 o1.2 o2.2)
  ∨ (ord_pw E o1.2 o2.2 ∧ wr_b E o1.1 o1.2)
  ∨ (ord_pr E o1.2 o2.2 ∧ ¬ wr_b E o1.1 o1.2 ∧ pub_r E o1.2 (ets E o1.1 o1.2)).

Definition rf_op (E : exec) : relation mop := λ o1 o2,
  o1.1 = o2.1 ∧ rf_b E o1.1 o1.2 o2.2.
Definition co_op (E : exec) : relation mop := λ o1 o2,
  o1.1 = o2.1 ∧ co_b E o1.1 o1.2 o2.2.
Definition fr_op (E : exec) : relation mop := λ o1 o2,
  o1.1 = o2.1 ∧ fr_b E o1.1 o1.2 o2.2.

(** NOTE: the union takes FULL [rf], not just [rfe].  The herd-style [ob]
    excludes [rfi] because a forwarded internal read need not be ordered after
    its source in the global order; here it always is ([opos] of a read
    dominates the timestamp it read), so keeping [rfi] makes the theorem
    strictly stronger. *)
Definition ob_op (E : exec) : relation mop := λ o1 o2,
  ppo_op E o1 o2 ∨ rf_op E o1 o2 ∨ co_op E o1 o2 ∨ fr_op E o1 o2.

Lemma ppo_op_gmo E o1 o2 : exec_wf E → ppo_op E o1 o2 → gmo_op E o1 o2.
Proof.
  intros Hwf Hppo. destruct o1 as [a1 e1], o2 as [a2 e2].
  rewrite /ppo_op /= in Hppo.
  destruct Hppo as [[Hpo Hw2]|[[<- Hpl]|[[Hord Hw1]|(Hord & Hn1 & Hpub)]]].
  - by eapply ppo_w_gmo.
  - by eapply ppo_loc_gmo.
  - by eapply ppo_ord_pw_gmo.
  - by eapply ppo_ord_pr_gmo.
Qed.

Lemma ob_op_gmo E o1 o2 : exec_wf E → ob_op E o1 o2 → gmo_op E o1 o2.
Proof.
  intros Hwf Hob. destruct o1 as [a1 e1], o2 as [a2 e2].
  rewrite /ob_op /rf_op /co_op /fr_op /= in Hob.
  destruct Hob as [Hppo|[[<- Hrf]|[[<- Hco]|[<- Hfr]]]];
    [by eapply ppo_op_gmo| | |].
  - by apply rf_gmo.
  - by apply co_gmo.
  - by apply fr_gmo.
Qed.

(** THE SLICE-2 THEOREM: the global external axiom, over operations. *)
Theorem promise_free_ob_acyclic E :
  exec_wf E → ∀ o, ¬ tc (ob_op E) o o.
Proof.
  intros Hwf. apply (tc_kless _ (okey E)).
  intros x y Hxy. by apply ob_op_gmo.
Qed.

(** ... and the same statement in "there is a global memory order" form: a
    total, transitive, irreflexive relation containing [ob]. *)
Theorem promise_free_gmo E :
  exec_wf E →
  (∀ o1 o2 o3, gmo_op E o1 o2 → gmo_op E o2 o3 → gmo_op E o1 o3) ∧
  (∀ o, ¬ gmo_op E o o) ∧
  (∀ o1 o2, gmo_op E o1 o2 ∨ o1 = o2 ∨ gmo_op E o2 o1) ∧
  (∀ o1 o2, ob_op E o1 o2 → gmo_op E o1 o2) ∧
  (∀ a w1 w2, wr_b E a w1 → wr_b E a w2 →
     (gmo_op E (a, w1) (a, w2) ↔ co_b E a w1 w2)) ∧
  (∀ a w r w', rf_b E a w r → wr_b E a w' →
     ¬ (gmo_op E (a, w) (a, w') ∧ gmo_op E (a, w') (a, r))).
Proof.
  intros Hwf. split_and!.
  - intros o1 o2 o3. apply gmo_op_trans.
  - apply gmo_op_irrefl.
  - apply gmo_op_total.
  - intros o1 o2. by apply ob_op_gmo.
  - intros a w1 w2 Hw1 Hw2. split; [by apply gmo_co|apply co_gmo].
  - intros a w r w'. by apply rf_gmo_tight.
Qed.

(* ================================================================== *)
(** * 7. Completeness: replaying a candidate on the machine

    Slice 1's §7(1) asked for
    "axiomatically-consistent candidate ⇒ machine-reachable".  This section
    lands the REACHABILITY CONSTRUCTION in full generality — a candidate is
    (image, trace), the machine's post-state is a FUNCTION of the label
    ([mnext]), so replaying is a fold and [exec_wf] reduces to a per-step side
    condition [mstep_ok] — and then discharges that side condition for a
    precisely delimited class of candidates (§7.3).  What does NOT close is
    recorded as a conjecture in §8, with the exact missing invariant. *)

(** ** 7.1 The machine step, as a function plus a side condition *)

Definition mnext (σ : mstate) (i : agent) (l : lbl) : mstate :=
  match l with
  | LLoad aq base ts vs =>
      MSt (ms_img σ) (ms_log σ)
        (upd_ws (ms_ws σ) i (load_post_run (ms_ws σ i) aq base ts))
  | LStore rl base vs =>
      MSt (ms_img σ) (ms_log σ ++ [WMsg base vs (Some i)])
        (upd_ws (ms_ws σ) i
           (store_post_run (ms_ws σ i) rl base (length vs) (S (length (ms_log σ)))))
  | LFence pr pw sr sw =>
      MSt (ms_img σ) (ms_log σ)
        (upd_ws (ms_ws σ) i (fence_post (ms_ws σ i) pr pw sr sw))
  | LRmw aq rl base ts rvs wvs =>
      MSt (ms_img σ) (ms_log σ ++ [WMsg base wvs (Some i)])
        (upd_ws (ms_ws σ) i
           (store_post_run (load_post_run (ms_ws σ i) aq base ts) rl base
              (length wvs) (S (length (ms_log σ)))))
  end.

Definition mstep_ok (σ : mstate) (i : agent) (l : lbl) : Prop :=
  match l with
  | LLoad aq base ts vs => rd_ok (ms_img σ) (ms_log σ) (ms_ws σ i) aq base ts vs
  | LStore rl base vs => vs ≠ []
  | LFence _ _ _ _ => True
  | LRmw aq rl base ts rvs wvs =>
      wvs ≠ [] ∧ length wvs = length ts ∧
      rd_ok (ms_img σ) (ms_log σ) (ms_ws σ i) aq base ts rvs ∧
      rmw_latest (ms_img σ) (ms_log σ) base ts
  end.

Lemma mstep_ok_step σ i l : mstep_ok σ i l → mstep σ i l (mnext σ i l).
Proof.
  destruct l; simpl.
  - intros Hrd. by apply MStepLoad.
  - intros Hne. by apply MStepStore.
  - intros _. by apply MStepFence.
  - intros (Hne & Hlen & Hrd & Hlat). by apply MStepRmw.
Qed.

Lemma mstep_det σ i l σ' : mstep σ i l σ' → σ' = mnext σ i l ∧ mstep_ok σ i l.
Proof. inversion 1; simplify_eq/=; by split_and!. Qed.

(** ** 7.2 The replay *)

Fixpoint replay (σ : mstate) (tr : list estep) : list mstate :=
  σ :: match tr with
       | [] => []
       | s :: tr' => replay (mnext σ (es_ag s) (es_lb s)) tr'
       end.

Lemma replay_length σ tr : length (replay σ tr) = S (length tr).
Proof.
  revert σ. induction tr as [|s tr IH]; intros σ; [done|].
  by rewrite /= IH.
Qed.

Lemma replay_0 σ tr : replay σ tr !! 0%nat = Some σ.
Proof. by destruct tr. Qed.

Lemma replay_step σ tr k s σk :
  tr !! k = Some s → replay σ tr !! k = Some σk →
  replay σ tr !! S k = Some (mnext σk (es_ag s) (es_lb s)).
Proof.
  revert σ k. induction tr as [|s0 tr IH]; intros σ k Hs Hσ.
  { by rewrite lookup_nil in Hs. }
  destruct k as [|k].
  - simpl in Hs. simplify_eq. simpl in Hσ. simplify_eq. by rewrite /= replay_0.
  - simpl in Hs. rewrite /= in Hσ |- *. by apply IH.
Qed.

(** The messages a trace appends, and the log at each prefix — both functions
    of the candidate alone, no machine state involved. *)
Definition es_msg (s : estep) : list wmsg :=
  match lb_wr (es_lb s) with
  | Some (base, vs) => [WMsg base vs (Some (es_ag s))]
  | None => []
  end.

Fixpoint tr_msgs (tr : list estep) : list wmsg :=
  match tr with [] => [] | s :: tr' => es_msg s ++ tr_msgs tr' end.

Lemma mnext_log σ i l :
  ms_log (mnext σ i l) = ms_log σ ++ es_msg (EStep i l).
Proof. destruct l; rewrite /es_msg /=; by rewrite ?app_nil_r. Qed.

Lemma mnext_img σ i l : ms_img (mnext σ i l) = ms_img σ.
Proof. by destruct l. Qed.

Lemma replay_log σ tr k σk :
  replay σ tr !! k = Some σk → ms_log σk = ms_log σ ++ tr_msgs (take k tr).
Proof.
  revert σ k. induction tr as [|s0 tr IH]; intros σ k Hσ.
  - destruct k as [|k]; simpl in Hσ; simplify_eq.
    by rewrite take_nil /= app_nil_r.
  - destruct k as [|k].
    { simpl in Hσ. simplify_eq. by rewrite /= app_nil_r. }
    rewrite /= in Hσ. rewrite (IH _ _ Hσ) mnext_log -app_assoc.
    by destruct s0.
Qed.

Lemma replay_img σ tr k σk : replay σ tr !! k = Some σk → ms_img σk = ms_img σ.
Proof.
  revert σ k. induction tr as [|s0 tr IH]; intros σ k Hσ.
  - by destruct k as [|k]; simpl in Hσ; simplify_eq.
  - destruct k as [|k]; [simpl in Hσ; by simplify_eq|].
    rewrite /= in Hσ. by rewrite (IH _ _ Hσ) mnext_img.
Qed.

(** ** 7.3 A candidate, and the general reachability theorem *)

Record cand := Cand { cd_img : image; cd_tr : list estep }.

Definition cand_init (c : cand) : mstate := MSt (cd_img c) [] (λ _, ws_init).
Definition cand_exec (c : cand) : exec :=
  Exec (replay (cand_init c) (cd_tr c)) (cd_tr c).

Definition cd_log (c : cand) (k : nat) : list wmsg := tr_msgs (take k (cd_tr c)).

Lemma cand_st c k :
  (k ≤ length (cd_tr c))%nat → ex_st (cand_exec c) !! k = Some (stt (cand_exec c) k).
Proof.
  intros Hk. rewrite /stt /=.
  destruct (lookup_lt_is_Some_2 (replay (cand_init c) (cd_tr c)) k) as [σ Hσ];
    [rewrite replay_length; lia|].
  by rewrite Hσ.
Qed.

Lemma cand_elog c k :
  (k ≤ length (cd_tr c))%nat → elog (cand_exec c) k = cd_log c k.
Proof.
  intros Hk. rewrite /elog /cd_log.
  by rewrite (replay_log _ _ _ _ (cand_st c k Hk)).
Qed.

Lemma cand_eimg c k :
  (k ≤ length (cd_tr c))%nat → eimg (cand_exec c) k = cd_img c.
Proof.
  intros Hk. rewrite /eimg. by rewrite (replay_img _ _ _ _ (cand_st c k Hk)).
Qed.

Lemma cand_next c k s :
  cd_tr c !! k = Some s →
  stt (cand_exec c) (S k) = mnext (stt (cand_exec c) k) (es_ag s) (es_lb s).
Proof.
  intros Hs. pose proof (lookup_lt_Some _ _ _ Hs) as Hk.
  pose proof (replay_step (cand_init c) (cd_tr c) k s _ Hs
                (cand_st c k ltac:(lia))) as Hnext.
  by rewrite /stt /= Hnext.
Qed.

(** THE REPLAY THEOREM.  Every candidate all of whose steps are admissible at
    their own replay state is a machine execution, with EXACTLY the given
    trace and image.  This is the [exec]-building half of completeness; it is
    unconditional. *)
Theorem cand_reachable c :
  (∀ k s, cd_tr c !! k = Some s →
     mstep_ok (stt (cand_exec c) k) (es_ag s) (es_lb s)) →
  exec_wf (cand_exec c) ∧
  ex_tr (cand_exec c) = cd_tr c ∧ ex_img (cand_exec c) = cd_img c.
Proof.
  intros Hok.
  assert (Hwf : exec_wf (cand_exec c)).
  { rewrite /exec_wf. split_and!.
    - exact (replay_length (cand_init c) (cd_tr c)).
    - intros σ0 Hσ0.
      assert (Hσ : replay (cand_init c) (cd_tr c) !! 0%nat = Some σ0)
        by exact Hσ0.
      rewrite replay_0 in Hσ. simplify_eq. by split.
    - intros k s σ σ' Hs Hσ Hσ'.
      rewrite -(stt_lookup _ _ _ Hσ) -(stt_lookup _ _ _ Hσ') (cand_next c k s Hs).
      by apply mstep_ok_step, Hok. }
  split_and!; [exact Hwf|done|].
  rewrite /ex_img (cand_eimg c 0%nat); [lia|done].
Qed.

(** ** 7.4 Boundedness along a replay

    The same invariant as §2, but for a replay whose steps are only known
    admissible BELOW the point of interest — which is what the induction that
    discharges [mstep_ok] needs. *)

Definition cfg_bounded (σ : mstate) : Prop :=
  ∀ i, ws_bounded (ms_ws σ i) (length (ms_log σ)).

Lemma upd_ws_bounded f i w n :
  (∀ j, ws_bounded (f j) n) → ws_bounded w n →
  ∀ j, ws_bounded (upd_ws f i w j) n.
Proof.
  intros Hf Hw j. destruct (decide (j = i)) as [->|Hne];
    [by rewrite upd_ws_eq|by rewrite upd_ws_ne].
Qed.

Lemma mnext_bounded σ i l :
  cfg_bounded σ →
  (∀ base ts vs, lb_rd l = Some (base, ts, vs) →
     Forall (λ t, (t ≤ length (ms_log σ))%nat) ts) →
  cfg_bounded (mnext σ i l).
Proof.
  rewrite /cfg_bounded. intros Hb Hrd.
  destruct l as [aq base ts vs|rl base vs|pr pw sr sw|
                 aq rl base ts rvs wvs]; simpl.
  - apply upd_ws_bounded; [exact Hb|].
    apply load_post_run_bounded; [apply Hb|by apply (Hrd base ts vs)].
  - rewrite length_app /=.
    apply upd_ws_bounded.
    + intros j. eapply ws_bounded_mono; [apply Hb|lia].
    + apply (store_post_run_bounded _ _ _ _ _ (length (ms_log σ)));
        [apply Hb|lia|lia].
  - apply upd_ws_bounded; [exact Hb|]. by apply fence_post_bounded, Hb.
  - rewrite length_app /=.
    apply upd_ws_bounded.
    + intros j. eapply ws_bounded_mono; [apply Hb|lia].
    + apply (store_post_run_bounded _ _ _ _ _ (length (ms_log σ)));
        [|lia|lia].
      apply load_post_run_bounded; [apply Hb|by apply (Hrd base ts rvs)].
Qed.

Lemma cand_bounded_upto c n :
  (n ≤ length (cd_tr c))%nat →
  (∀ k s, (k < n)%nat → cd_tr c !! k = Some s →
     mstep_ok (stt (cand_exec c) k) (es_ag s) (es_lb s)) →
  cfg_bounded (stt (cand_exec c) n).
Proof.
  induction n as [|n IH]; intros Hn Hok.
  { assert (Hσ : stt (cand_exec c) 0%nat = cand_init c).
    { apply stt_lookup. exact (replay_0 (cand_init c) (cd_tr c)). }
    rewrite Hσ. intros i. apply ws_bounded_init. }
  destruct (lookup_lt_is_Some_2 (cd_tr c) n ltac:(lia)) as [s Hs].
  rewrite (cand_next c n s Hs).
  apply mnext_bounded.
  - apply IH; [lia|]. intros k s' Hk. apply Hok. lia.
  - intros base ts vs Hrd.
    pose proof (Hok n s ltac:(lia) Hs) as Hstep.
    destruct (es_lb s) as [aq b0 t0 v0|rl b0 v0|????|aq rl b0 t0 rv0 wv0];
      simpl in Hrd; simplify_eq.
    + by eapply rd_ok_ts_bounded.
    + destruct Hstep as (_ & _ & Hrdok & _). by eapply rd_ok_ts_bounded.
Qed.

(** ** 7.5 Completeness for coherence-latest candidates

    The class that closes: candidates whose every byte read takes the LATEST
    write to that byte in the candidate's own log prefix — "SC candidates".
    Everything below is stated over the candidate alone: [cd_log] is the
    trace's own message list ([tr_msgs] of the prefix), not a machine notion.

    This is a genuine lower bound on the machine (every sequentially
    consistent behaviour with the given interleaving is realized, including
    all of its RMWs), and it is exactly the fragment whose [readable] side
    condition needs no view reasoning: a latest timestamp is readable at ANY
    floor ([WeakMem.latest_readable]).  §8 records what the general case
    needs. *)

Definition cand_shape (c : cand) : Prop :=
  ∀ k s, cd_tr c !! k = Some s →
    match es_lb s with
    | LLoad aq base ts vs => length vs = length ts
    | LStore rl base vs => vs ≠ []
    | LFence _ _ _ _ => True
    | LRmw aq rl base ts rvs wvs =>
        wvs ≠ [] ∧ length wvs = length ts ∧ length rvs = length ts
    end.

Definition cand_values (c : cand) : Prop :=
  ∀ k s base ts vs, cd_tr c !! k = Some s → lb_rd (es_lb s) = Some (base, ts, vs) →
    ∀ (j : nat) t v, ts !! j = Some t → vs !! j = Some v →
      log_byte (cd_img c) (cd_log c k) t (acc_addr base j) = Some v.

Definition cand_latest (c : cand) : Prop :=
  ∀ k s base ts vs, cd_tr c !! k = Some s → lb_rd (es_lb s) = Some (base, ts, vs) →
    ∀ (j : nat) t, ts !! j = Some t →
      latest (cd_img c) (cd_log c k) (acc_addr base j) t.

Lemma sc_rd_ok c k s aq base ts vs :
  cand_values c → cand_latest c → length vs = length ts →
  cfg_bounded (stt (cand_exec c) k) →
  cd_tr c !! k = Some s → lb_rd (es_lb s) = Some (base, ts, vs) →
  rd_ok (ms_img (stt (cand_exec c) k)) (ms_log (stt (cand_exec c) k))
        (ms_ws (stt (cand_exec c) k) (es_ag s)) aq base ts vs.
Proof.
  intros Hval Hlat Hlen Hb Hs Hrd.
  pose proof (lookup_lt_Some _ _ _ Hs) as Hk.
  assert (Himg : ms_img (stt (cand_exec c) k) = cd_img c)
    by (apply (cand_eimg c k); lia).
  assert (Hlog : ms_log (stt (cand_exec c) k) = cd_log c k)
    by (apply (cand_elog c k); lia).
  rewrite Himg Hlog. split; [exact Hlen|].
  intros j t v Hj Hv. split.
  - by eapply Hval.
  - apply latest_readable; [|by eapply Hlat].
    pose proof (Hb (es_ag s)) as Hbd. rewrite Hlog in Hbd.
    pose proof (load_vpre_bounded (ms_ws (stt (cand_exec c) k) (es_ag s)) aq
                  (length (cd_log c k)) Hbd).
    destruct Hbd as (_ & _ & _ & _ & _ & Hcoh & _).
    pose proof (Hcoh (acc_addr base j)). lia.
Qed.

Lemma sc_mstep_ok c :
  cand_shape c → cand_values c → cand_latest c →
  ∀ n k s, (k < n)%nat → cd_tr c !! k = Some s →
    mstep_ok (stt (cand_exec c) k) (es_ag s) (es_lb s).
Proof.
  intros Hsh Hval Hlat. induction n as [|n IH]; intros k s Hk Hs; [lia|].
  destruct (decide (k < n)%nat) as [Hlt|Hge]; [by apply IH|].
  assert (k = n) as -> by lia.
  pose proof (lookup_lt_Some _ _ _ Hs) as Hn.
  assert (Hb : cfg_bounded (stt (cand_exec c) n)).
  { apply cand_bounded_upto; [lia|]. intros k' s' Hk' Hs'. by eapply IH. }
  pose proof (Hsh n s Hs) as Hshape.
  assert (Himg : ms_img (stt (cand_exec c) n) = cd_img c)
    by (apply (cand_eimg c n); lia).
  assert (Hlog : ms_log (stt (cand_exec c) n) = cd_log c n)
    by (apply (cand_elog c n); lia).
  destruct (es_lb s) as [aq base ts vs|rl base vs|pr pw sr sw|
                         aq rl base ts rvs wvs] eqn:Hl; simpl in Hshape |- *.
  - eapply (sc_rd_ok c n s aq base ts vs Hval Hlat Hshape Hb Hs).
    by rewrite Hl.
  - exact Hshape.
  - done.
  - destruct Hshape as (Hne & Hlenw & Hlenr). split_and!.
    + exact Hne.
    + exact Hlenw.
    + eapply (sc_rd_ok c n s aq base ts rvs Hval Hlat Hlenr Hb Hs).
      by rewrite Hl.
    + rewrite Himg Hlog. intros j t Hj.
      eapply (Hlat n s base ts rvs Hs ltac:(by rewrite Hl) j t Hj).
Qed.

(** THE COMPLETENESS THEOREM FOR THE SC FRAGMENT. *)
Theorem sc_cand_reachable c :
  cand_shape c → cand_values c → cand_latest c →
  exec_wf (cand_exec c) ∧
  ex_tr (cand_exec c) = cd_tr c ∧ ex_img (cand_exec c) = cd_img c.
Proof.
  intros Hsh Hval Hlat. apply cand_reachable.
  intros k s Hs. eapply (sc_mstep_ok c Hsh Hval Hlat (S k) k s ltac:(lia) Hs).
Qed.

(* ================================================================== *)
(** * 8. The event-level statement of §7 is REFUTED

    Slice 1's §7(2) conjectured [ob]-acyclicity over EVENTS.  The header
    explains why that cannot hold; here it is a theorem.  The witness uses
    only [rfe], [co] and [fr] — no ppo edge at all — so it refutes the
    conjecture under ANY definition of [ppo]. *)

Definition rfe_ev (E : exec) (w r : ev) : Prop :=
  ∃ a k s, r = ev_at k ∧ ex_tr E !! k = Some s ∧
           rf_b E a w r ∧ ext_w E w (es_ag s).

Lemma mnext_ws_ne σ i l j : j ≠ i → ms_ws (mnext σ i l) j = ms_ws σ j.
Proof. intros Hne. destruct l; simpl; by rewrite upd_ws_ne. Qed.

(** An agent that has not stepped yet still holds [ws_init]. *)
Lemma cand_ws_untouched c i n :
  (n ≤ length (cd_tr c))%nat →
  (∀ k s, (k < n)%nat → cd_tr c !! k = Some s → es_ag s ≠ i) →
  ms_ws (stt (cand_exec c) n) i = ws_init.
Proof.
  induction n as [|n IH]; intros Hn Hne.
  { assert (Hσ : stt (cand_exec c) 0%nat = cand_init c).
    { apply stt_lookup. exact (replay_0 (cand_init c) (cd_tr c)). }
    by rewrite Hσ. }
  destruct (lookup_lt_is_Some_2 (cd_tr c) n ltac:(lia)) as [s Hs].
  rewrite (cand_next c n s Hs) (mnext_ws_ne _ (es_ag s) _ i).
  - intros Heq. by apply (Hne n s ltac:(lia) Hs).
  - apply IH; [lia|]. intros k' s' Hk'. apply Hne. lia.
Qed.

Section counterexample.
  Context (v : bv 8).

  (** Three stores and one two-byte load, as in the header:
      ts 1 writes byte 1; ts 2 writes bytes 0 and 1; ts 3 writes byte 0;
      then agent 2 loads bytes 0,1 taking ts 3 for byte 0 and ts 1 for
      byte 1 (both admissible: agent 2's floor is 0). *)
  Definition ce_tr : list estep :=
    [EStep 0 (LStore false 1 [v]);
     EStep 0 (LStore false 0 [v; v]);
     EStep 1 (LStore false 0 [v]);
     EStep 2 (LLoad false 0 [3; 1]%nat [v; v])].

  Definition ce : cand := Cand (λ _, None) ce_tr.
  Definition ceE : exec := cand_exec ce.

  Lemma ce_log k : (k ≤ 4)%nat → elog ceE k = tr_msgs (take k ce_tr).
  Proof. intros Hk. apply (cand_elog ce k). rewrite /= /ce_tr /=. lia. Qed.

  Lemma ce_ws2 k : (k ≤ 3)%nat → ms_ws (stt ceE k) 2 = ws_init.
  Proof.
    intros Hk. apply (cand_ws_untouched ce 2 k); [rewrite /ce /ce_tr /=; lia|].
    intros k' s' Hk' Hs'. rewrite /ce /ce_tr /= in Hs'.
    destruct k' as [|[|[|k']]]; simplify_eq/=; lia.
  Qed.
  Lemma ce_len : length (ex_tr ceE) = 4%nat.
  Proof. done. Qed.

  Lemma ce_ex_log : ex_log ceE = tr_msgs ce_tr.
  Proof.
    rewrite /ex_log ce_len (ce_log 4%nat ltac:(lia)) /ce_tr /= //.
  Qed.

  Lemma ce_ts0 : ev_ts ceE (ev_at 0) = 1%nat.
  Proof. rewrite ev_ts_at (ce_log 0%nat ltac:(lia)) //. Qed.
  Lemma ce_ts1 : ev_ts ceE (ev_at 1) = 2%nat.
  Proof. rewrite ev_ts_at (ce_log 1%nat ltac:(lia)) /ce_tr /= //. Qed.
  Lemma ce_ts2 : ev_ts ceE (ev_at 2) = 3%nat.
  Proof. rewrite ev_ts_at (ce_log 2%nat ltac:(lia)) /ce_tr /= //. Qed.

  (** The four write operations of the witness. *)
  Lemma ce_w0_1 : wr_b ceE 1 (ev_at 0).
  Proof.
    split; [by eexists|].
    rewrite /ev_writes ce_ts0 ce_ex_log /ce_tr /=. vm_compute. by eexists.
  Qed.
  Lemma ce_w1_0 : wr_b ceE 0 (ev_at 1).
  Proof.
    split; [by eexists|].
    rewrite /ev_writes ce_ts1 ce_ex_log /ce_tr /=. vm_compute. by eexists.
  Qed.
  Lemma ce_w1_1 : wr_b ceE 1 (ev_at 1).
  Proof.
    split; [by eexists|].
    rewrite /ev_writes ce_ts1 ce_ex_log /ce_tr /=. vm_compute. by eexists.
  Qed.
  Lemma ce_w2_0 : wr_b ceE 0 (ev_at 2).
  Proof.
    split; [by eexists|].
    rewrite /ev_writes ce_ts2 ce_ex_log /ce_tr /=. vm_compute. by eexists.
  Qed.

  (** The load's two byte reads. *)
  Lemma ce_rd0 : reads_at ceE 3 0 3 v.
  Proof.
    exists (EStep 2 (LLoad false 0 [3; 1]%nat [v; v])), 0, [3; 1]%nat,
           [v; v], 0%nat.
    split_and!; [done|done|done|done|rewrite /acc_addr //].
  Qed.
  Lemma ce_rd1 : reads_at ceE 3 1 1 v.
  Proof.
    exists (EStep 2 (LLoad false 0 [3; 1]%nat [v; v])), 0, [3; 1]%nat,
           [v; v], 1%nat.
    split_and!; [done|done|done|done|rewrite /acc_addr //].
  Qed.

  (** The machine really does admit this run: the load's two byte reads are
      [readable] because agent 2's floor is still 0. *)
  Lemma ce_rd : rd_ok (ms_img (stt ceE 3)) (ms_log (stt ceE 3))
                      (ms_ws (stt ceE 3) 2) false 0 [3; 1]%nat [v; v].
  Proof.
    assert (Hlog : ms_log (stt ceE 3) = tr_msgs (take 3 ce_tr)).
    { exact (ce_log 3%nat ltac:(lia)). }
    assert (Himg : ms_img (stt ceE 3) = (λ _ : Z, @None (bv 8))).
    { exact (cand_eimg ce 3%nat ltac:(rewrite /ce /ce_tr /=; lia)). }
    rewrite Hlog Himg (ce_ws2 3%nat ltac:(lia)).
    split; [done|]. intros j t v' Hj Hv'.
    destruct j as [|[|j]]; simplify_eq/=.
    - split; [vm_compute; done|]. split; [vm_compute; by eexists|].
      intros (t' & H1 & H2 & _). vm_compute in H2. lia.
    - split; [vm_compute; done|]. split; [vm_compute; by eexists|].
      intros (t' & H1 & H2 & _). vm_compute in H2. lia.
  Qed.

  Lemma ce_ok : ∀ k s, cd_tr ce !! k = Some s →
    mstep_ok (stt ceE k) (es_ag s) (es_lb s).
  Proof.
    intros k s Hs. rewrite /ce /ce_tr /= in Hs.
    destruct k as [|[|[|[|k]]]]; simpl in Hs; simplify_eq;
      [done|done|done|exact ce_rd].
  Qed.

  Lemma ce_wf : exec_wf ceE.
  Proof. exact (proj1 (cand_reachable ce ce_ok)). Qed.

  (** THE CYCLE. *)
  Theorem ev_rfe_co_fr_cyclic :
    ∃ (E : exec) (e : ev),
      exec_wf E ∧ tc (λ x y, rfe_ev E x y ∨ co E x y ∨ fr E x y) e e.
  Proof.
    exists ceE, (ev_at 2).
    split; [exact ce_wf|].
    assert (Hrf0 : rf_b ceE 0 (ev_at 2) (ev_at 3)).
    { split; [exact ce_w2_0|]. exists 3%nat, 3%nat, v.
      split_and!; [done|exact ce_rd0|exact ce_ts2]. }
    assert (Hrf1 : rf_b ceE 1 (ev_at 0) (ev_at 3)).
    { split; [exact ce_w0_1|]. exists 3%nat, 1%nat, v.
      split_and!; [done|exact ce_rd1|exact ce_ts0]. }
    eapply tc_l; [left|].
    { exists 0, 3%nat, (EStep 2 (LLoad false 0 [3; 1]%nat [v; v])).
      split_and!; [done|done|exact Hrf0|].
      rewrite /ext_w /=. eexists. split; [done|done]. }
    eapply tc_l with (ev_at 1); [right; right|].
    { exists 1. split; [|done]. exists (ev_at 0). split; [exact Hrf1|].
      split_and!; [exact ce_w0_1|exact ce_w1_1|].
      rewrite ce_ts0 ce_ts1. lia. }
    apply tc_once. right; left. exists 0.
    split_and!; [exact ce_w1_0|exact ce_w2_0|].
    rewrite ce_ts1 ce_ts2. lia.
  Qed.
End counterexample.

(* ================================================================== *)
(** * 9. WHAT SLICE 2 DOES NOT DO — the remaining obligation

    As in slice 1, everything that does not close is written as a comment, not
    as an [Axiom]: this file is axiom-free ([Print Assumptions] on
    [promise_free_ob_acyclic], [promise_free_gmo], [cand_reachable],
    [sc_cand_reachable] and [ev_rfe_co_fr_cyclic] all report "Closed under the
    global context").

    ------------------------------------------------------------------
    (1) FULL COMPLETENESS — STILL OPEN.  The intended statement, in this
    file's vocabulary (§7 supplies every definition it names, so this is a
    Rocq-checkable sentence the moment its proof exists):

<<
      Definition cand_axiomatic_ok (c : cand) : Prop :=
        axiomatic_ok (cand_exec c) ∧ (∀ o, ¬ tc (ob_op (cand_exec c)) o o).

      Conjecture promise_free_complete : ∀ c : cand,
        cand_shape c → cand_values c → cand_axiomatic_ok c →
        exec_wf (cand_exec c) ∧
        ex_tr (cand_exec c) = cd_tr c ∧ ex_img (cand_exec c) = cd_img c.
>>

    (Note that [cand_exec c]'s relations — [po], [rf_b], [co_b], [fr_b],
    [ppo_op] — are well defined whether or not the candidate is admissible:
    they are functions of the image, the trace and the prefix logs, and §7's
    [cand_elog]/[cand_eimg] show the logs are [tr_msgs] of the prefix.  So the
    hypothesis is a genuine axiomatic hypothesis, not a machine one.)

    By §7's [cand_reachable] the whole obligation is: DISCHARGE [mstep_ok] AT
    EVERY STEP.  Only the [readable] conjunct is hard, and exactly one lemma
    is missing:

<<
      (* VIEW DOMINATION — the missing induction. *)
      Lemma replay_view_dominated c k s i a :
        cand_shape c → cand_values c → cand_axiomatic_ok c →
        cd_tr c !! k = Some s → es_ag s = i →
        ∃ o : mop,                      (* an operation of an earlier step *)
          (o = (a, ev_init) ∨ ppo_op (cand_exec c) o (a, ev_at k)) ∧
          (Nat.max (load_vpre (ms_ws (stt (cand_exec c) k) i) (lb_aq (es_lb s)))
                   (coh (ms_ws (stt (cand_exec c) k) i) a)
           ≤ opos (cand_exec c) o.1 o.2)%nat.
>>

    With it the read case closes in the standard way: if some write [w] of
    byte [a] had [t < ev_ts w ≤ the floor], then [fr] would put the read
    before [w] while the dominating operation [o] would put [w] at or before
    [o] and [ppo] would put [o] before the read — an [ob] cycle, contradicting
    [cand_axiomatic_ok].

    WHY IT IS NOT A COROLLARY OF SLICE 1's [ax_ord], and hence why this is a
    real research item and not a lift: the machine's fence delivery is
    TRANSITIVE.  A [fence r,r] delivers [w_vrOld], which past loads raised to
    THEIR OWN pre-views, which earlier fences had raised in turn; so the
    justification of a floor value is an [ob]-PATH, not one [ord] edge.
    [ax_ord] is a one-edge statement and is provably too weak to reconstruct
    the floor.  The induction that is needed carries one conjunct per view
    component ([coh], [w_vrOld], [w_vwOld], [w_vrNew], [w_vwNew], [w_vRel] and
    the forward bank), each of the "≤ the position of some [ob]-predecessor"
    shape above, through the four step arms.  Honest estimate: 600–900 lines,
    with the forward bank the fiddly conjunct (a forwarded read's view is the
    BANKED value, so its dominator is the earlier STORE operation, not the
    read's own timestamp — the same asymmetry [pub_r] records).

    WHAT DOES CLOSE, and is landed: §7.5's [sc_cand_reachable] — every
    candidate whose reads take the coherence-LATEST write of their byte
    ([cand_latest]) is machine-reachable, RMWs included.  That fragment needs
    no view reasoning at all ([WeakMem.latest_readable]: a latest timestamp is
    readable at every floor), and it is a genuine lower bound: every
    sequentially consistent behaviour, in every interleaving, is a
    promise-free machine run.  The residue is precisely the STALE reads —
    which is where all the weak-memory content of completeness lives.

    ------------------------------------------------------------------
    (2) THE THREE PLACES SLICE 1's §7 SPEC MOVED (coordinator's call, all
    recorded, none of them a weakening of a slice-1 definition):

    - [ob] is over OPERATIONS, not events.  Forced: [ev_rfe_co_fr_cyclic]
      REFUTES the event-level statement, using only [rfe ∪ co ∪ fr], i.e. for
      any [ppo] whatsoever.  Slice 1's own relations are untouched — [rf_b],
      [co_b], [fr_b] were already byte-indexed, which is exactly what made the
      lift free.

    - [ppo_op] has FOUR arms where §7's sketch had three ([fence_between +
      acq_po + po_loc_b]).  The extra one is [po] INTO A WRITE OPERATION,
      which is free in a promise-free machine (a store appends at the top of
      the log) and subsumes every RVWMO ppo rule whose successor is a store —
      including the succ-W fence cases that [ord_pw]/[ord_pr] (both succ-R)
      never covered.  This is a strengthening.

    - The [ord_pr] arm carries the side condition [¬ wr_b E a1 e1] (§6 seam
      (a)): the fused RMW's operation at a byte it WRITES is not claimed to be
      ordered by a pred-R fence, because that fence publishes the read half's
      timestamp while the operation sits at the write half's.  Slice 1's
      [ax_ord] draws the same line (its conclusion is about the published
      [t]); the alternative — splitting the RMW into two operations — would
      change slice 1's event alphabet and is not this slice's call.

    ------------------------------------------------------------------
    (3) OWED LIFTS (for W4's "WeakMem/WeakPromise lemma lifts" batch):
    [load_post_fold_vrNew_aq_vpre] and [load_post_run_vrNew_aq_vpre] (§1) and
    [rd_ok_ts_bounded] (§1) belong in [WeakMem.v] next to their siblings;
    [exec_ws_bounded] (§2) belongs in [WeakAxiomatic.v] next to the other
    execution invariants, as do [evpre] and its four lemmas (§3) if slice 3
    wants them.  Nothing here edits either file. *)
