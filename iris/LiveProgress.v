(* LiveProgress.v -- THE ABSTRACT PROGRESS THEOREM of the liveness design,   *)
(*  over INFINITE STREAMS.                                                  *)
(*                                                                          *)
(*  claude-notes/projects/liveness.md: a pure library, below Iris, that     *)
(*  turns ledger consistency plus fairness into every obligation is         *)
(*  eventually fulfilled.  This file is that theorem with the MACHINE        *)
(*  ABSTRACTED AWAY: a stream of ledger snapshots indexed by [nat], a        *)
(*  stream of cycle events, and nothing else.                                *)
(*                                                                          *)
(*  STATUS (see the project note, section Pilot handoff): this is the        *)
(*  REFERENCE form of the argument, and NOTHING IN THE TREE CAN FEED IT      *)
(*  YET.  Iris adequacy exports a separate existential ledger witness at    *)
(*  every finite prefix, and separate witnesses do not form one infinite     *)
(*  stream without a compactness/choice bridge (Trillium-style trace        *)
(*  adequacy).  The pilot therefore argues PER PREFIX, from a FIXED initial   *)
(*  ledger, with physically constrained window exits; the generic per-prefix *)
(*  theorem, when written, should mirror the induction below (levels, then   *)
(*  rank, then budget twice).  Kept because it settles the SHAPE of the      *)
(*  ledger record and of the fairness hypotheses, and because it is what a   *)
(*  trace adequacy would consume directly.                                   *)
(*                                                                          *)
(*  THE MODEL (Ghost-Signals / Lilo discipline, on fuel).                    *)
(*                                                                          *)
(*  * A THREAD [t : T] is whatever the ledger opens windows for -- a hart,   *)
(*    or a parked process.  Its state at a snapshot is                       *)
(*        TOff              -- uncounted: outside the T-tier                 *)
(*        TIn r None b      -- counted, rank [r], budget [b] instructions     *)
(*        TIn r (Some o) b  -- counted, at a WAIT SITE on obligation [o]      *)
(*    The thread's MEASURE is lexicographic (rank, running-before-waiting,   *)
(*    budget), and the one step that does not decrease it is the            *)
(*    CHECKPOINT: a waiting thread refreshes its budget, which is allowed    *)
(*    only while the obligation it waits on is still pending and sits at a  *)
(*    LEVEL strictly below everything the thread itself holds.               *)
(*                                                                          *)
(*  * AN OBLIGATION [o : O] is a one-shot promise with a fixed [holder]      *)
(*    (a thread, or [None] for the environment) and a [lvl].  It is [pend]   *)
(*    from creation to fulfilment and [ful] from then on.  A thread that     *)
(*    holds a pending obligation is in the tier.                             *)
(*                                                                          *)
(*  * THE WAITED OBLIGATION IS FIXED AT A RANK.  A thread at rank [r]        *)
(*    waiting on [o'] cannot switch to waiting on [o''] without a rank       *)
(*    decrease.  Without this the theorem is FALSE: a hart spinning on a     *)
(*    TAS lock waits on holder i releases for i = 1, 2, ... , each of      *)
(*    which IS fulfilled, and never progresses -- xv6's genuine unfairness   *)
(*    (liveness.md F-lock).  The design therefore makes such a wait a wait   *)
(*    on ONE environment obligation (this hart acquires L), fulfilled by   *)
(*    the F-lock hypothesis, and the rule here is what forces that choice.   *)
(*                                                                          *)
(*  THE HYPOTHESES are all stated on the streams (liveness.md: every         *)
(*  assumption is a predicate on the run, never a semantic change), and     *)
(*  every eventually among them is a WITNESSING existential, so that the  *)
(*  proof below is constructive -- no classical axiom enters the audit      *)
(*  ([Print Assumptions progress] is closed under the global context).      *)
(*  In particular fairness is from any point, the thread either cycles or  *)
(*  leaves the tier, which is what F-pool gives for a hart directly.       *)
(*                                                                          *)
(*  THE THEOREM: every pending obligation is eventually fulfilled.  By      *)
(*  well-founded induction on the level; inside a level, on the holder's   *)
(*  rank; inside a rank, on the budget -- twice, once before and once      *)
(*  after the waited obligation (which the level induction fulfils) is     *)
(*  gone, since after that no checkpoint can refresh the budget.           *)

From Stdlib Require Import Lia.
From stdpp Require Import prelude.

Inductive tstate (O : Type) :=
  | TOff
  | TIn (r : nat) (w : option O) (b : nat).
Arguments TOff {_}.
Arguments TIn {_} _ _ _.

Section progress.
  Context {T O : Type}.
  Variable lvl : O -> nat.
  Variable holder : O -> option T.

  Implicit Types (st : tstate O) (o : O) (t : T).

  (* 1 while running, 0 while waiting: entering a wait is a decrease. *)
  Definition tflag (w : option O) : nat :=
    match w with None => 1 | Some _ => 0 end.

  Definition trank st : nat :=
    match st with TOff => 0 | TIn r _ _ => r end.

  (* STRICT DECREASE of the thread measure, inside the tier.  The waited
     obligation can change only through a rank decrease. *)
  Definition tdecr st st' : Prop :=
    match st, st' with
    | TIn r w b, TIn r' w' b' =>
        r' < r
        \/ (r' = r /\ tflag w' < tflag w)
        \/ (r' = r /\ w' = w /\ b' < b)
    | _, _ => False
    end.

  (* THE CHECKPOINT: a waiting thread refreshes its budget.  [held] is what
     the thread holds AFTER the step, [pend] what is pending after it. *)
  Definition tckpt (held pend : O -> Prop) st st' : Prop :=
    exists r o b b',
      st = TIn r (Some o) b /\ st' = TIn r (Some o) b'
      /\ pend o /\ (forall o', held o' -> lvl o < lvl o').

  (* One step of one thread: stutter, decrease, checkpoint, or a crossing
     of the tier boundary in either direction. *)
  Definition tstep (held pend : O -> Prop) st st' : Prop :=
    st' = st \/ tdecr st st' \/ tckpt held pend st st'
    \/ st = TOff \/ st' = TOff.

  (* The streams. *)
  Variable tst : nat -> T -> tstate O.
  Variable pend ful : nat -> O -> Prop.
  Variable cyc : nat -> T -> Prop.

  Definition held_by (n : nat) t o : Prop := pend n o /\ holder o = Some t.

  (* Ledger consistency at every prefix, and across every step. *)
  Hypothesis Hful_mono : forall n o, ful n o -> ful (S n) o.
  Hypothesis Hpend_step : forall n o, pend n o -> pend (S n) o \/ ful (S n) o.
  Hypothesis Hpend_ful : forall n o, pend n o -> ~ ful n o.
  Hypothesis Hheld_tier : forall n o t,
    pend n o -> holder o = Some t -> tst n t <> TOff.
  Hypothesis Hstep : forall n t,
    tstep (held_by (S n) t) (pend (S n)) (tst n t) (tst (S n) t).
  (* A cycle of a thread in the tier is never a stutter: counted code pays
     one unit of fuel per instruction. *)
  Hypothesis Hcyc : forall n t, cyc n t -> tst n t <> TOff -> tst (S n) t <> tst n t.

  (* Fairness, and the environment's obligations. *)
  Hypothesis Hfair : forall t n, exists m, n <= m /\ (cyc m t \/ tst m t = TOff).
  Hypothesis Henv : forall o n,
    holder o = None -> pend n o -> exists m, n <= m /\ ful m o.

  (* ------------------------------------------------------------------ *)
  (* Bookkeeping on the obligation streams.                              *)
  (* ------------------------------------------------------------------ *)

  Lemma ful_le n m o : n <= m -> ful n o -> ful m o.
  Proof.
    intros Hle Hf. induction Hle; [done|]. by apply Hful_mono.
  Qed.

  (* pending at [n], and still at [m]: pending in between *)
  Lemma pend_reach n m o :
    n <= m -> pend n o -> pend m o \/ exists k, n < k <= m /\ ful k o.
  Proof.
    intros Hle Hp. induction Hle as [|m Hle IH]; [by left|].
    destruct IH as [Hpm | (k & Hk & Hf)].
    - destruct (Hpend_step _ _ Hpm) as [Hp'|Hf]; [by left|].
      right. exists (S m). split; [lia|done].
    - right. exists k. split; [lia|done].
  Qed.

  Lemma pend_between n k m o :
    n <= k -> k <= m -> pend n o -> pend m o -> pend k o.
  Proof.
    intros Hnk Hkm Hn Hm.
    destruct (pend_reach n k o Hnk Hn) as [Hk | (j & Hj & Hf)]; [done|].
    exfalso. eapply Hpend_ful; [exact Hm|]. eapply ful_le; [|exact Hf]. lia.
  Qed.

  (* fulfilled at [m]: never pending again *)
  Lemma ful_not_pend m k o : m <= k -> ful m o -> ~ pend k o.
  Proof. intros Hle Hf Hp. eapply Hpend_ful; [exact Hp|]. by eapply ful_le. Qed.

  (* ------------------------------------------------------------------ *)
  (* A thread holding [o] moves only by stutter / decrease / checkpoint   *)
  (* while [o] is pending; the rank never rises and the waited            *)
  (* obligation stays put at a fixed rank.                                *)
  (* ------------------------------------------------------------------ *)

  Section holder.
    Variable o : O.
    Variable t : T.
    Hypothesis Hhold : holder o = Some t.

    Definition goal (n : nat) : Prop := exists m, n <= m /\ ful m o.

    Lemma tier_step n :
      pend n o -> pend (S n) o ->
      tst (S n) t = tst n t
      \/ tdecr (tst n t) (tst (S n) t)
      \/ tckpt (held_by (S n) t) (pend (S n)) (tst n t) (tst (S n) t).
    Proof.
      intros Hp Hp'.
      pose proof (Hheld_tier _ _ _ Hp Hhold) as Hin.
      pose proof (Hheld_tier _ _ _ Hp' Hhold) as Hin'.
      destruct (Hstep n t) as [?|[?|[?|[?|?]]]]; tauto.
    Qed.

    Lemma tier_step_rank n :
      pend n o -> pend (S n) o -> trank (tst (S n) t) <= trank (tst n t).
    Proof.
      intros Hp Hp'.
      destruct (tier_step n Hp Hp') as [Heq | [Hd | Hc]].
      - rewrite Heq. lia.
      - unfold tdecr in Hd.
        destruct (tst n t), (tst (S n) t); simpl in *; lia.
      - destruct Hc as (r & o' & b & b' & -> & -> & _). simpl. lia.
    Qed.

    Lemma tier_rank_mono n m :
      n <= m -> pend n o -> pend m o -> trank (tst m t) <= trank (tst n t).
    Proof.
      intros Hle Hn Hm. induction Hle as [|m Hle IH]; [lia|].
      assert (Hpm : pend m o) by (eapply pend_between; [| |exact Hn|exact Hm]; lia).
      pose proof (tier_step_rank m Hpm Hm). specialize (IH Hpm). lia.
    Qed.

    (* at a fixed rank the waited obligation is fixed *)
    Lemma tier_step_wait n r o' b :
      pend n o -> pend (S n) o ->
      tst n t = TIn r (Some o') b -> trank (tst (S n) t) = r ->
      exists b', tst (S n) t = TIn r (Some o') b'.
    Proof.
      intros Hp Hp' Hn Hr.
      destruct (tier_step n Hp Hp') as [Heq | [Hd | Hc]].
      - rewrite Heq. by exists b.
      - unfold tdecr in Hd. rewrite Hn in Hd.
        destruct (tst (S n) t) as [|r'' w'' b'']; [done|]. simpl in Hr. subst r''.
        destruct Hd as [? | [(_ & Hf) | (_ & -> & _)]]; [lia| |by exists b''].
        destruct w''; simpl in Hf; lia.
      - destruct Hc as (r0 & o0 & b0 & b0' & Heq & -> & _ & _).
        rewrite Hn in Heq. injection Heq as <- <- <-. by exists b0'.
    Qed.

    Lemma tier_wait_fixed n m r o' b :
      n <= m -> pend n o -> pend m o ->
      tst n t = TIn r (Some o') b -> trank (tst m t) = r ->
      exists b', tst m t = TIn r (Some o') b'.
    Proof.
      intros Hle Hn Hm Hst Hr. induction Hle as [|m Hle IH].
      - by exists b.
      - assert (Hpm : pend m o) by (eapply pend_between; [| |exact Hn|exact Hm]; lia).
        pose proof (tier_step_rank m Hpm Hm) as Hstep_r.
        pose proof (tier_rank_mono n m Hle Hn Hpm) as Hmono.
        rewrite Hst in Hmono. simpl in Hmono.
        destruct (IH Hpm) as [b0 Hm0]; [lia|].
        eapply tier_step_wait; eauto.
    Qed.

    (* ---------------------------------------------------------------- *)
    (* ADVANCE: from any point while [o] is pending, either [o] gets     *)
    (* fulfilled or the thread reaches its next non-stutter step, with   *)
    (* the same state it had at the start (it stuttered until then).     *)
    (* This is where fairness is spent.                                  *)
    (* ---------------------------------------------------------------- *)

    Lemma advance_aux d :
      forall n, pend n o -> (cyc (n + d) t \/ tst (n + d) t = TOff) ->
      goal n
      \/ exists k, n <= k /\ pend k o /\ pend (S k) o /\ tst k t = tst n t
           /\ (tdecr (tst k t) (tst (S k) t)
               \/ tckpt (held_by (S k) t) (pend (S k)) (tst k t) (tst (S k) t)).
    Proof.
      induction d as [|d IH]; intros n Hp Hfar.
      - rewrite Nat.add_0_r in Hfar.
        pose proof (Hheld_tier _ _ _ Hp Hhold) as Hin.
        destruct Hfar as [Hcy | Hoff]; [|done].
        pose proof (Hcyc _ _ Hcy Hin) as Hne.
        destruct (Hpend_step _ _ Hp) as [Hp' | Hf].
        + destruct (tier_step n Hp Hp') as [Heq | Hmove]; [done|].
          right. exists n. split_and!; [lia|done|done|done|exact Hmove].
        + left. exists (S n). split; [lia|done].
      - destruct (Hpend_step _ _ Hp) as [Hp' | Hf].
        + destruct (tier_step n Hp Hp') as [Heq | Hmove].
          * replace (n + S d) with (S n + d) in Hfar by lia.
            destruct (IH (S n) Hp' Hfar) as [(m & Hm & Hf) | (k & Hk & Hpk & Hpk' & Hst & Hmv)].
            { left. exists m. split; [lia|done]. }
            { right. exists k.
              split_and!; [lia|done|done|by rewrite Hst, Heq|exact Hmv]. }
          * right. exists n. split_and!; [lia|done|done|done|exact Hmove].
        + left. exists (S n). split; [lia|done].
    Qed.

    Lemma advance n :
      pend n o ->
      goal n
      \/ exists k, n <= k /\ pend k o /\ pend (S k) o /\ tst k t = tst n t
           /\ (tdecr (tst k t) (tst (S k) t)
               \/ tckpt (held_by (S k) t) (pend (S k)) (tst k t) (tst (S k) t)).
    Proof.
      intros Hp. destruct (Hfair t n) as (m & Hle & Hfar).
      apply (advance_aux (m - n) n Hp). by replace (n + (m - n)) with m by lia.
    Qed.

    (* ---------------------------------------------------------------- *)
    (* THE THREE BUDGET INDUCTIONS, at a fixed rank [r].  Each concludes  *)
    (* either the goal or a strictly smaller rank at a later pending      *)
    (* point.                                                             *)
    (* ---------------------------------------------------------------- *)

    Definition below (r n : nat) : Prop :=
      exists m, n <= m /\ pend m o /\ trank (tst m t) < r.

    (* the level induction hypothesis, for everything below [o]'s level *)
    Variable IHlvl : forall o', lvl o' < lvl o ->
      forall n, pend n o' -> exists m, n <= m /\ ful m o'.

    (* waiting on an obligation that is gone: no checkpoint can refresh
       the budget, so every step is a decrease *)
    Lemma wait_quiet r o' m0 :
      ful m0 o' ->
      forall b n, m0 <= n -> pend n o -> tst n t = TIn r (Some o') b ->
      goal n \/ below r n.
    Proof.
      intros Hf b. induction b as [b IH] using lt_wf_ind. intros n Hm0 Hp Hst.
      destruct (advance n Hp) as [Hg | (k & Hk & Hpk & Hpk' & Hkst & Hmv)]; [by left|].
      rewrite Hst in Hkst.
      destruct Hmv as [Hd | Hc].
      - unfold tdecr in Hd. rewrite Hkst in Hd.
        destruct (tst (S k) t) as [|r' w' b'] eqn:Hk'; [done|].
        destruct Hd as [Hr | [(-> & Hfl) | (-> & -> & Hb)]].
        + right. exists (S k). split; [lia|]. split; [done|]. rewrite Hk'. done.
        + destruct w'; simpl in Hfl; lia.
        + destruct (IH b' Hb (S k)) as [(m & Hm & Hfm) | (m & Hm & Hpm & Hrm)];
            [lia|done|done| |].
          * left. exists m. split; [lia|done].
          * right. exists m. split; [lia|done].
      - exfalso. destruct Hc as (r0 & o0 & b0 & b0' & Heq & _ & Hpo0 & _).
        rewrite Hkst in Heq. injection Heq as <- <- <-.
        eapply ful_not_pend; [|exact Hf|exact Hpo0]. lia.
    Qed.

    (* waiting: the level induction fulfils the waited obligation, then
       [wait_quiet] takes over *)
    Lemma wait_progress r o' :
      forall b n, pend n o -> tst n t = TIn r (Some o') b ->
      goal n \/ below r n.
    Proof.
      intros b. induction b as [b IH] using lt_wf_ind. intros n Hp Hst.
      destruct (advance n Hp) as [Hg | (k & Hk & Hpk & Hpk' & Hkst & Hmv)]; [by left|].
      rewrite Hst in Hkst.
      destruct Hmv as [Hd | Hc].
      - unfold tdecr in Hd. rewrite Hkst in Hd.
        destruct (tst (S k) t) as [|r' w' b'] eqn:Hk'; [done|].
        destruct Hd as [Hr | [(-> & Hfl) | (-> & -> & Hb)]].
        + right. exists (S k). split; [lia|]. split; [done|]. rewrite Hk'. done.
        + destruct w'; simpl in Hfl; lia.
        + destruct (IH b' Hb (S k) Hpk' Hk') as [(m & Hm & Hfm) | (m & Hm & Hpm & Hrm)].
          * left. exists m. split; [lia|done].
          * right. exists m. split; [lia|done].
      - destruct Hc as (r0 & o0 & b0 & b0' & Heq & Hk' & Hpo0 & Hlvl).
        rewrite Hkst in Heq. injection Heq as <- <- <-.
        (* [o'] sits below [o], which the thread holds *)
        assert (Hlt : lvl o' < lvl o).
        { apply Hlvl. split; [exact Hpk' | exact Hhold]. }
        destruct (IHlvl o' Hlt (S k) Hpo0) as (m0 & Hm0 & Hf0).
        (* is [o] still pending at [m0]? *)
        destruct (pend_reach (S k) m0 o Hm0 Hpk') as [Hpm0 | (j & Hj & Hfj)].
        + pose proof (tier_rank_mono (S k) m0 Hm0 Hpk' Hpm0) as Hmono.
          rewrite Hk' in Hmono. simpl in Hmono.
          destruct (Nat.lt_ge_cases (trank (tst m0 t)) r) as [Hlt_r | Hge].
          * right. exists m0. split; [lia|done].
          * assert (Hr : trank (tst m0 t) = r) by lia.
            destruct (tier_wait_fixed (S k) m0 r o' b0' Hm0 Hpk' Hpm0 Hk' Hr)
              as (b1 & Hm0st).
            destruct (wait_quiet r o' m0 Hf0 b1 m0 (le_n _) Hpm0 Hm0st)
              as [(m & Hm & Hfm) | (m & Hm & Hpm & Hrm)].
            { left. exists m. split; [lia|done]. }
            { right. exists m. split; [lia|done]. }
        + left. exists j. split; [lia|done].
    Qed.

    (* running: decrease, or enter a wait *)
    Lemma run_progress r :
      forall b n, pend n o -> tst n t = TIn r None b ->
      goal n \/ below r n.
    Proof.
      intros b. induction b as [b IH] using lt_wf_ind. intros n Hp Hst.
      destruct (advance n Hp) as [Hg | (k & Hk & Hpk & Hpk' & Hkst & Hmv)]; [by left|].
      rewrite Hst in Hkst.
      destruct Hmv as [Hd | Hc].
      - unfold tdecr in Hd. rewrite Hkst in Hd.
        destruct (tst (S k) t) as [|r' w' b'] eqn:Hk'; [done|].
        destruct Hd as [Hr | [(-> & Hfl) | (-> & -> & Hb)]].
        + right. exists (S k). split; [lia|]. split; [done|]. rewrite Hk'. done.
        + destruct w' as [o'|]; simpl in Hfl; [|lia].
          destruct (wait_progress r o' b' (S k) Hpk' Hk')
            as [(m & Hm & Hfm) | (m & Hm & Hpm & Hrm)].
          * left. exists m. split; [lia|done].
          * right. exists m. split; [lia|done].
        + destruct (IH b' Hb (S k) Hpk' Hk') as [(m & Hm & Hfm) | (m & Hm & Hpm & Hrm)].
          * left. exists m. split; [lia|done].
          * right. exists m. split; [lia|done].
      - exfalso. destruct Hc as (r0 & o0 & b0 & b0' & Heq & _).
        rewrite Hkst in Heq. discriminate.
    Qed.

    (* THE RANK INDUCTION *)
    Lemma rank_progress r :
      forall n, pend n o -> trank (tst n t) = r -> goal n.
    Proof.
      induction r as [r IH] using lt_wf_ind. intros n Hp Hr.
      pose proof (Hheld_tier _ _ _ Hp Hhold) as Hin.
      destruct (tst n t) as [|r' w b] eqn:Hst; [done|]. simpl in Hr. subst r'.
      assert (Hcases : goal n \/ below r n).
      { destruct w as [o'|].
        - exact (wait_progress r o' b n Hp Hst).
        - exact (run_progress r b n Hp Hst). }
      destruct Hcases as [Hg | (m & Hm & Hpm & Hrm)]; [done|].
      destruct (IH _ Hrm m Hpm eq_refl) as (m' & Hm' & Hf).
      exists m'. split; [lia|done].
    Qed.
  End holder.

  (* ------------------------------------------------------------------ *)
  (* THE THEOREM.                                                        *)
  (* ------------------------------------------------------------------ *)

  Theorem progress : forall o n, pend n o -> exists m, n <= m /\ ful m o.
  Proof.
    (* well-founded induction on the level *)
    assert (Hlvl : forall l, forall o, lvl o = l ->
                     forall n, pend n o -> exists m, n <= m /\ ful m o).
    { induction l as [l IH] using lt_wf_ind. intros o Hl n Hp.
      destruct (holder o) as [t|] eqn:Hh.
      - eapply (rank_progress o t Hh); [|exact Hp|reflexivity].
        intros o' Hlt. apply (IH (lvl o')); [lia|reflexivity].
      - exact (Henv o n Hh Hp). }
    intros o n Hp. exact (Hlvl (lvl o) o eq_refl n Hp).
  Qed.

End progress.
