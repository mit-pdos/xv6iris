(** * WeakRobustAcyc.v — the standalone acyclicity MEASURE theorem
      (M6 W2a, step 2: the disciplined-cycle refutation)

    [WeakRobustGraph.v] fixes the dependency graph [gdep = gpo ∪ grf] over
    a traced behavior and proves the STRUCTURAL half of acyclicity: every
    cycle contains a CROSS-AGENT rf edge ([tc_gdep_cross]), because inside
    one agent both edge families increase the trace index
    ([gdep_same_agent_lt], resting on [atrace_own_read]).  This file
    supplies the SEMANTIC half — the measure that refutes the remaining
    cross-agent cycles.

    THE MEASURE IS THE MESSAGE TIMESTAMP, and the whole argument is one
    segment lemma repeated around the cycle:

      S1.  If agent [i] READS timestamp [ts] at trace position [k], and
           later FULFILS timestamp [ts'] at position [k'], and the read
           is OK relative to [k'], then [ts < ts'].

    Walking a cycle, each cross rf edge's reader is followed in its own
    trace by the fulfil that sources the NEXT cross edge, so S1 makes the
    timestamps strictly increase around the cycle — impossible.

    WHAT "DISCIPLINED" MEANS, and why (the worklist's CORRECTION of
    2026-08-11).  The original sketch pinned SCfenced cycles with the
    WRITER-side fence ([fence rw,w] before the store).  That is refuted by
    LB with the fence BEFORE the load on both harts: the fence's [pr] half
    only covers reads po-BEFORE it, so nothing after it raises [w_vwNew]
    and EXT passes.  The load-bearing premise is READER-side acquire
    discipline: the cross read is either [aq]-labelled, or it is followed
    — strictly before the reader's next fulfil — by a [pr ∧ sw] fence
    ([fence r,rw]).  That is what [disciplined] below says, and it is
    exactly the kernel's discipline ([lw; fence r,rw] racy readers,
    [amoswap.w.aq] locks).

    THE SECOND ARM, [covered] (the owned-published refinement).  Reader
    discipline is TOO STRONG for a critical-section read: [ld x; sd y]
    inside a lock has a plain load and no fence before the store, so
    [disciplined] simply fails — and yet the edge is harmless, because
    the lock ACQUIRE preceded the read and had already pushed the
    reader's [w_vwNew] past the release timestamp, hence past the read
    message's.  [covered T k ts] says exactly that ([ts ≤ w_vwNew] in the
    read's PRE-state), and in that case EXT alone pins every later
    fulfil.  The per-edge obligation the theorem takes is therefore
    [edge_ok = disciplined ∨ covered].

    THE AUXILIARY INVARIANT [fwd_own].  The fence arm needs the read to
    raise [w_vrOld] to [ts], and [load_post_at] contributes the FORWARDED
    view [fwd_view], not the raw timestamp.  [fwd_own] — a forward-bank
    entry always names an OWN-authored log position — closes the gap: a
    FOREIGN read is never a bank hit, so [fwd_view = ts].  The bank starts
    empty ([ws_init]) and only [store_post_run] inserts, at the timestamp
    the step rule pins to the acting agent; and every agent's wstate
    at the START of the state phase is [ws_init], because the promise
    phase never touches [pa_ws] and [wp_init] starts there.  So [fwd_own]
    is DERIVED for a [wp_behavior] bundle, not assumed.

    WHAT IS *NOT* HERE.  The SCowned arm.  Per the worklist, an owned
    cross edge is refuted by the violation predicate φ, and φ speaks about
    promise-free RUNS — so it folds into W2b's induction, not into a
    standalone theorem.  The theorem below therefore takes "every
    cross-agent rf edge is [edge_ok]" as its premise.

    DEPENDENCY-FREE like its parents: stdpp only, no Iris, no Sail.
    [WeakAxiomatic] is imported FIRST (for its parked [WeakMem] fold
    lemmas) so that [WeakPromise]'s [wlabel] constructors shadow its
    [lbl] ones. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakAxiomatic.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakRobustTrace
                            WeakRobustGraph WeakRobust.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** [WeakMem]-level facts owed to the lift batch

    [WeakAxiomatic] parks [ws_le_coh] / [ws_le_vrOld] / [ws_le_vwOld] and
    the [coh] / [vrOld] fold lemmas; the [w_vwNew] projection of [ws_le]
    and the acquire-load [w_vwNew] fold are the two the aq arm of S1
    needs, and they are missing.  Proved exactly like their siblings. *)

Lemma ws_le_vwNew w1 w2 : ws_le w1 w2 → (w_vwNew w1 ≤ w_vwNew w2)%nat.
Proof. by intros (_ & _ & _ & _ & ? & _). Qed.

Local Lemma load_post_fold_vwNew_aq vpre ats ws a t :
  (a, t) ∈ ats →
  (t ≤ w_vwNew (foldl (λ w at_, load_post_at w true vpre at_.1 at_.2) ws ats))%nat.
Proof.
  revert ws. induction ats as [|p l IH]; intros ws Hin.
  { by apply elem_of_nil in Hin. }
  apply elem_of_cons in Hin as [<-|Hin]; [|by apply IH].
  simpl. etrans; [apply (load_post_at_vwNew_aq ws vpre a t)|].
  apply ws_le_vwNew, (load_post_fold_le true vpre l (load_post_at ws true vpre a t)).
Qed.

(** An ACQUIRE load pushes every byte's timestamp into [w_vwNew] — the
    reader-side ordering S1's aq arm rests on. *)
Lemma load_post_run_vwNew_aq ws base ts (j : nat) t :
  ts !! j = Some t → (t ≤ w_vwNew (load_post_run ws true base ts))%nat.
Proof.
  intros Ht. pose proof (lookup_lt_Some _ _ _ Ht) as Hj.
  rewrite /load_post_run /load_post_bytes.
  apply (load_post_fold_vwNew_aq _ _ _ (acc_addr base j) t).
  apply elem_of_list_lookup_2 with j.
  rewrite lookup_zip_with (lookup_seq_lt 0 (length ts) j Hj) Ht //.
Qed.

(* ------------------------------------------------------------------ *)
(** ** Label shapes the discipline speaks about *)

(** Does the label's READ half carry [aq]? *)
Definition lb_aq (l : wlabel) : bool :=
  match l with
  | LLoad aq _ _ _ => aq
  | LRmw aq _ _ _ _ => aq
  | _ => false
  end.

(** Is the label a [fence r,rw]-or-stronger — [pr] (past reads are
    pred) and [sw] (future writes are succ)?  Exactly the two bits
    [fence_post] needs to route [w_vrOld] into [w_vwNew]. *)
Definition lb_fence_prsw (l : wlabel) : Prop :=
  match l with LFence pr _ _ sw => pr = true ∧ sw = true | _ => False end.

(* ------------------------------------------------------------------ *)
(** ** DELIVERABLE 1: THE [fwd_own] INVARIANT *)

(** A forward-bank entry of agent [i]'s wstate names an OWN-authored log
    position.  (The timestamp convention is [WeakMem]'s: timestamp [S p]
    is log position [p], and timestamp 0 — the era-initial image — is
    excluded by the [0 < tf] conjunct.) *)
Definition fwd_own (log : list wmsg) (i : agent) (ws : wstate) : Prop :=
  ∀ a tf vf, w_fwd ws !! a = Some (tf, vf) →
    (0 < tf)%nat ∧ ∃ m, log !! (tf - 1)%nat = Some m ∧ wm_tid m = Some i.

Lemma fwd_own_init log i : fwd_own log i ws_init.
Proof. intros a tf vf. rewrite /ws_init /= lookup_empty. done. Qed.

(** THE COROLLARY: a foreign read is never forwarded.  Stated on the
    disjunction the call sites can supply — the read is [aq] (forwarding
    is disabled outright, [fwd_view_aq]) OR its source message is
    authored by somebody else (a bank hit would make it own-authored). *)
Definition read_unforwarded (log : list wmsg) (i : agent) (l : wlabel)
    (ts : nat) : Prop :=
  lb_aq l = true ∨
  (∃ m j, log !! (ts - 1)%nat = Some m ∧ wm_tid m = Some j ∧ j ≠ i).

Lemma fwd_own_read_unforwarded log i ws l a ts :
  fwd_own log i ws → read_unforwarded log i l ts →
  fwd_view ws (lb_aq l) a ts = ts.
Proof.
  intros Hfo [Haq|(m & j & Hm & Htid & Hne)].
  { rewrite Haq. apply fwd_view_aq. }
  rewrite /fwd_view. destruct (lb_aq l); [done|].
  destruct (w_fwd ws !! a) as [[tf vf]|] eqn:Hf; [|done].
  case_bool_decide as Heq; [|done]. subst tf.
  destruct (Hfo a ts vf Hf) as (_ & m' & Hm' & Htid').
  rewrite Hm in Hm'. by simplify_eq.
Qed.

(* ------------------------------------------------------------------ *)
(** ** [astep_ok]-level arithmetic

    The four facts S1 consumes, all stated on the ONE per-step
    specification [WeakPromiseFact.astep_ok] (one case per label, not one
    per rule) — in the style of [WeakRobustGraph]'s [astep_ok_*] block. *)

Section astep.
  Context {P : Type}.
  Implicit Types ag : wpagent P.

  (** [fwd_own] is a step invariant.  Only [store_post_run] inserts into
      the bank, and it inserts the FULFILLED timestamp, whose message the
      step rule pins to the acting agent [i] — that lookup is literally a
      conjunct of the [LStore]/[LRmw] arms of [astep_ok]. *)
  Lemma astep_ok_fwd_own img log i ag l f D :
    astep_ok img log i ag l f D →
    ∀ w, fwd_own log i w → fwd_own log i (f w).
  Proof.
    destruct l as [|aq lat base tvs|rl base data|aq rl base tvs data|pr pw sr sw|];
      simpl.
    - intros [-> _] w Hw. exact Hw.
    - intros (_ & -> & _) w Hw a tf vf. rewrite load_post_run_fwd.
      exact (Hw a tf vf).
    - intros (ts & kc & _ & Hlog & (_ & Hext) & -> & _) w Hw a tf vf Hlk.
      apply store_post_run_fwd_inv in Hlk as [->|Hlk];
        [|exact (Hw a tf vf Hlk)].
      split; [rewrite /fulfil_vpre in Hext; lia|].
      eexists. split; [exact Hlog|done].
    - intros (ts & kc & _ & _ & Hlog & _ & _ & (_ & Hext) & -> & _) w Hw a tf vf Hlk.
      apply store_post_run_fwd_inv in Hlk as [->|Hlk].
      + split; [rewrite /fulfil_vpre in Hext; lia|].
        eexists. split; [exact Hlog|done].
      + rewrite load_post_run_fwd in Hlk. exact (Hw a tf vf Hlk).
    - intros [-> _] w Hw a tf vf. rewrite fence_post_fwd. exact (Hw a tf vf).
    - intros [-> _] w Hw. exact Hw.
  Qed.

  (** EXT, in the form the measure wants: the fulfilling step's PRE-state
      write floor is strictly below the timestamp it fulfils.
      ([fulfil_ok]'s [fulfil_vpre < ts], and [fulfil_vpre ≥ w_vwNew]; for
      an [LRmw] the read half only raises [w_vwNew] further.) *)
  Lemma astep_ok_fulfil_ext img log i ag l f ts :
    astep_ok img log i ag l f (Some ts) → (w_vwNew (pa_ws ag) < ts)%nat.
  Proof.
    destruct l as [|aq lat base tvs|rl base data|aq rl base tvs data|pr pw sr sw|];
      simpl.
    - by intros [_ ?].
    - by intros (_ & _ & ?).
    - intros (ts' & kc & _ & _ & (_ & Hext) & _ & Heq). simplify_eq.
      rewrite /fulfil_vpre in Hext. lia.
    - intros (ts' & kc & _ & _ & _ & _ & _ & (_ & Hext) & _ & Heq). simplify_eq.
      rewrite /fulfil_vpre in Hext.
      have Hle : (w_vwNew (pa_ws ag)
                  ≤ w_vwNew (load_post_run (pa_ws ag) aq base (tvs.*1)))%nat
        by apply ws_le_vwNew, load_post_run_le.
      lia.
    - by intros [_ ?].
    - by intros [_ ?].
  Qed.

  (** THE SAME-STEP CASE, quantitatively.  [WeakRobustGraph]'s
      [astep_ok_read_fulfil_same] refutes "a step reads the very timestamp
      it fulfils"; the same geometry gives the STRICT INEQUALITY, which is
      what the cycle walk needs when the entry read and the exit fulfil
      are the SAME [LRmw] event.  (No discipline premise: the read half's
      [coh] gain is checked by the write half's own [fulfil_ok].) *)
  Lemma astep_ok_read_fulfil_lt img log i ag l f ts ts' a :
    astep_ok img log i ag l f (Some ts') → (a, ts) ∈ lb_reads l →
    (ts < ts')%nat.
  Proof.
    destruct l as [|aq lat base tvs|rl base data|aq rl base tvs data|pr pw sr sw|];
      simpl.
    - by intros [_ ?].
    - by intros (_ & _ & ?).
    - intros _ Hin%elem_of_nil. done.
    - intros (tsf & kc & Hlen & _ & _ & _ & _ & (Hcoh & _) & _ & Heq)
             [j [v [Hj ->]]]%elem_of_tvs_reads.
      injection Heq as Heq. subst tsf.
      have Hts : (tvs.*1) !! j = Some ts by rewrite list_lookup_fmap Hj.
      have Hjlt : (j < length data)%nat.
      { rewrite -Hlen. by eapply lookup_lt_Some. }
      have Hge := load_post_run_coh (pa_ws ag) aq base (tvs.*1) j ts Hts.
      have Hlt := Hcoh j Hjlt. rewrite /acc_addr in Hge. lia.
    - by intros [_ ?].
    - by intros [_ ?].
  Qed.

  (** THE AQ ARM's gain: an acquire read joins its timestamp into
      [w_vwNew] ([load_post_at]'s [vpost] feeds BOTH new floors, and
      forwarding is disabled by [fwd_view_aq]). *)
  Lemma astep_ok_read_vwNew_aq img log i ag l f D a ts :
    astep_ok img log i ag l f D → lb_aq l = true → (a, ts) ∈ lb_reads l →
    (ts ≤ w_vwNew (f (pa_ws ag)))%nat.
  Proof.
    destruct l as [|aq lat base tvs|rl base data|aq rl base tvs data|pr pw sr sw|];
      simpl.
    - intros _ _ Hin%elem_of_nil. done.
    - intros (_ & -> & _) -> [j [v [Hj ->]]]%elem_of_tvs_reads. simpl.
      have Hts : (tvs.*1) !! j = Some ts by rewrite list_lookup_fmap Hj.
      by apply (load_post_run_vwNew_aq (pa_ws ag) base (tvs.*1) j ts Hts).
    - intros _ _ Hin%elem_of_nil. done.
    - intros (tsf & kc & _ & _ & _ & _ & _ & _ & -> & _) ->
             [j [v [Hj ->]]]%elem_of_tvs_reads. simpl.
      have Hts : (tvs.*1) !! j = Some ts by rewrite list_lookup_fmap Hj.
      etrans; [by apply (load_post_run_vwNew_aq (pa_ws ag) base (tvs.*1) j ts Hts)|].
      apply ws_le_vwNew, store_post_run_le.
    - intros _ _ Hin%elem_of_nil. done.
    - intros _ _ Hin%elem_of_nil. done.
  Qed.

  (** THE FENCE ARM's gain, half 1: an UNFORWARDED read joins its
      timestamp into [w_vrOld] (this is where [fwd_own] pays). *)
  Lemma astep_ok_read_vrOld img log i ag l f D a ts :
    astep_ok img log i ag l f D →
    fwd_view (pa_ws ag) (lb_aq l) a ts = ts →
    (a, ts) ∈ lb_reads l →
    (ts ≤ w_vrOld (f (pa_ws ag)))%nat.
  Proof.
    destruct l as [|aq lat base tvs|rl base data|aq rl base tvs data|pr pw sr sw|];
      simpl.
    - intros _ _ Hin%elem_of_nil. done.
    - intros (_ & -> & _) Hfv [j [v [Hj ->]]]%elem_of_tvs_reads. simpl.
      have Hts : (tvs.*1) !! j = Some ts by rewrite list_lookup_fmap Hj.
      apply (load_post_run_vrOld' (pa_ws ag) aq base (tvs.*1) j ts Hts).
      rewrite /acc_addr. exact Hfv.
    - intros _ _ Hin%elem_of_nil. done.
    - intros (tsf & kc & _ & _ & _ & _ & _ & _ & -> & _) Hfv
             [j [v [Hj ->]]]%elem_of_tvs_reads. simpl.
      have Hts : (tvs.*1) !! j = Some ts by rewrite list_lookup_fmap Hj.
      etrans; [|apply ws_le_vrOld, store_post_run_le].
      apply (load_post_run_vrOld' (pa_ws ag) aq base (tvs.*1) j ts Hts).
      rewrite /acc_addr. exact Hfv.
    - intros _ _ Hin%elem_of_nil. done.
    - intros _ _ Hin%elem_of_nil. done.
  Qed.

  (** THE FENCE ARM's gain, half 2: a [pr ∧ sw] fence ships [w_vrOld]
      into [w_vwNew] ([fence_post]'s [v1] feeds from [w_vrOld] under [pr]
      and lands in [w_vwNew] under [sw]). *)
  Lemma astep_ok_fence_vwNew img log i ag l f D :
    astep_ok img log i ag l f D → lb_fence_prsw l →
    (w_vrOld (pa_ws ag) ≤ w_vwNew (f (pa_ws ag)))%nat.
  Proof.
    destruct l as [|aq lat base tvs|rl base data|aq rl base tvs data|pr pw sr sw|];
      simpl; try (by intros _ []).
    intros [-> _] [-> ->]. apply fence_post_vwNew_r.
  Qed.

End astep.

(* ------------------------------------------------------------------ *)
(** ** DELIVERABLE 2: READER DISCIPLINE

    Event [k] of the trace reads with [aq = true], or a [pr ∧ sw] fence
    sits strictly between [k] and [k'].  [k'] is the reader's next fulfil
    on the cycle; the definition takes it as a bound. *)
Definition disciplined {P D : Type} (T : atrace P D) (k k' : nat) : Prop :=
  (∃ ev, at_evs T !! k = Some ev ∧ lb_aq (ae_lb ev) = true) ∨
  (∃ k0 ev0, (k < k0)%nat ∧ (k0 < k')%nat ∧
             at_evs T !! k0 = Some ev0 ∧ lb_fence_prsw (ae_lb ev0)).

(** THE SECOND WAY an edge can be harmless — [covered], the
    owned-published (critical-section) shape.  A CS read is a PLAIN load
    and the reader's next store may follow with NO fence between
    ([ld x; sd y] inside a lock's critical section), so [disciplined]
    fails outright.  The edge is nevertheless harmless because the LOCK
    ACQUIRE PRECEDED the read: the reader's write floor was already at or
    above the lock-release timestamp, hence at or above the read
    message's timestamp, when the read happened — so EXT alone pins every
    later fulfil and none of the fence/aq machinery is needed.

    NOTE THE STATE: this is the PRE-state of event [k]
    ([at_ags T !! k] — the record the step at [k] runs FROM), not the
    post-state.  That is exactly what makes this a statement about what
    the reader had already acquired, and not a tautology about the read
    itself. *)
Definition covered {P D : Type} (T : atrace P D) (k : nat) (ts : nat) : Prop :=
  ∃ ag, at_ags T !! k = Some ag ∧ (ts ≤ w_vwNew (pa_ws ag))%nat.

(** THE PER-EDGE OBLIGATION the measure actually consumes: the reader is
    disciplined, or the message was already covered when it read. *)
Definition edge_ok {P D : Type} (T : atrace P D) (k k' : nat) (ts : nat) : Prop :=
  disciplined T k k' ∨ covered T k ts.

Lemma edge_ok_disciplined {P D : Type} (T : atrace P D) k k' ts :
  disciplined T k k' → edge_ok T k k' ts.
Proof. by left. Qed.

Lemma edge_ok_covered {P D : Type} (T : atrace P D) k k' ts :
  covered T k ts → edge_ok T k k' ts.
Proof. by right. Qed.

(* ------------------------------------------------------------------ *)
Section trace.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pdev : P → wlabel → P → bool).

  Implicit Types T : atrace P D.

  (* ---------------------------------------------------------------- *)
  (** ** [fwd_own] along a trace *)

  Lemma asteps_fwd_own img log i ags evs ag0 :
    asteps_wf pstep img log i ags evs →
    ags !! 0%nat = Some ag0 → fwd_own log i (pa_ws ag0) →
    ∀ k ag, ags !! k = Some ag → fwd_own log i (pa_ws ag).
  Proof.
    intros Hwf H0 Hfo0. induction k as [|k IH]; intros ag Hag.
    { rewrite H0 in Hag. by simplify_eq. }
    have [agk Hagk] : is_Some (ags !! k).
    { apply lookup_lt_is_Some_2. apply lookup_lt_Some in Hag. lia. }
    have Hfok := IH agk Hagk.
    have [ev Hev] : is_Some (evs !! k).
    { apply lookup_lt_is_Some_2. destruct Hwf as [Hlen _].
      apply lookup_lt_Some in Hag. lia. }
    destruct (asteps_wf_step pstep img log i ags evs k ev Hwf Hev)
      as (a1 & a2 & st' & f & Ha1 & Ha2 & _ & Hok & Heq).
    assert (a1 = agk) as -> by congruence.
    assert (a2 = ag) as -> by congruence.
    rewrite Heq /=. by eapply astep_ok_fwd_own.
  Qed.

  Lemma atrace_fwd_own img log i T ag0 :
    atrace_wf pstep img log i T →
    at_ags T !! 0%nat = Some ag0 → fwd_own log i (pa_ws ag0) →
    ∀ k ag, at_ags T !! k = Some ag → fwd_own log i (pa_ws ag).
  Proof. intros. by eapply asteps_fwd_own. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 3: THE SEGMENT LEMMA S1

      An OK read of [ts] at position [k] — disciplined, or already
      covered — followed at [k' > k] by a fulfil of [ts'], forces
      [ts < ts'].

      THREE ARMS, one shared tail.  All three do the same thing: push
      [ts] into [w_vwNew] at some position at or before [k'].  The aq arm
      does it AT the read ([load_post_at]'s [vpost] feeds [w_vwNew]); the
      fence arm does it at the fence ([w_vrOld] → [w_vwNew]); the covered
      arm does it BEFORE the read, with no machinery at all — the floor
      is already there in the read's pre-state.  Then [w_vwNew] is
      monotone along the trace and EXT closes at [k'].

      NOTE ON THE FOREIGNNESS PREMISE.  S1 asks for
      [read_unforwarded] — "the read is [aq], or its source message is
      authored by somebody else".  The aq arm does not use it at all
      (forwarding is disabled by [fwd_view_aq]); the fence arm does.
      The premise is discharged at the call site by case analysis on the
      source's author, which is legitimate because the OWN-author case
      never arises on a cycle: [WeakRobustGraph.atrace_own_read] already
      places an own read strictly AFTER the own fulfil, so a same-agent
      rf edge cannot participate in a cross-agent cycle — the measure
      only ever meets FOREIGN reads. *)
  Theorem atrace_S1 img log i T k k' ev ev' a ts ts' :
    atrace_wf pstep img log i T →
    (∀ n ag, at_ags T !! n = Some ag → fwd_own log i (pa_ws ag)) →
    at_evs T !! k = Some ev →
    (a, ts) ∈ lb_reads (ae_lb ev) →
    read_unforwarded log i (ae_lb ev) ts →
    at_evs T !! k' = Some ev' →
    ae_ts ev' = Some ts' →
    (k < k')%nat →
    edge_ok T k k' ts →
    (ts < ts')%nat.
  Proof.
    intros Hwf Hfo Hev Hin Hunf Hev' Hts' Hlt Hdisc.
    (* the READ step *)
    destruct (asteps_wf_step pstep img log i (at_ags T) (at_evs T) k ev Hwf Hev)
      as (ag & agn & st1 & f & Hag & Hagn & _ & Hok & Hagne).
    (* the FULFIL step *)
    destruct (asteps_wf_step pstep img log i (at_ags T) (at_evs T) k' ev'
                Hwf Hev')
      as (ag' & agn' & st2 & f' & Hag' & _ & _ & Hok' & _).
    rewrite Hts' in Hok'.
    have Hext : (w_vwNew (pa_ws ag') < ts')%nat by eapply astep_ok_fulfil_ext.
    (* the non-forwarding fact at the read *)
    have Hfv : fwd_view (pa_ws ag) (lb_aq (ae_lb ev)) a ts = ts.
    { eapply fwd_own_read_unforwarded; [exact (Hfo k ag Hag)|exact Hunf]. }
    (* IT SUFFICES to push [ts] into [w_vwNew] anywhere at or before [k'];
       [w_vwNew] only grows along the trace, and EXT closes at [k']. *)
    cut (∃ n agm, (n ≤ k')%nat ∧ at_ags T !! n = Some agm ∧
                  (ts ≤ w_vwNew (pa_ws agm))%nat).
    { intros (n & agm & Hn & Hagm & Hge).
      have Hmono : ws_le (pa_ws agm) (pa_ws ag').
      { eapply (asteps_ws_le pstep img log i (at_ags T) (at_evs T) n k');
          [exact Hwf|exact Hn|exact Hagm|exact Hag']. }
      have Hle := ws_le_vwNew _ _ Hmono. lia. }
    destruct Hdisc as [[(ev0 & Hev0 & Haq)
                       |(k0 & ev0 & Hk0 & Hk0' & Hev0 & Hfen)]
                      |(agc & Hagc & Hcov)].
    - (* THE AQ ARM: the read itself lands in [w_vwNew]. *)
      assert (ev0 = ev) as -> by congruence.
      exists (S k), agn. split_and!; [lia|exact Hagn|].
      rewrite Hagne /=.
      eapply (astep_ok_read_vwNew_aq img log i ag (ae_lb ev) f (ae_ts ev) a ts);
        [exact Hok|exact Haq|exact Hin].
    - (* THE FENCE ARM: the read lands in [w_vrOld]; the fence ships it. *)
      have Hro : (ts ≤ w_vrOld (pa_ws agn))%nat.
      { rewrite Hagne /=.
        eapply (astep_ok_read_vrOld img log i ag (ae_lb ev) f (ae_ts ev) a ts);
          [exact Hok|exact Hfv|exact Hin]. }
      have [ag0 Hag0] : is_Some (at_ags T !! k0).
      { apply lookup_lt_is_Some_2. destruct Hwf as [Hlen _].
        apply lookup_lt_Some in Hev0. lia. }
      have Hmono0 : ws_le (pa_ws agn) (pa_ws ag0).
      { eapply (asteps_ws_le pstep img log i (at_ags T) (at_evs T) (S k) k0);
          [exact Hwf|lia|exact Hagn|exact Hag0]. }
      have Hro0 : (ts ≤ w_vrOld (pa_ws ag0))%nat.
      { have Hle := ws_le_vrOld _ _ Hmono0. lia. }
      destruct (asteps_wf_step pstep img log i (at_ags T) (at_evs T) k0 ev0
                  Hwf Hev0)
        as (b0 & b1 & st3 & f0 & Hb0 & Hb1 & _ & Hok0 & Hb1e).
      assert (b0 = ag0) as -> by congruence.
      exists (S k0), b1. split_and!; [lia|exact Hb1|].
      rewrite Hb1e /=. etrans; [exact Hro0|].
      eapply (astep_ok_fence_vwNew img log i ag0 (ae_lb ev0) f0 (ae_ts ev0));
        [exact Hok0|exact Hfen].
    - (* THE COVERED ARM: the floor is already there, in the read's
         PRE-state.  Nothing to establish. *)
      assert (agc = ag) as -> by congruence.
      exists k, ag. split_and!; [lia|exact Hag|exact Hcov].
  Qed.

  (** S1 with the SAME-STEP case folded in: [k ≤ k'], and [edge_ok] is
      only demanded when the two positions differ.  This is the form the
      cycle walk applies, because an [LRmw] can be BOTH the entry read
      and the exit fulfil of a cycle segment — and in THAT case no
      premise is needed at all ([astep_ok_read_fulfil_lt] gets the strict
      inequality out of the rmw's own [fulfil_ok], which is checked on
      the post-[load_post_run] state). *)
  Corollary atrace_S1_le img log i T k k' ev ev' a ts ts' :
    atrace_wf pstep img log i T →
    (∀ n ag, at_ags T !! n = Some ag → fwd_own log i (pa_ws ag)) →
    at_evs T !! k = Some ev →
    (a, ts) ∈ lb_reads (ae_lb ev) →
    read_unforwarded log i (ae_lb ev) ts →
    at_evs T !! k' = Some ev' →
    ae_ts ev' = Some ts' →
    (k ≤ k')%nat →
    ((k < k')%nat → edge_ok T k k' ts) →
    (ts < ts')%nat.
  Proof.
    intros Hwf Hfo Hev Hin Hunf Hev' Hts' Hle Hdisc.
    destruct (decide (k = k')) as [->|Hne].
    - assert (ev' = ev) as -> by congruence.
      destruct (asteps_wf_step pstep img log i (at_ags T) (at_evs T) k' ev
                  Hwf Hev)
        as (ag & agn & st1 & f & _ & _ & _ & Hok & _).
      rewrite Hts' in Hok.
      by eapply (astep_ok_read_fulfil_lt img log i ag (ae_lb ev) f ts ts' a).
    - eapply (atrace_S1 img log i T k k' ev ev' a ts ts');
        [exact Hwf|exact Hfo|exact Hev|exact Hin|exact Hunf|exact Hev'
        |exact Hts'|lia|apply Hdisc; lia].
  Qed.

End trace.

(* ------------------------------------------------------------------ *)
(** ** The bundle-level premises *)

(** Every wstate reachable in every trace of the bundle satisfies
    [fwd_own] for its own agent. *)
Definition ptraces_fwd_own {P D : Type} (TS : ptraces P D) : Prop :=
  ∀ i T k ag, pt_trs TS !! i = Some T → at_ags T !! k = Some ag →
    fwd_own (pt_log TS) i (pa_ws ag).

(** THE PER-EDGE PREMISE.  "Every cross-agent rf edge into [(j, k)] is
    OK relative to EVERY later fulfil of agent [j]" — where OK is
    [edge_ok]: the reader is disciplined (aq / [fence r,rw]), or the
    message was already covered by the reader's write floor when it read
    (the critical-section shape).

    This is strictly stronger than the per-cycle statement the measure
    needs (which only speaks about the reader's next fulfil ON THE
    CYCLE), and is chosen because it is a property of the bundle alone —
    no cycle quantifier — so the Iris side can discharge it at the
    enumerated racy-read rules and at the lock rules.  It is also what
    the kernel actually gives: a racy reader's [aq] / [fence r,rw] sits
    before ANY subsequent store, and a critical-section reader's acquire
    floor covers EVERY later store of the section, not merely a
    distinguished one. *)
Definition rf_edges_ok {P D : Type} (TS : ptraces P D) : Prop :=
  ∀ e1 e2 T ts a k' ev',
    gev_ts TS e1 = Some ts → gev_reads TS e2 a ts → e1.1 ≠ e2.1 →
    pt_trs TS !! e2.1 = Some T →
    (e2.2 < k')%nat →
    at_evs T !! k' = Some ev' → is_Some (ae_ts ev') →
    edge_ok T e2.2 k' ts.

(** The ORIGINAL, discipline-only premise, kept because it is the shape
    the racy-read rules alone deliver — and it is strictly stronger. *)
Definition rf_disciplined {P D : Type} (TS : ptraces P D) : Prop :=
  ∀ e1 e2 T k' ev',
    grf TS e1 e2 → e1.1 ≠ e2.1 →
    pt_trs TS !! e2.1 = Some T →
    (e2.2 < k')%nat →
    at_evs T !! k' = Some ev' → is_Some (ae_ts ev') →
    disciplined T e2.2 k'.

Lemma rf_disciplined_edges_ok {P D : Type} (TS : ptraces P D) :
  rf_disciplined TS → rf_edges_ok TS.
Proof.
  intros H e1 e2 T ts a k' ev' Hts Hrd Hne HT Hlt Hev' Hsome.
  left. eapply H; [by exists ts, a|exact Hne|exact HT|exact Hlt|exact Hev'
                  |exact Hsome].
Qed.

(** Every agent's wstate is [ws_init] — the promise phase's invariant. *)
Definition cfg_ws_init {P D : Type} (c : wpcfg P D) : Prop :=
  ∀ i ag, pc_ags c !! i = Some ag → pa_ws ag = ws_init.

(* ------------------------------------------------------------------ *)
Section acyc.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pdev : P → wlabel → P → bool).

  Implicit Types TS : ptraces P D.
  Implicit Types e : gev.
  Implicit Types c : wpcfg P D.

  (* ---------------------------------------------------------------- *)
  (** ** From the bundle to the traces *)

  Lemma gev_reads_ev TS e a ts T :
    pt_trs TS !! e.1 = Some T → gev_reads TS e a ts →
    ∃ ev, at_evs T !! e.2 = Some ev ∧ (a, ts) ∈ lb_reads (ae_lb ev).
  Proof.
    intros HT (l & Hl & Hin). rewrite /gev_lb /gev_ev HT /= in Hl.
    destruct (at_evs T !! e.2) as [ev|]; simpl in Hl; [|done].
    simplify_eq. by exists ev.
  Qed.

  Lemma gev_ts_ev TS e ts T :
    pt_trs TS !! e.1 = Some T → gev_ts TS e = Some ts →
    ∃ ev, at_evs T !! e.2 = Some ev ∧ ae_ts ev = Some ts.
  Proof.
    intros HT. rewrite /gev_ts /gev_ev HT /=.
    destruct (at_evs T !! e.2) as [ev|]; simpl; [|done].
    intros Hts. by exists ev.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** [fwd_own] is DERIVED, not assumed *)

  Lemma cfg_ws_init_init img d0 ps :
    cfg_ws_init (wp_init (P:=P) (D:=D) img d0 ps).
  Proof.
    intros i ag Hlk. rewrite /wp_init /= in Hlk.
    rewrite list_lookup_fmap in Hlk.
    by destruct (ps !! i) as [p|]; simplify_eq/=.
  Qed.

  (** [WPPromise] does not touch [pa_ws] ([prom_add] rebuilds the record
      with the SAME wstate), so the whole promise phase preserves it. *)
  Lemma cfg_ws_init_promise_step c c' :
    cfg_ws_init c → wp_promise_step c c' → cfg_ws_init c'.
  Proof.
    intros H Hs.
    destruct (wp_promise_step_inv c c' Hs)
      as (j & agj & base & data & kc & Hlkj & _ & ->).
    intros i ag Hlk. simpl in Hlk.
    destruct (decide (i = j)) as [->|Hne].
    - rewrite list_lookup_insert in Hlk;
        [by eapply lookup_lt_Some|simplify_eq/=]. by eapply H.
    - rewrite list_lookup_insert_ne // in Hlk. by eapply H.
  Qed.

  Lemma cfg_ws_init_promise_run c c' :
    cfg_ws_init c → rtc (wp_promise_step (P:=P) (D:=D)) c c' → cfg_ws_init c'.
  Proof.
    intros H0 Hr. induction Hr as [|??? Hs _ IH]; [done|].
    apply IH. by eapply cfg_ws_init_promise_step.
  Qed.

  Lemma ptraces_of_fwd_own TS mid c :
    cfg_ws_init mid → ptraces_of pstep TS mid c → ptraces_fwd_own TS.
  Proof.
    intros Hinit (Himg & Hlog & _ & Hwf & Hfst & _).
    intros i T k ag HT Hag.
    have Hwfi := Hwf i T HT. have H0 := Hfst i T HT.
    destruct (atrace_first_is_Some pstep (pt_img TS) (pt_log TS) i T Hwfi)
      as [ag0 Hag0].
    have Hmid : pc_ags mid !! i = Some ag0 by rewrite -H0.
    eapply (atrace_fwd_own pstep (pt_img TS) (pt_log TS) i T ag0);
      [exact Hwfi|exact Hag0| |exact Hag].
    rewrite (Hinit i ag0 Hmid). apply fwd_own_init.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 4: THE MEASURE

      A cross-agent rf edge SITS ON A CYCLE when its reader can reach its
      source again.  Note this is exactly the shape
      [WeakRobustGraph.tc_gdep_cross] hands over. *)

  Definition on_cycle_rf TS (ts : nat) : Prop :=
    ∃ e1 e2 a, gev_ts TS e1 = Some ts ∧ gev_reads TS e2 a ts ∧
               e1.1 ≠ e2.1 ∧ rtc (gdep TS) e2 e1.

  (** THE CYCLE WALK, one step: from the reader, follow the path until it
      leaves the agent.  Everything up to the departure is same-agent, so
      the trace index only grows; the departing edge is cross-agent hence
      rf hence sourced at a FULFIL of the same agent — which is exactly
      S1's [k']. *)
  Lemma rtc_gdep_first_cross TS u v :
    ptraces_wf pstep TS → rtc (gdep TS) u v → u.1 ≠ v.1 →
    ∃ x y, u.1 = x.1 ∧ rtc (gdep TS) u x ∧ (u.2 ≤ x.2)%nat ∧
           grf TS x y ∧ x.1 ≠ y.1 ∧ rtc (gdep TS) y v.
  Proof.
    intros Hwf Hr. induction Hr as [z|u w v Huw Hwv IH]; intros Hne; [done|].
    destruct (decide (u.1 = w.1)) as [Hag|Hcross].
    - have Hlt : (u.2 < w.2)%nat
        by eapply (gdep_same_agent_lt pstep TS u w).
      destruct IH as (x & y & Hx1 & Hrx & Hx2 & Hrf & Hxy & Hry);
        [congruence|].
      exists x, y. split_and!; [congruence| |lia|done|done|done].
      eapply rtc_l; [exact Huw|exact Hrx].
    - exists u, w. split_and!; [done|apply rtc_refl|lia| |done|done].
      by destruct Huw as [(Hag & _)|Hrf].
  Qed.

  (** THE ADVANCE STEP: a cross rf edge on a cycle is followed, around
      the cycle, by a cross rf edge with a STRICTLY LARGER timestamp. *)
  Lemma on_cycle_rf_advance TS ts :
    ptraces_wf pstep TS → ptraces_fwd_own TS → rf_edges_ok TS →
    on_cycle_rf TS ts → ∃ ts', (ts < ts')%nat ∧ on_cycle_rf TS ts'.
  Proof.
    intros Hwf Hfo Hdisc (e1 & e2 & a & Hts1 & Hrd & Hne & Hback).
    have Hne' : e2.1 ≠ e1.1 by congruence.
    destruct (rtc_gdep_first_cross TS e2 e1 Hwf Hback Hne')
      as (x & y & Hx1 & Hrx & Hx2 & Hrfxy & Hxy & Hry).
    destruct Hrfxy as (ts2 & a2 & Hts2 & Hrd2).
    (* the reader's trace, which is also [x]'s *)
    have Hwfe2 : gev_wf TS e2 by eapply gev_reads_wf.
    apply gev_wf_bounds in Hwfe2 as (T & HT & _).
    have HTx : pt_trs TS !! x.1 = Some T by rewrite -Hx1.
    destruct (gev_reads_ev TS e2 a ts T HT Hrd) as (ev & Hev & Hinr).
    destruct (gev_ts_ev TS x ts2 T HTx Hts2) as (ev2 & Hev2 & Hts2').
    (* the source of the ENTRY edge is foreign, so the read is not
       forwarded *)
    destruct (gev_ts_msg pstep TS e1 ts Hwf Hts1) as (base & data & kc & Hm).
    have Hunf : read_unforwarded (pt_log TS) e2.1 (ae_lb ev) ts.
    { right. exists (WMsg base data (Some e1.1) kc), e1.1.
      split_and!; [exact Hm|done|exact Hne]. }
    (* S1 *)
    have Hlt : (ts < ts2)%nat.
    { eapply (atrace_S1_le pstep (pt_img TS) (pt_log TS) e2.1 T e2.2 x.2
                ev ev2 a ts ts2).
      - by eapply Hwf.
      - intros n ag Hag. by eapply (Hfo e2.1 T n ag HT Hag).
      - exact Hev.
      - exact Hinr.
      - exact Hunf.
      - exact Hev2.
      - exact Hts2'.
      - exact Hx2.
      - intros Hklt. eapply (Hdisc e1 e2 T ts a x.2 ev2);
          [exact Hts1|exact Hrd|exact Hne|exact HT|exact Hklt|exact Hev2|].
        rewrite Hts2'. by eexists. }
    exists ts2. split; [exact Hlt|].
    exists x, y, a2. split_and!; [exact Hts2|exact Hrd2|exact Hxy|].
    eapply rtc_transitive; [exact Hry|].
    eapply rtc_l; [|exact Hrx]. right. by exists ts, a.
  Qed.

  (** A timestamp on a cycle is a real log position, hence bounded. *)
  Lemma on_cycle_rf_bounded TS ts :
    ptraces_wf pstep TS → on_cycle_rf TS ts →
    (ts ≤ length (pt_log TS))%nat.
  Proof.
    intros Hwf (e1 & e2 & a & Hts1 & _).
    destruct (gev_ts_msg pstep TS e1 ts Hwf Hts1) as (base & data & kc & Hm).
    apply lookup_lt_Some in Hm.
    have Hpos : (0 < ts)%nat by eapply (gev_ts_pos pstep TS).
    lia.
  Qed.

  (** THE REFUTATION: the advance step cannot be iterated inside a
      bounded set of timestamps.  (The measure is [length log - ts]; no
      cycle-sequence extraction is needed.) *)
  Lemma on_cycle_rf_empty TS :
    ptraces_wf pstep TS → ptraces_fwd_own TS → rf_edges_ok TS →
    ∀ ts, ¬ on_cycle_rf TS ts.
  Proof.
    intros Hwf Hfo Hdisc.
    have Hgen : ∀ n ts, (length (pt_log TS) - ts ≤ n)%nat →
                        ¬ on_cycle_rf TS ts.
    { induction n as [|n IH]; intros ts Hn Hoc.
      - have Hb := on_cycle_rf_bounded TS ts Hwf Hoc.
        destruct (on_cycle_rf_advance TS ts Hwf Hfo Hdisc Hoc)
          as (ts' & Hlt & Hoc').
        have Hb' := on_cycle_rf_bounded TS ts' Hwf Hoc'. lia.
      - destruct (on_cycle_rf_advance TS ts Hwf Hfo Hdisc Hoc)
          as (ts' & Hlt & Hoc').
        eapply (IH ts'); [|exact Hoc'].
        have Hb' := on_cycle_rf_bounded TS ts' Hwf Hoc'. lia. }
    intros ts. by eapply (Hgen (length (pt_log TS) - ts)%nat).
  Qed.

  (** ** THE THEOREM *)

  Theorem gdep_acyclic_edges_ok TS :
    ptraces_wf pstep TS → ptraces_fwd_own TS → rf_edges_ok TS →
    gdep_acyclic TS.
  Proof.
    intros Hwf Hfo Hdisc e Hc.
    destruct (tc_gdep_cross pstep TS e Hwf Hc)
      as (x & y & Hrx & Hrf & Hcross & Hry).
    destruct Hrf as (ts & a & Hts & Hrd).
    eapply (on_cycle_rf_empty TS Hwf Hfo Hdisc ts).
    exists x, y, a. split_and!; [exact Hts|exact Hrd|exact Hcross|].
    eapply rtc_transitive; [exact Hry|exact Hrx].
  Qed.

  (** The ORIGINAL statement, now a corollary: discipline alone is a
      special case of [edge_ok]. *)
  Corollary gdep_acyclic_disciplined TS :
    ptraces_wf pstep TS → ptraces_fwd_own TS → rf_disciplined TS →
    gdep_acyclic TS.
  Proof.
    intros Hwf Hfo Hdisc. eapply gdep_acyclic_edges_ok;
      [exact Hwf|exact Hfo|by apply rf_disciplined_edges_ok].
  Qed.

  (** ... at the behavior level, with [fwd_own] DISCHARGED.  Only the
      per-edge obligation remains a premise (and the SCowned arm, which
      lives in W2b — see the header). *)
  Theorem wp_behavior_gdep_acyclic img d0 ps c :
    pdev_ok pstep pdev →
    lat_free_prog pstep → wp_behavior pstep img d0 ps c →
    ∃ mid TS,
      rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid ∧
      ptraces_of pstep TS mid c ∧
      no_promises c ∧
      ptraces_wf pstep TS ∧
      ptraces_fwd_own TS ∧
      (rf_edges_ok TS → gdep_acyclic TS).
  Proof.
    intros Hpok Hlfp Hb.
    destruct (wp_behavior_traced pstep pdev img d0 ps c Hpok Hlfp Hb)
      as (mid & TS & Hprom & HTS & Hnp).
    have Hwf : ptraces_wf pstep TS by eapply ptraces_of_wf.
    have Hinit : cfg_ws_init mid.
    { eapply cfg_ws_init_promise_run; [apply cfg_ws_init_init|exact Hprom]. }
    have Hfo : ptraces_fwd_own TS by eapply ptraces_of_fwd_own.
    exists mid, TS. split_and!; [done|done|done|done|done|].
    intros Hdisc. by eapply gdep_acyclic_edges_ok.
  Qed.

End acyc.

(* ------------------------------------------------------------------ *)
(** ** What W2b inherits from this file

    - [fwd_own] / [ptraces_fwd_own] and [ptraces_of_fwd_own]: the forward
      bank never names a foreign write, DERIVED from [wp_init] through
      the promise phase.  Reusable wherever a read's [w_vrOld] gain must
      be the raw timestamp.
    - [disciplined] / [covered] / [edge_ok] / [rf_edges_ok]: the exact
      per-edge obligation the Iris layer must discharge — at the
      racy-read rules ([disciplined]) and at the lock / critical-section
      rules ([covered], a pure statement about the reader's [w_vwNew] at
      the read).  Note the shape: it is per-(rf edge, later fulfil), with
      NO cycle quantifier.  [rf_disciplined] and
      [rf_disciplined_edges_ok] keep the discipline-only form available.
    - [atrace_S1] / [atrace_S1_le]: the segment lemma, the reusable
      "a disciplined read is ordered before every later fulfil" fact.
    - [gdep_acyclic_edges_ok] / [wp_behavior_gdep_acyclic]: the
      standalone acyclicity theorem, which is what W2b's topological sort
      consumes.  [gdep_acyclic_disciplined] is the discipline-only
      corollary, kept because it is the shape the racy-read rules alone
      deliver.

    NOT here, deliberately: the SCowned arm (it needs φ, which speaks
    about promise-free runs — the worklist's "acyclicity-under-φ is not
    standalone"), and any use of the classification [cls] or the
    publication [pub]. *)
