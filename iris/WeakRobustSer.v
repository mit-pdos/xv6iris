(** * WeakRobustSer.v — the WRITE-SERIALIZATION theorem
      (M6 W2b, the second pillar: [co ⊆ tc(D)] per byte)

    [WeakRobustAcyc.v] delivers the FIRST pillar of W2b — the dependency
    graph [gdep = gpo ∪ grf] over a traced behavior is ACYCLIC, so it can
    be topologically sorted.  A topological sort alone does not give a
    promise-free run: the sorted order must also agree with the MEMORY's
    own order, i.e. for every byte [a] the writes of [a] must appear in
    TIMESTAMP order along any linearization of [gdep].  That is exactly
    "coherence order is contained in the transitive closure of the
    dependency relation", per byte:

      [writes_b a e1 t1 → writes_b a e2 t2 → t1 < t2 → tc gdep e1 e2].

    This file proves it, from LOCAL, per-byte premises that the Iris side
    of W2b will discharge at the kernel's data-structure rules.

    THE VOCABULARY.  "[e] writes byte [a] at [t]" is [writes_b TS a e t]:
    [e] fulfilled timestamp [t] ([gev_ts]) and the message at log position
    [t - 1] covers byte [a] ([msg_byte]).  The message's author is [e.1]
    ([WeakRobustGraph.gev_ts_msg]), which is what turns "same author" into
    "same trace" and "different author" into "the message's [wm_tid]
    disagrees" — the two facts the whole development runs on.

    THE FOUR DELIVERABLES.

    (1) THE SAME-AUTHOR LEMMA [ser_same_author], PREMISE-FREE.  Two writes
        of the same byte by the same agent are in program order, and in
        TIMESTAMP order: a fulfil of [t] demands [coh a < t] in its
        pre-state ([astep_ok_fulfil_coh]) and leaves [coh a ≥ t] in its
        post-state ([astep_ok_fulfil_post_coh], new here), and [coh] only
        grows along a trace ([asteps_ws_le]).  So the earlier timestamp is
        the earlier trace position — no discipline, no classification, no
        premise beyond [ptraces_wf].

    (2) THE PER-BYTE PREMISES.  A byte is [sw_byte] (single writer),
        [excl_byte] (every write is either behind an all-same-author
        prefix or is an rmw READING the byte — the lock/AMO shape), or
        satisfies [handoff] (a cross-author co-consecutive pair is
        separated by a SYNC byte: a same-author-as-[e1], po-later write of
        a sync byte [b] at [tr], read back by [e2]'s agent po-before [e2]
        at [t_star ≥ tr] — the release/acquire shape).  [byte_ok] is the
        disjunction.

    (3) THE THEOREM [co_serialized].  Structure, and the one structural
        choice that makes it go through: STRATIFICATION.  Sync bytes are
        closed FIRST ([sync_connect], which uses only the [sw]/[excl]
        arms and therefore never recurses into [handoff]); the general
        per-byte theorem then uses [sync_connect] non-recursively.  Within
        each layer the argument is: prove connectivity for CO-CONSECUTIVE
        pairs, then chain ([writes_b_chain], a fuel induction on
        [t2 - t1]).  For a consecutive pair the three arms are
          - same author → (1);
          - [excl] → the rmw's own [excl_ok] forces its read timestamp to
            be EXACTLY [t1] (anything lower would put [t1], a foreign
            write, inside the exclusivity window; anything higher would be
            a write strictly between), so the edge is a single rf edge and
            NO recursion is needed;
          - [handoff] → the path [e1 →po? er →tc(sync b) e_star →rf rr
            →po? e2].

    (4) THE BEHAVIOR-LEVEL WRAPPER [wp_behavior_co_serialized], which
        discharges [ptraces_wf] and [writes_fulfilled] from
        [wp_behavior_fulfil_once] and leaves only the packaged byte
        premises ([ptraces_bytes_ok]) to the caller.

    DELTAS FROM THE W2b DESIGN NOTE (all recorded here deliberately;
    every one WEAKENS a premise or removes one):

    - CO-CONSECUTIVENESS is spelled on the LOG, not on the events:
      [co_consec TS a t1 t2 := ¬ writes_in (pt_log TS) a t1 (t2 - 1)].
      This is a STRONGER antecedent than "no EVENT writes [a] strictly
      between" (an event write is a log write), hence [handoff] is a
      WEAKER premise; and it is DECIDABLE ([writes_inb]), which is what
      lets the chaining induction case-split without classical logic.

    - THE rf PREMISES [Hrf_total] / [Hrf_fun] are replaced by the single
      premise [writes_fulfilled] ("every log message is fulfilled by some
      event").  It IMPLIES the totality the proof uses (the source of a
      read of a nonzero timestamp) and it is what
      [wp_behavior_fulfil_once] actually delivers; rf FUNCTIONALITY is not
      a premise at all — it is derived from [ptraces_wf] via
      [WeakRobustGraph.grf_source_unique].

    - [handoff] does NOT carry [(t1 ≤ tr)] nor an explicit source event
      for [t_star]: neither is used (the path direction is carried by the
      two po bounds [e1.2 ≤ er.2] and [rr.2 ≤ e2.2]), and the source of
      [t_star] is produced by [writes_fulfilled].

    DEPENDENCY-FREE like its parents: stdpp only, no Iris, no Sail.
    [WeakAxiomatic] is imported FIRST (for the parked [WeakMem] fold
    lemmas [store_post_run_coh] / [ws_le_coh]) so that [WeakPromise]'s
    [wlabel] constructors shadow its [lbl] ones.  Deliberately INDEPENDENT
    of [WeakRobustAcyc.v]: the two pillars of W2b are proved from disjoint
    premises and the few three-line helpers they share are re-derived. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakAxiomatic.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakRobustTrace
                            WeakRobustGraph.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** [astep_ok]-level facts

    Three additions to [WeakRobustGraph]'s [astep_ok_*] block, in the same
    style: one case per LABEL, not one per rule. *)

Section astep.
  Context {P : Type}.
  Implicit Types ag : wpagent P.

  (** THE FULFIL RAISES [coh].  [WeakRobustGraph.astep_ok_fulfil_coh] is
      the PRE-state half ([coh a < ts] on every byte of the message); this
      is the POST-state half ([coh a ≥ ts] on the same bytes), and the two
      together are the whole content of the same-author lemma.  The
      geometry: the message at [ts - 1] is [WMsg base data (Some i)] with
      [base]/[data] READ OFF THE LABEL, and the label's [f] ends in
      [store_post_run _ rl base (length data) ts] — so a byte of the
      message is a byte of the store run. *)
  Lemma astep_ok_fulfil_post_coh img log i ag l f ts m a :
    astep_ok img log i ag l f (Some ts) →
    log !! (ts - 1)%nat = Some m → is_Some (msg_byte m a) →
    (ts ≤ coh (f (pa_ws ag)) a)%nat.
  Proof.
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                  |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
      simpl.
    - by intros [_ ?].
    - by intros (_ & _ & ?).
    - intros (ts' & kc & _ & Hlog & _ & -> & Heq) Hm Hb.
      injection Heq as Heq. subst ts'.
      rewrite Hlog in Hm. simplify_eq.
      destruct (msg_byte_in_range _ _ Hb) as (j & Hj & Ha).
      simpl in Hj, Ha. subst a.
      have Hacc : base + Z.of_nat j = acc_addr base j by rewrite /acc_addr.
      rewrite Hacc. by apply store_post_run_d_coh.
    - intros (ts' & kc & _ & _ & Hlog & _ & _ & _ & -> & Heq) Hm Hb.
      injection Heq as Heq. subst ts'.
      rewrite Hlog in Hm. simplify_eq.
      destruct (msg_byte_in_range _ _ Hb) as (j & Hj & Ha).
      simpl in Hj, Ha. subst a.
      have Hacc : base + Z.of_nat j = acc_addr base j by rewrite /acc_addr.
      rewrite Hacc. by apply store_post_run_d_coh.
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    (* THE RMW SPLIT (S2) *)
    - by intros (_ & _ & ?).
    - intros (ts' & kc & R & _ & Hlog & _ & _ & _ & _ & _ & -> & Heq) Hm Hb.
      injection Heq as Heq. subst ts'.
      rewrite Hlog in Hm. simplify_eq.
      destruct (msg_byte_in_range _ _ Hb) as (j & Hj & Ha).
      simpl in Hj, Ha. subst a.
      have Hacc : ybase + Z.of_nat j = acc_addr ybase j by rewrite /acc_addr.
      rewrite Hacc. by apply store_post_run_d_coh.
  Qed.

  (** A step that BOTH reads [(a, tr)] and fulfils [ts] is an [LRmw]
      (only [LRmw] has both halves), and its read timestamp is strictly
      below the timestamp it fulfils — the same geometry as
      [WeakRobustGraph.astep_ok_read_fulfil_same], quantified. *)
  Lemma astep_ok_read_lt img log i ag l f ts tr a :
    astep_ok img log i ag l f (Some ts) → (a, tr) ∈ lb_reads l →
    (tr < ts)%nat.
  Proof.
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                  |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
      simpl.
    - by intros [_ ?].
    - by intros (_ & _ & ?).
    - intros _ Hin%elem_of_nil. done.
    - intros (tsf & kc & Hlen & _ & _ & _ & _ & (Hcoh & _) & _ & Heq)
             [j [v [Hj ->]]]%elem_of_tvs_reads.
      injection Heq as Heq. subst tsf.
      have Hts : (tvs.*1) !! j = Some tr by rewrite list_lookup_fmap Hj.
      have Hjlt : (j < length data)%nat.
      { rewrite -Hlen. by eapply lookup_lt_Some. }
      have Hge := load_post_run_d_coh (pa_ws ag) aq
                    (srcs_view (pa_ws ag) asrc) base (tvs.*1) j tr Hts.
      have Hlt := Hcoh j Hjlt. rewrite /acc_addr in Hge. lia.
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    (* THE RMW SPLIT (S2): VACUOUS on both halves — the exclusive read
       fulfils nothing, the conditional write reads nothing (design §7).
       The pair's own version of this fact is owed by S4. *)
    - by intros (_ & _ & ?).
    - intros _ Hin%elem_of_nil. done.
  Qed.

  (** ... and its EXCLUSIVITY WINDOW: no OTHER agent's write to the byte
      it read lands in [(tr, ts - 1]].  This is [excl_ok], the [LRmw]
      arm's own conjunct, transported from the label's index [j] to the
      byte address [base + j] the read names. *)
  Lemma astep_ok_read_excl img log i ag l f ts tr a :
    astep_ok img log i ag l f (Some ts) → (a, tr) ∈ lb_reads l →
    ¬ writes_in_by log (λ tid, tid ≠ Some i) a tr (ts - 1)%nat.
  Proof.
    destruct l as [|aq lat base tvs asrc|rl base data asrc vsrc
                  |aq rl base tvs data asrc vsrc|pr pw sr sw| |rdw wsrc|csrc| |xaq xbase xtvs xasrc|yrl ybase ydata yasrc yvsrc];
      simpl.
    - by intros [_ ?].
    - by intros (_ & _ & ?).
    - intros _ Hin%elem_of_nil. done.
    - intros (tsf & kc & _ & _ & _ & _ & Hexcl & _ & _ & Heq)
             [j [v [Hj ->]]]%elem_of_tvs_reads.
      injection Heq as Heq. subst tsf.
      exact (Hexcl j tr v Hj).
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    - by intros [_ ?].
    (* THE RMW SPLIT (S2): VACUOUS on both halves (design §7) *)
    - by intros (_ & _ & ?).
    - intros _ Hin%elem_of_nil. done.
  Qed.

End astep.

(* ------------------------------------------------------------------ *)
(** ** DELIVERABLE 2: the vocabulary and the per-byte premises

    All of these are functions of the trace bundle alone — no [pstep], no
    Iris — so the W2b simulation can state them once and the Iris side can
    discharge them per data structure. *)

(** "[e] writes byte [a] at timestamp [t]": [e] fulfilled [t], and the
    message at log position [t - 1] covers byte [a].  (The message's
    AUTHOR is [e.1], by [WeakRobustGraph.gev_ts_msg] — not restated
    here.) *)
Definition writes_b {P D : Type} (TS : ptraces P D) (a : Z) (e : gev) (t : nat)
    : Prop :=
  gev_ts TS e = Some t ∧
  ∃ m, pt_log TS !! (t - 1)%nat = Some m ∧ is_Some (msg_byte m a).

(** CO-CONSECUTIVE: no message strictly between [t1] and [t2] writes [a].
    Spelled on the LOG (not on the events) — see the header: stronger
    antecedent, hence weaker [handoff], and DECIDABLE via
    [WeakMem.writes_inb]. *)
Definition co_consec {P D : Type} (TS : ptraces P D) (a : Z) (t1 t2 : nat) : Prop :=
  ¬ writes_in (pt_log TS) a t1 (t2 - 1)%nat.

(** SINGLE WRITER: all writes of [a] come from one agent. *)
Definition sw_byte {P D : Type} (TS : ptraces P D) (a : Z) : Prop :=
  ∀ e1 e2 t1 t2, writes_b TS a e1 t1 → writes_b TS a e2 t2 → e1.1 = e2.1.

(** EXCLUSIVITY-CHAINED: every write of [a] either has ONLY same-author
    writes below it, or is an rmw whose read half READS byte [a].  (The
    read-half membership [gev_reads TS e a tr] is exactly what an [LRmw]
    label gives: its read range and its write range share [base] and
    length.  No further label inspection is asked of the caller.) *)
Definition excl_byte {P D : Type} (TS : ptraces P D) (a : Z) : Prop :=
  ∀ e t, writes_b TS a e t →
    (∀ e' t', writes_b TS a e' t' → (t' < t)%nat → e'.1 = e.1) ∨
    (∃ tr, gev_reads TS e a tr).

(** THE OWNED-BYTE HANDOFF: a CROSS-AUTHOR co-consecutive pair is
    separated by a SYNC byte.  The shape (and only the shape) is
    load-bearing: a write of a sync byte [b] by [e1]'s OWN agent at or
    after [e1] in program order, and a read of [b] by [e2]'s agent at or
    before [e2] in program order, at a timestamp at least the write's.
    The two edge cases are fine and need no special premise: [er = e1]
    (when [a] itself is sync) and [rr = e2] (when [e2] is the rmw that
    reads [b]). *)
Definition handoff {P D : Type} (TS : ptraces P D) (sync : Z → Prop) (a : Z)
    : Prop :=
  ∀ e1 e2 t1 t2,
    writes_b TS a e1 t1 → writes_b TS a e2 t2 →
    e1.1 ≠ e2.1 → (t1 < t2)%nat → co_consec TS a t1 t2 →
    ∃ (b : Z) (er : gev) (tr : nat) (rr : gev) (t_star : nat),
      sync b ∧
      writes_b TS b er tr ∧ er.1 = e1.1 ∧ (e1.2 ≤ er.2)%nat ∧
      gev_reads TS rr b t_star ∧ rr.1 = e2.1 ∧ (rr.2 ≤ e2.2)%nat ∧
      (tr ≤ t_star)%nat.

(** THE PER-BYTE OBLIGATION. *)
Definition byte_ok {P D : Type} (TS : ptraces P D) (sync : Z → Prop) (a : Z)
    : Prop :=
  sw_byte TS a ∨ excl_byte TS a ∨ handoff TS sync a.

(** THE BUNDLE-LEVEL PREMISE, packaged for the caller: sync bytes are
    closed FIRST (they may not use [handoff] — see the stratification note
    in the header), and every byte is [byte_ok]. *)
Definition ptraces_bytes_ok {P D : Type} (TS : ptraces P D) (sync : Z → Prop)
    : Prop :=
  (∀ b, sync b → sw_byte TS b ∨ excl_byte TS b) ∧ (∀ a, byte_ok TS sync a).

(** FULFILMENT TOTALITY: every log message is fulfilled by some event.
    This is the accounting half of [wp_behavior_fulfil_once] and it
    replaces the rf-totality premise of the design note (see the header):
    it implies it, and it is what makes [co_consec] usable as an
    induction handle. *)
Definition writes_fulfilled {P D : Type} (TS : ptraces P D) : Prop :=
  ∀ (t : nat) m, (0 < t)%nat → pt_log TS !! (t - 1)%nat = Some m →
    ∃ e, gev_ts TS e = Some t.

(** THE CONCLUSION, per byte: coherence order is contained in [tc gdep]. *)
Definition co_tc {P D : Type} (TS : ptraces P D) (a : Z) : Prop :=
  ∀ e1 e2 t1 t2, writes_b TS a e1 t1 → writes_b TS a e2 t2 → (t1 < t2)%nat →
    tc (gdep TS) e1 e2.

(* ------------------------------------------------------------------ *)
Section ser.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pdev : P → wlabel → P → bool).

  Implicit Types TS : ptraces P D.
  Implicit Types T : atrace P D.
  Implicit Types e : gev.
  Implicit Types c : wpcfg P D.

  (* ---------------------------------------------------------------- *)
  (** ** [writes_b] basics *)

  Lemma writes_b_wf TS a e t : writes_b TS a e t → gev_wf TS e.
  Proof. intros (Hts & _). by eapply gev_ts_wf. Qed.

  Lemma writes_b_pos TS a e t :
    ptraces_wf pstep TS → writes_b TS a e t → (0 < t)%nat.
  Proof. intros Hwf (Hts & _). by eapply gev_ts_pos. Qed.

  (** The message a write names is authored by the writing agent. *)
  Lemma writes_b_author TS a e t :
    ptraces_wf pstep TS → writes_b TS a e t →
    ∃ m, pt_log TS !! (t - 1)%nat = Some m ∧ is_Some (msg_byte m a) ∧
         wm_tid m = Some e.1.
  Proof.
    intros Hwf Hw. have Hw' := Hw. destruct Hw' as (Hts & m & Hm & Hb).
    destruct (gev_ts_msg pstep TS e t Hwf Hts) as (base & data & kc & Hm').
    rewrite Hm' in Hm. simplify_eq. by exists (WMsg base data (Some e.1) kc).
  Qed.

  (** Two events fulfilling the same timestamp are the same event — rf
      FUNCTIONALITY, derived (not assumed). *)
  Lemma writes_b_unique TS a1 a2 e1 e2 t :
    ptraces_wf pstep TS → writes_b TS a1 e1 t → writes_b TS a2 e2 t →
    e1 = e2.
  Proof.
    intros Hwf (H1 & _) (H2 & _). by eapply grf_source_unique.
  Qed.

  (** The trace event a write names, and the [coh] bracket around it: the
      PRE-state of the fulfilling step has [coh a < t], the POST-state has
      [coh a ≥ t]. *)
  Lemma writes_b_coh TS a e t T :
    ptraces_wf pstep TS → pt_trs TS !! e.1 = Some T → writes_b TS a e t →
    ∃ ag agn,
      at_ags T !! e.2 = Some ag ∧ at_ags T !! S e.2 = Some agn ∧
      (coh (pa_ws ag) a < t)%nat ∧ (t ≤ coh (pa_ws agn) a)%nat.
  Proof.
    intros Hwf HT (Hts & m & Hm & Hb).
    have Hts' := Hts. rewrite /gev_ts /gev_ev HT /= in Hts'.
    destruct (at_evs T !! e.2) as [ev|] eqn:Hev; simpl in Hts'; [|done].
    have Hgev : gev_ev TS e = Some ev by rewrite /gev_ev HT /= Hev.
    destruct (gev_step pstep TS e ev Hwf Hgev)
      as (T' & ag & agn & st' & f & HT' & Hag & Hagn & _ & Hok & Hagne).
    assert (T' = T) as -> by congruence.
    rewrite Hts' in Hok.
    exists ag, agn. split_and!; [done|done| |].
    - by eapply astep_ok_fulfil_coh.
    - rewrite Hagne. by eapply astep_ok_fulfil_post_coh.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 1: THE SAME-AUTHOR LEMMA (premise-free)

      Same agent, same byte, smaller timestamp ⇒ EARLIER in the trace.
      The whole content is the [coh] bracket of [writes_b_coh] plus
      monotonicity of [coh] along a trace. *)

  Theorem ser_same_author TS a e1 e2 t1 t2 :
    ptraces_wf pstep TS →
    writes_b TS a e1 t1 → writes_b TS a e2 t2 →
    e1.1 = e2.1 → (t1 < t2)%nat →
    gpo TS e1 e2.
  Proof.
    intros Hwf H1 H2 Hag Hlt.
    have Hw1 : gev_wf TS e1 by eapply writes_b_wf.
    have Hw2 : gev_wf TS e2 by eapply writes_b_wf.
    destruct (proj1 (gev_wf_bounds TS e1) Hw1) as (T & HT & _).
    have HT2 : pt_trs TS !! e2.1 = Some T by rewrite -Hag.
    destruct (writes_b_coh TS a e1 t1 T Hwf HT H1)
      as (ag1 & agn1 & Hag1 & Hagn1 & Hlo1 & Hhi1).
    destruct (writes_b_coh TS a e2 t2 T Hwf HT2 H2)
      as (ag2 & agn2 & Hag2 & Hagn2 & Hlo2 & Hhi2).
    have Hatr : atrace_wf pstep (pt_img TS) (pt_log TS) e1.1 T by apply Hwf.
    destruct (Nat.lt_trichotomy e1.2 e2.2) as [Hk|[Hk|Hk]].
    - split_and!; [done|done|done|done].
    - (* same index and same agent: the same event, so [t1 = t2] *)
      exfalso.
      have He : e1 = e2.
      { destruct e1 as [i1 k1], e2 as [i2 k2]. simpl in Hag, Hk. by subst. }
      subst e2. destruct H1 as (Hts1 & _). destruct H2 as (Hts2 & _).
      rewrite Hts1 in Hts2. simplify_eq. lia.
    - (* [e2] came first: then [coh a] was already ≥ [t2] when [e1] ran *)
      exfalso.
      have Hmono : ws_le (pa_ws agn2) (pa_ws ag1).
      { eapply (asteps_ws_le pstep (pt_img TS) (pt_log TS) e1.1
                  (at_ags T) (at_evs T) (S e2.2) e1.2);
          [exact Hatr|lia| |exact Hag1].
        exact Hagn2. }
      have Hle := ws_le_coh _ _ a Hmono. lia.
  Qed.

  Corollary ser_same_author_tc TS a e1 e2 t1 t2 :
    ptraces_wf pstep TS →
    writes_b TS a e1 t1 → writes_b TS a e2 t2 →
    e1.1 = e2.1 → (t1 < t2)%nat →
    tc (gdep TS) e1 e2.
  Proof.
    intros. apply tc_once. left. by eapply ser_same_author.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Reads, and the events behind them *)

  (** A step that reads [(a, tr)] and fulfils [t] — necessarily an
      [LRmw] — has [tr < t] and no FOREIGN write to [a] in [(tr, t - 1]].
      The bundle-level packaging of [astep_ok_read_lt] and
      [astep_ok_read_excl]. *)
  Lemma gev_read_fulfil TS e a tr t :
    ptraces_wf pstep TS → gev_reads TS e a tr → gev_ts TS e = Some t →
    (tr < t)%nat ∧
    ¬ writes_in_by (pt_log TS) (λ tid, tid ≠ Some e.1) a tr (t - 1)%nat.
  Proof.
    intros Hwf (l & Hl & Hin) Hts.
    rewrite /gev_lb in Hl.
    destruct (gev_ev TS e) as [ev|] eqn:Hev; simpl in Hl; [|done].
    simplify_eq.
    rewrite /gev_ts Hev /= in Hts.
    destruct (gev_step pstep TS e ev Hwf Hev)
      as (T & ag & agn & st' & f & _ & _ & _ & _ & Hok & _).
    rewrite Hts in Hok. split.
    - by eapply astep_ok_read_lt.
    - by eapply astep_ok_read_excl.
  Qed.

  (** The SOURCE of a read: [writes_fulfilled] turns the message a read
      names into the event that fulfilled it, which is therefore a write
      of the byte read — and the rf edge is immediate. *)
  Lemma gev_reads_source TS e a tr :
    ptraces_wf pstep TS → writes_fulfilled TS →
    gev_reads TS e a tr → (0 < tr)%nat →
    ∃ er, writes_b TS a er tr ∧ grf TS er e.
  Proof.
    intros Hwf Hwfu Hr Hpos.
    destruct tr as [|p]; [lia|].
    destruct (gev_reads_msg pstep TS e a p Hwf Hr) as (m & Hm & Hb).
    have Hp : (S p - 1)%nat = p by lia.
    have Hm' : pt_log TS !! (S p - 1)%nat = Some m by rewrite Hp.
    destruct (Hwfu (S p) m ltac:(lia) Hm') as (er & Hts).
    exists er. split.
    - split; [exact Hts|]. by exists m.
    - by exists (S p), a.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** CHAINING: from co-consecutive pairs to the whole order

      A fuel induction on [t2 - t1].  The case split is on
      [writes_inb] — this is where the log-level spelling of [co_consec]
      pays: it is decidable, and its witness is a MESSAGE, which
      [writes_fulfilled] turns back into an event. *)

  Lemma writes_b_chain TS a :
    writes_fulfilled TS →
    (∀ e1 e2 t1 t2, writes_b TS a e1 t1 → writes_b TS a e2 t2 →
       (t1 < t2)%nat → co_consec TS a t1 t2 → tc (gdep TS) e1 e2) →
    co_tc TS a.
  Proof.
    intros Hwfu Hcons.
    have Hgen : ∀ n e1 e2 t1 t2, (t2 - t1 ≤ n)%nat →
      writes_b TS a e1 t1 → writes_b TS a e2 t2 → (t1 < t2)%nat →
      tc (gdep TS) e1 e2.
    { induction n as [|n IH]; intros e1 e2 t1 t2 Hn H1 H2 Hlt; [lia|].
      destruct (writes_inb (pt_log TS) a t1 (t2 - 1)%nat) eqn:Hb.
      - (* a message writes [a] strictly between: split the interval *)
        destruct (writes_in_compute _ _ _ _ Hb)
          as (t' & Hlo & Hhi & m & Hm & Hbyte).
        destruct (Hwfu t' m ltac:(lia) Hm) as (e' & Hts').
        have H' : writes_b TS a e' t' by split; [exact Hts'|by exists m].
        eapply tc_transitive.
        + eapply (IH e1 e' t1 t'); [lia|exact H1|exact H'|lia].
        + eapply (IH e' e2 t' t2); [lia|exact H'|exact H2|lia].
      - eapply Hcons; [exact H1|exact H2|exact Hlt|].
        by apply not_writes_in_compute. }
    intros e1 e2 t1 t2 H1 H2 Hlt.
    by eapply (Hgen (t2 - t1)%nat).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE [excl] ARM on a co-consecutive pair

      The rmw's read timestamp is pinned to [t1] EXACTLY, so the edge is a
      single rf edge — no recursion.  Below [t1] is refuted by [excl_ok]
      ([t1] is a FOREIGN write inside the exclusivity window
      [(tr, t2 - 1]]); above [t1] is refuted by co-consecutiveness (the
      read's own message would be a write of [a] strictly between). *)

  Lemma ser_excl_consec TS a e1 e2 t1 t2 :
    ptraces_wf pstep TS → excl_byte TS a →
    writes_b TS a e1 t1 → writes_b TS a e2 t2 →
    e1.1 ≠ e2.1 → (t1 < t2)%nat → co_consec TS a t1 t2 →
    grf TS e1 e2.
  Proof.
    intros Hwf Hex H1 H2 Hne Hlt Hcc.
    destruct (Hex e2 t2 H2) as [Hall|(tr & Hr)].
    { by destruct (Hne (Hall e1 t1 H1 Hlt)). }
    destruct (gev_read_fulfil TS e2 a tr t2 Hwf Hr (proj1 H2)) as [Hrlt Hnw].
    destruct (Nat.lt_trichotomy tr t1) as [Hc|[Hc|Hc]].
    - (* [t1] itself sits in the exclusivity window, and it is FOREIGN *)
      exfalso. apply Hnw.
      destruct (writes_b_author TS a e1 t1 Hwf H1) as (m & Hm & Hbyte & Htid).
      exists t1. split_and!; [lia|lia|].
      exists m. split_and!; [exact Hm|exact Hbyte|]. rewrite Htid.
      by intros [= ?].
    - (* the read is EXACTLY [e1]'s write: the rf edge *)
      subst tr. exists t1, a. split; [apply H1|exact Hr].
    - (* the read's own message would be a write of [a] strictly between *)
      exfalso. apply Hcc.
      have Hpos : (0 < tr)%nat.
      { have := writes_b_pos TS a e1 t1 Hwf H1. lia. }
      destruct tr as [|p]; [lia|].
      destruct (gev_reads_msg pstep TS e2 a p Hwf Hr) as (m & Hm & Hbyte).
      have Hp : (S p - 1)%nat = p by lia.
      exists (S p). split_and!; [lia|lia|]. exists m. by rewrite Hp.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** LAYER 1: bytes that are single-writer or exclusivity-chained

      Self-contained: no [handoff], hence no recursion into another byte.
      This is the layer the SYNC bytes must live in
      (see the stratification note in the header). *)

  Theorem byte_connect_sw_excl TS a :
    ptraces_wf pstep TS → writes_fulfilled TS →
    (sw_byte TS a ∨ excl_byte TS a) →
    co_tc TS a.
  Proof.
    intros Hwf Hwfu Harm. apply (writes_b_chain TS a Hwfu).
    intros e1 e2 t1 t2 H1 H2 Hlt Hcc.
    destruct (decide (e1.1 = e2.1)) as [Hag|Hne].
    - by eapply ser_same_author_tc.
    - destruct Harm as [Hsw|Hex].
      + by destruct (Hne (Hsw e1 e2 t1 t2 H1 H2)).
      + apply tc_once. right. by eapply ser_excl_consec.
  Qed.

  (** The sync layer, closed. *)
  Corollary sync_connect TS (sync : Z → Prop) :
    ptraces_wf pstep TS → writes_fulfilled TS →
    (∀ b, sync b → sw_byte TS b ∨ excl_byte TS b) →
    ∀ b, sync b → co_tc TS b.
  Proof.
    intros Hwf Hwfu Hsync b Hb. by eapply byte_connect_sw_excl, Hsync.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** LAYER 2: the [handoff] arm *)

  (** A po-or-equal hop, as an [rtc]: the two endpoints of the handoff's
      po bounds may coincide ([er = e1], [rr = e2]). *)
  Lemma gpo_le_rtc TS e e' :
    e.1 = e'.1 → (e.2 ≤ e'.2)%nat → gev_wf TS e → gev_wf TS e' →
    rtc (gdep TS) e e'.
  Proof.
    intros Hag Hle Hw Hw'.
    destruct (decide (e.2 = e'.2)) as [Heq|Hne].
    - have He : e = e'.
      { destruct e as [i k], e' as [i' k']. simpl in Hag, Heq. by subst. }
      subst e'. apply rtc_refl.
    - apply rtc_once. left. split_and!; [done|lia|done|done].
  Qed.

  (** THE PATH: [e1 →po? er →tc(sync b) e_star →rf rr →po? e2].  The
      middle hop degenerates to an equality when [tr = t_star] (rf
      functionality identifies [er] with the read's source); otherwise it
      is layer 1 applied to the SYNC byte [b]. *)
  Lemma ser_handoff_consec TS (sync : Z → Prop) a e1 e2 t1 t2 :
    ptraces_wf pstep TS → writes_fulfilled TS →
    (∀ b, sync b → sw_byte TS b ∨ excl_byte TS b) →
    handoff TS sync a →
    writes_b TS a e1 t1 → writes_b TS a e2 t2 →
    e1.1 ≠ e2.1 → (t1 < t2)%nat → co_consec TS a t1 t2 →
    tc (gdep TS) e1 e2.
  Proof.
    intros Hwf Hwfu Hsync Hho H1 H2 Hne Hlt Hcc.
    destruct (Hho e1 e2 t1 t2 H1 H2 Hne Hlt Hcc)
      as (b & er & tr & rr & t_star &
          Hb & Her & Her1 & Hpo1 & Hrr & Hrr1 & Hpo2 & Hts).
    (* the two po hops *)
    have Hstep1 : rtc (gdep TS) e1 er.
    { eapply gpo_le_rtc; [by rewrite Her1|exact Hpo1| |].
      - by eapply writes_b_wf.
      - by eapply writes_b_wf. }
    have Hstep4 : rtc (gdep TS) rr e2.
    { eapply gpo_le_rtc; [exact Hrr1|exact Hpo2| |].
      - by eapply gev_reads_wf.
      - by eapply writes_b_wf. }
    (* the source of [rr]'s read of the sync byte *)
    have Hpos : (0 < tr)%nat by eapply writes_b_pos.
    destruct (gev_reads_source TS rr b t_star Hwf Hwfu Hrr ltac:(lia))
      as (es & Hes & Hrf).
    (* the sync-byte hop *)
    have Hstep2 : rtc (gdep TS) er es.
    { destruct (decide (tr = t_star)) as [->|Hnee].
      - have -> : er = es by eapply writes_b_unique.
        apply rtc_refl.
      - apply tc_rtc.
        eapply (byte_connect_sw_excl TS b Hwf Hwfu (Hsync b Hb));
          [exact Her|exact Hes|lia]. }
    (* assemble *)
    eapply tc_rtc_l; [eapply rtc_transitive; [exact Hstep1|exact Hstep2]|].
    eapply tc_rtc_r; [apply tc_once; by right|exact Hstep4].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 3: THE CONNECTIVITY THEOREM *)

  Theorem co_serialized TS (sync : Z → Prop) :
    ptraces_wf pstep TS → writes_fulfilled TS →
    (∀ b, sync b → sw_byte TS b ∨ excl_byte TS b) →
    (∀ a, byte_ok TS sync a) →
    ∀ a e1 e2 t1 t2,
      writes_b TS a e1 t1 → writes_b TS a e2 t2 → (t1 < t2)%nat →
      tc (gdep TS) e1 e2.
  Proof.
    intros Hwf Hwfu Hsync Hbytes a.
    destruct (Hbytes a) as [Hsw|[Hex|Hho]].
    - by apply byte_connect_sw_excl; [done|done|left].
    - by apply byte_connect_sw_excl; [done|done|right].
    - apply (writes_b_chain TS a Hwfu).
      intros e1 e2 t1 t2 H1 H2 Hlt Hcc.
      destruct (decide (e1.1 = e2.1)) as [Hag|Hne].
      + by eapply ser_same_author_tc.
      + by eapply ser_handoff_consec.
  Qed.

  (** The same, packaged against [ptraces_bytes_ok]. *)
  Corollary co_serialized_pkg TS (sync : Z → Prop) :
    ptraces_wf pstep TS → writes_fulfilled TS → ptraces_bytes_ok TS sync →
    ∀ a, co_tc TS a.
  Proof.
    intros Hwf Hwfu [Hsync Hbytes] a e1 e2 t1 t2 H1 H2 Hlt.
    by eapply co_serialized.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 4: THE BEHAVIOR-LEVEL WRAPPER

      [writes_fulfilled] is DISCHARGED here, exactly as
      [WeakRobustGraph.wp_behavior_graph] discharges rf totality: every
      logged message is authored ([log_authored], an invariant of the
      promise phase) and every authored message is fulfilled exactly once
      in its author's trace ([wp_behavior_fulfil_once]). *)

  Lemma ptraces_of_writes_fulfilled TS mid c :
    ptraces_of pstep TS mid c →
    log_authored (pc_log mid) →
    (∀ p m i, pc_log mid !! p = Some m → wm_tid m = Some i →
       ∃ T, pt_trs TS !! i = Some T ∧
         (∃ k ev, at_evs T !! k = Some ev ∧ ae_ts ev = Some (S p)) ∧
         (∀ k1 k2 ev1 ev2,
            at_evs T !! k1 = Some ev1 → ae_ts ev1 = Some (S p) →
            at_evs T !! k2 = Some ev2 → ae_ts ev2 = Some (S p) →
            k1 = k2)) →
    writes_fulfilled TS.
  Proof.
    intros HTS Hla Hacct t m Hpos Hm.
    destruct t as [|p]; [lia|].
    have Hp : (S p - 1)%nat = p by lia. rewrite Hp in Hm.
    have Hlog : pt_log TS = pc_log mid by destruct HTS as (_ & ? & _).
    rewrite Hlog in Hm.
    destruct (Hla p m Hm) as [i Hi].
    destruct (Hacct p m i Hm Hi) as (T & HT & (k & ev & Hev & Hts) & _).
    exists (i, k). rewrite /gev_ts /gev_ev /= HT /= Hev /=. exact Hts.
  Qed.

  Theorem wp_behavior_co_serialized img d0 ps c :
    pdev_ok pstep pdev →
    lat_free_prog pstep → wp_behavior pstep img d0 ps c →
    ∃ mid TS,
      rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid ∧
      ptraces_of pstep TS mid c ∧
      no_promises c ∧
      ptraces_wf pstep TS ∧
      writes_fulfilled TS ∧
      (∀ sync, ptraces_bytes_ok TS sync → ∀ a, co_tc TS a).
  Proof.
    intros Hpok Hlfp Hb.
    destruct (wp_behavior_fulfil_once pstep pdev img d0 ps c Hpok Hlfp Hb)
      as (mid & TS & Hprom & HTS & Hnp & Hacct).
    have Hwf : ptraces_wf pstep TS by eapply ptraces_of_wf.
    have Hla : log_authored (pc_log mid).
    { eapply log_authored_promise_run; [apply log_authored_init|exact Hprom]. }
    have Hwfu : writes_fulfilled TS
      by eapply ptraces_of_writes_fulfilled.
    exists mid, TS. split_and!; [done|done|done|done|done|].
    intros sync Hok. by eapply co_serialized_pkg.
  Qed.

End ser.

(* ------------------------------------------------------------------ *)
(** ** What W2b's simulation inherits from this file

    - [writes_b] / [co_consec] / [co_tc]: the per-byte coherence-order
      vocabulary, stated on the trace bundle alone.

    - [ser_same_author] (and [ser_same_author_tc]): PREMISE-FREE.  Two
      writes of a byte by one agent are in program order iff in timestamp
      order.  This is the half of write-serialization that needs no
      classification at all, and it is reusable wherever a per-agent
      coherence argument is wanted.

    - [sw_byte] / [excl_byte] / [handoff] / [byte_ok] /
      [ptraces_bytes_ok]: the EXACT per-byte obligations the Iris layer
      must discharge — one disjunct per data-structure discipline
      (single-writer fields, lock words and AMO-guarded counters,
      release/acquire-published payloads).  Note the shape: each is a
      property of the bundle alone, with no path or cycle quantifier, and
      [handoff]'s antecedent is the DECIDABLE log-level co-consecutiveness
      so a discharge only ever has to look at one gap in the log.

    - The STRATIFICATION [sync_connect] / [byte_connect_sw_excl] then
      [co_serialized]: sync bytes must be [sw]-or-[excl]; general bytes
      may additionally use [handoff], which never recurses into another
      [handoff].  This is what makes the induction well-founded, and it is
      a constraint on the CALLER's choice of [sync], not on the proof.

    - [co_serialized] / [wp_behavior_co_serialized]: the theorem, and its
      behavior-level form with [ptraces_wf] and [writes_fulfilled]
      discharged.

    NOT here, deliberately: acyclicity (that is [WeakRobustAcyc.v], the
    first pillar — the two are independent), the topological sort itself,
    and any use of the classification [cls] or the publication [pub]. *)
