(** * WeakRobustAcyc2.v — ACYCLICITY OF THE EXTENDED GRAPH D⁺ = gdep ∪ gE
      (M6 W2b, design item (iii): the milestone-floor measure)

    [WeakRobustAcyc.v] refutes every [gdep]-cycle with the MESSAGE
    TIMESTAMP as the measure: walk the cycle, and every cross-agent rf
    hop's timestamp strictly increases (segment lemma S1).
    [WeakRobustOrd.v] then EXTENDS the graph with the floor-protection
    edges [gE] — an E edge runs from the fulfil of a LEAF [t*] of read
    [r]'s byte-[a] floor [F = rd_floor TS r a] to the fulfil of a
    byte-[a] write [t̂ > F] that [r] stale-passes.  This file re-runs the
    walk on [gdep2 = gdep ∪ gE].

    WHY THE RAW TIMESTAMP NO LONGER WORKS, and what replaces it.  A
    [gE] edge connects two FULFILS, possibly of the SAME agent, and
    same-author fulfils on DIFFERENT bytes are NOT trace-order-ordered
    (promises let an agent fulfil ts = 100 before ts = 5).  So a
    same-agent [gE] edge need NOT move forward in the trace, and the
    "same-agent fragment is index-increasing" half of
    [WeakRobustGraph.tc_gdep_split] would break if [gE] were lumped in
    with the same-agent edges.  The fix, exactly as the worklist's W2b
    (iii) pins it:

      MILESTONE EDGES are {cross-agent rf} ∪ {ALL gE edges}
      ([gmile] below); everything else is a SAME-AGENT [gdep] edge and
      is index-increasing ([gdep_same_agent_lt]).

      THE MEASURE µ is the MILESTONE FLOOR, not the hop timestamp:
      a cross-rf milestone reading [ts] carries µ := [ts]; a [gE]
      milestone out of read [r] at byte [a] carries µ := [F(r,a)], the
      read's WHOLE floor (≥ every leaf, so entering the hop from any
      leaf still increases µ).  [mile_mu TS µ v u] packages
      "[v → u] is a milestone edge of measure µ".

    THE WALK.  [on_cycle2 TS µ] says some milestone edge [v → u] of
    measure µ sits on a cycle ([rtc gdep2 u v]).  The advance step
    ([on_cycle2_advance]) follows the return path from [u] until the
    FIRST milestone [x → y] ([rtc_gdep2_first_mile]); everything before
    it is same-agent [gdep], so [x] is a fulfil of [u]'s own agent at a
    trace position ≥ [u]'s.  The one arithmetic fact needed is then

      [mile_mu_gain]: µ < ts(x) for EVERY fulfil [x] of [u]'s agent at
      or after [u],

    which has one proof per entry kind:
      - cross-rf entry: [WeakRobustAcyc.atrace_S1_le] (discipline via
        [rf_edges_ok], non-forwarding via [ptraces_fwd_own] and the
        foreign author, the [k = k'] rmw case via
        [astep_ok_read_fulfil_lt]);
      - [gE] entry: the NEW premise [ee_ok] for [k < k'], and for
        [k = k'] (i.e. [x = u], the E-target itself sourcing the next
        milestone) the edge's OWN bound [F < t̂].
    The exit then re-establishes the invariant: a cross-rf exit takes
    µ' := ts(x) directly; a [gE] exit takes µ' := F(r', a') ≥ ts(x)
    because ts(x) is a LEAF of that floor ([lval_ge] at σ = [id]).

    BOUNDEDNESS is cheaper than the worklist feared: no
    leaf-occurrence plumbing and no [ws_bounded]-along-traces lemma is
    needed, because a [gE] milestone's own conjunct [F < t̂] bounds µ by
    the REAL fulfilled timestamp [t̂], and fulfilled timestamps are log
    positions ([gev_ts_msg]).  So [ptraces_ws_init] / [rd_floor_ws] are
    NOT premises of the theorem (the behavior wrapper still exports
    [ptraces_ws_init], which W2b's simulation wants).

    PACKAGING DELTAS (deliberate, nothing weakened):
    - [gE_at] hides the byte [a] under its existential, but µ must NAME
      the byte ([rd_floor TS r a]).  [gE_ra TS r a e1 e2] is the same
      term with [a] hoisted into the parameters; [gE_ra_gE_at] /
      [gE_at_gE_ra] are the (trivial) inversions.  [ee_ok] and
      [mile_mu] are stated over [gE_ra].
    - [on_cycle2] is ONE existential over a milestone edge plus the
      return path, with the two arms living inside [mile_mu], rather
      than two top-level arms.  Same content, one advance proof.
    - the first-milestone decomposition [rtc_gdep2_first_mile] returns a
      DISJUNCTION ("the whole path stayed same-agent and forward" ∨ "a
      first milestone"), because unlike [WeakRobustAcyc]'s
      [rtc_gdep_first_cross] the endpoints of a [gE] milestone may share
      an agent, so [u.1 ≠ v.1] is no longer available to force the
      milestone's existence.  The extra case is discharged by
      [mile_mu_gain] itself (it makes the milestone's own source
      timestamp exceed µ, which it cannot).

    DEPENDENCY-FREE like its parents: stdpp only, no Iris, no Sail.
    [WeakAxiomatic] is imported FIRST so that [WeakPromise]'s [wlabel]
    constructors shadow its [lbl] ones. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakAxiomatic.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakRobustTrace
                            WeakRobustGraph WeakRobust WeakRobustProv
                            WeakRobustAcyc WeakRobustLin WeakRobustOrd.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** The E edge with its BYTE named

    [WeakRobustOrd.gE_at] existentially hides the label, the byte, the
    read timestamp, the leaf and the stale-passed write.  The measure µ
    of design item (iii) is [rd_floor TS r a] — it needs [a].  [gE_ra]
    is the very same conjunction with [a] hoisted out. *)

Section edges.
  Context {P D : Type}.
  Implicit Types TS : ptraces P D.

  Definition gE_ra TS (r : gev) (a : Z) (e1 e2 : gev) : Prop :=
    ∃ l ts tstar that,
      gev_lb TS r = Some l ∧ (a, ts) ∈ lb_reads l ∧
      tstar ∈ rd_leaves TS r a ∧ (0 < tstar)%nat ∧
      gev_ts TS e1 = Some tstar ∧
      gev_ts TS e2 = Some that ∧
      msg_writes TS that a ∧
      (rd_floor TS r a < that)%nat.

  Lemma gE_ra_gE_at TS r a e1 e2 : gE_ra TS r a e1 e2 → gE_at TS r e1 e2.
  Proof.
    intros (l & ts & tstar & that & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    exists l, a, ts, tstar, that. by split_and!.
  Qed.

  Lemma gE_at_gE_ra TS r e1 e2 : gE_at TS r e1 e2 → ∃ a, gE_ra TS r a e1 e2.
  Proof.
    intros (l & a & ts & tstar & that & H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8).
    exists a, l, ts, tstar, that. by split_and!.
  Qed.

  Lemma gE_ra_gdep2 TS r a e1 e2 : gE_ra TS r a e1 e2 → gdep2 TS e1 e2.
  Proof. intros H. apply gE_gdep2. exists r. by eapply gE_ra_gE_at. Qed.

End edges.

(* ------------------------------------------------------------------ *)
(** ** THE NEW PREMISE [ee_ok] — the E-edge analogue of [rf_edges_ok]

    For every E edge (witnessing read [r], byte [a], floor
    [F = rd_floor TS r a], source [e1], target [et]) and EVERY fulfil
    [ey] of [et]'s own agent strictly po-AFTER [et]: [F < ts(ey)].

    This is the worklist's per-triple obligation, discharged on the
    Iris/static side by the three arms recorded there:
      (a) FENCE-COVER — a [pw ∧ sw] fence sits po-between [et] and [ey],
          shipping [t̂ ∈ w_vwOld] into [w_vwNew], so EXT at [ey] gives
          [ts(ey) > t̂ > F] (the release/publish sites);
      (b) WAW-COVER — the writer's [w_vwNew] at [et]'s pre-state was
          already ≥ F (ownership transfer), and EXT at [ey] finishes;
      (c) EMPTY FLOOR — [F = 0] with no real leaves generates NO E edges
          at all ([0 < tstar] is a conjunct of [gE_at]), so the racy
          started-spin shape needs no premise.

    Shape note: like [rf_edges_ok] it carries NO cycle quantifier — it
    is a property of the bundle alone, per (edge, later fulfil). *)
Definition ee_ok {P D : Type} (TS : ptraces P D) : Prop :=
  ∀ r a e1 et ey y,
    gE_ra TS r a e1 et →
    et.1 = ey.1 → (et.2 < ey.2)%nat →
    gev_ts TS ey = Some y →
    (rd_floor TS r a < y)%nat.

(* ------------------------------------------------------------------ *)
Section acyc2.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pdev : P → wlabel → P → bool).

  Implicit Types TS : ptraces P D.
  Implicit Types e : gev.

  (* ---------------------------------------------------------------- *)
  (** ** MILESTONE EDGES and the measure µ *)

  (** A MILESTONE: a cross-agent [gdep] edge (necessarily rf, since
      [gpo] is same-agent by definition) or ANY [gE] edge. *)
  Definition gmile TS (e1 e2 : gev) : Prop :=
    (gdep TS e1 e2 ∧ e1.1 ≠ e2.1) ∨ gE TS e1 e2.

  (** The milestone edge [v → u] TOGETHER WITH ITS MEASURE µ. *)
  Definition mile_mu TS (mu : nat) (v u : gev) : Prop :=
    (∃ a, gev_ts TS v = Some mu ∧ gev_reads TS u a mu ∧ v.1 ≠ u.1) ∨
    (∃ r a, gE_ra TS r a v u ∧ mu = rd_floor TS r a).

  Lemma mile_mu_gdep2 TS mu v u : mile_mu TS mu v u → gdep2 TS v u.
  Proof.
    intros [(a & Hts & Hrd & _)|(r & a & Hra & _)].
    - apply grf_gdep2. by exists mu, a.
    - by eapply gE_ra_gdep2.
  Qed.

  (** A milestone edge WITH its measure IS a milestone edge. *)
  Lemma mile_mu_gmile TS mu v u : mile_mu TS mu v u → gmile TS v u.
  Proof.
    intros [(a & Hts & Hrd & Hne)|(r & a & Hra & _)].
    - left. split; [right; by exists mu, a|exact Hne].
    - right. exists r. by eapply gE_ra_gE_at.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** A0: THE PER-EDGE PREMISE, RELATIVIZED TO THE WALK'S FULFILS

      [WeakRobustAcyc.rf_edges_ok] demands [edge_ok] of a cross rf edge
      against EVERY later fulfil of the reader, with coverage evaluated
      AT THE READ.  Both halves are more than the walk consumes, and the
      surplus is FALSE for xv6
      ([design/weak-memory-premise-discharge.md] §2b: [holding()]'s plain
      read of the lock word, followed by the acquire RMW with no fence
      and nothing acquired yet).  The walk only ever applies the premise
      at the fulfil that SOURCES THE EXIT MILESTONE
      ([on_cycle2_advance]), and it only ever needs coverage at that
      fulfil's own EXT view ([edge_ok_f]).  So:

      - [k'] must be a MILESTONE SOURCE ([∃ y, gmile TS (e2.1, k') y]:
        the fulfil's message is read cross-agent, or the fulfil is a
        [gE] source);
      - the conclusion is [edge_ok_f] (coverage at the FULFIL, which for
        an acquiring RMW is after its own read half).

      [k' = e2.2] — the rmw case, where the entry read and the exit
      fulfil are the SAME event — is EXCLUDED from the quantification and
      needs no premise at all: [WeakRobustAcyc.astep_ok_read_fulfil_lt]
      gets [ts < ts'] from the rmw's own COH conjunct, checked on the
      post-[load_post_run] state ([atrace_S1_le_f]'s [k = k'] arm). *)
  Definition rf_edges_ok_ms TS : Prop :=
    ∀ e1 e2 T ts a k' ev',
      gev_ts TS e1 = Some ts → gev_reads TS e2 a ts → e1.1 ≠ e2.1 →
      pt_trs TS !! e2.1 = Some T →
      (e2.2 < k')%nat →
      at_evs T !! k' = Some ev' → is_Some (ae_ts ev') →
      (∃ y, gmile TS (e2.1, k') y) →
      edge_ok_f T e2.2 k' ts.

  (** THE OLD PREMISE IMPLIES THE NEW ONE (so the relativization is a
      pure weakening of every theorem below). *)
  Lemma rf_edges_ok_rf_edges_ok_ms TS :
    ptraces_wf pstep TS → rf_edges_ok TS → rf_edges_ok_ms TS.
  Proof.
    intros Hwf H e1 e2 T ts a k' ev' Hts Hrd Hne HT Hlt Hev Hsome _.
    eapply (edge_ok_edge_ok_f pstep (pt_img TS) (pt_log TS) e2.1 T e2.2 k' ts ev');
      [by eapply Hwf|lia|exact Hev|exact Hsome|].
    by eapply H.
  Qed.

  Lemma gmile_mile_mu TS v u : gmile TS v u → ∃ mu, mile_mu TS mu v u.
  Proof.
    intros [[Hd Hne]|HE].
    - have Hrf : grf TS v u.
      { destruct Hd as [(Hag & _)|Hrf]; [by destruct (Hne Hag)|exact Hrf]. }
      destruct Hrf as (ts & a & Hts & Hrd).
      exists ts. left. exists a. by split_and!.
    - destruct HE as (r & Hat). destruct (gE_at_gE_ra TS r v u Hat) as (a & Hra).
      exists (rd_floor TS r a). right. by exists r, a.
  Qed.

  (** The milestone's SOURCE is always a fulfil, at or below µ: for a
      cross-rf milestone its timestamp IS µ; for a [gE] milestone its
      timestamp is a floor LEAF, hence ≤ the floor ([lval_ge] at
      σ = [id]). *)
  Lemma mile_mu_src_ts TS mu v u :
    mile_mu TS mu v u → ∃ tv, gev_ts TS v = Some tv ∧ (tv ≤ mu)%nat.
  Proof.
    intros [(a & Hts & _)|(r & a & Hra & ->)].
    - exists mu. split; [done|lia].
    - destruct Hra as (l & ts & tstar & that & _ & _ & Hleaf & _ & H5 & _).
      exists tstar. split; [done|]. by apply (lval_ge id _ _ Hleaf).
  Qed.

  (** µ IS BOUNDED BY THE LOG.  A cross-rf milestone's µ is a fulfilled
      timestamp; a [gE] milestone's µ is STRICTLY BELOW the fulfilled
      timestamp [t̂] of its target — the edge's own conjunct.  So no
      leaf-occurrence machinery is needed. *)
  Lemma mile_mu_bounded TS mu v u :
    ptraces_wf pstep TS → mile_mu TS mu v u → (mu ≤ length (pt_log TS))%nat.
  Proof.
    intros Hwf [(a & Hts & _)|(r & a & Hra & ->)].
    - destruct (gev_ts_msg pstep TS v mu Hwf Hts) as (base & data & kc & Hm).
      apply lookup_lt_Some in Hm.
      have Hpos : (0 < mu)%nat by eapply (gev_ts_pos pstep TS).
      lia.
    - destruct Hra as (l & ts & tstar & that & _ & _ & _ & _ & _ & H6 & _ & Hlt).
      destruct (gev_ts_msg pstep TS u that Hwf H6) as (base & data & kc & Hm).
      apply lookup_lt_Some in Hm.
      have Hpos : (0 < that)%nat by eapply (gev_ts_pos pstep TS).
      lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE FIRST-MILESTONE DECOMPOSITION

      Every [gdep2] edge is a milestone or a SAME-AGENT [gdep] edge, and
      the latter strictly increases the trace index. *)

  Lemma gdep2_mile_or_sa TS e1 e2 :
    gdep2 TS e1 e2 → gmile TS e1 e2 ∨ (gdep TS e1 e2 ∧ e1.1 = e2.1).
  Proof.
    intros [Hd|HE]; [|by left; right].
    destruct (decide (e1.1 = e2.1)) as [Hag|Hne]; [by right|by left; left].
  Qed.

  (** Follow an [rtc gdep2] path from [u] until it hits its FIRST
      milestone.  Either it never does — and then the whole path stayed
      in [u]'s agent, moving forward in the trace — or the path splits as
      [rtc gdep2 · milestone · rtc gdep2] with the milestone's SOURCE in
      [u]'s agent, at or after [u].

      (Contrast [WeakRobustAcyc.rtc_gdep_first_cross], which forces the
      cross edge to exist from [u.1 ≠ v.1]: a [gE] milestone may be
      same-agent, so that argument is unavailable and the "no milestone"
      case is returned to the caller.) *)
  Lemma rtc_gdep2_first_mile TS u v :
    ptraces_wf pstep TS → rtc (gdep2 TS) u v →
    (u.1 = v.1 ∧ (u.2 ≤ v.2)%nat) ∨
    ∃ x y, u.1 = x.1 ∧ (u.2 ≤ x.2)%nat ∧ rtc (gdep2 TS) u x ∧
           gmile TS x y ∧ rtc (gdep2 TS) y v.
  Proof.
    intros Hwf Hr. induction Hr as [z|u w v Huw Hwv IH].
    - left. split; [done|lia].
    - destruct (gdep2_mile_or_sa TS u w Huw) as [Hmile|[Hd Hag]].
      + right. exists u, w.
        split_and!; [done|lia|apply rtc_refl|exact Hmile|exact Hwv].
      + have Hlt : (u.2 < w.2)%nat
          by eapply (gdep_same_agent_lt pstep TS u w).
        destruct IH as [[Hag' Hle]|(x & y & Hx1 & Hx2 & Hrx & Hmile & Hry)].
        * left. split; [congruence|lia].
        * right. exists x, y.
          split_and!; [congruence|lia| |exact Hmile|exact Hry].
          eapply rtc_l; [exact Huw|exact Hrx].
  Qed.

  (** …and the [tc] form: a [gdep2] path either stayed same-agent and
      forward, or it contains a milestone.  ([WeakRobustGraph]'s
      [tc_gdep_split] with "cross-agent" replaced by "milestone".) *)
  Lemma tc_gdep2_split TS e1 e2 :
    ptraces_wf pstep TS → tc (gdep2 TS) e1 e2 →
    (e1.1 = e2.1 ∧ (e1.2 < e2.2)%nat) ∨
    (∃ x y, rtc (gdep2 TS) e1 x ∧ gmile TS x y ∧ rtc (gdep2 TS) y e2).
  Proof.
    intros Hwf. induction 1 as [x y Hxy|x y z Hxy Hyz IH].
    - destruct (gdep2_mile_or_sa TS x y Hxy) as [Hmile|[Hd Hag]].
      + right. exists x, y.
        split_and!; [apply rtc_refl|exact Hmile|apply rtc_refl].
      + left. split; [done|by eapply (gdep_same_agent_lt pstep TS)].
    - destruct (gdep2_mile_or_sa TS x y Hxy) as [Hmile|[Hd Hag]].
      + right. exists x, y.
        split_and!; [apply rtc_refl|exact Hmile|by apply tc_rtc].
      + have Hlt : (x.2 < y.2)%nat by eapply (gdep_same_agent_lt pstep TS).
        destruct IH as [[Hag' Hlt']|(p & q & Hrp & Hpq & Hrq)].
        * left. split; [by etrans|lia].
        * right. exists p, q. split_and!; [|exact Hpq|exact Hrq].
          eapply rtc_l; [exact Hxy|exact Hrp].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE GAIN LEMMA — the one arithmetic fact of the walk

      Entering agent [u.1] through a milestone of measure µ, EVERY
      fulfil [x] of that agent at or after [u] has [ts(x) > µ].

      Two proofs, one per entry kind.  The cross-rf entry is
      [WeakRobustAcyc]'s S1 verbatim (its [k ≤ k'] form folds in the rmw
      case where the entry read and the exit fulfil are the SAME event).
      The [gE] entry is [ee_ok] for [u.2 < x.2], and for [x = u] — the
      E-target itself sourcing the next milestone — it is the E edge's
      OWN conjunct [F < t̂], no premise at all. *)
  Lemma mile_mu_gain TS mu v u x tx :
    ptraces_wf pstep TS → ptraces_fwd_own TS → rf_edges_ok_ms TS → ee_ok TS →
    mile_mu TS mu v u → u.1 = x.1 → (u.2 ≤ x.2)%nat →
    (∃ y, gmile TS x y) →
    gev_ts TS x = Some tx →
    (mu < tx)%nat.
  Proof.
    intros Hwf Hfo Hrf Hee
           [(a & Hts1 & Hrd & Hne)|(r & a & Hra & ->)] Hag Hle Hms Htx.
    - (* CROSS-RF ENTRY: S1. *)
      have Hwfu : gev_wf TS u by eapply gev_reads_wf.
      apply gev_wf_bounds in Hwfu as (T & HT & _).
      have HTx : pt_trs TS !! x.1 = Some T by rewrite -Hag.
      destruct (gev_reads_ev TS u a mu T HT Hrd) as (ev & Hev & Hinr).
      destruct (gev_ts_ev TS x tx T HTx Htx) as (evx & Hevx & Htsx).
      (* the entry edge's source is FOREIGN, so the read is not
         forwarded *)
      destruct (gev_ts_msg pstep TS v mu Hwf Hts1) as (base & data & kc & Hm).
      have Hunf : read_unforwarded (pt_log TS) u.1 (ae_lb ev) mu.
      { right. exists (WMsg base data (Some v.1) kc), v.1.
        split_and!; [exact Hm|done|exact Hne]. }
      eapply (atrace_S1_le_f pstep (pt_img TS) (pt_log TS) u.1 T u.2 x.2
                ev evx a mu tx).
      + by eapply Hwf.
      + intros n ag Hn. by eapply (Hfo u.1 T n ag HT Hn).
      + exact Hev.
      + exact Hinr.
      + exact Hunf.
      + exact Hevx.
      + exact Htsx.
      + exact Hle.
      + intros Hklt. eapply (Hrf v u T mu a x.2 evx);
          [exact Hts1|exact Hrd|exact Hne|exact HT|exact Hklt|exact Hevx| |].
        * rewrite Htsx. by eexists.
        * destruct Hms as (y & Hy). exists y.
          by rewrite Hag -surjective_pairing.
    - (* gE ENTRY. *)
      destruct (decide (u.2 = x.2)) as [Heq|Hne].
      + (* [x = u]: the E-target itself.  The edge's own bound. *)
        have Hux : u = x.
        { destruct u as [i k], x as [i' k']. simpl in Hag, Heq. by subst. }
        rewrite -Hux in Htx.
        destruct Hra
          as (l & ts & tstar & that & _ & _ & _ & _ & _ & H6 & _ & Hlt).
        rewrite H6 in Htx. by simplify_eq.
      + (* a STRICTLY later fulfil of the same agent: [ee_ok]. *)
        eapply (Hee r a v u x tx); [exact Hra|exact Hag|lia|exact Htx].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE MEASURE ON A CYCLE *)

  (** A milestone edge SITS ON A CYCLE when its target can reach its
      source again.  µ is the edge's measure. *)
  Definition on_cycle2 TS (mu : nat) : Prop :=
    ∃ v u, mile_mu TS mu v u ∧ rtc (gdep2 TS) u v.

  (** THE ADVANCE STEP. *)
  Lemma on_cycle2_advance TS mu :
    ptraces_wf pstep TS → ptraces_fwd_own TS → rf_edges_ok_ms TS → ee_ok TS →
    on_cycle2 TS mu → ∃ mu', (mu < mu')%nat ∧ on_cycle2 TS mu'.
  Proof.
    intros Hwf Hfo Hrf Hee (v & u & Hm & Hpath).
    destruct (rtc_gdep2_first_mile TS u v Hwf Hpath)
      as [[Hag Hle]|(x & y & Hag & Hle & Hux & Hmile & Hyv)].
    - (* NO milestone on the return path: then the path stayed in [u]'s
         agent and reached [v] forward, so the gain lemma applies to
         [v] ITSELF — and the milestone's own source timestamp is ≤ µ. *)
      exfalso.
      destruct (mile_mu_src_ts TS mu v u Hm) as (tv & Htv & Hlev).
      have Hgt := mile_mu_gain TS mu v u v tv Hwf Hfo Hrf Hee Hm Hag Hle
                    (ex_intro _ u (mile_mu_gmile TS mu v u Hm)) Htv.
      lia.
    - (* THE EXIT MILESTONE [x → y]: its source [x] is a fulfil of [u]'s
         agent at or after [u]. *)
      have Hedge : gdep2 TS v u by eapply mile_mu_gdep2.
      have Hyx : rtc (gdep2 TS) y x.
      { eapply rtc_transitive; [exact Hyv|].
        eapply rtc_l; [exact Hedge|exact Hux]. }
      have Hgm : gmile TS x y := Hmile.
      destruct Hmile as [[Hd Hne]|HE].
      + (* CROSS-RF EXIT: µ' := ts(x). *)
        have Hrfxy : grf TS x y.
        { destruct Hd as [(Hag' & _)|Hrf']; [by destruct (Hne Hag')|exact Hrf']. }
        destruct Hrfxy as (ts2 & a2 & Hts2 & Hrd2).
        have Hlt := mile_mu_gain TS mu v u x ts2 Hwf Hfo Hrf Hee Hm Hag Hle
                      (ex_intro _ y Hgm) Hts2.
        exists ts2. split; [exact Hlt|].
        exists x, y. split; [|exact Hyx].
        left. exists a2. by split_and!.
      + (* gE EXIT: µ' := F(r', a') ≥ ts(x), since ts(x) is a LEAF of
           that floor. *)
        destruct HE as (r' & Hat).
        destruct (gE_at_gE_ra TS r' x y Hat) as (a' & Hra').
        have Hra'' := Hra'.
        destruct Hra''
          as (l' & ts' & tstar' & that' & _ & _ & Hleaf' & _ & H5' & _).
        have Hlt := mile_mu_gain TS mu v u x tstar'
                      Hwf Hfo Hrf Hee Hm Hag Hle (ex_intro _ y Hgm) H5'.
        have Hle' : (tstar' ≤ rd_floor TS r' a')%nat
          by apply (lval_ge id _ _ Hleaf').
        exists (rd_floor TS r' a'). split; [lia|].
        exists x, y. split; [|exact Hyx].
        right. by exists r', a'.
  Qed.

  Lemma on_cycle2_bounded TS mu :
    ptraces_wf pstep TS → on_cycle2 TS mu → (mu ≤ length (pt_log TS))%nat.
  Proof. intros Hwf (v & u & Hm & _). by eapply mile_mu_bounded. Qed.

  (** THE REFUTATION: the advance step cannot be iterated inside a
      bounded set of measures.  (Measure [length log - µ]; no
      cycle-sequence extraction needed — as in [on_cycle_rf_empty].) *)
  Lemma on_cycle2_empty TS :
    ptraces_wf pstep TS → ptraces_fwd_own TS → rf_edges_ok_ms TS → ee_ok TS →
    ∀ mu, ¬ on_cycle2 TS mu.
  Proof.
    intros Hwf Hfo Hrf Hee.
    have Hgen : ∀ n mu, (length (pt_log TS) - mu ≤ n)%nat →
                        ¬ on_cycle2 TS mu.
    { induction n as [|n IH]; intros mu Hn Hoc.
      - have Hb := on_cycle2_bounded TS mu Hwf Hoc.
        destruct (on_cycle2_advance TS mu Hwf Hfo Hrf Hee Hoc)
          as (mu' & Hlt & Hoc').
        have Hb' := on_cycle2_bounded TS mu' Hwf Hoc'. lia.
      - destruct (on_cycle2_advance TS mu Hwf Hfo Hrf Hee Hoc)
          as (mu' & Hlt & Hoc').
        eapply (IH mu'); [|exact Hoc'].
        have Hb' := on_cycle2_bounded TS mu' Hwf Hoc'. lia. }
    intros mu. by eapply (Hgen (length (pt_log TS) - mu)%nat).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE THEOREM *)

  Theorem gdep2_acyclic_edges_ok TS :
    ptraces_wf pstep TS → ptraces_fwd_own TS → rf_edges_ok_ms TS → ee_ok TS →
    gdep2_acyclic TS.
  Proof.
    intros Hwf Hfo Hrf Hee e Hc.
    destruct (tc_gdep2_split TS e e Hwf Hc)
      as [[_ Hlt]|(x & y & Hrx & Hmile & Hry)]; [lia|].
    destruct (gmile_mile_mu TS x y Hmile) as (mu & Hm).
    eapply (on_cycle2_empty TS Hwf Hfo Hrf Hee mu).
    exists x, y. split; [exact Hm|].
    eapply rtc_transitive; [exact Hry|exact Hrx].
  Qed.

  (** The [gdep]-acyclicity of [WeakRobustAcyc] is a corollary (D⁺ is
      the bigger graph). *)
  Corollary gdep_acyclic_of_gdep2 TS :
    ptraces_wf pstep TS → ptraces_fwd_own TS → rf_edges_ok_ms TS → ee_ok TS →
    gdep_acyclic TS.
  Proof.
    intros Hwf Hfo Hrf Hee. apply gdep2_acyclic_gdep.
    by eapply gdep2_acyclic_edges_ok.
  Qed.

  (** …at the behavior level, with [fwd_own] and [ws_init] DISCHARGED.
      Only the two per-edge obligations remain premises: [rf_edges_ok]
      (the reader-side discipline of W2a) and [ee_ok] (the E-edge
      obligation of W2b (iii)).  [ptraces_ws_init] is exported because
      W2b's simulation wants it (it is NOT used by the acyclicity proof
      — see the header's boundedness note). *)
  Theorem wp_behavior_gdep2_acyclic img d0 ps c :
    pdev_ok pstep pdev →
    lat_free_prog pstep → wp_behavior pstep img d0 ps c →
    ∃ mid TS,
      rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid ∧
      ptraces_of pstep TS mid c ∧
      no_promises c ∧
      ptraces_wf pstep TS ∧
      ptraces_fwd_own TS ∧
      ptraces_ws_init TS ∧
      (rf_edges_ok_ms TS → ee_ok TS → gdep2_acyclic TS).
  Proof.
    intros Hpok Hlfp Hb.
    destruct (wp_behavior_traced pstep pdev img d0 ps c Hpok Hlfp Hb)
      as (mid & TS & Hprom & HTS & Hnp).
    have Hwf : ptraces_wf pstep TS by eapply ptraces_of_wf.
    have Hinit : cfg_ws_init mid.
    { eapply cfg_ws_init_promise_run; [apply (cfg_ws_init_init img d0 ps)|exact Hprom]. }
    have Hfo : ptraces_fwd_own TS by eapply ptraces_of_fwd_own.
    have Hwsi : ptraces_ws_init TS by eapply ptraces_of_ws_init.
    exists mid, TS. split_and!; [done|done|done|done|done|done|].
    intros Hrf Hee. by eapply gdep2_acyclic_edges_ok.
  Qed.

End acyc2.

(* ------------------------------------------------------------------ *)
(** ** What W2b inherits from this file

    - [ee_ok]: the E-edge obligation, the ONE new premise of the
      extended acyclicity theorem — per (E edge, later fulfil of the
      target's agent), with no cycle quantifier, so the Iris/static side
      discharges it site by site (fence-cover / waw-cover / empty-floor,
      per the worklist's W2b (iii)).  [gE_ra] is the byte-named form of
      [WeakRobustOrd.gE_at] it is stated over, with [gE_ra_gE_at] /
      [gE_at_gE_ra] the inversions.

    - [gdep2_acyclic_edges_ok]: [gdep2_acyclic TS] from
      [ptraces_wf] + [ptraces_fwd_own] + [rf_edges_ok] + [ee_ok] — the
      hypothesis [WeakRobustOrd]'s [gdep2_toposort_S] / [toposort_ind_S]
      take, and hence what W2b's simulation consumes.
      [wp_behavior_gdep2_acyclic] is the behavior-level wrapper, with
      [ptraces_fwd_own] and [ptraces_ws_init] derived.

    - [rf_edges_ok_ms] (A0): the per-edge premise relativized to the
      fulfils the walk actually consumes — the fulfil is a MILESTONE
      SOURCE ([∃ y, gmile TS (e2.1, k') y]) and the coverage is
      [WeakRobustAcyc.fcov], at that fulfil's own EXT view.  The [k' =
      e2.2] rmw case is excluded and needs no premise
      ([astep_ok_read_fulfil_lt]).  [rf_edges_ok_rf_edges_ok_ms] is the
      implication from the pre-A0 [rf_edges_ok].

    - [gmile] / [mile_mu] / [on_cycle2] / [mile_mu_gain] /
      [rtc_gdep2_first_mile] / [tc_gdep2_split]: the milestone
      vocabulary.  [tc_gdep2_split] is the structural half ("every D⁺
      cycle contains a cross-rf or a gE edge") and is reusable
      independently of the measure. *)
