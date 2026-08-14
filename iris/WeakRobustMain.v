(** * WeakRobustMain.v — THE ASSEMBLED LAYER-1 ROBUSTNESS THEOREM (M6 W2c)

    The pieces landed by W2a/W2b are: the dependency graph and its
    extension ([WeakRobustGraph], [WeakRobustOrd]), the acyclicity walk
    over [gdep2] from the per-edge discipline premises
    ([WeakRobustAcyc2]), the byte-classification premises and
    co-serialization ([WeakRobustSer]), and the π-permuted simulation
    ([WeakRobustSim]).  This file assembles them into the theorem the
    worklist's W2c block asks for:

      (1) the per-edge premise WEAKENED from [rf_edges_ok] to
          "[edge_ok] OR [bad]" ([edges_split]), where [bad] is the
          owned-unpublished cross read — the shape the Layer-2
          violation predicate φ refutes;
      (2) THE EXHIBIT: given a [bad] edge whose target has
          bad-target-free strict ancestry ([bad_min]), the ancestor cone
          [U] of that target is sortable, the subset simulation replays
          it, and ONE more [wp_pf_step] appends the bad read — reaching
          a promise-free configuration that VIOLATES — with a HART
          author and a HART observer, since [bad] bounds both agent
          indices by [nh] — contradicting [pf_violation_free_hart].
          Hence no bad edge exists at all,
          [rf_edges_ok] holds, [gdep2_acyclic] follows, and [sim_full]
          delivers the robustness conclusion;
      (3) the honest residue, carried as the premise [bad_wf]: whenever
          a bad edge exists, SOME bad edge has bad-target-free strict
          ancestry (a "bad SCC" — mutually-justified owned reads — has
          no minimal element and no exhibit; same epistemic category as
          D-M6-8's static residue);
      (4) W2c proper: the transport corollary over completable prefixes.

    DELTAS FROM THE DESIGN SKETCH (the landed files are ground truth):

    - THE RELATIVIZED WALK IS TINY, and it is NOT a copy of
      [WeakRobustAcyc2]'s whole section.  Reading that file's proof:
      [rf_edges_ok] is consumed at exactly ONE place ([mile_mu_gain]'s
      cross-rf arm), and both call sites ([on_cycle2_advance]) have the
      milestone's TARGET [u] on a cycle.  So only [mile_mu_gain],
      [on_cycle2_advance], [on_cycle2_empty] and the theorem are
      restated here ([mile_mu_gain_on], [on_cycle2_advance_on],
      [on_cycle2_on_empty], [gdep2_acyclic_on]), over an ABSTRACT
      predicate [W] on readers ([rf_edges_ok_on]) closed under mutual
      reachability; [mile_mu], [gmile], [tc_gdep2_split],
      [rtc_gdep2_first_mile], [mile_mu_bounded], [mile_mu_src_ts] are
      imported unchanged.  Instantiating [W] at "is a strict ancestor
      of the bad read" gives the U-restricted acyclicity the exhibit
      needs; instantiating it at "lies on a cycle" gives global
      acyclicity from the STRONG form of the residue (recorded as
      [gdep2_acyclic_bad_free] — NOT used by the main theorem, which
      takes the weak [bad_wf] and spends the exhibit; the strong form
      would make [pf_violation_free_hart] unnecessary, which is not the
      design).

    - NO [Decision (tc (gdep2 TS) e e2)] IS PROVED.  The design's
      alternative — the concrete predecessor closure — is taken: [anc]
      iterates "add every carrier element with an edge into the current
      set" [|carrier|] times, saturates (pigeonhole on a [NoDup]
      sublist), and [e ∈ anc ↔ e = root ∨ tc R e root].  It is
      developed generically ([Section closure]) over a decidable
      relation and a finite carrier.

    - [sim_prefix] IS NOT USED: it consumes GLOBAL [gdep2_acyclic],
      which the exhibit does not have (the whole point of the exhibit
      is that a bad edge may create cycles elsewhere).  Instead the
      generic [WeakRobustLin.topo_sort] is instantiated at the
      RESTRICTED relation [gdep2 ∩ U²] and [toposort_ind_S]'s prefix
      induction is re-run over [Qinv] ([sim_prefix]'s own proof, with
      the restricted order) — 40 lines, and [Qinv_step] does all the
      work.

    - [bad] CARRIES THE AUTHOR'S OWN FULFIL in its "no publishing
      ancestor" conjunct ([e1.2 ≤ ep.2], not [<]).  At the [WeakPromise]
      level the message class [wm_ak] is UNCONSTRAINED by the step rules
      (the promise rule picks any class), so "[WCplain] ⇒ the store did
      not raise [w_pub]" is not derivable — including the author's own
      fulfil in the quantifier makes the exhibit close with no extra
      premise, and it is faithful to the intent (a store that raises
      [w_pub] publishes its own message, and Layer 2's [wm_class_of]
      tags exactly those [WCrel]).

    - THE PREMISE PACKAGE is [main_premises]: [edges_split] (the split),
      [bad_wf] (the residue), [ee_ok] (W2b (iii)) and
      [∃ sync, ptraces_bytes_ok TS sync] (the byte classification, which
      [WeakRobustSer.co_serialized_pkg] turns into [co_tc]).
      [ptraces_wf], [ptraces_ws_init], [ptraces_fwd_own],
      [writes_fulfilled] and the shape facts are DERIVED from the
      behavior, exactly as [WeakRobustSim]'s wrapper derives them;
      [ts_oblivious] is worklist finding (v).

    - [pub_event] reads the raise condition off the machine: [w_pub] is
      raised by [store_post] iff the label's [rl] bit is set or the
      PRE-state's [w_relp] is (a [pw ∧ sw] fence armed it).  The
      pf-side fold and the behavior's own trace agree on [w_relp]
      because [w_relp] is σ-INDEPENDENT ([w_relp_aevs_post_indep]) —
      nothing in the [wstate] update reads a timestamp to compute it.

    DEPENDENCY-FREE like its parents: stdpp only, no Iris, no Sail.
    [WeakAxiomatic] is imported FIRST so that [WeakPromise]'s [wlabel]
    constructors shadow its [lbl] ones. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakAxiomatic.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakPromiseBridge
                            WeakRobustTrace WeakRobustGraph WeakRobust
                            WeakRobustProv WeakRobustAcyc WeakRobustLin
                            WeakRobustOrd WeakRobustSer WeakRobustAcyc2
                            WeakRobustSim.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** LAYER 0: how a fold of trace events moves [w_pub] and [w_relp]

    Two inert [wstate] fields carry the publication story (D-M6-6):
    [w_relp] is armed by a [pw ∧ sw] fence and cleared by the next
    store; [w_pub] is raised to the store's own timestamp at a store
    taken with [w_relp] set or at an [rl] store.  The exhibit needs
    exactly two facts about the π-transported fold [aevs_post]:

    - [w_relp] does not depend on σ (nothing computes it from a
      timestamp), so the pf-side fold and the behavior's own trace
      agree on it;
    - [w_pub] stays STRICTLY BELOW a bound [N] as long as every
      RAISING event's transported timestamp does. *)

(** The [rl] bit of a store/rmw label; [false] for everything else. *)
Definition lb_rl (l : wlabel) : bool :=
  match l with
  | LStore rl _ _ => rl
  | LRmw _ rl _ _ _ => rl
  | _ => false
  end.

(* ---- the per-byte folds ---- *)

Lemma w_relp_foldl_load (aq : bool) (v : nat) ats :
  ∀ w, w_relp (foldl (λ w at_, load_post_at w aq v at_.1 at_.2) w ats)
       = w_relp w.
Proof. induction ats as [|at_ ats IH]; intros w; [done|by rewrite /= IH]. Qed.

Lemma w_pub_foldl_load (aq : bool) (v : nat) ats :
  ∀ w, w_pub (foldl (λ w at_, load_post_at w aq v at_.1 at_.2) w ats)
       = w_pub w.
Proof. induction ats as [|at_ ats IH]; intros w; [done|by rewrite /= IH]. Qed.

Lemma w_relp_load_post_bytes ws aq ats :
  w_relp (load_post_bytes ws aq ats) = w_relp ws.
Proof. apply w_relp_foldl_load. Qed.

Lemma w_pub_load_post_bytes ws aq ats :
  w_pub (load_post_bytes ws aq ats) = w_pub ws.
Proof. apply w_pub_foldl_load. Qed.

Lemma w_relp_load_post_run ws aq base ts :
  w_relp (load_post_run ws aq base ts) = w_relp ws.
Proof. apply w_relp_load_post_bytes. Qed.

Lemma w_pub_load_post_run ws aq base ts :
  w_pub (load_post_run ws aq base ts) = w_pub ws.
Proof. apply w_pub_load_post_bytes. Qed.

(** [w_relp] after a store run depends on the PRE-state's [w_relp] and
    on the byte list — never on the timestamp. *)
Lemma w_relp_foldl_store (rl : bool) as_ :
  ∀ w w' (t t' : nat), w_relp w = w_relp w' →
    w_relp (foldl (λ w a, store_post w rl a t) w as_)
    = w_relp (foldl (λ w a, store_post w rl a t') w' as_).
Proof.
  induction as_ as [|a as_ IH]; intros w w' t t' Heq; [done|].
  simpl. by apply IH.
Qed.

Lemma w_pub_foldl_store (rl : bool) as_ (t : nat) :
  ∀ w, (w_pub (foldl (λ w a, store_post w rl a t) w as_)
        ≤ Nat.max (w_pub w) t)%nat.
Proof.
  induction as_ as [|a as_ IH]; intros w; [simpl; lia|].
  simpl. have H := IH (store_post w rl a t).
  have Hp : (w_pub (store_post w rl a t) ≤ Nat.max (w_pub w) t)%nat.
  { rewrite /store_post /=. destruct (w_relp w || rl)%bool; lia. }
  lia.
Qed.

Lemma w_pub_foldl_store_eq (rl : bool) as_ (t : nat) :
  ∀ w, w_relp w = false → rl = false →
    w_pub (foldl (λ w a, store_post w rl a t) w as_) = w_pub w.
Proof.
  induction as_ as [|a as_ IH]; intros w Hrp Hrl; [done|].
  have Hrp' : w_relp (store_post w rl a t) = false by rewrite /store_post.
  simpl. rewrite (IH (store_post w rl a t) Hrp' Hrl).
  rewrite /store_post /= Hrp Hrl //.
Qed.

Lemma w_relp_store_post_bytes_indep (rl : bool) as_ w w' (t t' : nat) :
  w_relp w = w_relp w' →
  w_relp (store_post_bytes w rl as_ t) = w_relp (store_post_bytes w' rl as_ t').
Proof. apply w_relp_foldl_store. Qed.

Lemma w_pub_store_post_bytes_le (rl : bool) as_ (t : nat) w :
  (w_pub (store_post_bytes w rl as_ t) ≤ Nat.max (w_pub w) t)%nat.
Proof. apply w_pub_foldl_store. Qed.

Lemma w_pub_store_post_bytes_eq (rl : bool) as_ (t : nat) w :
  w_relp w = false → rl = false →
  w_pub (store_post_bytes w rl as_ t) = w_pub w.
Proof. apply w_pub_foldl_store_eq. Qed.

Lemma w_relp_store_post_run_indep (rl : bool) base n :
  ∀ w w' (t t' : nat), w_relp w = w_relp w' →
    w_relp (store_post_run w rl base n t)
    = w_relp (store_post_run w' rl base n t').
Proof. intros. by apply w_relp_store_post_bytes_indep. Qed.

Lemma w_pub_store_post_run_le (rl : bool) base n (t : nat) w :
  (w_pub (store_post_run w rl base n t) ≤ Nat.max (w_pub w) t)%nat.
Proof. apply w_pub_store_post_bytes_le. Qed.

Lemma w_pub_store_post_run_eq (rl : bool) base n (t : nat) w :
  w_relp w = false → rl = false →
  w_pub (store_post_run w rl base n t) = w_pub w.
Proof. intros. by apply w_pub_store_post_bytes_eq. Qed.

(* ---- the event folds ---- *)

(** σ-INDEPENDENCE of [w_relp]: no [wstate] rule computes the
    release-pending flag from a timestamp. *)
Lemma w_relp_aev_post_indep {D : Type} σ σ' (ev : aev D) w w' :
  w_relp w = w_relp w' → w_relp (aev_post σ ev w) = w_relp (aev_post σ' ev w').
Proof.
  intros Heq. rewrite /aev_post.
  destruct (ae_lb ev) as [|aq lat base tvs|rl base data|aq rl base tvs data
                          |pr pw sr sw]; [done| | | |].
  - by rewrite !w_relp_load_post_run.
  - destruct (ae_ts ev) as [ts|]; [|done].
    by apply w_relp_store_post_run_indep.
  - destruct (ae_ts ev) as [ts|]; [|done].
    apply w_relp_store_post_run_indep. by rewrite !w_relp_load_post_run.
  - rewrite /fence_post /=. by destruct (pw && sw)%bool.
Qed.

Lemma w_relp_aevs_post_indep {D : Type} σ σ' (evs : list (aev D)) :
  ∀ w w', w_relp w = w_relp w' →
    w_relp (aevs_post σ evs w) = w_relp (aevs_post σ' evs w').
Proof.
  induction evs as [|ev evs IH]; intros w w' Heq; [done|].
  rewrite /aevs_post /=. apply IH. by apply w_relp_aev_post_indep.
Qed.

(** ONE event keeps [w_pub] below [N] unless it RAISES — and a raising
    event is a fulfil whose label carries [rl] or whose pre-state has
    [w_relp] armed. *)
Lemma w_pub_aev_post_lt {D : Type} σ (ev : aev D) w (N : nat) :
  (w_pub w < N)%nat →
  (∀ ts, ae_ts ev = Some ts →
     (lb_rl (ae_lb ev) = true ∨ w_relp w = true) → (σ ts < N)%nat) →
  (w_pub (aev_post σ ev w) < N)%nat.
Proof.
  intros Hlt Hraise. rewrite /aev_post.
  destruct (ae_lb ev) as [|aq lat base tvs|rl base data|aq rl base tvs data
                          |pr pw sr sw] eqn:Hlb; [done| | | |].
  - by rewrite w_pub_load_post_run.
  - destruct (ae_ts ev) as [ts|] eqn:Hts; [|done].
    destruct (decide (w_relp w = true ∨ rl = true)) as [Hr|Hr].
    + have Hσ : (σ ts < N)%nat.
      { apply (Hraise ts eq_refl). simpl. tauto. }
      have := w_pub_store_post_run_le rl base (length data) (σ ts) w. lia.
    + have Hrp : w_relp w = false.
      { destruct (w_relp w) eqn:E; [|done]. destruct Hr. by left. }
      have Hrl : rl = false.
      { destruct rl eqn:E; [|done]. destruct Hr. by right. }
      by rewrite (w_pub_store_post_run_eq rl base (length data) (σ ts) w Hrp Hrl).
  - destruct (ae_ts ev) as [ts|] eqn:Hts; [|done].
    set w0 := load_post_run w aq base (σ <$> tvs.*1).
    have Hp0 : w_pub w0 = w_pub w by apply w_pub_load_post_run.
    have Hr0 : w_relp w0 = w_relp w by apply w_relp_load_post_run.
    destruct (decide (w_relp w = true ∨ rl = true)) as [Hr|Hr].
    + have Hσ : (σ ts < N)%nat.
      { apply (Hraise ts eq_refl). simpl. tauto. }
      have := w_pub_store_post_run_le rl base (length data) (σ ts) w0. lia.
    + have Hrp : w_relp w0 = false.
      { rewrite Hr0. destruct (w_relp w) eqn:E; [|done]. destruct Hr. by left. }
      have Hrl : rl = false.
      { destruct rl eqn:E; [|done]. destruct Hr. by right. }
      rewrite (w_pub_store_post_run_eq rl base (length data) (σ ts) w0 Hrp Hrl).
      lia.
  - by rewrite /fence_post /=.
Qed.

(** …hence a whole processed prefix does, provided every raising event
    in it has its transported timestamp below [N]. *)
Lemma w_pub_aevs_post_lt {D : Type} σ (evs : list (aev D)) :
  ∀ w (N : nat),
    (w_pub w < N)%nat →
    (∀ k ev ts, evs !! k = Some ev → ae_ts ev = Some ts →
       (lb_rl (ae_lb ev) = true ∨
        w_relp (aevs_post σ (take k evs) w) = true) →
       (σ ts < N)%nat) →
    (w_pub (aevs_post σ evs w) < N)%nat.
Proof.
  induction evs as [|ev evs IH]; intros w N Hw Hall; [done|].
  rewrite /aevs_post /=. apply IH.
  - apply (w_pub_aev_post_lt σ ev w N Hw).
    intros ts Hts Hr. by apply (Hall 0%nat ev ts).
  - intros k ev' ts Hk Hts Hr. apply (Hall (S k) ev' ts); [done|done|].
    by rewrite /= in Hr |- *.
Qed.

(* ------------------------------------------------------------------ *)
(** ** LAYER 1: the Layer-2 parameters, instantiated

    [WeakRobust]'s [violation] takes the classification [cls] and the
    publication predicate [pub] as PARAMETERS (D-M6-2/D-M6-6).  Here are
    the instances Layer 2 will hand it: the class is read off the
    message's inert [wm_ak] field, and publication off the AUTHOR's
    inert [w_pub] watermark in the configuration. *)

Definition cls_of (m : wmsg) : store_class :=
  match wm_ak m with
  | WCplain => SCowned
  | WCrel => SCfenced
  | WCexcl => SCexcl
  end.

(** [pub_of c ts]: the message at timestamp [ts] has been published by
    ITS OWN author.  [violation] uses it as [¬ pub c (S p)] for the
    message at log position [p], so the author is found through the log.

    PUBLICATION IS A LOG PREDICATE ([WeakMem.wpublished]): a LATER
    message of the same author is release-class.  That is the alignment
    item of the lift plan (obstacle 3): the Iris side's C/D/S invariant
    and φ export are stated with the very same [wpublished]
    ([WeakGhost.wcds_clean], [WeakGhost.no_violation]), so
    [WeakRobust.violation cls_of pub_of] and [WeakGhost.no_violation]
    now agree SYNTACTICALLY and the [wpub_covers] wiring debt
    ([WeakViolation] §4) is off the export path.

    IT REPLACES the old watermark reading ([∃ ag, pc_ags c !! i = Some ag
    ∧ ts ≤ w_pub (pa_ws ag)]).  The two are tied by
    [WeakViolation.wpublished_w_pub] under [wpub_covers]; the log form is
    the one both towers can state, and it is MONOTONE under append,
    which the watermark form was not (it reads the agent vector). *)
Definition pub_of {P D : Type} (c : wpcfg P D) (ts : nat) : Prop :=
  ∃ (p : nat) (m : wmsg),
    ts = S p ∧ pc_log c !! p = Some m ∧ wpublished (pc_log c) (wm_tid m) p.

(* ------------------------------------------------------------------ *)
(** ** LAYER 2: the per-edge split — [edge_ok] or [bad]

    [bad e1 e2] is the OWNED-UNPUBLISHED CROSS READ: a foreign agent
    reads a [WCplain] message and NO publishing event of the author
    lies, po-at-or-after the author's own fulfil, in the strict ancestry
    of the reader.  Worklist item (2b) pins exactly this shape; the
    "po-at-or-after" (rather than "strictly after") is this file's
    delta — see the header. *)

(** The author's pre-state at an event; [ws_init] off the trace (junk,
    never reached: every use is under [gev_wf]). *)
Definition pre_ws {P D : Type} (TS : ptraces P D) (e : gev) : wstate :=
  match pt_trs TS !! e.1 with
  | Some T => match at_ags T !! e.2 with
              | Some ag => pa_ws ag
              | None => ws_init
              end
  | None => ws_init
  end.

(** A PUBLISHING EVENT: a fulfil whose MESSAGE IS RELEASE-CLASS.

    THIS IS THE CLASS READING, not the old "raises [w_pub]" one
    ([lb_rl], or a [pw ∧ sw] fence armed [w_relp] before it — kept below
    as [pub_event_raises] for the record).  It changed with [pub_of]:
    publication is now [WeakMem.wpublished], which is itself class-based,
    so the exhibit's ¬pub arm reads a [WCrel] message straight off the pf
    log and needs no [w_pub] fold arithmetic at all (obstacle 3 of the
    lift plan: "it gets EASIER").  The two readings differ on exactly one
    shape — an [rl]-AMO raises [w_pub] while being tagged [WCexcl] — and
    BOTH sides of the new alignment take the class reading, so nothing is
    left dangling: an [rl]-AMO publishes under neither [wpublished] nor
    [pub_event]. *)
Definition pub_event {P D : Type} (TS : ptraces P D) (e : gev) : Prop :=
  ∃ ts m, gev_ts TS e = Some ts ∧ pt_log TS !! (ts - 1)%nat = Some m ∧
          wm_ak m = WCrel.

(** The MACHINE reading, RECORDED ONLY (nothing consumes it): the fulfil
    raises [w_pub].  [WeakInterp.wm_class_of] tags a store [WCrel] exactly
    when [¬ ak_latest ∧ (w_relp ∨ ak_sync)], so on non-exclusive fulfils
    the two coincide; the gap is the [rl]-AMO above. *)
Definition pub_event_raises {P D : Type} (TS : ptraces P D) (e : gev) : Prop :=
  is_Some (gev_ts TS e) ∧
  ∃ l, gev_lb TS e = Some l ∧
       (lb_rl l = true ∨ w_relp (pre_ws TS e) = true).

(** [bad nh TS e1 e2] — the OWNED-UNPUBLISHED CROSS READ.  [nh] is the
    number of HART agents; BOTH the writer and the reader must be one of
    them.

    THE HART CONJUNCTS ([e1.1 < nh], [e2.1 < nh]) are the DMA-tid
    unification's Layer-1 half (seam 1a of the lift plan).  Now that the disk is an ORDINARY
    agent with an ordinary index ([WeakLang.n_disk = NCPU]), its
    [WCplain] DMA messages would otherwise be candidates for [bad] — and
    φ says nothing about them: the C/D/S invariants exempt every non-hart
    author ([WeakGhost.wcds_clean]), because a device never publishes.
    Carrying "the writer is a hart" here keeps [bad] inside φ's domain of
    discourse.  It STRENGTHENS [edges_split] (fewer edges may take the
    [bad] escape) and weakens nothing downstream: [no_bad_edge]'s
    conclusion is only ever consumed to turn [edges_split] back into
    [rf_edges_ok].  Layer 1 cannot name [NCPU] (it is stdpp-only and
    knows no [RiscvLang]), so the bound is a parameter; [WeakCompose]
    fixes it.

    THE READER'S BOUND ([e2.1 < nh]) is the SAME conjunct on the OTHER
    end of the edge, and it is what makes the exhibit's conclusion
    [WeakRobust.violation_hart] rather than the unrestricted
    [violation]: the observer of the violating message is the reader of
    the bad edge, and φ says nothing about a NON-hart observer either —
    the disk's own DMA raises its [coh] over a plainly-written hart byte,
    which is a [violation] with [j = n_disk] and no φ to refute it.  The
    bound is FREE for xv6 at the site that discharges [edges_split]: a
    [grf] edge's target executes a load or an rmw, and in
    [WeakCompose.pstep_xv6] only the hart arms emit [LLoad]/[LRmw] (the
    disk arm emits stores only — [WeakCompose.xv6_lat_free]'s disk
    case).  Like the writer's bound it only NARROWS the [bad] escape
    hatch of [edges_split].

    THE ANCESTRY IS OVER [gdep3], NOT [gdep2] (G5's one deviation from the
    W2c shape, and it is forced).  The exhibit replays the ancestor cone of
    the bad read, and with a fabric the cone that is DOWNWARD CLOSED for
    [WeakRobustSim.Qinv_step] is the [gdep3 = gdep2 ∪ gdev] one — the
    replay has to hand each fabric-touching event the fabric it recorded,
    so a [gdev] predecessor of a cone event is a cone event.  The
    "no publishing ancestor" conjunct therefore has to quantify over the
    SAME relation the cone is closed under, or the ¬pub arm of
    [bad_edge_violates] cannot use the publishing fulfil it finds in the
    cone.  It STRENGTHENS [bad] (the ∃ it negates ranges over a bigger
    relation), hence strengthens [edges_split]; under a dev-free marker
    [gdep3] IS [gdep2] ([gdep3_nil_gdep2]) and nothing moves. *)
Definition bad {P D : Type} (nh : nat) (TS : ptraces P D) (DS : pdevs D)
    (e1 e2 : gev) : Prop :=
  grf TS e1 e2 ∧ e1.1 ≠ e2.1 ∧ (e1.1 < nh)%nat ∧ (e2.1 < nh)%nat ∧
  (∃ ts m, gev_ts TS e1 = Some ts ∧ pt_log TS !! (ts - 1)%nat = Some m ∧
           wm_ak m = WCplain) ∧
  ¬ (∃ ep, ep.1 = e1.1 ∧ (e1.2 ≤ ep.2)%nat ∧ pub_event TS ep ∧
           tc (gdep3 TS DS) ep e2).

(** THE WEAKENED PER-EDGE PREMISE.  Same quantification as
    [WeakRobustAcyc.rf_edges_ok], with the conclusion weakened to a
    disjunction. *)
Definition edges_split {P D : Type} (nh : nat) (TS : ptraces P D)
    (DS : pdevs D) : Prop :=
  ∀ e1 e2 T ts a k' ev',
    gev_ts TS e1 = Some ts → gev_reads TS e2 a ts → e1.1 ≠ e2.1 →
    pt_trs TS !! e2.1 = Some T →
    (e2.2 < k')%nat →
    at_evs T !! k' = Some ev' → is_Some (ae_ts ev') →
    edge_ok T e2.2 k' ts ∨ bad nh TS DS e1 e2.

(** …and the RELATIVIZED strong premise: [edge_ok] at every cross edge
    whose READER satisfies [W].  This is the shape the walk below
    consumes, and the only shape the walk ever APPLIES. *)
Definition rf_edges_ok_on {P D : Type} (TS : ptraces P D) (W : gev → Prop)
    : Prop :=
  ∀ e1 e2 T ts a k' ev',
    gev_ts TS e1 = Some ts → gev_reads TS e2 a ts → e1.1 ≠ e2.1 → W e2 →
    pt_trs TS !! e2.1 = Some T →
    (e2.2 < k')%nat →
    at_evs T !! k' = Some ev' → is_Some (ae_ts ev') →
    edge_ok T e2.2 k' ts.

Lemma rf_edges_ok_on_full {P D : Type} (TS : ptraces P D) (W : gev → Prop) :
  rf_edges_ok TS → rf_edges_ok_on TS W.
Proof.
  intros H e1 e2 T ts a k' ev' Hts Hrd Hne _ HT Hlt Hev Hsome.
  by eapply H.
Qed.

(** THE RESIDUE (worklist item (3)).  [bad_min TS e2]: no bad edge's
    target is a STRICT ancestor of [e2] — the minimality the exhibit
    picks.  [bad_wf]: whenever a bad edge exists, some bad edge is
    minimal in that sense.  A "bad SCC" (mutually-justified owned reads)
    is exactly what this excludes: it has no minimal element, its
    events' pf-realization is circular, and its message never enters the
    pf log, so no exhibit can be built. *)
Definition bad_min {P D : Type} (nh : nat) (TS : ptraces P D) (DS : pdevs D)
    (e2 : gev) : Prop :=
  ∀ f1 f2, bad nh TS DS f1 f2 → ¬ tc (gdep3 TS DS) f2 e2.

Definition bad_wf {P D : Type} (nh : nat) (TS : ptraces P D) (DS : pdevs D)
    : Prop :=
  ∀ e1 e2, bad nh TS DS e1 e2 →
    ∃ f1 f2, bad nh TS DS f1 f2 ∧ bad_min nh TS DS f2.

(* ------------------------------------------------------------------ *)
(** ** LAYER 3: THE RELATIVIZED WALK

    [WeakRobustAcyc2]'s measure walk consumes [rf_edges_ok] at EXACTLY
    ONE place — [mile_mu_gain]'s cross-rf arm — and both of
    [on_cycle2_advance]'s call sites have the milestone's TARGET [u] on
    a cycle.  So the walk relativizes to any predicate [W] on readers
    that is CLOSED under mutual reachability, giving "no cycle through a
    [W]-event".  Everything structural ([mile_mu], [gmile],
    [tc_gdep2_split], [rtc_gdep2_first_mile], [mile_mu_bounded],
    [mile_mu_src_ts]) is imported from that file unchanged.

    KEEP IN SYNC with [WeakRobustAcyc2]: the three lemmas below are
    line-for-line its [mile_mu_gain] / [on_cycle2_advance] /
    [on_cycle2_empty] with [W]-guarded premises. *)

Section walk.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pdev : P → wlabel → P → bool).

  Implicit Types TS : ptraces P D.
  Implicit Types e : gev.

  Lemma gmile_gdep2 TS x y : gmile TS x y → gdep2 TS x y.
  Proof. intros [[Hd _]|HE]; [by apply gdep_gdep2|by apply gE_gdep2]. Qed.

  (** THE GAIN LEMMA, relativized: the entry milestone's target [u] must
      satisfy [W] (that is where the discipline premise is spent). *)
  Lemma mile_mu_gain_on TS (W : gev → Prop) mu v u x tx :
    ptraces_wf pstep TS → ptraces_fwd_own TS →
    rf_edges_ok_on TS W → ee_ok TS →
    W u → mile_mu TS mu v u → u.1 = x.1 → (u.2 ≤ x.2)%nat →
    gev_ts TS x = Some tx →
    (mu < tx)%nat.
  Proof.
    intros Hwf Hfo Hrf Hee HWu
           [(a & Hts1 & Hrd & Hne)|(r & a & Hra & ->)] Hag Hle Htx.
    - (* CROSS-RF ENTRY: S1, with the reader [u] satisfying [W]. *)
      have Hwfu : gev_wf TS u by eapply gev_reads_wf.
      apply gev_wf_bounds in Hwfu as (T & HT & _).
      have HTx : pt_trs TS !! x.1 = Some T by rewrite -Hag.
      destruct (gev_reads_ev TS u a mu T HT Hrd) as (ev & Hev & Hinr).
      destruct (gev_ts_ev TS x tx T HTx Htx) as (evx & Hevx & Htsx).
      destruct (gev_ts_msg pstep TS v mu Hwf Hts1) as (base & data & kc & Hm).
      have Hunf : read_unforwarded (pt_log TS) u.1 (ae_lb ev) mu.
      { right. exists (WMsg base data (Some v.1) kc), v.1.
        split_and!; [exact Hm|done|exact Hne]. }
      eapply (atrace_S1_le pstep (pt_img TS) (pt_log TS) u.1 T u.2 x.2
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
          [exact Hts1|exact Hrd|exact Hne|exact HWu|exact HT|exact Hklt
           |exact Hevx|].
        rewrite Htsx. by eexists.
    - (* gE ENTRY: no discipline premise at all. *)
      destruct (decide (u.2 = x.2)) as [Heq|Hne].
      + have Hux : u = x.
        { destruct u as [i k], x as [i' k']. simpl in Hag, Heq. by subst. }
        rewrite -Hux in Htx.
        destruct Hra
          as (l & ts & tstar & that & _ & _ & _ & _ & _ & H6 & _ & Hlt).
        rewrite H6 in Htx. by simplify_eq.
      + eapply (Hee r a v u x tx); [exact Hra|exact Hag|lia|exact Htx].
  Qed.

  Definition on_cycle2_on TS (W : gev → Prop) (mu : nat) : Prop :=
    ∃ v u, mile_mu TS mu v u ∧ rtc (gdep2 TS) u v ∧ W u.

  Lemma on_cycle2_advance_on TS (W : gev → Prop) mu :
    ptraces_wf pstep TS → ptraces_fwd_own TS →
    rf_edges_ok_on TS W → ee_ok TS →
    (∀ u x, W u → rtc (gdep2 TS) u x → rtc (gdep2 TS) x u → W x) →
    on_cycle2_on TS W mu → ∃ mu', (mu < mu')%nat ∧ on_cycle2_on TS W mu'.
  Proof.
    intros Hwf Hfo Hrf Hee Hcl (v & u & Hm & Hpath & HWu).
    destruct (rtc_gdep2_first_mile pstep TS u v Hwf Hpath)
      as [[Hag Hle]|(x & y & Hag & Hle & Hux & Hmile & Hyv)].
    - exfalso.
      destruct (mile_mu_src_ts TS mu v u Hm) as (tv & Htv & Hlev).
      have Hgt := mile_mu_gain_on TS W mu v u v tv Hwf Hfo Hrf Hee HWu Hm
                    Hag Hle Htv.
      lia.
    - have Hedge : gdep2 TS v u by eapply mile_mu_gdep2.
      have Hyx : rtc (gdep2 TS) y x.
      { eapply rtc_transitive; [exact Hyv|].
        eapply rtc_l; [exact Hedge|exact Hux]. }
      (* the exit milestone's TARGET inherits [W] *)
      have HWy : W y.
      { eapply (Hcl u y HWu).
        - eapply rtc_r; [exact Hux|by apply gmile_gdep2].
        - eapply rtc_r; [exact Hyv|exact Hedge]. }
      destruct Hmile as [[Hd Hne]|HE].
      + have Hrfxy : grf TS x y.
        { destruct Hd as [(Hag' & _)|Hrf']; [by destruct (Hne Hag')|exact Hrf']. }
        destruct Hrfxy as (ts2 & a2 & Hts2 & Hrd2).
        have Hlt := mile_mu_gain_on TS W mu v u x ts2 Hwf Hfo Hrf Hee HWu Hm
                      Hag Hle Hts2.
        exists ts2. split; [exact Hlt|].
        exists x, y. split_and!; [|exact Hyx|exact HWy].
        left. exists a2. by split_and!.
      + destruct HE as (r' & Hat).
        destruct (gE_at_gE_ra TS r' x y Hat) as (a' & Hra').
        have Hra'' := Hra'.
        destruct Hra''
          as (l' & ts' & tstar' & that' & _ & _ & Hleaf' & _ & H5' & _).
        have Hlt := mile_mu_gain_on TS W mu v u x tstar' Hwf Hfo Hrf Hee HWu Hm
                      Hag Hle H5'.
        have Hle' : (tstar' ≤ rd_floor TS r' a')%nat
          by apply (lval_ge id _ _ Hleaf').
        exists (rd_floor TS r' a'). split; [lia|].
        exists x, y. split_and!; [|exact Hyx|exact HWy].
        right. by exists r', a'.
  Qed.

  Lemma on_cycle2_on_bounded TS W mu :
    ptraces_wf pstep TS → on_cycle2_on TS W mu →
    (mu ≤ length (pt_log TS))%nat.
  Proof. intros Hwf (v & u & Hm & _). by eapply mile_mu_bounded. Qed.

  Lemma on_cycle2_on_empty TS (W : gev → Prop) :
    ptraces_wf pstep TS → ptraces_fwd_own TS →
    rf_edges_ok_on TS W → ee_ok TS →
    (∀ u x, W u → rtc (gdep2 TS) u x → rtc (gdep2 TS) x u → W x) →
    ∀ mu, ¬ on_cycle2_on TS W mu.
  Proof.
    intros Hwf Hfo Hrf Hee Hcl.
    have Hgen : ∀ n mu, (length (pt_log TS) - mu ≤ n)%nat →
                        ¬ on_cycle2_on TS W mu.
    { induction n as [|n IH]; intros mu Hn Hoc.
      - have Hb := on_cycle2_on_bounded TS W mu Hwf Hoc.
        destruct (on_cycle2_advance_on TS W mu Hwf Hfo Hrf Hee Hcl Hoc)
          as (mu' & Hlt & Hoc').
        have Hb' := on_cycle2_on_bounded TS W mu' Hwf Hoc'. lia.
      - destruct (on_cycle2_advance_on TS W mu Hwf Hfo Hrf Hee Hcl Hoc)
          as (mu' & Hlt & Hoc').
        eapply (IH mu'); [|exact Hoc'].
        have Hb' := on_cycle2_on_bounded TS W mu' Hwf Hoc'. lia. }
    intros mu. by eapply (Hgen (length (pt_log TS) - mu)%nat).
  Qed.

  (** THE RELATIVIZED THEOREM: no [gdep2] cycle passes through a
      [W]-event. *)
  Theorem gdep2_acyclic_on TS (W : gev → Prop) :
    ptraces_wf pstep TS → ptraces_fwd_own TS →
    rf_edges_ok_on TS W → ee_ok TS →
    (∀ u x, W u → rtc (gdep2 TS) u x → rtc (gdep2 TS) x u → W x) →
    ∀ e, W e → ¬ tc (gdep2 TS) e e.
  Proof.
    intros Hwf Hfo Hrf Hee Hcl e HWe Hc.
    destruct (tc_gdep2_split pstep TS e e Hwf Hc)
      as [[_ Hlt]|(x & y & Hrx & Hmile & Hry)]; [lia|].
    have HWy : W y.
    { eapply (Hcl e y HWe).
      - eapply rtc_r; [exact Hrx|by apply gmile_gdep2].
      - exact Hry. }
    destruct (gmile_mile_mu TS x y Hmile) as (mu & Hm).
    eapply (on_cycle2_on_empty TS W Hwf Hfo Hrf Hee Hcl mu).
    exists x, y. split_and!; [exact Hm| |exact HWy].
    eapply rtc_transitive; [exact Hry|exact Hrx].
  Qed.

End walk.

(** THE STRONG-RESIDUE SHORTCUT (recorded, not used below).  If the
    residue is taken in its STRONG form — no bad edge's target lies on
    ANY cycle — the walk closes globally with no exhibit and no
    [pf_violation_free_hart] at all: every cross edge whose reader is on a
    cycle is [edge_ok] by [edges_split], and that is the only place the
    walk looks.  The main theorem deliberately takes the WEAK form
    ([bad_wf]: some bad edge is minimal), which does NOT give this and
    is what the exhibit is for. *)
Definition bad_wf_strong {P D : Type} (nh : nat) (TS : ptraces P D)
    (DS : pdevs D) : Prop :=
  ∀ e1 e2, bad nh TS DS e1 e2 → ¬ tc (gdep2 TS) e2 e2.

Theorem gdep2_acyclic_bad_free {P D : Type} (pstep : P → D → wlabel → P → D → Prop)
    (nh : nat) (TS : ptraces P D) (DS : pdevs D) :
  ptraces_wf pstep TS → ptraces_fwd_own TS → ee_ok TS →
  edges_split nh TS DS → bad_wf_strong nh TS DS →
  gdep2_acyclic TS.
Proof.
  intros Hwf Hfo Hee Hsplit Hbs.
  have Hrf : rf_edges_ok_on TS (λ e, tc (gdep2 TS) e e).
  { intros e1 e2 T ts a k' ev' Hts Hrd Hne HW HT Hlt Hev Hsome.
    destruct (Hsplit e1 e2 T ts a k' ev' Hts Hrd Hne HT Hlt Hev Hsome)
      as [Hok|Hbad]; [exact Hok|]. by destruct (Hbs e1 e2 Hbad HW). }
  have Hcl : ∀ u x, tc (gdep2 TS) u u → rtc (gdep2 TS) u x →
                    rtc (gdep2 TS) x u → tc (gdep2 TS) x x.
  { intros u x HWu Hux Hxu. eapply tc_rtc_l; [exact Hxu|].
    eapply tc_rtc_r; [exact HWu|exact Hux]. }
  intros e He.
  by eapply (gdep2_acyclic_on pstep TS (λ e0, tc (gdep2 TS) e0 e0)
               Hwf Hfo Hrf Hee Hcl e He).
Qed.

(* ------------------------------------------------------------------ *)
(** ** LAYER 4: THE ANCESTOR CONE, CONCRETELY

    The exhibit sorts the STRICT ANCESTRY of the bad read, and the
    subset sort needs that set to be DECIDABLE — [Decision (tc R e
    root)] is not free.  Rather than reflecting [tc], the predecessor
    closure is COMPUTED: start from [{root}] and repeatedly add every
    carrier element with an edge into the current set.  After
    [|carrier|] rounds the set has saturated (each non-saturated round
    strictly grows a [NoDup] sublist of the carrier), and a saturated
    set is predecessor-closed — which is exactly [tc]-completeness.

    Generic in the relation and the carrier; nothing here mentions
    [gev]. *)

Section closure.
  Context {A : Type} `{!EqDecision A}.
  Context (R : A → A → Prop) `{!RelDecision R}.
  Context (carrier : list A) (root : A).
  Context (Hroot : root ∈ carrier).
  Context (Hcar : ∀ x y, R x y → x ∈ carrier).
  Context (Hnd : NoDup carrier).

  Definition anc_new (l : list A) : list A :=
    filter (λ e, e ∉ l ∧ Exists (λ y, R e y) l) carrier.

  Definition anc_step (l : list A) : list A := l ++ anc_new l.

  Fixpoint anc_iter (n : nat) : list A :=
    match n with
    | O => [root]
    | S n => anc_step (anc_iter n)
    end.

  Definition anc : list A := anc_iter (length carrier).

  Lemma elem_of_anc_new l x :
    x ∈ anc_new l ↔ (x ∉ l ∧ (∃ y, y ∈ l ∧ R x y)) ∧ x ∈ carrier.
  Proof.
    rewrite /anc_new elem_of_list_filter. split.
    - intros [[Hnin Hex] Hin]. split; [split; [done|]|done].
      by apply list_relations.Exists_exists in Hex.
    - intros [[Hnin Hex] Hin]. split; [split; [done|]|done].
      by apply list_relations.Exists_exists.
  Qed.

  Lemma anc_iter_carrier n x : x ∈ anc_iter n → x ∈ carrier.
  Proof.
    induction n as [|n IH]; simpl.
    - intros Hx. by apply elem_of_list_singleton in Hx as ->.
    - rewrite /anc_step elem_of_app. intros [Hx|Hx]; [by apply IH|].
      by apply elem_of_anc_new in Hx as [_ ?].
  Qed.

  Lemma anc_iter_nodup n : NoDup (anc_iter n).
  Proof.
    induction n as [|n IH]; simpl; [apply NoDup_singleton|].
    rewrite /anc_step. apply list_relations.NoDup_app. split_and!.
    - exact IH.
    - intros x Hx Hx'. by apply elem_of_anc_new in Hx' as [[Hnin _] _].
    - apply list_relations.NoDup_filter, Hnd.
  Qed.

  Lemma anc_iter_mono n x : x ∈ anc_iter n → x ∈ anc_iter (S n).
  Proof. intros Hx. rewrite /= /anc_step elem_of_app. by left. Qed.

  Lemma anc_iter_mono_le n m x : (n ≤ m)%nat → x ∈ anc_iter n → x ∈ anc_iter m.
  Proof.
    intros Hle Hx. induction m as [|m IH].
    - have Hn : n = 0%nat by lia. by subst n.
    - destruct (decide (n = S m)) as [->|Hne]; [done|].
      apply anc_iter_mono, IH. lia.
  Qed.

  (** SOUNDNESS: everything the iteration collects is [root] or a
      [tc]-predecessor of it. *)
  Lemma anc_iter_sound n : ∀ x, x ∈ anc_iter n → x = root ∨ tc R x root.
  Proof.
    induction n as [|n IH]; simpl; intros x.
    - intros Hx. left. by apply elem_of_list_singleton in Hx.
    - rewrite /anc_step elem_of_app. intros [Hx|Hx]; [by apply IH|].
      apply elem_of_anc_new in Hx as [[_ (y & Hy & HR)] _].
      right. destruct (IH y Hy) as [->|Htc]; [by apply tc_once|].
      by eapply tc_l.
  Qed.

  (** SATURATION: either the round-[n] set already has [n+1] elements or
      the iteration has stopped by round [n]. *)
  Lemma anc_grow n :
    (S n ≤ length (anc_iter n))%nat ∨
    ∃ m, (m ≤ n)%nat ∧ anc_new (anc_iter m) = [].
  Proof.
    induction n as [|n IH].
    - left. by simpl.
    - destruct IH as [Hlen|(m & Hm & Hnil)]; [|right; exists m; split; [lia|done]].
      destruct (decide (anc_new (anc_iter n) = [])) as [Hnil|Hne].
      + right. exists n. by split; [lia|].
      + left. rewrite /= /anc_step length_app.
        have Hpos : (0 < length (anc_new (anc_iter n)))%nat.
        { destruct (anc_new (anc_iter n)); [done|simpl; lia]. }
        lia.
  Qed.

  Lemma anc_new_nil : anc_new anc = [].
  Proof.
    destruct (anc_grow (length carrier)) as [Hlen|(m & Hm & Hnil)].
    - exfalso.
      have Hle : (length (anc_iter (length carrier)) ≤ length carrier)%nat.
      { apply list_relations.submseteq_length.
        apply list_relations.NoDup_submseteq; [apply anc_iter_nodup|].
        apply anc_iter_carrier. }
      lia.
    - have Hstab : ∀ d, anc_iter (m + d) = anc_iter m.
      { induction d as [|d IH]; [by rewrite Nat.add_0_r|].
        rewrite Nat.add_succ_r /= /anc_step IH Hnil app_nil_r //. }
      have Hd : length carrier = (m + (length carrier - m))%nat by lia.
      rewrite /anc Hd Hstab //.
  Qed.

  Lemma root_in_anc : root ∈ anc.
  Proof.
    rewrite /anc. apply (anc_iter_mono_le 0%nat); [lia|].
    apply elem_of_list_here.
  Qed.

  Lemma anc_closed x y : y ∈ anc → R x y → x ∈ anc.
  Proof.
    intros Hy HR. destruct (decide (x ∈ anc)) as [Hx|Hx]; [done|exfalso].
    have Hin : x ∈ anc_new anc.
    { apply elem_of_anc_new. split; [split; [done|by exists y]|].
      by eapply Hcar. }
    rewrite anc_new_nil in Hin. by apply elem_of_nil in Hin.
  Qed.

  (** COMPLETENESS: every [tc]-predecessor of an element of [anc] is in
      [anc]. *)
  Lemma anc_tc x y : tc R x y → y ∈ anc → x ∈ anc.
  Proof.
    induction 1 as [x y HR|x y z HR Htc IH]; intros Hin.
    - by eapply anc_closed.
    - eapply anc_closed; [|exact HR]. by apply IH.
  Qed.

  Lemma elem_of_anc x : x ∈ anc ↔ (x = root ∨ tc R x root).
  Proof.
    split.
    - apply anc_iter_sound.
    - intros [->|Htc]; [apply root_in_anc|].
      eapply anc_tc; [exact Htc|apply root_in_anc].
  Qed.

End closure.

(* ------------------------------------------------------------------ *)
(** ** LAYER 5: THE CONE, SORTED — [Qinv] over the strict ancestry of one
       event

    [WeakRobustSim.sim_prefix] would do this in one line, but it
    consumes GLOBAL [gdep2_acyclic] — which the exhibit does not have.
    So the generic [WeakRobustLin.topo_sort] is instantiated at the
    RESTRICTED relation [Rcone = gdep2 ∩ Ucone²] (whose acyclicity is
    exactly the relativized walk's conclusion) and [toposort_ind_S]'s
    prefix induction is re-run with [Qinv_step] — which needs no
    acyclicity at all. *)

Section cone.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pdev : P → wlabel → P → bool).
  Context (TS : ptraces P D) (img : image) (d0 : D) (ps : list P).
  Context (Hwf : ptraces_wf pstep TS).
  Context (Hwsi : ptraces_ws_init TS).
  Context (Hco : ∀ a, co_tc TS a).
  Context (Hwfl : writes_fulfilled TS).
  Context (Hlf : lat_free_prog pstep).
  Context (Hobl : ts_oblivious pstep).
  Context (Himg : pt_img TS = img).
  Context (Hnag : length (pt_trs TS) = length ps).
  Context (Hdata : ∀ p m, pt_log TS !! p = Some m → wm_data m ≠ []).
  Context (Hps0 : ∀ j T ag0, pt_trs TS !! j = Some T →
                    at_ags T !! 0%nat = Some ag0 → ps !! j = Some (pa_st ag0)).
  (** THE FABRIC (G5b): the behavior's own device-order witness.  The
      cone is the ancestry under [gdep3 = gdep2 ∪ gdev] — [Qinv_step]'s
      predecessor hypothesis is over [gdep3], so a [gdev] predecessor of
      a cone event is a cone event, and the replay hands every
      fabric-touching event the fabric it recorded. *)
  Context (DS : pdevs D).
  Context (Hwit : ptraces_wit TS DS).
  Context (Hd0 : pd_init DS = d0).

  (** The event whose ancestry is replayed (the bad read), and the three
      facts about it the cone needs: it is a real event, it is not on a
      cycle, and no cycle passes through its ancestry. *)
  Context (r : gev).
  Context (Hrwf : gev_wf TS r).
  Context (Hrr : ¬ tc (gdep3 TS DS) r r).
  Context (Hconeacyc : ∀ e, tc (gdep3 TS DS) e r → ¬ tc (gdep3 TS DS) e e).

  Definition ancr : list gev := anc (gdep3 TS DS) (gev_enum TS) r.

  Definition Ucone (e : gev) : Prop := e ∈ ancr ∧ e ≠ r.

  Local Instance Ucone_dec e : Decision (Ucone e).
  Proof. rewrite /Ucone. apply and_dec; apply _. Defined.

  Lemma r_in_enum : r ∈ gev_enum TS.
  Proof. by apply elem_of_gev_enum. Qed.

  Lemma elem_of_ancr e : e ∈ ancr ↔ (e = r ∨ tc (gdep3 TS DS) e r).
  Proof.
    apply (elem_of_anc (gdep3 TS DS) (gev_enum TS) r r_in_enum).
    - intros x y Hd. apply elem_of_gev_enum.
      by destruct (gdep3_wf TS DS x y Hwit Hd).
    - apply NoDup_gev_enum.
  Qed.

  Lemma Ucone_iff e : Ucone e ↔ (gev_wf TS e ∧ tc (gdep3 TS DS) e r).
  Proof.
    split.
    - intros [Hin Hne]. split.
      + apply elem_of_gev_enum.
        eapply (anc_iter_carrier (gdep3 TS DS) (gev_enum TS) r r_in_enum);
          exact Hin.
      + apply elem_of_ancr in Hin as [->|Htc]; [done|exact Htc].
    - intros [Hwfe Htc]. split.
      + apply elem_of_ancr. by right.
      + intros ->. by apply Hrr.
  Qed.

  Lemma Ucone_wf e : Ucone e → gev_wf TS e.
  Proof. intros H. by apply Ucone_iff in H as [? _]. Qed.

  Lemma Ucone_dc : dc TS (gdep3 TS DS) Ucone.
  Proof.
    intros e e' HU Hd Hwf'. apply Ucone_iff. apply Ucone_iff in HU as [_ Htc].
    split; [done|]. by eapply tc_l.
  Qed.

  Lemma Ucone_sub_ok : sub_ok TS (gdep3 TS DS) Ucone.
  Proof. split; [apply Ucone_dc|apply Ucone_wf]. Qed.

  (** The RESTRICTED relation and its acyclicity. *)
  Definition Rcone (x y : gev) : Prop := gdep3 TS DS x y ∧ Ucone x ∧ Ucone y.

  Local Instance Rcone_dec : RelDecision Rcone.
  Proof. intros x y. rewrite /Rcone. apply and_dec; apply _. Defined.

  Lemma tc_Rcone x y : tc Rcone x y → tc (gdep3 TS DS) x y ∧ Ucone x.
  Proof.
    induction 1 as [x y (Hd & Hx & Hy)|x y z (Hd & Hx & Hy) Htc IH].
    - split; [by apply tc_once|done].
    - split; [|done]. eapply tc_l; [exact Hd|apply IH].
  Qed.

  Lemma Rcone_acyc x : ¬ tc Rcone x x.
  Proof.
    intros Hc. destruct (tc_Rcone x x Hc) as (Htc & HU).
    apply Ucone_iff in HU as [_ Hanc]. by eapply Hconeacyc.
  Qed.

  (** THE CONE ORDER: a topological order of the cone, and the
      simulation invariant established over the whole of it. *)
  Theorem cone_Qinv :
    ∃ order,
      Qinv pstep TS DS img d0 ps order ∧
      (∀ e, e ∈ order ↔ (gev_wf TS e ∧ tc (gdep3 TS DS) e r)).
  Proof.
    destruct (topo_sort Rcone (gev_enum_S TS Ucone) Rcone_acyc
                (NoDup_gev_enum_S TS Ucone)) as (order & Hnd & Hmem0 & Hord).
    have Hmem : ∀ e, e ∈ order ↔ (gev_wf TS e ∧ Ucone e).
    { intros e. rewrite Hmem0. apply elem_of_gev_enum_S. }
    have Hpre : ∀ n, (n ≤ length order)%nat → Qinv pstep TS DS img d0 ps (take n order).
    { intros n. induction n as [|n IH]; intros Hn.
      { rewrite take_0. by apply (Qinv_nil pstep TS DS img d0 ps Hwf Hnag Hps0 Hd0). }
      have [e He] : is_Some (order !! n) by apply lookup_lt_is_Some_2; lia.
      rewrite (take_S_r order n e He).
      have Hein : e ∈ order by eapply elem_of_list_lookup_2.
      have Hes : gev_wf TS e ∧ Ucone e by apply Hmem.
      eapply (Qinv_step pstep pdev TS DS img d0 ps Hwf Hwsi Hco Hwfl
                Hlf Hobl Himg Hnag Hdata Hwit (take n order) e).
      - apply IH. lia.
      - apply Hes.
      - (* not already processed *)
        intros Hin. apply elem_of_take in Hin as (i & Hi & Hilt).
        have : i = n by eapply list_relations.NoDup_lookup. lia.
      - (* every predecessor is processed — the cone is [gdep3]-closed *)
        intros e' Hd Hwf'.
        have HU' : Ucone e' by eapply Ucone_dc; [apply Hes|exact Hd|exact Hwf'].
        have He' : e' ∈ order by apply Hmem.
        apply elem_of_list_lookup in He' as (i & Hi).
        have Hlt : (i < n)%nat.
        { eapply Hord; [exact Hi|exact He|]. split_and!; [done|done|apply Hes]. }
        apply elem_of_take. by exists i. }
    have HQ := Hpre (length order) (Nat.le_refl _).
    have Hfull : take (length order) order = order by apply take_ge; lia.
    rewrite Hfull in HQ.
    exists order. split; [exact HQ|].
    intros e. rewrite Hmem. split.
    - intros [Hw HU]. apply Ucone_iff in HU. by split; [|apply HU].
    - intros [Hw Htc]. split; [done|]. by apply Ucone_iff.
  Qed.

End cone.

(* ------------------------------------------------------------------ *)
(** ** LAYER 6: THE EXHIBIT

    Two small helpers first: what a READING event does to the reader's
    [coh] at the byte it read (the observation floor of [violation]),
    and that the byte it read is a byte OF the message it read (the
    [msg_byte] conjunct). *)

Lemma aev_post_coh_read {D : Type} σ (ev : aev D) w (base : Z) tvs (jb : nat) (t : nat) (v : bv 8) :
  tvs !! jb = Some (t, v) →
  ((∃ aq lat, ae_lb ev = LLoad aq lat base tvs) ∨
   (∃ aq rl data ts, ae_lb ev = LRmw aq rl base tvs data ∧
                     ae_ts ev = Some ts)) →
  (σ t ≤ coh (aev_post σ ev w) (base + Z.of_nat jb))%nat.
Proof.
  intros Htv Hlb.
  have Hfm : (σ <$> tvs.*1) !! jb = Some (σ t)
    by rewrite !list_lookup_fmap Htv.
  destruct Hlb as [(aq & lat & Hlb)|(aq & rl & data & ts & Hlb & Hts)];
    rewrite /aev_post Hlb.
  - by apply load_post_run_coh.
  - rewrite Hts. etrans; [by apply load_post_run_coh|].
    apply ws_le_coh, store_post_run_le.
Qed.

Lemma astep_read_log_byte {P : Type} (img : image) log i (ag : wpagent P)
    l f D (base : Z) tvs (jb : nat) (t : nat) (v : bv 8) :
  astep_ok img log i ag l f D →
  ((∃ aq lat, l = LLoad aq lat base tvs) ∨
   (∃ aq rl data, l = LRmw aq rl base tvs data)) →
  tvs !! jb = Some (t, v) →
  log_byte img log t (base + Z.of_nat jb) = Some v.
Proof.
  intros Hok Hlb Htv.
  destruct Hlb as [(aq & lat & ->)|(aq & rl & data & ->)]; simpl in Hok.
  - destruct Hok as (Hro & _ & _). by destruct (Hro jb t v Htv) as (Hv & _).
  - destruct Hok as (ts & k & _ & _ & _ & Hro & _).
    by destruct (Hro jb t v Htv) as (Hv & _).
Qed.

(* ------------------------------------------------------------------ *)
(** ** LAYER 5b: THE MINIMAL-BAD-TARGET CONE IS ACYCLIC

    Stated TOP-LEVEL, with every hypothesis a named binder rather than a
    section variable: BOTH the witness route ([Section exhibit] below) and
    the archived dev-free route ([WeakRobustCone], [WeakComposeLang]) name
    these, and a section discharge would make their argument lists depend
    on which variables each proof happens to use. *)

Lemma rf_edges_ok_on_min {P D : Type} (TS : ptraces P D) (DS : pdevs D)
    (nh : nat) (b2 : gev) :
  edges_split nh TS DS → bad_min nh TS DS b2 →
  rf_edges_ok_on TS (λ e, tc (gdep3 TS DS) e b2).
Proof.
  intros Hsplit Hmin f1 f2 T ts a k' ev' Hts Hrd Hne HW HT Hlt Hev Hsome.
  destruct (Hsplit f1 f2 T ts a k' ev' Hts Hrd Hne HT Hlt Hev Hsome)
    as [Hok|Hbad]; [exact Hok|].
  by destruct (Hmin f1 f2 Hbad HW).
Qed.

(** The [gdep3]-cone predicate is closed under MUTUAL [gdep2]
    reachability, which is what the relativized walk asks of its [W]. *)
Lemma rtc_gdep2_gdep3 {P D : Type} (TS : ptraces P D) (DS : pdevs D) x y :
  rtc (gdep2 TS) x y → rtc (gdep3 TS DS) x y.
Proof.
  induction 1 as [|a b c Hab _ IH]; [done|].
  eapply rtc_l; [by apply gdep2_gdep3|exact IH].
Qed.

Lemma anc_mr {P D : Type} (TS : ptraces P D) (DS : pdevs D) (b2 : gev) :
  ∀ u x, tc (gdep3 TS DS) u b2 → rtc (gdep2 TS) u x → rtc (gdep2 TS) x u →
    tc (gdep3 TS DS) x b2.
Proof.
  intros u x HW _ Hxu. eapply tc_rtc_l; [|exact HW].
  by apply rtc_gdep2_gdep3.
Qed.

(** THE CONE'S ACYCLICITY, in two steps — the two halves of G5a: the
    relativized walk ([gdep2_acyclic_on]) kills every [gdep2] cycle
    through the cone, and the DEVICE EPOCH lifts that pointwise to
    [gdep3] ([gdep3_acyclic_at_epoch]). *)
Lemma cone_acyc2_of_min {P D : Type} (pstep : P → D → wlabel → P → D → Prop)
    (TS : ptraces P D) (DS : pdevs D) (nh : nat) (b2 : gev) :
  ptraces_wf pstep TS → ptraces_fwd_own TS → ee_ok TS →
  edges_split nh TS DS → bad_min nh TS DS b2 →
  ∀ e, tc (gdep3 TS DS) e b2 → ¬ tc (gdep2 TS) e e.
Proof.
  intros Hwf Hfo Hee Hsplit Hmin.
  apply (gdep2_acyclic_on pstep TS (λ e, tc (gdep3 TS DS) e b2) Hwf Hfo
           (rf_edges_ok_on_min TS DS nh b2 Hsplit Hmin) Hee
           (anc_mr TS DS b2)).
Qed.

Lemma cone_acyc_of_min {P D : Type} (pstep : P → D → wlabel → P → D → Prop)
    (TS : ptraces P D) (DS : pdevs D) (nh : nat) (b2 : gev) :
  ptraces_wf pstep TS → ptraces_fwd_own TS → ee_ok TS →
  ptraces_wit TS DS → dev_epoch_ok TS DS →
  edges_split nh TS DS → bad_min nh TS DS b2 →
  ∀ e, tc (gdep3 TS DS) e b2 → ¬ tc (gdep3 TS DS) e e.
Proof.
  intros Hwf Hfo Hee Hwit Hepo Hsplit Hmin e He.
  apply (gdep3_acyclic_at_epoch TS DS e Hwit Hepo).
  by apply (cone_acyc2_of_min pstep TS DS nh b2 Hwf Hfo Hee Hsplit Hmin).
Qed.

(** THE DEV-FREE READINGS (the archived instruction-atomic route): with
    an empty witness [gdep3] IS [gdep2] and the two statements are the
    pre-G5 ones, term for term. *)
Lemma tc_gdep3_nil {P D : Type} (TS : ptraces P D) (d : D) x y :
  tc (gdep3 TS (PDevs d [])) x y → tc (gdep2 TS) x y.
Proof. apply tc_subrel. intros u v. apply (gdep3_nil_gdep2 TS d). Qed.

Corollary cone_acyc_of_min_nil {P D : Type}
    (pstep : P → D → wlabel → P → D → Prop)
    (TS : ptraces P D) (d : D) (nh : nat) (b2 : gev) :
  ptraces_wf pstep TS → ptraces_fwd_own TS → ee_ok TS →
  (∀ i T k ev, pt_trs TS !! i = Some T → at_evs T !! k = Some ev →
     ae_dev ev = None) →
  edges_split nh TS (PDevs d []) → bad_min nh TS (PDevs d []) b2 →
  ∀ e, tc (gdep2 TS) e b2 → ¬ tc (gdep2 TS) e e.
Proof.
  intros Hwf Hfo Hee Hdf Hsplit Hmin e He Hc.
  eapply (cone_acyc_of_min pstep TS (PDevs d []) nh b2 Hwf Hfo Hee
            (ptraces_wit_nil TS d Hdf) (dev_epoch_ok_nil TS d) Hsplit Hmin e).
  - by apply tc_gdep2_gdep3.
  - by apply tc_gdep2_gdep3.
Qed.

Corollary cone_Qinv_nil {P D : Type} (pstep : P → D → wlabel → P → D → Prop)
    (pdev : P → wlabel → P → bool)
    (TS : ptraces P D) (img : image) (d0 : D) (ps : list P) :
  ptraces_wf pstep TS → ptraces_ws_init TS → (∀ a, co_tc TS a) →
  writes_fulfilled TS → lat_free_prog pstep → ts_oblivious pstep →
  pt_img TS = img → length (pt_trs TS) = length ps →
  (∀ p m, pt_log TS !! p = Some m → wm_data m ≠ []) →
  (∀ j T ag0, pt_trs TS !! j = Some T →
     at_ags T !! 0%nat = Some ag0 → ps !! j = Some (pa_st ag0)) →
  (∀ j T k ev, pt_trs TS !! j = Some T → at_evs T !! k = Some ev →
     ae_dev ev = None) →
  ∀ r, gev_wf TS r → ¬ tc (gdep2 TS) r r →
  (∀ e, tc (gdep2 TS) e r → ¬ tc (gdep2 TS) e e) →
  ∃ order,
    Qinv pstep TS (PDevs d0 []) img d0 ps order ∧
    (∀ e, e ∈ order ↔ (gev_wf TS e ∧ tc (gdep2 TS) e r)).
Proof.
  intros Hwf Hwsi Hco Hwfl Hlf Hobl Himg Hnag Hdata Hps0 Hdf r Hrwf Hrr Hcone.
  destruct (cone_Qinv pstep pdev TS img d0 ps Hwf Hwsi Hco Hwfl Hlf Hobl Himg
              Hnag Hdata Hps0 (PDevs d0 []) (ptraces_wit_nil TS d0 Hdf) eq_refl
              r Hrwf
              ltac:(intros Hc; apply Hrr; by eapply tc_gdep3_nil)
              ltac:(intros e He Hc; eapply (Hcone e);
                    by eapply tc_gdep3_nil))
    as (order & HQ & Hmem).
  exists order. split; [exact HQ|].
  intros e. rewrite Hmem. split; intros [H1 H2]; split; try done;
    [by eapply tc_gdep3_nil|by apply tc_gdep2_gdep3].
Qed.

Section exhibit.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pdev : P → wlabel → P → bool).
  Context (TS : ptraces P D) (img : image) (d0 : D) (ps : list P).
  Context (Hwf : ptraces_wf pstep TS).
  Context (Hwsi : ptraces_ws_init TS).
  Context (Hco : ∀ a, co_tc TS a).
  Context (Hwfl : writes_fulfilled TS).
  Context (Hlf : lat_free_prog pstep).
  Context (Hobl : ts_oblivious pstep).
  Context (Himg : pt_img TS = img).
  Context (Hnag : length (pt_trs TS) = length ps).
  Context (Hdata : ∀ p m, pt_log TS !! p = Some m → wm_data m ≠ []).
  Context (Hps0 : ∀ j T ag0, pt_trs TS !! j = Some T →
                    at_ags T !! 0%nat = Some ag0 → ps !! j = Some (pa_st ag0)).
  (** THE FABRIC (G5b): the real witness, and the NAMED per-trace residue
      G5a's rank criterion runs on. *)
  Context (DS : pdevs D).
  Context (Hwit : ptraces_wit TS DS).
  Context (Hd0 : pd_init DS = d0).
  Context (Hepo : dev_epoch_ok TS DS).
  Context (Hfo : ptraces_fwd_own TS).
  Context (Hee : ee_ok TS).
  Context (nh : nat).
  Context (Hsplit : edges_split nh TS DS).

  (** THE EXHIBIT: a minimal bad edge builds a promise-free run to a
      VIOLATING configuration — and the violation is HART-RESTRICTED
      ([WeakRobust.violation_hart]), which is what makes it refutable by
      φ: the author is [bad]'s writer and the observer is its reader,
      and [bad] bounds both by [nh]. *)
  Theorem bad_edge_violates b1 b2 :
    bad nh TS DS b1 b2 → bad_min nh TS DS b2 →
    ∃ cf, rtc (wp_pf_run pstep) (wp_init img d0 ps) cf ∧
          violation_hart cls_of pub_of nh cf.
  Proof.
    intros Hbad Hmin.
    have Hbad' := Hbad.
    destruct Hbad'
      as (Hrf & Hne & Hh1 & Hh2 & (t & m & Hts1 & Hlogm & Hak) & Hnopub).
    have Hrf' := Hrf. destruct Hrf' as (t' & a & Hts1' & Hrd2).
    have Htt : t' = t by rewrite Hts1 in Hts1'; simplify_eq.
    subst t'.
    have Hrr : ¬ tc (gdep3 TS DS) b2 b2 by apply (Hmin b1 b2 Hbad).
    have Hb2wf : gev_wf TS b2 by eapply gev_reads_wf.
    have Hb1wf : gev_wf TS b1 by eapply gev_ts_wf.
    have Htpos : (0 < t)%nat by eapply (gev_ts_pos pstep TS b1 t Hwf Hts1).
    (* ---- the cone, sorted, plus the bad read itself ---- *)
    destruct (cone_Qinv pstep pdev TS img d0 ps Hwf Hwsi Hco Hwfl Hlf Hobl Himg
                Hnag Hdata Hps0 DS Hwit Hd0 b2 Hb2wf Hrr
                (cone_acyc_of_min pstep TS DS nh b2 Hwf Hfo Hee Hwit Hepo
                   Hsplit Hmin))
      as (order & HQ & Hmem).
    have Hq : qorder TS order
      by eapply (Qinv_order pstep TS DS img d0 ps).
    have Hb2nin : b2 ∉ order.
    { intros Hin. apply Hmem in Hin as [_ Htc]. by apply Hrr. }
    have Hpre3 : ∀ e', gdep3 TS DS e' b2 → gev_wf TS e' → e' ∈ order.
    { intros e' Hd Hw'. apply Hmem. split; [done|by apply tc_once]. }
    have Hpre2 : ∀ e', gdep2 TS e' b2 → gev_wf TS e' → e' ∈ order.
    { intros e' Hd Hw'. apply Hpre3; [by apply gdep2_gdep3|done]. }
    have HQ' : Qinv pstep TS DS img d0 ps (order ++ [b2]).
    { eapply (Qinv_step pstep pdev TS DS img d0 ps Hwf Hwsi Hco Hwfl
                Hlf Hobl Himg Hnag Hdata Hwit order b2);
        [done|done|done|].
      intros e' Hd Hw'. by apply Hpre3. }
    have Hq' : qorder TS (order ++ [b2])
      by eapply (Qinv_order pstep TS DS img d0 ps).
    destruct (Qinv_run pstep TS DS img d0 ps (order ++ [b2]) HQ')
      as (cf & Hrun & Hcimg & Hclog & Hclen & Hcags & _).
    exists cf. split; [exact Hrun|].
    (* ---- the bad message and its pf position ---- *)
    have Hb1in : b1 ∈ order.
    { apply Hmem. split; [done|].
      apply tc_once, gdep2_gdep3, grf_gdep2. by exists t, a. }
    have Hb1in' : b1 ∈ order ++ [b2] by apply elem_of_app; left.
    have Htfl : t ∈ fl TS (order ++ [b2]).
    { apply elem_of_fl. by exists b1. }
    destruct (pf_log_pi pstep pdev TS ps Hwf Hnag (order ++ [b2]) t Hq' Htfl)
      as (Hp1 & Hp2 & Hp3).
    have Hmsgeq : msg_at TS t = m by apply msg_at_eq.
    destruct (gev_ts_msg pstep TS b1 t Hwf Hts1) as (base0 & data0 & kc & Hm0).
    have Hmeq : m = WMsg base0 data0 (Some b1.1) kc
      by rewrite Hlogm in Hm0; simplify_eq.
    (* ---- the reader's event and the byte it read ---- *)
    destruct (proj1 (gev_wf_bounds TS b2) Hb2wf) as (T2 & HT2 & Hklt).
    destruct (gev_reads_ev TS b2 a t T2 HT2 Hrd2) as (ev2 & Hev2 & Hinrd).
    have Hatr2 : atrace_wf pstep (pt_img TS) (pt_log TS) b2.1 T2 by apply Hwf.
    destruct (asteps_wf_step pstep (pt_img TS) (pt_log TS) b2.1 (at_ags T2)
                (at_evs T2) b2.2 ev2 Hatr2 Hev2)
      as (ag2 & ag2' & st2 & f2 & Hag2 & Hag2' & Hps2 & Hok2 & Hagn2).
    have Hshape : ∃ (base : Z) tvs (jb : nat) (v : bv 8),
        a = base + Z.of_nat jb ∧ tvs !! jb = Some (t, v) ∧
        ((∃ aq lat, ae_lb ev2 = LLoad aq lat base tvs) ∨
         (∃ aq rl data ts, ae_lb ev2 = LRmw aq rl base tvs data ∧
                           ae_ts ev2 = Some ts)).
    { remember (ae_lb ev2) as l2 eqn:Hlb2.
      destruct l2 as [|aq lat base tvs|rl base data
                     |aq rl base tvs data|pr pw sr sw];
        simpl in Hinrd;
        [by apply elem_of_nil in Hinrd| | by apply elem_of_nil in Hinrd
        | |by apply elem_of_nil in Hinrd].
      - apply elem_of_tvs_reads in Hinrd as (jb & v & Htv & ->).
        exists base, tvs, jb, v.
        split_and!; [done|done|left; by exists aq, lat].
      - apply elem_of_tvs_reads in Hinrd as (jb & v & Htv & ->).
        destruct Hok2 as (ts2 & k2 & _ & _ & _ & _ & _ & _ & _ & Hts2).
        exists base, tvs, jb, v.
        split_and!; [done|done|right; by exists aq, rl, data, ts2]. }
    destruct Hshape as (base & tvs & jb & v & Ha & Htv & Hlbsh).
    (* the message really writes that byte *)
    have Hlbv : log_byte (pt_img TS) (pt_log TS) t (base + Z.of_nat jb)
                = Some v.
    { eapply (astep_read_log_byte (pt_img TS) (pt_log TS) b2.1 ag2
                (ae_lb ev2) f2 (ae_ts ev2) base tvs jb t v Hok2); [|exact Htv].
      destruct Hlbsh as [(aq & lat & Hl)|(aq & rl & data & ts & Hl & _)];
        [left; by exists aq, lat|right; by exists aq, rl, data]. }
    have Hbyte : is_Some (msg_byte m (base + Z.of_nat jb)).
    { rewrite (log_byte_pos (pt_img TS) (pt_log TS) t m _ Htpos Hlogm) in Hlbv.
      by exists v. }
    (* ---- the reader's coherence floor ---- *)
    have Hnproc2 : nproc (order ++ [b2]) b2.1 = S b2.2.
    { rewrite (nproc_app_eq order b2).
      by rewrite (nproc_cur TS ps Hnag order b2 Hq Hb2wf Hb2nin Hpre2). }
    destruct (Hcags b2.1 T2 HT2) as (agn2 & Hagn2' & Hlk2).
    rewrite Hnproc2 (take_S_r _ _ _ Hev2) aevs_post_app in Hlk2.
    have Hcoh : (pi TS (order ++ [b2]) t ≤
                 coh (aev_post (pi TS (order ++ [b2])) ev2
                        (aevs_post (pi TS (order ++ [b2]))
                           (take b2.2 (at_evs T2)) ws_init))
                     (base + Z.of_nat jb))%nat.
    { by eapply aev_post_coh_read. }
    (* ---- the violating configuration ---- *)
    have HSp : S (pi TS (order ++ [b2]) t - 1)%nat = pi TS (order ++ [b2]) t
      by lia.
    exists (pi TS (order ++ [b2]) t - 1)%nat, m, b1.1, b2.1,
           (base + Z.of_nat jb).
    split_and!.
    - by rewrite Hclog Hp3 Hmsgeq.
    - by rewrite Hmeq.
    - (* THE AUTHOR IS A HART: [bad]'s writer conjunct, verbatim *)
      exists b1.1. by rewrite Hmeq.
    - by rewrite /cls_of Hak.
    - (* NOT PUBLISHED.  THE ALIGNMENT PAYOFF: [pub_of] is now the LOG
         predicate [wpublished], so this arm is a direct reading of
         [bad]'s no-publishing-ancestor conjunct — a [WCrel] message of
         the author at-or-past the bad message's pf position IS a
         processed publishing fulfil in the reader's ancestry.  The old
         watermark form needed the whole [w_pub_aevs_post_lt] fold
         arithmetic over the author's processed prefix; none of it is
         used here. *)
      rewrite HSp.
      intros (p' & m' & Heq & Hlogp & Hpub).
      have Hp' : p' = (pi TS (order ++ [b2]) t - 1)%nat by lia.
      subst p'. rewrite Hclog Hp3 Hmsgeq in Hlogp. injection Hlogp as <-.
      rewrite Hmeq /= in Hpub.
      destruct Hpub as (q & mq & Hle & Hq0 & Htidq & Hrelq).
      (* the publishing message names a PROCESSED timestamp … *)
      rewrite Hclog /pf_log list_lookup_fmap in Hq0.
      destruct (fl TS (order ++ [b2]) !! q) as [t0|] eqn:Hfl0;
        simpl in Hq0; [|done].
      injection Hq0 as Hq0. subst mq.
      have Ht0in : t0 ∈ fl TS (order ++ [b2])
        by eapply elem_of_list_lookup_2, Hfl0.
      (* … hence a processed FULFIL, and its author is the bad writer *)
      destruct (fl_msg pstep TS Hwf (order ++ [b2]) t0 Hq' Ht0in)
        as (ep & Hepin & Hepts & Heplog & Heptid).
      have Hepag : ep.1 = b1.1
        by rewrite Heptid in Htidq; injection Htidq.
      have Hepwf : gev_wf TS ep by eapply gev_ts_wf.
      have Hpiq : pi TS (order ++ [b2]) t0 = S q
        by eapply (pi_mem pstep pdev TS ps Hwf Hnag (order ++ [b2]) q t0 Hq' Hfl0).
      (* it is po-AT-OR-AFTER the author's own fulfil: a po-earlier
         fulfil would be π-ordered strictly BELOW the bad message *)
      have Hepge : (b1.2 ≤ ep.2)%nat.
      { destruct (decide (ep.2 < b1.2)%nat) as [Hlt|Hge]; [|lia]. exfalso.
        have Htcb1 : tc (gdep2 TS) ep b1
          by apply tc_once, gpo_gdep2; split_and!.
        have Hlt' := pi_lt_of_tc pstep pdev TS ps Hwf Hnag (order ++ [b2])
                       ep b1 t0 t Hq' Hb1in' Htcb1 Hepts Hts1.
        lia. }
      (* and it is a STRICT ANCESTOR of the reader: it is processed, and
         it is not the reader itself (different agent) *)
      have Hepord : ep ∈ order.
      { apply elem_of_app in Hepin as [Hin|Hin]; [exact Hin|].
        apply elem_of_list_singleton in Hin. exfalso.
        apply Hne. by rewrite -Hepag Hin. }
      apply Hnopub. exists ep. split_and!.
      + exact Hepag.
      + exact Hepge.
      + exists t0, (msg_at TS t0). split_and!; [exact Hepts|exact Heplog|exact Hrelq].
      + by apply Hmem.
    - done.
    - (* THE OBSERVER IS A HART: [bad]'s reader conjunct, verbatim *)
      by exists b2.1.
    - exact Hbyte.
    - rewrite /obs_flr Hlk2 /=. lia.
  Qed.

  (** …hence, under [pf_violation_free_hart], NO bad edge exists at all. *)
  Theorem no_bad_edge :
    pf_violation_free_hart cls_of pub_of nh pstep img d0 ps → bad_wf nh TS DS →
    ∀ e1 e2, ¬ bad nh TS DS e1 e2.
  Proof.
    intros Hvf Hbwf e1 e2 Hbad.
    destruct (Hbwf e1 e2 Hbad) as (f1 & f2 & Hbadf & Hmin).
    destruct (bad_edge_violates f1 f2 Hbadf Hmin) as (cf & Hrun & Hviol).
    by eapply Hvf.
  Qed.

  (** …so the per-edge premise is the full [rf_edges_ok] after all, and
      the extended graph is acyclic. *)
  Theorem gdep2_acyclic_main :
    pf_violation_free_hart cls_of pub_of nh pstep img d0 ps → bad_wf nh TS DS →
    gdep2_acyclic TS.
  Proof.
    intros Hvf Hbwf.
    eapply (gdep2_acyclic_edges_ok pstep TS Hwf Hfo); [|exact Hee].
    intros e1 e2 T ts b k' ev' Hts Hrd Hne HT Hlt Hev Hsome.
    destruct (Hsplit e1 e2 T ts b k' ev' Hts Hrd Hne HT Hlt Hev Hsome)
      as [Hok|Hbad]; [exact Hok|].
    by destruct (no_bad_edge Hvf Hbwf e1 e2 Hbad).
  Qed.

  (** …and the FABRIC-ORDERED graph is acyclic too, by G5a's rank: the
      device epoch never falls along [gdep2] (that is [dev_epoch_ok],
      plus the free [gpo] half) and strictly rises along [gdev]. *)
  Theorem gdep3_acyclic_main :
    pf_violation_free_hart cls_of pub_of nh pstep img d0 ps → bad_wf nh TS DS →
    gdep3_acyclic TS DS.
  Proof.
    intros Hvf Hbwf.
    apply (gdep3_acyclic_epoch TS DS Hwit Hepo).
    by apply gdep2_acyclic_main.
  Qed.

End exhibit.

(* ------------------------------------------------------------------ *)
(** ** LAYER 7: THE ASSEMBLED THEOREM, and W2c's transport

    The premise package, per traced bundle: the weakened per-edge split,
    the bad-SCC residue, the E-edge obligation, and the byte
    classification.  [ptraces_fwd_own], [ptraces_ws_init],
    [writes_fulfilled], [ptraces_wf] and the shape facts are DERIVED
    from the behavior, exactly as [WeakRobustSim]'s wrapper derives
    them. *)

Definition main_premises {P D : Type} (nh : nat) (TS : ptraces P D)
    (DS : pdevs D) : Prop :=
  edges_split nh TS DS ∧ bad_wf nh TS DS ∧ ee_ok TS ∧
  dev_epoch_ok TS DS ∧
  (∃ sync, ptraces_bytes_ok TS sync).

(** THE DEV-FREE READING of the package: with an empty witness the fabric
    residue is free and [gdep3] is [gdep2], so a caller that runs at a
    marker which never fires owes exactly what W2c's package asked for. *)
Lemma main_premises_nil {P D : Type} (nh : nat) (TS : ptraces P D) (d : D) :
  edges_split nh TS (PDevs d []) → bad_wf nh TS (PDevs d []) → ee_ok TS →
  (∃ sync, ptraces_bytes_ok TS sync) →
  main_premises nh TS (PDevs d []).
Proof.
  intros ????. split_and!; [done|done|done|by apply dev_epoch_ok_nil|done].
Qed.

Section main.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pdev : P → wlabel → P → bool).

  Implicit Types c : wpcfg P D.

  (** THE LAYER-1 ROBUSTNESS THEOREM.  A lat-free, timestamp-oblivious
      program whose promise-free runs never VIOLATE (the Layer-2 premise
      [pf_violation_free_hart], instantiated at [cls_of]/[pub_of] and at
      the hart count [nh]) and whose
      traced behaviors satisfy the per-edge split, the bad-SCC residue,
      the E-edge obligation and the byte classification, is ROBUST:
      every full-machine behavior is matched by a promise-free run with
      the same per-agent program states and the same flat memory.

      This is [WeakRobust.robust]'s conclusion, with the honest premises
      the M6 design pins ([WeakRobust.robust] itself is stated with
      [cls]/[pub] abstract and no bundle premises, and is not provable
      as stated — see the worklist's findings (v) and W2c (3)). *)
  Theorem robust_main nh img d0 ps c :
    pdev_ok pstep pdev →
    lat_free_prog pstep → ts_oblivious pstep →
    wp_behavior pstep img d0 ps c →
    (** THE PREMISE PACKAGE, PER TRACED BUNDLE *AND WITNESS* (G5b): the
        factorization hands out [(mid, TS, DS)] and every clause of the
        package that mentions the fabric mentions [DS]. *)
    (∀ mid TS DS,
       rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid →
       ptraces_dev_of pstep pdev TS DS mid c →
       main_premises nh TS DS) →
    pf_violation_free_hart cls_of pub_of nh pstep img d0 ps →
    ∃ cf, rtc (wp_pf_run pstep) (wp_init img d0 ps) cf ∧
          prog_of cf = prog_of c ∧ (∀ a, mem_of cf a = mem_of c a).
  Proof.
    intros Hpok Hlf Hobl Hb Hprem Hvf.
    destruct (wp_behavior_fulfil_once_dev pstep pdev img d0 ps c Hpok Hlf Hb)
      as (mid & TS & DS & Hprom & Hofd & Hnp & Hacct).
    have Hwit : ptraces_wit TS DS by eapply ptraces_dev_of_wit.
    have Hdinit : pd_init DS = pc_dev mid by destruct Hofd as (_ & ? & _).
    destruct (Hprem mid TS DS Hprom Hofd)
      as (Hsplit & Hbwf & Hee & Hepo & (sync & Hbytes)).
    destruct Hofd as (Hof & _).
    (* the derived bundle facts — as in [wp_behavior_robust] *)
    have Hwf : ptraces_wf pstep TS by eapply ptraces_of_wf.
    have Hla : log_authored (pc_log mid).
    { eapply log_authored_promise_run;
        [apply (log_authored_init img d0 ps)|exact Hprom]. }
    have Hwfl : writes_fulfilled TS
      by eapply (ptraces_of_writes_fulfilled pstep TS mid c).
    have Hlne : log_ne (pc_log mid).
    { eapply log_ne_promise_run; [apply (log_ne_init img d0 ps)|exact Hprom]. }
    have Hinit : cfg_ws_init mid.
    { eapply cfg_ws_init_promise_run;
        [apply (cfg_ws_init_init img d0 ps)|exact Hprom]. }
    have Hwsi : ptraces_ws_init TS by eapply (ptraces_of_ws_init pstep TS mid c).
    have Hfo : ptraces_fwd_own TS by eapply (ptraces_of_fwd_own pstep TS mid c).
    have Hco : ∀ a, co_tc TS a
      by eapply (co_serialized_pkg pstep pdev TS sync Hwf Hwfl Hbytes).
    destruct (promise_run_shape (wp_init img d0 ps) mid Hprom)
      as (Hpimg & Hplen & Hpdev & Hpst).
    have Hof' := Hof.
    destruct Hof' as (Himg0 & Hlog0 & Hlent & Hwft & Hfst & Hlst
                      & Hclogc & Hcimgc & Hclenc).
    have Himg1 : pt_img TS = img by rewrite Himg0 Hpimg.
    have Hlen1 : length (pt_trs TS) = length ps.
    { by rewrite Hlent Hplen /wp_init /= length_map. }
    have Hdata1 : ∀ p m, pt_log TS !! p = Some m → wm_data m ≠ [].
    { rewrite Hlog0. exact Hlne. }
    have Hps1 : ∀ j T ag0, pt_trs TS !! j = Some T →
                  at_ags T !! 0%nat = Some ag0 → ps !! j = Some (pa_st ag0).
    { intros j T ag0 HT Hag0.
      have Hmid : pc_ags mid !! j = Some ag0 by rewrite -(Hfst j T HT).
      destruct (Hpst j ag0 Hmid) as (ag & Hag & Hst).
      rewrite /wp_init /= list_lookup_fmap in Hag.
      destruct (ps !! j) as [p0|] eqn:Hp0; simpl in Hag; [|done].
      injection Hag as <-. by rewrite Hst. }
    have Hd01 : pd_init DS = d0 by rewrite Hdinit Hpdev.
    (* THE ACYCLICITY: the exhibit rules out every bad edge, so the
       per-edge split IS [rf_edges_ok] and the W2b walk closes; the
       DEVICE EPOCH (G5a) then lifts it to the fabric-ordered graph *)
    have Hacyc : gdep3_acyclic TS DS.
    { eapply (gdep3_acyclic_main pstep pdev TS img d0 ps Hwf Hwsi Hco Hwfl Hlf
                Hobl Himg1 Hlen1 Hdata1 Hps1 DS Hwit Hd01 Hepo Hfo Hee nh
                Hsplit Hvf Hbwf). }
    eapply (sim_full pstep pdev TS DS img d0 ps Hwf Hwsi Hco Hwfl
              Hlf Hobl Himg1 Hlen1 Hdata1 Hps1 Hwit Hd01 c Hacyc).
    - by rewrite Himg0 Hcimgc.
    - by rewrite Hlog0 Hclogc.
    - by rewrite Hclenc Hplen /wp_init /= length_map.
    - exact Hlst.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** W2c PROPER: the transport, over COMPLETABLE prefixes

      The full machine is never [wpstep]-stuck, so the statement W5
      consumes is not about stuckness but about the OBSERVABLES of
      completable prefixes: a prefix that can still drain its promises
      has a completion whose program states and flat memory a
      promise-free run reproduces. *)

  Definition completable img d0 ps c : Prop :=
    rtc (wpstep pstep) (wp_init img d0 ps) c ∧
    ∃ cend, rtc (wpstep pstep) c cend ∧ no_promises cend.

  Corollary robust_transport nh img d0 ps c :
    pdev_ok pstep pdev →
    lat_free_prog pstep → ts_oblivious pstep →
    completable img d0 ps c →
    (∀ cend mid TS DS,
       wp_behavior pstep img d0 ps cend →
       rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid →
       ptraces_dev_of pstep pdev TS DS mid cend →
       main_premises nh TS DS) →
    pf_violation_free_hart cls_of pub_of nh pstep img d0 ps →
    ∃ cend cf,
      rtc (wpstep pstep) c cend ∧ no_promises cend ∧
      rtc (wp_pf_run pstep) (wp_init img d0 ps) cf ∧
      prog_of cf = prog_of cend ∧ (∀ a, mem_of cf a = mem_of cend a).
  Proof.
    intros Hpok Hlf Hobl (Hpre & cend & Hrest & Hnp) Hprem Hvf.
    have Hbeh : wp_behavior pstep img d0 ps cend.
    { split; [by eapply rtc_transitive|exact Hnp]. }
    destruct (robust_main nh img d0 ps cend Hpok Hlf Hobl Hbeh
                (λ mid TS DS, Hprem cend mid TS DS Hbeh) Hvf)
      as (cf & Hrun & Hprog & Hmem).
    by exists cend, cf.
  Qed.

End main.

(* ------------------------------------------------------------------ *)
(** ** What W3/W5 inherit from this file

    - [cls_of] / [pub_of]: the instantiation of [WeakRobust]'s two
      Layer-2 parameters (D-M6-6's [wm_ak] and [w_pub]).  φ's obligation
      on the Iris side is [pf_violation_free_hart cls_of pub_of nh],
      nothing
      else — the trace-global premises are discharged per-site/static
      (D-M6-8).

    - [bad] / [edges_split] / [bad_wf]: the weakened per-edge premise
      and the honest residue.  W3's writer-discipline export should
      target [edges_split] (not [rf_edges_ok]): a racy read that the
      kernel does NOT discipline is admissible as long as it is [bad],
      because [bad_edge_violates] turns it into a φ-refutable
      promise-free run.

    - [bad_edge_violates]: the exhibit, as a standalone theorem — a
      minimal bad edge yields a REAL [wp_pf_run] reaching a
      [violation_hart nh] (hart author, hart observer — both bounds are
      [bad]'s own).  This is the only place Layer 1 hands Layer 2 a
      concrete violating configuration, and it is the sole consumer of
      [pf_violation_free_hart].

    - [gdep2_acyclic_on] / [rf_edges_ok_on]: the relativized walk, for
      any future argument that needs acyclicity only along a cone.

    - [robust_main] and [robust_transport]: the assembled theorem and
      W2c's completable-prefix corollary. *)
