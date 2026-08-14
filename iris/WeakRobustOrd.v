(** * WeakRobustOrd.v — the EXTENDED dependency graph D⁺ = gdep ∪ gE and
      its SUBSET topological sort (M6 W2b, design items (ii) and (iv))

    THE PROBLEM THIS FILE SOLVES.  W2b's delay simulation replays a
    traced full-machine behavior as a promise-free run whose log is a
    permutation π of the behavior's timestamps, processing the events in
    a topological order of the dependency graph.  The 2026-08-12 design
    revision recorded a machine-level COUNTEREXAMPLE ("floor inversion")
    showing that a toposort of [gdep = gpo ∪ grf] alone is NOT enough:
    a stale write with a HIGH timestamp may be sorted BELOW an acquired
    message, and then it sits inside the reader's promise-free floor
    window and BLOCKS the very read the behavior performed.

    The fix is to hand the sort a BIGGER graph.  For every read [r] of
    byte [a] the behavior's read floor is
    [F(r,a) = max (load_vpre, coh a)] at [r]'s pre-state; a byte-[a]
    write with timestamp [t̂ > F(r,a)] is one [r] "stale-passes".  The
    FLOOR-PROTECTION edges [gE] order the fulfil of every LEAF of that
    floor strictly before the fulfil of every stale-passed write.  In
    the promise-free run this is exactly what keeps the transported
    window [(π ts, pf-floor]] clean, so [readable] transports —
    whichever side of [r] the stale write is processed on.

    Leaves, not maxima: π is not monotone, so [π (max L) ≠ max (π <$> L)]
    and no statement about the floor as a NUMBER transports.
    [WeakRobustProv.v] computes the floor as a LEAF LIST
    ([lfloor S aq a], valuated by [lval σ]) so that a floor bound is a
    POINTWISE statement about σ on leaves — and pointwise statements are
    exactly what a topological order can enforce.  That is why the E
    edges are indexed by a leaf [t*] rather than by the floor itself.

    THE FOUR DELIVERABLES.

    (1) TRACE-PREFIX LEAF STATES ([pre_lstate]).  The leaf state of the
        prefix of [e]'s trace strictly before [e] — computable from the
        bundle alone.  [pre_lstate_lrel] is the bridge to the REAL
        [wstate] of the behavior: for a wf bundle whose traces start
        from [ws_init] ([ptraces_ws_init], which [ptraces_of_ws_init]
        derives from [cfg_ws_init mid]), [lrel id] relates the two.
        Proof: [asteps_ws_fold] says the behavior's [k]-th agent record
        IS [aevs_post id (take k evs) ws_init], and
        [lrel_aevs_post_id] relates that fold to the leaf fold.

    (2) READ FLOORS and the E EDGES.  [rd_leaves TS r a] is the floor
        leaf list of read [r] at byte [a] — GUARDED on the label being a
        [LLoad]/[LRmw], so a non-read event has NO floor (and hence
        generates no edges) even though [lb_aq] and [lfloor] are total.
        [rd_floor] is its [id]-valuation, i.e. the behavior's own floor
        number.  [gE] is the design's edge relation, [gdep2] the
        extended graph.

    (3) DECIDABILITY of [gE] (hence of [gdep2]).  Every existential is
        bounded: [r] ranges over the concrete list [gev_enum TS] (via
        [gE_at], the fixed-[r] slice, plus [gE_at_wf]); given [r] the
        label [l] is ONE [option]; [(a, ts)] ranges over the concrete
        list [lb_reads l]; and [t*]/[t̂] are pinned by [gev_ts TS e1] /
        [gev_ts TS e2], again single [option]s.  So the sort over
        [gdep2] is CONSTRUCTIVE, like [WeakRobustLin]'s.

    (4) THE SUBSET TOPOSORT.  Design item (iv) needs the induction to
        run not on all events but on a DOWNWARD-CLOSED subset [S] (the
        ancestor closure of a minimal bad edge).  [gdep2_toposort_S]
        sorts the filtered carrier; [toposort_ind_S] is the induction
        principle, whose predecessor-done step is where downward
        closure ([dc]) is spent: a [gdep2]-predecessor of an event of
        [S] is itself in [S], hence in the carrier, hence EARLIER.
        [S := gev_wf TS] recovers the full case ([dc_full]).

    DELTAS FROM THE SPEC (all recorded deliberately):

    - The E edge's "[e2] writes byte [a] at [t̂]" conjunct
      [∃ m, pt_log TS !! (t̂ - 1) = Some m ∧ is_Some (msg_byte m a)] is
      given the NAME [msg_writes TS t̂ a] (definitionally the same term)
      so that it carries its own [Decision] instance.  Together with
      the [gev_ts TS e2 = Some t̂] conjunct this is exactly
      [WeakRobustSer.writes_b TS a e2 t̂]; that file is NOT imported —
      the two conjuncts are kept apart because the decidability staging
      wants [t̂] pinned by [gev_ts] FIRST.
    - [gE] is spelled as [∃ r, gE_at TS r e1 e2] with [gE_at] the
      fixed-[r] slice.  That is the same term as the spec's flat
      [∃ r l a ts t* t̂, …]; the split exists only so the decidability
      proof can be staged (see [gE_at_dec] then [gE_dec]).
    - [dc] keeps the [gev_wf TS e'] premise of the spec even though
      [gdep2_wf] supplies it: it makes [dc] trivially provable for
      candidate subsets without unfolding [gdep2], and every consumer
      here has the [gev_wf] fact in hand anyway.
    - [sub_ok TS S := dc TS S ∧ (∀ e, S e → gev_wf TS e)] is a plain
      [Prop] pair; the [Decision] side condition stays a TYPECLASS
      CONTEXT (a [Decision] inside a [Prop] record would be unusable).

    DEPENDENCY-FREE like its parents: stdpp only, no Iris, no Sail.
    [WeakAxiomatic] is imported FIRST so that [WeakPromise]'s [wlabel]
    constructors shadow its [lbl] ones. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakAxiomatic.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakRobustTrace
                            WeakRobustGraph WeakRobust WeakRobustProv
                            WeakRobustAcyc WeakRobustLin.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
Section ord.
  Context {P D : Type}.

  Implicit Types TS : ptraces P D.
  Implicit Types e : gev.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 1: TRACE-PREFIX LEAF STATES *)

  (** The leaf state of [e]'s trace STRICTLY BEFORE [e].  For an
      ill-formed [e] this is [linit] (junk, never consumed). *)
  Definition pre_lstate TS e : lstate :=
    match pt_trs TS !! e.1 with
    | Some T => laevs_post (take e.2 (at_evs T)) linit
    | None => linit
    end.

  Lemma pre_lstate_tr TS e T :
    pt_trs TS !! e.1 = Some T →
    pre_lstate TS e = laevs_post (take e.2 (at_evs T)) linit.
  Proof. rewrite /pre_lstate. by intros ->. Qed.

  (** Every leaf of a prefix leaf state is a timestamp SOME event of
      that prefix read or fulfilled — [laevs_leaves_occur] relocated to
      the bundle vocabulary.  (The well-definedness the E edges need:
      an edge source is always a graph node.) *)
  Lemma pre_lstate_leaf_occurs TS e T t :
    pt_trs TS !! e.1 = Some T → lstate_leaf (pre_lstate TS e) t →
    ev_ts_occurs (take e.2 (at_evs T)) t.
  Proof.
    intros HT Hl. rewrite (pre_lstate_tr TS e T HT) in Hl.
    by apply laevs_leaves_occur.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 2: READ FLOORS and the E EDGES *)

  (** The floor-leaf list of read [r] at byte [a].  GUARDED on the
      label: a non-read event has no floor, hence generates no edges.
      (Without the guard [lfloor] would hand a store or a fence the
      list [l_vrNew ++ lcoh a], which has nothing to do with reading.) *)
  Definition rd_leaves TS (r : gev) (a : Z) : list nat :=
    match gev_lb TS r with
    | Some l =>
        match l with
        | LLoad _ _ _ _ | LRmw _ _ _ _ _ => lfloor (pre_lstate TS r) (lb_aq l) a
        | _ => []
        end
    | None => []
    end.

  (** The behavior's OWN floor number at that read: the [id]-valuation
      of the leaf list.  ([lrel_floor] at σ = [id] is what identifies
      it with [max (load_vpre, coh a)] of the real [wstate] — see
      [rd_floor_ws] below.) *)
  Definition rd_floor TS (r : gev) (a : Z) : nat := lval id (rd_leaves TS r a).

  Lemma rd_leaves_wf TS r a t : t ∈ rd_leaves TS r a → gev_wf TS r.
  Proof.
    rewrite /rd_leaves. destruct (gev_lb TS r) as [l|] eqn:Hl;
      [|by intros ?%elem_of_nil].
    intros _. by eapply gev_lb_wf.
  Qed.

  (** "[t] is a write of byte [a] at the log position timestamp [t]
      names" — the [gev_ts]-free half of [WeakRobustSer.writes_b]. *)
  Definition msg_writes TS (t : nat) (a : Z) : Prop :=
    ∃ m, pt_log TS !! (t - 1)%nat = Some m ∧ is_Some (msg_byte m a).

  Global Instance msg_writes_dec TS t a : Decision (msg_writes TS t a).
  Proof.
    rewrite /msg_writes.
    destruct (pt_log TS !! (t - 1)%nat) as [m|] eqn:Hm;
      [|by right; intros (m' & Hm' & _)].
    destruct (msg_byte m a) as [b|] eqn:Hb.
    - left. exists m. split; [done|]. rewrite Hb. by eexists.
    - right. intros (m' & Hm' & Hs). simplify_eq.
      rewrite Hb in Hs. by destruct Hs.
  Qed.

  (** THE FLOOR-PROTECTION EDGE, for a FIXED witnessing read [r]:
      [e1] fulfils a LEAF [t*] of [r]'s floor at byte [a], [e2] fulfils
      a byte-[a] write [t̂] STRICTLY ABOVE that floor (so [r]
      "stale-passes" [t̂]).  The edge orders [e1] before [e2]. *)
  Definition gE_at TS (r e1 e2 : gev) : Prop :=
    ∃ l a ts tstar that,
      gev_lb TS r = Some l ∧ (a, ts) ∈ lb_reads l ∧
      tstar ∈ rd_leaves TS r a ∧ (0 < tstar)%nat ∧
      gev_ts TS e1 = Some tstar ∧
      gev_ts TS e2 = Some that ∧
      msg_writes TS that a ∧
      (rd_floor TS r a < that)%nat.

  Definition gE TS (e1 e2 : gev) : Prop := ∃ r, gE_at TS r e1 e2.

  (** THE EXTENDED DEPENDENCY GRAPH D⁺. *)
  Definition gdep2 TS (e1 e2 : gev) : Prop := gdep TS e1 e2 ∨ gE TS e1 e2.

  Definition gdep2_acyclic TS : Prop := ∀ e, ¬ tc (gdep2 TS) e e.

  Lemma gdep_gdep2 TS e1 e2 : gdep TS e1 e2 → gdep2 TS e1 e2.
  Proof. by left. Qed.
  Lemma gE_gdep2 TS e1 e2 : gE TS e1 e2 → gdep2 TS e1 e2.
  Proof. by right. Qed.
  Lemma gpo_gdep2 TS e1 e2 : gpo TS e1 e2 → gdep2 TS e1 e2.
  Proof. intros ?. by do 2 left. Qed.
  Lemma grf_gdep2 TS e1 e2 : grf TS e1 e2 → gdep2 TS e1 e2.
  Proof. intros ?. left. by right. Qed.

  Lemma tc_gdep_gdep2 TS x y : tc (gdep TS) x y → tc (gdep2 TS) x y.
  Proof.
    induction 1 as [x y Hxy|x y z Hxy _ IH].
    - by apply tc_once, gdep_gdep2.
    - eapply tc_l; [by apply gdep_gdep2|exact IH].
  Qed.

  Lemma gdep2_acyclic_gdep TS : gdep2_acyclic TS → gdep_acyclic TS.
  Proof. intros Hac e Hc. by apply (Hac e), tc_gdep_gdep2. Qed.

  (** The witnessing read of an E edge is a real event. *)
  Lemma gE_at_wf_r TS r e1 e2 : gE_at TS r e1 e2 → gev_wf TS r.
  Proof.
    intros (l & a & ts & tstar & that & Hl & _). by eapply gev_lb_wf.
  Qed.

  Lemma gE_wf TS e1 e2 : gE TS e1 e2 → gev_wf TS e1 ∧ gev_wf TS e2.
  Proof.
    intros (r & l & a & ts & tstar & that & _ & _ & _ & _ & H1 & H2 & _).
    split; by eapply gev_ts_wf.
  Qed.

  Lemma gdep2_wf TS e1 e2 : gdep2 TS e1 e2 → gev_wf TS e1 ∧ gev_wf TS e2.
  Proof. intros [Hd|HE]; [by apply gdep_wf|by apply gE_wf]. Qed.

  (** EVERY E EDGE IS TIMESTAMP-INCREASING: the source's timestamp is a
      floor LEAF (so at most the floor, by [lval_ge] at σ = [id]) and
      the target's is strictly ABOVE the floor. *)
  Lemma gE_ts_lt TS e1 e2 t1 t2 :
    gE TS e1 e2 → gev_ts TS e1 = Some t1 → gev_ts TS e2 = Some t2 →
    (t1 < t2)%nat.
  Proof.
    intros (r & l & a & ts & tstar & that & _ & _ & Hleaf & _ & H1 & H2 & _ & Hlt)
           Ht1 Ht2.
    rewrite H1 in Ht1. rewrite H2 in Ht2. simplify_eq.
    have Hle : (t1 ≤ rd_floor TS r a)%nat by apply (lval_ge id _ _ Hleaf).
    lia.
  Qed.

  (** The packaged existential form, for consumers that only have the
      edge and not the two timestamps. *)
  Lemma gE_ts_lt_ex TS e1 e2 :
    gE TS e1 e2 → ∃ t1 t2, gev_ts TS e1 = Some t1 ∧ gev_ts TS e2 = Some t2 ∧
                           (t1 < t2)%nat.
  Proof.
    intros HE. have HE' := HE.
    destruct HE' as (r & l & a & ts & tstar & that & _ & _ & _ & _ & H1 & H2 & _).
    exists tstar, that. split_and!; [done|done|by eapply gE_ts_lt].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 3: DECIDABILITY *)

  (** Fixed [r]: the label is one [option], the two timestamps are
      pinned by [gev_ts], and [(a, ts)] ranges over the CONCRETE list
      [lb_reads l] — so the relation reflects into an [Exists] over it,
      exactly as [WeakRobustLin]'s [grf_dec] does. *)
  Global Instance gE_at_dec TS r e1 e2 : Decision (gE_at TS r e1 e2).
  Proof.
    rewrite /gE_at.
    destruct (gev_lb TS r) as [l|] eqn:Hl;
      [|by right; intros (l' & ? & ? & ? & ? & Hc & _)].
    destruct (gev_ts TS e1) as [tstar|] eqn:Ht1;
      [|by right; intros (? & ? & ? & ? & ? & _ & _ & _ & _ & Hc & _)].
    destruct (gev_ts TS e2) as [that|] eqn:Ht2;
      [|by right; intros (? & ? & ? & ? & ? & _ & _ & _ & _ & _ & Hc & _)].
    destruct (decide ((0 < tstar)%nat)) as [Hpos|Hpos];
      [|right; intros (? & ? & ? & tstar' & ? & _ & _ & _ & Hc & Heq & _);
        simplify_eq; lia].
    destruct (decide (Exists (λ p : Z * nat,
                        tstar ∈ rd_leaves TS r p.1 ∧ msg_writes TS that p.1 ∧
                        (rd_floor TS r p.1 < that)%nat) (lb_reads l)))
      as [Hex|Hex].
    - left. apply list_relations.Exists_exists in Hex
        as ([a ts] & Hin & Hleaf & Hw & Hlt); simpl in Hleaf, Hw, Hlt.
      by exists l, a, ts, tstar, that.
    - right. intros (l' & a & ts & tstar' & that' & Hl' & Hin & Hleaf & _ &
                     Heq1 & Heq2 & Hw & Hlt).
      simplify_eq.
      apply Hex, list_relations.Exists_exists. exists (a, ts). by split.
  Qed.

  Global Instance gE_dec TS e1 e2 : Decision (gE TS e1 e2).
  Proof.
    destruct (decide (Exists (λ r, gE_at TS r e1 e2) (gev_enum TS)))
      as [Hex|Hex].
    - left. apply list_relations.Exists_exists in Hex as (r & _ & Hr).
      by exists r.
    - right. intros (r & Hr). apply Hex, list_relations.Exists_exists.
      exists r. split; [|done]. apply elem_of_gev_enum. by eapply gE_at_wf_r.
  Qed.

  Global Instance gdep2_dec TS e1 e2 : Decision (gdep2 TS e1 e2).
  Proof. rewrite /gdep2. apply _. Qed.

  Global Instance gE_rel_dec TS : RelDecision (gE TS).
  Proof. intros e1 e2. apply _. Qed.
  Global Instance gdep2_rel_dec TS : RelDecision (gdep2 TS).
  Proof. intros e1 e2. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 4, part 1: the SUBSET vocabulary *)

  (** DOWNWARD CLOSURE under the extended graph: a [gdep2]-predecessor
      of an event of [S] is itself in [S]. *)
  Definition dc TS (S : gev → Prop) : Prop :=
    ∀ e e', S e → gdep2 TS e' e → gev_wf TS e' → S e'.

  (** A WELL-FORMED SUBSET: downward closed, and made of real events.
      (The [Decision] side condition is a typeclass context, not a
      field — see the header.) *)
  Definition sub_ok TS (S : gev → Prop) : Prop :=
    dc TS S ∧ (∀ e, S e → gev_wf TS e).

  (** THE FULL INSTANCE: [gev_wf] itself is downward closed. *)
  Lemma dc_full TS : dc TS (gev_wf TS).
  Proof. intros e e' _ _ Hwf. exact Hwf. Qed.

  Lemma sub_ok_full TS : sub_ok TS (gev_wf TS).
  Proof. split; [apply dc_full|done]. Qed.

  (** The packaged conclusion of the subset sort. *)
  Definition topo_order_S TS (S : gev → Prop) (order : list gev) : Prop :=
    NoDup order ∧
    (∀ e, e ∈ order ↔ (gev_wf TS e ∧ S e)) ∧
    (∀ x y i j, order !! i = Some x → order !! j = Some y → gdep2 TS x y →
                (i < j)%nat).

End ord.

(* ------------------------------------------------------------------ *)
(** ** DELIVERABLE 4, part 2: THE SUBSET TOPOSORT

    [S] is a section variable so the statements read cleanly; note it
    SHADOWS the [nat] successor inside this section, so nothing below
    ever writes [S n] (the constructor is still reached through lemma
    names like [take_S_r]). *)
Section subset.
  Context {P D : Type}.
  Context (TS : ptraces P D).
  Context (S : gev → Prop).
  Context `{!∀ e, Decision (S e)}.

  (** THE CARRIER: the wf events satisfying [S]. *)
  Definition gev_enum_S : list gev := filter S (gev_enum TS).

  Lemma elem_of_gev_enum_S e : e ∈ gev_enum_S ↔ (gev_wf TS e ∧ S e).
  Proof.
    rewrite /gev_enum_S elem_of_list_filter elem_of_gev_enum. tauto.
  Qed.

  Lemma NoDup_gev_enum_S : NoDup gev_enum_S.
  Proof. apply list_relations.NoDup_filter, NoDup_gev_enum. Qed.

  (** THE SORT.  Full acyclicity is inherited by the restriction, so
      [WeakRobustLin]'s generic [topo_sort] applies verbatim with
      [R := gdep2 TS] and the filtered carrier. *)
  Theorem gdep2_toposort_S :
    gdep2_acyclic TS →
    ∃ order : list gev,
      NoDup order ∧
      (∀ e, e ∈ order ↔ (gev_wf TS e ∧ S e)) ∧
      (∀ x y i j, order !! i = Some x → order !! j = Some y → gdep2 TS x y →
                  (i < j)%nat).
  Proof.
    intros Hacyc.
    destruct (topo_sort (gdep2 TS) gev_enum_S Hacyc NoDup_gev_enum_S)
      as (order & Hnd & Hmem & Hord).
    exists order. split_and!; [done| |].
    - intros e. rewrite Hmem. apply elem_of_gev_enum_S.
    - intros x y i j Hi Hj Hd. by eapply Hord.
  Qed.

  Corollary gdep2_toposort_S_pack :
    gdep2_acyclic TS → ∃ order, topo_order_S TS S order.
  Proof.
    intros Hacyc. destruct gdep2_toposort_S as (order & ? & ? & ?); [done|].
    exists order. by split_and!.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Prefix closure — where DOWNWARD CLOSURE is spent *)

  Lemma topo_order_S_wf order e :
    topo_order_S TS S order → e ∈ order → gev_wf TS e ∧ S e.
  Proof. intros (_ & Hmem & _) He. by apply Hmem. Qed.

  Lemma topo_order_S_index_unique order i j e :
    topo_order_S TS S order → order !! i = Some e → order !! j = Some e → i = j.
  Proof. intros (Hnd & _ & _) Hi Hj. by eapply list_relations.NoDup_lookup. Qed.

  (** No [gdep2] edge points from OUTSIDE a prefix INTO it — provided
      the source is a real event, which [gdep2_wf] always gives. *)
  Lemma topo_prefix_closed_S order n x y :
    topo_order_S TS S order → dc TS S →
    gdep2 TS x y → y ∈ take n order → x ∈ take n order.
  Proof.
    intros Ho Hdc Hd Hy. have Ho' := Ho. destruct Ho' as (Hnd & Hmem & Hord).
    apply elem_of_take in Hy as (j & Hj & Hjn).
    have Hyin : y ∈ order by eapply elem_of_list_lookup_2.
    have Hys : gev_wf TS y ∧ S y by apply Hmem.
    have Hxwf : gev_wf TS x by apply (gdep2_wf TS x y Hd).
    have Hxs : S x by eapply Hdc; [apply Hys|exact Hd|exact Hxwf].
    have Hx : x ∈ order by apply Hmem.
    apply elem_of_list_lookup in Hx as (i & Hi).
    have Hlt : (i < j)%nat by eapply Hord.
    apply elem_of_take. exists i. split; [done|lia].
  Qed.

  (** The same fact at the exact step the induction takes. *)
  Lemma topo_pred_done_S order n e :
    topo_order_S TS S order → dc TS S → order !! n = Some e →
    ∀ e', gdep2 TS e' e → gev_wf TS e' → e' ∈ take n order.
  Proof.
    intros Ho Hdc Hn e' Hd Hwf'. have Ho' := Ho.
    destruct Ho' as (Hnd & Hmem & Hord).
    have Hein : e ∈ order by eapply elem_of_list_lookup_2.
    have Hes : gev_wf TS e ∧ S e by apply Hmem.
    have Hs' : S e' by eapply Hdc; [apply Hes|exact Hd|exact Hwf'].
    have He' : e' ∈ order by apply Hmem.
    apply elem_of_list_lookup in He' as (i & Hi).
    have Hlt : (i < n)%nat by eapply Hord.
    apply elem_of_take. exists i. by split.
  Qed.

  Lemma topo_not_in_prefix_S order n e :
    topo_order_S TS S order → order !! n = Some e → e ∉ take n order.
  Proof.
    intros (Hnd & _ & _) Hn He.
    apply elem_of_take in He as (i & Hi & Hin).
    have Heq : i = n by eapply list_relations.NoDup_lookup. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** PER-AGENT MONOTONICITY in the subset order

      [gpo] edges are [gdep2] edges, so [WeakRobustLin]'s
      [topo_agent_mono] carries over verbatim — with the [gev_wf] side
      conditions supplied by membership in the (filtered) order. *)

  Lemma topo_agent_lt_S order i j x y :
    topo_order_S TS S order → order !! i = Some x → order !! j = Some y →
    x.1 = y.1 → (x.2 < y.2)%nat → (i < j)%nat.
  Proof.
    intros (Hnd & Hmem & Hord) Hi Hj Hag Hk.
    eapply Hord; [exact Hi|exact Hj|]. apply gpo_gdep2.
    split_and!; [done|done| |].
    - apply (Hmem x). by eapply elem_of_list_lookup_2.
    - apply (Hmem y). by eapply elem_of_list_lookup_2.
  Qed.

  Lemma topo_agent_mono_S order i j x y :
    topo_order_S TS S order → order !! i = Some x → order !! j = Some y →
    x.1 = y.1 → ((i < j)%nat ↔ (x.2 < y.2)%nat).
  Proof.
    intros Ho Hi Hj Hag. split; [|by eapply topo_agent_lt_S].
    intros Hij.
    destruct (Nat.lt_trichotomy x.2 y.2) as [Hlt|[Heq|Hgt]]; [done| |].
    - exfalso.
      have Hxy : x = y.
      { destruct x as [a1 k1], y as [a2 k2]. simpl in Hag, Heq. by subst. }
      subst y. have : i = j by eapply topo_order_S_index_unique. lia.
    - exfalso.
      have Hji : (j < i)%nat by eapply (topo_agent_lt_S order j i y x).
      lia.
  Qed.

  (** PER-AGENT PREFIX CLOSURE of the SUBSET itself: [S] contains the
      whole trace prefix of any event it contains (the [gpo] edge is a
      [gdep2] edge). *)
  Lemma dc_agent_prefix j k k' :
    dc TS S → S (j, k) → gev_wf TS (j, k) → gev_wf TS (j, k') →
    (k' < k)%nat → S (j, k').
  Proof.
    intros Hdc HS Hwf Hwf' Hlt. eapply Hdc; [exact HS| |exact Hwf'].
    apply gpo_gdep2. by split_and!.
  Qed.

  Lemma sub_ok_agent_prefix j k k' :
    sub_ok TS S → S (j, k) → gev_wf TS (j, k') → (k' < k)%nat → S (j, k').
  Proof.
    intros [Hdc Hsub] HS Hwf' Hlt.
    eapply dc_agent_prefix; [exact Hdc|exact HS|by apply Hsub|exact Hwf'|exact Hlt].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE INDUCTION PRINCIPLE — the interface W2b's simulation
         consumes on a downward-closed subset *)

  Lemma toposort_ind_S (Q : list gev → Prop) :
    gdep2_acyclic TS → dc TS S →
    Q [] →
    (∀ done e,
       Q done →
       gev_wf TS e → S e → e ∉ done →
       (∀ e', gdep2 TS e' e → gev_wf TS e' → e' ∈ done) →
       Q (done ++ [e])) →
    ∃ order,
      Q order ∧
      NoDup order ∧
      (∀ e, e ∈ order ↔ (gev_wf TS e ∧ S e)) ∧
      (∀ x y i j, order !! i = Some x → order !! j = Some y → gdep2 TS x y →
                  (i < j)%nat).
  Proof.
    intros Hacyc Hdc Hnil Hstep.
    destruct (gdep2_toposort_S_pack Hacyc) as (order & Ho).
    (* The induction is BOUNDED by the order's length (rather than
       [WeakRobustLin.toposort_ind]'s "past the end" case) — the bound
       makes the step's lookup total, and it is what keeps this proof
       from ever having to WRITE the successor constructor, which the
       section variable [S] shadows. *)
    have Hpre : ∀ n, (n ≤ length order)%nat → Q (take n order).
    { intros n. induction n as [|n IH]; intros Hn; [by rewrite take_0|].
      have [e He] : is_Some (order !! n) by apply lookup_lt_is_Some_2; lia.
      rewrite (take_S_r order n e He).
      have Hes : gev_wf TS e ∧ S e.
      { eapply topo_order_S_wf; [exact Ho|by eapply elem_of_list_lookup_2]. }
      apply Hstep.
      - apply IH. lia.
      - apply Hes.
      - apply Hes.
      - by eapply topo_not_in_prefix_S.
      - intros e' Hd Hwf'. by eapply topo_pred_done_S. }
    exists order. destruct Ho as (Hnd & Hmem & Hord).
    split_and!; [|done|done|done].
    have Hfull : take (length order) order = order by apply take_ge; lia.
    have HQ := Hpre (length order) (Nat.le_refl _). by rewrite Hfull in HQ.
  Qed.

End subset.

Global Arguments gev_enum_S {P D} _ _ {_}.

(* ------------------------------------------------------------------ *)
(** ** THE FULL CASE, as ONE instantiation

    [S := gev_wf TS] is downward closed ([dc_full]) and its [Decision]
    instance is [WeakRobustLin.gev_wf_dec], so the whole-event-set sort
    and induction are corollaries — no separate development. *)

Corollary gdep2_toposort_full {P D : Type} (TS : ptraces P D) :
  gdep2_acyclic TS →
  ∃ order : list gev,
    NoDup order ∧
    (∀ e, e ∈ order ↔ gev_wf TS e) ∧
    (∀ x y i j, order !! i = Some x → order !! j = Some y → gdep2 TS x y →
                (i < j)%nat).
Proof.
  intros Hacyc.
  destruct (gdep2_toposort_S TS (gev_wf TS) Hacyc) as (order & Hnd & Hmem & Hord).
  exists order. split_and!; [done| |done].
  intros e. rewrite Hmem. tauto.
Qed.

Corollary toposort_ind_full {P D : Type} (TS : ptraces P D) (Q : list gev → Prop) :
  gdep2_acyclic TS →
  Q [] →
  (∀ done e,
     Q done → gev_wf TS e → e ∉ done →
     (∀ e', gdep2 TS e' e → gev_wf TS e' → e' ∈ done) →
     Q (done ++ [e])) →
  ∃ order,
    Q order ∧
    NoDup order ∧
    (∀ e, e ∈ order ↔ gev_wf TS e) ∧
    (∀ x y i j, order !! i = Some x → order !! j = Some y → gdep2 TS x y →
                (i < j)%nat).
Proof.
  intros Hacyc Hnil Hstep.
  destruct (toposort_ind_S TS (gev_wf TS) Q Hacyc (dc_full TS) Hnil)
    as (order & HQ & Hnd & Hmem & Hord).
  { intros done e HQ Hwf _ Hnot Hpred. by apply Hstep. }
  exists order. split_and!; [done|done| |done].
  intros e. rewrite Hmem. tauto.
Qed.

(* ------------------------------------------------------------------ *)
(** ** DELIVERABLE 1 (continued): the bridge to the real [wstate] *)

Section ordwf.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pdev : P → wlabel → P → bool).

  Implicit Types TS : ptraces P D.
  Implicit Types e : gev.

  (** Every trace of the bundle starts from [ws_init] — the state
      phase's traces begin at [mid]'s agent records, whose [wstate]s the
      promise phase never touched. *)
  Definition ptraces_ws_init TS : Prop :=
    ∀ i T ag0, pt_trs TS !! i = Some T → at_ags T !! 0%nat = Some ag0 →
               pa_ws ag0 = ws_init.

  Lemma ptraces_of_ws_init TS mid c :
    ptraces_of pstep TS mid c → cfg_ws_init mid → ptraces_ws_init TS.
  Proof.
    intros (_ & _ & _ & _ & Hfst & _) Hinit i T ag0 HT Hag0.
    have H0 := Hfst i T HT. rewrite Hag0 in H0.
    by eapply Hinit.
  Qed.

  (** THE CORRESPONDENCE.  [pre_lstate TS e] is the [id]-leaf-mirror of
      the behavior's own [wstate] at [e]'s pre-state. *)
  Lemma pre_lstate_lrel TS e T ag :
    ptraces_wf pstep TS → ptraces_ws_init TS →
    pt_trs TS !! e.1 = Some T → at_ags T !! e.2 = Some ag →
    lrel id (pre_lstate TS e) (pa_ws ag).
  Proof.
    intros Hwf Hinit HT Hag.
    have Hwfi := Hwf e.1 T HT.
    destruct (atrace_first_is_Some pstep (pt_img TS) (pt_log TS) e.1 T Hwfi)
      as [ag0 Hag0].
    have Hws0 : pa_ws ag0 = ws_init by eapply Hinit.
    have Hfold : pa_ws ag = aevs_post id (take e.2 (at_evs T)) (pa_ws ag0).
    { eapply (asteps_ws_fold pstep (pt_img TS) (pt_log TS) e.1
                (at_ags T) (at_evs T) e.2 ag0 ag); [exact Hwfi|exact Hag0|exact Hag]. }
    rewrite (pre_lstate_tr TS e T HT) Hfold Hws0.
    apply lrel_aevs_post_id.
  Qed.

  (** …hence the read floor computed from the trace IS the behavior's
      own floor number, and [rd_floor] is the [F] of the design. *)
  Lemma rd_floor_ws TS r T ag l a :
    ptraces_wf pstep TS → ptraces_ws_init TS →
    pt_trs TS !! r.1 = Some T → at_ags T !! r.2 = Some ag →
    gev_lb TS r = Some l →
    match l with LLoad _ _ _ _ | LRmw _ _ _ _ _ => True | _ => False end →
    rd_floor TS r a
    = Nat.max (load_vpre (pa_ws ag) (lb_aq l)) (coh (pa_ws ag) a).
  Proof.
    intros Hwf Hinit HT Hag Hl Hrd.
    have Hrel : lrel id (pre_lstate TS r) (pa_ws ag) by eapply pre_lstate_lrel.
    rewrite (lrel_floor id (pre_lstate TS r) (pa_ws ag) (lb_aq l) a Hrel).
    rewrite /rd_floor /rd_leaves Hl.
    by destruct l.
  Qed.

End ordwf.

Global Arguments ptraces_ws_init {P D} _.

(* ------------------------------------------------------------------ *)
(** ** What W2b's simulation inherits from this file

    - [pre_lstate] + [pre_lstate_lrel] (+ [ptraces_ws_init] /
      [ptraces_of_ws_init]): the trace-computable leaf state of an
      event's pre-state, related to the behavior's real [wstate] at
      σ = [id].  Instantiating [WeakRobustProv]'s [lrel_aevs_post_init]
      at σ = π gives the promise-free run's [wstate] as the SAME leaf
      state's π-valuation — the two-valuations-of-one-leaf-state shape
      the readable-transport argument runs on.

    - [rd_leaves] / [rd_floor] (+ [rd_floor_ws]): the read floor as a
      LEAF LIST, and its identification with the behavior's
      [max (load_vpre, coh a)].

    - [gE] / [gdep2]: the extended graph.  [gE_ts_lt] says every E edge
      is timestamp-increasing (the fact the D⁺-acyclicity effort
      [WeakRobustAcyc2] starts from), [gE_wf]/[gdep2_wf] that it is a
      relation on real events, and [gdep2_dec]/[gdep2_rel_dec] that the
      sort over it stays CONSTRUCTIVE.

    - [gdep2_toposort_S] / [topo_order_S] / [toposort_ind_S]: the sort
      and the induction principle on a DOWNWARD-CLOSED subset [S], as
      design item (iv) requires (the ancestor closure of a minimal bad
      edge is such an [S]; [dc_full] / [sub_ok_full] and the
      corollaries [gdep2_toposort_full] / [toposort_ind_full] recover
      the whole-event-set case as ONE instantiation).
      [topo_pred_done_S] is the predecessor-done fact each step
      consumes, [topo_agent_mono_S] the per-agent monotonicity, and
      [dc_agent_prefix] / [sub_ok_agent_prefix] the "[S] contains whole
      trace prefixes" fact that makes [done] a per-agent trace prefix.

    NOT here, deliberately: any acyclicity proof for [gdep2] (that is
    [WeakRobustAcyc2]'s, and it is taken as the hypothesis
    [gdep2_acyclic] throughout), any timestamp permutation π, and any
    simulation relation. *)
