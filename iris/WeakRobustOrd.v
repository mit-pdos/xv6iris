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

    (4) THE SUBSET TOPOSORT, over an ARBITRARY edge relation [R].  Design
        item (iv) needs the induction to run not on all events but on a
        DOWNWARD-CLOSED subset [S] (the ancestor closure of a minimal bad
        edge).  [topo_sort_S] sorts the filtered carrier;
        [toposort_ind_S] is the induction principle, whose
        predecessor-done step is where downward closure ([dc]) is spent:
        an [R]-predecessor of an event of [S] is itself in [S], hence in
        the carrier, hence EARLIER.  [S := gev_wf TS] recovers the full
        case ([dc_full]).  [R] is a parameter (G3) because the exhibit
        route sorts [gdep2] while the fabric-carrying replay sorts
        [gdep3 = gdep2 ∪ gdev]; the argument is the same one, and the two
        properties it needs of [R] are section hypotheses ([Rwf]: edges
        relate real events; [Rpo]: [gpo ⊆ R]).

    (5) THE FABRIC-ORDERED GRAPH [gdep3 = gdep2 ∪ gdev] (G3), with the
        acyclicity criterion [gdep3_acyclic_of_rank] and the two
        instances that discharge it outright ([gdep3_acyclic_same_agent],
        [gdep3_acyclic_devfree]/[gdep3_acyclic_nodev]).  READ THE
        WARNING at the definition: the union's acyclicity is a NEW
        obligation, not a corollary of [gdep2]'s.

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
(** ** A RANK CRITERION FOR THE ACYCLICITY OF A UNION

    Generic, and stated in the shape G3 needs: [R] splits into a part
    that a rank never DECREASES along and a part it strictly INCREASES
    along; then any [R] cycle is a cycle of the first part.  (The union of
    an acyclic relation and a chain is NOT acyclic in general — this is
    the fact that has to be supplied, see [gdep3_acyclic_of_rank].) *)

Lemma tc_subrel {A} (R R' : A → A → Prop) :
  (∀ u v, R u v → R' u v) → ∀ x y, tc R x y → tc R' x y.
Proof.
  intros Hsub x y. induction 1 as [x y Hxy|x y z Hxy _ IH];
    [by apply tc_once, Hsub|].
  eapply tc_l; [by apply Hsub|exact IH].
Qed.

Lemma tc_rank_le {A} (R : A → A → Prop) (rk : A → nat) :
  (∀ u v, R u v → (rk u ≤ rk v)%nat) →
  ∀ x y, tc R x y → (rk x ≤ rk y)%nat.
Proof.
  intros Hle x y. induction 1 as [x y Hxy|x y z Hxy _ IH]; [by apply Hle|].
  etrans; [by apply Hle|done].
Qed.

Lemma tc_union_rank {A} (R R1 R2 : A → A → Prop) (rk : A → nat) :
  (∀ u v, R u v → R1 u v ∨ R2 u v) →
  (∀ u v, R1 u v → (rk u ≤ rk v)%nat) →
  (∀ u v, R2 u v → (rk u < rk v)%nat) →
  ∀ x y, tc R x y → tc R1 x y ∨ (rk x < rk y)%nat.
Proof.
  intros Hsplit Hle Hlt x y.
  induction 1 as [x y Hxy|x y z Hxy _ IH].
  - destruct (Hsplit x y Hxy) as [H1|H2]; [left; by apply tc_once|].
    right. by apply Hlt.
  - destruct (Hsplit x y Hxy) as [H1|H2], IH as [IH|IH].
    + left. by eapply tc_l.
    + right. have := Hle x y H1. lia.
    + right. have := tc_rank_le R1 rk Hle y z IH. have := Hlt x y H2. lia.
    + right. have := Hlt x y H2. lia.
Qed.

Lemma acyclic_union_rank {A} (R R1 R2 : A → A → Prop) (rk : A → nat) :
  (∀ u v, R u v → R1 u v ∨ R2 u v) →
  (∀ u v, R1 u v → (rk u ≤ rk v)%nat) →
  (∀ u v, R2 u v → (rk u < rk v)%nat) →
  (∀ e, ¬ tc R1 e e) →
  ∀ e, ¬ tc R e e.
Proof.
  intros Hsplit Hle Hlt Hacyc e Hc.
  destruct (tc_union_rank R R1 R2 rk Hsplit Hle Hlt e e Hc) as [Hc1|Hlt'];
    [by apply (Hacyc e)|lia].
Qed.

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
  (** D2: the ADDRESS-DEPENDENCY leaves come FIRST.  The machine's read
      pre-view is [load_vpre_d = V(asrc) ⊔ load_vpre], so the floor's leaf
      list is the operand leaves followed by the old floor's — and, by
      [WeakRobustProv.lsrcs_view_leaf], every one of the new leaves is
      already a leaf of the same [pre_lstate], so [rd_leaves_wf] and the
      E-edge well-definedness ([pre_lstate_leaf_occurs]) are unchanged. *)
  Definition rd_leaves TS (r : gev) (a : Z) : list nat :=
    match gev_lb TS r with
    | Some l =>
        match l with
        | LLoad _ _ _ _ _ | LRmw _ _ _ _ _ _ _ | LExLoad _ _ _ _ =>
            lsrcs_view (pre_lstate TS r) (lb_rasrc l)
            ++ lfloor (pre_lstate TS r) (lb_aq l) a
        | LSilent | LStore _ _ _ _ _ | LFence _ _ _ _ | LDev | LRegW _ _
        | LCtrl _ | LInstr | LExStore _ _ _ _ _ => []
        end
    | None => []
    end.

  Lemma rd_leaves_leaf TS r a t :
    t ∈ rd_leaves TS r a → lstate_leaf (pre_lstate TS r) t.
  Proof.
    rewrite /rd_leaves. destruct (gev_lb TS r) as [l|];
      [|by intros ?%elem_of_nil].
    destruct l; try by intros ?%elem_of_nil.
    all: intros [Ht|Ht]%elem_of_app;
      [by eapply lsrcs_view_leaf
      |rewrite /lfloor in Ht; apply elem_of_app in Ht as [Ht|Ht];
         [by eapply lload_vpre_leaf|by eapply lcoh_leaf]].
  Qed.

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
  (** ** THE FABRIC-ORDERED GRAPH D⁺⁺ = gdep2 ∪ gdev (G3)

      [WeakRobustGraph.gdev] is the successor relation on the global
      DEVICE-ORDER WITNESS.  Adding it to the graph is what makes every
      topological sort process the fabric-touching events in the
      behavior's own order — which is what lets the replay hand each of
      them the fabric it recorded ([WeakRobustSim], G4).

      ACYCLICITY IS A NEW OBLIGATION, NOT A COROLLARY.  A union of an
      acyclic relation with a chain on a subset is not acyclic in
      general, and here it is not even derivable from the behavior's
      TEMPORAL order: in the promising machine an rf edge may point
      BACKWARDS in time (a read may read a promise that its author
      fulfils later — that is what promises are for), so no
      behavior-order rank makes [gdep2] monotone.  What this file
      supplies is therefore (a) the rank CRITERION
      [gdep3_acyclic_of_rank], whose [gdep2] premise is exactly the
      compatibility that has to be established, and (b) the two
      instances that discharge it outright — no cross-agent device
      access ([gdep3_acyclic_same_agent]) and, as its special case, no
      device access at all ([gdep3_acyclic_nodev]), which is what every
      current (dev-free-scoped) consumer runs at. *)

  Definition gdep3 TS (DS : pdevs D) (e1 e2 : gev) : Prop :=
    gdep2 TS e1 e2 ∨ gdev TS DS e1 e2.

  Definition gdep3_acyclic TS DS : Prop := ∀ e, ¬ tc (gdep3 TS DS) e e.

  Lemma gdep2_gdep3 TS DS e1 e2 : gdep2 TS e1 e2 → gdep3 TS DS e1 e2.
  Proof. by left. Qed.
  Lemma gdev_gdep3 TS DS e1 e2 : gdev TS DS e1 e2 → gdep3 TS DS e1 e2.
  Proof. by right. Qed.
  Lemma gdep_gdep3 TS DS e1 e2 : gdep TS e1 e2 → gdep3 TS DS e1 e2.
  Proof. intros ?. by apply gdep2_gdep3, gdep_gdep2. Qed.
  Lemma gpo_gdep3 TS DS e1 e2 : gpo TS e1 e2 → gdep3 TS DS e1 e2.
  Proof. intros ?. by apply gdep2_gdep3, gpo_gdep2. Qed.
  Lemma grf_gdep3 TS DS e1 e2 : grf TS e1 e2 → gdep3 TS DS e1 e2.
  Proof. intros ?. by apply gdep2_gdep3, grf_gdep2. Qed.
  Lemma gE_gdep3 TS DS e1 e2 : gE TS e1 e2 → gdep3 TS DS e1 e2.
  Proof. intros ?. by apply gdep2_gdep3, gE_gdep2. Qed.

  Lemma tc_gdep2_gdep3 TS DS x y : tc (gdep2 TS) x y → tc (gdep3 TS DS) x y.
  Proof. apply tc_subrel. intros u v. apply gdep2_gdep3. Qed.

  Lemma gdep3_acyclic_gdep2 TS DS : gdep3_acyclic TS DS → gdep2_acyclic TS.
  Proof. intros Hac e Hc. by apply (Hac e), tc_gdep2_gdep3. Qed.

  Lemma gdep3_wf TS DS e1 e2 :
    ptraces_wit TS DS → gdep3 TS DS e1 e2 → gev_wf TS e1 ∧ gev_wf TS e2.
  Proof.
    intros Hwit [H2|Hd]; [by apply gdep2_wf|by eapply gdev_wf].
  Qed.

  Global Instance gdep3_dec TS DS e1 e2 : Decision (gdep3 TS DS e1 e2).
  Proof. rewrite /gdep3. apply _. Qed.
  Global Instance gdep3_rel_dec TS DS : RelDecision (gdep3 TS DS).
  Proof. intros e1 e2. apply _. Qed.

  (** THE CRITERION.  ([gdep2_acyclic] enters as the design prescribes;
      the rank premise on [gdep2] is the compatibility that the
      acyclicity band owes, NOT something the witness supplies.) *)
  Lemma gdep3_acyclic_of_rank TS DS (rk : gev → nat) :
    (∀ x y, gdep2 TS x y → (rk x ≤ rk y)%nat) →
    (∀ x y, gdev TS DS x y → (rk x < rk y)%nat) →
    gdep2_acyclic TS →
    gdep3_acyclic TS DS.
  Proof.
    intros Hle Hlt Hacyc e.
    apply (acyclic_union_rank (gdep3 TS DS) (gdep2 TS) (gdev TS DS) rk);
      [by intros u v Hd|exact Hle|exact Hlt|exact Hacyc].
  Qed.

  (** INSTANCE 1: a witness that never crosses agents adds NOTHING —
      (W3) already makes such a gdev edge a [gpo] edge. *)
  Lemma gdep3_same_agent_gdep2 TS DS e1 e2 :
    ptraces_wit TS DS → (∀ x y, gdev TS DS x y → x.1 = y.1) →
    gdep3 TS DS e1 e2 → gdep2 TS e1 e2.
  Proof.
    intros Hwit Hsa [H2|Hd]; [done|].
    apply gpo_gdep2. eapply gdev_gpo; [exact Hwit|exact Hd|by apply Hsa].
  Qed.

  Lemma gdep3_acyclic_same_agent TS DS :
    ptraces_wit TS DS → (∀ x y, gdev TS DS x y → x.1 = y.1) →
    gdep2_acyclic TS → gdep3_acyclic TS DS.
  Proof.
    intros Hwit Hsa Hacyc e Hc. apply (Hacyc e).
    eapply tc_subrel; [|exact Hc].
    intros u v. by apply (gdep3_same_agent_gdep2 TS DS).
  Qed.

  (** INSTANCE 2 (the dev-free collapse): with no gdev edges at all,
      D⁺⁺ IS D⁺.  A DEV-FREE bundle has none (W1: a listed position is a
      fabric-touching event), and so does the empty witness. *)
  Lemma gdep3_no_gdev_gdep2 TS DS e1 e2 :
    (∀ x y, ¬ gdev TS DS x y) → gdep3 TS DS e1 e2 → gdep2 TS e1 e2.
  Proof. intros Hno [H2|Hd]; [done|by destruct (Hno e1 e2)]. Qed.

  Lemma gdep3_acyclic_no_gdev TS DS :
    (∀ x y, ¬ gdev TS DS x y) → gdep2_acyclic TS → gdep3_acyclic TS DS.
  Proof.
    intros Hno Hacyc e Hc. apply (Hacyc e).
    eapply tc_subrel; [|exact Hc]. intros u v. by apply (gdep3_no_gdev_gdep2 TS DS).
  Qed.

  Lemma gdev_devfree TS DS :
    ptraces_wit TS DS →
    (∀ i T k ev, pt_trs TS !! i = Some T → at_evs T !! k = Some ev →
       ae_dev ev = None) →
    ∀ x y, ¬ gdev TS DS x y.
  Proof.
    intros (HW1 & _) Hdf x y (m & Hm & _).
    destruct (HW1 m x Hm) as (ev & Hev & Hs).
    rewrite /ev_at in Hev.
    destruct (pt_trs TS !! x.1) as [T|] eqn:HT; simpl in Hev; [|done].
    rewrite (Hdf x.1 T x.2 ev HT Hev) in Hs. by destruct Hs.
  Qed.

  Lemma gdep3_acyclic_devfree TS DS :
    ptraces_wit TS DS →
    (∀ i T k ev, pt_trs TS !! i = Some T → at_evs T !! k = Some ev →
       ae_dev ev = None) →
    gdep2_acyclic TS → gdep3_acyclic TS DS.
  Proof.
    intros Hwit Hdf. apply gdep3_acyclic_no_gdev. by eapply gdev_devfree.
  Qed.

  Lemma gdep3_nil_gdep2 TS (d : D) e1 e2 :
    gdep3 TS (PDevs d []) e1 e2 → gdep2 TS e1 e2.
  Proof. apply gdep3_no_gdev_gdep2. intros x y. apply gdev_nil. Qed.

  Lemma gdep3_acyclic_nodev TS (d : D) :
    gdep2_acyclic TS → gdep3_acyclic TS (PDevs d []).
  Proof. apply gdep3_acyclic_no_gdev. intros x y. apply gdev_nil. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE DEVICE EPOCH — the rank that discharges the criterion for
         [gpo] and [gdev], and NAMES the residue (G5a)

      SUPERSEDED AS A PREMISE (A0'): [dev_epoch_ok] below is no longer
      the clause [WeakRobustMain.main_premises] carries — it is STRICTLY
      STRONGER than what acyclicity needs (see [dev_wit_ok] further down,
      and [dev_wit_ok_of_epoch] for the implication).  Everything here
      stays: it is the sufficient condition with the per-edge shape, and
      [WeakRobustDisc] §A5's characterization is of it.

      THE ROUTE (worklist G5a, preference (1)).  The criterion
      [gdep3_acyclic_of_rank] wants a rank that [gdep2] never lowers and
      [gdev] always raises.  There is one canonical candidate — THE
      DEVICE EPOCH of an event: the witness position just past the LAST
      fabric-touching event of that event's OWN AGENT at or before it in
      that agent's trace.

      What the epoch buys, and it is exactly what the worklist's route
      (1) predicts:

      - [depoch_gpo_le]: a [gpo]-later event has an epoch ≥, because the
        predicate defining the epoch is monotone in the trace index.  No
        hypothesis at all.
      - [depoch_dev] / [depoch_gdev_lt]: a LISTED event's epoch is
        EXACTLY [S] its own witness index — the upper bound is (W3), the
        witness refining each agent's trace order — so a [gdev] edge
        raises the epoch by one.  This is the "gpo-adjacency to device
        events bridged by per-agent monotonicity" the route asks for, and
        it is a theorem.

      WHAT DOES NOT FOLLOW, AND WHY IT CANNOT (the honest residue, and
      the G3 finding one level down).  An [grf]/[gE] edge may LOWER the
      epoch, and no premise of the bundle forbids it.  The refutation is
      the promise mechanism again, one step past W7's:

          D₁ (agent A, witness index 10)  --gpo-->  w (agent A, a fulfil)
          w  --grf-->  r (agent B)  --gpo-->  D₂ (agent B, witness index 3)
          D₂ --gdev⁺--> D₁  (3 < 10)

      is a [gdep3] cycle with an ACYCLIC [gdep2] and all of (W1)–(W4)
      satisfied: the witness order is the behavior's temporal order, so
      the chain says only [D₂ < D₁] in time, hence [r < D₂ < D₁ < w];
      and [r] reading [w]'s message BEFORE [w] executes is precisely a
      read of a PROMISE, which the front-loaded promise phase supplies.
      So the union's acyclicity is not derivable from [gdep2]'s here
      either, and the epoch is where the gap is smallest.

      THE RESIDUE IS THEREFORE PER-EDGE, NOT GLOBAL: [dev_epoch_ok] says
      no reads-from and no floor-protection edge runs BACKWARDS ACROSS A
      FABRIC ACCESS.  It is strictly weaker than the refuted W7 ("rf is
      forward in behavior time"), it has the shape of the other per-edge
      obligations ([rf_edges_ok], [ee_ok] — no cycle quantifier, one
      statement per edge), and it collapses to [True] whenever the
      witness is empty ([dev_epoch_ok_nil]), which is what keeps every
      dev-free consumer free of it. *)

  (** [dep_go l e m] — the epoch of [e] computed over the witness suffix
      [l] whose head sits at witness position [m]: [S (m + i)] for the
      LAST position [i] of [l] holding an event of [e]'s own agent at or
      before [e], and [0] if there is none. *)
  Fixpoint dep_go (l : list gev) (e : gev) (m : nat) : nat :=
    match l with
    | [] => 0%nat
    | e' :: l' =>
        Nat.max (if bool_decide (e'.1 = e.1 ∧ (e'.2 ≤ e.2)%nat)
                 then S m else 0%nat)
                (dep_go l' e (S m))
    end.

  Lemma dep_go_lb l e m i e' :
    l !! i = Some e' → e'.1 = e.1 → (e'.2 ≤ e.2)%nat →
    (S (m + i) ≤ dep_go l e m)%nat.
  Proof.
    revert m i. induction l as [|x l IH]; intros m i Hi Hag Hle;
      [by rewrite lookup_nil in Hi|].
    destruct i as [|i]; rewrite lookup_cons in Hi.
    - simplify_eq. simpl.
      have -> : bool_decide (e'.1 = e.1 ∧ (e'.2 ≤ e.2)%nat) = true
        by apply bool_decide_eq_true.
      lia.
    - simpl. have := IH (S m) i Hi Hag Hle. lia.
  Qed.

  Lemma dep_go_ub l e m N :
    (∀ i e', l !! i = Some e' → e'.1 = e.1 → (e'.2 ≤ e.2)%nat →
       (S (m + i) ≤ N)%nat) →
    (dep_go l e m ≤ N)%nat.
  Proof.
    revert m. induction l as [|x l IH]; intros m H; [simpl; lia|].
    simpl. apply Nat.max_lub.
    - destruct (bool_decide (x.1 = e.1 ∧ (x.2 ≤ e.2)%nat)) eqn:Hb; [|lia].
      apply bool_decide_eq_true in Hb as [Hag Hle].
      have := H 0%nat x eq_refl Hag Hle. lia.
    - apply IH. intros i e' Hi Hag Hle.
      have := H (S i) e' Hi Hag Hle. lia.
  Qed.

  Lemma dep_go_mono l e1 e2 m :
    e1.1 = e2.1 → (e1.2 ≤ e2.2)%nat → (dep_go l e1 m ≤ dep_go l e2 m)%nat.
  Proof.
    intros Hag Hle. revert m. induction l as [|x l IH]; intros m; [done|].
    simpl. apply Nat.max_le_compat; [|apply IH].
    destruct (bool_decide (x.1 = e1.1 ∧ (x.2 ≤ e1.2)%nat)) eqn:Hb; [|lia].
    apply bool_decide_eq_true in Hb as [H1 H2].
    have -> : bool_decide (x.1 = e2.1 ∧ (x.2 ≤ e2.2)%nat) = true.
    { apply bool_decide_eq_true. split; [congruence|lia]. }
    lia.
  Qed.

  Definition depoch (DS : pdevs D) (e : gev) : nat := dep_go (pd_ord DS) e 0%nat.

  Lemma depoch_lb DS e m e' :
    pd_ord DS !! m = Some e' → e'.1 = e.1 → (e'.2 ≤ e.2)%nat →
    (S m ≤ depoch DS e)%nat.
  Proof.
    intros Hm Hag Hle.
    have := dep_go_lb (pd_ord DS) e 0%nat m e' Hm Hag Hle. rewrite /depoch. lia.
  Qed.

  (** A LISTED event's epoch is [S] its own witness index — the upper
      bound is (W3): a LATER witness entry of the same agent is a LATER
      trace position, so it cannot be at or before [e]. *)
  Lemma depoch_dev TS DS m e :
    ptraces_wit TS DS → pd_ord DS !! m = Some e → depoch DS e = S m.
  Proof.
    intros (_ & _ & HW3 & _) Hm.
    have Hlb : (S m ≤ depoch DS e)%nat by eapply depoch_lb; [exact Hm|done|done].
    have Hub : (depoch DS e ≤ S m)%nat.
    { apply dep_go_ub. intros i e' Hi Hag Hle.
      destruct (decide (i ≤ m)%nat) as [?|Hgt]; [lia|exfalso].
      have Hm' : pd_ord DS !! m = Some (e.1, e.2)
        by rewrite -(surjective_pairing e).
      have Hi' : pd_ord DS !! i = Some (e.1, e'.2)
        by rewrite -Hag -(surjective_pairing e').
      have := HW3 m i e.1 e.2 e'.2 ltac:(lia) Hm' Hi'. lia. }
    lia.
  Qed.

  Lemma depoch_gpo_le TS DS e1 e2 :
    gpo TS e1 e2 → (depoch DS e1 ≤ depoch DS e2)%nat.
  Proof. intros (Hag & Hlt & _ & _). apply dep_go_mono; [done|lia]. Qed.

  Lemma depoch_gdev_lt TS DS e1 e2 :
    ptraces_wit TS DS → gdev TS DS e1 e2 → (depoch DS e1 < depoch DS e2)%nat.
  Proof.
    intros Hwit (m & Hm1 & Hm2).
    rewrite (depoch_dev TS DS m e1 Hwit Hm1)
            (depoch_dev TS DS (S m) e2 Hwit Hm2). lia.
  Qed.

  (** THE NAMED RESIDUE: no reads-from and no floor-protection edge runs
      BACKWARDS across a fabric access.  Per-edge, no cycle quantifier —
      the same epistemic shape as [rf_edges_ok] and [ee_ok]. *)
  Definition dev_epoch_ok TS (DS : pdevs D) : Prop :=
    ∀ e1 e2, (grf TS e1 e2 ∨ gE TS e1 e2) →
      (depoch DS e1 ≤ depoch DS e2)%nat.

  Lemma dev_epoch_ok_nil TS (d : D) : dev_epoch_ok TS (PDevs d []).
  Proof. intros e1 e2 _. rewrite /depoch /=. lia. Qed.

  Lemma depoch_gdep2_le TS DS e1 e2 :
    dev_epoch_ok TS DS → gdep2 TS e1 e2 → (depoch DS e1 ≤ depoch DS e2)%nat.
  Proof.
    intros Hok [[Hpo|Hrf]|HE];
      [by eapply depoch_gpo_le|apply Hok; by left|apply Hok; by right].
  Qed.

  (** THE SPLIT, which is all three consumers need: a [gdep3] PATH is a
      [gdep2] path or it strictly raised the epoch. *)
  Lemma tc_gdep3_epoch TS DS x y :
    ptraces_wit TS DS → dev_epoch_ok TS DS →
    tc (gdep3 TS DS) x y →
    tc (gdep2 TS) x y ∨ (depoch DS x < depoch DS y)%nat.
  Proof.
    intros Hwit Hok.
    apply (tc_union_rank (gdep3 TS DS) (gdep2 TS) (gdev TS DS) (depoch DS)).
    - by intros u v Hd.
    - intros u v. by apply depoch_gdep2_le.
    - intros u v. by eapply depoch_gdev_lt.
  Qed.

  (** POINTWISE: an event off every [gdep2] cycle is off every [gdep3]
      cycle.  (This is the form the EXHIBIT's cone consumes — it has no
      global acyclicity to spend.) *)
  Lemma gdep3_acyclic_at_epoch TS DS e :
    ptraces_wit TS DS → dev_epoch_ok TS DS →
    ¬ tc (gdep2 TS) e e → ¬ tc (gdep3 TS DS) e e.
  Proof.
    intros Hwit Hok Hac Hc.
    destruct (tc_gdep3_epoch TS DS e e Hwit Hok Hc) as [Hc2|Hlt];
      [by apply Hac|lia].
  Qed.

  (** …and the global theorem, as an instance of the G3 criterion. *)
  Theorem gdep3_acyclic_epoch TS DS :
    ptraces_wit TS DS → dev_epoch_ok TS DS →
    gdep2_acyclic TS → gdep3_acyclic TS DS.
  Proof.
    intros Hwit Hok Hac e.
    by eapply (gdep3_acyclic_at_epoch TS DS e Hwit Hok (Hac e)).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** A0′: [dev_wit_ok] — THE EXACT CONDITION ACYCLICITY NEEDS
         (this SUPERSEDES [dev_epoch_ok] as the premise; the epoch stays
         as a sufficient condition, see [dev_wit_ok_of_epoch])

      WHY THE EPOCH WAS TOO STRONG.  [dev_epoch_ok] is a per-edge
      DOMINATION condition ([WeakRobustDisc] §A5 proves
      [dev_epoch_ok ↔ dev_dom]): it forces the READER of every rf edge to
      have a fabric access of its OWN dominating the writer's.  A bundle
      as ordinary as

          agent A: fabric access; store x      agent B: load x

      falsifies it — B never touches the fabric, so B's epoch is [0] and
      the rf edge A→B lowers it — even though the fabric-ordered graph is
      plainly acyclic (there is only ONE fabric event, hence no [gdev]
      edge at all).

      WHAT ACYCLICITY ACTUALLY NEEDS.  [gdev] is the SUCCESSOR relation
      on [pd_ord DS], i.e. the total chain over the witness in witness
      order, so it can only ever RAISE the witness index, by exactly one.
      Split a [gdep3] cycle at its [gdev] edges: the [gdev] hops walk the
      witness index up, so somewhere a [gdep2] run must walk it back
      DOWN — from a fabric event of higher witness index to one of lower
      (or, degenerately, back to the same one, which is a [gdep2] cycle).
      Forbidding exactly that is [dev_wit_ok]: THE WITNESS ORDER IS
      [gdep2]-CONSISTENT.  It quantifies over pairs of LISTED events
      only, so it is free whenever the witness has fewer than two entries
      ([dev_wit_ok_short], [dev_wit_ok_nil]) — in particular on the
      refuting bundle above — and free outright on a dev-free bundle
      ([dev_wit_ok_devfree]).

      It is not per-edge (it mentions [tc (gdep2 TS)]), which is the
      honest price of being exactly the right condition; but it is
      implied by the old per-edge one ([dev_wit_ok_of_epoch]), so nothing
      that discharged [dev_epoch_ok] is lost. *)

  Definition dev_wit_ok TS (DS : pdevs D) : Prop :=
    ∀ m1 m2 e1 e2, (m1 < m2)%nat →
      pd_ord DS !! m1 = Some e1 → pd_ord DS !! m2 = Some e2 →
      ¬ tc (gdep2 TS) e2 e1.

  Lemma dev_wit_ok_nil TS (d : D) : dev_wit_ok TS (PDevs d []).
  Proof. intros m1 m2 e1 e2 _ Hm1. by rewrite lookup_nil in Hm1. Qed.

  (** FREE ON THE §A5 REFUTING BUNDLE: it has a single fabric access, and
      one entry admits no pair [m1 < m2]. *)
  Lemma dev_wit_ok_short TS (DS : pdevs D) :
    (length (pd_ord DS) ≤ 1)%nat → dev_wit_ok TS DS.
  Proof.
    intros Hlen m1 m2 e1 e2 Hlt _ Hm2.
    (* NOTE: spell the bound out over [pd_ord DS] — reading it off [Hm2]
       gives [@length gev] and [lia] does not identify the two atoms. *)
    have Hb : (m2 < length (pd_ord DS))%nat by eapply lookup_lt_Some.
    lia.
  Qed.

  (** FREE ON A DEV-FREE BUNDLE: (W1) says a listed position is a
      fabric-touching event, and there are none. *)
  Lemma dev_wit_ok_devfree TS DS :
    ptraces_wit TS DS →
    (∀ i T k ev, pt_trs TS !! i = Some T → at_evs T !! k = Some ev →
       ae_dev ev = None) →
    dev_wit_ok TS DS.
  Proof.
    intros (HW1 & _) Hdf m1 m2 e1 e2 _ Hm1 _.
    destruct (HW1 m1 e1 Hm1) as (ev & Hev & Hs).
    rewrite /ev_at in Hev.
    destruct (pt_trs TS !! e1.1) as [T|] eqn:HT; simpl in Hev; [|done].
    rewrite (Hdf e1.1 T e1.2 ev HT Hev) in Hs. by destruct Hs.
  Qed.

  (** THE OLD PREMISE IMPLIES THE NEW ONE (so the new one is weaker, and
      every discharge route for the epoch still applies): the epoch never
      falls along a [gdep2] PATH under [dev_epoch_ok], and a listed
      event's epoch is [S] its own witness index ([depoch_dev]). *)
  Lemma depoch_tc_gdep2_le TS DS e1 e2 :
    dev_epoch_ok TS DS → tc (gdep2 TS) e1 e2 →
    (depoch DS e1 ≤ depoch DS e2)%nat.
  Proof.
    intros Hok. induction 1 as [x y Hxy|x y z Hxy _ IH].
    - by eapply depoch_gdep2_le.
    - have := depoch_gdep2_le TS DS x y Hok Hxy. lia.
  Qed.

  Lemma dev_wit_ok_of_epoch TS DS :
    ptraces_wit TS DS → dev_epoch_ok TS DS → dev_wit_ok TS DS.
  Proof.
    intros Hwit Hok m1 m2 e1 e2 Hlt Hm1 Hm2 Hc.
    have Hle := depoch_tc_gdep2_le TS DS e2 e1 Hok Hc.
    rewrite (depoch_dev TS DS m1 e1 Hwit Hm1)
            (depoch_dev TS DS m2 e2 Hwit Hm2) in Hle. lia.
  Qed.

  (** THE SPLIT, the [dev_wit_ok] analogue of [tc_gdep3_epoch]: a
      [gdep3] path is a [gdep2] path, or it ENTERS the witness at some
      position [m1] and LEAVES it at a STRICTLY LATER one [m2], with
      plain [gdep2] runs on either side.

      The invariant [m1 < m2] is what [dev_wit_ok] buys, and it is bought
      in the [gdev]-prefix case: the [gdep2] run leaving the new edge's
      target (witness index [S m]) reaches the old entry point [e1]
      (witness index [m1]), so [m1 < S m] would be a [gdep2] path from a
      LATER listed event to an EARLIER one. *)
  Lemma tc_gdep3_wit TS DS x y :
    ptraces_wit TS DS → dev_wit_ok TS DS →
    tc (gdep3 TS DS) x y →
    tc (gdep2 TS) x y ∨
    ∃ m1 m2 e1 e2,
      pd_ord DS !! m1 = Some e1 ∧ pd_ord DS !! m2 = Some e2 ∧
      (m1 < m2)%nat ∧ rtc (gdep2 TS) x e1 ∧ rtc (gdep2 TS) e2 y.
  Proof.
    intros Hwit Hok. induction 1 as [x y Hxy|x z y Hxz _ IH].
    - destruct Hxy as [H2|(m & Hm & Hsm)].
      + left. by apply tc_once.
      + right. exists m, (S m), x, y.
        split_and!; [exact Hm|exact Hsm|lia|apply rtc_refl|apply rtc_refl].
    - destruct Hxz as [H2|(m & Hm & Hsm)].
      + destruct IH as [Hzy|(m1 & m2 & e1 & e2 & Hm1 & Hm2 & Hlt & Hze1 & He2y)].
        * left. by eapply tc_l.
        * right. exists m1, m2, e1, e2.
          split_and!; [exact Hm1|exact Hm2|exact Hlt| |exact He2y].
          by eapply rtc_l.
      + destruct IH as [Hzy|(m1 & m2 & e1 & e2 & Hm1 & Hm2 & Hlt & Hze1 & He2y)].
        * right. exists m, (S m), x, z.
          split_and!; [exact Hm|exact Hsm|lia|apply rtc_refl|by apply tc_rtc].
        * have Hle : (S m ≤ m1)%nat.
          { apply rtc_tc in Hze1 as [Heq|Htc].
            - rewrite Heq in Hsm.
              have Heq' : S m = m1 by eapply pd_ord_index_inj;
                [exact Hwit|exact Hsm|exact Hm1].
              lia.
            - destruct (decide (m1 < S m)%nat) as [Hlt'|Hge]; [|lia].
              by destruct (Hok m1 (S m) e1 z Hlt' Hm1 Hsm Htc). }
          right. exists m, m2, x, e2.
          split_and!; [exact Hm|exact Hm2|lia|apply rtc_refl|exact He2y].
  Qed.

  (** POINTWISE, the form the EXHIBIT's cone consumes: an event off every
      [gdep2] cycle is off every [gdep3] cycle.  (The "leaves the witness
      later than it entered" branch is outright contradictory on a CYCLE:
      it closes a [gdep2] run from the later listed event back to the
      earlier one, which is what [dev_wit_ok] forbids — and if the two
      listed events coincide the witness indices do too.) *)
  Lemma gdep3_acyclic_at_wit TS DS e :
    ptraces_wit TS DS → dev_wit_ok TS DS →
    ¬ tc (gdep2 TS) e e → ¬ tc (gdep3 TS DS) e e.
  Proof.
    intros Hwit Hok Hac Hc.
    destruct (tc_gdep3_wit TS DS e e Hwit Hok Hc)
      as [Hc2|(m1 & m2 & e1 & e2 & Hm1 & Hm2 & Hlt & Hee1 & He2e)];
      [by apply Hac|].
    have He21 : rtc (gdep2 TS) e2 e1 by etrans.
    apply rtc_tc in He21 as [Heq|Htc].
    - rewrite Heq in Hm2.
      have Heq' : m1 = m2 by eapply pd_ord_index_inj;
        [exact Hwit|exact Hm1|exact Hm2].
      lia.
    - by destruct (Hok m1 m2 e1 e2 Hlt Hm1 Hm2 Htc).
  Qed.

  (** …and the global theorem: THE criterion the fabric-ordered graph is
      landed on (A0′). *)
  Theorem gdep3_acyclic_of_wit TS DS :
    ptraces_wit TS DS → gdep2_acyclic TS → dev_wit_ok TS DS →
    gdep3_acyclic TS DS.
  Proof.
    intros Hwit Hac Hok e.
    by eapply (gdep3_acyclic_at_wit TS DS e Hwit Hok (Hac e)).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 4, part 1: the SUBSET vocabulary

      GENERALIZED over the edge relation [R] (G3): the sort and its
      induction principle are run at [R := gdep2 TS] by the exhibit route
      and at [R := gdep3 TS DS] by the fabric-carrying replay, and the
      argument is the same one. *)

  (** DOWNWARD CLOSURE under [R]: an [R]-predecessor of an event of [S]
      is itself in [S]. *)
  Definition dc TS (R : gev → gev → Prop) (S : gev → Prop) : Prop :=
    ∀ e e', S e → R e' e → gev_wf TS e' → S e'.

  (** A WELL-FORMED SUBSET: downward closed, and made of real events.
      (The [Decision] side condition is a typeclass context, not a
      field — see the header.) *)
  Definition sub_ok TS R (S : gev → Prop) : Prop :=
    dc TS R S ∧ (∀ e, S e → gev_wf TS e).

  (** THE FULL INSTANCE: [gev_wf] itself is downward closed. *)
  Lemma dc_full TS R : dc TS R (gev_wf TS).
  Proof. intros e e' _ _ Hwf. exact Hwf. Qed.

  Lemma sub_ok_full TS R : sub_ok TS R (gev_wf TS).
  Proof. split; [apply dc_full|done]. Qed.

  (** [dc] only ever SHRINKS when the relation grows. *)
  Lemma dc_mono TS (R R' : gev → gev → Prop) S :
    (∀ x y, R x y → R' x y) → dc TS R' S → dc TS R S.
  Proof. intros Hsub Hdc e e' HS Hr Hwf. eapply Hdc; [exact HS| |exact Hwf]. by apply Hsub. Qed.

  (** The packaged conclusion of the subset sort. *)
  Definition topo_order_S TS R (S : gev → Prop) (order : list gev) : Prop :=
    NoDup order ∧
    (∀ e, e ∈ order ↔ (gev_wf TS e ∧ S e)) ∧
    (∀ x y i j, order !! i = Some x → order !! j = Some y → R x y →
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
  (** THE EDGE RELATION the sort respects — [gdep2 TS] for the exhibit
      route, [gdep3 TS DS] for the fabric-carrying replay. *)
  Context (R : gev → gev → Prop).
  Context `{!RelDecision R}.
  Context (Rwf : ∀ x y, R x y → gev_wf TS x ∧ gev_wf TS y).
  Context (Rpo : ∀ x y, gpo TS x y → R x y).
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
      [R] and the filtered carrier. *)
  Theorem topo_sort_S :
    (∀ e, ¬ tc R e e) →
    ∃ order : list gev,
      NoDup order ∧
      (∀ e, e ∈ order ↔ (gev_wf TS e ∧ S e)) ∧
      (∀ x y i j, order !! i = Some x → order !! j = Some y → R x y →
                  (i < j)%nat).
  Proof.
    intros Hacyc.
    destruct (topo_sort R gev_enum_S Hacyc NoDup_gev_enum_S)
      as (order & Hnd & Hmem & Hord).
    exists order. split_and!; [done| |].
    - intros e. rewrite Hmem. apply elem_of_gev_enum_S.
    - intros x y i j Hi Hj Hd. by eapply Hord.
  Qed.

  Corollary topo_sort_S_pack :
    (∀ e, ¬ tc R e e) → ∃ order, topo_order_S TS R S order.
  Proof.
    intros Hacyc. destruct topo_sort_S as (order & ? & ? & ?); [done|].
    exists order. by split_and!.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** Prefix closure — where DOWNWARD CLOSURE is spent *)

  Lemma topo_order_S_wf order e :
    topo_order_S TS R S order → e ∈ order → gev_wf TS e ∧ S e.
  Proof. intros (_ & Hmem & _) He. by apply Hmem. Qed.

  Lemma topo_order_S_index_unique order i j e :
    topo_order_S TS R S order → order !! i = Some e → order !! j = Some e → i = j.
  Proof. intros (Hnd & _ & _) Hi Hj. by eapply list_relations.NoDup_lookup. Qed.

  (** No [R] edge points from OUTSIDE a prefix INTO it — provided
      the source is a real event, which [Rwf] always gives. *)
  Lemma topo_prefix_closed_S order n x y :
    topo_order_S TS R S order → dc TS R S →
    R x y → y ∈ take n order → x ∈ take n order.
  Proof.
    intros Ho Hdc Hd Hy. have Ho' := Ho. destruct Ho' as (Hnd & Hmem & Hord).
    apply elem_of_take in Hy as (j & Hj & Hjn).
    have Hyin : y ∈ order by eapply elem_of_list_lookup_2.
    have Hys : gev_wf TS y ∧ S y by apply Hmem.
    have Hxwf : gev_wf TS x by apply (Rwf x y Hd).
    have Hxs : S x by eapply Hdc; [apply Hys|exact Hd|exact Hxwf].
    have Hx : x ∈ order by apply Hmem.
    apply elem_of_list_lookup in Hx as (i & Hi).
    have Hlt : (i < j)%nat by eapply Hord.
    apply elem_of_take. exists i. split; [done|lia].
  Qed.

  (** The same fact at the exact step the induction takes. *)
  Lemma topo_pred_done_S order n e :
    topo_order_S TS R S order → dc TS R S → order !! n = Some e →
    ∀ e', R e' e → gev_wf TS e' → e' ∈ take n order.
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
    topo_order_S TS R S order → order !! n = Some e → e ∉ take n order.
  Proof.
    intros (Hnd & _ & _) Hn He.
    apply elem_of_take in He as (i & Hi & Hin).
    have Heq : i = n by eapply list_relations.NoDup_lookup. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** PER-AGENT MONOTONICITY in the subset order

      [gpo] edges are [R] edges, so [WeakRobustLin]'s
      [topo_agent_mono] carries over verbatim — with the [gev_wf] side
      conditions supplied by membership in the (filtered) order. *)

  Lemma topo_agent_lt_S order i j x y :
    topo_order_S TS R S order → order !! i = Some x → order !! j = Some y →
    x.1 = y.1 → (x.2 < y.2)%nat → (i < j)%nat.
  Proof.
    intros (Hnd & Hmem & Hord) Hi Hj Hag Hk.
    eapply Hord; [exact Hi|exact Hj|]. apply Rpo.
    split_and!; [done|done| |].
    - apply (Hmem x). by eapply elem_of_list_lookup_2.
    - apply (Hmem y). by eapply elem_of_list_lookup_2.
  Qed.

  Lemma topo_agent_mono_S order i j x y :
    topo_order_S TS R S order → order !! i = Some x → order !! j = Some y →
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
      [R] edge). *)
  Lemma dc_agent_prefix j k k' :
    dc TS R S → S (j, k) → gev_wf TS (j, k) → gev_wf TS (j, k') →
    (k' < k)%nat → S (j, k').
  Proof.
    intros Hdc HS Hwf Hwf' Hlt. eapply Hdc; [exact HS| |exact Hwf'].
    apply Rpo. by split_and!.
  Qed.

  Lemma sub_ok_agent_prefix j k k' :
    sub_ok TS R S → S (j, k) → gev_wf TS (j, k') → (k' < k)%nat → S (j, k').
  Proof.
    intros [Hdc Hsub] HS Hwf' Hlt.
    eapply dc_agent_prefix; [exact Hdc|exact HS|by apply Hsub|exact Hwf'|exact Hlt].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** THE INDUCTION PRINCIPLE — the interface W2b's simulation
         consumes on a downward-closed subset *)

  Lemma toposort_ind_S (Q : list gev → Prop) :
    (∀ e, ¬ tc R e e) → dc TS R S →
    Q [] →
    (∀ done e,
       Q done →
       gev_wf TS e → S e → e ∉ done →
       (∀ e', R e' e → gev_wf TS e' → e' ∈ done) →
       Q (done ++ [e])) →
    ∃ order,
      Q order ∧
      NoDup order ∧
      (∀ e, e ∈ order ↔ (gev_wf TS e ∧ S e)) ∧
      (∀ x y i j, order !! i = Some x → order !! j = Some y → R x y →
                  (i < j)%nat).
  Proof.
    intros Hacyc Hdc Hnil Hstep.
    destruct (topo_sort_S_pack Hacyc) as (order & Ho).
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

Corollary topo_sort_full {P D : Type} (TS : ptraces P D)
    (R : gev -> gev -> Prop) `{!RelDecision R} :
  (∀ e, ¬ tc R e e) →
  ∃ order : list gev,
    NoDup order ∧
    (∀ e, e ∈ order ↔ gev_wf TS e) ∧
    (∀ x y i j, order !! i = Some x → order !! j = Some y → R x y →
                (i < j)%nat).
Proof.
  intros Hacyc.
  destruct (topo_sort_S TS R (gev_wf TS) Hacyc)
    as (order & Hnd & Hmem & Hord).
  exists order. split_and!; [done| |done].
  intros e. rewrite Hmem. tauto.
Qed.

Corollary toposort_ind_full {P D : Type} (TS : ptraces P D)
    (R : gev -> gev -> Prop) `{!RelDecision R}
    (Q : list gev → Prop) :
  (∀ e, ¬ tc R e e) →
  Q [] →
  (∀ done e,
     Q done → gev_wf TS e → e ∉ done →
     (∀ e', R e' e → gev_wf TS e' → e' ∈ done) →
     Q (done ++ [e])) →
  ∃ order,
    Q order ∧
    NoDup order ∧
    (∀ e, e ∈ order ↔ gev_wf TS e) ∧
    (∀ x y i j, order !! i = Some x → order !! j = Some y → R x y →
                (i < j)%nat).
Proof.
  intros Hacyc Hnil Hstep.
  destruct (toposort_ind_S TS R (gev_wf TS) Q Hacyc (dc_full TS R) Hnil)
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
    match l with
    | LLoad _ _ _ _ _ | LRmw _ _ _ _ _ _ _ | LExLoad _ _ _ _ => True
    | LSilent | LStore _ _ _ _ _ | LFence _ _ _ _ | LDev | LRegW _ _
    | LCtrl _ | LInstr | LExStore _ _ _ _ _ => False
    end →
    rd_floor TS r a
    = Nat.max (load_vpre_d (pa_ws ag) (lb_aq l)
                 (srcs_view (pa_ws ag) (lb_rasrc l)))
              (coh (pa_ws ag) a).
  Proof.
    intros Hwf Hinit HT Hag Hl Hrd.
    have Hrel : lrel id (pre_lstate TS r) (pa_ws ag) by eapply pre_lstate_lrel.
    rewrite (lrel_floor_d id (pre_lstate TS r) (pa_ws ag) (lb_aq l) a
               (lb_rasrc l) Hrel).
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

    - [gdep3] / [gdep3_acyclic]: the FABRIC-ORDERED graph, whose sort is
      what [WeakRobustSim]'s fabric fold runs along.  [gdep3_acyclic]
      implies [gdep2_acyclic] ([gdep3_acyclic_gdep2]); the converse needs
      a compatibility fact ([gdep3_acyclic_of_rank]) which the dev-free
      and single-agent instances supply for free.

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
