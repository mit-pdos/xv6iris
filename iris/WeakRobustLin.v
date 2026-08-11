(** * WeakRobustLin.v — the topological linearization of the dependency graph
      (M6 W2b, slice 1: the induction backbone)

    [WeakRobustGraph.v] builds the dependency relation [gdep = gpo ∪ grf]
    over a traced behavior's event set, and [WeakRobustAcyc.v] proves it
    ACYCLIC under the per-class premises.  This file turns that acyclicity
    into the object W2b's delay-simulation actually inducts over: a LIST of
    all the bundle's events, duplicate-free, complete, and topologically
    sorted — every [gdep] edge points strictly forward.

    THE FOUR DELIVERABLES.

    (1) THE EVENT ENUMERATION ([gev_enum]).  The finite list of every
        well-formed event of a [ptraces] bundle — all [(i, k)] with
        [i < length (pt_trs TS)] and [k < length (at_evs T_i)] — built as a
        left fold over the trace list ([gev_enum_from], an explicit offset
        recursion rather than a [flat_map]/[imap] so that the membership,
        [NoDup] and length lemmas are one induction each).  Proved:
        [NoDup_gev_enum], [elem_of_gev_enum] ([e ∈ gev_enum TS ↔ gev_wf TS e])
        and [length_gev_enum] (the sum of the trace lengths).

    (2) DECIDABILITY of the graph relations ([gev_wf_dec], [gev_reads_dec],
        [gpo_dec], [grf_dec], [gdep_dec], plus [RelDecision] wrappers).
        Every quantifier in the graph vocabulary is bounded by a list
        lookup: [gev_wf] is an [is_Some]; [gev_reads] is membership in the
        CONCRETE list [lb_reads l]; and [grf]'s [∃ ts a] ranges over the
        source's [gev_ts] (ONE [option]) and the reader's [lb_reads] (a
        concrete list), so it reflects into an [Exists] over that list.
        Route taken: direct [Decision] instances (no boolean reflection
        layer was needed — see the report).  These are what make the
        topological sort constructive: NOTHING below uses a classical
        axiom, and there is no [Admitted]/[Axiom] in this file.

    (3) THE LINEARIZATION ([gdep_toposort]).  An acyclic decidable relation
        on a finite carrier admits a topological order.  The proof is the
        textbook one, stated generically in [Section topo_generic] over an
        abstract [(A, R)] so that nothing about [gev] leaks into it:

          - [topo_scan]: scanning a list, EITHER some element has no
            R-predecessor in the carrier (a minimal element) OR every
            scanned element has one.  This is where decidability is spent —
            it is the constructive replacement for "¬∀ → ∃".
          - [topo_chain]: if EVERY element has a predecessor, then from any
            element one can walk back [n] steps for any [n], producing a
            list all of whose later entries are [tc R]-predecessors of the
            earlier ones.
          - [topo_min]: acyclicity makes such a chain [NoDup] (a repeat
            would be a [tc R x x]), so its length is bounded by the
            carrier's — PIGEONHOLE, via [list_relations.NoDup_submseteq] + [list_relations.submseteq_length].
            A chain of length [|carrier| + 1] is the contradiction, so a
            minimal element always exists.
          - [topo_sort_aux]: pop the minimal element, recurse on the rest
            (induction on the carrier's length).

    (4) THE INDUCTION PRINCIPLE ([toposort_ind]) — the interface W2b
        consumes.  Processing events in topological order, each step knows
        that ALL of its [gdep]-predecessors are already in the processed
        prefix.  Derived from (3) by inducting on [take n order] and
        reading the predecessor knowledge off [topo_pred_done].

    THE INCREMENTS the construction will want, all stated against the
    packaged [topo_order]:

      - [gev_index] — a FUNCTION giving each wf event its position, with
        [gev_index_lookup] / [gev_index_Some] / [gev_index_None];
      - [topo_prefix_closed] / [topo_pred_done] — PREFIX CLOSURE: no [gdep]
        edge points from outside a prefix of [order] into it.  This is the
        ordering property restated in the exact form the induction consumes;
      - [topo_agent_mono] — PER-AGENT MONOTONICITY: the subsequence of
        [order] belonging to one agent is increasing in the step index [k],
        in BOTH directions ([i < j ↔ x.2 < y.2]).  The forward direction is
        [gpo ⊆ gdep] (and [gpo] needs both endpoints [gev_wf], which
        membership in [order] supplies); the backward direction is [NoDup]
        plus the same [gpo] edge the other way round.  Note this needs NO
        [ptraces_wf]: the rf half of [gdep_same_agent_lt] is not used, since
        the sort already ordered every [gdep] edge.

    DEPENDENCY-FREE like its parents: stdpp only, no Iris, no Sail. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakRobustTrace
                            WeakRobustGraph.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(** ** DELIVERABLE 3, part 1: the GENERIC finite topological sort

    Nothing here mentions [gev]: the sort needs only a decidable acyclic
    relation and a duplicate-free finite carrier. *)

Section topo_generic.
  Context {A : Type}.
  Context (R : A → A → Prop).
  Context `{!RelDecision R}.

  (** THE DECIDABILITY SPEND.  Scanning [scan] (a sublist of the carrier
      [rem]), either we exhibit an element of [rem] with no R-predecessor
      in [rem], or every scanned element has one.  Constructive: the case
      split is [decide (Exists …)], not excluded middle. *)
  Lemma topo_scan (rem : list A) :
    ∀ scan : list A, (∀ x, x ∈ scan → x ∈ rem) →
      (∃ m, m ∈ rem ∧ ∀ x, x ∈ rem → ¬ R x m) ∨
      (∀ m, m ∈ scan → ∃ x, x ∈ rem ∧ R x m).
  Proof.
    intros scan. induction scan as [|a scan IH]; intros Hsub.
    - right. intros m Hm. by apply elem_of_nil in Hm.
    - have Hsub' : ∀ x, x ∈ scan → x ∈ rem.
      { intros x Hx. apply Hsub, elem_of_cons. by right. }
      destruct (decide (Exists (λ x, R x a) rem)) as [Hex|Hex].
      + destruct (IH Hsub') as [Hmin|Hall]; [by left|].
        right. intros m Hm. apply elem_of_cons in Hm as [->|Hm].
        * apply list_relations.Exists_exists in Hex as (x & Hx & HR).
          exists x. split; [exact Hx|exact HR].
        * by apply Hall.
      + left. exists a. split.
        { apply Hsub, elem_of_cons. by left. }
        intros x Hx HR. apply Hex, list_relations.Exists_exists.
        exists x. split; [exact Hx|exact HR].
  Qed.

  (** THE CHAIN.  If every element of [rem] has an R-predecessor in [rem],
      one can walk backwards from any element for any number of steps.  The
      invariant is that LATER entries are [tc R]-predecessors of EARLIER
      ones. *)
  Lemma topo_chain (rem : list A) :
    (∀ m, m ∈ rem → ∃ x, x ∈ rem ∧ R x m) →
    ∀ n y, y ∈ rem → ∃ l,
      length l = S n ∧ (∀ z, z ∈ l → z ∈ rem) ∧ l !! 0%nat = Some y ∧
      (∀ i j x z, (i < j)%nat → l !! i = Some x → l !! j = Some z → tc R z x).
  Proof.
    intros Hall n. induction n as [|n IH]; intros y Hy.
    - exists [y]. split_and!.
      + done.
      + intros z Hz. by apply elem_of_list_singleton in Hz as ->.
      + done.
      + intros i j x z Hij Hi Hj. exfalso.
        apply lookup_lt_Some in Hj. simpl in Hj. lia.
    - destruct (Hall y Hy) as (x & Hx & HR).
      destruct (IH x Hx) as (l & Hlen & Hin & H0 & Hord).
      exists (y :: l). split_and!.
      + simpl. by rewrite Hlen.
      + intros z Hz. apply elem_of_cons in Hz as [->|Hz]; [done|by apply Hin].
      + done.
      + intros i j x' z Hij Hi Hj.
        destruct i as [|i]; simpl in Hi.
        * injection Hi as <-.
          destruct j as [|j]; [lia|]. simpl in Hj.
          destruct j as [|j].
          -- rewrite H0 in Hj. injection Hj as <-. by apply tc_once.
          -- have Hzx : tc R z x by eapply (Hord 0%nat (S j)); [lia|exact H0|exact Hj].
             by eapply tc_r.
        * destruct j as [|j]; [lia|]. simpl in Hj.
          eapply Hord; [|exact Hi|exact Hj]. lia.
  Qed.

  (** THE MINIMAL ELEMENT, by pigeonhole: a chain of length [|rem| + 1] is
      [NoDup] (acyclicity) and included in [rem], which is impossible. *)
  Lemma topo_min (rem : list A) :
    (∀ x, ¬ tc R x x) → rem ≠ [] → NoDup rem →
    ∃ m, m ∈ rem ∧ ∀ x, x ∈ rem → ¬ R x m.
  Proof.
    intros Racyc Hne Hnd.
    destruct (topo_scan rem rem (λ x H, H)) as [Hmin|Hall]; [exact Hmin|].
    exfalso.
    destruct rem as [|y rem']; [done|].
    have Hy : y ∈ y :: rem' by apply elem_of_list_here.
    destruct (topo_chain (y :: rem') Hall (length (y :: rem')) y Hy)
      as (l & Hlen & Hin & _ & Hord).
    have Hnd' : NoDup l.
    { apply list_relations.NoDup_alt. intros i j x Hi Hj.
      destruct (Nat.lt_trichotomy i j) as [Hlt|[Heq|Hgt]]; [|done|].
      - exfalso. apply (Racyc x). by eapply (Hord i j x x).
      - exfalso. apply (Racyc x). by eapply (Hord j i x x). }
    have Hle : (length l ≤ length (y :: rem'))%nat.
    { apply list_relations.submseteq_length. by apply list_relations.NoDup_submseteq. }
    lia.
  Qed.

  (** THE SORT, by induction on the carrier's length: pop a minimal
      element, recurse. *)
  Lemma topo_sort_aux :
    (∀ x, ¬ tc R x x) →
    ∀ n (rem : list A), length rem = n → NoDup rem →
    ∃ order, NoDup order ∧ (∀ e, e ∈ order ↔ e ∈ rem) ∧
      (∀ i j x y, order !! i = Some x → order !! j = Some y → R x y →
                  (i < j)%nat).
  Proof.
    intros Racyc n. induction n as [|n IH]; intros rem Hlen Hnd.
    - apply nil_length_inv in Hlen as ->.
      exists []. split_and!.
      + apply NoDup_nil_2.
      + intros e. by rewrite elem_of_nil.
      + intros i j x y Hi. by rewrite lookup_nil in Hi.
    - have Hne : rem ≠ [].
      { intros ->. simpl in Hlen. lia. }
      destruct (topo_min rem Racyc Hne Hnd) as (m & Hm & Hmin).
      destruct (elem_of_list_split rem m Hm) as (l1 & l2 & ->).
      have Hlen' : length (l1 ++ l2) = n.
      { rewrite length_app. rewrite length_app /= in Hlen. lia. }
      have Hsplit : NoDup (l1 ++ l2) ∧ m ∉ l1 ++ l2.
      { apply list_relations.NoDup_app in Hnd as (H1 & H2 & H3).
        apply list_relations.NoDup_cons in H3 as (H3 & H4).
        split.
        - apply list_relations.NoDup_app. split_and!; [done| |done].
          intros x Hx Hx2. apply (H2 x Hx), elem_of_cons. by right.
        - rewrite elem_of_app. intros [Hc|Hc]; [|done].
          apply (H2 m Hc), elem_of_cons. by left. }
      destruct Hsplit as [Hnd' Hmnot].
      destruct (IH (l1 ++ l2) Hlen' Hnd') as (order & Hndo & Hmem & Hord).
      exists (m :: order). split_and!.
      + apply NoDup_cons_2; [|done]. rewrite Hmem. exact Hmnot.
      + intros e. rewrite elem_of_cons Hmem !elem_of_app elem_of_cons. tauto.
      + intros i j x y Hi Hj HR.
        destruct j as [|j]; simpl in Hj.
        * (* the head is minimal: nothing in the carrier points AT it *)
          exfalso. injection Hj as <-.
          have Hx : x ∈ m :: order by eapply elem_of_list_lookup_2.
          apply (Hmin x); [|done].
          apply elem_of_cons in Hx as [->|Hx]; [done|].
          apply Hmem in Hx. rewrite elem_of_app in Hx.
          rewrite elem_of_app elem_of_cons. tauto.
        * destruct i as [|i]; simpl in Hi; [lia|].
          have Hlt := Hord i j x y Hi Hj HR. lia.
  Qed.

  Theorem topo_sort (rem : list A) :
    (∀ x, ¬ tc R x x) → NoDup rem →
    ∃ order, NoDup order ∧ (∀ e, e ∈ order ↔ e ∈ rem) ∧
      (∀ i j x y, order !! i = Some x → order !! j = Some y → R x y →
                  (i < j)%nat).
  Proof. intros Racyc Hnd. by eapply (topo_sort_aux Racyc (length rem)). Qed.

End topo_generic.

(* ------------------------------------------------------------------ *)
Section lin.
  Context {P : Type}.

  Implicit Types TS : ptraces P.
  Implicit Types e : gev.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 1: THE EVENT ENUMERATION *)

  (** All events of the trace list [Ts], whose first trace is agent [i]. *)
  Fixpoint gev_enum_from (i : nat) (Ts : list (atrace P)) : list gev :=
    match Ts with
    | [] => []
    | T :: Ts' =>
        ((λ k, (i, k)) <$> seq 0 (length (at_evs T))) ++ gev_enum_from (S i) Ts'
    end.

  Definition gev_enum TS : list gev := gev_enum_from 0 (pt_trs TS).

  Lemma elem_of_gev_enum_from i Ts e :
    e ∈ gev_enum_from i Ts ↔
    ∃ j T, Ts !! j = Some T ∧ e.1 = (i + j)%nat ∧ (e.2 < length (at_evs T))%nat.
  Proof.
    revert i. induction Ts as [|T Ts IH]; intros i; simpl.
    - rewrite elem_of_nil. split; [done|].
      intros (j & T & HT & _). by rewrite lookup_nil in HT.
    - rewrite elem_of_app elem_of_list_fmap IH. split.
      + intros [(k & -> & Hk)|(j & T' & HT & Hj & Hlt)].
        * apply elem_of_seq in Hk. exists 0%nat, T. simpl.
          split_and!; [done|lia|lia].
        * exists (S j), T'. simpl. split_and!; [done|lia|done].
      + intros (j & T' & HT & Hj & Hlt). destruct j as [|j]; simpl in HT.
        * injection HT as <-. left. exists e.2. split.
          -- destruct e as [a k]. simpl in Hj |- *. f_equal. lia.
          -- apply elem_of_seq. lia.
        * right. exists j, T'. split_and!; [done|lia|done].
  Qed.

  Lemma gev_enum_from_ge i Ts e : e ∈ gev_enum_from i Ts → (i ≤ e.1)%nat.
  Proof.
    intros (j & T & _ & Hj & _)%elem_of_gev_enum_from. lia.
  Qed.

  Lemma NoDup_gev_enum_from i Ts : NoDup (gev_enum_from i Ts).
  Proof.
    revert i. induction Ts as [|T Ts IH]; intros i; simpl.
    - apply NoDup_nil_2.
    - apply list_relations.NoDup_app. split_and!.
      + apply NoDup_fmap_2_strong; [|apply NoDup_seq].
        intros k1 k2 _ _ Heq. by injection Heq.
      + intros e (k & -> & _)%elem_of_list_fmap He2.
        apply gev_enum_from_ge in He2. simpl in He2. lia.
      + apply IH.
  Qed.

  Lemma length_gev_enum_from i Ts :
    length (gev_enum_from i Ts) = sum_list_with (λ T, length (at_evs T)) Ts.
  Proof.
    revert i. induction Ts as [|T Ts IH]; intros i; simpl; [done|].
    by rewrite length_app length_fmap length_seq IH.
  Qed.

  (** COMPLETENESS: the enumeration is exactly the set of well-formed
      events. *)
  Lemma elem_of_gev_enum TS e : e ∈ gev_enum TS ↔ gev_wf TS e.
  Proof.
    rewrite /gev_enum elem_of_gev_enum_from gev_wf_bounds. split.
    - intros (j & T & HT & Hj & Hlt). exists T.
      have -> : e.1 = j by lia.
      by split.
    - intros (T & HT & Hlt). exists e.1, T. split_and!; [done|lia|done].
  Qed.

  Lemma NoDup_gev_enum TS : NoDup (gev_enum TS).
  Proof. apply NoDup_gev_enum_from. Qed.

  (** The CARDINALITY: the sum of the trace lengths. *)
  Lemma length_gev_enum TS :
    length (gev_enum TS) = sum_list_with (λ T, length (at_evs T)) (pt_trs TS).
  Proof. apply length_gev_enum_from. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 2: DECIDABILITY of the graph relations

      Every quantifier is bounded by a list lookup, so all of these are
      plain [Decision] instances — no classical axiom, and no boolean
      reflection layer needed. *)

  Global Instance gev_wf_dec TS e : Decision (gev_wf TS e).
  Proof. rewrite /gev_wf. apply _. Qed.

  Global Instance gev_ts_eq_dec TS e (o : option nat) :
    Decision (gev_ts TS e = o).
  Proof. apply _. Qed.

  Global Instance gev_reads_dec TS e a ts : Decision (gev_reads TS e a ts).
  Proof.
    rewrite /gev_reads.
    destruct (gev_lb TS e) as [l|].
    - destruct (decide ((a, ts) ∈ lb_reads l)) as [Hin|Hin].
      + left. by exists l.
      + right. intros (l' & Hl' & Hin'). injection Hl' as <-. by apply Hin.
    - right. by intros (l' & Hl' & _).
  Qed.

  Global Instance gpo_dec TS e1 e2 : Decision (gpo TS e1 e2).
  Proof. rewrite /gpo. apply _. Qed.

  (** [grf]'s two existentials are bounded: [ts] by the source's [gev_ts]
      (ONE [option]) and [a] by the reader's [lb_reads] (a concrete list),
      so the relation reflects into an [Exists] over that list. *)
  Global Instance grf_dec TS e1 e2 : Decision (grf TS e1 e2).
  Proof.
    rewrite /grf /gev_reads.
    destruct (gev_ts TS e1) as [ts|]; [|by right; intros (? & ? & ? & _)].
    destruct (gev_lb TS e2) as [l|];
      [|by right; intros (? & ? & _ & ? & ? & _)].
    destruct (decide (Exists (λ p : Z * nat, p.2 = ts) (lb_reads l)))
      as [Hex|Hex].
    - left. apply list_relations.Exists_exists in Hex as ([a t] & Hin & Ht).
      simpl in Ht. subst t. exists ts, a. split; [done|]. by exists l.
    - right. intros (ts' & a & Hts & l' & Hl' & Hin).
      injection Hts as <-. injection Hl' as <-.
      apply Hex, list_relations.Exists_exists. by exists (a, ts).
  Qed.

  Global Instance gdep_dec TS e1 e2 : Decision (gdep TS e1 e2).
  Proof. rewrite /gdep. apply _. Qed.

  Global Instance gpo_rel_dec TS : RelDecision (gpo TS).
  Proof. intros e1 e2. apply _. Qed.
  Global Instance grf_rel_dec TS : RelDecision (grf TS).
  Proof. intros e1 e2. apply _. Qed.
  Global Instance gdep_rel_dec TS : RelDecision (gdep TS).
  Proof. intros e1 e2. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 3: THE LINEARIZATION *)

  (** The packaged form of the conclusion, so the increments below (and
      W2b) can quantify over "a topological order of [TS]". *)
  Definition topo_order TS (order : list gev) : Prop :=
    NoDup order ∧
    (∀ e, e ∈ order ↔ gev_wf TS e) ∧
    (∀ x y i j, order !! i = Some x → order !! j = Some y → gdep TS x y →
                (i < j)%nat).

  Theorem gdep_toposort TS :
    gdep_acyclic TS →
    ∃ order : list gev,
      NoDup order ∧
      (∀ e, e ∈ order ↔ gev_wf TS e) ∧
      (∀ x y i j, order !! i = Some x → order !! j = Some y → gdep TS x y →
                  (i < j)%nat).
  Proof.
    intros Hacyc.
    destruct (topo_sort (gdep TS) (gev_enum TS) Hacyc (NoDup_gev_enum TS))
      as (order & Hnd & Hmem & Hord).
    exists order. split_and!; [done| |].
    - intros e. rewrite Hmem. apply elem_of_gev_enum.
    - intros x y i j Hi Hj Hd. by eapply Hord.
  Qed.

  Corollary gdep_toposort_pack TS :
    gdep_acyclic TS → ∃ order, topo_order TS order.
  Proof.
    intros Hacyc. destruct (gdep_toposort TS Hacyc) as (order & ? & ? & ?).
    exists order. by split_and!.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** INCREMENT (a): [order_index] — each wf event's position *)

  Definition gev_index (order : list gev) e : option nat :=
    fst <$> list_find (λ x, x = e) order.

  Lemma gev_index_Some order e :
    e ∈ order → ∃ i, gev_index order e = Some i ∧ order !! i = Some e.
  Proof.
    intros He.
    have [[i x] Hf] : is_Some (list_find (λ x, x = e) order).
    { by eapply list_find_elem_of. }
    rewrite /gev_index Hf /=.
    apply list_find_Some in Hf as (Hl & -> & _). by exists i.
  Qed.

  Lemma gev_index_None order e : e ∉ order → gev_index order e = None.
  Proof.
    intros He. rewrite /gev_index.
    have -> : list_find (λ x, x = e) order = None; [|done].
    apply list_find_None, list_relations.Forall_forall. intros x Hx ->. by apply He.
  Qed.

  (** THE CHARACTERIZATION: on a [NoDup] list the index is exactly the
      lookup position. *)
  Lemma gev_index_lookup order i e :
    NoDup order → order !! i = Some e → gev_index order e = Some i.
  Proof.
    intros Hnd Hi.
    have He : e ∈ order by eapply elem_of_list_lookup_2.
    destruct (gev_index_Some order e He) as (i' & Hidx & Hi').
    have Heq : i' = i by eapply list_relations.NoDup_lookup.
    by rewrite Hidx Heq.
  Qed.

  (** Every wf event has a position, and it is unique. *)
  Lemma topo_order_index TS order e :
    topo_order TS order → gev_wf TS e →
    ∃ i, gev_index order e = Some i ∧ order !! i = Some e.
  Proof.
    intros (Hnd & Hmem & _) Hwf. apply gev_index_Some, Hmem, Hwf.
  Qed.

  Lemma topo_order_index_unique TS order i j e :
    topo_order TS order → order !! i = Some e → order !! j = Some e → i = j.
  Proof. intros (Hnd & _ & _) Hi Hj. by eapply list_relations.NoDup_lookup. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** INCREMENT (b): PREFIX CLOSURE

      No [gdep] edge points from OUTSIDE a prefix of [order] INTO it —
      the ordering property restated in the form the W2b induction
      consumes. *)

  Lemma topo_prefix_closed TS order n x y :
    topo_order TS order → gdep TS x y → y ∈ take n order → x ∈ take n order.
  Proof.
    intros (Hnd & Hmem & Hord) Hd Hy.
    apply elem_of_take in Hy as (j & Hj & Hjn).
    have Hxwf : gev_wf TS x by apply (gdep_wf TS x y Hd).
    have Hx : x ∈ order by apply Hmem.
    apply elem_of_list_lookup in Hx as (i & Hi).
    have Hlt : (i < j)%nat by eapply Hord.
    apply elem_of_take. exists i. split; [done|lia].
  Qed.

  (** The same fact at the exact step the induction takes: when [e] sits at
      position [n], every [gdep]-predecessor of [e] is already in the
      processed prefix [take n order]. *)
  Lemma topo_pred_done TS order n e :
    topo_order TS order → order !! n = Some e →
    ∀ e', gdep TS e' e → e' ∈ take n order.
  Proof.
    intros (Hnd & Hmem & Hord) Hn e' Hd.
    have Hwf : gev_wf TS e' by apply (gdep_wf TS e' e Hd).
    have He' : e' ∈ order by apply Hmem.
    apply elem_of_list_lookup in He' as (i & Hi).
    have Hlt : (i < n)%nat by eapply Hord.
    apply elem_of_take. exists i. by split.
  Qed.

  (** …and the element at position [n] is fresh. *)
  Lemma topo_not_in_prefix TS order n e :
    topo_order TS order → order !! n = Some e → e ∉ take n order.
  Proof.
    intros (Hnd & _ & _) Hn He.
    apply elem_of_take in He as (i & Hi & Hin).
    have Heq : i = n by eapply list_relations.NoDup_lookup. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** ** INCREMENT (c): PER-AGENT MONOTONICITY

      The subsequence of [order] belonging to one agent is increasing in
      the step index.  Both directions, and no [ptraces_wf] needed: the
      forward direction is [gpo ⊆ gdep] (whose [gev_wf] side conditions
      membership in [order] supplies), the backward direction is that same
      edge the other way round plus [NoDup]. *)

  Lemma topo_agent_lt TS order i j x y :
    topo_order TS order → order !! i = Some x → order !! j = Some y →
    x.1 = y.1 → (x.2 < y.2)%nat → (i < j)%nat.
  Proof.
    intros (Hnd & Hmem & Hord) Hi Hj Hag Hk.
    eapply Hord; [exact Hi|exact Hj|]. left. split_and!; [done|done| |].
    - apply Hmem. by eapply elem_of_list_lookup_2.
    - apply Hmem. by eapply elem_of_list_lookup_2.
  Qed.

  Lemma topo_agent_mono TS order i j x y :
    topo_order TS order → order !! i = Some x → order !! j = Some y →
    x.1 = y.1 → ((i < j)%nat ↔ (x.2 < y.2)%nat).
  Proof.
    intros Ho Hi Hj Hag. split; [|by eapply topo_agent_lt].
    intros Hij.
    destruct (Nat.lt_trichotomy x.2 y.2) as [Hlt|[Heq|Hgt]]; [done| |].
    - (* equal step index and equal agent: the SAME event, so i = j *)
      exfalso.
      have Hxy : x = y.
      { destruct x as [a1 k1], y as [a2 k2]. simpl in Hag, Heq. by subst. }
      subst y. have : i = j by eapply (topo_order_index_unique TS order).
      lia.
    - exfalso.
      have Hji : (j < i)%nat by eapply (topo_agent_lt TS order j i y x).
      lia.
  Qed.

  (** The [gdep]-flavoured restatement: a same-agent [gdep] edge is a
      forward step in [order].  (Immediate from the ordering property; kept
      because it is the shape [gdep_same_agent_lt] hands over.) *)
  Lemma topo_gdep_forward TS order i j x y :
    topo_order TS order → order !! i = Some x → order !! j = Some y →
    gdep TS x y → (i < j)%nat.
  Proof. intros (_ & _ & Hord) Hi Hj Hd. by eapply Hord. Qed.

  (* ---------------------------------------------------------------- *)
  (** ** DELIVERABLE 4: THE INDUCTION PRINCIPLE

      The interface W2b consumes: process the events in topological order,
      each step knowing that ALL of its [gdep]-predecessors are already in
      the processed prefix. *)

  Lemma toposort_ind TS (Q : list gev → Prop) :
    gdep_acyclic TS →
    Q [] →
    (∀ done e,
       Q done →
       gev_wf TS e → e ∉ done →
       (∀ e', gdep TS e' e → e' ∈ done) →
       Q (done ++ [e])) →
    ∃ order,
      Q order ∧
      NoDup order ∧
      (∀ e, e ∈ order ↔ gev_wf TS e) ∧
      (∀ x y i j, order !! i = Some x → order !! j = Some y → gdep TS x y →
                  (i < j)%nat).
  Proof.
    intros Hacyc Hnil Hstep.
    destruct (gdep_toposort_pack TS Hacyc) as (order & Ho).
    have Hpre : ∀ n, Q (take n order).
    { intros n. induction n as [|n IH]; [by rewrite take_0|].
      destruct (order !! n) as [e|] eqn:Hn.
      - rewrite (take_S_r order n e Hn). apply Hstep.
        + exact IH.
        + destruct Ho as (_ & Hmem & _). apply Hmem.
          by eapply elem_of_list_lookup_2.
        + by eapply topo_not_in_prefix.
        + intros e' Hd. by eapply topo_pred_done.
      - (* past the end: the prefix does not grow *)
        have Hge : (length order ≤ n)%nat.
        { apply not_lt. intros Hlt.
          have [e He] : is_Some (order !! n) by apply lookup_lt_is_Some_2.
          by rewrite Hn in He. }
        have H1 : take (S n) order = order by apply take_ge; lia.
        have H2 : take n order = order by apply take_ge; lia.
        rewrite H2 in IH. by rewrite H1. }
    exists order. destruct Ho as (Hnd & Hmem & Hord). split_and!; [|done|done|done].
    have Hfull : take (length order) order = order by apply take_ge; lia.
    specialize (Hpre (length order)). by rewrite Hfull in Hpre.
  Qed.

End lin.

(* ------------------------------------------------------------------ *)
(** ** What W2b inherits from this file

    - [gev_enum] / [elem_of_gev_enum] / [NoDup_gev_enum] / [length_gev_enum]:
      the finite carrier the induction is over, with its cardinality.
    - The [Decision] instances: [gdep] (and its two halves) is decidable, so
      the sort is constructive.  No classical axiom is used anywhere below
      [gdep_toposort].
    - [gdep_toposort] / [topo_order]: the topological order itself.
    - [gev_index]: the position function, with [gev_index_lookup] pinning it
      to the lookup index on a [NoDup] list.
    - [topo_pred_done] / [topo_prefix_closed]: the prefix-closure property in
      the exact form the delay-simulation's step case consumes.
    - [topo_agent_mono]: per-agent monotonicity, so the pf run's per-agent
      program-state chain can be read straight off the order.
    - [toposort_ind]: the induction principle — this is the entry point.

    NOT here, deliberately: any use of [ptraces_wf]/[pstep] (the sort is a
    function of the trace bundle alone), any timestamp permutation π, and
    any simulation relation — those are W2b slice 2. *)

