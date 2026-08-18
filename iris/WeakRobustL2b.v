(** * WeakRobustL2b.v — L2-M2: THE ACYCLICITY THEOREM'S SKELETON

    [claude-notes/design/weak-memory-layer2.md] stages Layer 2 as a DIRECT
    acyclicity theorem.  L2-M1 ([WeakRobustL2.v]) delivered the MACHINE
    FACTS of the case tree; this file delivers the SKELETON that consumes
    them:

    - **§1 THE SCC SKELETON.**  Over the finite event graph
      ([WeakRobustLin.gev_enum]) and any DECIDABLE edge relation, the
      strongly connected components of the events that lie on a cycle
      have a MINIMAL one — minimal in the SCC DAG, i.e. no event of it
      has a strict ancestor that is itself on a cycle and outside the
      component.  The descent is on [length (sanc …)], the computed
      ancestor closure of [WeakRobustMain]'s [anc]: a strictly lower
      on-cycle ancestor has a STRICTLY SMALLER ancestor set (its own
      ancestors are ancestors of the old root, and the old root is not
      one of them).  Everything is decidable through [anc]: [tc R x y]
      holds iff some [R]-successor of [x] is in [anc R _ y], which is a
      [Exists] over a computed list.

    - **§2 THE STRICT ANCESTRY [Uanc] IS ACYCLIC AND DOWNWARD CLOSED**,
      hence REPLAYABLE.  [WeakRobustMain.cone_Qinv] replays the
      [gdep3]-ancestry of ONE root and needs that root off every cycle —
      which a segment head is NOT.  [U_Qinv] below is the minimal
      generalization: it replays ANY decidable, downward-closed,
      acyclic set of events.  Instantiated at [Uanc], it puts the
      machine in a pf-reachable configuration whose agent [j] sits
      EXACTLY at the pre-record of [j]'s segment head
      ([head_prestate_pf_real]).

    - **§3 [sf_edges] — THE SITE FACTS, AS TRACE SHAPES.**  The per-edge
      obligation [WeakRobustMain.edges_split_cyc] asks for [edge_ok_f],
      a statement about the machine's VIEW COMPONENTS.  [sf_edges] asks
      instead for one of FOUR TRACE SHAPES (C1/C2 a fence or an [aq]
      entry, C3 a register dependency chain into a branch, C4 two
      critical-section windows on a common lock word with [win_excl],
      or the message is [bad]) — the things a site can actually
      exhibit.  [sf_edges_edges_split_cyc] discharges [edge_ok_f] from
      them with L2-M1's lemmas, and [edges_split_cyc_sf_edges] is the
      converse, so the two are EQUIVALENT (see the FINDING in §3).

    - **§4 [robust_main_l2]** — [WeakRobustMain.robust_main_acyc] with
      [gdep3_acyclic TS DS] replaced by
      [sf_edges ∧ scc_no_bad ∧ dev_wit_ok].

    FINDING (C5, the bad-edge case at a minimal SCC).  The exhibit
    [WeakRobustMain.bad_edge_violates] CANNOT be run at an SCC event.
    Its hypothesis [bad_min nh TS DS b2] instantiated at the bad edge
    itself already gives [¬ tc (gdep3 TS DS) b2 b2]: the exhibit replays
    the STRICT [gdep3]-ancestor cone OF THE READER and then appends the
    reader, so a reader on a cycle is its own ancestor and the replay is
    circular.  A bad edge entering a minimal SCC is therefore NOT
    refuted inside the SCC.  It is refuted GLOBALLY, off the cycle:
    [bad_wf] says SOME bad edge is minimal, that one lies off every
    cycle, the exhibit applies to it and φ refutes it
    ([WeakRobustMain.no_bad_edge]).  So the no-bad-edge fact is taken
    here as the named hypothesis [scc_no_bad] ("no bad edge targets an
    on-cycle event" — convertible with [WeakRobustMain.bad_wf_strong]),
    with [l2_gdep2_acyclic_phi] recording the φ-derived form for callers
    that would rather supply [bad_wf] and
    [pf_violation_free_hart].

    DEPENDENCY-FREE like its parents: stdpp only, no Iris, no Sail. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakAxiomatic.
From xv6iris Require Import WeakMem WeakPromise WeakPromiseFact WeakPromiseBridge
                            WeakRobustTrace
                            WeakRobustGraph WeakRobust WeakRobustProv
                            WeakRobustAcyc WeakRobustLin WeakRobustOrd
                            WeakRobustSer WeakRobustAcyc2 WeakRobustSim
                            WeakRobustMain WeakRobustDisc WeakRobustL2.

Local Open Scope Z_scope.

(* ================================================================== *)
(** ** 0. TWO GENERIC INVERSIONS

    stdpp's [tc] has no left/right inversion lemma; both are one
    [destruct]/[induction]. *)

Lemma tc_inv_left {A : Type} (R : A → A → Prop) x z :
  tc R x z → R x z ∨ ∃ y, R x y ∧ tc R y z.
Proof. destruct 1 as [x' y' HR|x' y' z' HR Htc]; [by left|right; by exists y']. Qed.

(* ================================================================== *)
(** ** 1. THE SCC SKELETON

    Generic in the edge relation [R] on [gev]: the instances are
    [gdep2 TS] (the design's graph) and [gdep3 TS DS] (the one the
    fabric-carrying replay is closed under). *)

Definition sccR (R : gev → gev → Prop) (e f : gev) : Prop :=
  rtc R e f ∧ rtc R f e.

Definition oncycR (R : gev → gev → Prop) (e : gev) : Prop := tc R e e.

(** The computed ancestor closure of one event, over the whole event
    enumeration ([WeakRobustMain.anc]). *)
Definition sanc {P D : Type} (TS : ptraces P D) (R : gev → gev → Prop)
    `{!RelDecision R} (e : gev) : list gev := anc R (gev_enum TS) e.


(** [tc R x y] is DECIDABLE: it says some [R]-successor of [x] lies in
    the computed ancestry of [y]. *)
Definition tcb {P D : Type} (TS : ptraces P D) (R : gev → gev → Prop)
    `{!RelDecision R} (x y : gev) : Prop :=
  gev_wf TS y ∧ Exists (λ z, R x z) (sanc TS R y).

Global Instance tcb_dec {P D : Type} (TS : ptraces P D) (R : gev → gev → Prop)
    `{!RelDecision R} x y : Decision (tcb TS R x y).
Proof. rewrite /tcb. apply _. Defined.

(** The reflexive-transitive and the SCC predicates, decidably. *)
Definition rtcb {P D : Type} (TS : ptraces P D) (R : gev → gev → Prop)
    `{!RelDecision R} (x y : gev) : Prop := x = y ∨ tcb TS R x y.

Definition sccb {P D : Type} (TS : ptraces P D) (R : gev → gev → Prop)
    `{!RelDecision R} (e f : gev) : Prop := rtcb TS R e f ∧ rtcb TS R f e.

Global Instance rtcb_dec {P D : Type} (TS : ptraces P D) (R : gev → gev → Prop)
    `{!RelDecision R} x y : Decision (rtcb TS R x y).
Proof. rewrite /rtcb. apply _. Defined.

Global Instance sccb_dec {P D : Type} (TS : ptraces P D) (R : gev → gev → Prop)
    `{!RelDecision R} e f : Decision (sccb TS R e f).
Proof. rewrite /sccb. apply _. Defined.

Definition oncycb {P D : Type} (TS : ptraces P D) (R : gev → gev → Prop)
    `{!RelDecision R} (e : gev) : Prop := tcb TS R e e.

Global Instance oncycb_dec {P D : Type} (TS : ptraces P D) (R : gev → gev → Prop)
    `{!RelDecision R} e : Decision (oncycb TS R e).
Proof. rewrite /oncycb. apply _. Defined.


(* ------------------------------------------------------------------ *)
(** *** MINIMALITY IN THE SCC DAG

    [f]'s component is minimal iff no on-cycle event OUTSIDE it is a
    strict ancestor of [f].  Stated as the negation of a decidable
    [Exists] so that both the decision and the WITNESS extraction are
    free. *)
Definition sccR_min {P D : Type} (TS : ptraces P D) (R : gev → gev → Prop)
    `{!RelDecision R} (f : gev) : Prop :=
  ¬ Exists (λ x, oncycb TS R x ∧ tcb TS R x f ∧ ¬ sccb TS R f x) (gev_enum TS).

Global Instance sccR_min_dec {P D : Type} (TS : ptraces P D)
    (R : gev → gev → Prop) `{!RelDecision R} f : Decision (sccR_min TS R f).
Proof. rewrite /sccR_min. apply _. Defined.

(** THE STRICT ANCESTRY of [f]'s component — the design's [U]. *)
Definition Uanc {P D : Type} (TS : ptraces P D) (R : gev → gev → Prop)
    `{!RelDecision R} (f x : gev) : Prop :=
  tcb TS R x f ∧ ¬ sccb TS R f x.

Global Instance Uanc_dec {P D : Type} (TS : ptraces P D) (R : gev → gev → Prop)
    `{!RelDecision R} f x : Decision (Uanc TS R f x).
Proof. rewrite /Uanc. apply _. Defined.

(** THE SEGMENT HEAD: the least-index event of its agent in [f]'s
    component. *)
Definition scc_headR {P D : Type} (TS : ptraces P D) (R : gev → gev → Prop)
    `{!RelDecision R} (f h : gev) : Prop :=
  sccR R f h ∧ ∀ k, (k < h.2)%nat → ¬ sccR R f (h.1, k).

Section scc_generic.
  Context {P D : Type}.
  Context (TS : ptraces P D).
  Context (R : gev → gev → Prop).
  Context `{Rdec : !RelDecision R}.
  Context (Rwf : ∀ x y, R x y → gev_wf TS x ∧ gev_wf TS y).
  Context (Rpo : ∀ x y, gpo TS x y → R x y).

  (* ---------------------------------------------------------------- *)
  (** *** The equivalence-relation facts *)

  Lemma sccR_refl e : sccR R e e.
  Proof. by split. Qed.

  Lemma sccR_sym e f : sccR R e f → sccR R f e.
  Proof. by intros [H1 H2]; split. Qed.

  Lemma sccR_trans e f g : sccR R e f → sccR R f g → sccR R e g.
  Proof. intros [H1 H2] [H3 H4]. split; etrans; eauto. Qed.

  (** An SCC of an on-cycle event consists of on-cycle events. *)
  Lemma oncycR_sccR e f : oncycR R e → sccR R e f → oncycR R f.
  Proof.
    rewrite /oncycR /sccR. intros Hc [Hef Hfe].
    eapply tc_rtc_l; [exact Hfe|]. eapply tc_rtc_r; [exact Hc|exact Hef].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** Well-formedness along the relation *)


  Lemma tc_wf_l x y : tc R x y → gev_wf TS x.
  Proof.
    intros Htc. apply tc_inv_left in Htc as [HR|(z & HR & _)];
      by apply (Rwf _ _ HR).
  Qed.

  Lemma tc_wf_r x y : tc R x y → gev_wf TS y.
  Proof.
    induction 1 as [x' y' HR|x' y' z' HR Htc IH]; [by apply (Rwf _ _ HR)|done].
  Qed.

  Lemma oncycR_wf e : oncycR R e → gev_wf TS e.
  Proof. apply tc_wf_l. Qed.

  (* ---------------------------------------------------------------- *)
  (** *** [sanc] and the decidability it buys *)

  Lemma elem_of_sanc e x :
    gev_wf TS e → (x ∈ sanc TS R e ↔ (x = e ∨ tc R x e)).
  Proof.
    intros He. rewrite /sanc.
    apply (elem_of_anc R (gev_enum TS) e).
    - by apply elem_of_gev_enum.
    - intros u v Huv. apply elem_of_gev_enum. by apply (Rwf u v Huv).
    - apply NoDup_gev_enum.
  Qed.

  Lemma self_in_sanc e : gev_wf TS e → e ∈ sanc TS R e.
  Proof. intros He. apply (elem_of_sanc e e He). by left. Qed.


  Lemma tcb_iff x y : tcb TS R x y ↔ tc R x y.
  Proof.
    rewrite /tcb. split.
    - intros [Hy Hex]. apply list_relations.Exists_exists in Hex as (z & Hz & HR).
      apply (elem_of_sanc y z Hy) in Hz as [Heq|Htc].
      + subst z. by apply tc_once.
      + by eapply tc_l.
    - intros Htc. split; [by eapply tc_wf_r|].
      apply list_relations.Exists_exists.
      apply tc_inv_left in Htc as [HR|(z & HR & Htc)].
      + exists y. split; [|done].
        apply (elem_of_sanc y y); [by apply (Rwf _ _ HR)|by left].
      + exists z. split; [|done].
        apply (elem_of_sanc y z); [by eapply tc_wf_r|by right].
  Qed.

  Lemma rtcb_iff x y : rtcb TS R x y ↔ rtc R x y.
  Proof. rewrite /rtcb rtc_tc tcb_iff //. Qed.

  Lemma sccb_iff e f : sccb TS R e f ↔ sccR R e f.
  Proof. rewrite /sccb /sccR !rtcb_iff //. Qed.

  Lemma oncycb_iff e : oncycb TS R e ↔ oncycR R e.
  Proof. rewrite /oncycb /oncycR tcb_iff //. Qed.


  Lemma sccR_min_spec f x :
    sccR_min TS R f → oncycR R x → tc R x f → sccR R f x.
  Proof.
    intros Hmin Hc Htc.
    destruct (decide (sccb TS R f x)) as [Hs|Hs];
      [by apply sccb_iff|exfalso].
    apply Hmin, list_relations.Exists_exists. exists x. split_and!.
    - apply elem_of_gev_enum. by eapply oncycR_wf.
    - by apply oncycb_iff.
    - by apply tcb_iff.
    - exact Hs.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** The descent measure: the ancestor set shrinks strictly *)

  Lemma sanc_incl e x :
    gev_wf TS e → tc R x e → ∀ z, z ∈ sanc TS R x → z ∈ sanc TS R e.
  Proof.
    intros He Htc z Hz.
    have Hx : gev_wf TS x by eapply tc_wf_l.
    apply (elem_of_sanc x z Hx) in Hz as [Heq|Hzx].
    - subst z. apply (elem_of_sanc e x He). by right.
    - apply (elem_of_sanc e z He). right. by etrans.
  Qed.

  Lemma sanc_len_lt e x :
    gev_wf TS e → tc R x e → ¬ rtc R e x →
    (length (sanc TS R x) < length (sanc TS R e))%nat.
  Proof.
    intros He Htc Hnr.
    have Hx : gev_wf TS x by eapply tc_wf_l.
    have Hnd : NoDup (sanc TS R x).
    { rewrite /sanc /anc. by apply anc_iter_nodup, NoDup_gev_enum. }
    have Henot : e ∉ sanc TS R x.
    { intros Hin. apply (elem_of_sanc x e Hx) in Hin as [Heq|Hc].
      - apply Hnr. subst e. reflexivity.
      - apply Hnr. by apply tc_rtc. }
    have Hsub : ∀ z, z ∈ (e :: sanc TS R x) → z ∈ sanc TS R e.
    { intros z. rewrite elem_of_cons. intros [Heq|Hz].
      - subst z. by apply self_in_sanc.
      - by eapply sanc_incl. }
    have Hnd2 : NoDup (e :: sanc TS R x) by apply NoDup_cons_2.
    have Hle : (length (e :: sanc TS R x) ≤ length (sanc TS R e))%nat.
    { apply list_relations.submseteq_length.
      by apply list_relations.NoDup_submseteq. }
    simpl in Hle. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** EXISTENCE of a minimal nontrivial SCC *)

  Lemma sccR_min_exists_aux n :
    ∀ e, (length (sanc TS R e) ≤ n)%nat → oncycR R e →
    ∃ f, oncycR R f ∧ sccR_min TS R f ∧ rtc R f e.
  Proof.
    induction n as [|n IH]; intros e Hlen Hc.
    - exfalso.
      have He : gev_wf TS e by eapply oncycR_wf.
      have Hin : e ∈ sanc TS R e by apply self_in_sanc.
      apply elem_of_list_lookup in Hin as (i & Hi).
      apply lookup_lt_Some in Hi. lia.
    - destruct (decide (sccR_min TS R e)) as [Hmin|Hmin].
      { exists e. split_and!; [done|done|reflexivity]. }
      apply dec_stable in Hmin.
      apply list_relations.Exists_exists in Hmin
        as (x & _ & Hcx & Htx & Hnsx).
      have Hcx' : oncycR R x by apply oncycb_iff.
      have Htx' : tc R x e by apply tcb_iff.
      have He : gev_wf TS e by eapply oncycR_wf.
      have Hnr : ¬ rtc R e x.
      { intros Hr. apply Hnsx, sccb_iff. split; [exact Hr|].
        by apply tc_rtc. }
      have Hlt := sanc_len_lt e x He Htx' Hnr.
      destruct (IH x ltac:(lia) Hcx') as (f & Hf1 & Hf2 & Hf3).
      exists f. split_and!; [done|done|].
      etrans; [exact Hf3|by apply tc_rtc].
  Qed.

  Theorem sccR_min_exists e :
    oncycR R e → ∃ f, oncycR R f ∧ sccR_min TS R f ∧ rtc R f e.
  Proof.
    intros Hc.
    by apply (sccR_min_exists_aux (length (sanc TS R e)) e (Nat.le_refl _)).
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** [Uanc]: acyclic, downward closed, and it misses the component *)

  Lemma Uanc_iff f x : Uanc TS R f x ↔ (tc R x f ∧ ¬ sccR R f x).
  Proof.
    rewrite /Uanc tcb_iff. split; intros [H1 H2]; split; try done.
    - intros Hs. apply H2. by apply sccb_iff.
    - intros Hs. apply H2. by apply sccb_iff.
  Qed.

  Lemma Uanc_wf f x : Uanc TS R f x → gev_wf TS x.
  Proof. rewrite Uanc_iff. intros [H _]. by eapply tc_wf_l. Qed.

  (** THE KEY MINIMALITY PAYOFF: nothing in the strict ancestry of a
      MINIMAL component is itself on a cycle. *)
  Lemma Uanc_not_oncyc f x :
    sccR_min TS R f → Uanc TS R f x → ¬ oncycR R x.
  Proof.
    rewrite Uanc_iff. intros Hmin [Htc Hns] Hc.
    apply Hns. by eapply sccR_min_spec.
  Qed.

  Lemma Uanc_acyc f x : sccR_min TS R f → Uanc TS R f x → ¬ tc R x x.
  Proof. apply Uanc_not_oncyc. Qed.

  Lemma Uanc_dc f e e' : Uanc TS R f e → R e' e → Uanc TS R f e'.
  Proof.
    rewrite !Uanc_iff. intros [Htc Hns] HR. split; [by eapply tc_l|].
    intros [Hfe' He'f]. apply Hns. split; [|by apply tc_rtc].
    by eapply rtc_r.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** SEGMENT HEADS *)

  Lemma scc_headR_wf f h : oncycR R f → scc_headR TS R f h → gev_wf TS h.
  Proof.
    intros Hc [Hs _]. apply (oncycR_wf h). by apply (oncycR_sccR f h).
  Qed.

  Lemma scc_headR_exists f e :
    sccR R f e → ∃ h, h.1 = e.1 ∧ scc_headR TS R f h.
  Proof.
    destruct e as [j k]. simpl. revert k.
    have Haux : ∀ n k, (k ≤ n)%nat → sccR R f (j, k) →
                  ∃ h, h.1 = j ∧ scc_headR TS R f h.
    { induction n as [|n IH]; intros k Hle Hs.
      - have Hk : k = 0%nat by lia. subst k.
        exists (j, 0%nat). split; [done|]. split; [done|].
        simpl. intros k' Hlt. lia.
      - destruct (decide (Exists (λ k', sccb TS R f (j, k')) (seq 0 k)))
          as [Hex|Hex].
        + apply list_relations.Exists_exists in Hex as (k' & Hk' & Hs').
          apply elem_of_seq in Hk'.
          apply (IH k'); [lia|by apply sccb_iff].
        + exists (j, k). split; [done|]. split; [done|].
          simpl. intros k0 Hlt Hc. apply Hex, list_relations.Exists_exists.
          exists k0. split; [apply elem_of_seq; lia|].
          by apply sccb_iff. }
    intros k Hs. by apply (Haux k k).
  Qed.

  (** EVERY po-PREDECESSOR OF A SEGMENT HEAD IS IN [U] — the fact the
      replay of §2 consumes. *)

  Lemma scc_headR_po_pred f h k :
    oncycR R f → scc_headR TS R f h → (k < h.2)%nat → gev_wf TS (h.1, k) →
    Uanc TS R f (h.1, k).
  Proof.
    intros Hc Hh Hlt Hwfk.
    have Hwfh : gev_wf TS h by eapply scc_headR_wf.
    have Hpo : R (h.1, k) h.
    { apply Rpo. rewrite /gpo. split_and!; [done|simpl;lia|done|done]. }
    apply Uanc_iff. split.
    - eapply tc_rtc_r; [by apply tc_once|apply Hh].
    - apply Hh. simpl. exact Hlt.
  Qed.

  Lemma scc_headR_not_U f h : scc_headR TS R f h → ¬ Uanc TS R f h.
  Proof. intros [Hs _] HU. apply Uanc_iff in HU as [_ Hns]. by apply Hns. Qed.

End scc_generic.


(* ------------------------------------------------------------------ *)
(** *** THE DESIGN'S NAMES, at [R := gdep2 TS]

    [WeakRobustMain.on_cyc TS] IS [oncycR (gdep2 TS)] by definition. *)

Definition scc {P D : Type} (TS : ptraces P D) (e f : gev) : Prop :=
  sccR (gdep2 TS) e f.

Definition scc_min {P D : Type} (TS : ptraces P D) (f : gev) : Prop :=
  sccR_min TS (gdep2 TS) f.

Definition Ustrict {P D : Type} (TS : ptraces P D) (f : gev) : gev → Prop :=
  Uanc TS (gdep2 TS) f.

Theorem scc_min_exists {P D : Type} (TS : ptraces P D) e :
  on_cyc TS e → ∃ f, on_cyc TS f ∧ scc_min TS f ∧ rtc (gdep2 TS) f e.
Proof. apply (sccR_min_exists TS (gdep2 TS) (gdep2_wf TS) e). Qed.

Theorem Ustrict_not_on_cyc {P D : Type} (TS : ptraces P D) f x :
  scc_min TS f → Ustrict TS f x → ¬ on_cyc TS x.
Proof. apply (Uanc_not_oncyc TS (gdep2 TS) (gdep2_wf TS) f x). Qed.

Theorem Ustrict_acyclic {P D : Type} (TS : ptraces P D) f x :
  scc_min TS f → Ustrict TS f x → ¬ tc (gdep2 TS) x x.
Proof. apply (Uanc_acyc TS (gdep2 TS) (gdep2_wf TS) f x). Qed.

Theorem Ustrict_dc {P D : Type} (TS : ptraces P D) f :
  dc TS (gdep2 TS) (Ustrict TS f).
Proof.
  intros e e' HU Hd _. by eapply (Uanc_dc TS (gdep2 TS) (gdep2_wf TS)).
Qed.

Theorem Ustrict_wf {P D : Type} (TS : ptraces P D) f x :
  Ustrict TS f x → gev_wf TS x.
Proof. apply (Uanc_wf TS (gdep2 TS) (gdep2_wf TS) f x). Qed.

(* ------------------------------------------------------------------ *)
(** *** THE SAME NAMES AT [R := gdep3 TS DS]

    The replay of §2 is downward closed under [gdep3 = gdep2 ∪ gdev],
    NOT under [gdep2]: [WeakRobustSim.Qinv_step] hands every
    fabric-touching event the fabric it recorded, so a [gdev]
    predecessor of a replayed event must be replayed too.  The SCC
    skeleton the head-prestate theorem runs on is therefore the
    [gdep3] one.  The two agree on WHICH EVENTS ARE ON A CYCLE
    ([on_cyc_gdep3], under the fabric-order residue [dev_wit_ok]);
    they need not agree on the components themselves, and nothing
    below assumes they do. *)

Definition scc3 {P D : Type} (TS : ptraces P D) (DS : pdevs D) (e f : gev)
  : Prop := sccR (gdep3 TS DS) e f.

Definition scc_min3 {P D : Type} (TS : ptraces P D) (DS : pdevs D) (f : gev)
  : Prop := sccR_min TS (gdep3 TS DS) f.

Definition Ustrict3 {P D : Type} (TS : ptraces P D) (DS : pdevs D) (f : gev)
  : gev → Prop := Uanc TS (gdep3 TS DS) f.

Lemma on_cyc_gdep3 {P D : Type} (TS : ptraces P D) (DS : pdevs D) e :
  ptraces_wit TS DS → dev_wit_ok TS DS →
  (oncycR (gdep3 TS DS) e ↔ on_cyc TS e).
Proof.
  intros Hwit Hwok. rewrite /oncycR /on_cyc. split.
  - intros Hc.
    destruct (decide (oncycb TS (gdep2 TS) e)) as [H|H].
    + by apply (oncycb_iff TS (gdep2 TS) (gdep2_wf TS) e).
    + exfalso. eapply (gdep3_acyclic_at_wit TS DS e Hwit Hwok); [|exact Hc].
      intros Hc2. apply H.
      by apply (oncycb_iff TS (gdep2 TS) (gdep2_wf TS) e).
  - apply tc_subrel. intros u v. apply gdep2_gdep3.
Qed.

Theorem scc_min3_exists {P D : Type} (TS : ptraces P D) (DS : pdevs D) e :
  ptraces_wit TS DS → oncycR (gdep3 TS DS) e →
  ∃ f, oncycR (gdep3 TS DS) f ∧ scc_min3 TS DS f ∧ rtc (gdep3 TS DS) f e.
Proof.
  intros Hwit.
  apply (sccR_min_exists TS (gdep3 TS DS)
           (λ x y Hd, gdep3_wf TS DS x y Hwit Hd) e).
Qed.

Theorem Ustrict3_wf {P D : Type} (TS : ptraces P D) (DS : pdevs D) f x :
  ptraces_wit TS DS → Ustrict3 TS DS f x → gev_wf TS x.
Proof.
  intros Hwit.
  apply (Uanc_wf TS (gdep3 TS DS) (λ x y Hd, gdep3_wf TS DS x y Hwit Hd) f x).
Qed.

Theorem Ustrict3_acyclic {P D : Type} (TS : ptraces P D) (DS : pdevs D) f x :
  ptraces_wit TS DS → scc_min3 TS DS f → Ustrict3 TS DS f x →
  ¬ tc (gdep3 TS DS) x x.
Proof.
  intros Hwit.
  apply (Uanc_acyc TS (gdep3 TS DS) (λ x y Hd, gdep3_wf TS DS x y Hwit Hd) f x).
Qed.

Theorem Ustrict3_dc {P D : Type} (TS : ptraces P D) (DS : pdevs D) f :
  ptraces_wit TS DS → dc TS (gdep3 TS DS) (Ustrict3 TS DS f).
Proof.
  intros Hwit e e' HU Hd _.
  by eapply (Uanc_dc TS (gdep3 TS DS)
               (λ x y Hd', gdep3_wf TS DS x y Hwit Hd')).
Qed.

(** …and, off a MINIMAL component, no ancestor is on a cycle at all —
    the design's "[U] is acyclic because a lower nontrivial SCC would
    contradict minimality". *)
Theorem Ustrict3_not_on_cyc {P D : Type} (TS : ptraces P D) (DS : pdevs D)
    f x :
  ptraces_wit TS DS → dev_wit_ok TS DS →
  scc_min3 TS DS f → Ustrict3 TS DS f x → ¬ on_cyc TS x.
Proof.
  intros Hwit Hwok Hmin HU Hc.
  eapply (Ustrict3_acyclic TS DS f x Hwit Hmin HU).
  by apply (on_cyc_gdep3 TS DS x Hwit Hwok).
Qed.

Theorem scc_head3_exists {P D : Type} (TS : ptraces P D) (DS : pdevs D) f e :
  ptraces_wit TS DS → scc3 TS DS f e →
  ∃ h, h.1 = e.1 ∧ scc_headR TS (gdep3 TS DS) f h.
Proof.
  intros Hwit.
  apply (scc_headR_exists TS (gdep3 TS DS)
           (λ x y Hd, gdep3_wf TS DS x y Hwit Hd) f e).
Qed.

(* ================================================================== *)
(** ** 2. THE REPLAY OF A DOWNWARD-CLOSED ACYCLIC SET

    [WeakRobustMain.cone_Qinv] replays the [gdep3]-ancestry of one root,
    and needs that root OFF every cycle.  A segment head is not.  This
    is the same proof with the cone replaced by an ABSTRACT decidable,
    downward-closed, acyclic [U]. *)

Definition Ured {P D : Type} (TS : ptraces P D) (DS : pdevs D)
    (U : gev → Prop) (x y : gev) : Prop :=
  gdep3 TS DS x y ∧ U x ∧ U y.

Global Instance Ured_dec {P D : Type} (TS : ptraces P D) (DS : pdevs D)
    (U : gev → Prop) `{!∀ e, Decision (U e)} : RelDecision (Ured TS DS U).
Proof. intros x y. rewrite /Ured. apply _. Defined.

Section ureplay.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (pcls : P → wlabel → wstate → wm_class).
  Context (pdev : P → wlabel → P → bool).
  Context (TS : ptraces P D) (img : image) (d0 : D) (ps : list P).
  Context (Hwf : ptraces_wf pstep TS).
  Context (Hwsi : ptraces_ws_init TS).
  Context (Hco : ∀ a, co_tc TS a).
  Context (Hwfl : writes_fulfilled TS).
  Context (Hlf : lat_free_prog pstep).
  Context (Hobl : ts_oblivious pstep).
  Context (Hcls : cls_canonical pcls TS).
  Context (Hclsobl : pcls_obl pcls).
  Context (Himg : pt_img TS = img).
  Context (Hnag : length (pt_trs TS) = length ps).
  Context (Hdata : ∀ p m, pt_log TS !! p = Some m → wm_data m ≠ []).
  Context (Hps0 : ∀ j T ag0, pt_trs TS !! j = Some T →
                    at_ags T !! 0%nat = Some ag0 → ps !! j = Some (pa_st ag0)).
  Context (DS : pdevs D).
  Context (Hwit : ptraces_wit TS DS).
  Context (Hd0 : pd_init DS = d0).

  (** THE GENERALIZED CONE REPLAY. *)
  Theorem U_Qinv (U : gev → Prop) `{!∀ e, Decision (U e)} :
    (∀ e, U e → gev_wf TS e) →
    dc TS (gdep3 TS DS) U →
    (∀ e, U e → ¬ tc (gdep3 TS DS) e e) →
    ∃ order,
      Qinv pstep pcls TS DS img d0 ps order ∧
      (∀ e, e ∈ order ↔ (gev_wf TS e ∧ U e)).
  Proof.
    intros HUwf HUdc HUacyc.
    have HRacyc : ∀ x, ¬ tc (Ured TS DS U) x x.
    { have Htc : ∀ x y, tc (Ured TS DS U) x y → tc (gdep3 TS DS) x y ∧ U x.
      { induction 1 as [x y (Hd & Hx & Hy)|x y z (Hd & Hx & Hy) Htc IH].
        - split; [by apply tc_once|done].
        - split; [|done]. eapply tc_l; [exact Hd|apply IH]. }
      intros x Hc. destruct (Htc x x Hc) as (H1 & H2). by eapply HUacyc. }
    destruct (topo_sort (Ured TS DS U) (gev_enum_S TS U) HRacyc
                (NoDup_gev_enum_S TS U)) as (order & Hnd & Hmem0 & Hord).
    have Hmem : ∀ e, e ∈ order ↔ (gev_wf TS e ∧ U e).
    { intros e. rewrite Hmem0. apply elem_of_gev_enum_S. }
    have Hpre : ∀ n, (n ≤ length order)%nat →
                  Qinv pstep pcls TS DS img d0 ps (take n order).
    { intros n. induction n as [|n IH]; intros Hn.
      { rewrite take_0.
        by apply (Qinv_nil pstep pcls TS DS img d0 ps Hwf Hnag Hps0 Hd0). }
      have [e He] : is_Some (order !! n) by apply lookup_lt_is_Some_2; lia.
      rewrite (take_S_r order n e He).
      have Hein : e ∈ order by eapply elem_of_list_lookup_2.
      have Hes : gev_wf TS e ∧ U e by apply Hmem.
      eapply (Qinv_step pstep pcls pdev TS DS img d0 ps Hwf Hwsi Hco Hwfl
                Hlf Hobl Hcls Hclsobl Himg Hnag Hdata Hwit (take n order) e).
      - apply IH. lia.
      - apply Hes.
      - intros Hin. apply elem_of_take in Hin as (i & Hi & Hilt).
        have Heq : i = n by eapply list_relations.NoDup_lookup. lia.
      - intros e' Hd Hwf'.
        have HU' : U e' by eapply HUdc; [apply Hes|exact Hd|exact Hwf'].
        have He' : e' ∈ order by apply Hmem.
        apply elem_of_list_lookup in He' as (i & Hi).
        have Hlt : (i < n)%nat.
        { eapply Hord; [exact Hi|exact He|]. split_and!; [done|done|apply Hes]. }
        apply elem_of_take. by exists i. }
    have HQ := Hpre (length order) (Nat.le_refl _).
    have Hfull : take (length order) order = order by apply take_ge; lia.
    rewrite Hfull in HQ.
    exists order. by split.
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** THE SEGMENT HEAD HAS A pf-REAL PRE-STATE

      Instantiated at [R := gdep3 TS DS] — the relation the replay is
      downward closed under.  [Uanc] at a MINIMAL component is acyclic
      by [Uanc_acyc], downward closed by [Uanc_dc], and it excludes the
      head, whose po-predecessors it contains ([scc_headR_po_pred]).  So
      the replayed configuration's agent [h.1] sits at [h.2]. *)

  Lemma gdep3_wf' : ∀ x y, gdep3 TS DS x y → gev_wf TS x ∧ gev_wf TS y.
  Proof. intros x y Hd. by apply (gdep3_wf TS DS x y Hwit). Qed.

  (** The processed count of an agent whose whole po-prefix is
      processed and which is not itself processed — [nproc_cur] with the
      hypothesis restricted to po-predecessors (a cross-agent [gdep2]
      predecessor of a segment head is on the CYCLE, so [nproc_cur]'s
      own hypothesis is unavailable here). *)
  Lemma nproc_of_po_prefix done e :
    qorder TS done → gev_wf TS e → e ∉ done →
    (∀ k, (k < e.2)%nat → (e.1, k) ∈ done) →
    nproc done e.1 = e.2.
  Proof.
    intros Hq Hwfe Hnin Hpre. destruct e as [j k]. simpl in *.
    have Hle : (nproc done j ≤ k)%nat.
    { destruct (decide (k < nproc done j)%nat) as [Hlt|Hge]; [|lia].
      destruct Hnin. apply (qorder_mem TS done j k Hq). by split. }
    destruct (decide (nproc done j < k)%nat) as [Hlt|Hge]; [|lia]. exfalso.
    have Hin : (j, nproc done j) ∈ done by apply Hpre.
    apply (qorder_mem TS done j (nproc done j) Hq) in Hin as [_ Hc]. lia.
  Qed.

  Theorem head_prestate_pf_real f h T :
    oncycR (gdep3 TS DS) f →
    sccR_min TS (gdep3 TS DS) f →
    scc_headR TS (gdep3 TS DS) f h →
    pt_trs TS !! h.1 = Some T →
    ∃ order cf agn,
      Qinv pstep pcls TS DS img d0 ps order ∧
      (∀ e, e ∈ order ↔ (gev_wf TS e ∧ Uanc TS (gdep3 TS DS) f e)) ∧
      rtc (wp_pf_run pstep pcls) (wp_init img d0 ps) cf ∧
      pc_img cf = img ∧ pc_log cf = pf_log TS order ∧
      at_ags T !! h.2 = Some agn ∧
      pc_ags cf !! h.1 =
        Some (WPAgent (pa_st agn)
                (aevs_post (pi TS order) (take h.2 (at_evs T)) ws_init) ∅).
  Proof.
    intros Hcf Hmin Hh HT.
    have Hwfh : gev_wf TS h
      by eapply (scc_headR_wf TS (gdep3 TS DS) gdep3_wf' f h).
    destruct (U_Qinv (Uanc TS (gdep3 TS DS) f))
      as (order & HQ & Hmem).
    { intros e. apply (Uanc_wf TS (gdep3 TS DS) gdep3_wf' f e). }
    { intros e e' HU Hd _.
      by eapply (Uanc_dc TS (gdep3 TS DS) gdep3_wf' f e e'). }
    { intros e HU.
      by eapply (Uanc_acyc TS (gdep3 TS DS) gdep3_wf' f e Hmin). }
    have Hq : qorder TS order
      by eapply (Qinv_order pstep pcls TS DS img d0 ps).
    destruct (Qinv_run pstep pcls TS DS img d0 ps order HQ)
      as (cf & Hrun & Hcimg & Hclog & Hclen & Hcags & _).
    (* the head is not processed … *)
    have Hhnin : h ∉ order.
    { intros Hin. apply Hmem in Hin as [_ HU].
      by eapply (scc_headR_not_U TS (gdep3 TS DS) gdep3_wf' f h). }
    (* … and its whole po-prefix is *)
    have Hprefix : ∀ k, (k < h.2)%nat → (h.1, k) ∈ order.
    { intros k Hlt.
      have Hwfk : gev_wf TS (h.1, k).
      { apply gev_wf_bounds. apply gev_wf_bounds in Hwfh as (T' & HT' & Hk).
        exists T'. simpl in HT', Hk |- *. split; [done|lia]. }
      apply Hmem. split; [done|].
      eapply (scc_headR_po_pred TS (gdep3 TS DS) gdep3_wf'
                (gpo_gdep3 TS DS) f h k); done. }
    have Hnp : nproc order h.1 = h.2 by apply nproc_of_po_prefix.
    destruct (Hcags h.1 T HT) as (agn & Hagn & Hlk).
    rewrite Hnp in Hagn. rewrite Hnp in Hlk.
    exists order, cf, agn. split_and!; done.
  Qed.


  (** THE ITEM-2 CAPSTONE: from ANY cycle, a minimal component whose
      strict ancestry is on no cycle at all, and, for every agent with
      an event in it, a pf-reachable configuration in which that agent
      sits EXACTLY at its segment head's pre-record. *)
  Corollary cycle_min_scc_heads e0 :
    dev_wit_ok TS DS → on_cyc TS e0 →
    ∃ f, oncycR (gdep3 TS DS) f ∧ scc_min3 TS DS f ∧
      (∀ x, Ustrict3 TS DS f x → ¬ on_cyc TS x) ∧
      (∀ e T, scc3 TS DS f e → pt_trs TS !! e.1 = Some T →
         ∃ h order cf agn,
           h.1 = e.1 ∧ scc_headR TS (gdep3 TS DS) f h ∧
           Qinv pstep pcls TS DS img d0 ps order ∧
           (∀ z, z ∈ order ↔ (gev_wf TS z ∧ Ustrict3 TS DS f z)) ∧
           rtc (wp_pf_run pstep pcls) (wp_init img d0 ps) cf ∧
           at_ags T !! h.2 = Some agn ∧
           pc_ags cf !! e.1 =
             Some (WPAgent (pa_st agn)
                     (aevs_post (pi TS order) (take h.2 (at_evs T)) ws_init)
                     ∅)).
  Proof.
    intros Hwok Hc0.
    have Hc0' : oncycR (gdep3 TS DS) e0
      by apply (on_cyc_gdep3 TS DS e0 Hwit Hwok).
    destruct (scc_min3_exists TS DS e0 Hwit Hc0') as (f & Hcf & Hmin & _).
    exists f. split_and!; [done|done| |].
    { intros x HU. by eapply (Ustrict3_not_on_cyc TS DS f x Hwit Hwok Hmin). }
    intros e T Hse HT.
    destruct (scc_head3_exists TS DS f e Hwit Hse) as (h & Hh1 & Hh).
    have HTh : pt_trs TS !! h.1 = Some T by rewrite Hh1.
    destruct (head_prestate_pf_real f h T Hcf Hmin Hh HTh)
      as (order & cf & agn & HQ & Hmem & Hrun & Hcimg & Hclog & Hagn & Hlk).
    exists h, order, cf, agn. split_and!; try done.
    by rewrite -Hh1.
  Qed.

End ureplay.

(* ================================================================== *)
(** ** 3. [sf_edges]: THE SITE FACTS AS TRACE SHAPES

    The four shapes of the design's case tree, in the coordinates of
    [WeakRobustMain.edges_split_cyc]: [j] is the reader's agent, [T] its
    trace, [kr] the entry read's index, [(a, ts)] the byte and timestamp
    it read, [k'] the exit fulfil's index. *)

Definition sf_shape {P D : Type} (TS : ptraces P D) (j : nat)
    (T : atrace P D) (kr : nat) (a : Z) (ts : nat) (k' : nat) : Prop :=
  (** C1/C2 — the entry is [aq], or a [pr ∧ sw] fence sits between it
      and the exit ([WeakRobustAcyc.disciplined]) *)
  disciplined T kr k'
  (** C3 — a syntactic dependency chain from the entry read's result to
      a branch po-before the exit fulfil (D2/D3's rules; the
      [read_unforwarded] side condition is DISCHARGED at the theorem,
      the edge being cross-agent) *)
  ∨ (∃ evr k0 ev0 rd0 srcs0 hs kc rend evc ctrl,
       at_evs T !! kr = Some evr ∧ (a, ts) ∈ lb_reads (ae_lb evr) ∧
       (S kr ≤ k0)%nat ∧ no_instr T (S kr) k0 ∧
       at_evs T !! k0 = Some ev0 ∧ ae_lb ev0 = LRegW rd0 srcs0 ∧
       DLdRes ∈ srcs0 ∧
       rchain T (S k0) rd0 hs ∧ rchain_end (S k0) rd0 hs = (kc, rend) ∧
       at_evs T !! kc = Some evc ∧ ae_lb evc = LCtrl ctrl ∧
       DReg rend ∈ ctrl ∧ (kc < k')%nat)
  (** C4 — SF-1: the message was written inside its author's critical
      section of a lock word [L], the read sits inside the reader's
      critical section of the SAME [L], and the two windows are
      DISJOINT ([win_excl] — the site fact L2-M1 isolated) *)
  ∨ (∃ L i ka_i kr_i ta_i tw_i tr_i ka_j kr_j ta_j tw_j tr_j esrc evaj,
       i ≠ j ∧
       cs_window TS L i ka_i kr_i ta_i tw_i tr_i ∧
       cs_window TS L j ka_j kr_j ta_j tw_j tr_j ∧
       win_excl TS L i tw_i tr_i ∧ win_excl TS L j tw_j tr_j ∧
       (ta_i < tr_j)%nat ∧ (ta_i < ts)%nat ∧ (ts < tr_i)%nat ∧
       at_evs T !! ka_j = Some evaj ∧ lb_aq (ae_lb evaj) = true ∧
       esrc.1 ≠ j ∧ gev_ts TS esrc = Some ta_j ∧ (ka_j < kr)%nat)
  (** …or the exit fulfil's own EXT view already covers the message —
      the shape a caller that ALREADY has [edge_ok_f] supplies *)
  ∨ fcov T k' ts.

(** THE PER-BUNDLE RESIDUE: every cross-rf edge into an ON-CYCLE reader,
    at the fulfil that sources the exit milestone, has one of the four
    shapes — or the message is [bad]. *)
Definition sf_edges {P D : Type} (nh : nat) (TS : ptraces P D)
    (DS : pdevs D) : Prop :=
  ∀ e1 e2 T ts a k' ev',
    gev_ts TS e1 = Some ts → gev_reads TS e2 a ts → e1.1 ≠ e2.1 →
    on_cyc TS e2 →
    pt_trs TS !! e2.1 = Some T →
    (e2.2 < k')%nat →
    at_evs T !! k' = Some ev' → is_Some (ae_ts ev') →
    (∃ y, gmile TS (e2.1, k') y) →
    sf_shape TS e2.1 T e2.2 a ts k' ∨ bad nh TS DS e1 e2.

(** NO BAD EDGE TARGETS AN ON-CYCLE EVENT (C5) — convertible with
    [WeakRobustMain.bad_wf_strong]; see the FINDING in the header. *)
Definition scc_no_bad {P D : Type} (nh : nat) (TS : ptraces P D)
    (DS : pdevs D) : Prop :=
  ∀ e1 e2, bad nh TS DS e1 e2 → ¬ on_cyc TS e2.

Lemma scc_no_bad_strong {P D : Type} (nh : nat) (TS : ptraces P D)
    (DS : pdevs D) : scc_no_bad nh TS DS ↔ bad_wf_strong nh TS DS.
Proof. done. Qed.

Section sf.
  Context {P D : Type}.
  Context (pstep : P → D → wlabel → P → D → Prop).
  Context (TS : ptraces P D).
  Context (Hwf : ptraces_wf pstep TS).
  Context (Hfo : ptraces_fwd_own TS).

  (** THE DISCHARGE: each shape gives [edge_ok_f], by L2-M1's lemmas. *)
  Theorem sf_shape_edge_ok_f j T kr a ts k' ev' esrc :
    pt_trs TS !! j = Some T →
    gev_reads TS (j, kr) a ts →
    gev_ts TS esrc = Some ts → esrc.1 ≠ j →
    (kr < k')%nat → at_evs T !! k' = Some ev' → is_Some (ae_ts ev') →
    sf_shape TS j T kr a ts k' →
    edge_ok_f T kr k' ts.
  Proof.
    intros HT Hrd Hsrc Hne Hlt Hev' Hsome [Hd|[Hc3|[Hc4|Hf]]].
    - by left.
    - (* C3 — the dependency chain *)
      destruct Hc3 as (evr & k0 & ev0 & rd0 & srcs0 & hs & kc & rend & evc &
                       ctrl & Hevr & Hin & Hle0 & Hni & Hev0 & Hlb0 & Hld &
                       Hch & Hend & Hevc & Hlbc & Hinc & Hltc).
      right.
      have Hunf : read_unforwarded (pt_log TS) j (ae_lb evr) ts.
      { apply foreign_ts_unforwarded.
        by eapply (foreign_ts_of_fulfil pstep TS Hwf j esrc ts). }
      by eapply (fcov_of_dep_chain pstep TS Hwf Hfo j T kr evr a ts k0 ev0
                   rd0 srcs0 hs kc rend evc ctrl k' ev').
    - (* C4 — the lock-mediated read *)
      destruct Hc4 as (L & i & ka_i & kr_i & ta_i & tw_i & tr_i & ka_j & kr_j &
                       ta_j & tw_j & tr_j & esrc2 & evaj & Hij & Hwi & Hwj &
                       Hei & Hej & Hlate & Hlo & Hhi & Hevaj & Haq & Hne2 &
                       Hsrc2 & Hltaj).
      destruct (gev_reads_ev TS (j, kr) a ts T HT Hrd) as (evr & Hevr & _).
      destruct (ag_at pstep TS Hwf j T kr evr HT Hevr) as (agh & Hagh).
      have Hcov : covered T kr ts.
      { eapply (cs_read_covered_window pstep TS Hwf Hfo L i j T esrc2
                  ka_i kr_i ta_i tw_i tr_i ka_j kr_j ta_j tw_j tr_j kr ts
                  agh evaj); done. }
      eapply (edge_ok_edge_ok_f pstep (pt_img TS) (pt_log TS) j T kr k' ts ev');
        [by eapply Hwf|lia|exact Hev'|exact Hsome|by right].
    - by right.
  Qed.

  (** …hence [sf_edges] SERVES the Layer-1 per-edge premise. *)
  Theorem sf_edges_edges_split_cyc nh DS :
    sf_edges nh TS DS → edges_split_cyc nh TS DS.
  Proof.
    intros Hsf e1 e2 T ts a k' ev' Hts Hrd Hne Hcy HT Hlt Hev Hsome Hms.
    destruct (Hsf e1 e2 T ts a k' ev' Hts Hrd Hne Hcy HT Hlt Hev Hsome Hms)
      as [Hshape|Hbad]; [left|by right].
    destruct e2 as [j kr]. simpl in *.
    by eapply (sf_shape_edge_ok_f j T kr a ts k' ev' e1).
  Qed.

  (** …and CONVERSELY [edge_ok_f] is literally two of the four shapes,
      so the premise is not logically weakened.  FINDING: [sf_edges] and
      [edges_split_cyc] are EQUIVALENT.  That is forced — any sound
      shape implies [edge_ok_f], so a discharge theorem in this
      direction can only ever produce an equivalence.  What [sf_edges]
      buys is not logical strength but VOCABULARY: its obligations are
      statements about the LABELS of one agent's trace (a fence, an
      [aq] bit, a register chain, two lock windows), which a site can
      exhibit from the program text, whereas [edge_ok_f]'s [fcov] is a
      statement about the machine's view arithmetic, which it cannot.
      The genuine weakening of the per-edge premise was banked at A0''
      ([edges_split] ⟹ [edges_split_ms] ⟹ [edges_split_cyc]). *)
  Theorem edges_split_cyc_sf_edges nh DS :
    edges_split_cyc nh TS DS → sf_edges nh TS DS.
  Proof.
    intros H e1 e2 T ts a k' ev' Hts Hrd Hne Hcy HT Hlt Hev Hsome Hms.
    destruct (H e1 e2 T ts a k' ev' Hts Hrd Hne Hcy HT Hlt Hev Hsome Hms)
      as [[Hd|Hf]|Hbad]; [left;by left|left;right;right;by right|by right].
  Qed.

  (* ---------------------------------------------------------------- *)
  (** *** THE LAYER-2 ACYCLICITY THEOREM *)

  Theorem l2_gdep2_acyclic nh DS :
    ee_ok TS → sf_edges nh TS DS → scc_no_bad nh TS DS → gdep2_acyclic TS.
  Proof.
    intros Hee Hsf Hnb.
    eapply (gdep2_acyclic_bad_free pstep nh TS DS Hwf Hfo Hee); [|exact Hnb].
    by apply sf_edges_edges_split_cyc.
  Qed.

  Theorem l2_gdep3_acyclic nh DS :
    ptraces_wit TS DS → dev_wit_ok TS DS →
    ee_ok TS → sf_edges nh TS DS → scc_no_bad nh TS DS → gdep3_acyclic TS DS.
  Proof.
    intros Hwit Hwok Hee Hsf Hnb.
    apply (gdep3_acyclic_of_wit TS DS Hwit); [|exact Hwok].
    by eapply l2_gdep2_acyclic.
  Qed.

End sf.

(** THE φ-DERIVED FORM OF C5.  [scc_no_bad] is what [gdep2_acyclic_main]
    derives from [bad_wf] and [pf_violation_free_hart] via the exhibit —
    but the exhibit itself needs the per-edge premise, which [sf_edges]
    now supplies.  So a caller may discharge C5 either directly or by
    the same route Layer 1 uses. *)
Theorem l2_gdep2_acyclic_phi {P D : Type}
    (pstep : P → D → wlabel → P → D → Prop)
    (pcls : P → wlabel → wstate → wm_class) (pdev : P → wlabel → P → bool)
    (TS : ptraces P D) (img : image) (d0 : D) (ps : list P)
    (DS : pdevs D) (nh : nat) :
  ptraces_wf pstep TS → ptraces_ws_init TS → (∀ a, co_tc TS a) →
  writes_fulfilled TS → lat_free_prog pstep → ts_oblivious pstep →
  cls_canonical pcls TS → pcls_obl pcls →
  pt_img TS = img → length (pt_trs TS) = length ps →
  (∀ p m, pt_log TS !! p = Some m → wm_data m ≠ []) →
  (∀ j T ag0, pt_trs TS !! j = Some T →
     at_ags T !! 0%nat = Some ag0 → ps !! j = Some (pa_st ag0)) →
  ptraces_wit TS DS → pd_init DS = d0 → dev_wit_ok TS DS →
  ptraces_fwd_own TS → ee_ok TS →
  sf_edges nh TS DS →
  pf_violation_free_hart cls_of pub_of nh pstep pcls img d0 ps →
  bad_wf nh TS DS →
  gdep2_acyclic TS.
Proof.
  intros Hwf Hwsi Hco Hwfl Hlf Hobl Hcls Hclsobl Himg Hnag Hdata Hps0
    Hwit Hd0 Hwok Hfo Hee Hsf Hvf Hbwf.
  eapply (gdep2_acyclic_main pstep pcls pdev TS img d0 ps Hwf Hwsi Hco Hwfl
            Hlf Hobl Hcls Hclsobl Himg Hnag Hdata Hps0 DS Hwit Hd0 Hwok Hfo
            Hee nh); [|exact Hvf|exact Hbwf].
  by eapply sf_edges_edges_split_cyc.
Qed.

(* ------------------------------------------------------------------ *)
(** *** C5, MACHINE-CHECKED: THE EXHIBIT CANNOT RUN AT AN SCC EVENT

    [WeakRobustMain.bad_edge_violates] takes [bad_min nh TS DS b2] —
    "no bad edge's target is a strict [gdep3] ancestor of [b2]" — and
    its FIRST use of that hypothesis is at the bad edge itself, which
    yields [¬ tc (gdep3 TS DS) b2 b2].  So the exhibit's own premise
    already excludes an on-cycle reader; there is no way to refute a bad
    edge INSIDE a minimal SCC, and C5 has to be discharged off the
    cycle. *)
Lemma bad_min_not_on_cyc {P D : Type} (nh : nat) (TS : ptraces P D)
    (DS : pdevs D) e1 e2 :
  bad nh TS DS e1 e2 → bad_min nh TS DS e2 → ¬ on_cyc TS e2.
Proof.
  intros Hbad Hmin Hc. apply (Hmin e1 e2 Hbad).
  by apply tc_gdep2_gdep3.
Qed.

(** THE φ-DERIVED [scc_no_bad].  [bad_wf] says SOME bad edge is minimal;
    by the lemma above that one is off every cycle, so the exhibit
    applies to it and φ refutes it — and then NO bad edge exists, which
    is [scc_no_bad] a fortiori.  The exhibit consumes the per-edge
    premise, which [sf_edges] supplies. *)
Theorem scc_no_bad_of_phi {P D : Type}
    (pstep : P → D → wlabel → P → D → Prop)
    (pcls : P → wlabel → wstate → wm_class) (pdev : P → wlabel → P → bool)
    (TS : ptraces P D) (img : image) (d0 : D) (ps : list P)
    (DS : pdevs D) (nh : nat) :
  ptraces_wf pstep TS → ptraces_ws_init TS → (∀ a, co_tc TS a) →
  writes_fulfilled TS → lat_free_prog pstep → ts_oblivious pstep →
  cls_canonical pcls TS → pcls_obl pcls →
  pt_img TS = img → length (pt_trs TS) = length ps →
  (∀ p m, pt_log TS !! p = Some m → wm_data m ≠ []) →
  (∀ j T ag0, pt_trs TS !! j = Some T →
     at_ags T !! 0%nat = Some ag0 → ps !! j = Some (pa_st ag0)) →
  ptraces_wit TS DS → pd_init DS = d0 → dev_wit_ok TS DS →
  ptraces_fwd_own TS → ee_ok TS →
  sf_edges nh TS DS →
  pf_violation_free_hart cls_of pub_of nh pstep pcls img d0 ps →
  bad_wf nh TS DS →
  scc_no_bad nh TS DS.
Proof.
  intros Hwf Hwsi Hco Hwfl Hlf Hobl Hcls Hclsobl Himg Hnag Hdata Hps0
    Hwit Hd0 Hwok Hfo Hee Hsf Hvf Hbwf e1 e2 Hbad _.
  eapply (no_bad_edge pstep pcls pdev TS img d0 ps Hwf Hwsi Hco Hwfl Hlf Hobl
            Hcls Hclsobl Himg Hnag Hdata Hps0 DS Hwit Hd0 Hwok Hfo Hee nh);
    [|exact Hvf|exact Hbwf|exact Hbad].
  by eapply sf_edges_edges_split_cyc.
Qed.

(* ================================================================== *)
(** ** 4. [robust_main_l2]

    [WeakRobustMain.robust_main_acyc] with the acyclicity obligation
    replaced by the Layer-2 residue. *)

Theorem robust_main_l2 {P D : Type}
    (pstep : P → D → wlabel → P → D → Prop)
    (pcls : P → wlabel → wstate → wm_class) (pdev : P → wlabel → P → bool)
    (nh : nat) img d0 (ps : list P) (c mid : wpcfg P D)
    (TS : ptraces P D) (DS : pdevs D) :
  lat_free_prog pstep → ts_oblivious pstep → pcls_obl pcls →
  rtc (wp_promise_step (P:=P) (D:=D)) (wp_init img d0 ps) mid →
  ptraces_dev_of pstep pdev TS DS mid c →
  (∀ p m i, pc_log mid !! p = Some m → wm_tid m = Some i →
     ∃ T, pt_trs TS !! i = Some T ∧
       (∃ k ev, at_evs T !! k = Some ev ∧ ae_ts ev = Some (S p)) ∧
       (∀ k1 k2 ev1 ev2,
          at_evs T !! k1 = Some ev1 → ae_ts ev1 = Some (S p) →
          at_evs T !! k2 = Some ev2 → ae_ts ev2 = Some (S p) → k1 = k2)) →
  (∀ a, co_tc TS a) →
  ee_ok TS →
  (** THE LAYER-2 RESIDUE, in place of [gdep3_acyclic TS DS] *)
  sf_edges nh TS DS →
  scc_no_bad nh TS DS →
  dev_wit_ok TS DS →
  cls_canonical pcls TS →
  ∃ cf, rtc (wp_pf_run pstep pcls) (wp_init img d0 ps) cf ∧
        prog_of cf = prog_of c ∧ (∀ a, mem_of cf a = mem_of c a).
Proof.
  intros Hlf Hobl Hclsobl Hprom Hofd Hacct Hco Hee Hsf Hnb Hwok Hcls.
  have Hwit : ptraces_wit TS DS by eapply ptraces_dev_of_wit.
  have Hofd' := Hofd.
  destruct Hofd' as (Hof & _).
  have Hwf : ptraces_wf pstep TS by eapply ptraces_of_wf.
  have Hinit : cfg_ws_init mid.
  { eapply cfg_ws_init_promise_run;
      [apply (cfg_ws_init_init img d0 ps)|exact Hprom]. }
  have Hfo : ptraces_fwd_own TS by eapply (ptraces_of_fwd_own pstep TS mid c).
  have Hacyc : gdep3_acyclic TS DS
    by eapply (l2_gdep3_acyclic pstep TS Hwf Hfo nh DS).
  by eapply (robust_main_acyc pstep pcls pdev img d0 ps c mid TS DS).
Qed.
