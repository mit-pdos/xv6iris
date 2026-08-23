(** * WeakRvwmoPreNorm2.v — THE TWO-MOVE (W,W) NORMALIZATION, AND WHAT IT
      COSTS

    [WeakRvwmoPreNorm] normalizes the same-hart write order by DESCENDING
    the po-minimal write witness [e] towards the gmo-minimal inverted write
    [w], and pays for it with three residual configurations (K2/K3/K4),
    each reducible (§5 there) to one missing edge [ww_gap_link].  Its §7
    closing note records the counterexample that makes that edge genuinely
    missing, and observes that the graph is nonetheless normalizable — by
    the move the descent does not make, the ASCENT of [w].

    THIS FILE RUNS THE TWO-MOVE ANALYSIS TO ITS CONCLUSION.  The conclusion
    is that the exchange kit is not the right instrument at all:

    §1  [normalize_ww2] — [RacyD]-acyclicity ALONE gives the normalized
        [gd_equiv] member, with no kill, no [ww_gap_link] and no orbit
        quantification.  The proof is not an exchange argument: [RacyD]
        CONTAINS rule 14's own edge [gpow] (po into a write), so an acyclic
        graph already has a topological order putting [e] before [w] —
        [WeakRvwmoDec.normalize_of_acyclic'] retimes to a rule-14 graph and
        [WeakRvwmoWalk.gwrow_gmo_of_rule14] reads off the conclusion.  The
        ascent of [w] is what the retiming does; §7's counterexample is
        [RacyD]-acyclic and is therefore covered, exactly as its note says.

    §2  … and where that leaves the walk.  [gwrow_gmo] enters
        [WeakRvwmoWalk] at EXACTLY ONE place — [wlk_step'_of_supply] step
        3, "nothing of the hart's row between its current position [k0] and
        the write being emitted is itself a write".  §2 states that use
        site as [gwrow_seg] and proves [gwrow_seg G ↔ gwrow_gmo G]: THE
        RANGE RESTRICTION IS VACUOUS.  The walk runs over EVERY write of
        the graph, so every same-hart write pair is covered, and no
        restriction of the obligation to "the ranges the walk touches" can
        buy anything.  (Machine-checked, and it is a negative result: it
        closes off the cheapest-looking design change.)

    §3  THE REAL REDUCTION.  Reading [WeakRvwmoTopo]'s linearization
        section shows the [gpow] arm of [RacyD] is used in EXACTLY ONE of
        its lemmas, [lin_grule14] — the retimed graph's CONSISTENCY never
        touches it.  So the linearization goes through for a linear
        extension of the strictly smaller relation

          [RwwD] = [RacyD] with [gpow] narrowed to [gpoww]
                 = po between two writes OF THE SAME HART,

        and delivers [gwrow_gmo] in place of [grule14].  [normalize_ww3]:
        [RwwD]-acyclicity ⇒ a [gd_equiv] member with [gwrow_gmo].  This
        matters because the LB cycles the certification walk exists to
        refute run through [gpow] edges OUT OF A READ (load; store; rf;
        load; store; rf), which [RwwD] does not contain: a graph can carry
        a [RacyD] cycle and still be [RwwD]-acyclic.

    §4  SHARPNESS AND TRANSPORT.  [Rwwt] — [RwwD] minus [gco] and [gfr] —
        transports along [gd_equiv] ([WeakRvwmoAcyc] §5's fragment plus the
        dep set, which the orbit fixes), and [Rwwt]-acyclicity is
        NECESSARY: a [gd_equiv] member with [gwrow_gmo] makes every [Rwwt]
        arm gmo-forward there.  So

          [RwwD] acyclic  ⇒  ∃ member with [gwrow_gmo]  ⇒  [Rwwt] acyclic,

        and the remaining gap between the sufficient and the necessary
        condition is EXACTLY the two arms [gco] and [gfr] — the two that do
        not transport (F2′).  §4 also states the [RacyD] cycle transport
        with its precise [gco]/[gfr] side condition, and the sufficient
        instance (a gmo-order-preserving [π]).

    §5  THE REMAINING OBLIGATION, stated as one definition.

    Nothing below is [Admitted] or [Axiom]-ed.  A LEAF: nothing imports
    this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
Require Import SailStdpp.Operators_mwords.
Require Import SailStdpp.ConcurrencyInterfaceTypes.
Require Import Riscv.rv64d_types Riscv.rv64d.
Require Import DevModel.
Require Import WeakMem.
Require Import WeakDeps.
Require Import WeakLitmus.
Require Import WeakAxiomatic.
Require Import WeakAxiomatic2.
Require Import WeakAxiomatic3.
From stdpp Require Import namespaces.
From iris.proofmode Require Import proofmode.
From iris.program_logic Require Import language weakestpre adequacy.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import RiscvLang.
Require Import RiscvAdequacy.
Require Import WeakRobust.
Require Import WeakRobustMain.
Require Import WeakLang.
Require Import WeakEvCapstone.
Require Import WeakEvAdequacy.
Require Import WeakRvwmoGraph.
Require Import WeakRvwmoNorm.
Require Import WeakRvwmoXchg.
Require Import WeakRvwmoLin.
Require Import WeakRvwmoRestr.
Require Import WeakRvwmoAcyc.
Require Import WeakRvwmoHull.
Require Import WeakRvwmoTopo.
Require Import WeakRvwmoDec.
Require Import WeakInterp.
Require Import WeakEvLang.
Require Import WeakEvPf.
Require Import WeakPromise.
Require Import WeakPromiseFact.
Require Import WeakPromiseBridge.
Require Import WeakAxRealize.
Require Import WeakEvInst.
Require Import WeakEvProv.
Require Import WeakRvwmoConf.
Require Import WeakRvwmoSupply.
Require Import WeakRvwmoProbeK1.
Require Import WeakRvwmoLinInd.
Require Import WeakGhost.
Require Import WeakRvwmoLock.
Require Import WeakRvwmoCert.
Require Import WeakRvwmoFloor.
Require Import WeakRvwmoCert2.
Require Import WeakRvwmoCert3.
Require Import WeakRvwmoCert4.
Require Import WeakRvwmoKillArms.
Require Import WeakRvwmoGlue.
Require Import WeakRvwmoGlue2.
Require Import WeakSrvwmoLitmus.
Require Import WeakSrvwmoCapstone.
Require Import WeakRvwmoCapstone.
Require Import WeakRvwmoWalk.
Require Import WeakRvwmoProgress.
Require Import WeakRvwmoCycWit.
Require Import WeakRvwmoWalk2.
Require Import WeakRvwmoPreNorm.

(* ====================================================================== *)
(** * 1. THE THEOREM: acyclicity alone, both moves at once *)

(** [RacyD] carries [gpow] — po from a memory event INTO a write — which is
    rule 14's own edge.  A violating pair [(e, w)] ([e] po-before [w], [w]
    gmo-before [e], both writes of one hart) therefore ALREADY has its po
    edge in the relation, so any topological order of an acyclic [RacyD]
    puts [e] before [w].  The "ascent of [w] past its gmo-successors" that
    [WeakRvwmoPreNorm] §7 identifies as the missing move is precisely what
    the retiming performs, all inversions at once. *)
Theorem normalize_ww2 (GD : gdexec) :
  rvwmo_minus_deps_consistent GD →
  (∀ x, ¬ tc (RacyD GD) x x) →
  ∃ GD', gd_equiv GD GD' ∧ gwrow_gmo (gd_g GD').
Proof.
  intros Hcons Hacy.
  destruct (normalize_of_acyclic' GD Hcons Hacy)
    as (GD' & pi & Hcons' & H14 & Hrows & Hdeps & Hwp).
  exists GD'. split.
  - by exists pi.
  - apply gwrow_gmo_of_rule14; [by destruct Hcons' as ((H & _) & _ & _)|done].
Qed.

(** THE §7 COUNTEREXAMPLE, RE-EXAMINED.  [WeakRvwmoPreNorm] §7's graph is
    [RacyD]-ACYCLIC (its [R] is [{z → e, z → w, e → w}]), so it satisfies
    the hypothesis above and IS normalized by the retiming.  What it
    refutes is the implication "acyclicity ⇒ the three kills"
    ([kill_ww_of_acyclic] needs [ww_gap_link] on top), not the implication
    "acyclicity ⇒ normalizable".  Formally: [normalize_ww_of_acyclic]'s
    conclusion is available WITHOUT its [ww_gap_link] premise, and without
    quantifying acyclicity over the orbit. *)
Corollary normalize_ww_no_gap_link (GD : gdexec) :
  rvwmo_minus_deps_consistent GD →
  (∀ x, ¬ tc (RacyD GD) x x) →
  ∃ GD', gd_equiv GD GD' ∧ gwrow_gmo (gd_g GD').
Proof. exact (normalize_ww2 GD). Qed.

(* ====================================================================== *)
(** * 2. THE WALK'S USE SITE, AND WHY RESTRICTING IT BUYS NOTHING

    [gwrow_gmo] is consumed in [WeakRvwmoWalk.wlk_step'_of_supply] at one
    step and nowhere else: with the emitted write pinned at gmo index
    [S n] and the hart standing at row position [k0] (the walk invariant's
    [wpos_hi] holding there), no row position in [[k0, kz)] is a write.
    That is the following statement, verbatim. *)
Definition gwrow_seg (G : gexec) : Prop :=
  ∀ (n : nat) (x : agent) (kz k0 j : nat) (lb : lbl),
    gwrite_at G (S n) = Some (x, kz) →
    wpos_hi G n x k0 →
    (k0 ≤ j)%nat → (j < kz)%nat →
    gx_lbl G (x, j) = Some lb → lb_is_w lb = false.

Lemma gwrow_seg_of_gwrow_gmo (G : gexec) :
  gwf G → gwrow_gmo G → gwrow_seg G.
Proof.
  intros Hwf Hrow n x kz k0 j lb Hat Hhi Hk0 Hjkz Hlj.
  have Hnd : NoDup (gx_gmo G) by destruct Hwf as (H & _ & _).
  destruct (lb_is_w lb) eqn:Hb; [exfalso|done].
  destruct (gwrite_at_inv G (S n) (x, kz) Hnd Hat) as (Hmem & Hwix).
  have Hisw : gis_w G (x, kz) = true
    by (apply gwrites_elem_of in Hmem as [_ H]; exact H).
  destruct (gx_lbl G (x, kz)) as [lbz|] eqn:Hlbz;
    [|by rewrite /gis_w Hlbz in Hisw].
  have Hlbzw : lb_is_w lbz = true by rewrite /gis_w Hlbz in Hisw.
  have Hlt : (gwix G (x, j) < gwix G (x, kz))%nat
    := Hrow x j kz Hjkz (ex_intro _ lb (conj Hlj Hb))
         (ex_intro _ lbz (conj Hlbz Hlbzw)).
  have Hgt := Hhi j lb Hk0 Hlj Hb. lia.
Qed.

(** THE NEGATIVE RESULT.  The converse holds too, so the "restrict the
    obligation to the ranges the walk actually covers" design change is
    empty: the restricted statement IS the unrestricted one.  The reason is
    structural — [wlk_run'] runs for [length (gwrites G)] steps, i.e. over
    EVERY write, so every same-hart write pair is covered by some step; the
    proof below manufactures the covering step from an inversion by taking
    the inversion whose LATER-IN-PO member has the SMALLEST write index. *)
Lemma gwrow_gmo_of_gwrow_seg (G : gexec) :
  gwf G → gwrow_seg G → gwrow_gmo G.
Proof.
  intros Hwf Hseg x j k Hjk Hj Hk.
  have Hnd : NoDup (gx_gmo G) by destruct Hwf as (H & _ & _).
  destruct Hj as (lj & Hlj & Hbj). destruct Hk as (lk & Hlk & Hbk).
  have Hinj : (x, j) ∈ gwrites G
    by (eapply gis_w_gwrites; [exact Hwf|by exists lj|by rewrite /gis_w Hlj]).
  have Hink : (x, k) ∈ gwrites G
    by (eapply gis_w_gwrites; [exact Hwf|by exists lk|by rewrite /gis_w Hlk]).
  destruct (decide (gwix G (x, j) < gwix G (x, k))%nat) as [?|Hge]; [done|].
  exfalso.
  (* the inverted pairs, indexed by their LATER-IN-PO member *)
  pose Bad := (λ p : geid, ∃ i : nat, (i < p.2)%nat ∧
                 glbl_is G (p.1, i) lb_is_w ∧
                 (gwix G p < gwix G (p.1, i))%nat).
  have HBaddec : ∀ p : geid, Decision (Bad p).
  { intros p. rewrite /Bad.
    apply (dec_iff (P := ∃ i : nat, (i < p.2)%nat ∧
                           glbl_is G (p.1, i) lb_is_w ∧
                           (gwix G p < gwix G (p.1, i))%nat)
                   (Q := ∃ i : nat, i ∈ seq 0 p.2 ∧
                           (glbl_is G (p.1, i) lb_is_w ∧
                            (gwix G p < gwix G (p.1, i))%nat))).
    - split.
      + intros (i & Hi & H1 & H2). exists i. split; [|done].
        apply elem_of_seq. lia.
      + intros (i & Hi & H1 & H2). apply elem_of_seq in Hi.
        exists i. split; [lia|done].
    - apply list_exists_dec. intros i. apply _. }
  have Hbadk : Bad (x, k).
  { exists j. simpl. split_and!; [lia|by exists lj|].
    have Hne : gwix G (x, j) ≠ gwix G (x, k).
    { intros Heq. have Hxy := gwix_inj G (x, j) (x, k) Hnd Hinj Hink Heq.
      injection Hxy as Hxy. lia. }
    lia. }
  have Hne : filter Bad (gwrites G) ≠ [].
  { intros Hnil.
    have Hin : (x, k) ∈ filter Bad (gwrites G)
      by (apply elem_of_list_filter; split; [exact Hbadk|exact Hink]).
    rewrite Hnil in Hin. by apply elem_of_nil in Hin. }
  destruct (list_min_by (gwix G) _ Hne) as (p & Hpin & Hpmin).
  apply elem_of_list_filter in Hpin as [Hpbad Hpw].
  destruct p as [y kz]. destruct Hpbad as (j0 & Hj0lt & Hj0w & Hj0ix).
  simpl in Hj0lt, Hj0w, Hj0ix.
  (* the covering step: the walk emits [(y, kz)] at gmo index [gwix] *)
  have Hpos : (0 < gwix G (y, kz))%nat := gwix_pos G (y, kz) Hpw.
  pose n := (gwix G (y, kz) - 1)%nat.
  have Hgw : gwix G (y, kz) = S n by rewrite /n; lia.
  have Hat : gwrite_at G (S n) = Some (y, kz)
    := gwix_pin G (y, kz) n Hnd Hpw Hgw.
  (* the hart may be taken to stand exactly at [j0]: nothing at or after
     [j0] has already been emitted, by minimality *)
  have Hhi : wpos_hi G n y j0.
  { intros i lb Hi Hli Hbi.
    destruct (decide (n < gwix G (y, i))%nat) as [?|Hle]; [done|exfalso].
    have Hini : (y, i) ∈ gwrites G
      by (eapply gis_w_gwrites; [exact Hwf|by exists lb|by rewrite /gis_w Hli]).
    have Hlti : (gwix G (y, i) < gwix G (y, kz))%nat by lia.
    destruct (decide (i = j0)) as [->|Hne2]; [lia|].
    have Hij : (j0 < i)%nat by lia.
    have Hbadi : Bad (y, i).
    { exists j0. simpl. split_and!; [lia|exact Hj0w|lia]. }
    have Hini' : (y, i) ∈ filter Bad (gwrites G)
      by (apply elem_of_list_filter; split; [exact Hbadi|exact Hini]).
    have Hm := Hpmin (y, i) Hini'. lia. }
  destruct Hj0w as (lb0 & Hlb0 & Hbw0).
  have := Hseg n y kz j0 j0 lb0 Hat Hhi (Nat.le_refl _) Hj0lt Hlb0.
  rewrite Hbw0. done.
Qed.

Theorem gwrow_seg_iff (G : gexec) :
  gwf G → (gwrow_seg G ↔ gwrow_gmo G).
Proof.
  intros Hwf. split;
    [by apply gwrow_gmo_of_gwrow_seg|by apply gwrow_seg_of_gwrow_gmo].
Qed.

(* ====================================================================== *)
(** * 3. THE REAL REDUCTION: A SMALLER RELATION SUFFICES

    [WeakRvwmoTopo]'s linearization section uses the [gpow] arm of [Racy]
    in EXACTLY ONE lemma — [lin_grule14].  Every consistency clause of the
    re-timed graph ([gwf], [gppo_gmo], [gload_value], [gatomicity],
    [gdeps_wf], [gdeps_gmo]) is proved from the OTHER arms alone.  So a
    linear extension of a relation carrying only

        po between two writes of ONE hart   ([gpoww]),

    in place of the full "po into a write from any memory event", still
    re-times to a CONSISTENT graph — and orders exactly the pairs
    [gwrow_gmo] talks about.

    WHY THIS IS THE RIGHT WEAKENING.  The cycles the certification walk
    exists to refute are LB-shaped: [rf] from a store to a cross-hart load,
    then po from that LOAD to the hart's next store.  The po edge of such a
    cycle has a READ source, so it is a [gpow] edge that is NOT a [gpoww]
    edge: [WeakRvwmoCycWit.cyg]'s cycle disappears from [RwwD] entirely.
    A graph may therefore carry a [RacyD] cycle — be exactly the kind of
    graph the walk is run on — and still be [RwwD]-acyclic, which
    [normalize_ww2] can say nothing about. *)

Definition gpoww (G : gexec) (e w : geid) : Prop :=
  gpo G e w ∧ glbl_is G e lb_is_w ∧ glbl_is G w lb_is_w.

Lemma gpoww_gpow G e w : gpoww G e w → gpow G e w.
Proof.
  intros (Hpo & He & Hw). split_and!;
    [exact Hpo|by apply glbl_is_w_gmem|by apply glbl_is_w_gis_w].
Qed.

(** The same five arms as [Racy], with the first narrowed. *)
Definition Rww (G : gexec) (x y : geid) : Prop :=
  gpoww G x y ∨ grf G x y ∨ gco G x y ∨ gfr G x y ∨ gppo G x y.

Definition RwwD (GD : gdexec) (x y : geid) : Prop :=
  Rww (gd_g GD) x y ∨ (x, y) ∈ gd_deps GD.

Lemma Rww_Racy G x y : Rww G x y → Racy G x y.
Proof. intros [H|H]; [left; by apply gpoww_gpow|by right]. Qed.

Lemma RwwD_RacyD GD x y : RwwD GD x y → RacyD GD x y.
Proof. intros [H|H]; [left; by apply Rww_Racy|by right]. Qed.

(** … so [RacyD]-acyclicity is STRICTLY stronger. *)
Lemma RwwD_acyclic_of_RacyD GD :
  (∀ x, ¬ tc (RacyD GD) x x) → ∀ x, ¬ tc (RwwD GD) x x.
Proof.
  intros Hacy x Htc. apply (Hacy x).
  eapply tc_mono; [|exact Htc]. intros a b. apply RwwD_RacyD.
Qed.

Global Instance gpoww_dec G e w : Decision (gpoww G e w).
Proof. rewrite /gpoww. apply _. Qed.

Global Instance rww_dec G x y : Decision (Rww G x y).
Proof. rewrite /Rww. apply _. Qed.

Global Instance rwwD_dec GD x y : Decision (RwwD GD x y).
Proof. rewrite /RwwD. apply _. Qed.

(** Every [RwwD] edge runs between members of the order — [RacyD_mem]'s
    proof with the first arm re-derived from [gpoww]. *)
Lemma RwwD_mem GD x y :
  rvwmo_minus_deps_consistent GD → RwwD GD x y →
  x ∈ gx_gmo (gd_g GD) ∧ y ∈ gx_gmo (gd_g GD).
Proof.
  intros Hcons HR. apply (RacyD_mem GD x y Hcons). by apply RwwD_RacyD.
Qed.

(** THE INPUT THE RE-TIMING CONSUMES, weakened. *)
Definition linw_extD (GD : gdexec) (L : list geid) : Prop :=
  L ≡ₚ gx_gmo (gd_g GD) ∧ ∀ x y, RwwD GD x y → before L x y.
Section topo_linw.
  Context (GD : gdexec) (L : list geid).
  Context (Hcons : rvwmo_minus_deps_consistent GD).
  Context (Hlin : linw_extD GD L).

  Local Notation G := (gd_g GD).
  Local Notation G' := (retime (gd_g GD) L).
  Local Notation pi := (tren (gd_g GD) L).

  Local Lemma linw_wf : gwf G.
  Proof. apply Hcons. Qed.
  Local Lemma linw_lv : gload_value G.
  Proof. apply Hcons. Qed.
  Local Lemma linw_at : gatomicity G.
  Proof. apply Hcons. Qed.
  Local Lemma linw_perm : L ≡ₚ gx_gmo G.
  Proof. apply Hlin. Qed.

  Local Lemma linw_rows : rows_rel pi G G'.
  Proof. apply retime_rows_rel. Qed.

  (** ** 3.1 [L] is a well-formed order, and [pi] is a write permutation *)

  Local Lemma linw_nodup : NoDup L.
  Proof. rewrite linw_perm. by destruct linw_wf as (? & _ & _). Qed.

  Local Lemma linw_wfilter : filter (gis_w G) L ≡ₚ gwrites G.
  Proof. rewrite /gwrites. by rewrite linw_perm. Qed.

  Local Lemma linw_wlen : length (gwrites G') = length (gwrites G).
  Proof. rewrite retime_gwrites. by rewrite linw_wfilter. Qed.

  Local Lemma linw_welem w : w ∈ gwrites G' ↔ w ∈ gwrites G.
  Proof. rewrite retime_gwrites. by rewrite linw_wfilter. Qed.

  Local Lemma linw_wat t : gwrite_at G' (pi t) = gwrite_at G t.
  Proof.
    destruct (gwrite_at G t) as [w|] eqn:Ht.
    - rewrite (tren_at G L t w Ht) -retime_gwix.
      apply gwrite_at_gwix, linw_welem. by eapply gwrite_at_gwrites.
    - rewrite (tren_none G L t Ht). destruct t as [|i]; [done|].
      rewrite /gwrite_at. apply lookup_ge_None. rewrite linw_wlen.
      rewrite /gwrite_at in Ht. by apply lookup_ge_None in Ht.
  Qed.

  Local Lemma linw_wperm : wperm pi G G'.
  Proof.
    split_and!; [|exact linw_wat|exact linw_wlen].
    intros t1 t2 Heq.
    pose proof (linw_wat t1) as H1. pose proof (linw_wat t2) as H2.
    rewrite Heq H2 in H1.
    destruct (gwrite_at G t1) as [w|] eqn:E1.
    - destruct (gwrite_at_inv G t1 w ltac:(by destruct linw_wf as (?&_&_)) E1)
        as (_ & <-).
      destruct (gwrite_at_inv G t2 w ltac:(by destruct linw_wf as (?&_&_)) H1)
        as (_ & <-). done.
    - rewrite -(tren_none G L t1 E1) -(tren_none G L t2 H1). exact Heq.
  Qed.

  (** ** 3.2 The bridge: [before L] IS [gmo_lt] of the re-timed graph *)

  Local Lemma linw_before x y : before L x y ↔ gmo_lt G' x y.
  Proof.
    pose proof linw_nodup as Hnd. split.
    - intros (i & j & Hi & Hj & Hlt). split_and!.
      + by eapply elem_of_list_lookup_2.
      + by eapply elem_of_list_lookup_2.
      + rewrite (gpos_of_lookup G' i x Hnd Hi) (gpos_of_lookup G' j y Hnd Hj). lia.
    - intros (Hx & Hy & Hlt). exists (gpos G' x), (gpos G' y).
      split_and!; [by apply gpos_elem_lookup|by apply gpos_elem_lookup|lia].
  Qed.

  Local Lemma step_rww x y : Rww G x y → gmo_lt G' x y.
  Proof. intros HR. apply linw_before, (proj2 Hlin). by left. Qed.

  Local Lemma step_dep x y : (x, y) ∈ gd_deps GD → gmo_lt G' x y.
  Proof. intros Hd. apply linw_before, (proj2 Hlin). by right. Qed.

  (** ** 3.3 [pi] is MONOTONE ON SAME-BYTE WRITES, both ways *)

  Local Lemma linw_co_fwd w1 w2 a u1 u2 :
    gwrites_byte G w1 a u1 → gwrites_byte G w2 a u2 →
    (gwix G w1 < gwix G w2)%nat → (gwix G' w1 < gwix G' w2)%nat.
  Proof.
    intros H1 H2 Hlt.
    assert (Hmo : gmo_lt G' w1 w2).
    { apply step_rww. right; right; left. by exists a, u1, u2. }
    apply (gwix_gpos_lt G' w1 w2 linw_nodup).
    - apply linw_welem. by eapply gwrites_byte_in_gwrites; [apply linw_wf|].
    - apply linw_welem. by eapply gwrites_byte_in_gwrites; [apply linw_wf|].
    - by destruct Hmo as (_ & _ & ?).
  Qed.

  Local Lemma linw_co_inv w1 w2 a u1 u2 :
    gwrites_byte G w1 a u1 → gwrites_byte G w2 a u2 →
    (gwix G' w1 < gwix G' w2)%nat → (gwix G w1 < gwix G w2)%nat.
  Proof.
    intros H1 H2 Hlt.
    pose proof (gwrites_byte_in_gwrites G w1 a u1 linw_wf H1) as Hin1.
    pose proof (gwrites_byte_in_gwrites G w2 a u2 linw_wf H2) as Hin2.
    destruct (decide (gwix G w1 < gwix G w2)%nat) as [?|Hge]; [done|]. exfalso.
    destruct (decide (gwix G w1 = gwix G w2)) as [Heq|Hne].
    - assert (w1 = w2) as ->.
      { eapply gwix_inj; [|exact Hin1|exact Hin2|exact Heq].
        by destruct linw_wf as (?&_&_). }
      lia.
    - pose proof (linw_co_fwd w2 w1 a u2 u1 H2 H1 ltac:(lia)). lia.
  Qed.

  (** ** 3.4 The axioms of the re-timed graph *)

  Local Lemma linw_gwf : gwf G'.
  Proof.
    pose proof linw_wf as (Hnd & Hmem & Hsh). split_and!.
    - exact linw_nodup.
    - intros e. split.
      + intros He. apply (rows_rel_gmem _ G G' e linw_rows), Hmem.
        by apply (perm_elem_of L (gx_gmo G) e linw_perm).
      + intros He. apply (perm_elem_of L (gx_gmo G) e linw_perm), Hmem.
        by apply (rows_rel_gmem _ G G' e linw_rows).
    - intros i p k l Hp Hk.
      rewrite /= list_lookup_fmap in Hp. apply fmap_Some in Hp as (r & Hr & ->).
      rewrite list_lookup_fmap in Hk. apply fmap_Some in Hk as (l0 & Hl0 & ->).
      apply lbl_ren_shape. by eapply Hsh.
  Qed.

  Local Lemma linw_gppo : gppo_gmo G'.
  Proof.
    intros e1 e2 Hppo'. apply step_rww. right; right; right; right.
    by apply (proj1 (rows_rel_gppo _ G G' e1 e2 linw_rows)).
  Qed.

  (** THE REPLACEMENT FOR [linw_grule14]: the [gpow] arm is narrowed to
      [gpoww], and what it delivers is [gwrow_gmo] instead of rule 14. *)
  Local Lemma linw_gwrow : gwrow_gmo G'.
  Proof.
    intros x j k Hjk Hj' Hk'.
    have Hj : glbl_is G (x, j) lb_is_w
      by apply (proj1 (rows_rel_glbl_is _ G G' (x, j) lb_is_w linw_rows
                         (lbl_ren_is_w pi))).
    have Hk : glbl_is G (x, k) lb_is_w
      by apply (proj1 (rows_rel_glbl_is _ G G' (x, k) lb_is_w linw_rows
                         (lbl_ren_is_w pi))).
    destruct Hj as (lj & Hlj & Hbj). destruct Hk as (lk & Hlk & Hbk).
    have Hmo : gmo_lt G' (x, j) (x, k).
    { apply step_rww. left. split_and!.
      - split_and!; [done|simpl; lia|by exists lj|by exists lk].
      - by exists lj.
      - by exists lk. }
    have Hinj' : (x, j) ∈ gwrites G'.
    { destruct Hj' as (l & Hl & Hb). eapply gis_w_gwrites;
        [exact linw_gwf|by exists l|by rewrite /gis_w Hl]. }
    have Hink' : (x, k) ∈ gwrites G'.
    { destruct Hk' as (l & Hl & Hb). eapply gis_w_gwrites;
        [exact linw_gwf|by exists l|by rewrite /gis_w Hl]. }
    apply (proj2 (gwix_gpos_lt G' (x, j) (x, k) linw_nodup Hinj' Hink')).
    by destruct Hmo as (_ & _ & ?).
  Qed.

  Local Lemma linw_gload_value : gload_value G'.
  Proof.
    intros e a t' v Hrd'.
    destruct (rows_rel_rdb_inv pi G G' e a t' v linw_rows Hrd')
      as (t & -> & Hrd).
    pose proof linw_lv as Hlv. pose proof linw_wf as Hwf.
    destruct (Hlv e a t v Hrd) as [Hsrc Hmax].
    pose proof linw_wperm as Hwp. pose proof (proj1 Hwp) as Hinj.
    split.
    - destruct (pi t) as [|k] eqn:Hpt.
      + assert (t = 0%nat) as ->.
        { apply Hinj. by rewrite Hpt tren_zero. }
        simpl in Hsrc. exact Hsrc.
      + assert (Ht0 : t ≠ 0%nat).
        { intros ->. rewrite tren_zero in Hpt. done. }
        destruct t as [|t0]; [done|].
        destruct Hsrc as (w & Hwat & Hwb & _).
        exists w. split_and!.
        * rewrite -Hpt linw_wat. exact Hwat.
        * by apply (proj2 (rows_rel_wrb _ G G' w a v linw_rows)).
        * left. apply step_rww. right; left. by exists a, (S t0), v.
    - intros w' v' Hwb' Hvis'.
      assert (Hwb : gwrites_byte G w' a v')
        by (by apply (proj1 (rows_rel_wrb _ G G' w' a v' linw_rows))).
      pose proof (gwrites_byte_in_gwrites G w' a v' Hwf Hwb) as Hw'in.
      assert (Hne : w' ≠ e).
      { intros ->. destruct Hvis' as [Hm|Hp].
        - by eapply gmo_lt_irrefl.
        - by eapply gpo_irrefl. }
      (* the read is never gmo-before a visible write *)
      assert (Hnv : ¬ gmo_lt G' e w').
      { intros Hew. destruct Hvis' as [Hm|Hp].
        - eapply gmo_lt_irrefl. by eapply gmo_lt_trans; [exact Hew|exact Hm].
        - assert (Hpo : gpo G w' e)
            by (by apply (proj1 (rows_rel_gpo _ G G' w' e linw_rows))).
          assert (Hwe : gmo_lt G' w' e).
          { apply step_rww. right; right; right; right. left.
            split; [exact Hpo|]. exists a. split.
            - left. by exists v'.
            - right. by exists t, v. }
          eapply gmo_lt_irrefl. by eapply gmo_lt_trans; [exact Hew|exact Hwe]. }
      destruct (decide (t < gwix G w')%nat) as [Hgt|Hle].
      + exfalso. apply Hnv. apply step_rww. right; right; right; left.
        split; [by intros ->|]. by exists a, t, v, v'.
      + apply Nat.nlt_ge in Hle.
        destruct (decide (gwix G w' = t)) as [Heq|Hne2].
        * assert (Hat' : gwrite_at G t = Some w')
            by (rewrite -Heq; by apply gwrite_at_gwix).
          assert (Hgw : gwix G' w' = pi t).
          { rewrite retime_gwix. by rewrite (tren_at G L t w' Hat'). }
          lia.
        * assert (Hlt : (gwix G w' < t)%nat) by lia.
          assert (Ht0 : t ≠ 0%nat).
          { intros ->. pose proof (gwix_pos G w' Hw'in). lia. }
          destruct t as [|t0]; [done|].
          destruct Hsrc as (w & Hwat & Hwbw & _).
          assert (Hwix : gwix G w = S t0).
          { by destruct (gwrite_at_inv G (S t0) w
                           ltac:(by destruct Hwf as (?&_&_)) Hwat) as (_ & ->). }
          assert (Hgw : gwix G' w = pi (S t0)).
          { rewrite retime_gwix. by rewrite (tren_at G L (S t0) w Hwat). }
          rewrite -Hgw. apply Nat.lt_le_incl.
          eapply (linw_co_fwd w' w a v' v Hwb Hwbw). lia.
  Qed.

  Local Lemma linw_gatomicity : gatomicity G'.
  Proof.
    intros e a t' v Hrd' Hw' w' v' Hwb' [Hlt1 Hlt2].
    destruct (rows_rel_rdb_inv pi G G' e a t' v linw_rows Hrd')
      as (t & Hpt & Hrd).
    pose proof linw_wf as Hwf.
    assert (Hw : glbl_is G e lb_is_w)
      by (by apply (proj1 (rows_rel_glbl_is _ G G' e lb_is_w linw_rows
                            (lbl_ren_is_w pi)))).
    assert (Hwb : gwrites_byte G w' a v')
      by (by apply (proj1 (rows_rel_wrb _ G G' w' a v' linw_rows))).
    pose proof (gwrites_byte_in_gwrites G w' a v' Hwf Hwb) as Hw'in.
    destruct (gread_byte_write_byte G e a t v Hwf (glbl_is_w_gis_w G e Hw) Hrd)
      as (ve & Hwbe).
    (* the upper bound *)
    assert (Hup : (gwix G w' < gwix G e)%nat).
    { eapply (linw_co_inv w' e a v' ve Hwb Hwbe). lia. }
    (* the lower bound *)
    assert (Hlow : (t < gwix G w')%nat).
    { destruct t as [|t0].
      - pose proof (gwix_pos G w' Hw'in). lia.
      - destruct (proj1 (linw_lv e a (S t0) v Hrd)) as (w & Hwat & Hwbw & _).
        assert (Hwix : gwix G w = S t0).
        { by destruct (gwrite_at_inv G (S t0) w
                         ltac:(by destruct Hwf as (?&_&_)) Hwat) as (_ & ->). }
        assert (Hgw : gwix G' w = t').
        { rewrite retime_gwix Hpt. by rewrite (tren_at G L (S t0) w Hwat). }
        rewrite -Hwix. eapply (linw_co_inv w w' a v v' Hwbw Hwb). lia. }
    by eapply linw_at; [exact Hrd|exact Hw|exact Hwb|].
  Qed.

  Local Lemma linw_gdeps_wf : gdeps_wf G' (gd_deps GD).
  Proof.
    intros rw Hrw. destruct Hcons as (_ & Hdwf & _).
    destruct (Hdwf rw Hrw) as (H1 & H2 & H3 & H4). split_and!; [done|done| |].
    - by apply (proj2 (rows_rel_glbl_is _ G G' rw.1 lb_is_r linw_rows
                        (lbl_ren_is_r pi))).
    - by apply (proj2 (rows_rel_glbl_is _ G G' rw.2 lb_is_w linw_rows
                        (lbl_ren_is_w pi))).
  Qed.

  Local Lemma linw_gdeps_gmo : gdeps_gmo G' (gd_deps GD).
  Proof.
    intros rw Hrw. destruct rw as [r w]. apply step_dep. exact Hrw.
  Qed.

  (** THE DELIVERABLE. *)
  Theorem topo_linearizes_w :
    rvwmo_minus_deps_consistent (GDExec G' (gd_deps GD)) ∧
    gwrow_gmo G' ∧
    rows_rel pi G G' ∧
    wperm pi G G'.
  Proof.
    split_and!.
    - split_and!; [split_and!|exact linw_gdeps_wf|exact linw_gdeps_gmo].
      + exact linw_gwf.
      + exact linw_gppo.
      + exact linw_gload_value.
      + exact linw_gatomicity.
    - exact linw_gwrow.
    - exact linw_rows.
    - exact linw_wperm.
  Qed.
End topo_linw.
(** ** 3.1 EXISTENCE, and the deliverable *)

Theorem topo_exists_w (GD : gdexec) :
  rvwmo_minus_deps_consistent GD →
  (∀ x, ¬ tc (RwwD GD) x x) →
  ∃ L, linw_extD GD L.
Proof.
  intros Hcons Hacy.
  assert (Hnd : NoDup (gx_gmo (gd_g GD))).
  { destruct Hcons as ((Hwf & _ & _ & _) & _ & _).
    by destruct Hwf as (Hn & _ & _). }
  destruct (topo_sort_exists (RwwD GD) (λ x y, rwwD_dec GD x y) Hacy _ Hnd)
    as (L & HL & Hord).
  exists L. split; [exact HL|].
  intros x y HR. destruct (RwwD_mem GD x y Hcons HR) as [Hx Hy].
  by apply Hord.
Qed.

(** THE THEOREM THIS FILE IS FOR.  [gwrow_gmo] at a [gd_equiv] member from
    acyclicity of [RwwD] — strictly weaker than [normalize_ww2]'s
    hypothesis, and in particular compatible with an LB [RacyD] cycle. *)
Theorem normalize_ww3 (GD : gdexec) :
  rvwmo_minus_deps_consistent GD →
  (∀ x, ¬ tc (RwwD GD) x x) →
  ∃ GD', gd_equiv GD GD' ∧ gwrow_gmo (gd_g GD').
Proof.
  intros Hcons Hacy.
  destruct (topo_exists_w GD Hcons Hacy) as (L & Hlin).
  destruct (topo_linearizes_w GD L Hcons Hlin) as (Hc' & Hrow & Hr & Hw).
  exists (GDExec (retime (gd_g GD) L) (gd_deps GD)). split; [|exact Hrow].
  by exists (tren (gd_g GD) L).
Qed.

(** … and [normalize_ww2] is now a corollary. *)
Corollary normalize_ww2_of_ww3 (GD : gdexec) :
  rvwmo_minus_deps_consistent GD →
  (∀ x, ¬ tc (RacyD GD) x x) →
  ∃ GD', gd_equiv GD GD' ∧ gwrow_gmo (gd_g GD').
Proof.
  intros Hcons Hacy.
  apply (normalize_ww3 GD Hcons (RwwD_acyclic_of_RacyD GD Hacy)).
Qed.

(* ====================================================================== *)
(** * 4. SHARPNESS AND TRANSPORT

    [RwwD] has five arms; two of them, [gco] and [gfr], are the ones
    [WeakRvwmoAcyc] §5 shows do NOT transport along [rows_rel]/[wperm]
    (route-b F2′: they are preserved only where the pair is READ-PINNED, or
    where the write-index renaming happens to be monotone on the bytes in
    question).  The other three, together with the dep set the orbit fixes,
    DO transport.  That fragment is [Rwwt]. *)

Definition Rwwt (GD : gdexec) (x y : geid) : Prop :=
  (gpoww (gd_g GD) x y ∨ grf (gd_g GD) x y ∨ gppo (gd_g GD) x y) ∨
  (x, y) ∈ gd_deps GD.

Lemma Rwwt_RwwD GD x y : Rwwt GD x y → RwwD GD x y.
Proof.
  intros [[H|[H|H]]|H];
    [by left; left|by left; right; left
    |by left; right; right; right; right|by right].
Qed.

Lemma Rwwt_gd_equiv GD GD' x y :
  gd_equiv GD GD' → Rwwt GD x y → Rwwt GD' x y.
Proof.
  intros (π & Hr & Hw & Hd & _) [[H|[H|H]]|H].
  - left; left. destruct H as (Hpo & He & Hf). split_and!.
    + by apply (proj2 (rows_rel_gpo π _ _ x y Hr)).
    + by apply (proj2 (rows_rel_glbl_is π _ _ x lb_is_w Hr (lbl_ren_is_w π))).
    + by apply (proj2 (rows_rel_glbl_is π _ _ y lb_is_w Hr (lbl_ren_is_w π))).
  - left; right; left. by apply (proj1 (grf_rows_rel π _ _ x y Hr Hw)).
  - left; right; right. by apply (proj2 (rows_rel_gppo π _ _ x y Hr)).
  - right. by rewrite Hd.
Qed.

Corollary Rwwt_cycle_transport GD GD' x :
  gd_equiv GD GD' → tc (Rwwt GD) x x → tc (Rwwt GD') x x.
Proof.
  intros Heq Htc. eapply tc_mono; [|exact Htc].
  intros a b. by eapply Rwwt_gd_equiv.
Qed.

(** ** 4.1 [Rwwt]-acyclicity is NECESSARY

    At a graph with [gwrow_gmo], every [Rwwt] arm is gmo-forward — the
    [gpoww] arm BY [gwrow_gmo] and the other three by RVWMO⁻ itself. *)
Lemma Rwwt_gmo GD x y :
  rvwmo_minus_deps_consistent GD → gwrow_gmo (gd_g GD) →
  Rwwt GD x y → gmo_lt (gd_g GD) x y.
Proof.
  intros Hcons Hrow HR.
  pose proof Hcons as (Hc & Hdwf & Hdmo).
  pose proof Hc as (Hwf & Hppo & _ & _).
  have Hnd : NoDup (gx_gmo (gd_g GD)) by destruct Hwf as (H & _ & _).
  destruct HR as [[H|[H|H]]|H].
  - destruct H as (Hpo & He & Hf).
    destruct x as [a j], y as [b k]. destruct Hpo as (Hag & Hlt & _ & _).
    simpl in Hag, Hlt. subst b.
    have Hinj : (a, j) ∈ gwrites (gd_g GD)
      by (destruct He as (l & Hl & Hb); eapply gis_w_gwrites;
          [exact Hwf|by exists l|by rewrite /gis_w Hl]).
    have Hink : (a, k) ∈ gwrites (gd_g GD)
      by (destruct Hf as (l & Hl & Hb); eapply gis_w_gwrites;
          [exact Hwf|by exists l|by rewrite /gis_w Hl]).
    split_and!.
    + by eapply gwf_mem_gmo, glbl_is_w_gmem.
    + by eapply gwf_mem_gmo, glbl_is_w_gmem.
    + apply (proj1 (gwix_gpos_lt (gd_g GD) (a, j) (a, k) Hnd Hinj Hink)).
      by apply Hrow.
  - by eapply grf_gmo.
  - by apply Hppo.
  - by apply (Hdmo (x, y)).
Qed.

Theorem Rwwt_acyclic_of_gwrow GD :
  rvwmo_minus_deps_consistent GD → gwrow_gmo (gd_g GD) →
  ∀ x, ¬ tc (Rwwt GD) x x.
Proof.
  intros Hcons Hrow x Htc.
  have Hgmo : gmo_lt (gd_g GD) x x.
  { clear -Hcons Hrow Htc.
    have Hstep : ∀ a b, tc (Rwwt GD) a b → gmo_lt (gd_g GD) a b.
    { intros a b H. induction H as [a b Hab|a b c Hab Hbc IH].
      - by eapply Rwwt_gmo.
      - eapply gmo_lt_trans; [by eapply Rwwt_gmo|exact IH]. }
    by apply Hstep. }
  by eapply gmo_lt_irrefl.
Qed.

(** THE NECESSITY, in the orbit form the residue is stated in: if ANY
    [gd_equiv] member of [GD] has [gwrow_gmo], then [GD]'s own transporting
    fragment is acyclic.  With [normalize_ww3] this sandwiches the residue:

      [RwwD] acyclic  ⇒  ∃ member with [gwrow_gmo]  ⇒  [Rwwt] acyclic,

    and [RwwD] ∖ [Rwwt] is exactly [gco] ∪ [gfr]. *)
Theorem Rwwt_acyclic_necessary GD GD' :
  gd_equiv GD GD' → gwrow_gmo (gd_g GD') → ∀ x, ¬ tc (Rwwt GD) x x.
Proof.
  intros Heq Hrow x Htc.
  pose proof Heq as (_ & _ & _ & _ & Hcons').
  eapply (Rwwt_acyclic_of_gwrow GD' Hcons' Hrow x).
  by eapply Rwwt_cycle_transport.
Qed.

(** ** 4.2 THE FULL CYCLE TRANSPORT, with its exact side condition

    A [RacyD] cycle transports to an orbit member iff its [gco] and [gfr]
    edges do; nothing else in the relation is at risk. *)
Lemma RacyD_transport (GD GD' : gdexec) (π : nat → nat) :
  rows_rel π (gd_g GD) (gd_g GD') → wperm π (gd_g GD) (gd_g GD') →
  gd_deps GD' = gd_deps GD →
  (∀ w w', gco (gd_g GD) w w' → gco (gd_g GD') w w') →
  (∀ r w', gfr (gd_g GD) r w' → gfr (gd_g GD') r w') →
  ∀ x y, RacyD GD x y → RacyD GD' x y.
Proof.
  intros Hr Hw Hd Hco Hfr x y [[H|[H|[H|[H|H]]]]|H].
  - left; left. by apply (proj1 (gpow_rows_rel π _ _ x y Hr)).
  - left; right; left. by apply (proj1 (grf_rows_rel π _ _ x y Hr Hw)).
  - left; right; right; left. by apply Hco.
  - left; right; right; right; left. by apply Hfr.
  - left; right; right; right; right. by apply (proj2 (rows_rel_gppo π _ _ x y Hr)).
  - right. by rewrite Hd.
Qed.

Corollary cycle_transport (GD GD' : gdexec) (π : nat → nat) (x : geid) :
  rows_rel π (gd_g GD) (gd_g GD') → wperm π (gd_g GD) (gd_g GD') →
  gd_deps GD' = gd_deps GD →
  (∀ w w', gco (gd_g GD) w w' → gco (gd_g GD') w w') →
  (∀ r w', gfr (gd_g GD) r w' → gfr (gd_g GD') r w') →
  tc (RacyD GD) x x → tc (RacyD GD') x x.
Proof.
  intros Hr Hw Hd Hco Hfr Htc. eapply tc_mono; [|exact Htc].
  intros a b. by eapply RacyD_transport.
Qed.

(** THE SUFFICIENT INSTANCE the kit already proves: a write-index renaming
    that is MONOTONE discharges both side conditions.  (A normalization
    that genuinely reorders writes is of course not monotone — this is the
    boundary, stated, not a discharge.) *)
Corollary cycle_transport_mono (GD GD' : gdexec) (π : nat → nat) (x : geid) :
  gwf (gd_g GD) → gd_equiv GD GD' →
  rows_rel π (gd_g GD) (gd_g GD') → wperm π (gd_g GD) (gd_g GD') →
  (∀ t1 t2, (t1 < t2)%nat → (π t1 < π t2)%nat) →
  tc (RacyD GD) x x → tc (RacyD GD') x x.
Proof.
  intros Hwf Heq Hr Hw Hmono Htc.
  pose proof Heq as (_ & _ & _ & Hd & Hcons').
  have Hnd' : NoDup (gx_gmo (gd_g GD')).
  { destruct Hcons' as ((H & _ & _ & _) & _ & _). by destruct H as (? & _ & _). }
  eapply (cycle_transport GD GD' π x Hr Hw Hd); [| |exact Htc].
  - intros w w'.
    by apply (gco_rows_rel_mono π _ _ w w' Hwf Hnd' Hr Hw Hmono).
  - intros r w'.
    by apply (gfr_rows_rel_mono π _ _ r w' Hwf Hnd' Hr Hw Hmono).
Qed.

(* ====================================================================== *)
(** * 5. WHERE [gwrow_gmo] IS NEEDED, AND THE OBLIGATION THAT REMAINS

    §2 pinned the use site; this section pins the ARCHITECTURE around it.

    THE WALK RUNS ON THE CYCLIC GRAPH.  [WeakRvwmoLinInd.cycle_kill] — the
    T2-LIN induction step — is applied at a conformant consistent [GD] all
    of whose PROPER HULLS are acyclic, and refutes a cycle AT [GD] by
    running the certification walk THERE ([WeakRvwmoGlue2.walk_supply]'s
    conclusion is [log_of (gd_g GD) …], the log of THAT graph's write
    list).  So [gwrow_gmo] is required exactly where [RacyD] may be cyclic,
    which is exactly where [normalize_ww2]'s hypothesis fails.
    [normalize_ww2] is true and discharges the residue precisely on the
    graphs that need no walk — hence §3.

    THE ORBIT PULL-BACK IS NOT A ROUTE.  [WeakRvwmoPreNorm]'s
    [wsupply_orbit_pull] would carry [wsupply] BACK from the normalized
    member to [GD]; but [gwrow_gmo] is [wsupply]'s first clause, so the
    pull-back asserts that a graph whose normalization is well-supplied is
    ITSELF write-order-normal — i.e. it asserts away the very inversion the
    normalization exists to remove.  Machine-checked: *)
Lemma wsupply_orbit_pull_forces_gwrow (boot : agent → pexv6)
    (d0 : dev_state) (N : nat) (GD GD' : gdexec) :
  wsupply_orbit_pull boot d0 N →
  gd_equiv GD GD' → (∃ W T, wsupply boot d0 (gd_g GD') W T N) →
  gwrow_gmo (gd_g GD).
Proof.
  intros Hpull Heq Hw.
  by destruct (Hpull GD GD' Heq Hw) as (W & T & H & _).
Qed.

(** THE ROUTE THAT IS LEFT, stated as a theorem: run the walk AT THE
    NORMALIZED MEMBER (which is conformant and consistent, by
    [gdexec_qconf_ren] and [gd_equiv]) and transport the CYCLE forward
    rather than the supply backward.  The three obligations are then
    exactly the three hypotheses below. *)
Definition kill_at_member (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) : Prop :=
  ∀ GD GD' : gdexec,
    rvwmo_minus_deps_consistent GD → gdexec_qconf boot d0 im nh GD →
    gd_equiv GD GD' → gwrow_gmo (gd_g GD') →
    (∀ cs, proper_cut (gd_g GD) cs →
           ∀ x, ¬ tc (RacyD (gd_hull GD cs)) x x) →
    ∀ x, tc (RacyD GD') x x → False.

Definition orbit_cycle_transport : Prop :=
  ∀ (GD GD' : gdexec) (x : geid),
    gd_equiv GD GD' → tc (RacyD GD) x x → tc (RacyD GD') x x.

Theorem cycle_kill_of_member (boot : agent → pexv6) (d0 : dev_state)
    (im : image) (nh : nat) :
  kill_at_member boot d0 im nh →
  orbit_cycle_transport →
  (∀ GD : gdexec,
     rvwmo_minus_deps_consistent GD → gdexec_qconf boot d0 im nh GD →
     ∀ x, ¬ tc (RwwD GD) x x) →
  cycle_kill boot d0 im nh.
Proof.
  intros Hkill Htr Hacy GD Hcons Hq Hhulls x Hx.
  destruct (normalize_ww3 GD Hcons (Hacy GD Hcons Hq)) as (GD' & Heq & Hrow).
  exact (Hkill GD GD' Hcons Hq Heq Hrow Hhulls x (Htr GD GD' x Heq Hx)).
Qed.

(** [orbit_cycle_transport] is NOT free — §4.2 says exactly which arms are
    at risk — but its [Rwwt] fragment is, and that is what a cycle built
    out of [rf]/[po]/[ppo]/dep edges (an LB cycle, the shape the kill is
    about) consists of. *)
Corollary orbit_cycle_transport_Rwwt (GD GD' : gdexec) (x : geid) :
  gd_equiv GD GD' → tc (Rwwt GD) x x → tc (RacyD GD') x x.
Proof.
  intros Heq Htc.
  eapply tc_mono; [|exact (Rwwt_cycle_transport GD GD' x Heq Htc)].
  intros a b HR. by apply RwwD_RacyD, Rwwt_RwwD.
Qed.

(** ** 5.1 THE RESIDUE, NAMED

    What replaces [WeakRvwmoPreNorm]'s [ww_gap_link] + orbit acyclicity +
    three kills is ONE acyclicity statement, at [GD] itself. *)
Definition ww_residue (GD : gdexec) : Prop := ∀ x, ¬ tc (RwwD GD) x x.

Theorem ww_residue_gives_gwrow (GD : gdexec) :
  rvwmo_minus_deps_consistent GD → ww_residue GD →
  ∃ GD', gd_equiv GD GD' ∧ gwrow_gmo (gd_g GD') ∧
         gd_deps GD' = gd_deps GD ∧
         ∀ boot d0 im nh, gdexec_qconf boot d0 im nh GD →
           gdexec_qconf boot d0 im nh GD'.
Proof.
  intros Hcons Hres.
  destruct (normalize_ww3 GD Hcons Hres) as (GD' & Heq & Hrow).
  pose proof Heq as (π & Hr & Hw & Hd & Hcons').
  exists GD'. split_and!; [exact Heq|exact Hrow|exact Hd|].
  intros boot d0 im nh Hq. by eapply gdexec_qconf_ren.
Qed.

(** … and it is implied by [RacyD]-acyclicity, so nothing that was
    dischargeable before is lost. *)
Corollary ww_residue_of_acyclic (GD : gdexec) :
  (∀ x, ¬ tc (RacyD GD) x x) → ww_residue GD.
Proof. exact (RwwD_acyclic_of_RacyD GD). Qed.

Print Assumptions normalize_ww2.
Print Assumptions gwrow_seg_iff.
Print Assumptions topo_linearizes_w.
Print Assumptions normalize_ww3.
Print Assumptions Rwwt_acyclic_necessary.
Print Assumptions cycle_transport.
Print Assumptions cycle_kill_of_member.
Print Assumptions ww_residue_gives_gwrow.
