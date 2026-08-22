(** * WeakRvwmoTopo.v — B2d′(a): A TOPOLOGICAL ORDER OF [Racy] *IS* A
      CONSISTENT RULE-14 gmo

    Design: [claude-notes/design/weak-memory-route-b.md] §4d.1 (F2(ii), and
    F2′ for why the [co]/[fr] arms are taken with [G]'s own write order) and
    §4d.4 ("B2d′ — THE KILL-FREE NORMALIZATION, two options; RECOMMENDED:
    the direct linearization").

    THE POINT.  [WeakRvwmoNorm.normalize] reaches a rule-14 graph by the
    exchange induction, and pays for it with the KILL INTERFACE
    ([kill_K1]/[kill_K2]/[kill_K3]) — three residual configurations that the
    kernel-level argument must refute.  F2(ii) says the interface is
    unnecessary: RE-TIME the graph.  Keep the rows and the image; replace
    the global memory order wholesale by ANY list [L] that is a permutation
    of the old order and puts every [Racy] edge forward
    ([WeakRvwmoAcyc.Racy] = po-into-a-write ∪ rf ∪ co ∪ fr ∪ ppo⁻, plus the
    store-dep fragment in [RacyD]).  The result is [rvwmo_minus_deps_-
    consistent] AND [grule14], with exactly [normalize]'s output
    correspondence ([rows_rel] / [wperm] / same deps).  So once T2-LIN
    supplies acyclicity of [RacyD], [normalize]'s conclusion is a corollary
    and the three kills are retired.

    THE RENAMING.  Re-timing moves write INDICES: a read's per-byte [ts]
    entry names the [t]-th write of the OLD order and must be rewritten to
    name the same event's rank in the NEW one.  [tren G L] is that map —
    [tren G L t = gwixL G L w] when [gwrite_at G t = Some w], and [t]
    elsewhere (so [tren G L 0 = 0], the era-initial image, and the junk
    range above the write count is fixed pointwise, which is what makes the
    map INJECTIVE ON ALL OF [nat] as [wperm] demands).  [retime G L] applies
    it to every row.

    THE FOUR AXIOMS, and where each edge class is spent:
      - [gwf]        : [L] is a permutation of a [NoDup] list, membership is
                       a permutation fact, and [lbl_ren] preserves the label
                       shapes;
      - [gppo_gmo]   : ppo⁻ transports backwards along [rows_rel] and is the
                       fifth arm of [Racy];
      - [gload_value]: the source is before the read by [rf]; a same-byte
                       write with a HIGHER old index than the read's entry is
                       excluded by [fr] (and by [gvisible]'s own
                       irreflexivity when it IS the read — the fused-RMW
                       case, which [fr] excludes by construction), and one
                       with a LOWER index stays below by [co];
      - [gatomicity] : [co] gives that [tren] is MONOTONE ON SAME-BYTE
                       WRITES — in both directions, by trichotomy — so a
                       new-order co-interval is an old-order co-interval;
      - [grule14]    : the first arm of [Racy] verbatim;
      - [gdeps_wf]/[gdeps_gmo] : labels transport, and the dep arm of
                       [RacyD] is the order fact.

    ==================================================================
    WHAT HAD TO BE ADJUSTED versus the claim as stated (the probe's real
    output):

    (A) [π] CANNOT BE "[gwix_L] of the write at old index [t], else [t]"
        WITHOUT THE "else" — and the "else" branch is load-bearing for
        INJECTIVITY, not decoration.  [wperm] asks for π injective on ALL of
        [nat], including the junk above the write count; [tren]'s identity
        branch supplies that, and it does not collide with the rank branch
        because the ranks occupy exactly [1 .. length (gwrites G)] while
        [gwrite_at G t = None] means [t = 0] or [t > length (gwrites G)].
        [wperm]'s injectivity then FALLS OUT of its own second clause
        ([gwrite_at G' (π t) = gwrite_at G t]) rather than needing a
        separate argument.

    (B) THE CO-MAX HALF OF [gload_value] HAS A CASE THE F2(ii) SKETCH DOES
        NOT MENTION: [w' = e], a FUSED RMW's own write seen as a same-byte
        write "visible to" its own read.  [gfr] excludes the identity (herd's
        `∖ id`, [WeakRvwmoAcyc]'s correction (3)), so the sketch's "[fr]
        puts it after the read" is unavailable there.  It is discharged
        instead by [gvisible]'s irreflexivity: [gmo_lt G' e e] and
        [gpo G' e e] are both false, so the hypothesis is vacuous.  No new
        model content — but the sketch is incomplete as written.

    (C) [gatomicity] NEEDS THE MONOTONICITY IN THE *BACKWARD* DIRECTION
        (new-order interval ⇒ old-order interval), which [co] alone gives
        only forwards.  The converse comes from trichotomy on the old
        indices plus [gwix_inj]; it needs BOTH events to write the SAME
        byte, which for the RMW's own write is [gread_byte_write_byte]
        (a fused RMW's read footprint IS its write footprint).

    (D) [topo_exists] IS NOT AXIOM-FREE FOR AN ARBITRARY RELATION: picking
        a minimal element of a finite carrier under an acyclic relation is
        CONSTRUCTIVELY IMPOSSIBLE without deciding the relation (with
        [M = [a;b]] and no information about [R a b] / [R b a] there is no
        way to choose).  So [topo_exists] carries the hypothesis
        [∀ x y, Decision (RacyD GD x y)].  It is a genuine side condition,
        not a hole: [RacyD] is a bounded search over the rows (every
        existential in [greads_byte] / [gwrites_byte] / [gfence_between] is
        pinned by a list index), so the instance is provable — it is simply
        not proved here.  RECORDED AS THE ONE OPEN ITEM OF THIS SLICE.
        Note that [topo_linearizes] — the deliverable — needs NOTHING of the
        sort.

    (E) The minimal-element search needed only [Decision (R x y)], not
        [Decision (tc R x y)]: the descent [topo_min_desc] walks DOWN one
        [R]-edge at a time inside a shrinking list, and acyclicity of [tc R]
        is what stops [a] from re-entering.  (The naive induction "take the
        minimum of the tail, then compare [a] against it" does need [tc]
        decided; this one does not.)
    ==================================================================

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakAxiomatic WeakAxiomatic2
                            WeakRvwmoGraph WeakRvwmoXchg WeakRvwmoNorm
                            WeakRvwmoAcyc.

(* ====================================================================== *)
(** * 1. [before]: the order a list induces *)

Definition before {A} (L : list A) (x y : A) : Prop :=
  ∃ i j, L !! i = Some x ∧ L !! j = Some y ∧ (i < j)%nat.

Lemma before_cons {A} (m : A) L x y : before L x y → before (m :: L) x y.
Proof.
  intros (i & j & Hi & Hj & Hlt). exists (S i), (S j). split_and!; [done|done|lia].
Qed.

Lemma perm_elem_of {A} (l1 l2 : list A) (x : A) : l1 ≡ₚ l2 → (x ∈ l1 ↔ x ∈ l2).
Proof. intros Hp. by rewrite Hp. Qed.

Lemma before_head {A} (m : A) L y : y ∈ L → before (m :: L) m y.
Proof.
  intros [j Hj]%elem_of_list_lookup. exists 0%nat, (S j).
  split_and!; [done|done|lia].
Qed.

(* ====================================================================== *)
(** * 2. RE-TIMING: the new order, and the write-index renaming it forces *)

(** The rank (1-based, exactly as [gwix]) of [w] among the writes of [L]. *)
Definition gwixL (G : gexec) (L : list geid) (w : geid) : nat :=
  match list_find (λ e', e' = w) (filter (gis_w G) L) with
  | Some (i, _) => S i
  | None => 0%nat
  end.

(** The write-index renaming: old index ↦ new index of the SAME write.
    Off the write range (0, and anything above the write count) the map is
    the identity — see the header's (A). *)
Definition tren (G : gexec) (L : list geid) (t : nat) : nat :=
  match gwrite_at G t with
  | Some w => gwixL G L w
  | None => t
  end.

Definition retime (G : gexec) (L : list geid) : gexec :=
  {| gx_img := gx_img G;
     gx_prog := (λ row : list lbl, lbl_ren (tren G L) <$> row) <$> gx_prog G;
     gx_gmo := L |}.

(** A LINEAR EXTENSION of [Racy] — the input the re-timing consumes. *)
Definition lin_ext (G : gexec) (L : list geid) : Prop :=
  L ≡ₚ gx_gmo G ∧ ∀ x y, Racy G x y → before L x y.

(** … and its [gdexec] form (the store-dep fragment ordered too). *)
Definition lin_extD (GD : gdexec) (L : list geid) : Prop :=
  L ≡ₚ gx_gmo (gd_g GD) ∧ ∀ x y, RacyD GD x y → before L x y.

Lemma lin_extD_lin_ext GD L : lin_extD GD L → lin_ext (gd_g GD) L.
Proof. intros (HL & Hord). split; [done|]. intros x y HR. apply Hord. by left. Qed.

(** ** 2.1 The hypothesis-free half of the correspondence *)

Lemma tren_zero G L : tren G L 0%nat = 0%nat.
Proof. done. Qed.

Lemma tren_at G L t w : gwrite_at G t = Some w → tren G L t = gwixL G L w.
Proof. intros Ht. by rewrite /tren Ht. Qed.

Lemma tren_none G L t : gwrite_at G t = None → tren G L t = t.
Proof. intros Ht. by rewrite /tren Ht. Qed.

Lemma retime_rows_rel G L : rows_rel (tren G L) G (retime G L).
Proof. split_and!; [done|done|apply tren_zero]. Qed.

Lemma retime_gis_w G L e : gis_w (retime G L) e = gis_w G e.
Proof. apply (rows_rel_gis_w _ G _ e (retime_rows_rel G L)). Qed.

Lemma retime_gwrites G L : gwrites (retime G L) = filter (gis_w G) L.
Proof.
  rewrite /gwrites /=. apply list_filter_iff. intros x.
  by rewrite retime_gis_w.
Qed.

Lemma retime_gwix G L w : gwix (retime G L) w = gwixL G L w.
Proof. by rewrite /gwix /gwixL retime_gwrites. Qed.

(** [lbl_ren] preserves [gwf]'s shape clause. *)
Lemma lbl_ren_shape (pi : nat → nat) (l : lbl) :
  (match l with
   | LLoad _ _ ts vs => length vs = length ts
   | LStore _ _ vs _ => vs ≠ []
   | LFence _ _ _ _ => True
   | LRmw _ _ _ ts rvs wvs _ =>
       wvs ≠ [] ∧ length wvs = length ts ∧ length rvs = length ts
   end) →
  (match lbl_ren pi l with
   | LLoad _ _ ts vs => length vs = length ts
   | LStore _ _ vs _ => vs ≠ []
   | LFence _ _ _ _ => True
   | LRmw _ _ _ ts rvs wvs _ =>
       wvs ≠ [] ∧ length wvs = length ts ∧ length rvs = length ts
   end).
Proof. destruct l; simpl; rewrite ?length_fmap; done. Qed.

(* ====================================================================== *)
(** * 3. THE LINEARIZATION THEOREM *)

Section topo_lin.
  Context (GD : gdexec) (L : list geid).
  Context (Hcons : rvwmo_minus_deps_consistent GD).
  Context (Hlin : lin_extD GD L).

  Local Notation G := (gd_g GD).
  Local Notation G' := (retime (gd_g GD) L).
  Local Notation pi := (tren (gd_g GD) L).

  Local Lemma lin_wf : gwf G.
  Proof. apply Hcons. Qed.
  Local Lemma lin_lv : gload_value G.
  Proof. apply Hcons. Qed.
  Local Lemma lin_at : gatomicity G.
  Proof. apply Hcons. Qed.
  Local Lemma lin_perm : L ≡ₚ gx_gmo G.
  Proof. apply Hlin. Qed.

  Local Lemma lin_rows : rows_rel pi G G'.
  Proof. apply retime_rows_rel. Qed.

  (** ** 3.1 [L] is a well-formed order, and [pi] is a write permutation *)

  Local Lemma lin_nodup : NoDup L.
  Proof. rewrite lin_perm. by destruct lin_wf as (? & _ & _). Qed.

  Local Lemma lin_wfilter : filter (gis_w G) L ≡ₚ gwrites G.
  Proof. rewrite /gwrites. by rewrite lin_perm. Qed.

  Local Lemma lin_wlen : length (gwrites G') = length (gwrites G).
  Proof. rewrite retime_gwrites. by rewrite lin_wfilter. Qed.

  Local Lemma lin_welem w : w ∈ gwrites G' ↔ w ∈ gwrites G.
  Proof. rewrite retime_gwrites. by rewrite lin_wfilter. Qed.

  Local Lemma lin_wat t : gwrite_at G' (pi t) = gwrite_at G t.
  Proof.
    destruct (gwrite_at G t) as [w|] eqn:Ht.
    - rewrite (tren_at G L t w Ht) -retime_gwix.
      apply gwrite_at_gwix, lin_welem. by eapply gwrite_at_gwrites.
    - rewrite (tren_none G L t Ht). destruct t as [|i]; [done|].
      rewrite /gwrite_at. apply lookup_ge_None. rewrite lin_wlen.
      rewrite /gwrite_at in Ht. by apply lookup_ge_None in Ht.
  Qed.

  Local Lemma lin_wperm : wperm pi G G'.
  Proof.
    split_and!; [|exact lin_wat|exact lin_wlen].
    intros t1 t2 Heq.
    pose proof (lin_wat t1) as H1. pose proof (lin_wat t2) as H2.
    rewrite Heq H2 in H1.
    destruct (gwrite_at G t1) as [w|] eqn:E1.
    - destruct (gwrite_at_inv G t1 w ltac:(by destruct lin_wf as (?&_&_)) E1)
        as (_ & <-).
      destruct (gwrite_at_inv G t2 w ltac:(by destruct lin_wf as (?&_&_)) H1)
        as (_ & <-). done.
    - rewrite -(tren_none G L t1 E1) -(tren_none G L t2 H1). exact Heq.
  Qed.

  (** ** 3.2 The bridge: [before L] IS [gmo_lt] of the re-timed graph *)

  Local Lemma lin_before x y : before L x y ↔ gmo_lt G' x y.
  Proof.
    pose proof lin_nodup as Hnd. split.
    - intros (i & j & Hi & Hj & Hlt). split_and!.
      + by eapply elem_of_list_lookup_2.
      + by eapply elem_of_list_lookup_2.
      + rewrite (gpos_of_lookup G' i x Hnd Hi) (gpos_of_lookup G' j y Hnd Hj). lia.
    - intros (Hx & Hy & Hlt). exists (gpos G' x), (gpos G' y).
      split_and!; [by apply gpos_elem_lookup|by apply gpos_elem_lookup|lia].
  Qed.

  Local Lemma step_racy x y : Racy G x y → gmo_lt G' x y.
  Proof. intros HR. apply lin_before, (proj2 Hlin). by left. Qed.

  Local Lemma step_dep x y : (x, y) ∈ gd_deps GD → gmo_lt G' x y.
  Proof. intros Hd. apply lin_before, (proj2 Hlin). by right. Qed.

  (** ** 3.3 [pi] is MONOTONE ON SAME-BYTE WRITES, both ways *)

  Local Lemma lin_co_fwd w1 w2 a u1 u2 :
    gwrites_byte G w1 a u1 → gwrites_byte G w2 a u2 →
    (gwix G w1 < gwix G w2)%nat → (gwix G' w1 < gwix G' w2)%nat.
  Proof.
    intros H1 H2 Hlt.
    assert (Hmo : gmo_lt G' w1 w2).
    { apply step_racy. right; right; left. by exists a, u1, u2. }
    apply (gwix_gpos_lt G' w1 w2 lin_nodup).
    - apply lin_welem. by eapply gwrites_byte_in_gwrites; [apply lin_wf|].
    - apply lin_welem. by eapply gwrites_byte_in_gwrites; [apply lin_wf|].
    - by destruct Hmo as (_ & _ & ?).
  Qed.

  Local Lemma lin_co_inv w1 w2 a u1 u2 :
    gwrites_byte G w1 a u1 → gwrites_byte G w2 a u2 →
    (gwix G' w1 < gwix G' w2)%nat → (gwix G w1 < gwix G w2)%nat.
  Proof.
    intros H1 H2 Hlt.
    pose proof (gwrites_byte_in_gwrites G w1 a u1 lin_wf H1) as Hin1.
    pose proof (gwrites_byte_in_gwrites G w2 a u2 lin_wf H2) as Hin2.
    destruct (decide (gwix G w1 < gwix G w2)%nat) as [?|Hge]; [done|]. exfalso.
    destruct (decide (gwix G w1 = gwix G w2)) as [Heq|Hne].
    - assert (w1 = w2) as ->.
      { eapply gwix_inj; [|exact Hin1|exact Hin2|exact Heq].
        by destruct lin_wf as (?&_&_). }
      lia.
    - pose proof (lin_co_fwd w2 w1 a u2 u1 H2 H1 ltac:(lia)). lia.
  Qed.

  (** ** 3.4 The axioms of the re-timed graph *)

  Local Lemma lin_gwf : gwf G'.
  Proof.
    pose proof lin_wf as (Hnd & Hmem & Hsh). split_and!.
    - exact lin_nodup.
    - intros e. split.
      + intros He. apply (rows_rel_gmem _ G G' e lin_rows), Hmem.
        by apply (perm_elem_of L (gx_gmo G) e lin_perm).
      + intros He. apply (perm_elem_of L (gx_gmo G) e lin_perm), Hmem.
        by apply (rows_rel_gmem _ G G' e lin_rows).
    - intros i p k l Hp Hk.
      rewrite /= list_lookup_fmap in Hp. apply fmap_Some in Hp as (r & Hr & ->).
      rewrite list_lookup_fmap in Hk. apply fmap_Some in Hk as (l0 & Hl0 & ->).
      apply lbl_ren_shape. by eapply Hsh.
  Qed.

  Local Lemma lin_gppo : gppo_gmo G'.
  Proof.
    intros e1 e2 Hppo'. apply step_racy. right; right; right; right.
    by apply (proj1 (rows_rel_gppo _ G G' e1 e2 lin_rows)).
  Qed.

  Local Lemma lin_grule14 : grule14 G'.
  Proof.
    intros e w Hpo Hmem Hw. apply step_racy. left. split_and!.
    - by apply (proj1 (rows_rel_gpo _ G G' e w lin_rows)).
    - by apply (proj1 (rows_rel_gmem _ G G' e lin_rows)).
    - apply glbl_is_w_gis_w.
      by apply (proj1 (rows_rel_glbl_is _ G G' w lb_is_w lin_rows
                        (lbl_ren_is_w pi))).
  Qed.

  Local Lemma lin_gload_value : gload_value G'.
  Proof.
    intros e a t' v Hrd'.
    destruct (rows_rel_rdb_inv pi G G' e a t' v lin_rows Hrd')
      as (t & -> & Hrd).
    pose proof lin_lv as Hlv. pose proof lin_wf as Hwf.
    destruct (Hlv e a t v Hrd) as [Hsrc Hmax].
    pose proof lin_wperm as Hwp. pose proof (proj1 Hwp) as Hinj.
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
        * rewrite -Hpt lin_wat. exact Hwat.
        * by apply (proj2 (rows_rel_wrb _ G G' w a v lin_rows)).
        * left. apply step_racy. right; left. by exists a, (S t0), v.
    - intros w' v' Hwb' Hvis'.
      assert (Hwb : gwrites_byte G w' a v')
        by (by apply (proj1 (rows_rel_wrb _ G G' w' a v' lin_rows))).
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
            by (by apply (proj1 (rows_rel_gpo _ G G' w' e lin_rows))).
          assert (Hwe : gmo_lt G' w' e).
          { apply step_racy. right; right; right; right. left.
            split; [exact Hpo|]. exists a. split.
            - left. by exists v'.
            - right. by exists t, v. }
          eapply gmo_lt_irrefl. by eapply gmo_lt_trans; [exact Hew|exact Hwe]. }
      destruct (decide (t < gwix G w')%nat) as [Hgt|Hle].
      + exfalso. apply Hnv. apply step_racy. right; right; right; left.
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
          eapply (lin_co_fwd w' w a v' v Hwb Hwbw). lia.
  Qed.

  Local Lemma lin_gatomicity : gatomicity G'.
  Proof.
    intros e a t' v Hrd' Hw' w' v' Hwb' [Hlt1 Hlt2].
    destruct (rows_rel_rdb_inv pi G G' e a t' v lin_rows Hrd')
      as (t & Hpt & Hrd).
    pose proof lin_wf as Hwf.
    assert (Hw : glbl_is G e lb_is_w)
      by (by apply (proj1 (rows_rel_glbl_is _ G G' e lb_is_w lin_rows
                            (lbl_ren_is_w pi)))).
    assert (Hwb : gwrites_byte G w' a v')
      by (by apply (proj1 (rows_rel_wrb _ G G' w' a v' lin_rows))).
    pose proof (gwrites_byte_in_gwrites G w' a v' Hwf Hwb) as Hw'in.
    destruct (gread_byte_write_byte G e a t v Hwf (glbl_is_w_gis_w G e Hw) Hrd)
      as (ve & Hwbe).
    (* the upper bound *)
    assert (Hup : (gwix G w' < gwix G e)%nat).
    { eapply (lin_co_inv w' e a v' ve Hwb Hwbe). lia. }
    (* the lower bound *)
    assert (Hlow : (t < gwix G w')%nat).
    { destruct t as [|t0].
      - pose proof (gwix_pos G w' Hw'in). lia.
      - destruct (proj1 (lin_lv e a (S t0) v Hrd)) as (w & Hwat & Hwbw & _).
        assert (Hwix : gwix G w = S t0).
        { by destruct (gwrite_at_inv G (S t0) w
                         ltac:(by destruct Hwf as (?&_&_)) Hwat) as (_ & ->). }
        assert (Hgw : gwix G' w = t').
        { rewrite retime_gwix Hpt. by rewrite (tren_at G L (S t0) w Hwat). }
        rewrite -Hwix. eapply (lin_co_inv w w' a v v' Hwbw Hwb). lia. }
    by eapply lin_at; [exact Hrd|exact Hw|exact Hwb|].
  Qed.

  Local Lemma lin_gdeps_wf : gdeps_wf G' (gd_deps GD).
  Proof.
    intros rw Hrw. destruct Hcons as (_ & Hdwf & _).
    destruct (Hdwf rw Hrw) as (H1 & H2 & H3 & H4). split_and!; [done|done| |].
    - by apply (proj2 (rows_rel_glbl_is _ G G' rw.1 lb_is_r lin_rows
                        (lbl_ren_is_r pi))).
    - by apply (proj2 (rows_rel_glbl_is _ G G' rw.2 lb_is_w lin_rows
                        (lbl_ren_is_w pi))).
  Qed.

  Local Lemma lin_gdeps_gmo : gdeps_gmo G' (gd_deps GD).
  Proof.
    intros rw Hrw. destruct rw as [r w]. apply step_dep. exact Hrw.
  Qed.

  (** THE DELIVERABLE. *)
  Theorem topo_linearizes :
    rvwmo_minus_deps_consistent (GDExec G' (gd_deps GD)) ∧
    grule14 G' ∧
    rows_rel pi G G' ∧
    wperm pi G G'.
  Proof.
    split_and!.
    - split_and!; [split_and!|exact lin_gdeps_wf|exact lin_gdeps_gmo].
      + exact lin_gwf.
      + exact lin_gppo.
      + exact lin_gload_value.
      + exact lin_gatomicity.
    - exact lin_grule14.
    - exact lin_rows.
    - exact lin_wperm.
  Qed.
End topo_lin.

(* ====================================================================== *)
(** * 4. EXISTENCE: a finite topological sort

    See the header's (D)/(E): a minimal element of a finite carrier under an
    acyclic relation cannot be produced constructively without deciding the
    relation, so this section takes [Decision (R x y)] — and NOTHING more
    (in particular not [Decision (tc R x y)]). *)

Lemma list_ex_dec {A} (P : A → Prop) (Pdec : ∀ x, Decision (P x)) (l : list A) :
  ({x : A | x ∈ l ∧ P x} + (∀ x, x ∈ l → ¬ P x))%type.
Proof.
  induction l as [|a l IH].
  - right. intros x Hx. by apply elem_of_nil in Hx.
  - destruct (Pdec a) as [Hp|Hnp].
    + left. exists a. split; [by left|done].
    + destruct IH as [[x [Hx Hpx]]|Hno].
      * left. exists x. split; [by right|done].
      * right. intros x Hx. apply elem_of_cons in Hx as [->|Hx];
          [done|by apply Hno].
Qed.

Section topo_sort.
  Context {A : Type} (R : relation A).
  Context (Rdec : ∀ x y, Decision (R x y)).
  Context (Hacy : ∀ x, ¬ tc R x x).

  (** DESCEND to a minimal element: from any [a ∈ M], walk one [R]-edge down
      at a time inside a shrinking list.  Acyclicity is what keeps the
      dropped element from being a predecessor of the result. *)
  Local Lemma topo_min_desc (n : nat) (M : list A) :
    (length M ≤ n)%nat → NoDup M → ∀ a, a ∈ M →
    ∃ m, m ∈ M ∧ (m = a ∨ tc R m a) ∧ (∀ y, y ∈ M → ¬ R y m).
  Proof.
    revert M. induction n as [|n IH]; intros M Hlen Hnd a Ha.
    { destruct M as [|z M]; [by apply elem_of_nil in Ha|simpl in Hlen; lia]. }
    destruct (list_ex_dec (λ y, R y a) (λ y, Rdec y a) M)
      as [[y [Hy Hry]]|Hno].
    - assert (Hya : y ≠ a).
      { intros ->. by eapply Hacy, tc_once. }
      apply elem_of_Permutation in Ha as (M1 & Hperm).
      assert (Hnd' : NoDup (a :: M1)) by (by rewrite -Hperm).
      assert (Hy1 : y ∈ M1).
      { rewrite Hperm in Hy. apply elem_of_cons in Hy as [Heq|Hy1];
          [by destruct (Hya Heq)|exact Hy1]. }
      assert (Hlen1 : (length M1 ≤ n)%nat).
      { assert (length M = length (a :: M1)) as HeqL
          by (by apply (length_Permutation_proper _ _ Hperm)).
        simpl in HeqL. lia. }
      destruct (IH M1 Hlen1 (NoDup_cons_1_2 _ _ Hnd') y Hy1)
        as (m & Hm & Hmy & Hmin).
      assert (Hma : tc R m a).
      { destruct Hmy as [->|Hmy]; [by apply tc_once|].
        eapply tc_r; [exact Hmy|exact Hry]. }
      exists m. split_and!.
      + rewrite Hperm. by right.
      + by right.
      + intros z Hz Hrz. rewrite Hperm in Hz.
        apply elem_of_cons in Hz as [->|Hz]; [|by eapply Hmin].
        eapply Hacy. eapply tc_l; [exact Hrz|exact Hma].
    - exists a. split_and!; [done|by left|done].
  Qed.

  Local Lemma topo_min (M : list A) :
    NoDup M → ∀ a, a ∈ M → ∃ m, m ∈ M ∧ (∀ y, y ∈ M → ¬ R y m).
  Proof.
    intros Hnd a Ha.
    destruct (topo_min_desc (length M) M (Nat.le_refl _) Hnd a Ha)
      as (m & Hm & _ & Hmin).
    by exists m.
  Qed.

  Local Lemma topo_sort_aux (n : nat) (M : list A) :
    (length M ≤ n)%nat → NoDup M →
    ∃ L, L ≡ₚ M ∧ (∀ x y, x ∈ M → y ∈ M → R x y → before L x y).
  Proof.
    revert M. induction n as [|n IH]; intros M Hlen Hnd.
    { destruct M as [|z M]; [|simpl in Hlen; lia].
      exists []. split; [done|]. intros x y Hx. by apply elem_of_nil in Hx. }
    destruct M as [|a M0].
    { exists []. split; [done|]. intros x y Hx. by apply elem_of_nil in Hx. }
    destruct (topo_min (a :: M0) Hnd a ltac:(by left)) as (m & Hm & Hmin).
    apply elem_of_Permutation in Hm as (M1 & Hperm).
    assert (Hnd1 : NoDup (m :: M1)) by (by rewrite -Hperm).
    assert (Hlen1 : (length M1 ≤ n)%nat).
    { assert (length (a :: M0) = length (m :: M1)) as HeqL
        by (by apply (length_Permutation_proper _ _ Hperm)).
      simpl in HeqL, Hlen. lia. }
    destruct (IH M1 Hlen1 (NoDup_cons_1_2 _ _ Hnd1)) as (L1 & HL1 & Hord).
    exists (m :: L1). split.
    { rewrite HL1. by rewrite -Hperm. }
    intros x y Hx Hy Hr.
    assert (Hym : y ≠ m) by (intros ->; by apply (Hmin x Hx)).
    assert (Hy1 : y ∈ M1).
    { rewrite Hperm in Hy. apply elem_of_cons in Hy as [Heq|Hy1];
        [by destruct (Hym Heq)|exact Hy1]. }
    assert (Hx' : x = m ∨ x ∈ M1).
    { rewrite Hperm in Hx. by apply elem_of_cons in Hx. }
    destruct Hx' as [->|Hx1].
    - apply before_head. by rewrite HL1.
    - apply before_cons. apply Hord; [done|done|done].
  Qed.

  Lemma topo_sort_exists (M : list A) :
    NoDup M → ∃ L, L ≡ₚ M ∧ (∀ x y, x ∈ M → y ∈ M → R x y → before L x y).
  Proof. intros Hnd. by eapply topo_sort_aux. Qed.
End topo_sort.

(** Every [RacyD] edge runs between members of the order.  (Not derivable
    from [WeakRvwmoAcyc.RD_gmo] here: that route needs [grule14], which is
    exactly what we are trying to reach.) *)
Lemma RacyD_mem GD x y :
  rvwmo_minus_deps_consistent GD → RacyD GD x y →
  x ∈ gx_gmo (gd_g GD) ∧ y ∈ gx_gmo (gd_g GD).
Proof.
  intros (Hc & Hdwf & _) HR. pose proof Hc as (Hwf & _ & _ & _).
  destruct HR as [[H|[H|[H|[H|H]]]]|Hd].
  - destruct H as (_ & Hm & Hw). split.
    + by eapply gwf_mem_gmo.
    + by eapply gwf_mem_gmo, gis_w_gmem.
  - split.
    + by eapply gwf_mem_gmo, gis_w_gmem, grf_gis_w.
    + by eapply gwf_mem_gmo, grf_gmem_r.
  - destruct H as (a & v & v' & H1 & H2 & _). split; by eapply gwrites_byte_gmo.
  - destruct H as (_ & a & t & v & v' & H1 & H2 & _).
    split; [by eapply greads_byte_gmo|by eapply gwrites_byte_gmo].
  - destruct (gppo_gmem _ _ _ H) as [H1 H2]. split; by eapply gwf_mem_gmo.
  - destruct (Hdwf (x, y) Hd) as (_ & _ & H1 & H2). simpl in H1, H2.
    split.
    + by eapply gwf_mem_gmo, glbl_is_r_gmem.
    + by eapply gwf_mem_gmo, glbl_is_w_gmem.
Qed.

(** THE EXISTENCE THEOREM. *)
Theorem topo_exists (GD : gdexec) :
  rvwmo_minus_deps_consistent GD →
  (∀ x y, Decision (RacyD GD x y)) →
  (∀ x, ¬ tc (RacyD GD) x x) →
  ∃ L, lin_extD GD L.
Proof.
  intros Hcons Hdec Hacy.
  assert (Hnd : NoDup (gx_gmo (gd_g GD))).
  { destruct Hcons as ((Hwf & _ & _ & _) & _ & _).
    by destruct Hwf as (Hn & _ & _). }
  destruct (topo_sort_exists (RacyD GD) Hdec Hacy _ Hnd) as (L & HL & Hord).
  exists L. split; [exact HL|].
  intros x y HR. destruct (RacyD_mem GD x y Hcons HR) as [Hx Hy].
  by apply Hord.
Qed.

(* ====================================================================== *)
(** * 5. THE COROLLARY: [normalize]'s conclusion, from acyclicity alone *)

Corollary normalize_of_acyclic (GD : gdexec) :
  rvwmo_minus_deps_consistent GD →
  (∀ x y, Decision (RacyD GD x y)) →
  (∀ x, ¬ tc (RacyD GD) x x) →
  ∃ (GD' : gdexec) (pi : nat → nat),
    rvwmo_minus_deps_consistent GD' ∧
    grule14 (gd_g GD') ∧
    rows_rel pi (gd_g GD) (gd_g GD') ∧
    gd_deps GD' = gd_deps GD ∧
    wperm pi (gd_g GD) (gd_g GD').
Proof.
  intros Hcons Hdec Hacy.
  destruct (topo_exists GD Hcons Hdec Hacy) as (L & Hlin).
  destruct (topo_linearizes GD L Hcons Hlin) as (Hc' & H14 & Hr & Hw).
  by exists (GDExec (retime (gd_g GD) L) (gd_deps GD)), (tren (gd_g GD) L).
Qed.

Print Assumptions topo_linearizes.
Print Assumptions topo_exists.
Print Assumptions normalize_of_acyclic.
