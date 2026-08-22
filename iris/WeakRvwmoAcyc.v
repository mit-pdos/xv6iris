(** * WeakRvwmoAcyc.v — rule-14 linearizability ⇒ R acyclic
      (route-b §4d.1 F2, corrected: R includes co and fr — B2d's K3/K2 shapes)

    Design: [claude-notes/design/weak-memory-route-b.md] §4d.1 F2 and §4d.4
    ("B2e-3a (i)"), with the ORCHESTRATOR'S SCOPE CORRECTION: the obligation
    relation is not `po ∪ rf` but the full herd-style union

      R := po-into-a-write  ∪  rf  ∪  co  ∪  fr  ∪  ppo⁻          (§2)

    (and, over a [gdexec], the store-dep fragment as well — [RD]).  Every
    arm of R is gmo-forward in a rule-14 consistent graph, and [gmo_lt] is a
    STRICT ORDER, so R-acyclicity is immediate rather than an induction:

      [R_gmo]     : rvwmo_minus_consistent G → grule14 G → R G x y → gmo_lt G x y
      [R_acyclic] : … → tc (R G) x x → False                       (THE THEOREM)
      [RD_gmo] / [RD_acyclic]                       — the same over a [gdexec].

    Also delivered, because `po ∪ rf` is NOT a sub-relation of R (a po edge
    into a READ is in neither) and route B's F2 sentence is about it:

      [gcaus_acyclic] : rvwmo_minus_consistent G → grule14 G →
                        tc (gcaus G) x x → False

    proved by its own induction: a causality path from a REFLEXIVE-PO PREFIX
    of a memory event to a WRITE is gmo-forward ([caus_write_gmo]); a cycle
    carries a write ([caus_write_on_path]); rotate to it.

    THREE STATEMENT CORRECTIONS the mechanization forced, each recorded here
    because the design's prose has the uncorrected shape:

    (1) [grule14]'s antecedent carries [gmem G e], and it MUST: [gpo] ranges
        over all program events, FENCES included, and a fence is not in
        [gmo] at all ([gwf]'s membership clause), so "po-before a write ⇒
        gmo-before it" is FALSE for a fence source.  Hence [gpow] is
        [gpo ∧ gmem ∧ gis_w], not [gpo ∧ gis_w].
    (2) [gfr] must be BYTE-MATCHED — `rf⁻¹ ; co` with the co edge at the very
        byte the read read.  A co edge at some OTHER byte of a multi-byte
        write carries no load-value information and is not gmo-forward.
    (3) [gfr] must EXCLUDE THE IDENTITY.  A fused RMW reads byte [a] at index
        [t] and writes [a] at index [gwix > t], so the un-restricted
        `rf⁻¹ ; co` is REFLEXIVE at every RMW; herd spells this
        `fr = (rf⁻¹ ; co) ∖ id` for exactly this reason.

    TRANSPORT along the normalization's output correspondence
    ([rows_rel] / [wperm], [WeakRvwmoNorm.v] §3) — §5.  [gpo], [gpow], [grf],
    [gppo] and [gcaus] transport, so acyclicity of the rows-equivalent graph's
    relation pulls back:

      [gcaus_acyclic_orbit] / [Rt_acyclic_orbit].

    A NEGATIVE RESULT, and it is the interesting one: [gco] and [gfr] DO NOT
    transport.  [wperm]'s π is an arbitrary INJECTION on write indices — B2d's
    (W,W) exchange renames by a NON-MONOTONE transposition, and §3's own
    header says so — while [gco]/[gfr] are statements about the ORDER of write
    indices.  Nor is this an artifact of the correspondence being too weak:
    the co-order of two same-byte writes that nothing reads is unconstrained
    by [rvwmo_minus_consistent], so two rows-equivalent consistent graphs can
    genuinely disagree on it.  §5 therefore states the co/fr transport under
    an explicit MONOTONICITY hypothesis on π ([gco_rows_rel_mono],
    [gfr_rows_rel_mono]), and the unconditional orbit corollary is for the
    transporting fragment [Rt := gpow ∪ grf ∪ gppo] only.

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakAxiomatic WeakAxiomatic2
                            WeakRvwmoGraph WeakRvwmoXchg WeakRvwmoNorm.

(* ====================================================================== *)
(** * 1. Small bridges the graph file does not export *)

(** [gis_w] is a [match] on [gx_lbl], so it certifies its own [Some]. *)
Lemma gis_w_glbl_is G e : gis_w G e = true → glbl_is G e lb_is_w.
Proof.
  intros Hw. rewrite /gis_w in Hw.
  destruct (gx_lbl G e) as [l|] eqn:Hl; [|done]. by exists l.
Qed.

Lemma gis_w_gmem G e : gis_w G e = true → gmem G e.
Proof. intros Hw. by apply glbl_is_w_gmem, gis_w_glbl_is. Qed.

(** A named write index denotes a member of the write sub-order. *)
Lemma gwrite_at_gwrites G t w : gwrite_at G t = Some w → w ∈ gwrites G.
Proof. destruct t as [|i]; [done|]. apply gwrites_lookup_elem. Qed.

Lemma gwrites_byte_in_gwrites G e a v :
  gwf G → gwrites_byte G e a v → e ∈ gwrites G.
Proof.
  intros Hwf Hw. apply gwrites_elem_of. split.
  - eapply gwf_mem_gmo; [done|]. eapply gaccesses_gmem. left. by exists v.
  - by eapply gwrites_byte_gis_w.
Qed.

Lemma gwrites_byte_gmo G e a v : gwf G → gwrites_byte G e a v → e ∈ gx_gmo G.
Proof.
  intros Hwf Hw.
  by pose proof (gwrites_byte_in_gwrites G e a v Hwf Hw) as
    [? _]%gwrites_elem_of.
Qed.

Lemma greads_byte_gmo G e a t v : gwf G → greads_byte G e a t v → e ∈ gx_gmo G.
Proof.
  intros Hwf Hrd. eapply gwf_mem_gmo; [done|].
  eapply gaccesses_gmem. right. by exists t, v.
Qed.

(** [gpo] is a strict order (it compares offsets inside one hart). *)
Lemma gpo_irrefl G x : ¬ gpo G x x.
Proof. intros (_ & Hlt & _). lia. Qed.

Lemma gpo_trans G x y z : gpo G x y → gpo G y z → gpo G x z.
Proof.
  intros (H1 & H2 & H3 & _) (H4 & H5 & _ & H6).
  split_and!; [congruence|lia|done|done].
Qed.

(** A sub-relation's transitive closure is inside the larger one's.  (Needed
    as a NAMED lemma rather than an inline [induction]: the goal of an
    acyclicity proof mentions [x] in both index positions of the closure, so
    [induction] on the hypothesis cannot generalize it.) *)
Lemma tc_mono {A} (R1 R2 : relation A) x y :
  (∀ a b, R1 a b → R2 a b) → tc R1 x y → tc R2 x y.
Proof.
  intros Hsub. induction 1 as [a b H|a b c H _ IH].
  - by apply tc_once, Hsub.
  - eapply tc_l; [by apply Hsub|exact IH].
Qed.

(* ====================================================================== *)
(** * 2. THE RELATIONS *)

(** [grf]: [r] reads a byte from the write [w]. *)
Definition grf (G : gexec) (w r : geid) : Prop :=
  ∃ a t v, greads_byte G r a t v ∧ gwrite_at G t = Some w.

(** [gcaus]: route B's F2 sentence's relation, `po ∪ rf`. *)
Definition gcaus (G : gexec) (x y : geid) : Prop := gpo G x y ∨ grf G x y.

(** [gco]: the same-byte write order, read off the write indices. *)
Definition gco (G : gexec) (w w' : geid) : Prop :=
  ∃ a v v', gwrites_byte G w a v ∧ gwrites_byte G w' a v' ∧
            (gwix G w < gwix G w')%nat.

(** [gfr]: `rf⁻¹ ; co ∖ id`, byte-matched — see corrections (2)/(3) in the
    header.  Stated directly on the read's [ts] entry, which IS the write
    index of its source ([gwrite_at_inv]), so no source event is named. *)
Definition gfr (G : gexec) (r w' : geid) : Prop :=
  r ≠ w' ∧ ∃ a t v v', greads_byte G r a t v ∧ gwrites_byte G w' a v' ∧
                       (t < gwix G w')%nat.

(** [gpow]: po INTO a write, from a MEMORY event — rule 14's own edges. *)
Definition gpow (G : gexec) (e w : geid) : Prop :=
  gpo G e w ∧ gmem G e ∧ gis_w G w = true.

(** THE OBLIGATION RELATION. *)
Definition Racy (G : gexec) (x y : geid) : Prop :=
  gpow G x y ∨ grf G x y ∨ gco G x y ∨ gfr G x y ∨ gppo G x y.

(** … and its [gdexec] form, with the store-dep fragment. *)
Definition RacyD (GD : gdexec) (x y : geid) : Prop :=
  Racy (gd_g GD) x y ∨ (x, y) ∈ gd_deps GD.

(** THE TRANSPORTING FRAGMENT (§5): the arms that survive [rows_rel]/[wperm]. *)
Definition Rt (G : gexec) (x y : geid) : Prop :=
  gpow G x y ∨ grf G x y ∨ gppo G x y.

Lemma Rt_Racy G x y : Rt G x y → Racy G x y.
Proof. intros [H|[H|H]]; [by left|by right;left|by right;right;right;right]. Qed.

(* ====================================================================== *)
(** * 3. EVERY ARM IS GMO-FORWARD *)

(** rf ⊆ gmo.  The [gvisible] disjunction's FORWARDING half is not a hole:
    a same-hart same-byte source po-before the read is [gpoloc]-ordered
    (ppo⁻ rules 1–3), hence gmo-ordered.  (Same move as
    [WeakRvwmoLock.acq_ts_lt].) *)
Lemma grf_gmo G w r : rvwmo_minus_consistent G → grf G w r → gmo_lt G w r.
Proof.
  intros (Hwf & Hppo & Hlv & _) (a & t & v & Hrd & Hat).
  destruct t as [|i]; [done|].
  destruct (Hlv r a (S i) v Hrd) as [(w0 & Hat0 & Hwb & Hvis) _].
  assert (w0 = w) as -> by congruence.
  destruct Hvis as [Hmo|Hpo]; [exact Hmo|].
  apply Hppo. left. split; [exact Hpo|].
  exists a. split; [left; by exists v|right; by exists (S i), v].
Qed.

Lemma grf_gis_w G w r : grf G w r → gis_w G w = true.
Proof.
  intros (a & t & v & _ & Hat).
  by pose proof (gwrite_at_gwrites G t w Hat) as [_ ?]%gwrites_elem_of.
Qed.

Lemma grf_gmem_r G w r : grf G w r → gmem G r.
Proof.
  intros (a & t & v & Hrd & _). eapply gaccesses_gmem. right. by exists t, v.
Qed.

(** co ⊆ gmo: [gwrites] is a FILTER of [gx_gmo], so write indices and gmo
    positions order the writes the same way ([gwix_gpos_lt]). *)
Lemma gco_gmo G w w' : gwf G → gco G w w' → gmo_lt G w w'.
Proof.
  intros Hwf (a & v & v' & H1 & H2 & Hlt). pose proof Hwf as (Hnd & _ & _).
  pose proof (gwrites_byte_in_gwrites G w a v Hwf H1) as Hw.
  pose proof (gwrites_byte_in_gwrites G w' a v' Hwf H2) as Hw'.
  split_and!.
  - by eapply gwrites_byte_gmo.
  - by eapply gwrites_byte_gmo.
  - by apply (gwix_gpos_lt G w w' Hnd Hw Hw').
Qed.

(** fr ⊆ gmo: load-value's CO-MAXIMALITY half.  A same-byte write with a
    write index ABOVE the read's [ts] entry cannot be [gvisible] to the
    read, so by gmo-totality (and [r ≠ w']) it is gmo-AFTER it. *)
Lemma gfr_gmo G r w' : rvwmo_minus_consistent G → gfr G r w' → gmo_lt G r w'.
Proof.
  intros Hcons (Hne & a & t & v & v' & Hrd & Hwb & Hlt).
  pose proof Hcons as (Hwf & _ & Hlv & _). pose proof Hwf as (Hnd & _ & _).
  pose proof (greads_byte_gmo G r a t v Hwf Hrd) as Hr.
  pose proof (gwrites_byte_gmo G w' a v' Hwf Hwb) as Hgw'.
  destruct (Hlv r a t v Hrd) as [_ Hmax].
  assert (Hnv : ¬ gvisible G w' r).
  { intros Hvis. specialize (Hmax w' v' Hwb Hvis). lia. }
  destruct (gmo_lt_total G r w' Hnd Hr Hgw' Hne) as [?|Hbad]; [done|].
  destruct Hnv. by left.
Qed.

(** po-into-a-write ⊆ gmo: this IS [grule14]. *)
Lemma rule14_po_write G e w : grule14 G → gpow G e w → gmo_lt G e w.
Proof.
  intros H14 (Hpo & Hm & Hw). apply H14; [done|done|by apply gis_w_glbl_is].
Qed.

(** THE UNION. *)
Lemma R_gmo G x y :
  rvwmo_minus_consistent G → grule14 G → Racy G x y → gmo_lt G x y.
Proof.
  intros Hcons H14 [H|[H|[H|[H|H]]]].
  - by eapply rule14_po_write.
  - by eapply grf_gmo.
  - by eapply gco_gmo; [apply Hcons|].
  - by eapply gfr_gmo.
  - by apply Hcons.
Qed.

Lemma RD_gmo GD x y :
  rvwmo_minus_deps_consistent GD → grule14 (gd_g GD) →
  RacyD GD x y → gmo_lt (gd_g GD) x y.
Proof.
  intros (Hcons & _ & Hdg) H14 [HR|Hd]; [by eapply R_gmo|].
  by apply (Hdg (x, y)).
Qed.

(* ====================================================================== *)
(** * 4. THE THEOREM: R IS ACYCLIC

    [gmo_lt] is transitive and irreflexive, so a sub-relation's transitive
    closure stays inside it and cannot close a cycle. *)

Lemma tc_R_gmo G x y :
  rvwmo_minus_consistent G → grule14 G → tc (Racy G) x y → gmo_lt G x y.
Proof.
  intros Hcons H14. induction 1 as [x y HR|x u y HR Htc IH].
  - by eapply R_gmo.
  - eapply gmo_lt_trans; [by eapply R_gmo|exact IH].
Qed.

Theorem R_acyclic G x :
  rvwmo_minus_consistent G → grule14 G → tc (Racy G) x x → False.
Proof. intros Hcons H14 Htc. by eapply gmo_lt_irrefl, tc_R_gmo. Qed.

Lemma tc_RD_gmo GD x y :
  rvwmo_minus_deps_consistent GD → grule14 (gd_g GD) →
  tc (RacyD GD) x y → gmo_lt (gd_g GD) x y.
Proof.
  intros Hcons H14. induction 1 as [x y HR|x u y HR Htc IH].
  - by eapply RD_gmo.
  - eapply gmo_lt_trans; [by eapply RD_gmo|exact IH].
Qed.

Theorem RD_acyclic GD x :
  rvwmo_minus_deps_consistent GD → grule14 (gd_g GD) →
  tc (RacyD GD) x x → False.
Proof. intros Hcons H14 Htc. by eapply gmo_lt_irrefl, tc_RD_gmo. Qed.

(** The transporting fragment inherits acyclicity. *)
Theorem Rt_acyclic G x :
  rvwmo_minus_consistent G → grule14 G → tc (Rt G) x x → False.
Proof.
  intros Hcons H14 Htc. eapply (R_acyclic G x Hcons H14).
  eapply tc_mono; [|exact Htc]. intros a b. apply Rt_Racy.
Qed.

(* ====================================================================== *)
(** * 4b. `po ∪ rf` IS ACYCLIC — route B's F2 sentence

    [gcaus] is NOT a sub-relation of [Racy]: a po edge into a READ (or out of
    a FENCE) is in neither, so §4's one-liner does not cover it and it gets
    its own induction.

    THE INVARIANT.  A causality path [y →⁺ z] that ENDS AT A WRITE is
    gmo-forward from any REFLEXIVE-PO PREFIX [x] of [y] that is itself a
    memory event.  Carrying the prefix reflexively is what absorbs the po
    runs: a maximal po run in front of an rf edge collapses (po is
    transitive) onto a single po edge into the rf edge's SOURCE, which is a
    write, where rule 14 applies. *)

Lemma caus_write_gmo G :
  rvwmo_minus_consistent G → grule14 G →
  ∀ y z, tc (gcaus G) y z →
  ∀ x, (x = y ∨ gpo G x y) → gmem G x → gis_w G z = true → gmo_lt G x z.
Proof.
  intros Hcons H14 y z Htc.
  induction Htc as [y z Hc|y u z Hc Htc IH]; intros x Hx Hmx Hwz.
  - destruct Hc as [Hpo|Hrf].
    + assert (gpo G x z) as Hxz
        by (destruct Hx as [->|Hxy]; [done|by eapply gpo_trans]).
      by eapply rule14_po_write.
    + pose proof (grf_gmo G y z Hcons Hrf) as Hyz.
      destruct Hx as [->|Hxy]; [done|].
      eapply gmo_lt_trans; [|exact Hyz].
      eapply rule14_po_write; [done|split_and!]; [done|done|].
      by eapply grf_gis_w.
  - destruct Hc as [Hpo|Hrf].
    + apply (IH x); [|done|done].
      right. destruct Hx as [->|Hxy]; [done|by eapply gpo_trans].
    + pose proof (grf_gmo G y u Hcons Hrf) as Hyu.
      assert (gmo_lt G u z) as Huz
        by (apply (IH u); [by left|by eapply grf_gmem_r|done]).
      assert (gmo_lt G y z) as Hyz by (by eapply gmo_lt_trans).
      destruct Hx as [->|Hxy]; [done|].
      eapply gmo_lt_trans; [|exact Hyz].
      eapply rule14_po_write; [done|split_and!]; [done|done|].
      by eapply grf_gis_w.
Qed.

(** A causality path is either a single po edge or passes through a WRITE
    (the source of its first rf edge). *)
Lemma caus_write_on_path G x y :
  tc (gcaus G) x y →
  gpo G x y ∨ ∃ w, gis_w G w = true ∧ rtc (gcaus G) x w ∧ tc (gcaus G) w y.
Proof.
  induction 1 as [x y Hc|x u y Hc Htc IH].
  - destruct Hc as [Hpo|Hrf]; [by left|].
    right. exists x. split_and!.
    + by eapply grf_gis_w.
    + apply rtc_refl.
    + by apply tc_once; right.
  - destruct IH as [Hpo|(w & Hw & Hrw & Htw)].
    + destruct Hc as [Hpo'|Hrf].
      * left. by eapply gpo_trans.
      * right. exists x. split_and!.
        { by eapply grf_gis_w. }
        { apply rtc_refl. }
        { eapply tc_l; [by right|exact Htc]. }
    + right. exists w. split_and!; [done| |done].
      eapply rtc_l; [exact Hc|exact Hrw].
Qed.

Theorem gcaus_acyclic G x :
  rvwmo_minus_consistent G → grule14 G → tc (gcaus G) x x → False.
Proof.
  intros Hcons H14 Htc.
  destruct (caus_write_on_path G x x Htc) as [Hpo|(w & Hw & Hrw & Htw)].
  - by eapply gpo_irrefl.
  - assert (tc (gcaus G) w w) as Hww by (eapply tc_rtc_r; [exact Htw|exact Hrw]).
    apply (gmo_lt_irrefl G w).
    apply (caus_write_gmo G Hcons H14 w w Hww w); [by left| |done].
    by apply gis_w_gmem.
Qed.

(** THE HEIGHT COROLLARY (design §4d.1 F2's parenthetical: "every causal
    cycle passes through a VIOLATING WRITE").  Stated CONSTRUCTIVELY — the
    positive `∃ e w, gviol G e w` needs excluded middle, this contrapositive
    does not — via [WeakRvwmoXchg.gviol_grule14]. *)
Corollary caus_cycle_gviol G x :
  rvwmo_minus_consistent G → tc (gcaus G) x x → ¬ (∀ e w, ¬ gviol G e w).
Proof.
  intros Hcons Htc Hno.
  eapply (gcaus_acyclic G x Hcons); [|exact Htc].
  by apply gviol_grule14; [apply Hcons|].
Qed.

(* ====================================================================== *)
(** * 5. TRANSPORT along [rows_rel] / [wperm] *)

(** The inverse of [rows_rel_rdb]: every read entry of [G'] comes from one
    of [G], renamed. *)
Lemma lbl_ren_rd_inv π l base ts' vs :
  lb_rd (lbl_ren π l) = Some (base, ts', vs) →
  ∃ ts, lb_rd l = Some (base, ts, vs) ∧ ts' = π <$> ts.
Proof. destruct l; simpl; intros H; simplify_eq; eauto. Qed.

Lemma rows_rel_rdb_inv π G G' e a t' v :
  rows_rel π G G' → greads_byte G' e a t' v →
  ∃ t, t' = π t ∧ greads_byte G e a t v.
Proof.
  intros Hr (l' & base & ts' & vs & j & Hl' & Hrd' & Ht' & Hv & Ha).
  rewrite (rows_rel_lbl π G G' e Hr) in Hl'.
  destruct (gx_lbl G e) as [l|] eqn:Hl; simpl in Hl'; [|done].
  simplify_eq.
  apply lbl_ren_rd_inv in Hrd' as (ts & Hrd & ->).
  rewrite list_lookup_fmap in Ht'.
  destruct (ts !! j) as [t|] eqn:Htj; simpl in Ht'; [|done].
  simplify_eq. exists t. split; [done|]. by exists l, base, ts, vs, j.
Qed.

(** ** 5.1 [grf], [gpow], [gcaus] *)

Lemma grf_rows_rel π G G' w r :
  rows_rel π G G' → wperm π G G' → (grf G w r ↔ grf G' w r).
Proof.
  intros Hr Hw. pose proof Hw as (_ & Hwat & _). split.
  - intros (a & t & v & Hrd & Hat). exists a, (π t), v. split.
    + by eapply rows_rel_rdb.
    + by rewrite Hwat.
  - intros (a & t' & v & Hrd' & Hat').
    destruct (rows_rel_rdb_inv π G G' r a t' v Hr Hrd') as (t & -> & Hrd).
    exists a, t, v. split; [done|]. by rewrite -Hwat.
Qed.

Lemma gpow_rows_rel π G G' e w :
  rows_rel π G G' → (gpow G e w ↔ gpow G' e w).
Proof.
  intros Hr. rewrite /gpow (rows_rel_gis_w π G G' w Hr).
  pose proof (rows_rel_gpo π G G' e w Hr) as Hpo.
  pose proof (rows_rel_gmem π G G' e Hr) as Hm.
  naive_solver.
Qed.

Lemma gcaus_rows_rel π G G' :
  rows_rel π G G' → wperm π G G' → ∀ x y, gcaus G x y ↔ gcaus G' x y.
Proof.
  intros Hr Hw x y.
  pose proof (rows_rel_gpo π G G' x y Hr) as Hpo.
  pose proof (grf_rows_rel π G G' x y Hr Hw) as Hrf.
  split; intros [H|H].
  - left. by apply (proj2 Hpo).
  - right. by apply (proj1 Hrf).
  - left. by apply (proj1 Hpo).
  - right. by apply (proj2 Hrf).
Qed.

(** ** 5.2 [gppo] — every arm, by the label lemmas *)

Lemma rows_rel_gaccesses π G G' e a :
  rows_rel π G G' → (gaccesses G' e a ↔ gaccesses G e a).
Proof.
  intros Hr. split.
  - intros [(v & Hwb)|(t & v & Hrd)].
    + left. exists v. by apply (proj1 (rows_rel_wrb π G G' e a v Hr)).
    + destruct (rows_rel_rdb_inv π G G' e a t v Hr Hrd) as (t0 & _ & Hrd0).
      right. by exists t0, v.
  - intros [(v & Hwb)|(t & v & Hrd)].
    + left. exists v. by apply (proj2 (rows_rel_wrb π G G' e a v Hr)).
    + right. exists (π t), v. by eapply rows_rel_rdb.
Qed.

Lemma rows_rel_fence π G G' e pr pw sr sw :
  rows_rel π G G' →
  (gx_lbl G' e = Some (LFence pr pw sr sw) ↔
   gx_lbl G e = Some (LFence pr pw sr sw)).
Proof.
  intros Hr. rewrite (rows_rel_lbl π G G' e Hr).
  destruct (gx_lbl G e) as [l|] eqn:Hl; simpl; [|naive_solver].
  split.
  - intros Heq. destruct l; simplify_eq/=; done.
  - intros Heq. by simplify_eq/=.
Qed.

Lemma rows_rel_gfb π G G' e1 e2 pr pw sr sw :
  rows_rel π G G' →
  (gfence_between G' e1 e2 pr pw sr sw ↔ gfence_between G e1 e2 pr pw sr sw).
Proof.
  intros Hr. rewrite /gfence_between.
  pose proof (λ kf, rows_rel_fence π G G' (e1.1, kf) pr pw sr sw Hr) as Hf.
  split; intros (Hag & Hlt & kf & H1 & H2 & Hl); split_and!;
    [done|done|exists kf|done|done|exists kf]; split_and!; try done.
  - by apply (proj1 (Hf kf)).
  - by apply (proj2 (Hf kf)).
Qed.

Lemma rows_rel_gppo π G G' e1 e2 :
  rows_rel π G G' → (gppo G' e1 e2 ↔ gppo G e1 e2).
Proof.
  intros Hr.
  pose proof (rows_rel_gpo π G G' e1 e2 Hr) as Hpo.
  pose proof (λ e, rows_rel_gaccesses π G G' e) as Hacc.
  pose proof (λ e, rows_rel_glbl_is π G G' e lb_is_r Hr (lbl_ren_is_r π)) as Hisr.
  pose proof (λ e, rows_rel_glbl_is π G G' e lb_is_w Hr (lbl_ren_is_w π)) as Hisw.
  pose proof (λ e, rows_rel_glbl_is π G G' e lb_aq Hr (lbl_ren_aq π)) as Haq.
  pose proof (λ e, rows_rel_glbl_is π G G' e lb_rl Hr (lbl_ren_rl π)) as Hrl.
  pose proof (λ e, rows_rel_gmem π G G' e Hr) as Hmem.
  pose proof (λ e1' e2' pr pw sr sw,
                rows_rel_gfb π G G' e1' e2' pr pw sr sw Hr) as Hfb.
  rewrite /gppo /gpoloc /gfence_covers /gacq_po /grel_acq.
  split.
  - intros [(H & a & A1 & A2)
           |[(pr & pw & sr & sw & Hb & C1 & C2)
            |[(H & B1 & B2 & B3)|(H & D1 & D2 & D3 & D4)]]].
    + left. split; [by apply (proj1 Hpo)|].
      exists a. split; [by apply (proj1 (Hacc e1 a Hr))
                       |by apply (proj1 (Hacc e2 a Hr))].
    + right; left. exists pr, pw, sr, sw. split_and!.
      * by apply (proj1 (Hfb e1 e2 pr pw sr sw)).
      * destruct C1 as [[H1 ->]|[H1 ->]];
          [left; split; [by apply (proj1 (Hisr e1))|done]
          |right; split; [by apply (proj1 (Hisw e1))|done]].
      * destruct C2 as [[H2 ->]|[H2 ->]];
          [left; split; [by apply (proj1 (Hisr e2))|done]
          |right; split; [by apply (proj1 (Hisw e2))|done]].
    + right; right; left. split_and!.
      * by apply (proj1 Hpo).
      * by apply (proj1 (Hisr e1)).
      * by apply (proj1 (Haq e1)).
      * by apply (proj1 (Hmem e2)).
    + right; right; right. split_and!.
      * by apply (proj1 Hpo).
      * by apply (proj1 (Hisw e1)).
      * by apply (proj1 (Hrl e1)).
      * by apply (proj1 (Hisr e2)).
      * by apply (proj1 (Haq e2)).
  - intros [(H & a & A1 & A2)
           |[(pr & pw & sr & sw & Hb & C1 & C2)
            |[(H & B1 & B2 & B3)|(H & D1 & D2 & D3 & D4)]]].
    + left. split; [by apply (proj2 Hpo)|].
      exists a. split; [by apply (proj2 (Hacc e1 a Hr))
                       |by apply (proj2 (Hacc e2 a Hr))].
    + right; left. exists pr, pw, sr, sw. split_and!.
      * by apply (proj2 (Hfb e1 e2 pr pw sr sw)).
      * destruct C1 as [[H1 ->]|[H1 ->]];
          [left; split; [by apply (proj2 (Hisr e1))|done]
          |right; split; [by apply (proj2 (Hisw e1))|done]].
      * destruct C2 as [[H2 ->]|[H2 ->]];
          [left; split; [by apply (proj2 (Hisr e2))|done]
          |right; split; [by apply (proj2 (Hisw e2))|done]].
    + right; right; left. split_and!.
      * by apply (proj2 Hpo).
      * by apply (proj2 (Hisr e1)).
      * by apply (proj2 (Haq e1)).
      * by apply (proj2 (Hmem e2)).
    + right; right; right. split_and!.
      * by apply (proj2 Hpo).
      * by apply (proj2 (Hisw e1)).
      * by apply (proj2 (Hrl e1)).
      * by apply (proj2 (Hisr e2)).
      * by apply (proj2 (Haq e2)).
Qed.

(** ** 5.3 [gco] / [gfr] — ONLY under a MONOTONE renaming

    See the header's negative result: [wperm]'s π is merely injective (B2d's
    (W,W) exchange renames by a transposition), and the co-order of two
    same-byte writes that nothing reads is not pinned by consistency, so
    these two arms do NOT transport unconditionally. *)

Lemma gco_rows_rel_mono π G G' w w' :
  gwf G → NoDup (gx_gmo G') → rows_rel π G G' → wperm π G G' →
  (∀ t1 t2, (t1 < t2)%nat → (π t1 < π t2)%nat) →
  gco G w w' → gco G' w w'.
Proof.
  intros Hwf Hnd' Hr Hw Hmono (a & v & v' & H1 & H2 & Hlt).
  exists a, v, v'. split_and!.
  - by apply (proj2 (rows_rel_wrb π G G' w a v Hr)).
  - by apply (proj2 (rows_rel_wrb π G G' w' a v' Hr)).
  - rewrite (wperm_gwix π G G' w Hnd' Hw (gwrites_byte_in_gwrites G w a v Hwf H1))
            (wperm_gwix π G G' w' Hnd' Hw
               (gwrites_byte_in_gwrites G w' a v' Hwf H2)).
    by apply Hmono.
Qed.

Lemma gfr_rows_rel_mono π G G' r w' :
  gwf G → NoDup (gx_gmo G') → rows_rel π G G' → wperm π G G' →
  (∀ t1 t2, (t1 < t2)%nat → (π t1 < π t2)%nat) →
  gfr G r w' → gfr G' r w'.
Proof.
  intros Hwf Hnd' Hr Hw Hmono (Hne & a & t & v & v' & Hrd & Hwb & Hlt).
  split; [done|]. exists a, (π t), v, v'. split_and!.
  - by eapply rows_rel_rdb.
  - by apply (proj2 (rows_rel_wrb π G G' w' a v' Hr)).
  - rewrite (wperm_gwix π G G' w' Hnd' Hw
               (gwrites_byte_in_gwrites G w' a v' Hwf Hwb)).
    by apply Hmono.
Qed.

(** ** 5.4 The orbit corollaries

    "A rows-equivalent rule-14 graph exists ONLY IF [G]'s relation is
    acyclic" — the direction route B's F2 consumes. *)

Lemma tc_gcaus_rows_rel π G G' x y :
  rows_rel π G G' → wperm π G G' → tc (gcaus G) x y → tc (gcaus G') x y.
Proof.
  intros Hr Hw. apply tc_mono. intros a b.
  apply (proj1 (gcaus_rows_rel π G G' Hr Hw a b)).
Qed.

Corollary gcaus_acyclic_orbit π G G' x :
  rvwmo_minus_consistent G' → grule14 G' → rows_rel π G G' → wperm π G G' →
  tc (gcaus G) x x → False.
Proof.
  intros Hcons H14 Hr Hw Htc.
  by eapply (gcaus_acyclic G' x Hcons H14), tc_gcaus_rows_rel.
Qed.

Lemma Rt_rows_rel π G G' x y :
  rows_rel π G G' → wperm π G G' → Rt G x y → Rt G' x y.
Proof.
  intros Hr Hw [H|[H|H]].
  - left. by apply (proj1 (gpow_rows_rel π G G' x y Hr)).
  - right; left. by apply (proj1 (grf_rows_rel π G G' x y Hr Hw)).
  - right; right. by apply (proj2 (rows_rel_gppo π G G' x y Hr)).
Qed.

Corollary Rt_acyclic_orbit π G G' x :
  rvwmo_minus_consistent G' → grule14 G' → rows_rel π G G' → wperm π G G' →
  tc (Rt G) x x → False.
Proof.
  intros Hcons H14 Hr Hw Htc.
  eapply (Rt_acyclic G' x Hcons H14).
  eapply tc_mono; [|exact Htc]. intros a b. by eapply Rt_rows_rel.
Qed.
