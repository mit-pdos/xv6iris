(** * WeakRvwmoHull.v — THE CAUSAL HULL SLICE (route B, stage B1a')

    Design: [claude-notes/design/weak-memory-route-b.md] §4d.1 F3 and
    §4d.4 ("B1a' — CAUSAL HULLS"); generalizes B1a
    ([WeakRvwmoRestr.v], §4b).

    WHY B1a IS NOT ENOUGH.  [restr_ok] ties the per-hart cut to a gmo
    PREFIX, and [WeakRvwmoProbeRestr.erg] shows no cut vector can satisfy
    that at the frontier: another hart's EARLY READ (a load gmo-below the
    violating write whose own po-predecessor is gmo-above it) is
    consistent, is not a violation, and breaks the tie.  The realizable
    region is not the prefix — it is the CAUSAL HULL.

    THE OBJECT.  A hull is a per-hart cut vector [cs] (hart [i] keeps its
    first [cs !! i] row events, so po-closure is BY CONSTRUCTION — B1a's
    [gcut]) that is RF-CLOSED: every kept read's named source is kept
    ([hull_ok]).  There is NO gmo cut: the hull's gmo is
    [filter (gcut cs) (gx_gmo G)], a SUBSEQUENCE.  Hence the hull's writes
    are a subsequence of [gwrites G] and write indices RENUMBER — which is
    the one thing B1a did not have to do, and the reason this file factors
    as

        G  ---- gx_cut ---->  gx_cut G cs  ---- lbl_ren ---->  gx_hull G cs

    the CUT (B1a's row-cutting shape, with the filtered gmo) followed by
    the RENAMING [hren G cs] of every read's [ts] entries.  Both halves are
    already mechanized elsewhere and are REUSED rather than re-proved: the
    cut's label layer is B1a's [gxr_*] family (every one of those lemmas
    depends on [gx_prog] alone, so it applies to [gx_cut] verbatim, at
    [n := 0]), and the renaming layer is [WeakRvwmoNorm]'s [rows_rel] with
    [WeakRvwmoAcyc]'s transport lemmas ([rows_rel_gppo],
    [rows_rel_rdb_inv], …).  What is genuinely new here is the RENUMBERING
    ARITHMETIC: [filter] preserves relative order ([sorted_pos_iff]), so
    both [gmo] positions and write indices restrict order-isomorphically,
    and [hren] is exactly "the index of [gwrite_at G t] among the hull's
    writes".

    WHAT IS PROVED: the [gxc_*]/[gxh_*] bookkeeping, [hull_consistent],
    [hull_rule14], [hull_deps_consistent], the composition
    [hull_linearizes], the [rows_rel] correspondence B1b consumes
    ([hull_rows_rel] — stated PURELY, so this file need not import the
    heavy [WeakRvwmoConf]), the full-cut identity ([hull_ok_full],
    [gx_hull_full]), and NON-VACUITY at [erg]: the hull [ [1;0] ] IS
    rf-closed and violation-free, so [hull_linearizes] applies exactly
    where [restrict_linearizes] provably could not
    ([erg_hull_beats_restr]).

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations sorting.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakLitmus WeakAxiomatic WeakAxiomatic2
                            WeakAxiomatic3 WeakRvwmoGraph WeakRvwmoLin
                            WeakRvwmoXchg WeakRvwmoNorm WeakRvwmoAcyc
                            WeakRvwmoRestr WeakRvwmoProbeRestr.

(* ====================================================================== *)
(** * 1. THE GENERIC KIT *)

(** Filters commute. *)
Lemma filter_comm {A} (P Q : A → Prop)
    `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)} (l : list A) :
  filter P (filter Q l) = filter Q (filter P l).
Proof.
  rewrite !list_filter_filter. apply list_filter_iff. intros x. tauto.
Qed.

(** A filter that drops nothing is the identity. *)
Lemma filter_all {A} (P : A → Prop) `{∀ x, Decision (P x)} (l : list A) :
  (∀ x, x ∈ l → P x) → filter P l = l.
Proof.
  induction l as [|x l IH]; intros Hall; [by rewrite filter_nil|].
  assert (Hx : P x) by (apply Hall, elem_of_list_here).
  rewrite filter_cons decide_True //. f_equal.
  apply IH. intros y Hy. by apply Hall, elem_of_list_further.
Qed.

(** THE ORDER-PRESERVATION ENGINE.  In a list sorted strictly by a
    numeric key, LIST POSITION and KEY order agree — so applying it to
    [filter P l] (sorted by inheritance, [StronglySorted_filter]) says a
    subsequence renumbers ORDER-ISOMORPHICALLY.  This is the one fact the
    whole renumbering rests on, used twice: for gmo positions and for
    write indices. *)
Lemma sorted_pos_iff {A} (f : A → nat) (l : list A) i1 i2 x1 x2 :
  StronglySorted (λ x y, (f x < f y)%nat) l →
  l !! i1 = Some x1 → l !! i2 = Some x2 →
  ((i1 < i2)%nat ↔ (f x1 < f x2)%nat).
Proof.
  intros Hss H1 H2. split.
  - intros Hlt.
    pose proof (StronglySorted_lookup_elim _ _ i1 i2 x1 x2 Hss H1 H2 Hlt) as Hr.
    cbn in Hr. lia.
  - intros Hlt. destruct (decide (i1 < i2)%nat) as [?|Hge]; [done|].
    destruct (decide (i1 = i2)) as [->|Hne].
    { rewrite H1 in H2. simplify_eq. lia. }
    pose proof (StronglySorted_lookup_elim _ _ i2 i1 x2 x1 Hss H2 H1
                  ltac:(lia)) as Hr. cbn in Hr. lia.
Qed.

(** [gx_gmo] is sorted by [gpos]; [gwrites] is sorted by [gwix]. *)
Lemma gmo_gpos_sorted G :
  NoDup (gx_gmo G) →
  StronglySorted (λ x y, (gpos G x < gpos G y)%nat) (gx_gmo G).
Proof.
  intros Hnd. apply StronglySorted_lookup_intro. intros i j x y Hi Hj Hlt.
  rewrite (gpos_of_lookup G i x Hnd Hi) (gpos_of_lookup G j y Hnd Hj). lia.
Qed.

Lemma gwrites_gwix_sorted G :
  NoDup (gx_gmo G) →
  StronglySorted (λ x y, (gwix G x < gwix G y)%nat) (gwrites G).
Proof.
  intros Hnd. apply StronglySorted_lookup_intro. intros i j x y Hi Hj Hlt.
  rewrite (gwix_of_lookup G i x Hnd Hi) (gwix_of_lookup G j y Hnd Hj). lia.
Qed.

(** [lbl_ren] preserves [gwf]'s shape clause (it only [fmap]s the [ts]
    list, whose LENGTH is what the clause constrains). *)
Lemma lbl_ren_shape π l :
  match l with
  | LLoad _ _ ts vs => length vs = length ts
  | LStore _ _ vs _ => vs ≠ []
  | LFence _ _ _ _ => True
  | LRmw _ _ _ ts rvs wvs _ =>
      wvs ≠ [] ∧ length wvs = length ts ∧ length rvs = length ts
  end →
  match lbl_ren π l with
  | LLoad _ _ ts vs => length vs = length ts
  | LStore _ _ vs _ => vs ≠ []
  | LFence _ _ _ _ => True
  | LRmw _ _ _ ts rvs wvs _ =>
      wvs ≠ [] ∧ length wvs = length ts ∧ length rvs = length ts
  end.
Proof. destruct l; simpl; by rewrite ?length_fmap. Qed.

(** The two shapes of [gload_value]'s ∃-half, so no consumer has to
    destruct the index-0 match by hand. *)
Lemma gload_src_elim G t a v e :
  (0 < t)%nat →
  match t with
  | 0%nat => gx_img G a = Some v
  | S _ => ∃ w, gwrite_at G t = Some w ∧ gwrites_byte G w a v ∧ gvisible G w e
  end →
  ∃ w, gwrite_at G t = Some w ∧ gwrites_byte G w a v ∧ gvisible G w e.
Proof. intros Ht H. by destruct t; [lia|]. Qed.

Lemma gload_src_intro G t a v e :
  (0 < t)%nat →
  (∃ w, gwrite_at G t = Some w ∧ gwrites_byte G w a v ∧ gvisible G w e) →
  match t with
  | 0%nat => gx_img G a = Some v
  | S _ => ∃ w, gwrite_at G t = Some w ∧ gwrites_byte G w a v ∧ gvisible G w e
  end.
Proof. intros Ht H. by destruct t; [lia|]. Qed.

(* ====================================================================== *)
(** * 2. THE CUT: B1a's rows, a FILTERED gmo

    [gx_cut] is [gx_restrict] with the gmo prefix replaced by the gmo
    SUBSEQUENCE the cut selects.  Its label layer is literally B1a's:
    [gx_lbl] reads [gx_prog] only, and [gx_prog (gx_cut G cs)] is
    convertible with [gx_prog (gx_restrict G cs 0)] — so every [gxr_*]
    lemma applies by conversion.  (NOT consistent on its own: the reads
    still name [G]'s write indices, which is what §3's renaming fixes.) *)

Definition gx_cut (G : gexec) (cs : list nat) : gexec :=
  GExec (gx_img G)
        (zip_with take cs (gx_prog G))
        (filter (gcut cs) (gx_gmo G)).

Lemma gxc_gmo G cs : gx_gmo (gx_cut G cs) = filter (gcut cs) (gx_gmo G).
Proof. reflexivity. Qed.

Lemma gxc_img G cs : gx_img (gx_cut G cs) = gx_img G.
Proof. reflexivity. Qed.

(** ** 2.1 The label layer, BY CONVERSION from B1a *)

Lemma gxc_prog_lookup G cs i :
  gx_prog (gx_cut G cs) !! i = (c ← cs !! i; p ← gx_prog G !! i; Some (take c p)).
Proof. exact (gxr_prog_lookup G cs 0%nat i). Qed.

Lemma gxc_row G cs i :
  default [] (gx_prog (gx_cut G cs) !! i)
  = take (default 0%nat (cs !! i)) (default [] (gx_prog G !! i)).
Proof. exact (gxr_row G cs 0%nat i). Qed.

Lemma gxc_lbl G cs e :
  gx_lbl (gx_cut G cs) e = if gcut cs e then gx_lbl G e else None.
Proof. exact (gxr_lbl G cs 0%nat e). Qed.

Lemma gxc_lbl_in G cs e :
  gcut cs e = true → gx_lbl (gx_cut G cs) e = gx_lbl G e.
Proof. exact (gxr_lbl_in G cs 0%nat e). Qed.

Lemma gxc_glbl_is G cs e P :
  glbl_is (gx_cut G cs) e P ↔ gcut cs e = true ∧ glbl_is G e P.
Proof. exact (gxr_glbl_is G cs 0%nat e P). Qed.

Lemma gxc_gmem G cs e : gmem (gx_cut G cs) e ↔ gcut cs e = true ∧ gmem G e.
Proof. exact (gxr_gmem G cs 0%nat e). Qed.

Lemma gxc_gis_w G cs e :
  gis_w (gx_cut G cs) e = if gcut cs e then gis_w G e else false.
Proof. exact (gxr_gis_w G cs 0%nat e). Qed.

Lemma gxc_gpo G cs e1 e2 :
  gpo (gx_cut G cs) e1 e2 ↔ gpo G e1 e2 ∧ gcut cs e2 = true.
Proof. exact (gxr_gpo G cs 0%nat e1 e2). Qed.

Lemma gxc_wrb G cs e a v :
  gwrites_byte (gx_cut G cs) e a v ↔ gcut cs e = true ∧ gwrites_byte G e a v.
Proof. exact (gxr_wrb G cs 0%nat e a v). Qed.

Lemma gxc_rdb G cs e a t v :
  greads_byte (gx_cut G cs) e a t v ↔ gcut cs e = true ∧ greads_byte G e a t v.
Proof. exact (gxr_rdb G cs 0%nat e a t v). Qed.

Lemma gxc_gmsg G cs e : gcut cs e = true → gmsg (gx_cut G cs) e = gmsg G e.
Proof. exact (gxr_gmsg G cs 0%nat e). Qed.

Lemma gxc_gppo G cs e1 e2 : gppo (gx_cut G cs) e1 e2 → gppo G e1 e2.
Proof. exact (gxr_gppo G cs 0%nat e1 e2). Qed.

Lemma gxc_gppo_cut G cs e1 e2 :
  gppo (gx_cut G cs) e1 e2 → gcut cs e1 = true ∧ gcut cs e2 = true.
Proof. exact (gxr_gppo_cut G cs 0%nat e1 e2). Qed.

(** ** 2.2 The gmo layer: a SUBSEQUENCE, order-isomorphically *)

Lemma gxc_gmo_elem G cs e :
  e ∈ gx_gmo (gx_cut G cs) ↔ gcut cs e = true ∧ e ∈ gx_gmo G.
Proof. rewrite gxc_gmo elem_of_list_filter Is_true_true. done. Qed.

Lemma gxc_nodup G cs : NoDup (gx_gmo G) → NoDup (gx_gmo (gx_cut G cs)).
Proof. intros Hnd. rewrite gxc_gmo. by apply list_relations.NoDup_filter. Qed.

Lemma gxc_gmo_sorted G cs :
  NoDup (gx_gmo G) →
  StronglySorted (λ x y, (gpos G x < gpos G y)%nat) (gx_gmo (gx_cut G cs)).
Proof.
  intros Hnd. rewrite gxc_gmo.
  by apply StronglySorted_filter, gmo_gpos_sorted.
Qed.

Lemma gxc_gmo_lt G cs e1 e2 :
  NoDup (gx_gmo G) →
  gmo_lt (gx_cut G cs) e1 e2
  ↔ gcut cs e1 = true ∧ gcut cs e2 = true ∧ gmo_lt G e1 e2.
Proof.
  intros Hnd. split.
  - intros (H1 & H2 & Hlt).
    pose proof (proj1 (gxc_gmo_elem G cs e1) H1) as [Hc1 Hm1].
    pose proof (proj1 (gxc_gmo_elem G cs e2) H2) as [Hc2 Hm2].
    split_and!; [done|done|].
    destruct (gpos_lookup (gx_cut G cs) e1 H1) as (i1 & Hi1 & E1).
    destruct (gpos_lookup (gx_cut G cs) e2 H2) as (i2 & Hi2 & E2).
    rewrite E1 E2 in Hlt.
    split_and!; [done|done|].
    by apply (sorted_pos_iff (gpos G) _ i1 i2 e1 e2
                (gxc_gmo_sorted G cs Hnd) Hi1 Hi2).
  - intros (Hc1 & Hc2 & (Hm1 & Hm2 & Hlt)).
    assert (H1 : e1 ∈ gx_gmo (gx_cut G cs)) by (apply gxc_gmo_elem; done).
    assert (H2 : e2 ∈ gx_gmo (gx_cut G cs)) by (apply gxc_gmo_elem; done).
    destruct (gpos_lookup (gx_cut G cs) e1 H1) as (i1 & Hi1 & E1).
    destruct (gpos_lookup (gx_cut G cs) e2 H2) as (i2 & Hi2 & E2).
    split_and!; [done|done|]. rewrite E1 E2.
    by apply (sorted_pos_iff (gpos G) _ i1 i2 e1 e2
                (gxc_gmo_sorted G cs Hnd) Hi1 Hi2).
Qed.

(** ** 2.3 The write sub-order: [filter (gcut cs)] of [gwrites G] *)

Lemma gxc_gwrites G cs : gwrites (gx_cut G cs) = filter (gcut cs) (gwrites G).
Proof.
  rewrite /gwrites gxc_gmo.
  trans (filter (gis_w G) (filter (gcut cs) (gx_gmo G))).
  - apply filter_iff_elem. intros e He.
    apply elem_of_list_filter in He as [Hc _]. apply Is_true_true in Hc.
    rewrite gxc_gis_w Hc. done.
  - apply filter_comm.
Qed.

Lemma gxc_gwrites_elem G cs w :
  w ∈ gwrites (gx_cut G cs) ↔ gcut cs w = true ∧ w ∈ gwrites G.
Proof. rewrite gxc_gwrites elem_of_list_filter Is_true_true. done. Qed.

Lemma gxc_gwrites_sorted G cs :
  NoDup (gx_gmo G) →
  StronglySorted (λ x y, (gwix G x < gwix G y)%nat) (gwrites (gx_cut G cs)).
Proof.
  intros Hnd. rewrite gxc_gwrites.
  by apply StronglySorted_filter, gwrites_gwix_sorted.
Qed.

(** THE RENUMBERING IS MONOTONE. *)
Lemma gxc_gwix_lt G cs w1 w2 :
  NoDup (gx_gmo G) →
  w1 ∈ gwrites (gx_cut G cs) → w2 ∈ gwrites (gx_cut G cs) →
  ((gwix (gx_cut G cs) w1 < gwix (gx_cut G cs) w2)%nat
   ↔ (gwix G w1 < gwix G w2)%nat).
Proof.
  intros Hnd H1 H2.
  destruct (gwix_lookup (gx_cut G cs) w1 H1) as (i1 & Hi1 & E1).
  destruct (gwix_lookup (gx_cut G cs) w2 H2) as (i2 & Hi2 & E2).
  rewrite E1 E2.
  trans ((i1 < i2)%nat); [lia|].
  by apply (sorted_pos_iff (gwix G) _ i1 i2 w1 w2
              (gxc_gwrites_sorted G cs Hnd) Hi1 Hi2).
Qed.

Lemma gxc_gwix_le G cs w1 w2 :
  NoDup (gx_gmo G) →
  w1 ∈ gwrites (gx_cut G cs) → w2 ∈ gwrites (gx_cut G cs) →
  (gwix G w1 ≤ gwix G w2)%nat →
  (gwix (gx_cut G cs) w1 ≤ gwix (gx_cut G cs) w2)%nat.
Proof.
  intros Hnd H1 H2 Hle.
  destruct (decide (gwix G w1 = gwix G w2)) as [Heq|Hne].
  - assert (w1 = w2) as ->; [|lia].
    apply (gwix_inj G w1 w2 Hnd); [| |done];
      by apply (proj1 (gxc_gwrites_elem G cs _)).
  - assert (Hlt : (gwix G w1 < gwix G w2)%nat) by lia.
    apply (gxc_gwix_lt G cs w1 w2 Hnd H1 H2) in Hlt. lia.
Qed.

(* ====================================================================== *)
(** * 3. THE RENAMING AND THE HULL

    [hren G cs t] is THE INDEX OF [gwrite_at G t] AMONG THE HULL'S WRITES —
    1-based, like [gwix], and [0] at [0] (the era-initial image) because
    [gwrite_at G 0 = None].  Off the hull it is the identity: nothing
    inside the hull names such an index (that is exactly [hull_ok]), so the
    value is junk, and [t] is the choice that makes the full cut the
    identity renaming ([hren_full]). *)

Definition hren (G : gexec) (cs : list nat) (t : nat) : nat :=
  match gwrite_at G t with
  | Some w => if gcut cs w then gwix (gx_cut G cs) w else t
  | None => t
  end.

Lemma hren_zero G cs : hren G cs 0%nat = 0%nat.
Proof. reflexivity. Qed.

(** THE OBJECT: the cut rows, with every kept label's [ts] entries
    renamed. *)
Definition gx_hull (G : gexec) (cs : list nat) : gexec :=
  GExec (gx_img G)
        ((λ row : list lbl, lbl_ren (hren G cs) <$> row)
           <$> zip_with take cs (gx_prog G))
        (filter (gcut cs) (gx_gmo G)).

(** THE FACTORIZATION, and the statement B1b consumes: the hull's rows are
    the CUT rows renamed.  [WeakRvwmoConf.hart_conf_prefix] takes [G]'s
    rows to the cut's, [hart_conf_ren] takes the cut's to the hull's; this
    file states only the pure row correspondence, so that it need not
    import that (heavy) file. *)
Lemma hull_rows_rel G cs : rows_rel (hren G cs) (gx_cut G cs) (gx_hull G cs).
Proof. split_and!; [reflexivity|reflexivity|apply hren_zero]. Qed.

(** The gmo is UNTOUCHED by the renaming — so positions, membership and
    [gmo_lt] are the cut's, definitionally. *)
Lemma gxh_gmo G cs : gx_gmo (gx_hull G cs) = gx_gmo (gx_cut G cs).
Proof. reflexivity. Qed.

Lemma gxh_gpos G cs e : gpos (gx_hull G cs) e = gpos (gx_cut G cs) e.
Proof. reflexivity. Qed.

Lemma gxh_img G cs : gx_img (gx_hull G cs) = gx_img G.
Proof. reflexivity. Qed.

(** ** 3.1 The label layer: the cut's, composed with the renaming *)

Lemma gxh_prog_lookup G cs i :
  gx_prog (gx_hull G cs) !! i
  = (c ← cs !! i; p ← gx_prog G !! i;
     Some (lbl_ren (hren G cs) <$> take c p)).
Proof.
  change (gx_prog (gx_hull G cs))
    with ((λ row : list lbl, lbl_ren (hren G cs) <$> row)
            <$> gx_prog (gx_cut G cs)).
  rewrite list_lookup_fmap gxc_prog_lookup.
  destruct (cs !! i) as [c|]; [|done].
  by destruct (gx_prog G !! i) as [p|].
Qed.

Lemma gxh_row G cs i :
  default [] (gx_prog (gx_hull G cs) !! i)
  = lbl_ren (hren G cs)
      <$> take (default 0%nat (cs !! i)) (default [] (gx_prog G !! i)).
Proof.
  rewrite gxh_prog_lookup -gxc_row gxc_prog_lookup.
  destruct (cs !! i) as [c|]; [|done].
  by destruct (gx_prog G !! i) as [p|].
Qed.

Lemma gxh_lbl G cs e :
  gx_lbl (gx_hull G cs) e
  = if gcut cs e then lbl_ren (hren G cs) <$> gx_lbl G e else None.
Proof.
  rewrite (rows_rel_lbl _ _ _ e (hull_rows_rel G cs)) gxc_lbl.
  by destruct (gcut cs e).
Qed.

Lemma gxh_glbl_is G cs e (P : lbl → bool) :
  (∀ π l, P (lbl_ren π l) = P l) →
  (glbl_is (gx_hull G cs) e P ↔ gcut cs e = true ∧ glbl_is G e P).
Proof.
  intros HP. etrans;
    [apply (rows_rel_glbl_is _ _ _ e P (hull_rows_rel G cs) (HP _))|].
  apply gxc_glbl_is.
Qed.

Lemma gxh_gmem G cs e : gmem (gx_hull G cs) e ↔ gcut cs e = true ∧ gmem G e.
Proof.
  etrans; [apply (rows_rel_gmem _ _ _ e (hull_rows_rel G cs))|].
  apply gxc_gmem.
Qed.

Lemma gxh_gis_w G cs e :
  gis_w (gx_hull G cs) e = if gcut cs e then gis_w G e else false.
Proof.
  rewrite (rows_rel_gis_w _ _ _ e (hull_rows_rel G cs)). apply gxc_gis_w.
Qed.

Lemma gxh_gpo G cs e1 e2 :
  gpo (gx_hull G cs) e1 e2 ↔ gpo G e1 e2 ∧ gcut cs e2 = true.
Proof.
  etrans; [apply (rows_rel_gpo _ _ _ e1 e2 (hull_rows_rel G cs))|].
  apply gxc_gpo.
Qed.

Lemma gxh_wrb G cs e a v :
  gwrites_byte (gx_hull G cs) e a v ↔ gcut cs e = true ∧ gwrites_byte G e a v.
Proof.
  etrans; [apply (rows_rel_wrb _ _ _ e a v (hull_rows_rel G cs))|].
  apply gxc_wrb.
Qed.

(** THE RENAMING'S PAYLOAD: a kept read reads the SAME byte and value at
    the RENAMED index. *)
Lemma gxh_rdb_in G cs r a t v :
  gcut cs r = true → greads_byte G r a t v →
  greads_byte (gx_hull G cs) r a (hren G cs t) v.
Proof.
  intros Hc Hrd. apply (rows_rel_rdb _ _ _ r a t v (hull_rows_rel G cs)).
  by apply gxc_rdb.
Qed.

Lemma gxh_rdb_inv G cs r a t' v :
  greads_byte (gx_hull G cs) r a t' v →
  gcut cs r = true ∧ ∃ t, greads_byte G r a t v ∧ t' = hren G cs t.
Proof.
  intros Hrd'.
  destruct (rows_rel_rdb_inv _ _ _ r a t' v (hull_rows_rel G cs) Hrd')
    as (t & -> & Hrd).
  apply gxc_rdb in Hrd as [Hc Hrd]. split; [done|]. by exists t.
Qed.

Lemma gxh_gppo G cs e1 e2 : gppo (gx_hull G cs) e1 e2 → gppo G e1 e2.
Proof.
  intros Hppo. apply (gxc_gppo G cs).
  by apply (rows_rel_gppo _ _ _ e1 e2 (hull_rows_rel G cs)).
Qed.

Lemma gxh_gppo_cut G cs e1 e2 :
  gppo (gx_hull G cs) e1 e2 → gcut cs e1 = true ∧ gcut cs e2 = true.
Proof.
  intros Hppo. apply (gxc_gppo_cut G cs).
  by apply (rows_rel_gppo _ _ _ e1 e2 (hull_rows_rel G cs)).
Qed.

Lemma gxh_gmsg G cs e : gcut cs e = true → gmsg (gx_hull G cs) e = gmsg G e.
Proof.
  intros Hc. rewrite /gmsg (rows_rel_lbl _ _ _ e (hull_rows_rel G cs))
                     (gxc_lbl_in G cs e Hc).
  destruct (gx_lbl G e) as [l|]; [|done]. simpl. rewrite lbl_ren_wr.
  destruct (lb_wr l) as [[base vs]|]; [|done]. by rewrite lbl_ren_cls.
Qed.

(** ** 3.2 The gmo and write-index layers, in terms of [G] *)

Lemma gxh_gmo_lt G cs e1 e2 :
  NoDup (gx_gmo G) →
  gmo_lt (gx_hull G cs) e1 e2
  ↔ gcut cs e1 = true ∧ gcut cs e2 = true ∧ gmo_lt G e1 e2.
Proof. exact (gxc_gmo_lt G cs e1 e2). Qed.

Lemma gxh_gwrites G cs : gwrites (gx_hull G cs) = gwrites (gx_cut G cs).
Proof.
  rewrite /gwrites gxh_gmo. apply filter_iff_elem. intros e _.
  rewrite (rows_rel_gis_w _ _ _ e (hull_rows_rel G cs)). done.
Qed.

Lemma gxh_gwrites_G G cs :
  gwrites (gx_hull G cs) = filter (gcut cs) (gwrites G).
Proof. by rewrite gxh_gwrites gxc_gwrites. Qed.

Lemma gxh_gwrites_elem G cs w :
  w ∈ gwrites (gx_hull G cs) ↔ gcut cs w = true ∧ w ∈ gwrites G.
Proof. rewrite gxh_gwrites. apply gxc_gwrites_elem. Qed.

Lemma gxh_gwix G cs w : gwix (gx_hull G cs) w = gwix (gx_cut G cs) w.
Proof. by rewrite /gwix gxh_gwrites. Qed.

Lemma gxh_gwrite_at G cs t :
  gwrite_at (gx_hull G cs) t = gwrite_at (gx_cut G cs) t.
Proof. rewrite /gwrite_at gxh_gwrites. by destruct t. Qed.

Lemma gxh_gwix_lt G cs w1 w2 :
  NoDup (gx_gmo G) →
  w1 ∈ gwrites (gx_hull G cs) → w2 ∈ gwrites (gx_hull G cs) →
  ((gwix (gx_hull G cs) w1 < gwix (gx_hull G cs) w2)%nat
   ↔ (gwix G w1 < gwix G w2)%nat).
Proof.
  rewrite !gxh_gwix gxh_gwrites. apply gxc_gwix_lt.
Qed.

Lemma gxh_gwix_le G cs w1 w2 :
  NoDup (gx_gmo G) →
  w1 ∈ gwrites (gx_hull G cs) → w2 ∈ gwrites (gx_hull G cs) →
  (gwix G w1 ≤ gwix G w2)%nat →
  (gwix (gx_hull G cs) w1 ≤ gwix (gx_hull G cs) w2)%nat.
Proof.
  rewrite !gxh_gwix gxh_gwrites. apply gxc_gwix_le.
Qed.

(** ** 3.3 [hren], spelled through the hull *)

(** THE DEFINING EQUATION: [π (gwix G w) = gwix (hull) w] for a hull
    write, in the form every consumer holds it (a [gwrite_at] fact). *)
Lemma hren_wix G cs t w :
  gwrite_at G t = Some w → gcut cs w = true →
  hren G cs t = gwix (gx_hull G cs) w.
Proof. intros Ht Hc. rewrite /hren Ht Hc. by rewrite gxh_gwix. Qed.

Lemma hren_gwix G cs w :
  NoDup (gx_gmo G) → w ∈ gwrites G → gcut cs w = true →
  hren G cs (gwix G w) = gwix (gx_hull G cs) w.
Proof.
  intros Hnd Hw Hc. apply hren_wix; [by apply gwrite_at_gwix|done].
Qed.

Lemma hren_wat G cs t w :
  gwrite_at G t = Some w → gcut cs w = true →
  gwrite_at (gx_hull G cs) (hren G cs t) = Some w.
Proof.
  intros Ht Hc. rewrite (hren_wix G cs t w Ht Hc).
  apply gwrite_at_gwix, gxh_gwrites_elem. split; [done|].
  destruct t as [|i]; [done|]. by eapply gwrites_lookup_elem.
Qed.

Lemma hren_pos G cs t w :
  gwrite_at G t = Some w → gcut cs w = true → (0 < hren G cs t)%nat.
Proof.
  intros Ht Hc. rewrite (hren_wix G cs t w Ht Hc).
  apply gwix_pos, gxh_gwrites_elem. split; [done|].
  destruct t as [|i]; [done|]. by eapply gwrites_lookup_elem.
Qed.

(** [π] REFLECTS [0]: only the era-initial index maps to the era-initial
    index — the reason the hull's [gload_value] lands in the right branch
    of its own match. *)
Lemma hren_zero_inv G cs t w :
  gwrite_at G t = Some w → gcut cs w = true → hren G cs t ≠ 0%nat.
Proof. intros Ht Hc. pose proof (hren_pos G cs t w Ht Hc). lia. Qed.

(* ====================================================================== *)
(** * 4. THE HULL CONDITION AND CONSISTENCY

    [hull_ok] is the whole of F3's "closed under po-predecessors and
    rf-sources": po-closure is free (a per-hart cut is a prefix), so only
    RF-CLOSURE is a clause. *)

Definition hull_ok (G : gexec) (cs : list nat) : Prop :=
  length cs = length (gx_prog G) ∧
  (∀ r a t v w, gcut cs r = true → greads_byte G r a t v →
                gwrite_at G t = Some w → gcut cs w = true).

Lemma hull_ok_len G cs : hull_ok G cs → length cs = length (gx_prog G).
Proof. by intros [? _]. Qed.

Lemma hull_ok_rf G cs r a t v w :
  hull_ok G cs → gcut cs r = true → greads_byte G r a t v →
  gwrite_at G t = Some w → gcut cs w = true.
Proof. intros [_ H]. by eapply H. Qed.

(** The same clause in [WeakRvwmoAcyc]'s vocabulary: the cut is closed
    under [grf]. *)
Lemma hull_ok_grf G cs w r :
  hull_ok G cs → gcut cs r = true → grf G w r → gcut cs w = true.
Proof. intros Hok Hc (a & t & v & Hrd & Hat). by eapply hull_ok_rf. Qed.

Theorem hull_consistent G cs :
  rvwmo_minus_consistent G → hull_ok G cs →
  rvwmo_minus_consistent (gx_hull G cs).
Proof.
  intros Hcons Hok. pose proof Hcons as (Hwf & Hppo & Hlv & Hat).
  pose proof Hwf as (Hnd & Hmem & Hsh).
  pose proof (hull_ok_rf G cs) as Hrf.
  split_and!.
  - (* ---------------- gwf ---------------- *)
    split_and!.
    + rewrite gxh_gmo. by apply gxc_nodup.
    + intros e. rewrite gxh_gmo gxc_gmo_elem gxh_gmem.
      split; intros [Hc He]; (split; [done|by apply Hmem]).
    + intros i p' k l' Hp' Hk'.
      rewrite gxh_prog_lookup in Hp'.
      destruct (cs !! i) as [c|] eqn:Hc; [|done].
      destruct (gx_prog G !! i) as [p|] eqn:Hp; [|done].
      simpl in Hp'. simplify_eq.
      rewrite list_lookup_fmap in Hk'.
      apply fmap_Some in Hk' as (l & Hl & ->).
      apply lookup_take_Some in Hl as [Hl _].
      apply lbl_ren_shape. by eapply Hsh.
  - (* ---------------- ppo⁻ ⊆ gmo ---------------- *)
    intros e1 e2 Hppo'.
    destruct (gxh_gppo_cut G cs e1 e2 Hppo') as [Hc1 Hc2].
    pose proof (Hppo e1 e2 (gxh_gppo G cs e1 e2 Hppo')) as Hmo.
    apply gxh_gmo_lt; [done|]. by split_and!.
  - (* ---------------- load value ---------------- *)
    intros e a t' v Hrd'.
    apply gxh_rdb_inv in Hrd' as (Hce & t & Hrd & ->).
    destruct (Hlv e a t v Hrd) as [Hsrc Hmax].
    (* the source facts, once: available to BOTH halves *)
    assert (Hsrcw : ∀ (Ht : (0 < t)%nat),
              ∃ w, gwrite_at G t = Some w ∧ gcut cs w = true ∧
                   gwrites_byte G w a v ∧ gvisible G w e ∧
                   w ∈ gwrites (gx_hull G cs) ∧ gwix G w = t).
    { intros Ht. destruct (gload_src_elim G t a v e Ht Hsrc)
        as (w & Hwat & Hwb & Hvis).
      assert (Hcw : gcut cs w = true)
        by exact (Hrf e a t v w Hok Hce Hrd Hwat).
      destruct (gwrite_at_inv G t w Hnd Hwat) as (Hwg & Hwix).
      exists w. split_and!; [done|done|done|done| |done].
      apply gxh_gwrites_elem. done. }
    split.
    + (* the ∃ / visibility half: the source is IN the hull, at [π t] *)
      destruct t as [|i].
      * rewrite hren_zero. exact Hsrc.
      * destruct (Hsrcw ltac:(lia))
          as (w & Hwat & Hcw & Hwb & Hvis & Hwh & Hwix).
        apply gload_src_intro; [by eapply hren_pos|].
        exists w. split_and!.
        { by apply hren_wat. }
        { by apply gxh_wrb. }
        { destruct Hvis as [Hmo|Hpo]; [left|right].
          - apply gxh_gmo_lt; [done|]. by split_and!.
          - apply gxh_gpo. by split. }
    + (* the co-max half: FEWER writes only weakens it *)
      intros w' v' Hwb' Hvis'.
      apply gxh_wrb in Hwb' as [Hcw' Hwb'].
      assert (Hvis : gvisible G w' e).
      { destruct Hvis' as [Hmo|Hpo]; [left|right].
        - by apply (gxh_gmo_lt G cs w' e Hnd) in Hmo as (_ & _ & ?).
        - by apply gxh_gpo in Hpo as [? _]. }
      pose proof (Hmax w' v' Hwb' Hvis) as Hle.
      assert (Hw'g : w' ∈ gwrites G)
        by (eapply gis_w_gwrites; [done| |by eapply gwrites_byte_gis_w];
            destruct Hwb' as (l & ? & ? & ? & Hl & _); by exists l).
      assert (Hw'h : w' ∈ gwrites (gx_hull G cs))
        by (apply gxh_gwrites_elem; done).
      destruct t as [|i].
      * exfalso. pose proof (gwix_pos G w' Hw'g). lia.
      * destruct (Hsrcw ltac:(lia))
          as (w & Hwat & Hcw & Hwb & Hvisw & Hwh & Hwix).
        rewrite (hren_wix G cs (S i) w Hwat Hcw).
        apply gxh_gwix_le; [done|done|done|]. lia.
  - (* ---------------- atomicity ---------------- *)
    intros e a t' v Hrd' Hw'.
    apply gxh_rdb_inv in Hrd' as (Hce & t & Hrd & ->).
    apply gxh_glbl_is in Hw' as [_ Hw]; [|apply lbl_ren_is_w].
    destruct (Hlv e a t v Hrd) as [Hsrc _].
    intros w' v' Hwb' [Hlt1 Hlt2].
    apply gxh_wrb in Hwb' as [Hcw' Hwb'].
    assert (Heg : e ∈ gwrites G)
      by (eapply gis_w_gwrites; [done| |by eapply glbl_is_w_gis_w];
          destruct Hw as (l & Hl & _); by exists l).
    assert (Heh : e ∈ gwrites (gx_hull G cs))
      by (apply gxh_gwrites_elem; done).
    assert (Hw'g : w' ∈ gwrites G)
      by (eapply gis_w_gwrites; [done| |by eapply gwrites_byte_gis_w];
          destruct Hwb' as (l & ? & ? & ? & Hl & _); by exists l).
    assert (Hw'h : w' ∈ gwrites (gx_hull G cs))
      by (apply gxh_gwrites_elem; done).
    apply (Hat e a t v Hrd Hw w' v' Hwb'). split.
    + destruct t as [|i]; [by apply gwix_pos|].
      destruct (gload_src_elim G (S i) a v e ltac:(lia) Hsrc)
        as (w & Hwat & Hwb & Hvis).
      assert (Hcw : gcut cs w = true)
        by exact (Hrf e a (S i) v w Hok Hce Hrd Hwat).
      destruct (gwrite_at_inv G (S i) w Hnd Hwat) as (Hwg & Hwix).
      assert (Hwh : w ∈ gwrites (gx_hull G cs))
        by (apply gxh_gwrites_elem; done).
      rewrite (hren_wix G cs (S i) w Hwat Hcw) in Hlt1.
      apply (gxh_gwix_lt G cs w w' Hnd Hwh Hw'h) in Hlt1. lia.
    + by apply (gxh_gwix_lt G cs w' e Hnd Hw'h Heh).
Qed.

(* ====================================================================== *)
(** * 5. RULE 14 FROM VIOLATION-FREEDOM OF THE HULL *)

Lemma gviol_hull G cs e w :
  NoDup (gx_gmo G) → gviol (gx_hull G cs) e w →
  gviol G e w ∧ gcut cs e = true ∧ gcut cs w = true.
Proof.
  intros Hnd (Hpo & Hme & Hw & Hmo).
  apply gxh_gpo in Hpo as [Hpo Hcw].
  apply gxh_gmem in Hme as [Hce Hme].
  apply gxh_glbl_is in Hw as [_ Hw]; [|apply lbl_ren_is_w].
  apply (gxh_gmo_lt G cs w e Hnd) in Hmo as (_ & _ & Hmo).
  by split_and!.
Qed.

Theorem hull_rule14 G cs :
  rvwmo_minus_consistent G → hull_ok G cs →
  (∀ e w, gcut cs e = true → gcut cs w = true → ¬ gviol G e w) →
  grule14 (gx_hull G cs).
Proof.
  intros Hc Hok Hvf. pose proof Hc as (Hwf & _ & _). pose proof Hwf as (Hnd & _).
  apply gviol_grule14.
  - by apply (hull_consistent G cs Hc Hok).
  - intros e w Hv. destruct (gviol_hull G cs e w Hnd Hv) as (Hv' & Hce & Hcw).
    by apply (Hvf e w Hce Hcw).
Qed.

(* ====================================================================== *)
(** * 6. THE [gdexec] FORM: the dep fragment restricts by filtering *)

Definition gd_hull (GD : gdexec) (cs : list nat) : gdexec :=
  GDExec (gx_hull (gd_g GD) cs)
         (filter (λ rw : geid * geid, gcut cs rw.1 && gcut cs rw.2)
                 (gd_deps GD)).

Lemma gd_hull_deps GD cs rw :
  rw ∈ gd_deps (gd_hull GD cs) ↔
  rw ∈ gd_deps GD ∧ gcut cs rw.1 = true ∧ gcut cs rw.2 = true.
Proof.
  rewrite /gd_hull /= elem_of_list_filter Is_true_true andb_true_iff.
  naive_solver.
Qed.

Theorem hull_deps_consistent GD cs :
  rvwmo_minus_deps_consistent GD → hull_ok (gd_g GD) cs →
  rvwmo_minus_deps_consistent (gd_hull GD cs).
Proof.
  intros (Hc & Hdwf & Hdmo) Hok.
  pose proof Hc as (Hwf & _ & _). pose proof Hwf as (Hnd & Hmem & _).
  split_and!.
  - by apply hull_consistent.
  - intros rw [Hrw [Hc1 Hc2]]%gd_hull_deps.
    destruct (Hdwf rw Hrw) as (H1 & H2 & H3 & H4).
    split_and!; [done|done| |];
      apply gxh_glbl_is; by [apply lbl_ren_is_r|apply lbl_ren_is_w| |].
  - intros rw [Hrw [Hc1 Hc2]]%gd_hull_deps.
    pose proof (Hdmo rw Hrw) as Hmo.
    apply gxh_gmo_lt; [done|]. by split_and!.
Qed.

(* ====================================================================== *)
(** * 7. THE COMPOSITION: a violation-free hull LINEARIZES

    The exact shape of [restrict_linearizes], with the rows RENAMED and the
    log the HULL'S writes' messages.  Messages carry base, values, author
    and class — none of them a [ts] entry — so [gmsg] is renaming-blind
    ([gxh_gmsg]) and the log is [G]'s own messages, in [G]'s own order. *)

Lemma omap_gmsg_hull G cs (l : list geid) :
  (∀ e, e ∈ l → gcut cs e = true) →
  omap (gmsg (gx_hull G cs)) l = omap (gmsg G) l.
Proof.
  induction l as [|e l IH]; intros Hcut; [done|].
  assert (Hrest : ∀ x, x ∈ l → gcut cs x = true)
    by (intros x Hx; by apply Hcut, elem_of_list_further).
  csimpl. rewrite (gxh_gmsg G cs e (Hcut e (elem_of_list_here _ _))).
  destruct (gmsg G e); by rewrite (IH Hrest).
Qed.

Theorem hull_linearizes GD cs :
  rvwmo_minus_deps_consistent GD → hull_ok (gd_g GD) cs →
  (∀ e w, gcut cs e = true → gcut cs w = true → ¬ gviol (gd_g GD) e w) →
  ∃ c : cand,
    srvwmo_consistent c ∧
    cd_img c = gx_img (gd_g GD) ∧
    (∀ i, (λ s, es_lb s) <$> filter (λ s, es_ag s = i) (cd_tr c)
          = lbl_ren (hren (gd_g GD) cs)
              <$> take (default 0%nat (cs !! i))
                       (default [] (gx_prog (gd_g GD) !! i))) ∧
    cd_log c (length (cd_tr c))
      = omap (gmsg (gd_g GD)) (filter (gcut cs) (gwrites (gd_g GD))).
Proof.
  intros HD Hok Hvf. pose proof HD as (Hc & _ & _).
  destruct (rule14_linearization (gx_hull (gd_g GD) cs)
              (hull_consistent _ _ Hc Hok)
              (hull_rule14 _ _ Hc Hok Hvf))
    as (c & Hsr & Himg & Hrow & Hlog).
  exists c. split_and!; [done|exact Himg| |].
  - intros i. by rewrite (Hrow i) gxh_row.
  - rewrite Hlog gxh_gwrites_G. apply omap_gmsg_hull.
    intros e He. apply elem_of_list_filter in He as [He _].
    by apply Is_true_true.
Qed.

(* ====================================================================== *)
(** * 8. THE FULL CUT IS A HULL, AND IT IS THE IDENTITY

    [hull_ok] is satisfiable and [gcut] is not accidentally empty — B1a's
    §9.1, with the extra content that the RENAMING is the identity there
    ([hren_full]), so [gx_hull] is a genuine generalization of [G] itself
    rather than of some renamed copy. *)

Lemma gfull_cut G e : is_Some (gx_lbl G e) → gcut (gfull_cs G) e = true.
Proof.
  intros [l Hl]. rewrite /gx_lbl in Hl.
  destruct (gx_prog G !! e.1) as [p|] eqn:Hp; simpl in Hl; [|done].
  apply (gcut_intro _ _ (length p)).
  - by rewrite /gfull_cs list_lookup_fmap Hp.
  - by eapply lookup_lt_Some.
Qed.

Lemma gfull_filter_gmo G :
  gwf G → filter (gcut (gfull_cs G)) (gx_gmo G) = gx_gmo G.
Proof.
  intros Hwf. apply filter_all. intros e He. apply Is_true_true.
  apply gfull_cut. destruct (gwf_gmo_mem G e Hwf He) as (l & Hl & _).
  by exists l.
Qed.

Lemma gfull_filter_gwrites G :
  gwf G → filter (gcut (gfull_cs G)) (gwrites G) = gwrites G.
Proof.
  intros Hwf. apply filter_all. intros e He. apply Is_true_true.
  apply gwrites_elem_of in He as [He _].
  apply gfull_cut. destruct (gwf_gmo_mem G e Hwf He) as (l & Hl & _).
  by exists l.
Qed.

Lemma hren_full G : gwf G → ∀ t, hren G (gfull_cs G) t = t.
Proof.
  intros Hwf t. pose proof Hwf as (Hnd & _ & _).
  rewrite /hren. destruct (gwrite_at G t) as [w|] eqn:Ht; [|done].
  destruct (gcut (gfull_cs G) w) eqn:Hc; [|done].
  rewrite /gwix gxc_gwrites (gfull_filter_gwrites G Hwf).
  by destruct (gwrite_at_inv G t w Hnd Ht) as (_ & <-).
Qed.

Theorem hull_ok_full G : gwf G → hull_ok G (gfull_cs G).
Proof.
  intros Hwf. split.
  - by rewrite /gfull_cs length_fmap.
  - intros r a t v w _ _ Hwat. apply gfull_cut.
    destruct t as [|i]; [done|].
    assert (Hw : w ∈ gwrites G) by (by eapply gwrites_lookup_elem).
    apply gwrites_elem_of in Hw as [Hw _].
    destruct (gwf_gmo_mem G w Hwf Hw) as (l & Hl & _). by exists l.
Qed.

Lemma zip_with_take_full (prog : list (list lbl)) :
  zip_with take (length <$> prog) prog = prog.
Proof.
  induction prog as [|p prog IH]; [done|].
  by rewrite fmap_cons /= take_ge // IH.
Qed.

Theorem gx_hull_full G : gwf G → gx_hull G (gfull_cs G) = G.
Proof.
  intros Hwf. pose proof (hren_full G Hwf) as Hpi.
  rewrite /gx_hull /gfull_cs zip_with_take_full (gfull_filter_gmo G Hwf).
  destruct G as [img prog gmo]; simpl in *. f_equal.
  trans ((λ row : list lbl, row) <$> prog); [|apply fmap_id_gen].
  apply list_fmap_ext. intros i r _. simpl.
  trans (lbl_ren (λ t, t) <$> r); [|apply row_ren_id].
  apply list_fmap_ext. intros j l _. by apply lbl_ren_ext.
Qed.

(* ====================================================================== *)
(** * 9. NON-VACUITY, AT THE PROBE THAT MOTIVATED THE GENERALIZATION

    [WeakRvwmoProbeRestr.erg] is the graph where B1a's [restr_ok] has NO
    solution at the frontier ([erg_no_restr]) — hart 1's early read
    straddles it out of po order.  The hull [ecs = [1; 0] ] keeps exactly
    hart 0's load [e] and nothing else: [e] reads the ERA-INITIAL image, so
    there is no source to keep and rf-closure is immediate; and a one-event
    cut carries no po edge, so it is violation-free.  Hence
    [hull_linearizes] applies exactly where [restrict_linearizes] provably
    could not. *)

Definition ecs : list nat := [1%nat; 0%nat].

Lemma erg_cut e : gcut ecs e = true ↔ e = (0%nat, 0%nat).
Proof.
  destruct e as [i k]. split.
  - rewrite /gcut /=. destruct i as [|[|i]]; simpl.
    + intros Hd%bool_decide_eq_true. simpl in Hd.
      assert (k = 0%nat) as -> by lia. done.
    + done.
    + done.
  - intros Heq. simplify_eq. by vm_compute.
Qed.

Lemma erg_hull_ok : hull_ok erg ecs.
Proof.
  split; [reflexivity|].
  intros r a t v w Hcr Hrd Hwat.
  apply erg_cut in Hcr as ->.
  destruct Hrd as (l & base & ts & vs & j & Hl & Hrd & Ht & _).
  rewrite /gx_lbl /= in Hl. simplify_eq/=.
  (* the load names the era-initial index, which is no write at all,
     so [Hwat] is absurd *)
  by destruct j as [|j]; simplify_eq/=.
Qed.

Lemma erg_hull_viol_free :
  ∀ e w, gcut ecs e = true → gcut ecs w = true → ¬ gviol erg e w.
Proof.
  intros e w He%erg_cut Hw%erg_cut. simplify_eq.
  intros ((_ & Hlt & _) & _). simpl in Hlt. lia.
Qed.

Definition ergd : gdexec := GDExec erg [].

Lemma ergd_consistent : rvwmo_minus_deps_consistent ergd.
Proof.
  split_and!; [exact erg_consistent| |]; by intros rw Hrw%elem_of_nil.
Qed.

(** THE INSTANTIATION. *)
Theorem erg_hull_linearizes :
  ∃ c : cand,
    srvwmo_consistent c ∧
    cd_img c = gx_img erg ∧
    (∀ i, (λ s, es_lb s) <$> filter (λ s, es_ag s = i) (cd_tr c)
          = lbl_ren (hren erg ecs)
              <$> take (default 0%nat (ecs !! i))
                       (default [] (gx_prog erg !! i))) ∧
    cd_log c (length (cd_tr c))
      = omap (gmsg erg) (filter (gcut ecs) (gwrites erg)).
Proof.
  exact (hull_linearizes ergd ecs ergd_consistent erg_hull_ok
                         erg_hull_viol_free).
Qed.

(** THE CONTRAST, in one statement: the hull condition is SATISFIABLE at
    [erg] while B1a's restriction condition is NOT. *)
Theorem erg_hull_beats_restr :
  hull_ok erg ecs ∧ (∀ cs, ¬ restr_ok erg cs 1%nat).
Proof. split; [exact erg_hull_ok|exact erg_no_restr]. Qed.
