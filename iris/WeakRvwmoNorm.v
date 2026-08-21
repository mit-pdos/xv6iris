(** * WeakRvwmoNorm.v — THE EXCHANGE NORMALIZATION (route B, stage B2d)

    Design: [claude-notes/design/weak-memory-route-b.md] §3b′, including the
    "TERMINATION — RESOLVED" block, whose PO-MINIMAL-WITNESS DISCIPLINE this
    file mechanizes.  The kit it composes is [WeakRvwmoXchg.v] (B2a/B2c/B2b);
    the model is [WeakRvwmoGraph.v]'s RVWMO⁻ + the dep fragment.

    THE POINT.  Route B's chain starts by NORMALIZING an RVWMO⁻(+deps)
    consistent graph towards [grule14] — the gate T2-1c's linearization
    consumes.  The normalization is a sequence of ADJACENT gmo exchanges,
    organised as:

      - OUTER induction on the number of rule-14 inversions [nviol] (§2);
      - pick [w], the gmo-MINIMAL violating write, and [e*], its PO-MINIMAL
        witness (§8 — both exist, finitely many events);
      - INNER induction: DESCEND [e*] one gmo slot at a time until it sits
        directly above [w], then swap the pair itself.  Each interior swap
        is B2a/B2c/B2b with its side conditions VACUOUS or DERIVABLE; the
        final swap is [gswap_resolves]/[gswapw_resolves], which is where the
        measure strictly drops.

    THE ENGINE is §6's VACUITY LEMMA [po_min_no_blocker]: a same-hart
    po-earlier memory event sitting gmo-between [w] and [e*] would
    ITSELF be a witness of [w] po-before [e*], contradicting [e*]'s
    po-minimality.  Every [¬ gppo z e*] and [¬ gpo z e*] side condition of
    the kit, every same-hart rf-source block, and the same-hart half of
    (W,W) byte-disjointness are one application of it.

    WHAT IS LEFT OVER — the three KILL configurations (§5), taken as
    explicit hypotheses of [normalize] and discharged later by B2e from the
    realized prefix + the exports:

      - [kill_K1] — [e*] a read whose CROSS-HART rf-source sits gmo-in the
        interval (S6's reader-of-the-early-write, entered from the witness
        side);
      - [kill_K2] — [e*] a write, and an interval event reads one of [e*]'s
        bytes at an OLDER write index (the MP-stale-reader shape; the co-max
        side condition of B2c);
      - [kill_K3] — [e*] a write and a CROSS-HART SAME-BYTE write sits
        gmo-in the interval (the kit's deliberately excluded (W,W) case).

    THE ONE BINDER ADJUSTMENT relative to the B2d spec, and why: each kill
    quantifies over an arbitrary [GD'] with [gd_equiv GD GD'] — the same
    rows and the same write messages modulo the write-index renaming, still
    consistent with the same dep fragment — rather than over [GD] alone.
    The descent's kill configurations arise at INTERMEDIATE graphs of the
    exchange chain, and they cannot be pulled back to [GD].  Two independent
    obstructions: (i) violations only SHRINK along the chain, so a violation
    of [GD] need not be one of the intermediate graph — and hence the
    intermediate graph's gmo-minimality clause does NOT imply [GD]'s, the
    minimality premises being backward-unstable exactly where the kit is
    forward-monotone; (ii) a (W,W) swap renumbers write indices by a
    NON-MONOTONE transposition, so [kill_K2]'s [t < gwix e] does not
    transport under [π] even when everything else does.  [gd_equiv] is exactly the
    invariant the induction maintains anyway (it IS [normalize]'s own
    conclusion), and B2e's discharge is unaffected in kind: a rows-equivalent
    consistent graph has the same program rows and the same per-write
    messages, so the realized-prefix argument applies to it verbatim.

    THE OUTPUT correspondence: [rows_rel π] (same image, same rows up to
    renaming every read's [ts] entries by [π], [π 0 = 0]) and [wperm π]
    (π injective, [gwrite_at G' (π t) = gwrite_at G t], same write count) —
    i.e. the observables are EQUAL and only write-index names move.

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakAxiomatic WeakAxiomatic2
                            WeakRvwmoGraph WeakRvwmoXchg.

(* ====================================================================== *)
(** * 1. A GENERIC LIST KIT: filter counts and minima

    Nothing here mentions the memory model.  Two facts carry the measure — a
    pointwise-smaller predicate filters no more elements, and STRICTLY fewer
    as soon as one element is dropped — and one carries the two choices (a
    non-empty list has an element of minimal key). *)

Lemma filter_length_le {A} (P Q : A → Prop)
    `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)} (l : list A) :
  (∀ y, P y → Q y) → (length (filter P l) ≤ length (filter Q l))%nat.
Proof.
  intros HPQ. induction l as [|a l IH]; [done|].
  rewrite !filter_cons.
  case_decide as HP; case_decide as HQ; simpl; try lia.
  by destruct (HQ (HPQ a HP)).
Qed.

Lemma filter_length_lt {A} (P Q : A → Prop)
    `{∀ x, Decision (P x)} `{∀ x, Decision (Q x)} (l : list A) x :
  (∀ y, P y → Q y) → x ∈ l → Q x → ¬ P x →
  (length (filter P l) < length (filter Q l))%nat.
Proof.
  intros HPQ Hx HQx HPx. induction l as [|a l IH]; [by apply elem_of_nil in Hx|].
  apply elem_of_cons in Hx as [->|Hx].
  - rewrite !filter_cons.
    case_decide as H1; [by destruct (HPx H1)|].
    case_decide as H2; [|by destruct (H2 HQx)].
    simpl. pose proof (filter_length_le P Q l HPQ). lia.
  - specialize (IH Hx). rewrite !filter_cons.
    case_decide as HP; case_decide as HQ; simpl; try lia.
    by destruct (HQ (HPQ a HP)).
Qed.

Lemma filter_pos {A} (P : A → Prop) `{∀ x, Decision (P x)} (l : list A) x :
  x ∈ l → P x → (0 < length (filter P l))%nat.
Proof.
  intros Hx HPx.
  assert (Hin : x ∈ filter P l) by (apply elem_of_list_filter; done).
  destruct (filter P l) as [|y k] eqn:Hf; [by apply elem_of_nil in Hin|]. simpl. lia.
Qed.

(** A non-empty list has an element of minimal key. *)
Lemma list_min_by {A} (f : A → nat) (l : list A) :
  l ≠ [] → ∃ y, y ∈ l ∧ ∀ z, z ∈ l → (f y ≤ f z)%nat.
Proof.
  induction l as [|a l IH]; [done|]. intros _.
  destruct l as [|b l'].
  - exists a. split; [apply elem_of_list_here|].
    intros z Hz. apply elem_of_list_singleton in Hz as ->. lia.
  - destruct IH as (y & Hy & Hmin); [done|].
    destruct (decide (f a ≤ f y)%nat) as [Hle|Hgt].
    + exists a. split; [apply elem_of_list_here|].
      intros z Hz. apply elem_of_cons in Hz as [->|Hz]; [lia|].
      specialize (Hmin z Hz). lia.
    + exists y. split; [by apply elem_of_list_further|].
      intros z Hz. apply elem_of_cons in Hz as [->|Hz]; [lia|].
      by apply Hmin.
Qed.

(* ====================================================================== *)
(** * 2. THE MEASURE: the number of rule-14 inversions

    Events are finite — a graph's programs are a finite list of finite rows —
    so [gevs'] enumerates every LABELLED position and [gpairs] every pair of
    them.  [nviol] counts the [gviol] pairs among those.  The enumeration is
    read off [gx_prog] ALONE, which is what makes it literally EQUAL for two
    rows-related graphs (§3), so the two measures are comparable without any
    permutation reasoning. *)

Definition nrow (G : gexec) (i : nat) : nat := length (default [] (gx_prog G !! i)).

Definition gevs' (G : gexec) : list geid :=
  mjoin ((λ i, (λ k, (i, k)) <$> seq 0%nat (nrow G i))
           <$> seq 0%nat (length (gx_prog G))).

Lemma elem_of_gevs' G e : is_Some (gx_lbl G e) → e ∈ gevs' G.
Proof.
  intros [l Hl]. rewrite /gx_lbl in Hl.
  destruct (gx_prog G !! e.1) as [p|] eqn:Hp; simpl in Hl; [|done].
  rewrite /gevs'. apply elem_of_list_join.
  exists ((λ k, (e.1, k)) <$> seq 0%nat (nrow G e.1)). split.
  - apply elem_of_list_fmap. exists e.2. split; [by destruct e|].
    apply elem_of_seq. rewrite /nrow Hp /=. split; [lia|].
    by eapply lookup_lt_Some.
  - apply elem_of_list_fmap. exists e.1. split; [done|].
    apply elem_of_seq. split; [lia|]. simpl. by eapply lookup_lt_Some.
Qed.

Definition gpairs (G : gexec) : list (geid * geid) :=
  mjoin ((λ e, (λ w, (e, w)) <$> gevs' G) <$> gevs' G).

Lemma elem_of_gpairs G e w : e ∈ gevs' G → w ∈ gevs' G → (e, w) ∈ gpairs G.
Proof.
  intros He Hw. apply elem_of_list_join.
  exists ((λ w', (e, w')) <$> gevs' G). split.
  - apply elem_of_list_fmap. by exists w.
  - apply elem_of_list_fmap. by exists e.
Qed.

(** ** 2.1 Decidability of the model's predicates *)

Local Instance gmem_dec G e : Decision (gmem G e).
Proof.
  rewrite /gmem. destruct (gx_lbl G e) as [l|].
  - destruct (lb_is_mem l) eqn:Hm.
    + left. by exists l.
    + right. intros (l' & Hl' & Hm'). simplify_eq. by rewrite Hm in Hm'.
  - right. intros (l' & Hl' & _). by simplify_eq.
Qed.

Local Instance glbl_is_dec G e P : Decision (glbl_is G e P).
Proof.
  rewrite /glbl_is. destruct (gx_lbl G e) as [l|].
  - destruct (P l) eqn:Hm.
    + left. by exists l.
    + right. intros (l' & Hl' & Hm'). simplify_eq. by rewrite Hm in Hm'.
  - right. intros (l' & Hl' & _). by simplify_eq.
Qed.

Local Instance gpo_dec G e1 e2 : Decision (gpo G e1 e2).
Proof. rewrite /gpo. apply _. Qed.

Local Instance gmo_lt_dec G e1 e2 : Decision (gmo_lt G e1 e2).
Proof. rewrite /gmo_lt. apply _. Qed.

Local Instance gviol_dec G e w : Decision (gviol G e w).
Proof. rewrite /gviol. apply _. Qed.

(** ** 2.2 The count *)

Definition violp (G : gexec) (p : geid * geid) : Prop := gviol G p.1 p.2.

Local Instance violp_dec G p : Decision (violp G p).
Proof. rewrite /violp. apply _. Qed.

Definition nviol (G : gexec) : nat := length (filter (violp G) (gpairs G)).

(** A violating pair is one of the enumerated pairs. *)
Lemma gviol_gpairs G e w : gviol G e w → (e, w) ∈ gpairs G.
Proof.
  intros (Hpo & (l & Hl & _) & (lw & Hlw & _) & _). apply elem_of_gpairs.
  - apply elem_of_gevs'. by exists l.
  - apply elem_of_gevs'. by exists lw.
Qed.

Lemma nviol_zero G : gwf G → nviol G = 0%nat → grule14 G.
Proof.
  intros Hwf H0. apply (gviol_grule14 G Hwf). intros e w Hv.
  pose proof (filter_pos (violp G) (gpairs G) (e, w) (gviol_gpairs G e w Hv) Hv).
  rewrite /nviol in H0. lia.
Qed.

Lemma nviol_le G G' :
  gpairs G' = gpairs G → (∀ e w, gviol G' e w → gviol G e w) →
  (nviol G' ≤ nviol G)%nat.
Proof.
  intros Hp Hmono. rewrite /nviol Hp.
  apply filter_length_le. intros [e w]. apply Hmono.
Qed.

Lemma nviol_lt G G' e w :
  gpairs G' = gpairs G → (∀ e' w', gviol G' e' w' → gviol G e' w') →
  gviol G e w → ¬ gviol G' e w → (nviol G' < nviol G)%nat.
Proof.
  intros Hp Hmono Hv Hnv. rewrite /nviol Hp.
  apply (filter_length_lt _ _ _ (e, w)); [|by apply gviol_gpairs|done|done].
  intros [e' w']. apply Hmono.
Qed.

(* ====================================================================== *)
(** * 3. THE OUTPUT CORRESPONDENCE: [rows_rel] and [wperm]

    The normalization moves no event between harts, changes no value, base,
    class or ordering bit, and adds/removes nothing: the ONLY thing that
    moves is the NAME of a write index, both where it is stored (a read's
    per-byte [ts] entry) and what it denotes (the write sub-order).  [π] is
    that renaming — the composition of the run's adjacent transpositions. *)

(** ** 3.1 Renaming a label's [ts] entries.  [lbl_tswap] is this at [tswap]. *)

(** Two [fmap] equations, stated at the LAMBDA shapes the renaming produces
    (stdpp's [list_fmap_id]/[list_fmap_compose] are at [id]/[∘], and
    rewriting with the latter's higher-order pattern diverges here). *)
Lemma fmap_id_gen {A} (l : list A) : (λ x, x) <$> l = l.
Proof. induction l; f_equal/=; auto. Qed.

Lemma fmap_fmap_gen {A B C} (f : A → B) (g : B → C) (l : list A) :
  g <$> (f <$> l) = (λ x, g (f x)) <$> l.
Proof. induction l; f_equal/=; auto. Qed.

Definition lbl_ren (π : nat → nat) (l : lbl) : lbl :=
  match l with
  | LLoad aq base ts vs => LLoad aq base (π <$> ts) vs
  | LStore rl base vs k => LStore rl base vs k
  | LFence pr pw sr sw => LFence pr pw sr sw
  | LRmw aq rl base ts rvs wvs k => LRmw aq rl base (π <$> ts) rvs wvs k
  end.

Lemma lbl_ren_tswap k1 l : lbl_ren (tswap k1) l = lbl_tswap k1 l.
Proof. by destruct l. Qed.

Lemma lbl_ren_id l : lbl_ren (λ t, t) l = l.
Proof. destruct l; simpl; try done; f_equal; apply fmap_id_gen. Qed.

Lemma lbl_ren_comp π1 π2 l :
  lbl_ren π2 (lbl_ren π1 l) = lbl_ren (λ t, π2 (π1 t)) l.
Proof. destruct l; simpl; try done; f_equal; apply fmap_fmap_gen. Qed.

Lemma lbl_ren_ext π1 π2 l : (∀ t, π1 t = π2 t) → lbl_ren π1 l = lbl_ren π2 l.
Proof.
  intros H. destruct l; simpl; try done; f_equal;
    apply list_fmap_ext; intros i x _; apply H.
Qed.

(** The two renaming equations, lifted to a ROW and to a whole PROGRAM. *)
Lemma row_ren_id (r : list lbl) : lbl_ren (λ t, t) <$> r = r.
Proof.
  trans ((λ l : lbl, l) <$> r).
  - apply list_fmap_ext. intros i l _. apply lbl_ren_id.
  - apply fmap_id_gen.
Qed.

Lemma row_ren_comp π1 π2 π (r : list lbl) :
  (∀ t, π t = π2 (π1 t)) →
  lbl_ren π2 <$> (lbl_ren π1 <$> r) = lbl_ren π <$> r.
Proof.
  intros H. rewrite fmap_fmap_gen. apply list_fmap_ext. intros i l _. simpl.
  rewrite lbl_ren_comp. apply lbl_ren_ext. intros t. by rewrite H.
Qed.

Lemma prog_ren_id (p : list (list lbl)) :
  (λ row : list lbl, lbl_ren (λ t, t) <$> row) <$> p = p.
Proof.
  trans ((λ row : list lbl, row) <$> p).
  - apply list_fmap_ext. intros i r _. apply row_ren_id.
  - apply fmap_id_gen.
Qed.

Lemma prog_ren_comp π1 π2 π (p : list (list lbl)) :
  (∀ t, π t = π2 (π1 t)) →
  (λ row : list lbl, lbl_ren π2 <$> row)
    <$> ((λ row : list lbl, lbl_ren π1 <$> row) <$> p)
  = (λ row : list lbl, lbl_ren π <$> row) <$> p.
Proof.
  intros H. rewrite fmap_fmap_gen. apply list_fmap_ext. intros i r _. simpl.
  by apply row_ren_comp.
Qed.

Lemma lbl_ren_is_r π l : lb_is_r (lbl_ren π l) = lb_is_r l.
Proof. by destruct l. Qed.
Lemma lbl_ren_is_w π l : lb_is_w (lbl_ren π l) = lb_is_w l.
Proof. by destruct l. Qed.
Lemma lbl_ren_is_mem π l : lb_is_mem (lbl_ren π l) = lb_is_mem l.
Proof. by destruct l. Qed.
Lemma lbl_ren_aq π l : lb_aq (lbl_ren π l) = lb_aq l.
Proof. by destruct l. Qed.
Lemma lbl_ren_rl π l : lb_rl (lbl_ren π l) = lb_rl l.
Proof. by destruct l. Qed.
Lemma lbl_ren_cls π l : lb_cls (lbl_ren π l) = lb_cls l.
Proof. by destruct l. Qed.
Lemma lbl_ren_wr π l : lb_wr (lbl_ren π l) = lb_wr l.
Proof. by destruct l. Qed.
Lemma lbl_ren_rd π l base ts vs :
  lb_rd l = Some (base, ts, vs) → lb_rd (lbl_ren π l) = Some (base, π <$> ts, vs).
Proof. destruct l; simpl; intros Hl; by simplify_eq/=. Qed.

(** ** 3.2 [rows_rel]: the SAME OBSERVABLES, modulo the renaming

    Same image; the per-hart rows are the SAME LIST, position by position,
    with every label's constructor, acquire/release bits, base, values and
    class UNCHANGED and only its read [ts] entries renamed by [π]; and [π]
    fixes [0], the era-initial image.  ([rows_rel_lbl] / [rows_rel_gis_w] /
    [rows_rel_wrb] / [rows_rel_rdb] below spell that out event by event.) *)

Definition rows_rel (π : nat → nat) (G G' : gexec) : Prop :=
  gx_img G' = gx_img G ∧
  gx_prog G' = (λ row : list lbl, lbl_ren π <$> row) <$> gx_prog G ∧
  π 0%nat = 0%nat.

Lemma rows_rel_img π G G' : rows_rel π G G' → gx_img G' = gx_img G.
Proof. by intros (? & _ & _). Qed.

Lemma rows_rel_zero π G G' : rows_rel π G G' → π 0%nat = 0%nat.
Proof. by intros (_ & _ & ?). Qed.

(** Same number of harts. *)
Lemma rows_rel_nharts π G G' :
  rows_rel π G G' → length (gx_prog G') = length (gx_prog G).
Proof. intros (_ & Hp & _). by rewrite Hp length_fmap. Qed.

(** Same row, renamed — hence the same row LENGTH. *)
Lemma rows_rel_row π G G' i r :
  rows_rel π G G' → gx_prog G !! i = Some r →
  gx_prog G' !! i = Some (lbl_ren π <$> r).
Proof. intros (_ & Hp & _) Hr. by rewrite Hp list_lookup_fmap Hr. Qed.

Lemma rows_rel_nrow π G G' i : rows_rel π G G' → nrow G' i = nrow G i.
Proof.
  intros (_ & Hp & _). rewrite /nrow Hp list_lookup_fmap.
  destruct (gx_prog G !! i) as [r|]; simpl; [by rewrite length_fmap|done].
Qed.

(** THE EVENT-LEVEL EQUATION. *)
Lemma rows_rel_lbl π G G' e :
  rows_rel π G G' → gx_lbl G' e = lbl_ren π <$> gx_lbl G e.
Proof.
  intros (_ & Hp & _). rewrite /gx_lbl Hp list_lookup_fmap.
  destruct (gx_prog G !! e.1) as [r|]; simpl; [|done].
  by rewrite list_lookup_fmap.
Qed.

Lemma rows_rel_is_Some π G G' e :
  rows_rel π G G' → (is_Some (gx_lbl G' e) ↔ is_Some (gx_lbl G e)).
Proof. intros Hr. rewrite (rows_rel_lbl π G G' e Hr). apply fmap_is_Some. Qed.

Lemma rows_rel_glbl_is π G G' e (P : lbl → bool) :
  rows_rel π G G' → (∀ l, P (lbl_ren π l) = P l) →
  (glbl_is G' e P ↔ glbl_is G e P).
Proof.
  intros Hr HP. rewrite /glbl_is (rows_rel_lbl π G G' e Hr). split.
  - intros (l & Hl & HPl). apply fmap_Some in Hl as (l0 & Hl0 & ->).
    exists l0. rewrite -HP. done.
  - intros (l & Hl & HPl). exists (lbl_ren π l). rewrite Hl /= HP. done.
Qed.

Lemma rows_rel_gis_w π G G' e : rows_rel π G G' → gis_w G' e = gis_w G e.
Proof.
  intros Hr. rewrite /gis_w (rows_rel_lbl π G G' e Hr).
  destruct (gx_lbl G e) as [l|]; simpl; [apply lbl_ren_is_w|done].
Qed.

Lemma rows_rel_gmem π G G' e : rows_rel π G G' → (gmem G' e ↔ gmem G e).
Proof. intros Hr. apply (rows_rel_glbl_is π G G' e lb_is_mem Hr), lbl_ren_is_mem. Qed.

Lemma rows_rel_gpo π G G' e1 e2 : rows_rel π G G' → (gpo G' e1 e2 ↔ gpo G e1 e2).
Proof. intros Hr. rewrite /gpo !(rows_rel_is_Some π G G' _ Hr). done. Qed.

(** Write footprints and values are UNTOUCHED. *)
Lemma rows_rel_wrb π G G' e a v :
  rows_rel π G G' → (gwrites_byte G' e a v ↔ gwrites_byte G e a v).
Proof.
  intros Hr. rewrite /gwrites_byte (rows_rel_lbl π G G' e Hr). split.
  - intros (l & base & vs & j & Hl & Hwr & Hv & Ha).
    apply fmap_Some in Hl as (l0 & Hl0 & ->).
    rewrite lbl_ren_wr in Hwr. by exists l0, base, vs, j.
  - intros (l & base & vs & j & Hl & Hwr & Hv & Ha).
    exists (lbl_ren π l), base, vs, j. rewrite Hl /= lbl_ren_wr. done.
Qed.

(** Read footprints and values are untouched; the [ts] entry [t] becomes
    [π t] — the spec's "every read [ts] entry [t] of [G] becomes [π t]". *)
Lemma rows_rel_rdb π G G' e a t v :
  rows_rel π G G' → greads_byte G e a t v → greads_byte G' e a (π t) v.
Proof.
  intros Hr (l & base & ts & vs & j & Hl & Hrd & Ht & Hv & Ha).
  exists (lbl_ren π l), base, (π <$> ts), vs, j.
  rewrite (rows_rel_lbl π G G' e Hr) Hl /= (lbl_ren_rd π l base ts vs Hrd)
          list_lookup_fmap Ht /=. done.
Qed.

(** The measure's enumeration is LITERALLY the same list. *)
Lemma rows_rel_gevs π G G' : rows_rel π G G' → gevs' G' = gevs' G.
Proof.
  intros Hr. rewrite /gevs' (rows_rel_nharts π G G' Hr).
  f_equal. apply list_fmap_ext. intros i j _.
  by rewrite (rows_rel_nrow π G G' j Hr).
Qed.

Lemma rows_rel_gpairs π G G' : rows_rel π G G' → gpairs G' = gpairs G.
Proof. intros Hr. by rewrite /gpairs (rows_rel_gevs π G G' Hr). Qed.

(** ** 3.3 Composition *)

Lemma rows_rel_refl G : rows_rel (λ t, t) G G.
Proof. split_and!; [done|by rewrite prog_ren_id|done]. Qed.

Lemma rows_rel_trans π1 π2 π G1 G2 G3 :
  rows_rel π1 G1 G2 → rows_rel π2 G2 G3 → (∀ t, π t = π2 (π1 t)) →
  rows_rel π G1 G3.
Proof.
  intros (Hi1 & Hp1 & Hz1) (Hi2 & Hp2 & Hz2) Hpi. split_and!.
  - by rewrite Hi2 Hi1.
  - rewrite Hp2 Hp1. by apply prog_ren_comp.
  - by rewrite Hpi Hz1 Hz2.
Qed.

(** ** 3.4 [wperm]: the write MESSAGES are preserved under the renaming

    [π] is injective, the number of writes is unchanged, and the write that
    sat at index [t] of [G] sits at index [π t] of [G'] — as the SAME EVENT,
    hence (with [rows_rel]) with the same base, values, author hart and
    class.  §3.5 turns this into the bijection statement. *)

Definition wperm (π : nat → nat) (G G' : gexec) : Prop :=
  (∀ t1 t2, π t1 = π t2 → t1 = t2) ∧
  (∀ t, gwrite_at G' (π t) = gwrite_at G t) ∧
  length (gwrites G') = length (gwrites G).

Lemma wperm_refl G : wperm (λ t, t) G G.
Proof. by split_and!. Qed.

Lemma wperm_trans π1 π2 π G1 G2 G3 :
  wperm π1 G1 G2 → wperm π2 G2 G3 → (∀ t, π t = π2 (π1 t)) →
  wperm π G1 G3.
Proof.
  intros (Hi1 & Hw1 & Hl1) (Hi2 & Hw2 & Hl2) Hpi. split_and!.
  - intros t1 t2 Heq. rewrite !Hpi in Heq. by apply Hi1, Hi2.
  - intros t. by rewrite Hpi Hw2 Hw1.
  - by rewrite Hl2 Hl1.
Qed.

(** ** 3.5 The bijection statement, derived *)

Lemma wperm_gwix π G G' w :
  NoDup (gx_gmo G') → wperm π G G' → w ∈ gwrites G → gwix G' w = π (gwix G w).
Proof.
  intros Hnd (_ & Hw & _) Hin.
  assert (Hat : gwrite_at G' (π (gwix G w)) = Some w).
  { rewrite Hw. by apply gwrite_at_gwix. }
  by destruct (gwrite_at_inv G' _ w Hnd Hat) as (_ & ->).
Qed.

Lemma wperm_range π G G' t :
  NoDup (gx_gmo G') → wperm π G G' →
  (0 < t)%nat → (t ≤ length (gwrites G))%nat →
  (0 < π t)%nat ∧ (π t ≤ length (gwrites G))%nat.
Proof.
  intros Hnd (Hinj & Hw & Hlen) Ht Hle.
  destruct t as [|i]; [lia|].
  assert (Hi : (i < length (gwrites G))%nat) by lia.
  apply lookup_lt_is_Some_2 in Hi as [x Hx].
  assert (Hat : gwrite_at G (S i) = Some x) by exact Hx.
  rewrite -Hw in Hat.
  destruct (π (S i)) as [|j] eqn:Hpi; [done|].
  split; [lia|]. simpl in Hat. apply lookup_lt_Some in Hat. lia.
Qed.

(** SURJECTIVITY, by pigeonhole: an injective self-map of [{1..N}] is onto. *)
Lemma wperm_surj π G G' t' :
  NoDup (gx_gmo G') → wperm π G G' →
  (0 < t')%nat → (t' ≤ length (gwrites G))%nat →
  ∃ t, (0 < t)%nat ∧ (t ≤ length (gwrites G))%nat ∧ π t = t'.
Proof.
  intros Hnd Hwp Ht' Hle'. pose proof Hwp as (Hinj & _ & _).
  set (N := length (gwrites G)).
  assert (Hsub : (π <$> seq 1%nat N) ⊆+ seq 1%nat N).
  { apply NoDup_submseteq.
    - apply NoDup_fmap_2_strong; [|apply NoDup_seq]. intros x y _ _. apply Hinj.
    - intros x Hx. apply elem_of_list_fmap in Hx as (t & -> & Ht).
      apply elem_of_seq in Ht. apply elem_of_seq.
      destruct (wperm_range π G G' t Hnd Hwp ltac:(lia) ltac:(rewrite /N; lia)).
      lia. }
  assert (Hperm : (π <$> seq 1%nat N) ≡ₚ seq 1%nat N).
  { apply submseteq_length_Permutation; [done|].
    rewrite length_fmap length_seq. lia. }
  assert (Hin : t' ∈ (π <$> seq 1%nat N)).
  { rewrite Hperm. apply elem_of_seq. lia. }
  apply elem_of_list_fmap in Hin as (t & Heq & Ht).
  apply elem_of_seq in Ht. exists t. split_and!; [lia|rewrite /N; lia|done].
Qed.

(* ====================================================================== *)
(** * 4. THE MOVES' CORRESPONDENCES

    A [gswap] (one of the pair a non-write) renames nothing: [π] is the
    identity, the programs are untouched and [gwrites] is EQUAL AS A LIST.
    A [gswapw] renames by the adjacent transposition [tswap (gwix G x)]. *)

Lemma rows_rel_gswap G n : rows_rel (λ t, t) G (gswap G n).
Proof. apply (rows_rel_refl G). Qed.

Lemma wperm_gswap_hi G n x r :
  gx_gmo G !! n = Some x → gx_gmo G !! S n = Some r → gis_w G r = false →
  wperm (λ t, t) G (gswap G n).
Proof.
  intros Hx Hr Hnw. split_and!; [done| |].
  - intros t. by rewrite (gswap_gwrite_at G n x r t Hx Hr Hnw).
  - by rewrite (gswap_gwrites G n x r Hx Hr Hnw).
Qed.

Lemma wperm_gswap_lo G n x e :
  gx_gmo G !! n = Some x → gx_gmo G !! S n = Some e → gis_w G x = false →
  wperm (λ t, t) G (gswap G n).
Proof.
  intros Hx He Hnw. split_and!; [done| |].
  - intros t. by rewrite (gswap_gwrite_at_lo G n x e t Hx He Hnw).
  - by rewrite (gswap_gwrites_lo G n x e Hx He Hnw).
Qed.

Lemma rows_rel_gswapw G n k1 : (0 < k1)%nat → rows_rel (tswap k1) G (gswapw G n k1).
Proof.
  intros Hk. split_and!; [done| |by apply tswap_zero].
  rewrite /gswapw /=. apply list_fmap_ext. intros i r _.
  apply list_fmap_ext. intros j l _. by rewrite lbl_ren_tswap.
Qed.

Lemma wperm_gswapw G n x e :
  NoDup (gx_gmo G) →
  gx_gmo G !! n = Some x → gx_gmo G !! S n = Some e →
  gis_w G x = true → gis_w G e = true →
  wperm (tswap (gwix G x)) G (gswapw G n (gwix G x)).
Proof.
  intros Hnd Hx He Hwx Hwe.
  destruct (gswapw_writes_kit G n (gwix G x) x e Hnd Hx He Hwx Hwe)
    as (m & Hm & HSm & Hkx & Hke & Hgws).
  rewrite Hkx in Hgws. rewrite Hkx. split_and!.
  - apply tswap_inj.
  - intros t. by rewrite (gswapw_gwrite_at G n x e m Hm HSm Hgws) tswap_invol.
  - rewrite Hgws. by eapply lswap_length.
Qed.

(* ====================================================================== *)
(** * 5. THE KILL INTERFACE — B2e's three obligations

    [gd_equiv GD GD'] is the orbit the normalization moves in: same rows and
    same write messages modulo a write-index renaming, same dep fragment,
    still consistent.  See the file header for why the kills quantify over
    it rather than over [GD] alone. *)

Definition gd_equiv (GD GD' : gdexec) : Prop :=
  ∃ π, rows_rel π (gd_g GD) (gd_g GD') ∧
       wperm π (gd_g GD) (gd_g GD') ∧
       gd_deps GD' = gd_deps GD ∧
       rvwmo_minus_deps_consistent GD'.

Lemma gd_equiv_refl GD : rvwmo_minus_deps_consistent GD → gd_equiv GD GD.
Proof.
  intros Hc. exists (λ t, t).
  split_and!; [apply rows_rel_refl|apply wperm_refl|done|done].
Qed.

Lemma gd_equiv_trans GD1 GD2 GD3 :
  gd_equiv GD1 GD2 → gd_equiv GD2 GD3 → gd_equiv GD1 GD3.
Proof.
  intros (π1 & Hr1 & Hw1 & Hd1 & _) (π2 & Hr2 & Hw2 & Hd2 & Hc2).
  exists (λ t, π2 (π1 t)). split_and!.
  - by eapply rows_rel_trans.
  - by eapply wperm_trans.
  - by rewrite Hd2 Hd1.
  - done.
Qed.

(** K1: the PO-MINIMAL WITNESS is a READ, and its CROSS-HART rf-source sits
    gmo-strictly inside the descent interval [(w, e)].  (S6's
    reader-of-the-early-write shape, entered from the witness side.) *)
Definition kill_K1 (GD : gdexec) : Prop :=
  ∀ GD', gd_equiv GD GD' →
  ∀ w e a t v w0,
    gviol (gd_g GD') e w →
    (∀ e' w', gviol (gd_g GD') e' w' → ¬ gmo_lt (gd_g GD') w' w) →
    (∀ e', gviol (gd_g GD') e' w → ¬ (e'.2 < e.2)%nat) →
    gis_w (gd_g GD') e = false →
    greads_byte (gd_g GD') e a t v →
    gwrite_at (gd_g GD') t = Some w0 →
    w0.1 ≠ e.1 →
    gmo_lt (gd_g GD') w w0 → gmo_lt (gd_g GD') w0 e →
    False.

(** K2: the PO-MINIMAL WITNESS is a WRITE, and an event [z] sitting
    gmo-strictly inside the interval reads one of [e]'s bytes at an OLDER
    write index (the MP-stale-reader shape; B2c's co-maximality condition). *)
Definition kill_K2 (GD : gdexec) : Prop :=
  ∀ GD', gd_equiv GD GD' →
  ∀ w e z a t v v',
    gviol (gd_g GD') e w →
    (∀ e' w', gviol (gd_g GD') e' w' → ¬ gmo_lt (gd_g GD') w' w) →
    (∀ e', gviol (gd_g GD') e' w → ¬ (e'.2 < e.2)%nat) →
    gis_w (gd_g GD') e = true →
    gmo_lt (gd_g GD') w z → gmo_lt (gd_g GD') z e →
    greads_byte (gd_g GD') z a t v →
    gwrites_byte (gd_g GD') e a v' →
    (t < gwix (gd_g GD') e)%nat →
    False.

(** K3: the PO-MINIMAL WITNESS is a WRITE, and a CROSS-HART SAME-BYTE write
    sits gmo-strictly inside the interval — the kit's excluded (W,W) case,
    a write-write race interleaved with an early-store window. *)
Definition kill_K3 (GD : gdexec) : Prop :=
  ∀ GD', gd_equiv GD GD' →
  ∀ w e z a v v',
    gviol (gd_g GD') e w →
    (∀ e' w', gviol (gd_g GD') e' w' → ¬ gmo_lt (gd_g GD') w' w) →
    (∀ e', gviol (gd_g GD') e' w → ¬ (e'.2 < e.2)%nat) →
    gis_w (gd_g GD') e = true →
    gis_w (gd_g GD') z = true → z.1 ≠ e.1 →
    gmo_lt (gd_g GD') w z → gmo_lt (gd_g GD') z e →
    gwrites_byte (gd_g GD') z a v → gwrites_byte (gd_g GD') e a v' →
    False.

(** ** 5.1 THE KILLS ARE REAL OBLIGATIONS — the LB non-collapse check

    [kill_K1] is not vacuously true: the non-collapse witness REFUTES it.
    In [lbg] the gmo-minimal violating write is hart 0's store [(0,1)] (gmo
    position 0), its po-minimal — indeed only — witness is hart 0's load
    [(0,0)], and the event the load must descend past is hart 1's store
    [(1,1)], which is EXACTLY the load's own cross-hart rf-source.  So the
    descent is stuck at K1 — as it must be: LB is a genuine RVWMO⁻ behavior
    outside sRVWMO, and an unconditionally successful normalization would
    collapse the two models against our own witness.  The induction's
    success for the xv6 image IS the kernel-level exhaustiveness claim, and
    this is where it is paid for. *)

Lemma lbgd_kill_K1_false : ¬ kill_K1 lbgd.
Proof.
  intros HK.
  apply (HK lbgd (gd_equiv_refl lbgd lb_graph_deps_consistent)
            (0%nat, 1%nat) (0%nat, 0%nat) 0%Z 2%nat WeakLitmus.b1
            (1%nat, 1%nat)).
  - (* the violation *)
    split_and!.
    + split_and!; [done|simpl; lia|by eexists|by eexists].
    + eexists. split; reflexivity.
    + eexists. split; reflexivity.
    + split_and!; [rewrite !elem_of_cons; auto|rewrite !elem_of_cons; auto
                  |vm_compute; lia].
  - (* [(0,1)] is gmo-minimal: it sits at gmo position 0 *)
    intros e' w' _ (_ & _ & Hlt). revert Hlt. vm_compute. lia.
  - (* [(0,0)] is po-minimal: it sits at po position 0 *)
    intros e' _ Hlt. simpl in Hlt. lia.
  - (* the witness is a read *)
    reflexivity.
  - (* it reads byte 0 at write index 2 *)
    exists (LLoad false 0 [2%nat] [WeakLitmus.b1]), 0%Z, [2%nat],
           [WeakLitmus.b1], 0%nat. split_and!; reflexivity.
  - (* write index 2 is hart 1's store *)
    by vm_compute.
  - (* which is CROSS-HART *)
    by simpl.
  - (* and sits gmo-above the violating write ... *)
    split_and!; [rewrite !elem_of_cons; auto|rewrite !elem_of_cons; auto
                |vm_compute; lia].
  - (* ... and gmo-below the witness *)
    split_and!; [rewrite !elem_of_cons; auto|rewrite !elem_of_cons; auto
                |vm_compute; lia].
Qed.

(* ====================================================================== *)
(** * 6. THE VACUITY LEMMA — the descent's engine

    Every side condition of the exchange kit that the descent has to
    discharge says "the passed-over event [z] is not same-hart-po-before the
    descending witness [e]".  It is VACUOUS under the po-minimal-witness
    discipline: such a [z] is po-before [w] too (po is transitive along the
    hart's row), it is gmo-above [w] (it sits in the interval), and it is a
    memory event — so it is ITSELF a witness of [w], po-EARLIER than [e]. *)

Lemma po_min_no_blocker (G : gexec) (w e z : geid) :
  gviol G e w →
  (∀ e', gviol G e' w → ¬ (e'.2 < e.2)%nat) →
  gmem G z → gmo_lt G w z → z.1 = e.1 → (z.2 < e.2)%nat → False.
Proof.
  intros Hv Hpmin Hz Hmo Hag Hlt.
  pose proof Hv as (Hpo & _ & Hw & _).
  destruct Hpo as (Hag' & Hlt' & _ & Hsw).
  assert (Hsz : is_Some (gx_lbl G z)).
  { destruct Hz as (l & Hl & _). by exists l. }
  apply (Hpmin z); [|exact Hlt].
  split; [|split; [exact Hz|split; [exact Hw|exact Hmo]]].
  split; [by rewrite Hag Hag'|]. split; [lia|]. split; [exact Hsz|exact Hsw].
Qed.

(** The two shapes the kit asks for.  Note [gmem G z] is free in the descent:
    [z] sits at a gmo position, and [gwf] puts exactly the memory events
    there. *)

Lemma po_min_no_gppo (G : gexec) (w e z : geid) :
  gviol G e w →
  (∀ e', gviol G e' w → ¬ (e'.2 < e.2)%nat) →
  gmem G z → gmo_lt G w z → ¬ gppo G z e.
Proof.
  intros Hv Hpmin Hz Hmo Hppo.
  destruct (gppo_po_lt G z e Hppo) as [Hag Hlt].
  by eapply po_min_no_blocker.
Qed.

Lemma po_min_no_gpo (G : gexec) (w e z : geid) :
  gviol G e w →
  (∀ e', gviol G e' w → ¬ (e'.2 < e.2)%nat) →
  gmem G z → gmo_lt G w z → ¬ gpo G z e.
Proof.
  intros Hv Hpmin Hz Hmo (Hag & Hlt & _ & _).
  by eapply po_min_no_blocker.
Qed.

(** A dep edge INTO the descending witness is refused the same way: its
    source is a po-earlier same-hart READ ([gdeps_wf]), hence a witness. *)
Lemma po_min_no_dep (GD : gdexec) (w e z : geid) :
  gdeps_wf (gd_g GD) (gd_deps GD) →
  gviol (gd_g GD) e w →
  (∀ e', gviol (gd_g GD) e' w → ¬ (e'.2 < e.2)%nat) →
  gmem (gd_g GD) z → gmo_lt (gd_g GD) w z → (z, e) ∉ gd_deps GD.
Proof.
  intros Hdwf Hv Hpmin Hz Hmo Hdep.
  destruct (Hdwf (z, e) Hdep) as (Hag & Hlt & _ & _). simpl in Hag, Hlt.
  by eapply po_min_no_blocker.
Qed.

(* ====================================================================== *)
(** * 7. ONE DESCENT STEP, ABSTRACTLY

    The three exchange lemmas produce three different graphs, but the
    bookkeeping their results feed is identical: the measure does not grow,
    the violation [(e, w)] survives, [w] stays the gmo-minimal violating
    write and [e] its po-minimal witness, and [e]'s gmo position drops by
    exactly one.  This section proves that ONCE, off the two facts every
    move supplies — a [rows_rel] and "the order is [gswap]'s". *)

Lemma gpos_gmo_eq G1 G2 e : gx_gmo G1 = gx_gmo G2 → gpos G1 e = gpos G2 e.
Proof. intros H. by rewrite /gpos H. Qed.

Lemma gmo_lt_gmo_eq G1 G2 e1 e2 :
  gx_gmo G1 = gx_gmo G2 → (gmo_lt G1 e1 e2 ↔ gmo_lt G2 e1 e2).
Proof. intros H. rewrite /gmo_lt /gpos H. done. Qed.

Lemma swap_invariant (π : nat → nat) (G G' : gexec) (w e z : geid) (n : nat) :
  gwf G →
  gx_gmo G !! n = Some z → gx_gmo G !! S n = Some e →
  rows_rel π G G' →
  gx_gmo G' = gx_gmo (gswap G n) →
  (∀ e' w', gviol G' e' w' → gviol G e' w') →
  gviol G e w → (gpos G w < n)%nat →
  (∀ e' w', gviol G e' w' → ¬ gmo_lt G w' w) →
  (∀ e', gviol G e' w → ¬ (e'.2 < e.2)%nat) →
  (nviol G' ≤ nviol G)%nat ∧
  gviol G' e w ∧
  (∀ e' w', gviol G' e' w' → ¬ gmo_lt G' w' w) ∧
  (∀ e', gviol G' e' w → ¬ (e'.2 < e.2)%nat) ∧
  gpos G' e = n ∧ gpos G' w = gpos G w.
Proof.
  intros Hwf Hz He Hrows Hgmo Hmono Hv Hwn Hmin Hpmin.
  pose proof Hwf as (Hnd & _ & _).
  assert (Hzne : w ≠ z).
  { intros Heqz. rewrite Heqz (gpos_of_lookup G n z Hnd Hz) in Hwn. lia. }
  pose proof Hv as (Hpo & Hme & Hww & Hmo).
  assert (Hwin : w ∈ gx_gmo G) by (by destruct Hmo as (? & _ & _)).
  split_and!.
  - apply nviol_le; [by eapply rows_rel_gpairs|exact Hmono].
  - split_and!.
    + by apply (rows_rel_gpo π G G' e w Hrows).
    + by apply (rows_rel_gmem π G G' e Hrows).
    + by apply (rows_rel_glbl_is π G G' w lb_is_w Hrows (lbl_ren_is_w π)).
    + apply (gmo_lt_gmo_eq G' (gswap G n) w e Hgmo).
      apply (gswap_gmo_lt G n z e w e Hnd Hz He Hmo). by intros [-> _].
  - intros e' w' Hv' Hlt'.
    apply (gmo_lt_gmo_eq G' (gswap G n) w' w Hgmo) in Hlt'.
    destruct (gswap_gmo_lt_inv G n z e w' w Hnd Hz He Hlt') as [Hg|[-> ->]];
      [|done].
    by apply (Hmin e' w' (Hmono e' w' Hv')).
  - intros e' Hv'. by apply Hpmin, Hmono.
  - rewrite (gpos_gmo_eq G' (gswap G n) e Hgmo).
    by apply (gswap_gpos_upper G n z e Hnd Hz He).
  - rewrite (gpos_gmo_eq G' (gswap G n) w Hgmo)
            (gswap_gpos G n z e w Hnd Hz He Hwin).
    apply sidx_id; lia.
Qed.

(* ====================================================================== *)
(** * 8. THE DESCENT

    [w] is the gmo-minimal violating write and [e] its po-minimal witness.
    Slide [e] down one gmo slot at a time until it sits directly above [w],
    then swap the pair — which kills the violation ([gswap_resolves] /
    [gswapw_resolves]) while creating none. *)

Section descent.
  Context (GD0 : gdexec).
  Context (HK1 : kill_K1 GD0) (HK2 : kill_K2 GD0) (HK3 : kill_K3 GD0).

  Lemma descent (D : nat) (GD : gdexec) (w e : geid) :
    gd_equiv GD0 GD →
    gviol (gd_g GD) e w →
    (∀ e' w', gviol (gd_g GD) e' w' → ¬ gmo_lt (gd_g GD) w' w) →
    (∀ e', gviol (gd_g GD) e' w → ¬ (e'.2 < e.2)%nat) →
    (gpos (gd_g GD) e - gpos (gd_g GD) w ≤ D)%nat →
    ∃ GD', gd_equiv GD0 GD' ∧ (nviol (gd_g GD') < nviol (gd_g GD))%nat.
  Proof.
    revert GD w e. induction D as [|D IH]; intros GD w e Heq Hv Hmin Hpmin Hd.
    { exfalso. destruct Hv as (_ & _ & _ & (_ & _ & Hlt)). lia. }
    pose proof Heq as (π & Hrows0 & Hwp0 & Hdeps0 & Hcons).
    pose proof Hcons as (Hc & Hdwf & Hdgmo).
    pose proof Hc as (Hwf & Hppo & Hlv & Hat).
    pose proof Hwf as (Hnd & Hmemi & Hshape).
    pose proof Hv as (Hpo_ew & Hmem_e & Hlw & Hmo_we).
    destruct Hpo_ew as (Hag_ew & Hlt_ew & Hse & Hsw).
    pose proof Hmo_we as (Hwin & Hein & Hposlt).
    assert (Hwisw : gis_w (gd_g GD) w = true) by (by apply glbl_is_w_gis_w).
    (* [e] sits at [gpos e]; the slot below it holds [z]. *)
    assert (HSn : gx_gmo (gd_g GD) !! gpos (gd_g GD) e = Some e)
      by (by apply gpos_elem_lookup).
    destruct (decide (gpos (gd_g GD) e = S (gpos (gd_g GD) w))) as [Hfin|Hint].
    - (* ------------------------------------------------------------- *)
      (* THE FINAL SWAP: [e] is directly above [w].                     *)
      (* ------------------------------------------------------------- *)
      set (n := gpos (gd_g GD) w).
      assert (Hn : gx_gmo (gd_g GD) !! n = Some w) by (by apply gpos_elem_lookup).
      assert (HSn' : gx_gmo (gd_g GD) !! S n = Some e) by (by rewrite -Hfin).
      (* the two side conditions shared by both sub-cases *)
      assert (Hnppo : ¬ gppo (gd_g GD) w e).
      { intros Hp. destruct (gppo_po_lt _ _ _ Hp) as [_ Hlt]. lia. }
      destruct (gis_w (gd_g GD) e) eqn:Hew.
      + (* [e] a write: the (W,W) move, byte-disjoint by poloc *)
        assert (Hdisj : ∀ a, (∃ v, gwrites_byte (gd_g GD) w a v) →
                             ¬ ∃ v', gwrites_byte (gd_g GD) e a v').
        { intros a (v & Hwv) (v' & Hev).
          assert (Hpl : gppo (gd_g GD) e w).
          { left. split; [by split_and!|]. exists a. split.
            - left. by exists v'.
            - left. by exists v. }
          pose proof (Hppo e w Hpl) as (_ & _ & ?). lia. }
        assert (Hdep : (w, e) ∉ gd_deps GD).
        { intros Hin. destruct (Hdwf (w, e) Hin) as (_ & Hlt & _ & _).
          simpl in Hlt. lia. }
        pose proof (gswapw_ww_deps GD n w e Hcons Hn HSn' Hwisw Hew
                      Hdisj Hnppo Hdep) as Hcons'.
        assert (Hk : (0 < gwix (gd_g GD) w)%nat)
          by (apply gwix_pos; by apply gis_w_gwrites).
        set (G' := gswapw (gd_g GD) n (gwix (gd_g GD) w)).
        exists (GDExec G' (gd_deps GD)). split.
        * exists (λ t, tswap (gwix (gd_g GD) w) (π t)). split_and!.
          { eapply rows_rel_trans;
              [exact Hrows0|exact (rows_rel_gswapw (gd_g GD) n _ Hk)|done]. }
          { eapply wperm_trans;
              [exact Hwp0
              |exact (wperm_gswapw (gd_g GD) n w e Hnd Hn HSn' Hwisw Hew)|done]. }
          { done. }
          { exact Hcons'. }
        * simpl. destruct (gswapw_resolves (gd_g GD) n w e Hwf Hn HSn' Hwisw Hew
                             Hag_ew Hlt_ew) as [_ Hnv].
          eapply (nviol_lt _ _ e w).
          { exact (rows_rel_gpairs _ _ _ (rows_rel_gswapw (gd_g GD) n _ Hk)). }
          { intros e' w' Hv'.
            eapply (gswapw_viol_mono (gd_g GD) n (gwix (gd_g GD) w) w e);
              [exact Hnd|exact Hn|exact HSn'| |exact Hv'].
            intros Hp. destruct Hp as (_ & Hlt & _ & _). lia. }
          { exact Hv. }
          { exact Hnv. }
      + (* [e] a read: the read-down move *)
        assert (Hnrf : ∀ a t v, greads_byte (gd_g GD) e a t v →
                                gwrite_at (gd_g GD) t ≠ Some w).
        { intros a t v Hrd Hsrc.
          pose proof (gread_source_byte (gd_g GD) e a t v w Hlv Hrd Hsrc) as Hwb.
          assert (Hpl : gppo (gd_g GD) e w).
          { left. split; [by split_and!|]. exists a. split.
            - right. by exists t, v.
            - left. by exists v. }
          pose proof (Hppo e w Hpl) as (_ & _ & ?). lia. }
        pose proof (gswap_read_down_deps GD n w e Hcons Hn HSn' Hew
                      Hnrf Hnppo) as Hcons'.
        set (G' := gswap (gd_g GD) n).
        exists (GDExec G' (gd_deps GD)). split.
        * exists π. split_and!.
          { eapply rows_rel_trans; [exact Hrows0|apply rows_rel_gswap|done]. }
          { eapply wperm_trans;
              [exact Hwp0
              |exact (wperm_gswap_hi (gd_g GD) n w e Hn HSn' Hew)|done]. }
          { done. }
          { exact Hcons'. }
        * simpl. destruct (gswap_resolves (gd_g GD) n w e Hwf Hn HSn' Hew Hwisw
                             Hag_ew Hlt_ew) as [_ Hnv].
          eapply (nviol_lt _ _ e w).
          { by eapply rows_rel_gpairs, rows_rel_gswap. }
          { intros e' w' Hv'.
            exact (gswap_viol_mono (gd_g GD) n w e e' w' Hnd Hn HSn' Hew Hv'). }
          { exact Hv. }
          { exact Hnv. }
    - (* ------------------------------------------------------------- *)
      (* AN INTERIOR SWAP: something sits between [w] and [e].          *)
      (* ------------------------------------------------------------- *)
      assert (Hgap : (S (gpos (gd_g GD) w) < gpos (gd_g GD) e)%nat) by lia.
      set (n := (gpos (gd_g GD) e - 1)%nat).
      assert (HSn' : gx_gmo (gd_g GD) !! S n = Some e).
      { replace (S n) with (gpos (gd_g GD) e) by (rewrite /n; lia). exact HSn. }
      assert (Hnlt : (n < length (gx_gmo (gd_g GD)))%nat).
      { rewrite /n. pose proof (gpos_lt_len (gd_g GD) e Hein). lia. }
      apply lookup_lt_is_Some_2 in Hnlt as [z Hz].
      assert (Hzin : z ∈ gx_gmo (gd_g GD)) by (by eapply elem_of_list_lookup_2).
      assert (Hzpos : gpos (gd_g GD) z = n) by (by apply gpos_of_lookup).
      assert (Hzmem : gmem (gd_g GD) z) by (by eapply gwf_gmo_mem).
      assert (Hwn : (gpos (gd_g GD) w < n)%nat) by (rewrite /n; lia).
      assert (Hmo_wz : gmo_lt (gd_g GD) w z) by (split_and!; [done|done|lia]).
      assert (Hmo_ze : gmo_lt (gd_g GD) z e) by (split_and!; [done|done|lia]).
      assert (Hzs : is_Some (gx_lbl (gd_g GD) z))
        by (destruct Hzmem as (l & Hl & _); by exists l).
      assert (Hzne_e : z ≠ e).
      { intros Heqze. rewrite Heqze in Hmo_ze. by eapply gmo_lt_irrefl. }
      (* the vacuous side conditions *)
      assert (Hnppo : ¬ gppo (gd_g GD) z e)
        by (exact (po_min_no_gppo (gd_g GD) w e z Hv Hpmin Hzmem Hmo_wz)).
      assert (Hnpo : ¬ gpo (gd_g GD) z e)
        by (exact (po_min_no_gpo (gd_g GD) w e z Hv Hpmin Hzmem Hmo_wz)).
      assert (Hdep : (z, e) ∉ gd_deps GD)
        by (exact (po_min_no_dep GD w e z Hdwf Hv Hpmin Hzmem Hmo_wz)).
      (* the swap: three cases *)
      assert (Hstep : ∃ (π' : nat → nat) (G' : gexec),
                rows_rel π' (gd_g GD) G' ∧ wperm π' (gd_g GD) G' ∧
                gx_gmo G' = gx_gmo (gswap (gd_g GD) n) ∧
                rvwmo_minus_deps_consistent (GDExec G' (gd_deps GD)) ∧
                (∀ e' w', gviol G' e' w' → gviol (gd_g GD) e' w')).
      { destruct (gis_w (gd_g GD) e) eqn:Hew.
        - (* [e] a WRITE *)
          destruct (gis_w (gd_g GD) z) eqn:Hzw.
          + (* (W,W): byte-disjoint or K3 *)
            assert (Hkz : (0 < gwix (gd_g GD) z)%nat)
              by (apply gwix_pos, (gis_w_gwrites (gd_g GD) z Hwf Hzs Hzw)).
            assert (Hdisj : ∀ a, (∃ v, gwrites_byte (gd_g GD) z a v) →
                                 ¬ ∃ v', gwrites_byte (gd_g GD) e a v').
            { intros a (v & Hzv) (v' & Hev).
              destruct (decide (z.1 = e.1)) as [Hag|Hag].
              - destruct (decide (z.2 < e.2)%nat) as [Hlt|Hge].
                { exact (po_min_no_blocker (gd_g GD) w e z Hv Hpmin Hzmem
                           Hmo_wz Hag Hlt). }
                destruct (decide (z.2 = e.2)) as [Heq2|Hne2].
                { destruct Hzne_e. by apply injective_projections. }
                assert (Hpl : gppo (gd_g GD) e z).
                { left. split.
                  - split_and!; [by rewrite Hag|lia|exact Hse|exact Hzs].
                  - exists a. split; [left; by exists v'|left; by exists v]. }
                pose proof (Hppo e z Hpl) as (_ & _ & ?). lia.
              - exact (HK3 GD Heq w e z a v v' Hv Hmin Hpmin Hew Hzw Hag
                         Hmo_wz Hmo_ze Hzv Hev). }
            exists (tswap (gwix (gd_g GD) z)),
                   (gswapw (gd_g GD) n (gwix (gd_g GD) z)).
            split_and!.
            * exact (rows_rel_gswapw (gd_g GD) n _ Hkz).
            * exact (wperm_gswapw (gd_g GD) n z e Hnd Hz HSn' Hzw Hew).
            * done.
            * exact (gswapw_ww_deps GD n z e Hcons Hz HSn' Hzw Hew Hdisj
                       Hnppo Hdep).
            * intros e' w' Hv'.
              exact (gswapw_viol_mono (gd_g GD) n (gwix (gd_g GD) z) z e e' w'
                       Hnd Hz HSn' Hnpo Hv').
          + (* (R,W): the co-max condition, or K2 *)
            assert (Hcomax : ∀ a t v, greads_byte (gd_g GD) z a t v →
                       (∃ v', gwrites_byte (gd_g GD) e a v') →
                       (gwix (gd_g GD) e ≤ t)%nat).
            { intros a t v Hrd (v' & Hwb).
              destruct (decide (gwix (gd_g GD) e ≤ t)%nat) as [?|Hgt]; [done|].
              exfalso.
              exact (HK2 GD Heq w e z a t v v' Hv Hmin Hpmin Hew Hmo_wz Hmo_ze
                       Hrd Hwb ltac:(lia)). }
            exists (λ t, t), (gswap (gd_g GD) n). split_and!.
            * apply rows_rel_gswap.
            * exact (wperm_gswap_lo (gd_g GD) n z e Hz HSn' Hzw).
            * done.
            * exact (gswap_write_down_deps GD n z e Hcons Hz HSn' Hzw Hew
                       Hnppo Hcomax Hdep).
            * intros e' w' Hv'.
              exact (gswap_viol_mono_rw (gd_g GD) n z e e' w'
                       Hnd Hz HSn' Hnpo Hv').
        - (* [e] a READ: the read-down move; the source block is K1 *)
          assert (Hnrf : ∀ a t v, greads_byte (gd_g GD) e a t v →
                                  gwrite_at (gd_g GD) t ≠ Some z).
          { intros a t v Hrd Hsrc.
            pose proof (gread_source_byte (gd_g GD) e a t v z Hlv Hrd Hsrc)
              as Hwb.
            destruct (decide (z.1 = e.1)) as [Hag|Hag].
            - destruct (decide (z.2 < e.2)%nat) as [Hlt|Hge].
              { exact (po_min_no_blocker (gd_g GD) w e z Hv Hpmin Hzmem
                         Hmo_wz Hag Hlt). }
              destruct (decide (z.2 = e.2)) as [Heq2|Hne2].
              { destruct Hzne_e. by apply injective_projections. }
              assert (Hpl : gppo (gd_g GD) e z).
              { left. split.
                - split_and!; [by rewrite Hag|lia|exact Hse|exact Hzs].
                - exists a. split; [right; by exists t, v|left; by exists v]. }
              pose proof (Hppo e z Hpl) as (_ & _ & ?). lia.
            - exact (HK1 GD Heq w e a t v z Hv Hmin Hpmin Hew Hrd Hsrc Hag
                       Hmo_wz Hmo_ze). }
          exists (λ t, t), (gswap (gd_g GD) n). split_and!.
          * apply rows_rel_gswap.
          * exact (wperm_gswap_hi (gd_g GD) n z e Hz HSn' Hew).
          * done.
          * exact (gswap_read_down_deps GD n z e Hcons Hz HSn' Hew Hnrf Hnppo).
          * intros e' w' Hv'.
            exact (gswap_viol_mono (gd_g GD) n z e e' w' Hnd Hz HSn' Hew Hv'). }
      destruct Hstep as (π' & G' & Hrows' & Hwp' & Hgmo' & Hcons' & Hmono').
      destruct (swap_invariant π' (gd_g GD) G' w e z n Hwf Hz HSn' Hrows'
                  Hgmo' Hmono' Hv Hwn Hmin Hpmin)
        as (Hnle & Hv' & Hmin' & Hpmin' & Hpe' & Hpw').
      assert (Heq' : gd_equiv GD0 (GDExec G' (gd_deps GD))).
      { exists (λ t, π' (π t)). split_and!.
        - by eapply rows_rel_trans.
        - by eapply wperm_trans.
        - done.
        - exact Hcons'. }
      destruct (IH (GDExec G' (gd_deps GD)) w e Heq' Hv' Hmin' Hpmin')
        as (GD'' & Heq'' & Hlt'').
      { simpl. rewrite Hpe' Hpw'. rewrite /n. lia. }
      exists GD''. split; [done|]. simpl in Hlt''. lia.
  Qed.
End descent.

(* ====================================================================== *)
(** * 9. THE NORMALIZATION THEOREM *)

Lemma normalize_aux (GD0 : gdexec) (N : nat) :
  kill_K1 GD0 → kill_K2 GD0 → kill_K3 GD0 →
  ∀ GD, gd_equiv GD0 GD → (nviol (gd_g GD) ≤ N)%nat →
  ∃ GD', gd_equiv GD0 GD' ∧ grule14 (gd_g GD').
Proof.
  intros HK1 HK2 HK3. induction N as [|N IH]; intros GD Heq HN.
  - (* no inversions left *)
    pose proof Heq as (π & _ & _ & _ & ((Hwf & _ & _ & _) & _ & _)).
    exists GD. split; [done|]. apply nviol_zero; [done|lia].
  - pose proof Heq as (π & _ & _ & _ & Hcons).
    pose proof Hcons as ((Hwf & _ & _ & _) & _ & _).
    destruct (decide (nviol (gd_g GD) = 0%nat)) as [H0|H0].
    { exists GD. split; [done|]. by apply nviol_zero. }
    (* pick the gmo-minimal violating write [w] ... *)
    assert (Hne : filter (violp (gd_g GD)) (gpairs (gd_g GD)) ≠ []).
    { intros Hnil. rewrite /nviol Hnil in H0. by apply H0. }
    destruct (list_min_by (λ p : geid * geid, gpos (gd_g GD) p.2) _ Hne)
      as ([e0 w] & Hin & Hmin0).
    apply elem_of_list_filter in Hin as [Hv0 Hin0].
    assert (Hmin : ∀ e' w', gviol (gd_g GD) e' w' → ¬ gmo_lt (gd_g GD) w' w).
    { intros e' w' Hv' (_ & _ & Hlt).
      assert (Hin' : (e', w') ∈ filter (violp (gd_g GD)) (gpairs (gd_g GD))).
      { apply elem_of_list_filter. split; [exact Hv'|].
        by apply gviol_gpairs. }
      pose proof (Hmin0 (e', w') Hin') as Hle. simpl in Hle, Hlt. lia. }
    (* ... and its po-minimal witness [e]. *)
    assert (Hne2 : filter (λ e', gviol (gd_g GD) e' w) (gevs' (gd_g GD)) ≠ []).
    { intros Hnil.
      assert (He0 : e0 ∈ filter (λ e', gviol (gd_g GD) e' w) (gevs' (gd_g GD))).
      { apply elem_of_list_filter. split; [exact Hv0|].
        destruct Hv0 as (_ & (l & Hl & _) & _ & _). apply elem_of_gevs'.
        by exists l. }
      rewrite Hnil in He0. by apply elem_of_nil in He0. }
    destruct (list_min_by (λ e' : geid, e'.2) _ Hne2) as (e & Hin2 & Hmin2).
    apply elem_of_list_filter in Hin2 as [Hv Hin2].
    assert (Hpmin : ∀ e', gviol (gd_g GD) e' w → ¬ (e'.2 < e.2)%nat).
    { intros e' Hv' Hlt.
      assert (Hin' : e' ∈ filter (λ e'', gviol (gd_g GD) e'' w) (gevs' (gd_g GD))).
      { apply elem_of_list_filter. split; [exact Hv'|].
        destruct Hv' as (_ & (l & Hl & _) & _ & _). apply elem_of_gevs'.
        by exists l. }
      pose proof (Hmin2 e' Hin') as Hle. simpl in Hle. lia. }
    destruct (descent GD0 HK1 HK2 HK3
                (gpos (gd_g GD) e - gpos (gd_g GD) w)%nat GD w e
                Heq Hv Hmin Hpmin ltac:(lia)) as (GD1 & Heq1 & Hlt1).
    apply (IH GD1 Heq1). lia.
Qed.

(** THE DELIVERABLE.  Every RVWMO⁻(+deps)-consistent graph whose three
    residual kill configurations are refuted normalizes to a [grule14] graph
    with the SAME OBSERVABLES: same image, same rows (values, bases,
    classes and ordering bits all equal), same dep fragment, and the write
    messages preserved under a write-index permutation [π] that fixes the
    era-initial image. *)
Theorem normalize (GD : gdexec) :
  rvwmo_minus_deps_consistent GD →
  kill_K1 GD → kill_K2 GD → kill_K3 GD →
  ∃ (GD' : gdexec) (π : nat → nat),
    rvwmo_minus_deps_consistent GD' ∧
    grule14 (gd_g GD') ∧
    rows_rel π (gd_g GD) (gd_g GD') ∧
    gd_deps GD' = gd_deps GD ∧
    wperm π (gd_g GD) (gd_g GD').
Proof.
  intros Hcons HK1 HK2 HK3.
  destruct (normalize_aux GD (nviol (gd_g GD)) HK1 HK2 HK3 GD
              (gd_equiv_refl GD Hcons) (Nat.le_refl _)) as (GD' & Heq & Hr14).
  destruct Heq as (π & Hrows & Hwp & Hdeps & Hcons').
  by exists GD', π.
Qed.
