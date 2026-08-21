(** * WeakRvwmoXchg.v — THE EXCHANGE KIT, lemma 1: the READ-DOWN SWAP (B2a)

    Design: [claude-notes/design/weak-memory-route-b.md] §3b (the
    stress-test findings block).  The model is [WeakRvwmoGraph]'s RVWMO⁻.

    THE POINT.  Route B normalizes an RVWMO⁻-consistent graph towards
    [grule14] by ADJACENT EXCHANGES in the global memory order.  The
    stress-test finding is that the read-side moves are nearly free: a
    violation [(e, w)] whose early event [e] is a READ is resolved by
    sliding [e] gmo-EARLIER, and sliding a read down past its gmo
    predecessor breaks nothing — no write position moves (so every
    [gwix]/[gwrite_at] fact and every OTHER event's visible-write set is
    untouched), the moved read's own visible set only SHRINKS (which
    weakens co-maximality and preserves the source, as long as the
    passed-over event is not the read's own rf-source), and the only ppo⁻
    pair whose order flips is the swapped pair itself.

    THIS FILE delivers exactly that step:

      - [gswap G n] — the graph with gmo positions [n] and [S n]
        exchanged (§2), on top of a generic list-swap kit (§1) whose
        whole content is one index INVOLUTION [sidx]: [lswap l n !! i =
        l !! sidx n i], from which membership, [NoDup], [gpos] and
        [gmo_lt] transport are one-liners;
      - [gswap_read_down] (§3) — the main lemma: RVWMO⁻-consistency is
        preserved when the UPPER of the two swapped events is not a
        write, is not reading the lower one, and is not ppo⁻-ordered
        after it;
      - [gswap_read_down_deps] (§4) — the [gdexec] corollary; the "no dep
        edge from [x] to [r]" side condition is FREE from [gdeps_wf]
        (dep targets are writes, [r] is not one);
      - [gviol] + [gswap_viol_mono] / [gswap_resolves] (§5) — the rule-14
        bookkeeping the B2 induction's measure will consume: a read-down
        swap never CREATES a violation, and it RESOLVES the violation of
        the pair it exchanges.

    NOT IN SCOPE (deliberately, per the slice's spec): the fused-RMW read
    ([r] both reads and writes — excluded by the [gis_w G r = false]
    hypothesis) and the write-up move (B2b).

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakAxiomatic WeakRvwmoGraph.

(* ====================================================================== *)
(** * 1. A GENERIC ADJACENT-SWAP KIT FOR LISTS

    Nothing here mentions the memory model.  The kit is organised around
    the INDEX INVOLUTION [sidx n], which exchanges [n] and [S n] and
    fixes everything else: the swapped list's lookup at [i] is the
    original's lookup at [sidx n i], and every structural fact
    (membership, [NoDup], and — downstream — positions and order)
    follows from that single equation plus [sidx]'s involutivity,
    injectivity and monotonicity-off-the-swapped-pair. *)

(** ** 1.1 The index involution *)

Definition sidx (n i : nat) : nat :=
  if bool_decide (i = n) then S n
  else if bool_decide (i = S n) then n else i.

Lemma sidx_n n : sidx n n = S n.
Proof. rewrite /sidx. repeat case_bool_decide; lia. Qed.

Lemma sidx_Sn n : sidx n (S n) = n.
Proof. rewrite /sidx. repeat case_bool_decide; lia. Qed.

Lemma sidx_id n i : i ≠ n → i ≠ S n → sidx n i = i.
Proof. intros H1 H2. rewrite /sidx. repeat case_bool_decide; lia. Qed.

Lemma sidx_invol n i : sidx n (sidx n i) = i.
Proof. rewrite /sidx. repeat case_bool_decide; lia. Qed.

Lemma sidx_inj n i j : sidx n i = sidx n j → i = j.
Proof. intros Heq. by rewrite -(sidx_invol n i) -(sidx_invol n j) Heq. Qed.

(** The order behaviour: [sidx] is monotone EXCEPT on the swapped pair. *)
Lemma sidx_mono n p1 p2 :
  (p1 < p2)%nat → ¬ (p1 = n ∧ p2 = S n) → (sidx n p1 < sidx n p2)%nat.
Proof.
  intros Hlt Hne. rewrite /sidx. repeat case_bool_decide; lia.
Qed.

Lemma sidx_mono_inv n p1 p2 :
  (sidx n p1 < sidx n p2)%nat → (p1 < p2)%nat ∨ (p1 = S n ∧ p2 = n).
Proof. rewrite /sidx. repeat case_bool_decide; lia. Qed.

(** ** 1.2 [lswap]: exchange the elements at positions [n] and [S n] *)

Definition lswap {A} (l : list A) (n : nat) : list A :=
  match l !! n, l !! S n with
  | Some a, Some b => take n l ++ b :: a :: drop (S (S n)) l
  | _, _ => l
  end.

Lemma lswap_split {A} (l : list A) n a b :
  l !! n = Some a → l !! S n = Some b →
  lswap l n = take n l ++ b :: a :: drop (S (S n)) l.
Proof. intros Hn HSn. by rewrite /lswap Hn HSn. Qed.

(** The companion decomposition of the ORIGINAL list, with the same
    take/drop skeleton — the shape every [filter] argument needs. *)
Lemma lsplit2 {A} (l : list A) n a b :
  l !! n = Some a → l !! S n = Some b →
  l = take n l ++ a :: b :: drop (S (S n)) l.
Proof.
  intros Hn HSn.
  rewrite -{1}(take_drop_middle l n a Hn).
  by rewrite (drop_S l b (S n) HSn).
Qed.

(** THE EQUATION the whole kit rests on. *)
Lemma lswap_lookup {A} (l : list A) n a b i :
  l !! n = Some a → l !! S n = Some b →
  lswap l n !! i = l !! sidx n i.
Proof.
  intros Hn HSn.
  assert (Hlen : (S n < length l)%nat) by (by eapply lookup_lt_Some).
  assert (Htk : length (take n l) = n) by (rewrite length_take; lia).
  rewrite (lswap_split l n a b Hn HSn).
  destruct (decide (i < n)%nat) as [Hi|Hi].
  - assert (Hlt : (i < length (take n l))%nat) by lia.
    assert (H1 : i ≠ n) by lia. assert (H2 : i ≠ S n) by lia.
    by rewrite (lookup_app_l _ _ _ Hlt) (lookup_take _ _ _ Hi) (sidx_id n i H1 H2).
  - destruct (decide (i = n)) as [->|Hne1].
    { assert (Hge : (length (take n l) ≤ n)%nat) by lia.
      rewrite (lookup_app_r _ _ _ Hge) Htk Nat.sub_diag /= sidx_n. done. }
    destruct (decide (i = S n)) as [->|Hne2].
    { assert (Hge : (length (take n l) ≤ S n)%nat) by lia.
      rewrite (lookup_app_r _ _ _ Hge) Htk.
      replace (S n - n)%nat with 1%nat by lia.
      rewrite /= sidx_Sn. done. }
    assert (Hgt : (S n < i)%nat) by lia.
    assert (Hge : (length (take n l) ≤ i)%nat) by lia.
    rewrite (lookup_app_r _ _ _ Hge) Htk.
    replace (i - n)%nat with (S (S (i - S (S n))))%nat by lia.
    rewrite /= lookup_drop (sidx_id n i Hne1 Hne2). f_equal. lia.
Qed.

Lemma lswap_elem_of {A} `{EqDecision A} (l : list A) n a b x :
  l !! n = Some a → l !! S n = Some b → (x ∈ lswap l n ↔ x ∈ l).
Proof.
  intros Hn HSn. rewrite !elem_of_list_lookup. split.
  - intros [i Hi]. rewrite (lswap_lookup l n a b i Hn HSn) in Hi.
    by exists (sidx n i).
  - intros [i Hi]. exists (sidx n i).
    by rewrite (lswap_lookup l n a b _ Hn HSn) sidx_invol.
Qed.

Lemma lswap_NoDup {A} (l : list A) n a b :
  l !! n = Some a → l !! S n = Some b → NoDup l → NoDup (lswap l n).
Proof.
  intros Hn HSn Hnd. apply NoDup_alt. intros i j x Hi Hj.
  rewrite (lswap_lookup l n a b i Hn HSn) in Hi.
  rewrite (lswap_lookup l n a b j Hn HSn) in Hj.
  apply (sidx_inj n). by apply (proj1 (NoDup_alt l) Hnd _ _ x).
Qed.

Lemma lswap_length {A} (l : list A) n a b :
  l !! n = Some a → l !! S n = Some b → length (lswap l n) = length l.
Proof.
  intros Hn HSn.
  assert (Hlen : (S n < length l)%nat) by (by eapply lookup_lt_Some).
  rewrite (lswap_split l n a b Hn HSn) length_app /= length_take length_drop. lia.
Qed.

(** THE FILTER FACT.  A swap is invisible to a filter that rejects one of
    the two swapped elements — which is why moving a READ past its gmo
    predecessor leaves [gwrites] EQUAL AS A LIST, not merely as a set. *)
Lemma lswap_filter {A} (P : A → Prop) `{∀ z, Decision (P z)}
    (l : list A) n a b :
  l !! n = Some a → l !! S n = Some b → (¬ P a ∨ ¬ P b) →
  filter P (lswap l n) = filter P l.
Proof.
  intros Hn HSn Hnp.
  assert (Hrhs : filter P l =
                 filter P (take n l) ++ filter P (a :: b :: drop (S (S n)) l)).
  { rewrite -list_basics.filter_app. f_equal. by apply lsplit2. }
  rewrite Hrhs (lswap_split l n a b Hn HSn) list_basics.filter_app !filter_cons.
  destruct Hnp as [Hnp|Hnp]; repeat case_decide; naive_solver.
Qed.

(* ====================================================================== *)
(** * 2. [gswap]: the adjacent exchange as a graph transformation

    Only [gx_gmo] moves.  The image and the per-hart programs are
    untouched, so EVERY label-derived notion is unchanged — definitionally,
    which is what makes §2.1's transport lemmas [reflexivity]. *)

Definition gswap (G : gexec) (n : nat) : gexec :=
  GExec (gx_img G) (gx_prog G) (lswap (gx_gmo G) n).

(** ** 2.1 Everything read off the labels is untouched *)

Lemma gswap_img G n : gx_img (gswap G n) = gx_img G.
Proof. reflexivity. Qed.
Lemma gswap_prog G n : gx_prog (gswap G n) = gx_prog G.
Proof. reflexivity. Qed.
Lemma gswap_gmo G n : gx_gmo (gswap G n) = lswap (gx_gmo G) n.
Proof. reflexivity. Qed.
Lemma gswap_lbl G n : gx_lbl (gswap G n) = gx_lbl G.
Proof. reflexivity. Qed.
Lemma gswap_is_w G n : gis_w (gswap G n) = gis_w G.
Proof. reflexivity. Qed.
Lemma gswap_mem G n : gmem (gswap G n) = gmem G.
Proof. reflexivity. Qed.
Lemma gswap_lbl_is G n : glbl_is (gswap G n) = glbl_is G.
Proof. reflexivity. Qed.
Lemma gswap_wrb G n : gwrites_byte (gswap G n) = gwrites_byte G.
Proof. reflexivity. Qed.
Lemma gswap_rdb G n : greads_byte (gswap G n) = greads_byte G.
Proof. reflexivity. Qed.
Lemma gswap_accesses G n : gaccesses (gswap G n) = gaccesses G.
Proof. reflexivity. Qed.
Lemma gswap_po G n : gpo (gswap G n) = gpo G.
Proof. reflexivity. Qed.
Lemma gswap_ppo G n : gppo (gswap G n) = gppo G.
Proof. reflexivity. Qed.

(** ** 2.2 Membership, [NoDup] and positions *)

Lemma gswap_elem_of G n x r e :
  gx_gmo G !! n = Some x → gx_gmo G !! S n = Some r →
  (e ∈ gx_gmo (gswap G n) ↔ e ∈ gx_gmo G).
Proof. intros Hx Hr. rewrite gswap_gmo. by eapply lswap_elem_of. Qed.

Lemma gswap_nodup G n x r :
  gx_gmo G !! n = Some x → gx_gmo G !! S n = Some r →
  NoDup (gx_gmo G) → NoDup (gx_gmo (gswap G n)).
Proof. intros Hx Hr Hnd. rewrite gswap_gmo. by eapply lswap_NoDup. Qed.

(** The position law: a member's new position is [sidx] of its old one —
    i.e. positions are exchanged on [x] and [r] and fixed elsewhere. *)
Lemma gswap_gpos G n x r e :
  NoDup (gx_gmo G) → gx_gmo G !! n = Some x → gx_gmo G !! S n = Some r →
  e ∈ gx_gmo G → gpos (gswap G n) e = sidx n (gpos G e).
Proof.
  intros Hnd Hx Hr He.
  apply (gpos_of_lookup (gswap G n) _ e); [by eapply gswap_nodup|].
  rewrite gswap_gmo (lswap_lookup _ n x r _ Hx Hr) sidx_invol.
  by apply gpos_elem_lookup.
Qed.

Lemma gswap_gpos_lower G n x r :
  NoDup (gx_gmo G) → gx_gmo G !! n = Some x → gx_gmo G !! S n = Some r →
  gpos (gswap G n) x = S n.
Proof.
  intros Hnd Hx Hr.
  rewrite (gswap_gpos G n x r x Hnd Hx Hr (elem_of_list_lookup_2 _ _ _ Hx)).
  by rewrite (gpos_of_lookup G n x Hnd Hx) sidx_n.
Qed.

Lemma gswap_gpos_upper G n x r :
  NoDup (gx_gmo G) → gx_gmo G !! n = Some x → gx_gmo G !! S n = Some r →
  gpos (gswap G n) r = n.
Proof.
  intros Hnd Hx Hr.
  rewrite (gswap_gpos G n x r r Hnd Hx Hr (elem_of_list_lookup_2 _ _ _ Hr)).
  by rewrite (gpos_of_lookup G (S n) r Hnd Hr) sidx_Sn.
Qed.

(** ** 2.3 [gmo_lt]: every pair keeps its order, except the swapped one *)

Lemma gswap_gmo_lt G n x r e1 e2 :
  NoDup (gx_gmo G) → gx_gmo G !! n = Some x → gx_gmo G !! S n = Some r →
  gmo_lt G e1 e2 → ¬ (e1 = x ∧ e2 = r) → gmo_lt (gswap G n) e1 e2.
Proof.
  intros Hnd Hx Hr (H1 & H2 & Hlt) Hne. split_and!.
  - by apply (gswap_elem_of G n x r e1 Hx Hr).
  - by apply (gswap_elem_of G n x r e2 Hx Hr).
  - rewrite (gswap_gpos G n x r e1 Hnd Hx Hr H1)
            (gswap_gpos G n x r e2 Hnd Hx Hr H2).
    apply sidx_mono; [done|]. intros [Hp1 Hp2]. apply Hne. split.
    + pose proof (gpos_elem_lookup G e1 H1) as Hl1.
      rewrite Hp1 Hx in Hl1. by simplify_eq.
    + pose proof (gpos_elem_lookup G e2 H2) as Hl2.
      rewrite Hp2 Hr in Hl2. by simplify_eq.
Qed.

Lemma gswap_gmo_lt_inv G n x r e1 e2 :
  NoDup (gx_gmo G) → gx_gmo G !! n = Some x → gx_gmo G !! S n = Some r →
  gmo_lt (gswap G n) e1 e2 → gmo_lt G e1 e2 ∨ (e1 = r ∧ e2 = x).
Proof.
  intros Hnd Hx Hr (H1 & H2 & Hlt).
  apply (gswap_elem_of G n x r e1 Hx Hr) in H1.
  apply (gswap_elem_of G n x r e2 Hx Hr) in H2.
  rewrite (gswap_gpos G n x r e1 Hnd Hx Hr H1)
          (gswap_gpos G n x r e2 Hnd Hx Hr H2) in Hlt.
  destruct (sidx_mono_inv _ _ _ Hlt) as [Hp|[Hp1 Hp2]].
  - left. by split_and!.
  - right. split.
    + pose proof (gpos_elem_lookup G e1 H1) as Hl1.
      rewrite Hp1 Hr in Hl1. by simplify_eq.
    + pose proof (gpos_elem_lookup G e2 H2) as Hl2.
      rewrite Hp2 Hx in Hl2. by simplify_eq.
Qed.

(** ** 2.4 The write sub-order is EQUAL when the upper event is no write *)

Lemma gswap_gwrites G n x r :
  gx_gmo G !! n = Some x → gx_gmo G !! S n = Some r → gis_w G r = false →
  gwrites (gswap G n) = gwrites G.
Proof.
  intros Hx Hr Hnw. rewrite /gwrites gswap_is_w gswap_gmo.
  apply (lswap_filter _ _ n x r Hx Hr). right. rewrite Hnw. by intros [].
Qed.

Lemma gswap_gwrite_at G n x r t :
  gx_gmo G !! n = Some x → gx_gmo G !! S n = Some r → gis_w G r = false →
  gwrite_at (gswap G n) t = gwrite_at G t.
Proof.
  intros Hx Hr Hnw. rewrite /gwrite_at (gswap_gwrites G n x r Hx Hr Hnw). done.
Qed.

Lemma gswap_gwix G n x r :
  gx_gmo G !! n = Some x → gx_gmo G !! S n = Some r → gis_w G r = false →
  gwix (gswap G n) = gwix G.
Proof.
  intros Hx Hr Hnw. rewrite /gwix (gswap_gwrites G n x r Hx Hr Hnw). done.
Qed.

(* ====================================================================== *)
(** * 3. THE MAIN LEMMA — the read-down move preserves RVWMO⁻

    [r] sits at gmo position [S n] and [x] at [n]; [r] moves DOWN past
    [x].  The three hypotheses on the pair:

      - [r] is NOT A WRITE.  This is what freezes [gwrites] as a list
        (§2.4), and hence every [gwix]/[gwrite_at] fact of the whole
        graph.  It also excludes the fused-RMW read, deliberately.
      - [x] is not [r]'s rf-SOURCE (no [ts] entry of [r] names [x]).
        Moving [r] below [x] would otherwise strand the source above the
        read.
      - [x] is not ppo⁻-BEFORE [r].  This is the only pair whose gmo
        order flips, so it is the only [gppo_gmo] obligation at risk.
        For a CROSS-HART pair it is free — see
        [WeakRvwmoGraph.gppo_same_hart].

    Note that "[r] is a read" is NOT a hypothesis: it follows from
    [gwf] + membership + [gis_w G r = false] ([gswap_upper_is_read]). *)

(** [r] is a read, for free. *)
Lemma gswap_upper_is_read G r :
  gwf G → r ∈ gx_gmo G → gis_w G r = false → glbl_is G r lb_is_r.
Proof.
  intros Hwf Hin Hnw. destruct (gwf_gmo_mem G r Hwf Hin) as (l & Hl & Hm).
  exists l. split; [done|]. rewrite /gis_w Hl in Hnw.
  rewrite /lb_is_mem Hnw orb_false_r in Hm. done.
Qed.

Theorem gswap_read_down G n x r :
  rvwmo_minus_consistent G →
  gx_gmo G !! n = Some x →
  gx_gmo G !! S n = Some r →
  gis_w G r = false →
  (∀ a t v, greads_byte G r a t v → gwrite_at G t ≠ Some x) →
  ¬ gppo G x r →
  rvwmo_minus_consistent (gswap G n).
Proof.
  intros (Hwf & Hppo & Hlv & Hat) Hx Hr Hnw Hnrf Hnppo.
  pose proof Hwf as (Hnd & Hmem & Hshape).
  split_and!.
  - (* gwf *) split_and!.
    + by eapply gswap_nodup.
    + intros e. rewrite gswap_mem (gswap_elem_of G n x r e Hx Hr). apply Hmem.
    + exact Hshape.
  - (* gppo⁻ ⊆ gmo *)
    intros e1 e2 Hp. rewrite gswap_ppo in Hp.
    apply (gswap_gmo_lt G n x r e1 e2 Hnd Hx Hr (Hppo e1 e2 Hp)).
    intros [-> ->]. exact (Hnppo Hp).
  - (* load value *)
    intros e a t v Hrd. rewrite gswap_rdb in Hrd.
    destruct (Hlv e a t v Hrd) as [Hsrc Hmax]. split.
    + destruct t as [|t]; [by rewrite gswap_img|].
      destruct Hsrc as (w & Hwat & Hwb & Hvis).
      exists w. split_and!.
      * by rewrite (gswap_gwrite_at G n x r _ Hx Hr Hnw).
      * by rewrite gswap_wrb.
      * destruct Hvis as [Hgmo|Hpo]; [left|by right].
        apply (gswap_gmo_lt G n x r w e Hnd Hx Hr Hgmo).
        intros [-> ->]. by apply (Hnrf a (S t) v Hrd).
    + intros w' v' Hwb' Hvis'.
      rewrite gswap_wrb in Hwb'. rewrite (gswap_gwix G n x r Hx Hr Hnw).
      apply (Hmax w' v' Hwb').
      destruct Hvis' as [Hgmo|Hpo]; [|by right].
      destruct (gswap_gmo_lt_inv G n x r w' e Hnd Hx Hr Hgmo)
        as [?|[-> ->]]; [by left|].
      exfalso. rewrite (gwrites_byte_gis_w G r a v' Hwb') in Hnw. done.
  - (* atomicity *)
    intros e a t v Hrd Hw w' v' Hwb.
    rewrite gswap_rdb in Hrd. rewrite gswap_lbl_is in Hw.
    rewrite gswap_wrb in Hwb. rewrite !(gswap_gwix G n x r Hx Hr Hnw).
    by eapply Hat.
Qed.

(** ** 3.1 A NON-VACUITY SMOKE TEST

    The move applies to the non-collapse witness: in [lbg]'s gmo
    [[(0,1); (1,1); (0,0); (1,0)]] the last two events are the two
    (cross-hart) LOADS, so hart 1's load may slide below hart 0's — it
    reads write index 1, which is hart 0's STORE, not the event it passes
    — and the result is still RVWMO⁻-consistent.  Note how the ppo⁻ side
    condition is discharged: cross-hart, via [gppo_same_hart]. *)
Example lbg_swap_consistent : rvwmo_minus_consistent (gswap lbg 2).
Proof.
  eapply (gswap_read_down lbg 2 (0%nat, 0%nat) (1%nat, 0%nat));
    [exact lb_graph_consistent|reflexivity|reflexivity|reflexivity| |].
  - intros a t v (l & base & ts & vs & j & Hl & Hrd & Ht & Hv & Ha).
    rewrite /gx_lbl /= in Hl. simplify_eq/=.
    destruct j as [|j]; simplify_eq/=. by vm_compute.
  - intros Hppo. by apply gppo_same_hart in Hppo.
Qed.

(* ====================================================================== *)
(** * 4. The [gdexec] corollary

    The dep fragment rides through untouched: [gdeps_wf] is label-level,
    and [gdeps_gmo]'s only risk is the flipped pair — which is EXCLUDED
    FOR FREE, because a dep edge targets a WRITE and [r] is not one. *)

Corollary gswap_read_down_deps GD n x r :
  rvwmo_minus_deps_consistent GD →
  gx_gmo (gd_g GD) !! n = Some x →
  gx_gmo (gd_g GD) !! S n = Some r →
  gis_w (gd_g GD) r = false →
  (∀ a t v, greads_byte (gd_g GD) r a t v → gwrite_at (gd_g GD) t ≠ Some x) →
  ¬ gppo (gd_g GD) x r →
  rvwmo_minus_deps_consistent (GDExec (gswap (gd_g GD) n) (gd_deps GD)).
Proof.
  intros ((Hwf & Hppo & Hlv & Hat) & Hdwf & Hdgmo) Hx Hr Hnw Hnrf Hnppo.
  pose proof Hwf as (Hnd & _ & _).
  split_and!.
  - by eapply gswap_read_down.
  - intros rw Hrw. rewrite /= gswap_lbl_is. exact (Hdwf rw Hrw).
  - intros rw Hrw. simpl.
    apply (gswap_gmo_lt (gd_g GD) n x r _ _ Hnd Hx Hr (Hdgmo rw Hrw)).
    intros [_ Heq]. destruct (Hdwf rw Hrw) as (_ & _ & _ & Hw).
    rewrite Heq in Hw. rewrite (glbl_is_w_gis_w _ _ Hw) in Hnw. done.
Qed.

(* ====================================================================== *)
(** * 5. RULE-14 BOOKKEEPING for the B2 induction's measure

    A rule-14 INVERSION of [G] is a pair [(e, w)] with [e] a memory event
    po-before the write [w], but [w] gmo-before [e] — exactly the
    negation of [grule14]'s conclusion, in its positive form (gmo is
    total on its members, so "not gmo-before" is "gmo-after"). *)

Definition gviol (G : gexec) (e w : geid) : Prop :=
  gpo G e w ∧ gmem G e ∧ glbl_is G w lb_is_w ∧ gmo_lt G w e.

Lemma gviol_grule14 G :
  gwf G → (∀ e w, ¬ gviol G e w) → grule14 G.
Proof.
  intros Hwf Hno e w Hpo Hme Hw. pose proof Hwf as (Hnd & _ & _).
  assert (Hew : e ≠ w).
  { intros ->. destruct Hpo as (_ & Hlt & _). lia. }
  assert (Hmw : gmem G w).
  { destruct Hw as (l & Hl & Hlw). exists l. split; [done|].
    by rewrite /lb_is_mem Hlw orb_true_r. }
  destruct (gmo_lt_total G e w Hnd (gwf_mem_gmo G e Hwf Hme)
              (gwf_mem_gmo G w Hwf Hmw) Hew) as [?|Hlt]; [done|].
  by destruct (Hno e w).
Qed.

(** VIOLATIONS ONLY SHRINK: a read-down swap never creates one. *)
Lemma gswap_viol_mono G n x r e w :
  NoDup (gx_gmo G) → gx_gmo G !! n = Some x → gx_gmo G !! S n = Some r →
  gis_w G r = false → gviol (gswap G n) e w → gviol G e w.
Proof.
  intros Hnd Hx Hr Hnw (Hpo & Hme & Hw & Hgmo).
  rewrite gswap_po in Hpo. rewrite gswap_mem in Hme.
  rewrite gswap_lbl_is in Hw.
  split_and!; [done|done|done|].
  destruct (gswap_gmo_lt_inv G n x r w e Hnd Hx Hr Hgmo) as [?|[-> ->]]; [done|].
  exfalso. rewrite (glbl_is_w_gis_w _ _ Hw) in Hnw. done.
Qed.

(** ... AND THE SWAPPED PAIR'S OWN VIOLATION IS RESOLVED, when the lower
    event [x] is a write po-after the read [r]: the pair [(r, x)] is a
    violation of [G] and is not one of [gswap G n].  With
    [gswap_viol_mono] (nothing new appears), the inversion count drops
    strictly. *)
Lemma gswap_resolves G n x r :
  gwf G → gx_gmo G !! n = Some x → gx_gmo G !! S n = Some r →
  gis_w G r = false → gis_w G x = true → r.1 = x.1 → (r.2 < x.2)%nat →
  gviol G r x ∧ ¬ gviol (gswap G n) r x.
Proof.
  intros Hwf Hx Hr Hnw Hwx Hag Hlt.
  pose proof Hwf as (Hnd & _ & _).
  pose proof (elem_of_list_lookup_2 _ _ _ Hx) as Hxin.
  pose proof (elem_of_list_lookup_2 _ _ _ Hr) as Hrin.
  destruct (gwf_gmo_mem G x Hwf Hxin) as (lx & Hlx & _).
  destruct (gwf_gmo_mem G r Hwf Hrin) as (lr & Hlr & Hmr).
  split.
  - split_and!.
    + split_and!; [done|done|by eexists|by eexists].
    + by exists lr.
    + exists lx. split; [done|]. by rewrite /gis_w Hlx in Hwx.
    + split_and!; [done|done|].
      rewrite (gpos_of_lookup G n x Hnd Hx) (gpos_of_lookup G (S n) r Hnd Hr).
      lia.
  - intros (_ & _ & _ & (_ & _ & Hpos)).
    rewrite (gswap_gpos_lower G n x r Hnd Hx Hr)
            (gswap_gpos_upper G n x r Hnd Hx Hr) in Hpos. lia.
Qed.
