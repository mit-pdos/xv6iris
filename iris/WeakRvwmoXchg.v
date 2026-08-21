(** * WeakRvwmoXchg.v — THE EXCHANGE KIT (route B, stage B2a/B2c/B2b)

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

    ... AND THE TWO REMAINING EXCHANGES, which complete the kit:

      - [gswap_write_down] (§6, B2c) — the (R,W) move: a WRITE descends
        past a read.  Still plain [gswap] (only one of the pair is a
        write, so [gwrites] is again frozen), but the passed read's
        visible set GROWS by exactly the descending write, so
        co-maximality needs ONE side condition: on every byte both touch,
        the read already reads at-or-after that write.  A same-hart
        forwarded read satisfies it with equality;
      - [gswapw] + [gswapw_ww] (§7–§9, B2b) — the (W,W) move, on
        BYTE-DISJOINT writes.  Here the write sub-order itself swaps, so
        the two [gwix] values EXCHANGE and every reader's [ts] entry
        naming either one is renumbered by the adjacent transposition
        [tswap] — which is §1.1's index involution [sidx] at a different
        argument, so §1's kit self-applies one level down.  Byte
        disjointness is exactly what stops any single axiom instance from
        mentioning BOTH transposed values, which is the only way an
        adjacent transposition can break an inequality;
      - the corresponding [gdexec] corollaries and violation bookkeeping
        (§6.3/§6.4, §9.1/§10).

    TWO SIDE CONDITIONS BEYOND THE ORDER THEORY, both flagged where they
    appear and both discharged by the B2 induction, not by these lemmas:
    [(x, e) ∉ gd_deps] on BOTH descent corollaries (a dep edge into a
    descending write blocks the descent — the violation is then dep-killed
    by [gdeps_gmo] instead), and [¬ gpo G x e] on the two
    violation-monotonicity lemmas (discharged by the sweep order: the reads
    between the two writes are pushed down FIRST).

    NOT IN SCOPE (deliberately, per the slices' specs): the SAME-BYTE
    (W,W) exchange, and the fused-RMW read in the (R,R)/(W,R) lemma
    ([r] both reads and writes — excluded there by [gis_w G r = false];
    B2b's byte-disjointness DOES cover fused RMWs, via
    [WeakRvwmoGraph.gread_byte_write_byte]).

    A LEAF: nothing imports this file. *)
From Stdlib.ssr Require Import ssreflect.
From stdpp Require Import gmap finite list relations.
From stdpp Require Import bitvector.definitions.
From xv6iris Require Import WeakMem WeakAxiomatic WeakAxiomatic2 WeakRvwmoGraph.

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

(** THE SELF-APPLICATION SHAPE.  When a filter KEEPS both swapped elements
    the swap survives into the filtered list — as a swap at the filtered
    position.  Stated on the [take]/[drop]-free normal form, which is what
    both sides of the [gwrites] computation reduce to. *)
Lemma lswap_app_middle {A} (L R : list A) (a b : A) :
  lswap (L ++ a :: b :: R) (length L) = L ++ b :: a :: R.
Proof.
  assert (Hn : (L ++ a :: b :: R) !! length L = Some a).
  { by apply list_lookup_middle. }
  assert (HSn : (L ++ a :: b :: R) !! S (length L) = Some b).
  { rewrite (lookup_app_r L (a :: b :: R) (S (length L)) ltac:(lia)).
    by replace (S (length L) - length L)%nat with 1%nat by lia. }
  rewrite (lswap_split _ (length L) a b Hn HSn).
  rewrite (take_app_length' _ _ (length L) eq_refl).
  do 3 f_equal.
  rewrite drop_app (drop_ge L (S (S (length L))) ltac:(lia)).
  by replace (S (S (length L)) - length L)%nat with 2%nat by lia.
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

(* ====================================================================== *)
(** * 6. B2c — THE WRITE-DOWN MOVE: a write descends past a read

    The pair is now oriented the other way round from §3: the LOWER event
    [x] is the NON-write and the UPPER event [e] is the WRITE, so [e]
    DESCENDS.  The transformation is still plain [gswap] — only one of the
    two is a write, so [gwrites] is again EQUAL AS A LIST and every
    [gwix]/[gwrite_at] fact of the whole graph is frozen.  [lswap_filter]
    needs only ONE of the swapped pair rejected, so §2.4's proofs mirror
    verbatim with the OTHER disjunct.

    What genuinely changes relative to §3: [x]'s visible-write set GROWS,
    by exactly [e].  The [∃]-half of [gload_value] is insensitive to that
    (a bigger visible set cannot invalidate a named source), but the
    [∀]-half — co-maximality — is not, and it needs exactly one side
    condition: ON EVERY BYTE BOTH TOUCH, the read [x] already reads
    at-or-after [e].  A same-hart forwarded read of [e] itself satisfies it
    with EQUALITY (and the descent then strictly improves [e]'s
    visibility), so the condition is not vacuous on the forwarding case. *)

(** ** 6.1 The write sub-order equations, mirrored to a non-write LOWER *)

Lemma gswap_gwrites_lo G n x e :
  gx_gmo G !! n = Some x → gx_gmo G !! S n = Some e → gis_w G x = false →
  gwrites (gswap G n) = gwrites G.
Proof.
  intros Hx He Hnw. rewrite /gwrites gswap_is_w gswap_gmo.
  apply (lswap_filter _ _ n x e Hx He). left. rewrite Hnw. by intros [].
Qed.

Lemma gswap_gwrite_at_lo G n x e t :
  gx_gmo G !! n = Some x → gx_gmo G !! S n = Some e → gis_w G x = false →
  gwrite_at (gswap G n) t = gwrite_at G t.
Proof.
  intros Hx He Hnw. rewrite /gwrite_at (gswap_gwrites_lo G n x e Hx He Hnw). done.
Qed.

Lemma gswap_gwix_lo G n x e :
  gx_gmo G !! n = Some x → gx_gmo G !! S n = Some e → gis_w G x = false →
  gwix (gswap G n) = gwix G.
Proof.
  intros Hx He Hnw. rewrite /gwix (gswap_gwrites_lo G n x e Hx He Hnw). done.
Qed.

(** ** 6.2 The lemma *)

Theorem gswap_write_down G n x e :
  rvwmo_minus_consistent G →
  gx_gmo G !! n = Some x → gx_gmo G !! S n = Some e →
  gis_w G x = false → gis_w G e = true →
  ¬ gppo G x e →
  (* THE CO-MAX SIDE CONDITION: on every byte both touch, the passed
     read already reads at-or-after the descending write *)
  (∀ a t v, greads_byte G x a t v →
     (∃ v', gwrites_byte G e a v') → (gwix G e ≤ t)%nat) →
  rvwmo_minus_consistent (gswap G n).
Proof.
  intros (Hwf & Hppo & Hlv & Hat) Hx He Hnwx Hwe Hnppo Hcomax.
  pose proof Hwf as (Hnd & Hmem & Hshape).
  split_and!.
  - (* gwf *) split_and!.
    + by eapply gswap_nodup.
    + intros e'. rewrite gswap_mem (gswap_elem_of G n x e e' Hx He). apply Hmem.
    + exact Hshape.
  - (* gppo⁻ ⊆ gmo *)
    intros e1 e2 Hp. rewrite gswap_ppo in Hp.
    apply (gswap_gmo_lt G n x e e1 e2 Hnd Hx He (Hppo e1 e2 Hp)).
    intros [-> ->]. exact (Hnppo Hp).
  - (* load value *)
    intros e' a t v Hrd. rewrite gswap_rdb in Hrd.
    destruct (Hlv e' a t v Hrd) as [Hsrc Hmax]. split.
    + (* the ∃-half: the named source is untouched — the swap only ADDS
         visibility, and the passed-over [x] is no write, so it can never
         BE the source that would have to move *)
      destruct t as [|t]; [by rewrite gswap_img|].
      destruct Hsrc as (w & Hwat & Hwb & Hvis).
      exists w. split_and!.
      * by rewrite (gswap_gwrite_at_lo G n x e _ Hx He Hnwx).
      * by rewrite gswap_wrb.
      * destruct Hvis as [Hgmo|Hpo]; [left|by right].
        apply (gswap_gmo_lt G n x e w e' Hnd Hx He Hgmo).
        intros [-> ->].
        by rewrite (gwrites_byte_gis_w G x a v Hwb) in Hnwx.
    + (* the ∀-half: THE side condition's only consumer *)
      intros w' v' Hwb' Hvis'.
      rewrite gswap_wrb in Hwb'. rewrite (gswap_gwix_lo G n x e Hx He Hnwx).
      destruct Hvis' as [Hgmo|Hpo]; [|by apply (Hmax w' v' Hwb'); right].
      destruct (gswap_gmo_lt_inv G n x e w' e' Hnd Hx He Hgmo) as [?|[-> ->]].
      * by apply (Hmax w' v' Hwb'); left.
      * (* THE NEW VISIBILITY: [e] has descended below the read [x] *)
        apply (Hcomax a t v Hrd). by exists v'.
  - (* atomicity: every number it mentions is frozen *)
    intros e' a t v Hrd Hw w' v' Hwb.
    rewrite gswap_rdb in Hrd. rewrite gswap_lbl_is in Hw.
    rewrite gswap_wrb in Hwb.
    rewrite !(gswap_gwix_lo G n x e Hx He Hnwx). by eapply Hat.
Qed.

(** ** 6.3 The [gdexec] corollary

    UNLIKE §4, the "no dep edge across the swapped pair" side condition is
    NOT free here and is HYPOTHESIZED — see the flag in the header of §6.4.
    A dep edge into a descending write blocks the descent, correctly: the
    induction discharges the hypothesis because a dep-pinned violation is
    killed by [gdeps_gmo] instead of by an exchange. *)

Corollary gswap_write_down_deps GD n x e :
  rvwmo_minus_deps_consistent GD →
  gx_gmo (gd_g GD) !! n = Some x →
  gx_gmo (gd_g GD) !! S n = Some e →
  gis_w (gd_g GD) x = false →
  gis_w (gd_g GD) e = true →
  ¬ gppo (gd_g GD) x e →
  (∀ a t v, greads_byte (gd_g GD) x a t v →
     (∃ v', gwrites_byte (gd_g GD) e a v') → (gwix (gd_g GD) e ≤ t)%nat) →
  (x, e) ∉ gd_deps GD →
  rvwmo_minus_deps_consistent (GDExec (gswap (gd_g GD) n) (gd_deps GD)).
Proof.
  intros (Hcons & Hdwf & Hdgmo) Hx He Hnwx Hwe Hnppo Hcomax Hdep.
  pose proof Hcons as (Hwf & _ & _ & _). pose proof Hwf as (Hnd & _ & _).
  split_and!.
  - by eapply gswap_write_down.
  - intros rw Hrw. rewrite /= gswap_lbl_is. exact (Hdwf rw Hrw).
  - intros rw Hrw. simpl.
    apply (gswap_gmo_lt (gd_g GD) n x e _ _ Hnd Hx He (Hdgmo rw Hrw)).
    intros [H1 H2]. apply Hdep. destruct rw as [r1 r2]; simpl in *.
    by simplify_eq.
Qed.

(** ** 6.4 Violation bookkeeping

    The only gmo pair whose order flips is [(x, e)], so the only violation
    the move could CREATE is [(x, e)] itself — excluded by [¬ gpo G x e].
    (The B2 induction discharges that by SWEEP ORDER: the reads sitting
    gmo-between the two writes are pushed down FIRST, per the route-B
    design's move strategy.) *)

Lemma gswap_viol_mono_rw G n x e e' w' :
  NoDup (gx_gmo G) → gx_gmo G !! n = Some x → gx_gmo G !! S n = Some e →
  ¬ gpo G x e → gviol (gswap G n) e' w' → gviol G e' w'.
Proof.
  intros Hnd Hx He Hnpo (Hpo & Hme & Hw & Hgmo).
  rewrite gswap_po in Hpo. rewrite gswap_mem in Hme.
  rewrite gswap_lbl_is in Hw.
  split_and!; [done|done|done|].
  destruct (gswap_gmo_lt_inv G n x e w' e' Hnd Hx He Hgmo) as [?|[-> ->]];
    [done|].
  by destruct (Hnpo Hpo).
Qed.

(* ====================================================================== *)
(** * 7. THE TRANSPOSITION ARITHMETIC

    B2b exchanges two WRITES, so the write sub-order itself moves and every
    reader's [ts] entry that names either of them must be RENUMBERED.  The
    renumbering is an ADJACENT TRANSPOSITION of write indices — and an
    adjacent transposition of indices is the SAME function as §1.1's index
    involution, at a different argument.  So [tswap] is literally [sidx],
    and the whole arithmetic is §1.1's, re-exported under the names the
    label rewrite uses.

    The load-bearing facts: [tswap] is an involution (so it is its own
    inverse on [ts] entries), and it preserves every strict inequality and
    every non-strict one EXCEPT between the transposed pair — which is
    where B2b's byte-disjointness hypothesis does its work. *)

Definition tswap (k1 : nat) (t : nat) : nat := sidx k1 t.

Lemma tswap_unfold k1 t :
  tswap k1 t =
    if bool_decide (t = k1) then S k1
    else if bool_decide (t = S k1) then k1 else t.
Proof. reflexivity. Qed.

Lemma tswap_invol k1 t : tswap k1 (tswap k1 t) = t.
Proof. apply sidx_invol. Qed.

Lemma tswap_inj k1 t1 t2 : tswap k1 t1 = tswap k1 t2 → t1 = t2.
Proof. apply sidx_inj. Qed.

Lemma tswap_lt k1 a b :
  (a < b)%nat → ¬ (a = k1 ∧ b = S k1) → (tswap k1 a < tswap k1 b)%nat.
Proof. apply sidx_mono. Qed.

Lemma tswap_lt_inv k1 a b :
  (tswap k1 a < tswap k1 b)%nat → (a < b)%nat ∨ (a = S k1 ∧ b = k1).
Proof. apply sidx_mono_inv. Qed.

(** The ≤ variant — co-maximality's shape.  Same exclusion. *)
Lemma tswap_le k1 a b :
  (a ≤ b)%nat → ¬ (a = k1 ∧ b = S k1) → (tswap k1 a ≤ tswap k1 b)%nat.
Proof.
  intros Hle Hne. rewrite /tswap /sidx. repeat case_bool_decide; lia.
Qed.

(** [0] is the ERA-INITIAL image and must stay put: it does, as soon as the
    transposed pair sits at genuine write indices ([k1 ≥ 1]). *)
Lemma tswap_zero k1 : (0 < k1)%nat → tswap k1 0%nat = 0%nat.
Proof. intros Hk. rewrite /tswap /sidx. repeat case_bool_decide; lia. Qed.

Lemma tswap_eq_zero k1 t : (0 < k1)%nat → tswap k1 t = 0%nat → t = 0%nat.
Proof. intros Hk. rewrite /tswap /sidx. repeat case_bool_decide; lia. Qed.

(** The successor shift: transposing write indices [S m] / [S (S m)] is
    transposing LIST positions [m] / [S m], which is what lets §1's
    [lswap]/[sidx] kit be applied verbatim at the [gwrites] level. *)
Lemma tswap_S m i : tswap (S m) (S i) = S (sidx m i).
Proof. rewrite /tswap /sidx. repeat case_bool_decide; lia. Qed.

(* ====================================================================== *)
(** * 8. [gswapw]: the (W,W) exchange, with the [ts]-transposition rewrite

    The graph transformation now touches the PROGRAMS as well as the order:
    every read label's per-byte [ts] list is mapped by [tswap k1].  Values,
    bases, widths, acquire/release bits and the class field are untouched,
    so EVERY label-shape classifier is stable and only the numeric layer
    moves. *)

Definition lbl_tswap (k1 : nat) (l : lbl) : lbl :=
  match l with
  | LLoad aq base ts vs => LLoad aq base (tswap k1 <$> ts) vs
  | LStore rl base vs k => LStore rl base vs k
  | LFence pr pw sr sw => LFence pr pw sr sw
  | LRmw aq rl base ts rvs wvs k => LRmw aq rl base (tswap k1 <$> ts) rvs wvs k
  end.

(** ** 8.1 Label-shape stability *)

Lemma lbl_tswap_is_r k1 l : lb_is_r (lbl_tswap k1 l) = lb_is_r l.
Proof. by destruct l. Qed.
Lemma lbl_tswap_is_w k1 l : lb_is_w (lbl_tswap k1 l) = lb_is_w l.
Proof. by destruct l. Qed.
Lemma lbl_tswap_is_mem k1 l : lb_is_mem (lbl_tswap k1 l) = lb_is_mem l.
Proof. by destruct l. Qed.
Lemma lbl_tswap_aq k1 l : lb_aq (lbl_tswap k1 l) = lb_aq l.
Proof. by destruct l. Qed.
Lemma lbl_tswap_rl k1 l : lb_rl (lbl_tswap k1 l) = lb_rl l.
Proof. by destruct l. Qed.
Lemma lbl_tswap_cls k1 l : lb_cls (lbl_tswap k1 l) = lb_cls l.
Proof. by destruct l. Qed.
Lemma lbl_tswap_wr k1 l : lb_wr (lbl_tswap k1 l) = lb_wr l.
Proof. by destruct l. Qed.

Lemma lbl_tswap_rd k1 l base ts vs :
  lb_rd l = Some (base, ts, vs) →
  lb_rd (lbl_tswap k1 l) = Some (base, tswap k1 <$> ts, vs).
Proof. destruct l; simpl; intros Hl; by simplify_eq/=. Qed.

Lemma lbl_tswap_rd_inv k1 l base ts vs :
  lb_rd (lbl_tswap k1 l) = Some (base, ts, vs) →
  ∃ ts0, lb_rd l = Some (base, ts0, vs) ∧ ts = tswap k1 <$> ts0.
Proof. destruct l; simpl; intros Hl; simplify_eq/=; eauto. Qed.

Lemma lbl_tswap_fence k1 l pr pw sr sw :
  lbl_tswap k1 l = LFence pr pw sr sw → l = LFence pr pw sr sw.
Proof. destruct l; simpl; intros Hl; by simplify_eq/=. Qed.

(** ** 8.2 The transformation *)

Definition gswapw (G : gexec) (n k1 : nat) : gexec :=
  GExec (gx_img G)
        ((λ row : list lbl, lbl_tswap k1 <$> row) <$> gx_prog G)
        (lswap (gx_gmo G) n).

(** The ORDER half of [gswapw] is literally [gswap]'s, so §2.2/§2.3's
    position kit applies verbatim — these are [reflexivity]. *)
Lemma gswapw_img G n k1 : gx_img (gswapw G n k1) = gx_img G.
Proof. reflexivity. Qed.
Lemma gswapw_gmo G n k1 : gx_gmo (gswapw G n k1) = gx_gmo (gswap G n).
Proof. reflexivity. Qed.
Lemma gswapw_gpos G n k1 : gpos (gswapw G n k1) = gpos (gswap G n).
Proof. reflexivity. Qed.
Lemma gswapw_gmo_lt G n k1 : gmo_lt (gswapw G n k1) = gmo_lt (gswap G n).
Proof. reflexivity. Qed.

(** ** 8.3 The label equation, and everything read off it *)

Lemma gswapw_lbl G n k1 e : gx_lbl (gswapw G n k1) e = lbl_tswap k1 <$> gx_lbl G e.
Proof.
  rewrite /gx_lbl /= list_lookup_fmap.
  destruct (gx_prog G !! e.1) as [p|]; simpl; [|done].
  by rewrite list_lookup_fmap.
Qed.

Lemma gswapw_is_w G n k1 e : gis_w (gswapw G n k1) e = gis_w G e.
Proof.
  rewrite /gis_w gswapw_lbl. destruct (gx_lbl G e) as [l|]; simpl; [|done].
  apply lbl_tswap_is_w.
Qed.

Lemma gswapw_is_Some G n k1 e :
  is_Some (gx_lbl (gswapw G n k1) e) ↔ is_Some (gx_lbl G e).
Proof. rewrite gswapw_lbl. apply fmap_is_Some. Qed.

Lemma gswapw_glbl_is G n k1 e (P : lbl → bool) :
  (∀ l, P (lbl_tswap k1 l) = P l) →
  (glbl_is (gswapw G n k1) e P ↔ glbl_is G e P).
Proof.
  intros HP. rewrite /glbl_is gswapw_lbl. split.
  - intros (l & Hl & HPl). apply fmap_Some in Hl as (l0 & Hl0 & ->).
    exists l0. rewrite -HP. done.
  - intros (l & Hl & HPl). exists (lbl_tswap k1 l).
    rewrite Hl /= HP. done.
Qed.

Lemma gswapw_mem G n k1 e : gmem (gswapw G n k1) e ↔ gmem G e.
Proof. apply (gswapw_glbl_is G n k1 e lb_is_mem), lbl_tswap_is_mem. Qed.

Lemma gswapw_wrb G n k1 e a v :
  gwrites_byte (gswapw G n k1) e a v ↔ gwrites_byte G e a v.
Proof.
  rewrite /gwrites_byte gswapw_lbl. split.
  - intros (l & base & vs & j & Hl & Hwr & Hv & Ha).
    apply fmap_Some in Hl as (l0 & Hl0 & ->).
    rewrite lbl_tswap_wr in Hwr. by exists l0, base, vs, j.
  - intros (l & base & vs & j & Hl & Hwr & Hv & Ha).
    exists (lbl_tswap k1 l), base, vs, j.
    rewrite Hl /= lbl_tswap_wr. done.
Qed.

(** THE READ EQUATION: reads survive with their [ts] entries transposed —
    and because [tswap] is an involution the statement is symmetric. *)
Lemma gswapw_rdb G n k1 e a t v :
  greads_byte (gswapw G n k1) e a t v ↔ greads_byte G e a (tswap k1 t) v.
Proof.
  rewrite /greads_byte gswapw_lbl. split.
  - intros (l & base & ts & vs & j & Hl & Hrd & Ht & Hv & Ha).
    apply fmap_Some in Hl as (l0 & Hl0 & ->).
    apply lbl_tswap_rd_inv in Hrd as (ts0 & Hrd0 & ->).
    rewrite list_lookup_fmap in Ht. apply fmap_Some in Ht as (t0 & Ht0 & ->).
    rewrite tswap_invol. by exists l0, base, ts0, vs, j.
  - intros (l & base & ts & vs & j & Hl & Hrd & Ht & Hv & Ha).
    exists (lbl_tswap k1 l), base, (tswap k1 <$> ts), vs, j.
    rewrite Hl /= (lbl_tswap_rd k1 l base ts vs Hrd) list_lookup_fmap Ht /=
            tswap_invol. done.
Qed.

Lemma gswapw_accesses G n k1 e a : gaccesses (gswapw G n k1) e a ↔ gaccesses G e a.
Proof.
  rewrite /gaccesses. split.
  - intros [(v & Hw)|(t & v & Hr)].
    + left. exists v. by apply (proj1 (gswapw_wrb G n k1 e a v)).
    + right. exists (tswap k1 t), v. by apply (proj1 (gswapw_rdb G n k1 e a t v)).
  - intros [(v & Hw)|(t & v & Hr)].
    + left. exists v. by apply (proj2 (gswapw_wrb G n k1 e a v)).
    + right. exists (tswap k1 t), v.
      apply (proj2 (gswapw_rdb G n k1 e a (tswap k1 t) v)).
      by rewrite tswap_invol.
Qed.

(** ** 8.4 Program order and ppo⁻ are untouched *)

Lemma gswapw_po G n k1 e1 e2 : gpo (gswapw G n k1) e1 e2 ↔ gpo G e1 e2.
Proof.
  rewrite /gpo !(gswapw_is_Some G n k1). done.
Qed.

Lemma gswapw_fence_between G n k1 e1 e2 pr pw sr sw :
  gfence_between (gswapw G n k1) e1 e2 pr pw sr sw ↔
  gfence_between G e1 e2 pr pw sr sw.
Proof.
  rewrite /gfence_between. split.
  - intros (Hag & Hlt & kf & H1 & H2 & Hlf).
    rewrite gswapw_lbl in Hlf. apply fmap_Some in Hlf as (l0 & Hl0 & Heq).
    symmetry in Heq. apply lbl_tswap_fence in Heq as ->. eauto 10.
  - intros (Hag & Hlt & kf & H1 & H2 & Hlf).
    split_and!; [done|done|]. exists kf. split_and!; [done|done|].
    by rewrite gswapw_lbl Hlf.
Qed.

Lemma gswapw_poloc G n k1 e1 e2 : gpoloc (gswapw G n k1) e1 e2 ↔ gpoloc G e1 e2.
Proof.
  rewrite /gpoloc. split.
  - intros (Hp & a & H1 & H2). split.
    + by apply (proj1 (gswapw_po G n k1 e1 e2)).
    + exists a. split.
      * by apply (proj1 (gswapw_accesses G n k1 e1 a)).
      * by apply (proj1 (gswapw_accesses G n k1 e2 a)).
  - intros (Hp & a & H1 & H2). split.
    + by apply (proj2 (gswapw_po G n k1 e1 e2)).
    + exists a. split.
      * by apply (proj2 (gswapw_accesses G n k1 e1 a)).
      * by apply (proj2 (gswapw_accesses G n k1 e2 a)).
Qed.

Lemma gswapw_fence_covers G n k1 e1 e2 :
  gfence_covers (gswapw G n k1) e1 e2 ↔ gfence_covers G e1 e2.
Proof.
  rewrite /gfence_covers. split.
  - intros (pr & pw & sr & sw & Hfb & H1 & H2). exists pr, pw, sr, sw. split_and!.
    + by apply (proj1 (gswapw_fence_between G n k1 e1 e2 pr pw sr sw)).
    + destruct H1 as [[Hl Hb]|[Hl Hb]]; [left|right]; (split; [|done]).
      * by apply (proj1 (gswapw_glbl_is G n k1 e1 lb_is_r (lbl_tswap_is_r k1))).
      * by apply (proj1 (gswapw_glbl_is G n k1 e1 lb_is_w (lbl_tswap_is_w k1))).
    + destruct H2 as [[Hl Hb]|[Hl Hb]]; [left|right]; (split; [|done]).
      * by apply (proj1 (gswapw_glbl_is G n k1 e2 lb_is_r (lbl_tswap_is_r k1))).
      * by apply (proj1 (gswapw_glbl_is G n k1 e2 lb_is_w (lbl_tswap_is_w k1))).
  - intros (pr & pw & sr & sw & Hfb & H1 & H2). exists pr, pw, sr, sw. split_and!.
    + by apply (proj2 (gswapw_fence_between G n k1 e1 e2 pr pw sr sw)).
    + destruct H1 as [[Hl Hb]|[Hl Hb]]; [left|right]; (split; [|done]).
      * by apply (proj2 (gswapw_glbl_is G n k1 e1 lb_is_r (lbl_tswap_is_r k1))).
      * by apply (proj2 (gswapw_glbl_is G n k1 e1 lb_is_w (lbl_tswap_is_w k1))).
    + destruct H2 as [[Hl Hb]|[Hl Hb]]; [left|right]; (split; [|done]).
      * by apply (proj2 (gswapw_glbl_is G n k1 e2 lb_is_r (lbl_tswap_is_r k1))).
      * by apply (proj2 (gswapw_glbl_is G n k1 e2 lb_is_w (lbl_tswap_is_w k1))).
Qed.

Lemma gswapw_acq_po G n k1 e1 e2 : gacq_po (gswapw G n k1) e1 e2 ↔ gacq_po G e1 e2.
Proof.
  rewrite /gacq_po. split.
  - intros (Hp & H1 & H2). split_and!.
    + by apply (proj1 (gswapw_po G n k1 e1 e2)).
    + by apply (proj1 (gswapw_glbl_is G n k1 e1 lb_is_r (lbl_tswap_is_r k1))).
    + by apply (proj1 (gswapw_glbl_is G n k1 e1 lb_aq (lbl_tswap_aq k1))).
  - intros (Hp & H1 & H2). split_and!.
    + by apply (proj2 (gswapw_po G n k1 e1 e2)).
    + by apply (proj2 (gswapw_glbl_is G n k1 e1 lb_is_r (lbl_tswap_is_r k1))).
    + by apply (proj2 (gswapw_glbl_is G n k1 e1 lb_aq (lbl_tswap_aq k1))).
Qed.

Lemma gswapw_rel_acq G n k1 e1 e2 :
  grel_acq (gswapw G n k1) e1 e2 ↔ grel_acq G e1 e2.
Proof.
  rewrite /grel_acq. split.
  - intros (Hp & H1 & H2 & H3 & H4). split_and!.
    + by apply (proj1 (gswapw_po G n k1 e1 e2)).
    + by apply (proj1 (gswapw_glbl_is G n k1 e1 lb_is_w (lbl_tswap_is_w k1))).
    + by apply (proj1 (gswapw_glbl_is G n k1 e1 lb_rl (lbl_tswap_rl k1))).
    + by apply (proj1 (gswapw_glbl_is G n k1 e2 lb_is_r (lbl_tswap_is_r k1))).
    + by apply (proj1 (gswapw_glbl_is G n k1 e2 lb_aq (lbl_tswap_aq k1))).
  - intros (Hp & H1 & H2 & H3 & H4). split_and!.
    + by apply (proj2 (gswapw_po G n k1 e1 e2)).
    + by apply (proj2 (gswapw_glbl_is G n k1 e1 lb_is_w (lbl_tswap_is_w k1))).
    + by apply (proj2 (gswapw_glbl_is G n k1 e1 lb_rl (lbl_tswap_rl k1))).
    + by apply (proj2 (gswapw_glbl_is G n k1 e2 lb_is_r (lbl_tswap_is_r k1))).
    + by apply (proj2 (gswapw_glbl_is G n k1 e2 lb_aq (lbl_tswap_aq k1))).
Qed.

Lemma gswapw_ppo G n k1 e1 e2 : gppo (gswapw G n k1) e1 e2 ↔ gppo G e1 e2.
Proof.
  rewrite /gppo. split.
  - intros [H|[H|[H|H]]].
    + left. by apply (proj1 (gswapw_poloc G n k1 e1 e2)).
    + right; left. by apply (proj1 (gswapw_fence_covers G n k1 e1 e2)).
    + right; right; left. by apply (proj1 (gswapw_acq_po G n k1 e1 e2)).
    + right; right; right. by apply (proj1 (gswapw_rel_acq G n k1 e1 e2)).
  - intros [H|[H|[H|H]]].
    + left. by apply (proj2 (gswapw_poloc G n k1 e1 e2)).
    + right; left. by apply (proj2 (gswapw_fence_covers G n k1 e1 e2)).
    + right; right; left. by apply (proj2 (gswapw_acq_po G n k1 e1 e2)).
    + right; right; right. by apply (proj2 (gswapw_rel_acq G n k1 e1 e2)).
Qed.

(** ** 8.5 THE WRITE SUB-ORDER SWAPS TOO — the §1 kit, self-applied

    Both exchanged events are writes, so [gwrites] is NOT frozen: it is the
    SAME adjacent swap, one level down.  Two gmo-adjacent writes are
    [gwrites]-adjacent (nothing can sit between them), so the write indices
    that move are [S m] and [S (S m)] for one [m] — which is exactly the
    adjacent transposition [tswap (S m)] that §7 renumbers [ts] entries by.

    This lemma packages all of it: the [gwrites] position [m] of the pair,
    the two [gwix] values, and the list equation. *)

Lemma gswapw_writes_kit G n k1 x e :
  NoDup (gx_gmo G) →
  gx_gmo G !! n = Some x → gx_gmo G !! S n = Some e →
  gis_w G x = true → gis_w G e = true →
  ∃ m, gwrites G !! m = Some x ∧ gwrites G !! S m = Some e ∧
       gwix G x = S m ∧ gwix G e = S (S m) ∧
       gwrites (gswapw G n k1) = lswap (gwrites G) m.
Proof.
  intros Hnd Hx He Hwx Hwe.
  assert (Hx' : Is_true (gis_w G x)) by (rewrite Hwx; done).
  assert (He' : Is_true (gis_w G e)) by (rewrite Hwe; done).
  assert (Hfilt : ∀ z : geid,
            Is_true (gis_w (gswapw G n k1) z) ↔ Is_true (gis_w G z)).
  { intros z. by rewrite gswapw_is_w. }
  assert (Hsplit : ∃ L R, gwrites G = L ++ x :: e :: R ∧
                          gwrites (gswapw G n k1) = L ++ e :: x :: R).
  { exists (filter (gis_w G) (take n (gx_gmo G))),
           (filter (gis_w G) (drop (S (S n)) (gx_gmo G))).
    split.
    - rewrite /gwrites {1}(lsplit2 (gx_gmo G) n x e Hx He)
              list_basics.filter_app !filter_cons.
      case_decide as Hd1; [|by destruct (Hd1 Hx')].
      case_decide as Hd2; [|by destruct (Hd2 He')]. done.
    - rewrite /gwrites /gswapw /= (list_filter_iff _ _ _ Hfilt)
              (lswap_split (gx_gmo G) n x e Hx He)
              list_basics.filter_app !filter_cons.
      case_decide as Hd1; [|by destruct (Hd1 He')].
      case_decide as Hd2; [|by destruct (Hd2 Hx')]. done. }
  destruct Hsplit as (L & R & Hgw1 & Hgw2).
  assert (Hm : gwrites G !! length L = Some x).
  { rewrite Hgw1. by apply list_lookup_middle. }
  assert (HSm : gwrites G !! S (length L) = Some e).
  { rewrite Hgw1 (lookup_app_r L (x :: e :: R) (S (length L)) ltac:(lia)).
    by replace (S (length L) - length L)%nat with 1%nat by lia. }
  exists (length L). split_and!; [done|done| | |].
  - by apply gwix_of_lookup.
  - by apply gwix_of_lookup.
  - by rewrite Hgw2 Hgw1 lswap_app_middle.
Qed.

(** ADJACENCY, standalone: nothing sits between two gmo-adjacent writes,
    so their write indices are consecutive.  This is what makes the
    renumbering an ADJACENT transposition rather than a general one. *)
Lemma gwix_adjacent G n x e :
  NoDup (gx_gmo G) →
  gx_gmo G !! n = Some x → gx_gmo G !! S n = Some e →
  gis_w G x = true → gis_w G e = true →
  gwix G e = S (gwix G x).
Proof.
  intros Hnd Hx He Hwx Hwe.
  destruct (gswapw_writes_kit G n 0%nat x e Hnd Hx He Hwx Hwe)
    as (m & _ & _ & Hkx & Hke & _). by rewrite Hke Hkx.
Qed.

(** ** 8.6 THE KEY EQUATIONS: write indices are renumbered by [tswap]

    [gwrite_at] is INVARIANT modulo the renumbering — a [ts] entry and the
    write it names move together — and [gwix] is renumbered by exactly the
    same transposition, TOTALLY (off the write sub-order both sides are the
    junk [0], which [tswap] fixes). *)

Section gswapw_wix.
  Context (G : gexec) (n : nat) (x e : geid) (m : nat).
  Context (Hnd : NoDup (gx_gmo G)).
  Context (Hx : gx_gmo G !! n = Some x) (He : gx_gmo G !! S n = Some e).
  Context (Hm : gwrites G !! m = Some x) (HSm : gwrites G !! S m = Some e).
  Context (Hgws : gwrites (gswapw G n (S m)) = lswap (gwrites G) m).

  Lemma gswapw_gwrites_lookup i :
    gwrites (gswapw G n (S m)) !! i = gwrites G !! sidx m i.
  Proof. rewrite Hgws. by apply (lswap_lookup _ m x e). Qed.

  Lemma gswapw_gwrite_at t :
    gwrite_at (gswapw G n (S m)) t = gwrite_at G (tswap (S m) t).
  Proof.
    destruct t as [|i]; [by rewrite (tswap_zero (S m) ltac:(lia))|].
    rewrite /gwrite_at tswap_S /=. apply gswapw_gwrites_lookup.
  Qed.

  Lemma gswapw_nodup' : NoDup (gx_gmo (gswapw G n (S m))).
  Proof. rewrite gswapw_gmo. by eapply gswap_nodup. Qed.

  Lemma gswapw_gwix w : gwix (gswapw G n (S m)) w = tswap (S m) (gwix G w).
  Proof.
    destruct (decide (w ∈ gwrites G)) as [Hin|Hnin].
    - destruct (gwix_lookup G w Hin) as (i & Hi & ->).
      rewrite tswap_S. apply gwix_of_lookup; [apply gswapw_nodup'|].
      rewrite gswapw_gwrites_lookup sidx_invol. exact Hi.
    - rewrite (gwix_zero G w Hnin) (tswap_zero (S m) ltac:(lia)).
      apply gwix_zero. intros Hin. apply Hnin.
      apply gwrites_elem_of in Hin as [Hin Hw].
      apply gwrites_elem_of. rewrite gswapw_is_w in Hw. split; [|done].
      by apply (gswap_elem_of G n x e w Hx He).
  Qed.
End gswapw_wix.

(* ====================================================================== *)
(** * 9. B2b — THE (W,W) EXCHANGE, byte-disjoint

    Both events are writes, so the write sub-order itself moves: their
    [gwix] values EXCHANGE (they are adjacent, §8.5) and every reader's
    [ts] entry naming either one must be renumbered — which is what
    [gswapw]'s label rewrite does, by the adjacent transposition
    [tswap (gwix G x)].

    THE LOAD-BEARING OBSERVATION.  Every numeric comparison [gload_value]
    and [gatomicity] make is between [ts] entries and [gwix] values that
    are ALL renumbered by the SAME adjacent transposition, and an adjacent
    transposition preserves every (strict or non-strict) inequality EXCEPT
    one between the transposed pair itself.  An instance can mention BOTH
    transposed values only if [x] and [e] are both same-byte-relevant to
    it — excluded by BYTE-DISJOINTNESS, which also covers the fused-RMW
    read halves because an [LRmw]'s read footprint IS its write footprint
    ([WeakRvwmoGraph.gread_byte_write_byte]).

    Visibility: [x]'s readers sit gmo-after [S n] — the adjacent slot holds
    [e], which by byte-disjointness cannot be reading [x] — so [x] moving
    up one slot breaks nothing; [e]'s readers only gain. *)

Theorem gswapw_ww G n x e :
  rvwmo_minus_consistent G →
  gx_gmo G !! n = Some x → gx_gmo G !! S n = Some e →
  gis_w G x = true → gis_w G e = true →
  (* byte-disjoint (this also covers the RMW read halves: an [LRmw]'s read
     footprint equals its write footprint — same base/width) *)
  (∀ a, (∃ v, gwrites_byte G x a v) → ¬ ∃ v', gwrites_byte G e a v') →
  ¬ gppo G x e →
  rvwmo_minus_consistent (gswapw G n (gwix G x)).
Proof.
  intros (Hwf & Hppo & Hlv & Hat) Hx He Hwx Hwe Hdisj Hnppo.
  pose proof Hwf as (Hnd & Hmem & Hshape).
  destruct (gswapw_writes_kit G n (gwix G x) x e Hnd Hx He Hwx Hwe)
    as (m & Hm & HSm & Hkx & Hke & Hgws).
  rewrite Hkx in Hgws. rewrite Hkx.
  pose proof (gswapw_gwrite_at G n x e m Hm HSm Hgws) as Hgwat.
  pose proof (gswapw_gwix G n x e m Hnd Hx He Hm HSm Hgws) as Hgwix.
  assert (Hxin : x ∈ gwrites G).
  { apply gwrites_elem_of. split; [by eapply elem_of_list_lookup_2|done]. }
  assert (Hein : e ∈ gwrites G).
  { apply gwrites_elem_of. split; [by eapply elem_of_list_lookup_2|done]. }
  (* THE THREE BYTE-DISJOINTNESS COROLLARIES, in the shapes the cases use *)
  assert (Hxrd : ∀ a t v, greads_byte G x a t v → ¬ ∃ v', gwrites_byte G e a v').
  { intros a t v Hrd.
    destruct (gread_byte_write_byte G x a t v Hwf Hwx Hrd) as (v2 & Hv2).
    apply (Hdisj a). by exists v2. }
  assert (Herd : ∀ a t v, greads_byte G e a t v → ¬ ∃ v', gwrites_byte G x a v').
  { intros a t v Hrd (v' & Hv').
    destruct (gread_byte_write_byte G e a t v Hwf Hwe Hrd) as (v2 & Hv2).
    apply (Hdisj a); [by exists v'|by exists v2]. }
  assert (Hrde : ∀ e' a v, greads_byte G e' a (gwix G e) v → gwrites_byte G e a v).
  { intros e' a v Hrd. eapply gread_source_byte; [exact Hlv|exact Hrd|].
    by apply gwrite_at_gwix. }
  split_and!.
  - (* gwf *) split_and!.
    + by eapply gswapw_nodup'.
    + intros e'. rewrite (gswapw_mem G n (S m) e') gswapw_gmo.
      rewrite (gswap_elem_of G n x e e' Hx He). apply Hmem.
    + intros i p' k l' Hp' Hk'.
      rewrite /= list_lookup_fmap in Hp'.
      apply fmap_Some in Hp' as (p & Hp & ->).
      rewrite list_lookup_fmap in Hk'. apply fmap_Some in Hk' as (l & Hl & ->).
      specialize (Hshape i p k l Hp Hl).
      destruct l; simpl in *; rewrite ?length_fmap; naive_solver.
  - (* gppo⁻ ⊆ gmo *)
    intros e1 e2 Hp. apply (proj1 (gswapw_ppo G n (S m) e1 e2)) in Hp.
    rewrite gswapw_gmo_lt.
    apply (gswap_gmo_lt G n x e e1 e2 Hnd Hx He (Hppo e1 e2 Hp)).
    intros [-> ->]. exact (Hnppo Hp).
  - (* load value *)
    intros e' a t v Hrd.
    apply (proj1 (gswapw_rdb G n (S m) e' a t v)) in Hrd.
    destruct (Hlv e' a (tswap (S m) t) v Hrd) as [Hsrc Hmax].
    split.
    + (* the ∃-half: the source moves WITH the renumbering *)
      destruct t as [|i].
      * rewrite (tswap_zero (S m) ltac:(lia)) in Hsrc. exact Hsrc.
      * rewrite tswap_S in Hsrc. simpl in Hsrc.
        destruct Hsrc as (w & Hwat & Hwb & Hvis).
        exists w. split_and!.
        { rewrite Hgwat tswap_S. exact Hwat. }
        { by apply (proj2 (gswapw_wrb G n (S m) w a v)). }
        { destruct Hvis as [Hgmo|Hpo];
            [left|right; by apply (proj2 (gswapw_po G n (S m) w e'))].
          rewrite gswapw_gmo_lt.
          apply (gswap_gmo_lt G n x e w e' Hnd Hx He Hgmo).
          intros [-> ->]. (* [e] would have to read [x] — byte-disjoint *)
          apply (Herd a _ v Hrd). by exists v. }
    + (* the ∀-half: co-maximality, transported by [tswap_le] *)
      intros w' v' Hwb' Hvis'.
      apply (proj1 (gswapw_wrb G n (S m) w' a v')) in Hwb'.
      assert (Hle : (tswap (S m) (gwix G w')
                     ≤ tswap (S m) (tswap (S m) t))%nat).
      { apply tswap_le.
        - apply (Hmax w' v' Hwb').
          destruct Hvis' as [Hgmo|Hpo];
            [|right; by apply (proj1 (gswapw_po G n (S m) w' e'))].
          rewrite gswapw_gmo_lt in Hgmo.
          destruct (gswap_gmo_lt_inv G n x e w' e' Hnd Hx He Hgmo)
            as [?|[-> ->]]; [by left|].
          (* the NEW visibility [(e, x)] — vacuous: [x] would read [e]'s
             byte, and an RMW's read footprint is its write footprint *)
          exfalso. apply (Hxrd a _ v Hrd). by exists v'.
        - (* THE TRANSPOSED PAIR: [w' = x] AND the read names [e] *)
          intros [Hw'k Htk].
          assert (Hw'in : w' ∈ gwrites G) by (apply gwix_elem; rewrite Hw'k; lia).
          assert (w' = x) as ->.
          { apply (gwix_inj G w' x Hnd Hw'in Hxin). by rewrite Hw'k Hkx. }
          apply (Hdisj a); [by exists v'|].
          exists v. apply (Hrde e' a v). rewrite Hke -Htk. exact Hrd. }
      rewrite tswap_invol in Hle. by rewrite Hgwix.
  - (* atomicity *)
    intros e' a t v Hrd Hw w' v' Hwb.
    apply (proj1 (gswapw_rdb G n (S m) e' a t v)) in Hrd.
    apply (proj1 (gswapw_glbl_is G n (S m) e' lb_is_w (lbl_tswap_is_w (S m))))
      in Hw.
    apply (proj1 (gswapw_wrb G n (S m) w' a v')) in Hwb.
    rewrite !Hgwix. intros [H1 H2].
    assert (H1' : (tswap (S m) (tswap (S m) t) < tswap (S m) (gwix G w'))%nat)
      by (by rewrite tswap_invol).
    apply tswap_lt_inv in H1'. apply tswap_lt_inv in H2.
    destruct H1' as [Hlt1|[Ha1 Hb1]]; destruct H2 as [Hlt2|[Ha2 Hb2]].
    + (* both comparisons survive: [G]'s own atomicity refutes it *)
      by apply (Hat e' a (tswap (S m) t) v Hrd Hw w' v' Hwb).
    + (* [w' = e] co-between and [e' = x] the RMW — same byte, excluded *)
      assert (Hw'in : w' ∈ gwrites G) by (apply gwix_elem; rewrite Ha2; lia).
      assert (He'in : e' ∈ gwrites G) by (apply gwix_elem; rewrite Hb2; lia).
      assert (w' = e) as ->.
      { apply (gwix_inj G w' e Hnd Hw'in Hein). by rewrite Ha2 Hke. }
      assert (e' = x) as ->.
      { apply (gwix_inj G e' x Hnd He'in Hxin). by rewrite Hb2 Hkx. }
      apply (Hxrd a _ v Hrd). by exists v'.
    + (* the read names [e] and [w' = x] — same byte, excluded *)
      assert (Hw'in : w' ∈ gwrites G) by (apply gwix_elem; rewrite Hb1; lia).
      assert (w' = x) as ->.
      { apply (gwix_inj G w' x Hnd Hw'in Hxin). by rewrite Hb1 Hkx. }
      apply (Hdisj a); [by exists v'|].
      exists v. apply (Hrde e' a v). rewrite Hke -Ha1. exact Hrd.
    + lia.
Qed.

(** ** 9.1 The [gdexec] corollary

    FLAGGED DEVIATION (see the file header's B2b note): the "no dep edge
    across the swapped pair" condition is HYPOTHESIZED, not derived.  The
    spec expected it to be free ("a dep edge has a READ source and [x] is a
    write"), but the alphabet is FUSED: an [LRmw] is a write AND a read, so
    [(x, e)] with [x] an RMW and [e] a po-later same-hart store is a
    perfectly well-formed dep edge, and the swap would break [gdeps_gmo]
    for it.  Byte-disjointness does not exclude it either (the two events
    touch different bytes, which is exactly what an address-dependent store
    after an AMO looks like).  So the side condition is genuine, and it is
    the SAME one B2c carries. *)

Corollary gswapw_ww_deps GD n x e :
  rvwmo_minus_deps_consistent GD →
  gx_gmo (gd_g GD) !! n = Some x →
  gx_gmo (gd_g GD) !! S n = Some e →
  gis_w (gd_g GD) x = true → gis_w (gd_g GD) e = true →
  (∀ a, (∃ v, gwrites_byte (gd_g GD) x a v) →
        ¬ ∃ v', gwrites_byte (gd_g GD) e a v') →
  ¬ gppo (gd_g GD) x e →
  (x, e) ∉ gd_deps GD →
  rvwmo_minus_deps_consistent
    (GDExec (gswapw (gd_g GD) n (gwix (gd_g GD) x)) (gd_deps GD)).
Proof.
  intros (Hcons & Hdwf & Hdgmo) Hx He Hwx Hwe Hdisj Hnppo Hdep.
  pose proof Hcons as (Hwf & _ & _ & _). pose proof Hwf as (Hnd & _ & _).
  split_and!.
  - by eapply gswapw_ww.
  - intros rw Hrw. destruct (Hdwf rw Hrw) as (H1 & H2 & H3 & H4).
    split_and!; [done|done| |].
    + by apply (proj2 (gswapw_glbl_is (gd_g GD) n (gwix (gd_g GD) x) rw.1
                         lb_is_r (lbl_tswap_is_r _))).
    + by apply (proj2 (gswapw_glbl_is (gd_g GD) n (gwix (gd_g GD) x) rw.2
                         lb_is_w (lbl_tswap_is_w _))).
  - intros rw Hrw. rewrite /= gswapw_gmo_lt.
    apply (gswap_gmo_lt (gd_g GD) n x e _ _ Hnd Hx He (Hdgmo rw Hrw)).
    intros [Ha Hb]. apply Hdep. destruct rw as [r1 r2]; simpl in *.
    by simplify_eq.
Qed.

(* ====================================================================== *)
(** * 10. RULE-14 BOOKKEEPING for the (W,W) move

    [gviol] mentions labels only through [gpo], [gmem] and
    [glbl_is _ lb_is_w] — all three [lbl_tswap]-invariant, since the
    rewrite touches only [ts] entries — so the renumbering is invisible to
    the measure, and the ordering half is §2.3's, verbatim. *)

Lemma gswapw_viol_mono G n k1 x e e' w' :
  NoDup (gx_gmo G) → gx_gmo G !! n = Some x → gx_gmo G !! S n = Some e →
  ¬ gpo G x e → gviol (gswapw G n k1) e' w' → gviol G e' w'.
Proof.
  intros Hnd Hx He Hnpo (Hpo & Hme & Hw & Hgmo).
  apply (proj1 (gswapw_po G n k1 e' w')) in Hpo.
  apply (proj1 (gswapw_mem G n k1 e')) in Hme.
  apply (proj1 (gswapw_glbl_is G n k1 w' lb_is_w (lbl_tswap_is_w k1))) in Hw.
  rewrite gswapw_gmo_lt in Hgmo.
  split_and!; [done|done|done|].
  destruct (gswap_gmo_lt_inv G n x e w' e' Hnd Hx He Hgmo) as [?|[-> ->]];
    [done|].
  by destruct (Hnpo Hpo).
Qed.

(** ... AND THE SWAPPED PAIR'S OWN VIOLATION IS RESOLVED, in the resolving
    orientation: the UPPER event [e] is po-BEFORE the lower write [x], so
    [(e, x)] is a rule-14 inversion of [G] and is not one of the swapped
    graph.  With [gswapw_viol_mono] the inversion count drops strictly. *)

Lemma gswapw_resolves G n x e :
  gwf G → gx_gmo G !! n = Some x → gx_gmo G !! S n = Some e →
  gis_w G x = true → gis_w G e = true → e.1 = x.1 → (e.2 < x.2)%nat →
  gviol G e x ∧ ¬ gviol (gswapw G n (gwix G x)) e x.
Proof.
  intros Hwf Hx He Hwx Hwe Hag Hlt.
  pose proof Hwf as (Hnd & _ & _).
  pose proof (elem_of_list_lookup_2 _ _ _ Hx) as Hxin.
  pose proof (elem_of_list_lookup_2 _ _ _ He) as Hein.
  destruct (gwf_gmo_mem G x Hwf Hxin) as (lx & Hlx & _).
  destruct (gwf_gmo_mem G e Hwf Hein) as (le & Hle & Hme).
  split.
  - split_and!.
    + split_and!; [done|done|by eexists|by eexists].
    + by exists le.
    + exists lx. split; [done|]. by rewrite /gis_w Hlx in Hwx.
    + split_and!; [done|done|].
      rewrite (gpos_of_lookup G n x Hnd Hx) (gpos_of_lookup G (S n) e Hnd He).
      lia.
  - intros (_ & _ & _ & (_ & _ & Hpos)).
    rewrite gswapw_gpos in Hpos.
    rewrite (gswap_gpos_lower G n x e Hnd Hx He)
            (gswap_gpos_upper G n x e Hnd Hx He) in Hpos. lia.
Qed.

(** ** 10.1 A NON-VACUITY SMOKE TEST for the (W,W) move

    The move applies to the non-collapse witness too: [lbg]'s gmo
    [[(0,1); (1,1); (0,0); (1,0)]] opens with the two STORES, and they are
    byte-disjoint (hart 0 stores byte 8, hart 1 stores byte 0), so they may
    be exchanged — with every reader's [ts] entry renumbered, since BOTH
    loads name one of them.  The ppo⁻ side condition is again discharged
    cross-hart, via [gppo_same_hart]. *)

Example lbg_swapw_consistent :
  rvwmo_minus_consistent (gswapw lbg 0 (gwix lbg (0%nat, 1%nat))).
Proof.
  eapply (gswapw_ww lbg 0 (0%nat, 1%nat) (1%nat, 1%nat));
    [exact lb_graph_consistent|reflexivity|reflexivity|reflexivity
    |reflexivity| |].
  - intros a (v & Hv) (v' & Hv').
    destruct (lbg_wr _ _ _ Hv) as [[_ Ha]|[Hb _]]; [|by inversion Hb].
    destruct (lbg_wr _ _ _ Hv') as [[Hb _]|[_ Ha']]; [by inversion Hb|].
    rewrite Ha in Ha'. lia.
  - intros Hppo. by apply gppo_same_hart in Hppo.
Qed.
