(* FsStateBitmap.v -- the free-space state, CSL-style.

   Design of record: claude-notes/design/fs-state.md section 2,
   "[free_bitmap], CSL-style", and claude-notes/design/fs-bitmap.md.

   [free_bitmap_at Γ bms nb u] owns the bitmap block [bms], at its encoding
   [bm_bytes] of the set [u] of blocks IN USE (xv6: bit set = allocated, bit
   clear = free), AND, for every block below [nb] whose bit reads FREE, THE
   BLOCK ITSELF, at arbitrary content.  [free_bitmap Γ sb u] is that at the
   superblock's two numbers.

   Two things fall out of that and neither is a maintained clause:

   - [bfree] hands a block in.  If the block's bit read free, the pool would
     already own it -- two owners of one block's bytes, which is [False] by
     [blk_owned_excl].  So the bit reads allocated and the "freeing free
     block" panic arm is DEAD.  That is [free_pool_used] below, and it is
     the one place [phi_excl] is used.
   - [balloc] flips a free bit and takes that block out of the [∗].  Nobody
     carries a bit resource; there is NO "used set" clause anywhere and no
     completeness clause.  A block nobody owns is a lost resource, which is
     what a leaked block is. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list list_numbers bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop.
Require Import BioDefs.
Require Import BitmapEnc.
Require Import FsImg.
Require Export FsStateDefs.

Local Open Scope Z_scope.

Section Bitmap.
  Context {Σ : gFunctors}.
  Implicit Types Γ : fs_view_names Σ.

  (* one block's slot in the pool: owned iff its bit reads free *)
  Definition pool_elt Γ (u : gset Z) (b : Z) : iProp Σ :=
    (if bool_decide (b ∈ u) then emp else ∃ bs, blk_owned Γ b bs)%I.

  Definition free_pool Γ (nb : Z) (u : gset Z) : iProp Σ :=
    ([∗ list] b ∈ seqZ 0 nb, pool_elt Γ u b)%I.

  (* the pool with position [i0] held out -- the shape [big_sepL_delete]
     produces, and the one at which a change of [u] at one block is a
     [big_sepL_proper] *)
  Definition free_pool_but Γ (nb : Z) (u : gset Z) (i0 : nat) : iProp Σ :=
    ([∗ list] k ↦ b ∈ seqZ 0 nb,
       if decide (k = i0) then emp else pool_elt Γ u b)%I.

  (* THE GEOMETRY-FREE FORM.  The predicate reads exactly two numbers off
     the superblock -- the bitmap block's number and the block count -- so
     the theory is stated at those two [Z]s and [free_bitmap] is the
     superblock reading of it.  That is what lets a consumer with no
     [fs_sb] in hand ([BitmapInv.bitmap_inv], which carries [bmapstart] and
     [size] as the plain cells balloc reads out of memory) own the very
     same predicate. *)
  Definition free_bitmap_at Γ (bms nb : Z) (u : gset Z) : iProp Σ :=
    (blk_owned Γ bms (bm_bytes BSIZE u) ∗ free_pool Γ nb u)%I.

  Definition free_bitmap Γ (sb : fs_sb) (u : gset Z) : iProp Σ :=
    free_bitmap_at Γ (sb_bmapstart sb) (sb_size sb) u.

  Lemma free_bitmap_unfold Γ sb u :
    free_bitmap Γ sb u
    ⊣⊢ free_bitmap_at Γ (sb_bmapstart sb) (sb_size sb) u.
  Proof. done. Qed.

  (* neither the link family nor the top map is read here: the bitmap piece
     of a view depends on [fsΦ] alone.  [FsState.fs_footprint_gname] is the
     same fact for the whole footprint, and this is what lets an owner that
     has only the byte view's [fsΦ] hold the predicate stage 2c's real
     [Γ_L] will own. *)
  Lemma free_bitmap_at_gname Γ g t bms nb u :
    free_bitmap_at Γ bms nb u
    ⊣⊢ free_bitmap_at (MkFsView (fsΦ Γ) g t) bms nb u.
  Proof. done. Qed.

  Global Instance pool_elt_timeless `{!GTimeless Γ} u b :
    Timeless (pool_elt Γ u b).
  Proof. rewrite /pool_elt. destruct (bool_decide (b ∈ u)); apply _. Qed.

  Global Instance free_pool_timeless `{!GTimeless Γ} nb u :
    Timeless (free_pool Γ nb u).
  Proof. rewrite /free_pool. apply _. Qed.

  Global Instance free_bitmap_at_timeless `{!GTimeless Γ} bms nb u :
    Timeless (free_bitmap_at Γ bms nb u).
  Proof. rewrite /free_bitmap_at. apply _. Qed.

  Global Instance free_bitmap_timeless `{!GTimeless Γ} sb u :
    Timeless (free_bitmap Γ sb u).
  Proof. rewrite /free_bitmap. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (*  The pool, at one block                                           *)
  (* ---------------------------------------------------------------- *)

  Lemma seqZ_lookup_nat (nb : Z) (i : nat) :
    (Z.of_nat i < nb)%Z -> seqZ 0 nb !! i = Some (Z.of_nat i).
  Proof.
    intros Hi.
    rewrite lookup_seqZ_lt //.
  Qed.

  Lemma free_pool_split Γ nb u (i0 : nat) :
    (Z.of_nat i0 < nb)%Z ->
    free_pool Γ nb u ⊣⊢
      pool_elt Γ u (Z.of_nat i0) ∗ free_pool_but Γ nb u i0.
  Proof.
    intros Hi.
    rewrite /free_pool /free_pool_but.
    by rewrite (big_sepL_delete _ (seqZ 0 nb) i0 (Z.of_nat i0))
         ; [| apply seqZ_lookup_nat].
  Qed.

  (* changing [u] at ONE block does not disturb the rest of the pool *)
  Lemma free_pool_but_eq Γ nb u u' (i0 : nat) :
    (forall x : Z, x <> Z.of_nat i0 -> (x ∈ u <-> x ∈ u')) ->
    free_pool_but Γ nb u i0 ⊣⊢ free_pool_but Γ nb u' i0.
  Proof.
    intros Hoff.
    rewrite /free_pool_but.
    apply big_sepL_proper. intros k x Hk.
    destruct (decide (k = i0)) as [-> |]; [done |].
    apply lookup_seqZ in Hk as [-> Hlt].
    rewrite /pool_elt (bool_decide_iff_eq (0 + Z.of_nat k ∈ u)
                                          (0 + Z.of_nat k ∈ u')) //.
    apply Hoff. lia.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  The three pool moves                                             *)
  (* ---------------------------------------------------------------- *)

  (* ALLOCATE: a clear bit yields the block, and the pool shrinks by
     exactly that block. *)
  Lemma free_pool_take Γ nb u (b : Z) :
    0 <= b < nb -> b ∉ u ->
    free_pool Γ nb u ⊢ (∃ bs, blk_owned Γ b bs) ∗ free_pool Γ nb (u ∪ {[b]}).
  Proof.
    intros [Hb0 Hbn] Hnu.
    assert (Hb : Z.of_nat (Z.to_nat b) = b) by lia.
    assert (Hub : b ∈ u ∪ {[b]}) by set_solver.
    rewrite (free_pool_split Γ nb u (Z.to_nat b)); [| lia].
    rewrite Hb {1}/pool_elt (bool_decide_eq_false_2 _ Hnu).
    iIntros "[$ Hrest]".
    rewrite (free_pool_split Γ nb (u ∪ {[b]}) (Z.to_nat b)); [| lia].
    rewrite Hb /pool_elt (bool_decide_eq_true_2 _ Hub).
    iSplitR; [done |].
    rewrite -(free_pool_but_eq Γ nb u (u ∪ {[b]}) (Z.to_nat b)); [done |].
    intros x Hx. rewrite Hb in Hx. set_solver.
  Qed.

  (* THE PANIC REFUTATION: a holder of block [b]'s bytes proves [b]'s bit
     reads ALLOCATED, because a clear bit would put a SECOND owner of those
     bytes in the pool.  Exclusivity, not a clause. *)
  Lemma free_pool_used Γ (Hex : phi_excl Γ) nb u (b : Z) bs :
    0 <= b < nb ->
    free_pool Γ nb u -∗ blk_owned Γ b bs -∗ ⌜b ∈ u⌝.
  Proof.
    intros [Hb0 Hbn].
    assert (Hb : Z.of_nat (Z.to_nat b) = b) by lia.
    destruct (decide (b ∈ u)) as [Hin | Hnot].
    { iIntros "_ _". iPureIntro. exact Hin. }
    rewrite (free_pool_split Γ nb u (Z.to_nat b)); [| lia].
    rewrite Hb {1}/pool_elt (bool_decide_eq_false_2 _ Hnot).
    iIntros "[Helt _] Hin".
    iDestruct "Helt" as (bs') "Helt".
    iDestruct (blk_owned_excl Γ Hex with "Helt Hin") as "[]".
  Qed.

  (* FREE: the block goes back into the pool and its bit is cleared. *)
  Lemma free_pool_give Γ (Hex : phi_excl Γ) nb u (b : Z) bs :
    0 <= b < nb ->
    blk_owned Γ b bs -∗ free_pool Γ nb u -∗ free_pool Γ nb (u ∖ {[b]}).
  Proof.
    intros [Hb0 Hbn].
    assert (Hb : Z.of_nat (Z.to_nat b) = b) by lia.
    assert (Hnb : b ∉ u ∖ {[b]}) by set_solver.
    iIntros "Hin Hpool".
    iDestruct (free_pool_used Γ Hex nb u b bs ltac:(lia)
                 with "Hpool Hin") as %Hin.
    rewrite (free_pool_split Γ nb u (Z.to_nat b)); [| lia].
    rewrite Hb.
    iDestruct "Hpool" as "[_ Hrest]".
    rewrite (free_pool_split Γ nb (u ∖ {[b]}) (Z.to_nat b)); [| lia].
    rewrite Hb /pool_elt (bool_decide_eq_false_2 _ Hnb).
    iSplitL "Hin"; [by iExists bs |].
    rewrite -(free_pool_but_eq Γ nb u (u ∖ {[b]}) (Z.to_nat b)); [| ].
    { iExact "Hrest". }
    intros x Hx. rewrite Hb in Hx. set_solver.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  Building a pool: boot's set-indexed form                         *)
  (* ---------------------------------------------------------------- *)

  (* the blocks below [nb] whose bit is CLEAR -- an INDEXING device for the
     one place a pool is built from scratch (the image, at boot), never a
     fact anybody maintains *)
  Definition free_set (nb : Z) (u : gset Z) : gset Z :=
    (list_to_set (seqZ 0 nb) : gset Z) ∖ u.

  Lemma elem_of_free_set (nb : Z) (u : gset Z) (x : Z) :
    x ∈ free_set nb u <-> (0 <= x < nb /\ x ∉ u).
  Proof.
    unfold free_set.
    rewrite elem_of_difference elem_of_list_to_set elem_of_seqZ.
    split.
    - intros [H1 H2]. split; [lia | exact H2].
    - intros [H1 H2]. split; [lia | exact H2].
  Qed.

  Lemma diff_int_split (X Y : gset Z) : X = (X ∖ Y) ∪ (X ∩ Y).
  Proof.
    apply set_eq. intros x.
    rewrite elem_of_union elem_of_difference elem_of_intersection.
    destruct (decide (x ∈ Y)); tauto.
  Qed.

  Lemma diff_int_disj (X Y : gset Z) : (X ∖ Y) ## (X ∩ Y).
  Proof.
    intros x Hx1 Hx2.
    apply elem_of_difference in Hx1 as [_ Hn].
    apply elem_of_intersection in Hx2 as [_ Hi]. exact (Hn Hi).
  Qed.

  Lemma free_pool_intro Γ (nb : Z) (u : gset Z) :
    ([∗ set] b ∈ free_set nb u, ∃ bs, blk_owned Γ b bs) ⊢ free_pool Γ nb u.
  Proof.
    rewrite /free_pool.
    rewrite -(big_sepS_list_to_set (fun b => pool_elt Γ u b) (seqZ 0 nb)
                (NoDup_seqZ 0 nb)).
    rewrite (diff_int_split (list_to_set (seqZ 0 nb) : gset Z) u).
    rewrite big_sepS_union; [| apply diff_int_disj].
    rewrite /free_set.
    iIntros "H". iSplitL "H".
    - iApply (big_sepS_mono with "H"). intros b Hb.
      apply elem_of_difference in Hb as [_ Hnu].
      rewrite /pool_elt (bool_decide_eq_false_2 _ Hnu). done.
    - iApply big_sepS_intro. iModIntro. iIntros (b Hb).
      apply elem_of_intersection in Hb as [_ Hin].
      rewrite /pool_elt (bool_decide_eq_true_2 _ Hin). done.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  The two movers, at the whole predicate                           *)
  (* ---------------------------------------------------------------- *)

  Lemma bitmap_alloc Γ (bms nb : Z) u (b : Z) :
    0 <= b < nb -> b ∉ u ->
    free_bitmap_at Γ bms nb u ⊢
      (∃ bs, blk_owned Γ b bs)
      ∗ blk_owned Γ bms (bm_bytes BSIZE u)
      ∗ (blk_owned Γ bms (bm_bytes BSIZE (u ∪ {[b]}))
         -∗ free_bitmap_at Γ bms nb (u ∪ {[b]})).
  Proof.
    intros Hrng Hnu. rewrite /free_bitmap_at (free_pool_take Γ nb u b Hrng Hnu).
    iIntros "(Hbm & Hblk & Hpool)". iFrame "Hblk Hbm".
    iIntros "$". iExact "Hpool".
  Qed.

  Lemma bitmap_free Γ (Hex : phi_excl Γ) (bms nb : Z) u (b : Z) bs :
    0 <= b < nb ->
    free_bitmap_at Γ bms nb u -∗ blk_owned Γ b bs -∗
      ⌜b ∈ u⌝
      ∗ blk_owned Γ bms (bm_bytes BSIZE u)
      ∗ (blk_owned Γ bms (bm_bytes BSIZE (u ∖ {[b]}))
         -∗ free_bitmap_at Γ bms nb (u ∖ {[b]})).
  Proof.
    intros Hrng. rewrite /free_bitmap_at.
    iIntros "(Hbm & Hpool) Hin".
    iDestruct (free_pool_used Γ Hex nb u b bs Hrng with "Hpool Hin") as %Hin.
    iSplitR; [done |]. iFrame "Hbm". iIntros "$".
    iApply (free_pool_give Γ Hex nb u b bs Hrng with "Hin Hpool").
  Qed.

End Bitmap.

(* the pool is a big-op over a block-count-sized index list; seal it for the
   same reason [byte_range] is sealed (durable-notes.md, the [iFrame] hang) *)
Global Typeclasses Opaque
  pool_elt free_pool free_pool_but free_bitmap_at free_bitmap.
