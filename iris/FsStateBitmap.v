(* FsStateBitmap.v -- the free-space state, CSL-style.

   Design of record: claude-notes/design/fs-state.md section 2,
   "[free_bitmap], CSL-style".

   [free_bitmap Γ sb u] owns the bitmap block, at its encoding [bm_bytes] of
   the set [u] of blocks IN USE (xv6: bit set = allocated, bit clear = free),
   AND, for every block whose bit reads FREE, THE BLOCK ITSELF, at arbitrary
   content.

   Two things fall out of that and neither is a maintained clause:

   - [bfree] hands a block in.  If the block's bit read free, [free_bitmap]
     would already own it -- two owners of one block's bytes, which is
     [False] by [blk_owned_excl].  So the bit reads allocated and the
     "freeing free block" panic arm is DEAD.  That is [bitmap_free] below,
     and it is the one place [phi_excl] is used.
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

  Definition free_bitmap Γ (sb : fs_sb) (u : gset Z) : iProp Σ :=
    (blk_owned Γ (sb_bmapstart sb) (bm_bytes BSIZE u)
     ∗ free_pool Γ (sb_size sb) u)%I.

  Global Instance pool_elt_timeless `{!GTimeless Γ} u b :
    Timeless (pool_elt Γ u b).
  Proof. rewrite /pool_elt. destruct (bool_decide (b ∈ u)); apply _. Qed.

  Global Instance free_pool_timeless `{!GTimeless Γ} nb u :
    Timeless (free_pool Γ nb u).
  Proof. rewrite /free_pool. apply _. Qed.

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
  (*  balloc: flip a free bit, take the block out of the pool          *)
  (* ---------------------------------------------------------------- *)

  Lemma bitmap_alloc Γ sb u (b : Z) :
    0 <= b < sb_size sb -> b ∉ u ->
    free_bitmap Γ sb u ⊢
      (∃ bs, blk_owned Γ b bs)
      ∗ blk_owned Γ (sb_bmapstart sb) (bm_bytes BSIZE u)
      ∗ (blk_owned Γ (sb_bmapstart sb) (bm_bytes BSIZE (u ∪ {[b]}))
         -∗ free_bitmap Γ sb (u ∪ {[b]})).
  Proof.
    intros [Hb0 Hbn] Hnu.
    assert (Hb : Z.of_nat (Z.to_nat b) = b) by lia.
    assert (Hub : b ∈ u ∪ {[b]}) by set_solver.
    rewrite /free_bitmap (free_pool_split Γ (sb_size sb) u (Z.to_nat b));
      [| lia].
    rewrite Hb {1}/pool_elt (bool_decide_eq_false_2 _ Hnu).
    iIntros "(Hbm & Hblk & Hrest)". iFrame "Hblk Hbm".
    iIntros "Hbm". iFrame "Hbm".
    rewrite (free_pool_split Γ (sb_size sb) (u ∪ {[b]}) (Z.to_nat b));
      [| lia].
    rewrite Hb /pool_elt (bool_decide_eq_true_2 _ Hub).
    iSplitR; [done |].
    rewrite -(free_pool_but_eq Γ (sb_size sb) u (u ∪ {[b]}) (Z.to_nat b));
      [done |].
    intros x Hx. rewrite Hb in Hx. set_solver.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  bfree: hand a block in.  The bit reads ALLOCATED by exclusivity. *)
  (* ---------------------------------------------------------------- *)

  Lemma bitmap_free Γ (Hex : phi_excl Γ) sb u (b : Z) bs :
    0 <= b < sb_size sb ->
    free_bitmap Γ sb u -∗ blk_owned Γ b bs -∗
      ⌜b ∈ u⌝
      ∗ blk_owned Γ (sb_bmapstart sb) (bm_bytes BSIZE u)
      ∗ (blk_owned Γ (sb_bmapstart sb) (bm_bytes BSIZE (u ∖ {[b]}))
         -∗ free_bitmap Γ sb (u ∖ {[b]})).
  Proof.
    intros [Hb0 Hbn].
    assert (Hb : Z.of_nat (Z.to_nat b) = b) by lia.
    assert (Hnb : b ∉ u ∖ {[b]}) by set_solver.
    rewrite /free_bitmap (free_pool_split Γ (sb_size sb) u (Z.to_nat b));
      [| lia].
    rewrite Hb.
    iIntros "(Hbm & Helt & Hrest) Hin".
    (* the panic refutation: if the bit read free the pool would own [b] *)
    destruct (decide (b ∈ u)) as [Hin | Hnot]; last first.
    { rewrite {1}/pool_elt (bool_decide_eq_false_2 _ Hnot).
      iDestruct "Helt" as (bs') "Helt".
      iDestruct (blk_owned_excl Γ Hex with "Helt Hin") as "[]". }
    iSplitR; [done |]. iFrame "Hbm". iIntros "Hbm". iFrame "Hbm".
    rewrite (free_pool_split Γ (sb_size sb) (u ∖ {[b]}) (Z.to_nat b));
      [| lia].
    rewrite Hb /pool_elt (bool_decide_eq_false_2 _ Hnb).
    iSplitL "Hin"; [by iExists bs |].
    rewrite -(free_pool_but_eq Γ (sb_size sb) u (u ∖ {[b]}) (Z.to_nat b));
      [done |].
    intros x Hx. rewrite Hb in Hx. set_solver.
  Qed.

End Bitmap.

(* the pool is a big-op over a block-count-sized index list; seal it for the
   same reason [byte_range] is sealed (durable-notes.md, the [iFrame] hang) *)
Global Typeclasses Opaque pool_elt free_pool free_pool_but free_bitmap.
