(* ====================================================================== *)
(*  FsCfgSnap.v -- THE ERA'S FILE-SYSTEM MINT, READ OFF THE DURABLE        *)
(*  SNAPSHOT (durable-fs-plan.md section 5; durable-disk lane E-mint).     *)
(*                                                                        *)
(*  [FsCfgBoot.fs_cfg_alloc] mints the era's file-system instance by       *)
(*  DECODING fs.img: every premise it takes is a conjunct of               *)
(*  [FsCfgBoot.fs_boot_image_wf], and every object it hands out is spelled *)
(*  at [FsImg.fs_dinode] / [FsCfgBoot.img_node].  That is what makes       *)
(*  [SystemAdequacy.Himg] load-bearing AT EVERY ERA rather than only at    *)
(*  era 0, because an era's disk is whatever the previous era wrote.       *)
(*                                                                        *)
(*  This file replaces the decoding by a READING OF THE DURABLE SNAPSHOT.  *)
(*  The mint's input becomes [FsDurSnap.snap_ok S D] -- "the committed map *)
(*  [D] is the encoding of the abstract state [S], every inode of [S] is   *)
(*  locally well formed, no two share a block" -- which the crash          *)
(*  predicate carries at EVERY era ([FsCrash.P_fs]'s durable snapshot,     *)
(*  read out as [SystemAdequacy.fs_boot_pure]) and which the IMAGE only    *)
(*  has to produce ONCE, at era 0 ([FsDurImg.img_snap_ok]).                *)
(*                                                                        *)
(*  WHAT IS HERE, bottom up:                                              *)
(*                                                                        *)
(*    1.  THE DECODE BRIDGE.  [snap_rec_decode]: at a named inum the       *)
(*        image DECODER's record IS the snapshot node's record.  It is     *)
(*        [FsDurSnap.sk_rec] against [FsDurImg.img_rec_in_blk] closed by   *)
(*        [FsDurSnap.rec_in_blk_inj], and it is the ONE place a byte fact  *)
(*        becomes a node fact.  Everything below reads [S] and never [P].  *)
(*    2.  [IcacheBoot.ireg_alloc]'s six decoding conjuncts, off            *)
(*        [FsStateInode.inode_local] and [FsDurSnap.sk_regdom].            *)
(*    3.  A NODE'S OWN BLOCKS as a [gset], with the carve's two facts      *)
(*        (each set is inside the home set, and two nodes' are disjoint)   *)
(*        off [FsDurSnap.snap_names_home] and [sk_disj].                   *)
(*    4.  The resource halves: [snap_inode_blocks_res] (one node's blocks  *)
(*        as [InodeInv.inode_blocks] + [ind_res]) and [bitmap_res_of_snap] *)
(*        (the bitmap block and the free pool as [BitmapInv.bitmap_res]).  *)
(*                                                                        *)
(*  NOTHING HERE COMPUTES.  Every lemma is generic in [P], [S] and the     *)
(*  home set; the literal image enters only through the era-0 corollary.   *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list sets bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac excl.
From iris.base_logic.lib Require Import invariants own ghost_map ghost_var mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvModelBytes.
Require Import FsState.
Require Import FsStateDefs FsStateInode FsStateBitmap FsStateEra.
Require Import FsBlocks FsBytesGamma.
Require Import DinodeEnc DirView.
Require Import FsCrash LogDefs.
Require Import InodeInv InodeLock InodeRegion.
Require Import IcacheEscrow IcacheBoot.
Require Import BitmapEnc BitmapInv.
Require Import FsImg FsImgBridge.
Require Import FsDurSnap FsDurImg.
Require Import FsBoot FsCfgBoot.
Require Import Xv6G.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE DECODE BRIDGE                                                  *)
(* ====================================================================== *)

(*  The image's DECODER at inum [i] reads the 64 bytes of block            *)
(*  [inodestart + i/16] at offset [64 * (i mod 16)]; [FsDurSnap.sk_rec]    *)
(*  says the snapshot node's record sits in exactly those bytes; and       *)
(*  [rec_in_blk_inj] says a well-formed record is determined by them.      *)
(*  So at a named inum the two are ONE record -- which is what lets every  *)
(*  premise [FsCfgBoot] discharges off an image sweep be discharged off    *)
(*  [FsStateInode.inode_local] instead.                                    *)
Lemma snap_rec_decode (S : fs_state_rec) (P : Z -> list (bv 8))
    (home : gset Z) (i : Z) (n : fs_node) :
  fs_blocks_full P ->
  snap_bytes S (fs_restrict P home) ->
  fss_inodes S !! i = Some n ->
  fs_dinode P (fss_sb S) i = fn_rec n.
Proof.
  intros Hfull Hb Hi.
  destruct (sk_rec Hb i n Hi) as (bs & Hbs & Hin).
  apply fs_restrict_lookup_Some in Hbs as [_ ->].
  pose proof (sk_inum Hb i n Hi) as Hran.
  pose proof (img_rec_in_blk P (fss_sb S) i Hfull Hran) as Hin2.
  exact (rec_in_blk_inj _ _ (fs_dinode P (fss_sb S) i) (fn_rec n)
           (fs_dinode_wf P (fss_sb S) i)
           (inr_rec_wf (sk_repr Hb i n Hi)) Hin2 Hin).
Qed.

(*  ...and the same at the region's OWN width, where [sk_regdom] is what   *)
(*  says the inum is named at all.  This is the form every consumer below  *)
(*  uses: [nib] is the caller's region width, tied to [S]'s superblock.    *)
Definition snap_node (S : fs_state_rec) (z : Z) : fs_node :=
  fss_inodes S !!! z.

Lemma snap_node_at (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (nib : nat) (z : Z) :
  snap_bytes S D ->
  Z.of_nat nib = sb_ninodes (fss_sb S) / 16 + 1 ->
  z ∈ region_inums nib ->
  fss_inodes S !! z = Some (snap_node S z).
Proof.
  intros Hb Hw Hz. apply region_inums_spec in Hz.
  destruct (sk_regdom Hb z ltac:(lia)) as [n Hn].
  rewrite /snap_node (lookup_total_correct _ _ _ Hn) //.
Qed.

Lemma snap_rec_decode_region (S : fs_state_rec) (P : Z -> list (bv 8))
    (home : gset Z) (nib : nat) (z : Z) :
  fs_blocks_full P ->
  snap_bytes S (fs_restrict P home) ->
  Z.of_nat nib = sb_ninodes (fss_sb S) / 16 + 1 ->
  z ∈ region_inums nib ->
  fs_dinode P (fss_sb S) z = fn_rec (snap_node S z).
Proof.
  intros Hfull Hb Hw Hz.
  exact (snap_rec_decode S P home z (snap_node S z) Hfull Hb
           (snap_node_at S (fs_restrict P home) nib z Hb Hw Hz)).
Qed.

(* ====================================================================== *)
(*  2.  [IcacheBoot.ireg_alloc]'s SIX DECODING CONJUNCTS                   *)
(*                                                                        *)
(*  [FsCfgBoot.image_ireg_premises] proves these from [FsImg.fsimg_wf] +   *)
(*  [fs_region_wf] + [fs_region_bare].  Off the snapshot every one of them *)
(*  is a clause of [FsStateInode.inode_local] at the node [sk_regdom]      *)
(*  names, and no sweep is spent: [image_free_nlink] is [inl_free],        *)
(*  [image_nlink_short] is [inl_nlink], [image_ty_ok] is [inl_type],       *)
(*  [image_bare] is [inl_bare_free] read through                           *)
(*  [InodeRegion.ireg_bare_of_fn_bare], and the two indexing equations are *)
(*  the decode bridge.                                                    *)
(* ====================================================================== *)

Lemma snap_ireg_premises (S : fs_state_rec) (P : Z -> list (bv 8))
    (home : gset Z) (dss : list (list dinode)) (nib : nat) :
  fs_blocks_full P ->
  snap_bytes S (fs_restrict P home) ->
  snap_local S ->
  Z.of_nat nib = sb_ninodes (fss_sb S) / 16 + 1 ->
  16 * Z.of_nat nib <= 2 ^ 32 ->
  length dss = nib -> Forall diblk_wf dss ->
  (forall bi : nat, (bi < nib)%nat ->
     P (sb_inodestart (fss_sb S) + Z.of_nat bi) = diblk_bytes (dss !!! bi)) ->
  image_free_nlink dss nib /\ image_nlink_short dss nib
  /\ image_ty_ok dss nib
  /\ image_nlink_at (fun z => fn_nlink (snap_node S z)) dss nib
  /\ image_bare dss nib
  /\ image_rec_at (fun z => fn_rec (snap_node S z)) dss nib.
Proof.
  intros Hfull Hb Hloc Hw Hnib Hl Hdwf He.
  (* the decoded record IS the snapshot node's record, at every region inum *)
  assert (Hbr : forall z : Z, z ∈ region_inums nib ->
            image_dinode dss z = fn_rec (snap_node S z)).
  { intros z Hz.
    rewrite (image_dinode_fs_dinode P (fss_sb S) dss nib z Hl Hdwf He
               (proj1 (region_inums_spec nib z) Hz) Hnib).
    exact (snap_rec_decode_region S P home nib z Hfull Hb Hw Hz). }
  assert (Hln : forall z : Z, z ∈ region_inums nib ->
            inode_local z (snap_node S z)).
  { intros z Hz.
    exact (Hloc z (snap_node S z)
             (snap_node_at S (fs_restrict P home) nib z Hb Hw Hz)). }
  split.
  { (* (L1) a free record has no links *)
    intros z Hz Hty. rewrite (Hbr z Hz). rewrite (Hbr z Hz) in Hty.
    pose proof (inl_free (Hln z Hz) Hty) as Hnl.
    rewrite /fn_nlink in Hnl.
    pose proof (proj1 (bv_unsigned_in_range _
                         (di_nlink (fn_rec (snap_node S z))))) as Hnn.
    lia. }
  split.
  { (* (L4) the link count is a non-negative short *)
    intros z Hz. rewrite (Hbr z Hz). exact (inl_nlink (Hln z Hz)). }
  split.
  { (* (L5) the type enumeration *)
    intros z Hz. rewrite (Hbr z Hz).
    destruct (inl_type (Hln z Hz)) as [H | [H | [H | H]]];
      rewrite /ireg_ty_ok; rewrite /fn_type in H.
    - by left.
    - by right; left.
    - by right; right; left.
    - by right; right; right. }
  split.
  { (* the link RA's tie *)
    intros z Hz. rewrite /ireg_nl (Hbr z Hz) /fn_nlink //. }
  split.
  { (* conjunct (14): a free record is bare *)
    intros z Hz Hty. rewrite (Hbr z Hz). rewrite (Hbr z Hz) in Hty.
    exact (ireg_bare_of_fn_bare (snap_node S z)
             (inl_bare_free (Hln z Hz) Hty)). }
  (* ...and the record function the park is indexed by *)
  intros z Hz. rewrite (Hbr z Hz) //.
Qed.

(* ====================================================================== *)
(*  3.  A NODE'S OWN BLOCKS, AS A SET                                      *)
(*                                                                        *)
(*  [FsCfgBoot]'s carve is set-shaped: [FsBoot.big_sepS_carve] hands each  *)
(*  live inode its own [gset] of blocks out of the boot thread's home      *)
(*  ledger and keeps the remainder.  [FsImg.fs_inode_blocks_set] is the    *)
(*  image's spelling; this is the snapshot's, and its two carve facts are  *)
(*  [FsDurSnap.snap_names_home] (each set is inside the home set) and      *)
(*  [sk_disj] (two nodes' sets are disjoint).                              *)
(* ====================================================================== *)

(*  [FsStateEra.bm_of_slot] reads a node's blkmap slot at [InodeInv]'s     *)
(*  [MAXFILE] while [FsDurSnap.fn_slot] spells the same thing at           *)
(*  [FsImg]'s [FS_MAXFILE].  The two constants are equal by conversion but *)
(*  not syntactically, and a [rewrite] cannot see through that -- so the   *)
(*  bridge is named once (durable-notes.md, "rewrite can fail on a subterm *)
(*  that prints character-for-character").                                 *)
Lemma bm_of_slot_fn (n : fs_node) (k : nat) :
  dinode_wf (fn_rec n) -> (k <= MAXFILE)%nat ->
  bv_unsigned (bm_slot (bm_of n) k) = fn_slot n k.
Proof.
  intros Hwf Hk. rewrite (bm_of_slot n k Hwf Hk) /fn_slot -MAXFILE_FS //.
Qed.

Definition snap_blk_set (n : fs_node) : gset Z :=
  set_map (fn_naddr n) (dom (fn_blk n))
  ∪ (if decide (fn_indb n = 0) then ∅ else {[ fn_indb n ]}).

Lemma elem_of_snap_blk_set (n : fs_node) (b : Z) :
  b ∈ snap_blk_set n <-> fn_owns n b.
Proof.
  rewrite /snap_blk_set /fn_owns elem_of_union elem_of_map.
  split.
  - intros [(k & -> & Hk) | Hi].
    + left. exists k. rewrite elem_of_dom in Hk. split; [exact Hk | reflexivity].
    + right. destruct (decide (fn_indb n = 0)) as [Hz | Hnz].
      * exfalso. exact (not_elem_of_empty b Hi).
      * apply elem_of_singleton in Hi as ->. split; [exact Hnz | reflexivity].
  - intros [(k & Hk & Heq) | [Hnz Heq]].
    + left. exists k. split; [by symmetry | by apply elem_of_dom].
    + right. rewrite decide_False; [| exact Hnz].
      apply elem_of_singleton. by symmetry.
Qed.

Lemma snap_blk_set_home (S : fs_state_rec) (P : Z -> list (bv 8))
    (home : gset Z) (i : Z) (n : fs_node) :
  snap_bytes S (fs_restrict P home) ->
  fss_inodes S !! i = Some n ->
  snap_blk_set n ⊆ home.
Proof.
  intros Hb Hi. apply elem_of_subseteq. intros b Hbb.
  apply elem_of_snap_blk_set in Hbb.
  apply (snap_names_home S P home b Hb). right; left. by exists i, n.
Qed.

Lemma snap_blk_set_disj (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (i j : Z) (n m : fs_node) :
  snap_bytes S D ->
  fss_inodes S !! i = Some n -> fss_inodes S !! j = Some m ->
  i <> j -> snap_blk_set n ## snap_blk_set m.
Proof.
  intros Hb Hi Hj Hne b Hn Hm.
  apply elem_of_snap_blk_set in Hn. apply elem_of_snap_blk_set in Hm.
  exact (Hne (sk_disj Hb i n j m b Hi Hj Hn Hm)).
Qed.

(* ...and the whole live set's, which is what the remainder is stated at *)
Definition snap_live_blocks (S : fs_state_rec) (A : gset Z) : gset Z :=
  ⋃ ((fun i => snap_blk_set (snap_node S i)) <$> elements A).

Lemma elem_of_snap_live_blocks (S : fs_state_rec) (A : gset Z) (b : Z) :
  b ∈ snap_live_blocks S A
  <-> exists i : Z, i ∈ A /\ b ∈ snap_blk_set (snap_node S i).
Proof.
  rewrite /snap_live_blocks elem_of_union_list. split.
  - intros (X & HX & Hb). apply elem_of_list_fmap in HX as (i & -> & Hi).
    apply elem_of_elements in Hi. by exists i.
  - intros (i & Hi & Hb). exists (snap_blk_set (snap_node S i)). split.
    + apply elem_of_list_fmap. exists i. split; [reflexivity |].
      by apply elem_of_elements.
    + exact Hb.
Qed.

(* ====================================================================== *)
(*  4.  THE RESOURCE HALVES                                                *)
(* ====================================================================== *)

(*  THE BITMAP BLOCK AND THE FREE POOL, off [sk_bmap] / [sk_pool] /        *)
(*  [sk_meta_used].  [FsCfgBoot.bitmap_res_of_image]'s twin, and shorter:  *)
(*  the disjointness of the bitmap block from the pool is [sk_meta_used]   *)
(*  ("the bitmap block's bit reads IN USE") rather than an arithmetic      *)
(*  argument about the data region, and the byte-level equation is         *)
(*  [sk_bmap] itself rather than [FsImg.bm_bytes_fs_bmap_set].             *)
Definition snap_bitmap_spent (S : fs_state_rec) : gset Z :=
  {[ sb_bmapstart (fss_sb S) ]}
  ∪ free_set (sb_size (fss_sb S)) (fss_used S).

Section SnapRes.
  Context `{!riscvGS Σ, !xv6G Σ}.

  Lemma bitmap_res_of_snap (γfs : fs_names) (S : fs_state_rec)
      (P : Z -> list (bv 8)) (home : gset Z) :
    snap_bytes S (fs_restrict P home) ->
    ([∗ set] b ∈ snap_bitmap_spent S, fsblock (fs_bytes γfs) b (P b)) -∗
    bitmap_res γfs (sb_bmapstart (fss_sb S)) (sb_size (fss_sb S))
      (fss_used S).
  Proof.
    intros Hb. iIntros "H".
    (* the bitmap block is IN USE, so it is not in the free pool *)
    assert (Hdj : ({[ sb_bmapstart (fss_sb S) ]} : gset Z)
                  ## free_set (sb_size (fss_sb S)) (fss_used S)).
    { apply disjoint_singleton_l. intros Hin.
      apply elem_of_free_set in Hin as [_ Hnu].
      apply Hnu. apply (sk_meta_used Hb). right. by left. }
    (* the byte-level equation is [sk_bmap] read through [fs_restrict] *)
    assert (Hbytes : P (sb_bmapstart (fss_sb S))
                     = bm_bytes BSIZE (fss_used S)).
    { pose proof (sk_bmap Hb) as Hm.
      apply fs_restrict_lookup_Some in Hm as [_ Hm]. by rewrite Hm. }
    rewrite /snap_bitmap_spent (big_sepS_union _ _ _ Hdj) big_sepS_singleton.
    iDestruct "H" as "[Hbm Hpool]".
    rewrite /bitmap_res /free_bitmap_at.
    iSplitL "Hbm".
    { rewrite -gamma_blk_owned -Hbytes. iExact "Hbm". }
    iApply free_pool_intro.
    iApply (big_sepS_mono with "Hpool"). intros b Hbb.
    iIntros "Hf". iExists (P b). rewrite -gamma_blk_owned. iExact "Hf".
  Qed.

  (*  ONE NODE'S BLOCKS, in the [InodeInv] vocabulary.                      *)
  (*  [InodeInv.inode_blocks_of_blocks] is generic; its four premises come  *)
  (*  off [FsStateInode.inode_local] ([inl_blk_dom] for "a nonzero slot is  *)
  (*  owned"), [FsDurSnap.sk_slot] (the slot injectivity) and               *)
  (*  [sk_blk]/[sk_ind] (the slot's bytes ARE the block's).                 *)
  Lemma snap_inode_blocks_res (γfs : fs_names) (S : fs_state_rec)
      (P : Z -> list (bv 8)) (home : gset Z) (i : Z) (n : fs_node) :
    snap_bytes S (fs_restrict P home) ->
    inode_local i n ->
    fss_inodes S !! i = Some n ->
    ([∗ set] b ∈ snap_blk_set n, fsblock (fs_bytes γfs) b (P b)) -∗
    inode_blocks γfs (bm_of n) (fn_data n) ∗ ind_res γfs (bm_of n).
  Proof.
    intros Hb Hl Hi.
    pose proof (inl_rec_wf Hl) as Hwf.
    (* the two spellings of 268 are equal by conversion and opaque to
       [lia]; naming the equation is what lets every index side goal below
       run as plain arithmetic *)
    pose proof MAXFILE_FS as HMF.
    apply (inode_blocks_of_blocks γfs (bm_of n) (snap_blk_set n) P
             (fn_data n)).
    - (* the slot injectivity *)
      intros k j Hk Hj Hnz Heq.
      apply (sk_slot Hb i n Hi k j ltac:(lia) ltac:(lia)).
      + rewrite -(bm_of_slot_fn n k Hwf Hk). exact Hnz.
      + rewrite -(bm_of_slot_fn n k Hwf Hk) -(bm_of_slot_fn n j Hwf Hj).
        by rewrite Heq.
    - (* a nonzero slot is one of the node's own blocks *)
      intros k Hk Hnz.
      rewrite (bm_of_slot_fn n k Hwf Hk) in Hnz.
      rewrite (bm_of_slot_fn n k Hwf Hk).
      apply elem_of_snap_blk_set.
      destruct (decide (k = FS_MAXFILE)) as [-> | Hne].
      + rewrite fn_slot_ind in Hnz. rewrite fn_slot_ind.
        right. split; [exact Hnz | reflexivity].
      + rewrite (fn_slot_data n k ltac:(lia)) in Hnz.
        rewrite (fn_slot_data n k ltac:(lia)).
        left. exists k. split; [| reflexivity].
        exact (proj2 (inl_blk_dom Hl k ltac:(lia)) Hnz).
    - (* the slot's data IS the block's bytes *)
      intros k Hk Hnz.
      rewrite (bm_of_get n k Hwf Hk) in Hnz |- *.
      destruct (proj2 (inl_blk_dom Hl k ltac:(lia)) Hnz) as [bs Hbs].
      pose proof (sk_blk Hb i n k bs Hi Hbs) as Hd.
      apply fs_restrict_lookup_Some in Hd as [_ ->].
      rewrite /fn_data Hbs //.
    - (* ...and the indirect block's *)
      rewrite bm_of_ent bm_of_ind. intros Hnz.
      pose proof (sk_ind Hb i n Hi Hnz) as Hd.
      apply fs_restrict_lookup_Some in Hd as [_ ->]. reflexivity.
  Qed.

End SnapRes.
