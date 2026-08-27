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
Require Import DinodeEnc DirView FsTree.
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

(* ====================================================================== *)
(*  5.  THE WHOLE [inode_ok], AT THE SNAPSHOT'S NODE                       *)
(*                                                                        *)
(*  [FsStateEra.inode_ok_of_local] takes [inode_local] plus the two facts  *)
(*  OWNERSHIP -- not a clause -- produces: the coverage / log-disjointness *)
(*  pair and the slot injectivity.  Off the snapshot they are             *)
(*  [FsDurSnap.snap_names_cov] (every block the snapshot names is a HOME   *)
(*  block, hence covered and outside the log region -- section 9a's own    *)
(*  bookkeeping) and [sk_slot].  So the mint owes no new clause for either *)
(*  half, and [FsImgBridge.img_inode_ok]'s image sweep has no reader left. *)
(* ====================================================================== *)

Lemma fn_slot_owns (i : Z) (n : fs_node) (k : nat) :
  inode_local i n -> (k <= FS_MAXFILE)%nat -> fn_slot n k <> 0 ->
  fn_owns n (fn_slot n k).
Proof.
  intros Hl Hk Hnz.
  destruct (decide (k = FS_MAXFILE)) as [-> | Hne].
  - rewrite fn_slot_ind. rewrite fn_slot_ind in Hnz.
    right. split; [exact Hnz | reflexivity].
  - rewrite (fn_slot_data n k ltac:(lia)).
    rewrite (fn_slot_data n k ltac:(lia)) in Hnz.
    left. exists k. split; [| reflexivity].
    exact (proj2 (inl_blk_dom Hl k ltac:(lia)) Hnz).
Qed.

Lemma snap_inode_ok (S : fs_state_rec) (P : Z -> list (bv 8))
    (cov : gset Z) (ls : Z) (i : Z) (n : fs_node) :
  snap_bytes S (fs_restrict P (fs_home_set cov ls)) ->
  inode_local i n ->
  fss_inodes S !! i = Some n ->
  fn_type n <> 0 ->
  inode_ok cov ls (fn_rec n) (bm_of n) (fn_data n).
Proof.
  intros Hb Hl Hi Hty.
  pose proof (inl_rec_wf Hl) as Hwf.
  pose proof MAXFILE_FS as HMF.
  apply (inode_ok_of_local i n cov ls Hl).
  - (* coverage and log-disjointness, off [snap_names_cov] *)
    intros k Hk Hnz.
    rewrite (bm_of_slot_fn n k Hwf Hk) in Hnz.
    rewrite (bm_of_slot_fn n k Hwf Hk).
    apply (snap_names_cov S P cov ls (fn_slot n k) Hb).
    right; left. exists i, n. split; [exact Hi |].
    exact (fn_slot_owns i n k Hl ltac:(lia) Hnz).
  - (* the slot injectivity, off [sk_slot] *)
    intros k j Hk Hj Hnz Heq.
    apply (sk_slot Hb i n Hi k j ltac:(lia) ltac:(lia)).
    + rewrite -(bm_of_slot_fn n k Hwf Hk). exact Hnz.
    + rewrite -(bm_of_slot_fn n k Hwf Hk) -(bm_of_slot_fn n j Hwf Hj).
      by rewrite Heq.
  - exact Hty.
Qed.

(* ====================================================================== *)
(*  6.  THE TYPE REGISTER, ROUTED OFF [FsState.fs_links]                   *)
(*                                                                        *)
(*  [FsCfgBoot.ireg_lnks_of_image] cuts the boot's FULL family (every      *)
(*  inum's authority with all its fragments still at home) into the        *)
(*  region's authorities, the root's keep-alive and the directories'       *)
(*  tickets, and it spends [FsImg]'s W9 arithmetic to do it.  Off the      *)
(*  snapshot there is nothing to cut: [FsDurSnap.sk_links] IS              *)
(*  [FsState.fs_boot_alloc_root_slack]'s premise, so ONE [own_alloc]       *)
(*  yields [fs_links] -- each inum's authority beside exactly the          *)
(*  fragments its OWN entries claim -- plus the root's spare token, and    *)
(*  [FsStateInode.inode_link_iff] is the whole of the routing.             *)
(*                                                                        *)
(*  The two arithmetic bridges are equations between spellings:            *)
(*  [FsStateInode.fn_mult] IS [InodeRegion.ireg_mult_at] at the node's own *)
(*  count and type, and [fn_ity_ok] IS [ireg_reg_ok].                      *)
(*                                                                        *)
(*  THE ROOT'S KEEP-ALIVE IS AT THE AUTHORITY'S OWN VALUE, and it is not   *)
(*  assumed: [sk_links] binds the slack fragment's value existentially and *)
(*  [FsStateLink.link_auth_tok_agree] reads it off the root's own          *)
(*  authority -- one fragment's element IS the target's type.              *)
(* ====================================================================== *)

Lemma fn_mult_ireg (n : fs_node) :
  fn_mult n = ireg_mult_at (fn_nlink n) (fn_type n).
Proof. reflexivity. Qed.

Lemma fn_ity_ok_ireg (n : fs_node) (v : ity) :
  fn_ity_ok n v -> ireg_reg_ok (fn_type n) v.
Proof.
  destruct v as [| p]; rewrite /fn_ity_ok /ireg_reg_ok /fn_is_dir.
  - intros Hf. exact (proj1 (bool_decide_eq_false _) Hf).
  - intros Hf. exact (proj1 (bool_decide_eq_true _) Hf).
Qed.

Section SnapLinks.
  Context `{!riscvGS Σ, !xv6G Σ}.

  (*  A big-op over a MAP, read at its DOMAIN.  [FsCfgBoot]'s
      [big_sepM_img_nodes] is this equation at the image's own node map,
      where the domain is [region_inums] by construction; off the snapshot
      the state's domain is only known to CONTAIN the region
      ([FsDurSnap.sk_regdom]), so the general form is what is needed. *)
  Lemma big_sepM_as_set {A : Type} `{Inhabited A}
      (m : gmap Z A) (Phi : Z -> A -> iProp Σ) :
    ([∗ map] i ↦ x ∈ m, Phi i x) ⊣⊢ ([∗ set] z ∈ dom m, Phi z (m !!! z)).
  Proof.
    induction m as [| k v m Hk IH] using map_ind.
    { rewrite dom_empty_L big_sepM_empty big_sepS_empty //. }
    assert (Hkd : k ∉ dom m) by (apply not_elem_of_dom; exact Hk).
    rewrite (big_sepM_insert Phi m k v Hk).
    rewrite dom_insert_L.
    rewrite (big_sepS_insert
               (fun z => Phi z (<[k := v]> m !!! z)) (dom m) k Hkd).
    rewrite lookup_total_insert.
    rewrite IH. f_equiv.
    apply big_sepS_proper. intros z Hz.
    assert (Hzk : k <> z) by (intros <-; exact (Hkd Hz)).
    rewrite lookup_total_insert_ne; [done | exact Hzk].
  Qed.

  Lemma snap_links_to_set (γfs : fs_names) (S : fs_state_rec)
      (D : gmap Z (list (bv 8))) (nib : nat) :
    snap_bytes S D ->
    Z.of_nat nib = sb_ninodes (fss_sb S) / 16 + 1 ->
    fs_links (fs_link γfs) (fss_inodes S) -∗
    [∗ set] z ∈ region_inums nib,
      fs_link_node (fs_link γfs) z (snap_node S z).
  Proof.
    intros Hb Hw.
    assert (Hsub : region_inums nib ⊆ dom (fss_inodes S)).
    { apply elem_of_subseteq. intros z Hz.
      apply elem_of_dom.
      apply region_inums_spec in Hz. apply (sk_regdom Hb z). lia. }
    rewrite /fs_links big_sepM_as_set.
    iIntros "H".
    iDestruct (big_sepS_subseteq _ _ _ Hsub with "H") as "H".
    iExact "H".
  Qed.

  (*  THE ROUTING.  Each inum's contribution splits into the region's
      per-inum authority (with the root's keep-alive parked on it) and the
      directory's own entry tickets, which are what the free pool's bundle
      carries as [IcacheEscrow.dlinks]. *)
  Lemma snap_link_route (γfs : fs_names) (S : fs_state_rec)
      (D : gmap Z (list (bv 8))) (nib : nat) (v0 : ity) :
    snap_bytes S D ->
    Z.of_nat nib = sb_ninodes (fss_sb S) / 16 + 1 ->
    (0 < nib)%nat ->
    fs_links (fs_link γfs) (fss_inodes S) -∗
    link_tok (fs_gamma_L γfs) ireg_root v0 -∗
      ([∗ set] z ∈ region_inums nib,
         ireg_lnk_at γfs z (fn_nlink (snap_node S z))
                     (fn_type (snap_node S z)))
      ∗ ([∗ set] z ∈ region_inums nib,
           ent_toks_x (fs_gamma_L γfs) z (snap_node S z)).
  Proof.
    intros Hb Hw Hnib.
    assert (Hroot : ireg_root ∈ region_inums nib).
    { apply region_inums_spec. rewrite /ireg_root. lia. }
    iIntros "Hl Ht".
    iDestruct (snap_links_to_set γfs S D nib Hb Hw with "Hl") as "Hl".
    rewrite -big_sepS_sep.
    (* the two [Phi]s are SPELLED OUT: [big_sepS_delete]'s left-hand side is
       a big-op at an evar predicate, and ssreflect's [rewrite] does not
       solve that higher-order pattern under the proofmode's [envs_entails]. *)
    rewrite (big_sepS_delete
               (fun z => (ireg_lnk_at γfs z (fn_nlink (snap_node S z))
                            (fn_type (snap_node S z))
                          ∗ ent_toks_x (fs_gamma_L γfs) z (snap_node S z))%I)
               (region_inums nib) ireg_root Hroot).
    iEval (rewrite (big_sepS_delete
                      (fun z => fs_link_node (fs_link γfs) z (snap_node S z))
                      (region_inums nib) ireg_root Hroot))
      in "Hl".
    iDestruct "Hl" as "[Hr Hrest]".
    iSplitL "Hr Ht".
    - (* THE ROOT: the keep-alive rides the authority *)
      iDestruct (inode_link_iff (fs_gamma_L γfs) ireg_root
                   (snap_node S ireg_root)) as "[_ Hback]".
      iDestruct ("Hback" with "Hr") as "[Hav Htk]".
      iDestruct "Hav" as (v) "[%Hv Ha]".
      iDestruct (link_auth_tok_agree with "Ha Ht") as %[-> _].
      iSplitR "Htk"; [| iExact "Htk"].
      rewrite /ireg_lnk_at. iExists v.
      iSplitR; [iPureIntro; exact (fn_ity_ok_ireg _ v Hv) |].
      rewrite -fn_mult_ireg. iSplitL "Ha"; [iExact "Ha" |].
      rewrite /ireg_keep (bool_decide_eq_true_2 (ireg_root = ireg_root) eq_refl).
      iExact "Ht".
    - (* EVERY OTHER INUM: the keep-alive is [emp] *)
      iApply (big_sepS_mono with "Hrest"). intros z Hz.
      assert (Hne : z <> ireg_root).
      { apply elem_of_difference in Hz as [_ Hn]. intros ->.
        apply Hn, elem_of_singleton. reflexivity. }
      iIntros "H".
      iDestruct (inode_link_iff (fs_gamma_L γfs) z (snap_node S z))
        as "[_ Hback]".
      iDestruct ("Hback" with "H") as "[Hav Htk]".
      iDestruct "Hav" as (v) "[%Hv Ha]".
      iSplitR "Htk"; [| iExact "Htk"].
      rewrite /ireg_lnk_at. iExists v.
      iSplitR; [iPureIntro; exact (fn_ity_ok_ireg _ v Hv) |].
      rewrite -fn_mult_ireg. iSplitL "Ha"; [iExact "Ha" |].
      rewrite /ireg_keep (bool_decide_eq_false_2 (z = ireg_root) Hne). done.
  Qed.

End SnapLinks.

(* ====================================================================== *)
(*  7.  THE FREE POOL, STOCKED FROM THE SNAPSHOT                           *)
(*                                                                        *)
(*  [FsCfgBoot.ipool_alloc_of_image]'s twin.  Every per-inum obligation    *)
(*  [IcacheBoot.ipool_alloc] carries is a reading of [snap_ok] at the      *)
(*  inum's own node: [InodeLock.inode_ok] is section 5,                     *)
(*  [FsStateEra.inode_rec_local] and [FsTree.dir_uniq] are                  *)
(*  [FsStateInode.inode_local] clauses, the three [DirView] premises are   *)
(*  [FsDurSnap.snap_node_dir_local] (which is [sk_dirloc]), and the block  *)
(*  resources are section 4's [snap_inode_blocks_res].  The node's own     *)
(*  [(dn, bm, data)] decomposition is [FsStateEra.bm_of] / [fn_data], and  *)
(*  [FsStateEra.era_node_bm_of] is what says it rebuilds the very node.    *)
(* ====================================================================== *)

Lemma dir_uniq_of_local (i : Z) (n : fs_node) :
  inode_local i n -> dir_uniq (fn_rec n) (fn_data n).
Proof.
  intros Hl Hty. apply (inl_dir_uniq Hl).
  rewrite /fn_is_dir. exact (bool_decide_eq_true_2 _ Hty).
Qed.

Section SnapPool.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, ICFG : icfg, !irefslotG Σ}.
  Context `{GEN : GenId}.

  Lemma ipool_alloc_of_snap (γfs : fs_names) (γi : gname)
      (S : fs_state_rec) (P : Z -> list (bv 8)) (cov C A : gset Z) :
    snap_ok S (fs_restrict P (fs_home_set cov (sb_logstart (fss_sb S)))) ->
    Z.of_nat icfg_nib = sb_ninodes (fss_sb S) / 16 + 1 ->
    16 * Z.of_nat icfg_nib <= 2 ^ 32 ->
    (* the live set as a PARAMETER, exactly as the image route takes it *)
    (forall z : Z, z ∈ A <-> z ∈ region_inums icfg_nib
                             /\ fn_type (snap_node S z) <> 0) ->
    (* the carve's corner: each live node's own blocks are inside [C] *)
    (forall z : Z, z ∈ A -> snap_blk_set (snap_node S z) ⊆ C) ->
    ([∗ set] z ∈ region_inums icfg_nib, icnt_half z 0%nat) -∗
    ([∗ set] z ∈ region_inums icfg_nib, frzm_h z false) -∗
    ([∗ set] z ∈ region_inums icfg_nib, ifreeze_off z) -∗
    ([∗ set] z ∈ region_inums icfg_nib,
       dv_ride z (dv_of (fn_rec (snap_node S z)) (fn_data (snap_node S z)))) -∗
    ([∗ set] z ∈ region_inums icfg_nib,
       fv_ride z (fv_of (fn_rec (snap_node S z)) (fn_data (snap_node S z)))) -∗
    ([∗ set] z ∈ A, top_frag (fs_gamma_L γfs) z (snap_node S z)) -∗
    ([∗ set] z ∈ region_inums icfg_nib,
       ireg_out γi (mword_of_int z : mword 32) (fn_rec (snap_node S z))) -∗
    ([∗ set] z ∈ A, ent_toks_x (fs_gamma_L γfs) z (snap_node S z)) -∗
    ([∗ set] b ∈ C, fsblock (fs_bytes γfs) b (P b)) -∗
    ipool_rows γfs γi cov (sb_logstart (fss_sb S)) (region_inums icfg_nib)
      ∗ ([∗ set] b ∈ C ∖ snap_live_blocks S A,
           fsblock (fs_bytes γfs) b (P b)).
  Proof.
    intros Hok Hw Hnib HA HC.
    iIntros "Hcnt Hmir Hoff Hdv Hfv Htop Hout Hdlk Hblk".
    pose proof (sk_bytes Hok) as Hb.
    pose proof (sk_local Hok) as Hloc.
    assert (HARs : A ⊆ region_inums icfg_nib).
    { apply elem_of_subseteq. intros z Hz.
      exact (proj1 (proj1 (HA z) Hz)). }
    assert (Hty : forall z : Z, z ∈ A -> fn_type (snap_node S z) <> 0)
      by (intros z Hz; exact (proj2 (proj1 (HA z) Hz))).
    assert (Hnode : forall z : Z, z ∈ region_inums icfg_nib ->
              fss_inodes S !! z = Some (snap_node S z))
      by (intros z Hz;
          exact (snap_node_at S _ icfg_nib z Hb Hw Hz)).
    assert (Hln : forall z : Z, z ∈ region_inums icfg_nib ->
              inode_local z (snap_node S z))
      by (intros z Hz; exact (Hloc z (snap_node S z) (Hnode z Hz))).
    assert (Hfree : forall z : Z, z ∈ region_inums icfg_nib -> z ∉ A ->
              fn_type (snap_node S z) = 0).
    { intros z Hz Hna.
      destruct (decide (fn_type (snap_node S z) = 0)) as [H0 | H0];
        [exact H0 |].
      exfalso. apply Hna, (proj2 (HA z)). split; [exact Hz | exact H0]. }
    (* ---- the ledger columns, shifted onto the pool's keys ------------ *)
    iDestruct (region_key_shift icfg_nib (fun z => icnt_half z 0%nat) Hnib
                 with "Hcnt") as "Hcnt".
    iDestruct (region_key_shift icfg_nib (fun z => frzm_h z false) Hnib
                 with "Hmir") as "Hmir".
    iDestruct (region_key_shift icfg_nib (fun z => ifreeze_off z) Hnib
                 with "Hoff") as "Hoff".
    (* ---- the blocks, carved ------------------------------------------ *)
    assert (Hsub : forall i : Z, i ∈ elements A ->
              snap_blk_set (snap_node S i) ⊆ C)
      by (intros i Hi; apply HC, elem_of_elements, Hi).
    assert (Hdisj : forall i j : Z, i ∈ elements A -> j ∈ elements A ->
              i <> j ->
              snap_blk_set (snap_node S i) ## snap_blk_set (snap_node S j)).
    { intros i j Hi Hj Hne.
      apply elem_of_elements in Hi. apply elem_of_elements in Hj.
      exact (snap_blk_set_disj S _ i j (snap_node S i) (snap_node S j) Hb
               (Hnode i (proj1 (proj1 (HA i) Hi)))
               (Hnode j (proj1 (proj1 (HA j) Hj))) Hne). }
    rewrite /snap_live_blocks.
    iDestruct (big_sepS_carve
                 (fun b => fsblock (fs_bytes γfs) b (P b))%I
                 C (elements A) (fun i => snap_blk_set (snap_node S i))
                 (NoDup_elements A) Hsub Hdisj with "Hblk") as "[Hpc Hrem]".
    iSplitR "Hrem"; [| iExact "Hrem"].
    iDestruct (big_sepS_of_elements
                 (fun i => [∗ set] b ∈ snap_blk_set (snap_node S i),
                             fsblock (fs_bytes γfs) b (P b))%I A
                 with "Hpc") as "Hpc".
    (* ---- the region's payout, split along the same subset ------------ *)
    iDestruct (big_sepS_split_sub _ (region_inums icfg_nib) A HARs
                 with "Hout") as "[HoutA HoutF]".
    iAssert ([∗ set] z ∈ region_inums icfg_nib ∖ A,
               imark γi (bv_unsigned (mword_of_int z : mword 32)))%I
      with "[HoutF]" as "Hmk".
    { iApply (big_sepS_mono with "HoutF"). intros z Hz.
      apply elem_of_difference in Hz as [Hz1 Hz2]. iIntros "H".
      iApply (ireg_out_free_inv γi (mword_of_int z : mword 32)
                (fn_rec (snap_node S z)) (Hfree z Hz1 Hz2) with "H"). }
    (* ---- the contents holds, split along the same subset -------------- *)
    iDestruct (big_sepS_split_sub _ (region_inums icfg_nib) A HARs
                 with "Hdv") as "[HdvA HdvF]".
    iAssert ([∗ set] z ∈ region_inums icfg_nib ∖ A,
               ∃ e, dv_ride (bv_unsigned (mword_of_int z : mword 32)) e)%I
      with "[HdvF]" as "HdvF".
    { iApply (big_sepS_mono with "HdvF"). intros z Hz.
      apply elem_of_difference in Hz as [Hz1 _].
      rewrite (region_inum_faithful icfg_nib z Hnib Hz1).
      iIntros "H". iExists _. iExact "H". }
    iDestruct (big_sepS_split_sub _ (region_inums icfg_nib) A HARs
                 with "Hfv") as "[HfvA HfvF]".
    iAssert ([∗ set] z ∈ region_inums icfg_nib ∖ A,
               ∃ b, fv_ride (bv_unsigned (mword_of_int z : mword 32)) b)%I
      with "[HfvF]" as "HfvF".
    { iApply (big_sepS_mono with "HfvF"). intros z Hz.
      apply elem_of_difference in Hz as [Hz1 _].
      rewrite (region_inum_faithful icfg_nib z Hnib Hz1).
      iIntros "H". iExists _. iExact "H". }
    (* ---- the allocated arm, one named application per inum ----------- *)
    iDestruct (big_sepS_sep_2 with "HoutA Hdlk") as "Ha".
    iDestruct (big_sepS_sep_2 with "Ha Hpc") as "Ha".
    iDestruct (big_sepS_sep_2 with "Ha HdvA") as "Ha".
    iDestruct (big_sepS_sep_2 with "Ha HfvA") as "Ha".
    iDestruct (big_sepS_sep_2 with "Ha Htop") as "Ha".
    iApply (ipool_alloc γfs γi cov (sb_logstart (fss_sb S))
              (region_inums icfg_nib) A HARs
              with "Hcnt Hmir Hoff [Ha] Hmk HdvF HfvF").
    iApply (big_sepS_mono with "Ha"). intros z Hz.
    pose proof (Hln z (HARs z Hz)) as Hlz.
    pose proof (Hnode z (HARs z Hz)) as Hnz.
    rewrite (region_inum_faithful icfg_nib z Hnib (HARs z Hz)).
    iIntros "[[[[[Hreg Hdl] Hblks] Hdv] Hfv] Htopz]".
    iExists (fn_rec (snap_node S z)), (bm_of (snap_node S z)),
            (fn_data (snap_node S z)).
    iSplitR.
    { iPureIntro.
      exact (snap_inode_ok S P cov (sb_logstart (fss_sb S)) z
               (snap_node S z) Hb Hlz Hnz (Hty z Hz)). }
    iSplitR; [iPureIntro; exact (inode_rec_local_of z (snap_node S z) Hlz) |].
    (* the three [DirView] premises, off [sk_dirloc] *)
    pose proof (snap_node_dir_local S _ z (snap_node S z) icfg_nib
                  Hb Hnz Hw) as Hdl3.
    iSplitR; [iPureIntro; exact (node_dir_local_ok Hdl3) |].
    iSplitR; [iPureIntro; exact (node_dir_local_ix Hdl3) |].
    iSplitR; [iPureIntro; exact (node_dir_local_orph Hdl3) |].
    iSplitR; [iPureIntro; exact (dir_uniq_of_local z (snap_node S z) Hlz) |].
    iSplitL "Hdl".
    { rewrite /dlinks (era_node_bm_of z (snap_node S z) Hlz). iExact "Hdl". }
    iDestruct (snap_inode_blocks_res γfs S P
                 (fs_home_set cov (sb_logstart (fss_sb S))) z (snap_node S z)
                 Hb Hlz Hnz with "Hblks") as "[Hblks Hind]".
    iSplitL "Hreg".
    { iApply (ireg_out_alloc_inv γi (mword_of_int z : mword 32)
                (fn_rec (snap_node S z)) (Hty z Hz) with "Hreg"). }
    iSplitL "Hind"; [iExact "Hind" |].
    iSplitL "Hblks"; [iExact "Hblks" |].
    iSplitL "Htopz".
    { rewrite (era_node_bm_of z (snap_node S z) Hlz). iExact "Htopz". }
    iSplitL "Hdv"; [iExact "Hdv" | iExact "Hfv"].
  Qed.

End SnapPool.
