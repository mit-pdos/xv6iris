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
Require Import FsStateInode FsStateBitmap FsStateEra.
Require Import FsBlocks FsBytesGamma.
Require Import DinodeEnc FsTree.
Require Import FsCrash LogDefs.
Require Import InodeInv InodeLock InodeRegion.
Require Import IcacheEscrow IcacheBoot.
Require Import BitmapEnc BitmapInv.
Require Import FsImg FsImgBridge.
Require Import FsDurSnap FsDurImg.
Require Import WpUart.         (* [uart_names] *)
Require Import VirtioModel.    (* [disk_read]  *)
Require Import DiskPtsto.      (* [disk_names] *)
Require Import WpLockAt BioInitAt KallocInv IrefSlots BioDefs.
Require Import LogInv.
Require Import FsCfg.
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

(* ====================================================================== *)
(*  8.  THE CARVE'S SETS, AND WHY EVERY PEEL IS THE USED-SET COUPLING      *)
(*                                                                        *)
(*  [FsCfgBoot.fs_cfg_alloc] peels the boot thread's home ledger by four   *)
(*  set inclusions -- block 1, the inode region, every live inode's own    *)
(*  blocks, and the bitmap block with the whole free pool -- and proves    *)
(*  each one off an image sweep.  Off the snapshot every one of them is    *)
(*  [FsDurSnap.snap_names_cov] (a named block is covered and outside the   *)
(*  log region) closed by the USED-SET COUPLING: the metadata roles are    *)
(*  marked in use ([sk_meta_used]), a node's own blocks are marked in use  *)
(*  and are no metadata block ([sk_own_used]), and a block whose bit reads *)
(*  CLEAR is neither.  The only geometry spent is [sk_sbok]'s.             *)
(* ====================================================================== *)

(*  every block of the inode REGION is a metadata block of the snapshot:
    [inodestart + j] is inum [16*j]'s record block and [sk_regdom] names
    that inum.  This is what puts the region OUTSIDE the free pool and
    outside every node's footprint without a single image fact. *)
Lemma snap_meta_ireg (S : fs_state_rec) (D : gmap Z (list (bv 8)))
    (nib : nat) (b : Z) :
  snap_bytes S D ->
  Z.of_nat nib = sb_ninodes (fss_sb S) / 16 + 1 ->
  b ∈ ireg_blk_set (sb_inodestart (fss_sb S)) nib -> snap_meta S b.
Proof.
  intros Hb Hw Hbb. apply ireg_blk_set_spec in Hbb.
  right; right.
  exists ((b - sb_inodestart (fss_sb S)) * 16).
  split.
  - apply (sk_regdom Hb). lia.
  - rewrite (Z.div_mul (b - sb_inodestart (fss_sb S)) 16 ltac:(lia)). lia.
Qed.

(*  the LIVE inums of a snapshot: the region's inums whose record is
    typed.  [FsImg.fs_live_set]'s twin, and the pool's [A]. *)
Definition snap_live_set (S : fs_state_rec) (nib : nat) : gset Z :=
  @base.filter Z (gset Z) _ (fun z => fn_type (snap_node S z) <> 0) _
          (region_inums nib).

Lemma elem_of_snap_live_set (S : fs_state_rec) (nib : nat) (z : Z) :
  z ∈ snap_live_set S nib
  <-> z ∈ region_inums nib /\ fn_type (snap_node S z) <> 0.
Proof. rewrite /snap_live_set elem_of_filter. tauto. Qed.

(*  ...and the blocks the era fupd SPENDS, [FsCfgBoot.fs_kit_spent]'s twin:
    block 1 (to fsinit), the log region (to initlog), the inode region
    (into [ireg_inv]), the bitmap block and the whole free pool (into
    [BitmapInv.bitmap_inv]) and every live inode's own blocks (into the
    pool).  What is LEFT is whatever [cov] holds that the snapshot does not
    name. *)
Definition snap_spent (S : fs_state_rec) (nib : nat) : gset Z :=
  ({[ (1:Z) ]} ∪ log_region_set (sb_logstart (fss_sb S))
     ∪ ireg_blk_set (sb_inodestart (fss_sb S)) nib
     ∪ snap_bitmap_spent S)
  ∪ snap_live_blocks S (snap_live_set S nib).

(* ====================================================================== *)
(*  9.  THE MINT                                                           *)
(*                                                                        *)
(*  [FsCfgBoot.fs_cfg_alloc] with every image premise replaced by the      *)
(*  durable snapshot, and every object spelled at [S]'s own node rather    *)
(*  than at [FsImg.fs_dinode].  The RESOURCE routing is unchanged -- same  *)
(*  peels, same allocators, same two kits out -- because the resources     *)
(*  never depended on the image: only the pure facts did.                  *)
(* ====================================================================== *)

Section SnapMint.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !irefslotG Σ}.
  Context `{GEN : GenId}.

  Lemma fs_cfg_alloc_snap (γd : uart_names) (γv : disk_names)
      (dk : Z -> bv 8) (ndisk : nat) (S : fs_state_rec) (cov : gset Z)
      (nib : nat) (E : coPset)
      (* ---- THE VALUE THE ERA'S BYTE VIEW IS MINTED AT (durable-disk lane
         E-except): the COMMITTED view [FsCrash.fr_D], which differs from
         the raw disk exactly on [Xexc], the pending home blocks of a dirty
         on-disk log header.  The CACHE map stays raw -- that is what keeps
         [BioInv.pool_blk] honest -- and the difference comes out as the
         WAL's exception handle.  At a clean header [Xexc = ∅] and [Pb] IS
         the raw home content. ---- *)
      (Pb : Z -> list (bv 8)) (Xexc : gset Z) :
    (* ---- THE DURABLE SNAPSHOT, and it is the whole of the file system's
       side: the committed map IS what the machine would recover to, and it
       is the encoding of the abstract state [S]. ---- *)
    snap_ok S (fs_restrict Pb
                 (fs_home_set cov (sb_logstart (fss_sb S)))) ->
    (forall b : Z, length (Pb b) = BSIZE) ->
    Xexc ⊆ fs_home_set cov (sb_logstart (fss_sb S)) ->
    (1 : Z) ∉ Xexc ->
    (forall b : Z, b ∈ fs_home_set cov (sb_logstart (fss_sb S)) ->
       b ∉ Xexc -> Pb b = fs_blocks dk b) ->
    (* ---- the region's width, tied to [S]'s OWN superblock ---- *)
    Z.of_nat nib = sb_ninodes (fss_sb S) / 16 + 1 ->
    16 * Z.of_nat nib <= 2 ^ 32 ->
    (* ---- R4's coverage corners ---- *)
    fs_cov_in cov ndisk ->
    (* ...AND ONE CORNER, NOT TWO (durable-disk lane E-himg).  The DATA
       region's corner was never read: the mint spends only the FREE pool
       there, and [FsDurSnap.sk_pool] already puts every free block below
       [size] into [D] -- hence into the home ledger.  What is left is the
       METADATA window, and at a boot from the snapshot that comes off
       [FsDurSnap.snap_cov_window]. *)
    (forall b : Z, 1 <= b < fs_data_start (fss_sb S) -> b ∈ cov) ->
    disk_bytes γv 0 (disk_read dk 0 ndisk) -∗
    bslots_auth -∗ bslots BSLOTS_FS ={E}=∗
    ∃ (ICFG : icfg) (FSC : fscfg),
      ⌜icfg_dev = ROOTDEV⌝ ∗ ⌜icfg_nib = nib⌝ ∗
      ⌜icfg_ist = sb_inodestart (fss_sb S)⌝ ∗
      ⌜fsc_uart = γd⌝ ∗ ⌜fsc_disk = γv⌝ ∗ ⌜fsc_cov = cov⌝ ∗
      ⌜fsc_logst = sb_logstart (fss_sb S)⌝ ∗
      ⌜fsc_bmapstart = sb_bmapstart (fss_sb S)⌝ ∗
      ⌜fsc_size = sb_size (fss_sb S)⌝ ∗
      ⌜fsc_ninodes = sb_ninodes (fss_sb S)⌝ ∗
      fs_kit_icache ICFG FSC ∗
      fs_kit_fsinit_ghost ICFG FSC (fs_blocks dk) (snap_spent S nib) Pb Xexc.
  Proof.
    intros Hok HlPb HXsub HX1 Hagr Hnibeq Hnib32 Hcovin Hcovmeta.
    pose proof (sk_bytes Hok) as Hb.
    pose proof (sk_local Hok) as Hloc.
    iIntros "Hdisk Hsa Hsf".
    (* ---- 1. the log's four gnames, at their genesis values ---------- *)
    iMod log_ghost_alloc as (γlog) "Hlogtok".
    (* ---- 2. THE INODE CACHE'S RECORD -------------------------------- *)
    iMod (icfg_alloc ROOTDEV nib
            (link_boot_map (region_inums nib))
            (icnt_boot_map (region_inums nib))
            (frzo_boot_map (region_inums nib))
            (frzm_boot_map (region_inums nib))
            (dview_boot_map (region_inums nib))
            (fview_boot_map (region_inums nib))
            γlog (sb_inodestart (fss_sb S))
            (link_boot_map_valid _) (icnt_boot_map_valid _)
            (frzo_boot_map_valid _) (frzm_boot_map_valid _)
            (dview_boot_map_valid _) (fview_boot_map_valid _))
      as (ICFG g0) "(%Hdev & %Hnibq & %Hlogq & %Histq & Hiref & Hlive &
                     Hlk & Hcnt & Hfrzo & Hfrzm & Hdv & Hfv & Hboot & Hep &
                     Hisl & Hrauth & Hlkauth & Hpkey & Hxkey & Hhpn & Htkey &
                     Hckey)".
    iDestruct (hpn_boot_split with "Hhpn") as "Hhpn".
    symmetry in Hnibq. subst nib.
    (* ---- the pure geometry, off [sk_sbok] alone --------------------- *)
    pose proof (sk_sbok Hb) as Hsb.
    pose proof (sbo_logstart _ Hsb) as Hls.
    pose proof (sbo_nlog _ Hsb) as Hnl.
    pose proof (sbo_inodestart _ Hsb) as Hist.
    pose proof (sbo_bmapstart _ Hsb) as Hbms.
    pose proof (sbo_ninodes _ Hsb) as Hni. unfold ROOTINO in Hni.
    assert (Hdiv0 : 0 <= sb_ninodes (fss_sb S) / 16)
      by (apply Z.div_pos; lia).
    assert (Hnin : sb_ninodes (fss_sb S) <= 16 * Z.of_nat icfg_nib).
    { pose proof (Z.div_mod (sb_ninodes (fss_sb S)) 16 ltac:(lia)) as Hdm.
      pose proof (Z.mod_pos_bound (sb_ninodes (fss_sb S)) 16 ltac:(lia))
        as Hmb. lia. }
    assert (Hnib0 : (0 < icfg_nib)%nat) by lia.
    assert (Hfull : fs_blocks_full Pb) by (intros b; apply HlPb).
    assert (Hds : fs_data_start (fss_sb S)
                  = sb_inodestart (fss_sb S) + Z.of_nat icfg_nib + 1)
      by (rewrite /fs_data_start; lia).
    assert (HlogI : forall b : Z,
              b ∈ log_region_set (sb_logstart (fss_sb S)) ->
              1 < b < sb_inodestart (fss_sb S)).
    { intros b Hbb.
      pose proof (log_region_bound (sb_logstart (fss_sb S)) b Hbb).
      unfold LOGBLOCKS in *. lia. }
    assert (HiregI : forall b : Z,
              b ∈ ireg_blk_set (sb_inodestart (fss_sb S)) icfg_nib ->
              sb_inodestart (fss_sb S) <= b < fs_data_start (fss_sb S)).
    { intros b Hbb. apply ireg_blk_set_spec in Hbb. lia. }
    assert (H1lt : 1 < fs_data_start (fss_sb S)) by lia.
    (* ---- the peels, each a subset of what is left of [cov] ---------- *)
    assert (Hhomesub : fs_home_set cov (sb_logstart (fss_sb S)) ⊆ cov).
    { rewrite /fs_home_set. apply elem_of_subseteq. intros b Hbb.
      apply elem_of_difference in Hbb as [Hc _]. exact Hc. }
    assert (H1home : ({[ (1:Z) ]} : gset Z)
                     ⊆ fs_home_set cov (sb_logstart (fss_sb S))).
    { rewrite /fs_home_set. apply elem_of_subseteq. intros b Hbb.
      apply elem_of_singleton in Hbb as ->. apply elem_of_difference.
      split; [apply Hcovmeta; lia |].
      intros Hc. pose proof (HlogI 1 Hc). lia. }
    assert (Hcancel : cov ∖ fs_home_set cov (sb_logstart (fss_sb S))
                      = log_region_set (sb_logstart (fss_sb S))).
    { rewrite /fs_home_set. apply set_eq. intros x. split.
      - intros Hx. apply elem_of_difference in Hx as [Hc Hn].
        destruct (decide (x ∈ log_region_set (sb_logstart (fss_sb S))))
          as [Hr | Hr]; [exact Hr |].
        exfalso. apply Hn. apply elem_of_difference. split; assumption.
      - intros Hx. apply elem_of_difference.
        split; [apply Hcovmeta; pose proof (HlogI x Hx); lia |].
        intros Hd. apply elem_of_difference in Hd as [_ Hn]. exact (Hn Hx). }
    assert (Hsetcomm : fs_home_set cov (sb_logstart (fss_sb S))
                         ∖ ({[ (1:Z) ]} : gset Z)
                       = (cov ∖ ({[ (1:Z) ]} : gset Z))
                           ∖ log_region_set (sb_logstart (fss_sb S))).
    { rewrite /fs_home_set !difference_difference_l_L. f_equal.
      apply union_comm_L. }
    assert (Hiregcov : ireg_blk_set (sb_inodestart (fss_sb S)) icfg_nib
                       ⊆ (cov ∖ ({[ (1:Z) ]} : gset Z))
                           ∖ log_region_set (sb_logstart (fss_sb S))).
    { apply elem_of_subseteq. intros b Hbb. pose proof (HiregI b Hbb).
      apply elem_of_difference. split.
      - apply elem_of_difference. split; [apply Hcovmeta; lia |].
        rewrite elem_of_singleton. lia.
      - intros Hc. pose proof (HlogI b Hc). lia. }
    (* ---- 3. the inode-reference authorities, all-plain -------------- *)
    iDestruct (link_boot_split (region_inums icfg_nib) with "Hlk") as "Hlk".
    iEval (rewrite big_sepS_sep) in "Hlk".
    iDestruct "Hlk" as "[Hla Hoff]".
    iDestruct (icnt_boot_split (region_inums icfg_nib) with "Hcnt") as "Hcnt".
    iEval (rewrite big_sepS_sep) in "Hcnt".
    iDestruct "Hcnt" as "[HcntR HcntP]".
    iDestruct (frzo_boot_split (region_inums icfg_nib) with "Hfrzo")
      as "Hrcpt".
    iDestruct (frzm_boot_split (region_inums icfg_nib) with "Hfrzm")
      as "Hmir".
    iEval (rewrite big_sepS_sep) in "Hmir".
    iDestruct "Hmir" as "[HmirR HmirP]".
    (* THE CONTENTS GHOSTS, MINTED AT [∅] AND SET TO THE SNAPSHOT'S TRUTH *)
    iDestruct (dv_boot_split (region_inums icfg_nib) with "Hdv") as "Hdv".
    iAssert (|==> [∗ set] z ∈ region_inums icfg_nib,
                    dv_hold z (dv_of (fn_rec (snap_node S z))
                                 (fn_data (snap_node S z))))%I
      with "[Hdv]" as ">Hdv".
    { iApply big_sepS_bupd. iApply (big_sepS_mono with "Hdv").
      intros z _. iIntros "H".
      iApply (dv_set z ∅
                (dv_of (fn_rec (snap_node S z)) (fn_data (snap_node S z)))
               with "H"). }
    iDestruct (fv_boot_split (region_inums icfg_nib) with "Hfv") as "Hfv".
    iAssert (|==> [∗ set] z ∈ region_inums icfg_nib,
                    fv_hold z (fv_of (fn_rec (snap_node S z))
                                 (fn_data (snap_node S z))))%I
      with "[Hfv]" as ">Hfv".
    { iApply big_sepS_bupd. iApply (big_sepS_mono with "Hfv").
      intros z _. iIntros "H".
      iApply (fv_set z []
                (fv_of (fn_rec (snap_node S z)) (fn_data (snap_node S z)))
               with "H"). }
    iDestruct (region_of_seq (fun z => mono_nat_auth_own (icfg_iep z) 1 0)
                 icfg_nib with "Hep") as "Hep".
    iDestruct (live_boot_split g0 with "Hlive") as "Hlive".
    (* ---- 4. the block layer's ghosts, and the FILE SYSTEM's two ----- *)
    (* THE LINK FAMILY IS ONE [own_alloc] AT [sk_links]'s SLACKED ELEMENT
       (durable-disk lane E-clauses): what comes out is [FsState.fs_links] --
       each inum's authority beside exactly the fragments its own entries
       claim -- plus the ROOT's spare token, which is the region's
       keep-alive.  No image sweep and no ticket routing. *)
    destruct (sk_links Hb) as (fch & vroot & Hfok & Hfvalid).
    iMod (fs_boot_alloc_root_slack (fss_inodes S) fch ROOTINO vroot
            Hfok Hfvalid)
      as (γlk γtp) "(Htopa & Htopf & Hlnk & Hkeep)".
    iMod (fs_boot_ghosts γv dk ndisk cov
            (fs_home_set cov (sb_logstart (fss_sb S)))
            ROOTDEV γlk γtp E Pb Xexc Hcovin Hhomesub
            ltac:(intros b _; apply HlPb) HXsub Hagr
            with "Hdisk")
      as (γfs) "(%Hlkq & %Htp & Hpool & HaL & HaD & #Hbinv & Hxo & Hdty & Hfsb & Hchl)".
    (* THE EXCEPTION HANDLE (durable-disk lane E-except) goes into
       fsinit's kit: the mint runs at [X = ∅] -- the byte view is born
       equal to the RAW home blocks -- and [initlog] is what seals it. *)
    iAssert (fs_bytes_at γfs (fs_home_set cov (sb_logstart (fss_sb S))))
      as "#Hbrow"; [iExists Pb; iExact "Hbinv" |].
    (* ---- THE TOP MAP IS ROUTED HERE --------------------------------- *)
    iEval (rewrite -Htp) in "Htopa".
    iEval (rewrite -Htp) in "Htopf".
    iMod (ftop_alloc E γfs (fss_inodes S) Hloc with "Htopa Hlkauth")
      as "#Hftopi".
    iEval (rewrite (big_sepM_as_set (fss_inodes S)
                      (fun i n => top_frag (fs_gamma_L γfs) i n))) in "Htopf".
    assert (Hregdom : region_inums icfg_nib ⊆ dom (fss_inodes S)).
    { apply elem_of_subseteq. intros z Hz. apply elem_of_dom.
      apply region_inums_spec in Hz. apply (sk_regdom Hb z). lia. }
    iDestruct (big_sepS_subseteq _ _ _ Hregdom with "Htopf") as "Htopf".
    (* the live set, and the free inums' fragments to the region *)
    assert (HAsub : snap_live_set S icfg_nib ⊆ region_inums icfg_nib).
    { apply elem_of_subseteq. intros z Hz.
      exact (proj1 (proj1 (elem_of_snap_live_set S icfg_nib z) Hz)). }
    iDestruct (big_sepS_split_sub _ (region_inums icfg_nib)
                 (snap_live_set S icfg_nib) HAsub
                 with "Htopf") as "[Htopf Htopreg]".
    iAssert ([∗ set] z ∈ region_inums icfg_nib,
               ireg_top_boot γfs (fun z => fn_rec (snap_node S z)) z)%I
      with "[Htopreg]" as "Htopreg".
    { rewrite {2}(union_difference_L (snap_live_set S icfg_nib)
                    (region_inums icfg_nib) HAsub).
      rewrite big_sepS_union; [| set_solver].
      iSplitR "Htopreg".
      { iApply big_sepS_intro. iModIntro. iIntros (z Hz).
        iApply (ireg_top_boot_live γfs (fun z => fn_rec (snap_node S z)) z).
        exact (proj2 (proj1 (elem_of_snap_live_set S icfg_nib z) Hz)). }
      iApply (big_sepS_mono with "Htopreg"). intros z Hz.
      apply elem_of_difference in Hz as [Hz1 Hz2].
      assert (Hty : fn_type (snap_node S z) = 0).
      { destruct (decide (fn_type (snap_node S z) = 0)) as [H0 | H0];
          [exact H0 |].
        exfalso. apply Hz2, (proj2 (elem_of_snap_live_set S icfg_nib z)).
        split; [exact Hz1 | exact H0]. }
      iIntros "H". rewrite /ireg_top_boot decide_True; [| exact Hty].
      rewrite -(free_node_of_bare (snap_node S z)
                  (inl_bare_free
                     (Hloc z (snap_node S z)
                        (snap_node_at S _ icfg_nib z Hb Hnibeq Hz1)) Hty)).
      iExact "H". }
    (* ---- THE TYPE REGISTER, ROUTED ---------------------------------- *)
    iEval (rewrite -Hlkq) in "Hlnk".
    iEval (rewrite -Hlkq) in "Hkeep".
    iDestruct (snap_link_route γfs S _ icfg_nib vroot Hb Hnibeq Hnib0
                 with "Hlnk Hkeep") as "[Hlnks Hetk]".
    (* ---- 5. THE PEELS ----------------------------------------------- *)
    rewrite Hcancel.
    iDestruct (fs_log_region_split γfs dk (sb_logstart (fss_sb S))
                 with "Hchl") as "[Hhdr Hslots]".
    iDestruct (big_sepS_split_sub _ _ ({[ (1:Z) ]} : gset Z) H1home
                 with "Hfsb") as "[Hb1 Hblk]".
    iEval (rewrite Hsetcomm) in "Hblk".
    iDestruct (big_sepS_split_sub _ _
                 (ireg_blk_set (sb_inodestart (fss_sb S)) icfg_nib)
                 Hiregcov with "Hblk") as "[Hbireg HfsbC]".
    iEval (rewrite big_sepS_singleton) in "Hb1".
    iDestruct (ireg_blk_of_set
                 (fun b => fsblock (fs_bytes γfs) b (Pb b))
                 (sb_inodestart (fss_sb S)) icfg_nib with "Hbireg")
      as "Hbireg".
    (* ---- 6. THE INODE REGION ---------------------------------------- *)
    iAssert (ireg_boot) with "[Hboot]" as "Hboot".
    { rewrite /ireg_boot /ity_pending. iExact "Hboot". }
    iMod (ireg_alloc E γfs (sb_inodestart (fss_sb S)) icfg_nib
            (fs_home_set cov (sb_logstart (fss_sb S)))
            (fun bi : nat =>
               Pb (sb_inodestart (fss_sb S) + Z.of_nat bi))
            (fun z => fn_nlink (snap_node S z))
            (fun z => fn_rec (snap_node S z))
            Hnib32 eq_refl
            ltac:(intros bi _; rewrite HlPb; reflexivity)
            ltac:(intros dss Hdl Hdwf Hde;
                  exact (snap_ireg_premises S Pb
                           (fs_home_set cov (sb_logstart (fss_sb S)))
                           dss icfg_nib Hfull Hb Hloc Hnibeq Hnib32
                           Hdl Hdwf Hde))
            with "Hla Hlnks HcntR Hrcpt HmirR Hep Htopreg Hbireg Hbrow Hftopi Hboot Hrauth")
      as (γi dss) "(%Hdl & %Hdwf & %Hde & Hireginv & Hboot & Hlics & Hflics &
                    Hout)".
    iDestruct "Hireginv" as "#Hireginv".
    iClear "Hlics". iClear "Hflics".
    iAssert ([∗ set] z ∈ region_inums icfg_nib,
               dv_ride z (dv_of (fn_rec (snap_node S z))
                            (fn_data (snap_node S z))))%I
      with "[Hdv]" as "Hdv".
    { iApply (big_sepS_mono with "Hdv"). intros z _. iIntros "H".
      iApply (dv_ride_of_hold with "H"). }
    iAssert ([∗ set] z ∈ region_inums icfg_nib,
               fv_ride z (fv_of (fn_rec (snap_node S z))
                            (fn_data (snap_node S z))))%I
      with "[Hfv]" as "Hfv".
    { iApply (big_sepS_mono with "Hfv"). intros z _. iIntros "H".
      iApply (fv_ride_of_hold with "H"). }
    (* the payout is at the DECODED record; restate it at [S]'s own *)
    destruct (snap_ireg_premises S Pb
                (fs_home_set cov (sb_logstart (fss_sb S)))
                dss icfg_nib Hfull Hb Hloc Hnibeq Hnib32 Hdl Hdwf Hde)
      as (_ & _ & _ & _ & _ & Hrecat).
    iAssert ([∗ set] z ∈ region_inums icfg_nib,
               ireg_out γi (mword_of_int z : mword 32)
                 (fn_rec (snap_node S z)))%I with "[Hout]" as "Hout".
    { iApply (big_sepS_mono with "Hout"). intros z Hz.
      rewrite (Hrecat z Hz) //. }
    (* ---- 7. the pool ------------------------------------------------ *)
    (* the live inodes' blocks are inside the carve's remainder: each is
       marked IN USE and is no metadata block ([sk_own_used]), so it is
       covered, outside the log region, not block 1 and not a region
       block. *)
    assert (HC : forall z : Z, z ∈ snap_live_set S icfg_nib ->
              snap_blk_set (snap_node S z)
              ⊆ (((cov ∖ ({[ (1:Z) ]} : gset Z))
                    ∖ log_region_set (sb_logstart (fss_sb S)))
                   ∖ ireg_blk_set (sb_inodestart (fss_sb S)) icfg_nib)).
    { intros z Hz. apply elem_of_subseteq. intros b Hbb.
      apply elem_of_snap_blk_set in Hbb.
      pose proof (snap_node_at S _ icfg_nib z Hb Hnibeq (HAsub z Hz)) as Hnz.
      destruct (sk_own_used Hb z (snap_node S z) b Hnz Hbb) as [_ Hnm].
      destruct (snap_names_cov S Pb cov
                  (sb_logstart (fss_sb S)) b Hb
                  ltac:(right; left; by exists z, (snap_node S z)))
        as [Hcv Hnlg].
      apply elem_of_difference. split.
      - apply elem_of_difference. split.
        + apply elem_of_difference. split; [exact Hcv |].
          rewrite elem_of_singleton. exact (snap_meta_sb S b Hnm).
        + exact Hnlg.
      - intros Hc. exact (Hnm (snap_meta_ireg S _ icfg_nib b Hb Hnibeq Hc)). }
    iDestruct (ipool_alloc_of_snap γfs γi S Pb cov
                 (((cov ∖ ({[ (1:Z) ]} : gset Z))
                     ∖ log_region_set (sb_logstart (fss_sb S)))
                    ∖ ireg_blk_set (sb_inodestart (fss_sb S)) icfg_nib)
                 (snap_live_set S icfg_nib) Hok Hnibeq Hnib32
                 (elem_of_snap_live_set S icfg_nib) HC
                 with "HcntP HmirP Hoff Hdv Hfv Htopf Hout [Hetk] HfsbC")
      as "[Hipool Hrem]".
    { (* the pool takes the LIVE inums' tickets; the free inums' are
         [emp]-shaped and are dropped here *)
      iDestruct (big_sepS_subseteq _ _ _ HAsub with "Hetk") as "Hetk".
      iExact "Hetk". }
    (* ---- 7b. the bitmap block and the free pool --------------------- *)
    assert (Hbmsub : snap_bitmap_spent S
                     ⊆ ((((cov ∖ ({[ (1:Z) ]} : gset Z))
                            ∖ log_region_set (sb_logstart (fss_sb S)))
                           ∖ ireg_blk_set (sb_inodestart (fss_sb S)) icfg_nib)
                          ∖ snap_live_blocks S (snap_live_set S icfg_nib))).
    { apply elem_of_subseteq. intros b Hbb.
      assert (Hnames : snap_names S b).
      { rewrite /snap_bitmap_spent elem_of_union elem_of_singleton in Hbb.
        destruct Hbb as [-> | Hf].
        - left. right. by left.
        - apply elem_of_free_set in Hf as [Hran Hnu].
          right; right. split; [exact Hran | exact Hnu]. }
      destruct (snap_names_cov S Pb cov
                  (sb_logstart (fss_sb S)) b Hb Hnames) as [Hcv Hnlg].
      (* the bitmap block is a METADATA role, hence marked in use, hence in
         no node's footprint; a free block's bit reads CLEAR, and every
         metadata role and every node's block is marked in use. *)
      assert (Hnodeb : forall z : Z, z ∈ snap_live_set S icfg_nib ->
                fn_owns (snap_node S z) b ->
                b ∈ fss_used S /\ ~ snap_meta S b).
      { intros z Hz Hown.
        exact (sk_own_used Hb z (snap_node S z) b
                 (snap_node_at S _ icfg_nib z Hb Hnibeq (HAsub z Hz))
                 Hown). }
      assert (Hkey : b <> 1
                     /\ b ∉ ireg_blk_set (sb_inodestart (fss_sb S)) icfg_nib
                     /\ b ∉ snap_live_blocks S (snap_live_set S icfg_nib)).
      { rewrite /snap_bitmap_spent elem_of_union elem_of_singleton in Hbb.
        destruct Hbb as [Heqb | Hf].
        - split.
          { pose proof (snap_sb_bmap_ne S Hsb) as Hne.
            rewrite /SB_BNO in Hne. lia. }
          split.
          { intros Hc. apply ireg_blk_set_spec in Hc. lia. }
          intros Hc. apply elem_of_snap_live_blocks in Hc as (z & Hz & Hbz).
          apply elem_of_snap_blk_set in Hbz.
          destruct (Hnodeb z Hz Hbz) as [_ Hnm].
          apply Hnm. right. left. exact Heqb.
        - apply elem_of_free_set in Hf as [Hran Hnu].
          split.
          { intros ->. apply Hnu. apply (sk_meta_used Hb). by left. }
          split.
          { intros Hc. apply Hnu. apply (sk_meta_used Hb).
            exact (snap_meta_ireg S _ icfg_nib b Hb Hnibeq Hc). }
          intros Hc. apply elem_of_snap_live_blocks in Hc as (z & Hz & Hbz).
          apply elem_of_snap_blk_set in Hbz.
          destruct (Hnodeb z Hz Hbz) as [Hu _]. exact (Hnu Hu). }
      destruct Hkey as (Hne1 & Hnireg & Hnlive).
      apply elem_of_difference. split; [| exact Hnlive].
      apply elem_of_difference. split; [| exact Hnireg].
      apply elem_of_difference. split; [| exact Hnlg].
      apply elem_of_difference. split; [exact Hcv |].
      rewrite elem_of_singleton. exact Hne1. }
    iDestruct (big_sepS_split_sub
                 (fun b => fsblock (fs_bytes γfs) b (Pb b))%I
                 _ (snap_bitmap_spent S) Hbmsub with "Hrem")
      as "[Hbmspent Hrem]".
    iDestruct (bitmap_res_of_snap γfs S Pb
                 (fs_home_set cov (sb_logstart (fss_sb S))) Hb
                 with "Hbmspent") as "Hbmres".
    iMod (bitmap_inv_alloc E with "Hbrow Hbmres") as "#Hbmres".
    (* ---- 8. the gname-only mints, and the record -------------------- *)
    iMod (bio_names_ghost_alloc with "Hsa Hsf") as (bn) "Hbio".
    iMod lock_ghost_alloc as (git) "Hitlk".
    iMod lock_ghost_alloc as (gkm) "Hkmlk".
    iMod lock_ghost_alloc as (gdl) "Hdllk".
    iMod lock_ghost_alloc as (gpr) "Hprlk".
    iMod (kalloc_avail_alloc 0%nat) as (gkp) "[Hkav Hkauth]".
    iMod (ic_names_alloc (fun _ : nat => ((mword_of_int 0 : mword 32),
                                          (mword_of_int 0 : mword 32))))
      as (cn) "(Htok & Hmid & Hgid)".
    iAssert ([∗ list] k ∈ seq 0 NINODE,
               ∃ (v : bool) (d n : mword 32), ic_id cn k 1 v d n)%I
      with "[Hgid]" as "Hgid".
    { iApply (big_sepL_mono with "Hgid"). intros idx k _. iIntros "H".
      iExists false, (mword_of_int 0 : mword 32),
              (mword_of_int 0 : mword 32). iExact "H". }
    iModIntro.
    iExists ICFG,
      (MkFscfg gpr gkm gkp γd γv gdl bn γfs γi cn git
               cov (sb_logstart (fss_sb S)) (sb_bmapstart (fss_sb S))
               (sb_size (fss_sb S)) (sb_ninodes (fss_sb S))).
    rewrite /fs_kit_icache /fs_kit_fsinit_ghost.
    cbn [fsc_printk fsc_kalloc fsc_kpages fsc_uart fsc_disk fsc_dlock
         fsc_bio fsc_fs fsc_ireg fsc_ic fsc_itlock fsc_cov fsc_logst
         fsc_bmapstart fsc_size fsc_ninodes].
    rewrite Hdev Histq Hlogq.
    assert (Hset : (((((cov ∖ ({[ (1:Z) ]} : gset Z))
                         ∖ log_region_set (sb_logstart (fss_sb S)))
                        ∖ ireg_blk_set (sb_inodestart (fss_sb S)) icfg_nib)
                       ∖ snap_live_blocks S (snap_live_set S icfg_nib))
                      ∖ snap_bitmap_spent S)
                   = cov ∖ snap_spent S icfg_nib).
    { apply set_eq. intros b. rewrite /snap_spent.
      rewrite 6!elem_of_difference 4!elem_of_union. tauto. }
    rewrite Hset.
    iSplitR; [iPureIntro; reflexivity |].
    iSplitR; [iPureIntro; reflexivity |].
    iSplitR; [iPureIntro; reflexivity |].
    iSplitR; [iPureIntro; reflexivity |].
    iSplitR; [iPureIntro; reflexivity |].
    iSplitR; [iPureIntro; reflexivity |].
    iSplitR; [iPureIntro; reflexivity |].
    iSplitR; [iPureIntro; reflexivity |].
    iSplitR; [iPureIntro; reflexivity |].
    iSplitR; [iPureIntro; reflexivity |].
    iSplitL "Hiref Hlive Hisl Hipool Hpkey Hxkey Hitlk Htok Hmid Hgid Hbio Hpool
             Hkmlk Hdllk Hprlk Hkav Hkauth Hhpn Htkey Hckey".
    { iSplitL "Hiref"; [iExact "Hiref" |].
      iSplitL "Hlive"; [iExact "Hlive" |].
      iSplitL "Hisl"; [iExact "Hisl" |].
      iSplitL "Hipool"; [iExact "Hipool" |].
      iSplitL "Hpkey"; [iExact "Hpkey" |].
      iSplitL "Hxkey"; [iExact "Hxkey" |].
      iSplitL "Hitlk"; [iExact "Hitlk" |].
      iSplitL "Htok"; [iExact "Htok" |].
      iSplitL "Hmid"; [iExact "Hmid" |].
      iSplitL "Hgid"; [iExact "Hgid" |].
      iSplitL "Hbio"; [iExact "Hbio" |].
      iSplitL "Hpool"; [iExact "Hpool" |].
      iSplitL "Hkmlk"; [iExact "Hkmlk" |].
      iSplitL "Hdllk"; [iExact "Hdllk" |].
      iSplitL "Hprlk"; [iExact "Hprlk" |].
      iSplitL "Hkav"; [iExact "Hkav" |].
      iSplitL "Hkauth"; [iExact "Hkauth" |].
      iSplitL "Hhpn"; [iExact "Hhpn" |].
      iSplitL "Htkey"; [iExact "Htkey" | iExact "Hckey"]. }
    iSplitL "Hlogtok"; [iExact "Hlogtok" |].
    iSplitL "Hboot"; [iExact "Hboot" |].
    iSplitR; [iExact "Hireginv" |].
    iEval (rewrite (Hagr 1 (H1home 1 (elem_of_singleton_2 1 1 eq_refl)) HX1))
      in "Hb1".
    iSplitL "Hb1"; [iExact "Hb1" |].
    iSplitL "HaL HaD".
    { iExists (fs_C0 dk cov), (fs_D0 dk cov).
      iSplitR; [iPureIntro; exact (fs_C0_lookup dk cov) |].
      iSplitL "HaL"; [iExact "HaL" | iExact "HaD"]. }
    iSplitL "Hdty"; [iExact "Hdty" |].
    iSplitL "Hhdr"; [iExact "Hhdr" |].
    iSplitL "Hslots"; [iExact "Hslots" |].
    iSplitL "Hbmres"; [iExact "Hbmres" |].
    iSplitL "Hrem"; [iExact "Hrem" |].
    iSplitR; [iExact "Hbinv" | iExact "Hxo"].
  Qed.

End SnapMint.

(* ====================================================================== *)
(*  10.  ERA 0 IS NOT A SPECIAL CASE ANY MORE (durable-disk lane E-himg).  *)
(*                                                                        *)
(*  [fs_cfg_alloc_img] -- the mint applied to [FsDurImg.img_snap_ok], with *)
(*  the spent-set weakening [fs_kit_fsinit_ghost_weaken] and the four      *)
(*  [img_snap_*] readings it needed -- IS DELETED.                          *)
(*  [BootShared.boot_shared_alloc] calls [fs_cfg_alloc_snap] at EVERY era, *)
(*  era 0 included: the boot's file system comes off the crash predicate's *)
(*  durable snapshot, and what the IMAGE still does is produce that        *)
(*  snapshot once, inside [FsCrash.P_fs_alloc] at the top-level theorem    *)
(*  ([FsDurImg.img_snap_ok], which stays).                                 *)
(*                                                                        *)
(*  WHAT THIS LEAVES CALLER-LESS in [FsCfgBoot.v] -- the image ROUTING the *)
(*  deleted corollary was the last reader of, measured: [fs_kit_spent],    *)
(*  [ipool_alloc_of_image], [ent_toks_of_region], [image_ireg_premises],   *)
(*  [bitmap_res_of_image], [ireg_lnks_of_image], [img_nodes_local],        *)
(*  [fs_live_blocks_range], [fs_live_blocks_used], [fs_bitmap_spent_bound],*)
(*  [img_ity_ok], [fs_boot_inodes_ok], [fs_boot_inodes_valid] and the      *)
(*  helpers only they reach.  Their snapshot twins are named at that       *)
(*  file's own deletion note.  Sweeping them is a CLEANUP, not a           *)
(*  correctness step: nothing above [FsDurImg] reads the image decoders.   *)
(* ====================================================================== *)
