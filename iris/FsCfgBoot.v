(* ====================================================================== *)
(* FsCfgBoot.v -- THE BOOT-SIDE ALLOCATION OF THE FILE SYSTEM'S GHOSTS     *)
(*                                                                        *)
(* claude-notes/projects/fs-cfg-boot.md is the plan; this file is its      *)
(* stage 3.  IT STARTS WITH THE STOCKING LEMMA ONLY:                      *)
(* [ipool_alloc_of_image] discharges [IcacheBoot.ipool_alloc]'s ALLOCATED  *)
(* arm from an image's well-formedness (per ruling R5 that arm must be     *)
(* discharged in the era fupd -- [iget] inside [namei("/")] in [userinit]  *)
(* moves a pool bundle into the itable, so the pool has to be             *)
(* image-accurate before [main] runs, and the type-0-only shortcut         *)
(* [IcacheBoot.ipool_alloc_all_free] will not do: the root inode is       *)
(* allocated in every mkfs image).                                        *)
(*                                                                        *)
(* WHAT IS AND IS NOT COMPUTED HERE.  NOTHING.  Every image fact arrives   *)
(* as a HYPOTHESIS (ruling R3): [FsImg]'s NINE boolean sweeps are          *)
(* instantiated at the literal image in [FsImgCheck.v] (measured 241 s of  *)
(* [vm_compute], off the adequacy cone) and reach this lemma through their *)
(* lookup specs.  In particular the live set [A] is a PARAMETER with a     *)
(* membership characterisation ([FsImg.fs_live_set_elem_of]'s shape): the  *)
(* lemma never decides liveness inum by inum, which a measured ~2 s x 208  *)
(* per-inum [vm_compute] ruled out.                                       *)
(*                                                                        *)
(* AND NOTHING WALKS A BIG-OP.  The framing hazard on record              *)
(* ([IcacheEscrow.v]:1516-1522) is that a search walking [inode_blocks]'   *)
(* 268-element big-op costs 48-172 s per sentence, and the image's twenty- *)
(* four live inodes carry 24 x 269 = 6456 slots.  Every step below is a    *)
(* NAMED lemma applied inside one [big_sepS_mono]:                        *)
(* [FsBoot.big_sepS_carve] cuts [cov] into the per-inode block sets        *)
(* (pairwise disjoint by [FsImg.fs_inode_blocks_disjoint], W4) plus the    *)
(* remainder the rest of boot needs, and [FsImgBridge.img_inode_blocks_res] *)
(* -- i.e. [InodeInv.inode_blocks_of_blocks], ONE induction on an abstract *)
(* index list -- turns one inode's block set into its two resources.  The  *)
(* fupd side of [fs_cfg_alloc] must stay O(1) in big-op size the same way. *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac excl.
From iris.base_logic.lib Require Import invariants own ghost_map ghost_var mono_nat.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvModelBytes.
(* THE ERA'S FILE-SYSTEM-STATE GHOSTS (durable-disk 2b-A / B3).  Required
   HERE, ahead of everything else, on purpose: [FsState] exports four names
   that collide with live ones ([fs_view] with [FsBlocks]', [link_auth]
   with [IcacheRef]'s ten-argument ledger, [byte_range]/[blk_owned] with
   [FsBlocks]'), and an earlier [Require Import] is exactly what lets the
   later ones win -- fs-state.md section 7's last two bullets. *)
Require Import FsState.
(* the four name records [fscfg] carries and this file must be able to spell *)
Require Import WpUart.         (* [uart_names]  *)
Require Import VirtioModel.    (* [disk_read]    *)
Require Import DiskPtsto.      (* [disk_names]  *)
Require Import FsBlocks.
Require Import DinodeEnc.
Require Import DirView.
Require Import FsTree.        (* [dir_wins] / [dir_entry] -- the view is an [omap] *)
Require Import DirLinks.
Require Import FsCrash.
Require Import LogDefs.
Require Import LogInv.
(* the era fupd's gname-only mints: the four spinlock ghosts, the buffer
   cache's whole ghost record, the page allocator's count/seal pair *)
Require Import WpLockAt.
Require Import SleepLock.      (* [sl_free_tok] / [slh_auth]: [icfg_isl]'s pair *)
Require Import BioInitAt.
Require Import KallocInv.
Require Import InodeInv.
Require Import InodeLock.   (* [inode_ok] -- the image node's readings, moved down here *)
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheEscrow.
Require Import IcacheBoot.
Require Import FsBoot.
(* debt (D): the bitmap block's resource and the free pool.  [BioDefs] for
   [BSIZE] (the block size [bitmap_bytes] and [fs_bmap_set] are taken at),
   [BitmapEnc] for the encoder the equation is stated over. *)
Require Import BioDefs.
Require Import BitmapEnc.
Require Import BitmapInv.
Require Import FsStateBitmap.
Require Import FsBytesGamma.
Require Import FsImg.
Require Import FsImgBridge.
Require Import FsStateEra.     (* [era_node] / [inode_rec_local] -- the era node *)
Require Import FsCfg.          (* the record this file finally gives a value *)
Require Import Xv6G.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  THE ERA'S INITIAL INODE MAP IS THE IMAGE'S (durable-disk 2b-inode-3)  *)
(* ===================================================================== *)

(* ONE INUM'S NODE, AS THE IMAGE HAS IT.  [FsStateEra.era_node] of the image's
   record, the image's block map and the image's data -- which is EXACTLY
   the node [IcacheBoot.ipool_shape_alloc] ties this inum's [top_frag] to,
   so boot's fragment and the pool's arm name one value by construction and
   no equation is ever stated.

   A FREE inum gets one too, and it is honest: [fs_dinode] at a free slot
   is the image's own type-0 record, whose [di_addrs] is all zeros, so
   [era_node] of it owns no block.  The pool's marker arm carries the fragment
   UNTIED, so nothing reads that value until ialloc re-ties it. *)
Definition img_node (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) : fs_node :=
  era_node (fs_dinode P sb z) (img_blkmap P (fs_dinode P sb z))
        (fs_data_of P (fs_dinode P sb z)).

Definition img_nodes (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
  : gmap Z fs_node :=
  list_to_map ((fun z => (z, img_node P sb z))
                 <$> elements (region_inums nib)).

(* the three [fn_*] readings of [FsCfgBoot.img_node] that this file uses,
   each one delta-step off [FsStateEra.era_node_*] *)
Lemma img_node_rec (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  fn_rec (img_node P sb z) = fs_dinode P sb z.
Proof. reflexivity. Qed.

Lemma img_node_ent (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  fn_ent (img_node P sb z) = bm_ent (img_blkmap P (fs_dinode P sb z)).
Proof. reflexivity. Qed.

Lemma img_node_blk (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  fn_blk (img_node P sb z)
  = node_blk (img_blkmap P (fs_dinode P sb z))
             (fs_data_of P (fs_dinode P sb z)).
Proof. reflexivity. Qed.

(* ---- 2a. A FREE INUM'S NODE IS BARE --------------------------------- *)

Lemma img_node_bare (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) (z : Z) :
  fs_region_bare P sb nib = true -> fs_region_nlink P sb nib = true ->
  0 <= z < 16 * Z.of_nat nib ->
  bv_unsigned (di_type (fs_dinode P sb z)) = 0 ->
  fn_bare (img_node P sb z).
Proof.
  intros Hbare Hnl Hz Hty.
  set (dn := fs_dinode P sb z).
  assert (Hwf : length (di_addrs dn) = 13%nat) by exact (fs_dinode_wf P sb z).
  assert (Ha : forall k : nat, (k < 13)%nat ->
                 bv_unsigned (di_addrs dn !!! k) = 0)
    by (intros k Hk; exact (fs_region_bare_addr P sb nib z k Hbare Hz Hty Hk)).
  assert (Hsz : bv_unsigned (di_size dn) = 0)
    by exact (fs_region_bare_size P sb nib z Hbare Hz Hty).
  (* the addresses, as a list *)
  assert (Haddrs : di_addrs dn = replicate 13 (bv_0 32)).
  { apply list_eq. intros k.
    destruct (Nat.lt_ge_cases k 13) as [Hk | Hk].
    - rewrite (lookup_replicate_2 _ _ _ Hk).
      destruct (lookup_lt_is_Some_2 (di_addrs dn) k ltac:(lia)) as [a Hk'].
      rewrite Hk'. f_equal. apply bv_eq.
      rewrite -(list_lookup_total_correct _ _ _ Hk') (Ha k Hk).
      by change (bv_unsigned (bv_0 32)) with 0.
    - assert (H1 : di_addrs dn !! k = None)
        by (apply lookup_ge_None; lia).
      assert (H2 : (replicate 13 (bv_0 32) : list (bv 32)) !! k = None)
        by (apply lookup_ge_None; rewrite length_replicate; lia).
      rewrite H1 H2 //. }
  assert (Hind : bv_unsigned (bm_ind (img_blkmap P dn)) = 0).
  { rewrite img_blkmap_ind. apply Ha. lia. }
  (* the indirect entries, as a list *)
  assert (Hent : bm_ent (img_blkmap P dn) = replicate FS_NINDIRECT (bv_0 32)).
  { rewrite (img_blkmap_noind P dn Hind). rewrite /NINDIRECT /FS_NINDIRECT //. }
  (* every slot reads zero, so the node owns no block *)
  assert (Hget : forall k : nat, (k < MAXFILE)%nat ->
                   bv_unsigned (blkmap_get (img_blkmap P dn) k) = 0).
  { intros k Hk. rewrite (img_blkmap_get P dn k Hwf Hk) /fs_blk_addr.
    destruct (Nat.ltb_spec k FS_NDIRECT) as [Hd | Hd].
    - apply Ha. unfold FS_NDIRECT in Hd. lia.
    - rewrite /fs_ind_ents. cbv zeta.
      rewrite (proj2 (Z.eqb_eq _ _) (Ha 12%nat ltac:(lia))).
      rewrite lookup_total_replicate_2; [reflexivity |].
      unfold MAXFILE, NDIRECT, NINDIRECT, FS_MAXFILE, FS_NDIRECT,
             FS_NINDIRECT in *. lia. }
  rewrite /fn_bare img_node_rec img_node_ent img_node_blk.
  split; [exact Haddrs |].
  split; [exact Hent |].
  split.
  { apply map_eq. intros k. rewrite node_blk_lookup lookup_empty.
    case_decide as Hc; [| reflexivity].
    exfalso. destruct Hc as [Hk Hnz]. apply Hnz. exact (Hget k Hk). }
  split.
  { rewrite /fn_size img_node_rec. exact Hsz. }
  rewrite /fn_nlink img_node_rec.
  rewrite (fs_region_nlink_free P sb nib z Hnl Hz Hty). reflexivity.
Qed.

Lemma img_inode_local_free (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (z : Z) :
  fs_region_bare P sb nib = true -> fs_region_nlink P sb nib = true ->
  0 <= z < 16 * Z.of_nat nib ->
  bv_unsigned (di_type (fs_dinode P sb z)) = 0 ->
  inode_local z (img_node P sb z).
Proof.
  intros Hbare Hnl Hz Hty.
  apply (inode_local_bare z (img_node P sb z)
           (img_node_bare P sb nib z Hbare Hnl Hz Hty)).
  left. rewrite /fn_type img_node_rec. exact Hty.
Qed.

(* ---- 2b. A LIVE INUM'S NODE, exactly as [FsCfgBoot] reads it --------- *)

Lemma img_inode_ok_at (P : Z -> list (bv 8)) (sb : fs_sb) (cov : gset Z)
    (z : Z) :
  fsimg_wf P sb = true -> fs_blocks_full P ->
  (forall b : Z, fs_data_start sb <= b < sb_size sb -> b ∈ cov) ->
  0 <= z < FsImg.sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
  inode_ok cov (sb_logstart sb) (fs_dinode P sb z)
    (img_blkmap P (fs_dinode P sb z)) (fs_data_of P (fs_dinode P sb z)).
Proof.
  intros Hwf Hfull Hcov Hran Hty.
  exact (img_inode_ok P sb cov (sb_logstart sb) (fs_dinode P sb z)
           (fs_dinode_wf P sb z) (fsimg_wf_sb P sb Hwf) eq_refl Hfull Hcov
           (fsimg_wf_inode P sb z Hwf Hran Hty) Hty
           (fsimg_wf_slot_inj P sb z Hwf Hran Hty)).
Qed.

Lemma img_inode_local_live (P : Z -> list (bv 8)) (sb : fs_sb) (cov : gset Z)
    (nib : nat) (z : Z) :
  fsimg_wf P sb = true -> fs_region_nlink P sb nib = true ->
  fs_blocks_full P ->
  FsImg.sb_ninodes sb <= 16 * Z.of_nat nib ->
  (forall b : Z, fs_data_start sb <= b < sb_size sb -> b ∈ cov) ->
  0 <= z < FsImg.sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
  inode_local z (img_node P sb z).
Proof.
  intros Hwf Hrnl Hfull Hnin Hcov Hran Hty.
  set (dn := fs_dinode P sb z).
  assert (Hok : fs_inode_ok P sb dn)
    by exact (fsimg_wf_inode P sb z Hwf Hran Hty).
  assert (Hdir : bv_unsigned (di_type dn) = T_DIR_z -> fs_dir_ok P sb z dn)
    by (intros Hd; exact (fsimg_wf_dir P sb z Hwf Hran Hd)).
  (* the three record-only facts, each off the sweep that proves it *)
  assert (Hrl : inode_rec_local dn).
  { split_and!.
    - right. exact (fio_type P sb dn Hok).
    - apply (fs_region_nlink_short P sb nib z Hrnl). lia.
    - intros Hd. exact (fdo_gran P sb z dn (Hdir Hd)). }
  apply (inode_local_of_ok_rec z cov (sb_logstart sb) dn
           (img_blkmap P dn) (fs_data_of P dn)
           (img_inode_ok_at P sb cov z Hwf Hfull Hcov Hran Hty) Hrl).
  - exact (img_dir_uniq P sb z dn Hdir).
  - intros Hd Hnl0. exact (fsimg_wf_dots P sb z Hwf Hran Hd Hd Hnl0).
Qed.

(* ...and the two arms as ONE fact over the whole region *)
Lemma img_inode_local (P : Z -> list (bv 8)) (sb : fs_sb) (cov : gset Z)
    (nib : nat) (z : Z) :
  fsimg_wf P sb = true -> fs_region_wf P sb nib = true ->
  fs_region_bare P sb nib = true ->
  fs_blocks_full P ->
  FsImg.sb_ninodes sb <= 16 * Z.of_nat nib ->
  (forall b : Z, fs_data_start sb <= b < sb_size sb -> b ∈ cov) ->
  z ∈ region_inums nib ->
  inode_local z (img_node P sb z).
Proof.
  intros Hwf Hrw Hbare Hfull Hnin Hcov Hz.
  apply region_inums_spec in Hz.
  destruct (decide (bv_unsigned (di_type (fs_dinode P sb z)) = 0))
    as [H0 | Hnz].
  - exact (img_inode_local_free P sb nib z Hbare
             (fs_region_wf_nlink _ _ _ Hrw) Hz H0).
  - assert (Hran : 0 <= z < FsImg.sb_ninodes sb).
    { split; [lia |].
      destruct (Z_lt_ge_dec z (FsImg.sb_ninodes sb)) as [Hlt | Hge];
        [exact Hlt |].
      exfalso. apply Hnz.
      exact (fs_region_free_spec P sb nib z (fs_region_wf_free _ _ _ Hrw)
               ltac:(lia) ltac:(lia) ltac:(lia)). }
    exact (img_inode_local_live P sb cov nib z Hwf
             (fs_region_wf_nlink _ _ _ Hrw) Hfull Hnin Hcov Hran Hnz).
Qed.

Lemma img_nodes_keys (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) :
  ((fun z => (z, img_node P sb z)) <$> elements (region_inums nib)).*1
  = elements (region_inums nib).
Proof.
  rewrite -list_fmap_compose.
  rewrite (list_fmap_ext _ id); [apply list_fmap_id | intros; reflexivity].
Qed.

Lemma img_nodes_nodup (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) :
  base.NoDup (((fun z => (z, img_node P sb z))
                 <$> elements (region_inums nib)).*1).
Proof. rewrite img_nodes_keys. apply NoDup_elements. Qed.

(* the converse reading: a key the node map answers at is a region inum, and
   the answer is the image's own node *)
Lemma img_nodes_lookup_inv (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (z : Z) (n : fs_node) :
  img_nodes P sb nib !! z = Some n ->
  z ∈ region_inums nib /\ n = img_node P sb z.
Proof.
  intros Hz. rewrite /img_nodes in Hz.
  apply elem_of_list_to_map_2 in Hz.
  apply elem_of_list_fmap in Hz as (y & Heq & Hy).
  injection Heq as -> <-. split; [by apply elem_of_elements | reflexivity].
Qed.

(* THE BOOT ROW (durable-disk lane A, plan section 4b): every inode the
   era's abstract map names is well-formed.  It is what
   [InodeRegion.ftop_alloc] takes, and it is the image's own two arms read
   over the map -- conjunct (14) [fs_region_bare] is what makes the FREE
   arm true (a garbage type-0 record would break [inl_size]/[inl_covers]). *)
Lemma img_nodes_local (P : Z -> list (bv 8)) (sb : fs_sb) (cov : gset Z)
    (nib : nat) :
  fsimg_wf P sb = true -> fs_region_wf P sb nib = true ->
  fs_region_bare P sb nib = true ->
  fs_blocks_full P ->
  FsImg.sb_ninodes sb <= 16 * Z.of_nat nib ->
  (forall b : Z, fs_data_start sb <= b < sb_size sb -> b ∈ cov) ->
  forall (i : Z) (n : fs_node),
    img_nodes P sb nib !! i = Some n -> inode_local i n.
Proof.
  intros Hwf Hrw Hbare Hfull Hnin Hcov i n Hi.
  destruct (img_nodes_lookup_inv P sb nib i n Hi) as [Hin ->].
  exact (img_inode_local P sb cov nib i Hwf Hrw Hbare Hfull Hnin Hcov Hin).
Qed.

Lemma img_nodes_lookup (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (z : Z) :
  z ∈ region_inums nib -> img_nodes P sb nib !! z = Some (img_node P sb z).
Proof.
  intros Hz. rewrite /img_nodes.
  apply elem_of_list_to_map; [apply img_nodes_nodup |].
  apply elem_of_list_fmap. exists z. split; [reflexivity |].
  by apply elem_of_elements.
Qed.

(* THE BLOCKS THE LIVE INODES BETWEEN THEM CLAIM.  The carve's own
   spelling, so the remainder [cov ∖ fs_live_blocks P sb A] -- which
   carries the log region, the inode region, the bitmap block and the free
   pool onward to [bio_init]/[initlog]/[ireg_alloc] -- is statable. *)
Definition fs_live_blocks (P : Z -> list (bv 8)) (sb : fs_sb) (A : gset Z)
  : gset Z := ⋃ (fs_inode_blocks_set P sb <$> elements A).

Lemma elem_of_fs_live_blocks (P : Z -> list (bv 8)) (sb : fs_sb) (A : gset Z)
    (b : Z) :
  b ∈ fs_live_blocks P sb A
  <-> exists i : Z, i ∈ A /\ b ∈ fs_inode_blocks P (fs_dinode P sb i).
Proof.
  rewrite /fs_live_blocks elem_of_union_list. split.
  - intros (X & HX & Hb). apply elem_of_list_fmap in HX as (i & -> & Hi).
    apply elem_of_elements in Hi. exists i. split; [exact Hi |].
    rewrite /fs_inode_blocks_set elem_of_list_to_set in Hb. exact Hb.
  - intros (i & Hi & Hb). exists (fs_inode_blocks_set P sb i). split.
    + apply elem_of_list_fmap. exists i. split; [reflexivity |].
      apply elem_of_elements. exact Hi.
    + rewrite /fs_inode_blocks_set elem_of_list_to_set. exact Hb.
Qed.

(* the live inodes' blocks are DATA blocks, and they are exactly what W4's
   used set collects.  Both readings are what puts the bitmap block and the
   free pool OUTSIDE the live set, which is what makes the peel below
   disjoint from the stocking carve. *)
Lemma fs_live_blocks_range (P : Z -> list (bv 8)) (sb : fs_sb) (A : gset Z)
    (b : Z) :
  fsimg_wf P sb = true ->
  (forall z : Z, z ∈ A -> 0 <= z < FsImg.sb_ninodes sb
                          /\ bv_unsigned (di_type (fs_dinode P sb z)) <> 0) ->
  b ∈ fs_live_blocks P sb A -> fs_data_start sb <= b < sb_size sb.
Proof.
  intros Hwf HA Hb. apply elem_of_fs_live_blocks in Hb as (i & Hi & Hb).
  destruct (HA i Hi) as [Hran Hty].
  exact (fs_inode_blocks_range P sb (fs_dinode P sb i) b
           (fsimg_wf_inode P sb i Hwf Hran Hty) Hb).
Qed.

Lemma fs_live_blocks_used (P : Z -> list (bv 8)) (sb : fs_sb) (A u : gset Z)
    (b : Z) :
  fs_used_set P sb = Some u ->
  (forall z : Z, z ∈ A -> 0 <= z < FsImg.sb_ninodes sb
                          /\ bv_unsigned (di_type (fs_dinode P sb z)) <> 0) ->
  b ∈ fs_live_blocks P sb A -> b ∈ u.
Proof.
  intros Hus HA Hb. apply elem_of_fs_live_blocks in Hb as (i & Hi & Hb).
  destruct (HA i Hi) as [Hran Hty].
  apply (fs_used_set_elem P sb u b Hus).
  exact (fs_used_blocks_inode P sb i b Hran Hty Hb).
Qed.

(* ---------------------------------------------------------------------- *)
(*  DEBT (D): THE BITMAP BLOCK AND THE FREE POOL                           *)
(*                                                                        *)
(*  [BitmapInv.bitmap_res] is two things, and boot has both in the          *)
(*  coverage remainder: the bitmap block AT [bitmap_bytes used], and the    *)
(*  byte run of every block whose bit reads CLEAR below [size].             *)
(*                                                                        *)
(*  [used] IS THE BLOCK'S OWN BIT SET ([FsImg.fs_bmap_set]) rather than     *)
(*  "the used set ∪ the metadata blocks": at the block's own bits the       *)
(*  byte-level equation is a theorem ([FsImg.bm_bytes_fs_bmap_set]) and no  *)
(*  new image sweep exists, where the reconstructed set would additionally  *)
(*  need the 6192 bits above [size] swept clear.  Nothing distinguishes     *)
(*  the two: [free_set] intersects [seqZ 0 size].                          *)
(* ---------------------------------------------------------------------- *)
(*  The blocks the producer takes OUT of the remainder: the bitmap block
    itself and the whole free pool.  One set, so [fs_kit_spent] can name it.
    [FsImg.fs_bmap_set BSIZE (P (sb_bmapstart sb))] is written out at every
    site rather than abbreviated: the set is SEALED (see FsImg.v), and an
    abbreviation would put a delta step between two spellings of it at
    every unification. *)
Definition fs_bitmap_spent (P : Z -> list (bv 8)) (sb : fs_sb) : gset Z :=
  {[ FsImg.sb_bmapstart sb ]}
  ∪ free_set (FsImg.sb_size sb)
      (FsImg.fs_bmap_set BSIZE (P (FsImg.sb_bmapstart sb))).

(* every member is either the bitmap block or a free DATA block no inode
   names -- which is what puts [fs_bitmap_spent] inside the remainder. *)
Lemma fs_bitmap_spent_bound (P : Z -> list (bv 8)) (sb : fs_sb) (u : gset Z)
    (b : Z) :
  fsimg_wf P sb = true -> fs_used_set P sb = Some u ->
  b ∈ fs_bitmap_spent P sb ->
  b = FsImg.sb_bmapstart sb
  \/ (fs_data_start sb <= b < FsImg.sb_size sb /\ b ∉ u).
Proof.
  intros Hwf Hus Hb.
  pose proof (fsimg_wf_sb P sb Hwf) as Hsb.
  destruct (fsimg_wf_used P sb Hwf) as (u' & Hus' & _ & Hbw).
  rewrite Hus in Hus'. injection Hus' as <-.
  rewrite /fs_bitmap_spent elem_of_union elem_of_singleton in Hb.
  destruct Hb as [-> | Hb]; [by left |]. right.
  apply elem_of_free_set in Hb as [Hran Hnu].
  destruct (fs_bmap_set_free P sb u b Hsb Hbw Hran Hnu) as [Hge Hnuu].
  split; [lia | exact Hnuu].
Qed.

(* ---------------------------------------------------------------------- *)
(*  THE DINODE BRIDGE (stage-(d) item ii)                                  *)
(* ---------------------------------------------------------------------- *)

(*  [IcacheBoot.ireg_alloc] pays out at [IcacheBoot.image_dinode dss z] --
    the record it DECODED out of the inode block it was handed -- while every
    image fact and the whole stocking lemma is stated at
    [FsImg.fs_dinode P sb z], the record [FsImg]'s own reader produces off
    the block CONTENTS.  Nothing tied the two, and this is the tie: both are
    slot [z mod 16] of block [z / 16], one reached through
    [DinodeEnc.diblk_bytes]' inverse and the other through
    [FsImg.fs_dinode_of_diblk]'s round trip.

    This file is the earliest home: [IcacheBoot.v] does not import [FsImg]
    (and must not -- FsImg's only tracked importer is the image check), and
    [FsImgBridge.v] does not import [IcacheBoot].  Here both sides are in
    scope and nothing new is imported.                                     *)
Lemma image_dinode_fs_dinode (P : Z -> list (bv 8)) (sb : fs_sb)
    (dss : list (list dinode)) (nib : nat) (z : Z) :
  length dss = nib -> Forall diblk_wf dss ->
  (forall bi : nat, (bi < nib)%nat ->
     P (FsImg.sb_inodestart sb + Z.of_nat bi) = diblk_bytes (dss !!! bi)) ->
  0 <= z < 16 * Z.of_nat nib -> 16 * Z.of_nat nib <= 2 ^ 32 ->
  image_dinode dss z = fs_dinode P sb z.
Proof.
  intros Hl Hwf He Hz Hnib.
  (* the block index, and its two arithmetic readings *)
  assert (Hdiv : 0 <= z / 16 < Z.of_nat nib).
  { split; [apply Z.div_pos; lia |].
    apply (Z.div_lt_upper_bound z 16 (Z.of_nat nib)); lia. }
  assert (Hbi : (Z.to_nat (z / 16) < nib)%nat) by (lia).
  (* the inum's [bv 32] round trip *)
  assert (Hbv : bv_unsigned (fs_inum_bv z) = z).
  { unfold fs_inum_bv. apply Z_to_bv_small.
    assert (Hm : bv_modulus 32 = 2 ^ 32) by (reflexivity).
    rewrite Hm. lia. }
  assert (Hblkwf : diblk_wf (dss !!! Z.to_nat (z / 16))).
  { apply (Forall_lookup_1 _ dss (Z.to_nat (z / 16))); [exact Hwf |].
    apply list_lookup_lookup_total_lt. lia. }
  assert (Hblk : P (IBLOCK (fs_inum_bv z) (FsImg.sb_inodestart sb))
                 = diblk_bytes (dss !!! Z.to_nat (z / 16))).
  { unfold IBLOCK. rewrite Hbv.
    rewrite <- (He (Z.to_nat (z / 16)) Hbi).
    f_equal. lia. }
  rewrite (fs_dinode_of_diblk P sb z (dss !!! Z.to_nat (z / 16))
             Hblkwf Hblk).
  (* [islot] is QUALIFIED: another [islot] is in scope from the icache's
     slot vocabulary, and the unqualified [unfold] silently picks it. *)
  unfold image_dinode, DinodeEnc.islot. rewrite Hbv. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(*  THE TICKET COUNT, ONE ELEMENT AT A TIME                                *)
(* ---------------------------------------------------------------------- *)

Lemma fs_tick_count_cons (t z : Z) (L : list Z) :
  fs_tick_count (t :: L) z
  = (if decide (t = z) then S (fs_tick_count L z) else fs_tick_count L z)%nat.
Proof.
  unfold fs_tick_count. cbn [List.filter].
  destruct (decide (t = z)) as [Heq | Hne].
  - rewrite (bool_decide_eq_true_2 (t = z) Heq). reflexivity.
  - rewrite (bool_decide_eq_false_2 (t = z) Hne). reflexivity.
Qed.

Section FsCfgBootPool.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, ICFG : icfg, !irefslotG Σ}.
  Context `{GEN : GenId}.

  (* the carve indexes by [elements A]; the pool by [A] *)
  Lemma big_sepS_of_elements {A0 : Type} `{Countable A0}
      (Φ : A0 -> iProp Σ) (X : gset A0) :
    ([∗ list] x ∈ elements X, Φ x) ⊢ [∗ set] x ∈ X, Φ x.
  Proof.
    rewrite -(big_sepS_list_to_set Φ (elements X) (NoDup_elements X)).
    rewrite list_to_set_elements_L //.
  Qed.

  (* ==================================================================== *)
  (*  THE STOCKING LEMMA                                                  *)
  (* ==================================================================== *)

  (* [P] is the image's block-content function; at the era fupd it is
     [FsCrash.fs_blocks dk] for the boot disk [dk], which is what makes the
     [fs_chalf] halves [FsBoot.fs_boot_ghosts] mints ([fs_blocks dk b] at
     every [b ∈ cov]) the very resources the pool's allocated arm asks for,
     and [FsImgDisk.fsimg_P] IS that at the literal image.

     THE ONE RESOURCE WITH NO PRODUCER IN REACH IS [dir_links] (see the
     report / the file's worklist entry): it is a PREMISE here, exactly as
     [IcacheBoot.ipool_shape_alloc] takes it and for the same reason
     [dinode_at] is a premise -- [dinode_at] is minted by
     [IcacheBoot.ireg_alloc] and arrives inside its [ireg_out] payout,
     while [dir_links]' only constructor [DirLinks.dir_links_of_plain]
     wants one [IcacheRef.ilink] per live non-self record of each image
     directory, which [ireg_alloc]'s all-plain ledger premise
     ([link_auth z 0 ...]) cannot coexist with.  Nothing is improvised for
     it here. *)
  (* [C] IS THE RESOURCE SET, AND IT IS NOT [cov].  The pool's LOGICAL
     coverage is [cov] ([inode_ok]'s [blkmap_wf] is stated at it and the
     pool carries it), but the blocks this lemma is HANDED cannot be all of
     [cov]: [IcacheBoot.ireg_alloc] must run FIRST (it is what pays out the
     [ireg_out] fragments below) and it CONSUMES the inode region's
     [fs_chalf] halves, and the log region's and block 1's go to fsinit.
     So the era fupd peels those off [cov] and passes the rest as [C]; the
     only thing the carve needs of [C] is that it holds the DATA region,
     which is [HcovC] and which the geometry makes free.  Stated with two
     coverage premises rather than [C ⊆ cov] because neither direction of
     inclusion is used: [Hcov] feeds [img_inode_ok], [HcovC] feeds the
     carve. *)
  Lemma ipool_alloc_of_image (γfs : fs_names) (γi : gname)
      (P : Z -> list (bv 8)) (sb : fs_sb) (cov C A : gset Z) :
    (* W1-W8, at an arbitrary image *)
    fsimg_wf P sb = true ->
    (* the [ninodes, 16*nib) tail of the inode region, which no W clause
       sweeps (mkfs rounds the region up: at the literal image
       [ninodes = 200] while [16 * 13 = 208]) *)
    fs_region_free P sb icfg_nib = true ->
    (* L4 AT THE REGION'S WIDTH (durable-disk 2b-inode-3): the nlink bound
       is one of the three record-only facts [inode_ok] does not carry, and
       [FsStateEra.inode_local_of_ok_rec] needs it.  It is
       [FsImg.fs_region_wf]'s second half, so [fs_cfg_alloc] already has
       it and no new image sweep is added. *)
    fs_region_nlink P sb icfg_nib = true ->
    fs_blocks_full P ->
    FsImg.sb_ninodes sb <= 16 * Z.of_nat icfg_nib ->
    16 * Z.of_nat icfg_nib <= 2 ^ 32 ->
    (* the live set as a PARAMETER, with [FsImg.fs_live_set_elem_of]'s
       characterisation -- never a per-inum decision *)
    (forall z : Z, z ∈ A <-> 0 <= z < FsImg.sb_ninodes sb
                             /\ bv_unsigned (di_type (fs_dinode P sb z)) <> 0) ->
    (* R4's coverage corner: every data block is covered.  It is the one
       thing the block layer's [cov] parameter owes the file system, and
       [blkmap_wf]'s home-block clause is what needs it. *)
    (forall b : Z, fs_data_start sb <= b < sb_size sb -> b ∈ cov) ->
    (* ...and the same corner for the RESOURCE set: the carve cuts each live
       inode's block set out of [C], so [C] must hold the data region. *)
    (forall b : Z, fs_data_start sb <= b < sb_size sb -> b ∈ C) ->
    (* the three uncached ledger columns, at [IcacheRef]'s boot splits' own
       keys (plain [Z] over the region; [region_key_shift] is the bridge to
       the pool's [mword] round trip) *)
    ([∗ set] z ∈ region_inums icfg_nib, icnt_half z 0%nat) -∗
    ([∗ set] z ∈ region_inums icfg_nib, frzm_h z false) -∗
    ([∗ set] z ∈ region_inums icfg_nib, ifreeze_off z) -∗
    (* ...and the CONTENTS HOLDS, ALREADY AT THE IMAGE'S TRUTH
       (namei-pinned-lookup.md §9 W3).  The caller mints them at [∅] and
       [dv_set]s each one here's value before calling -- whole ownership
       makes that a free own-update, so this lemma stays an entailment and
       no boot modality moves.  The value is uniform over the whole region:
       at a LIVE inum it is the tie the allocated arm carries, and at a free
       one it is determined garbage the marker arm forgets. *)
    ([∗ set] z ∈ region_inums icfg_nib,
       dv_ride z (dv_of (fs_dinode P sb z) (fs_data_of P (fs_dinode P sb z)))) -∗
    (* ...and the PER-FILE contents holds beside them (N-5.2A), at the same
       keys, from the same sweep and with the same uniformity *)
    ([∗ set] z ∈ region_inums icfg_nib,
       fv_ride z (fv_of (fs_dinode P sb z) (fs_data_of P (fs_dinode P sb z)))) -∗
    (* ...AND THE ERA'S ABSTRACT VALUE, AT THE IMAGE'S OWN NODE
       (durable-disk 2b-inode-3).  One [FsState.top_frag] per LIVE inum,
       allocated by [FsState.fs_boot_alloc_at] at [img_nodes]; it is the very
       node the allocated arm ties to.  A FREE inum's does not come here any
       more (durable-disk C-3c): it parks region-side with its record, in
       [InodeRegion.ireg_top_park], and [IcacheBoot.ireg_alloc] is what takes
       it. *)
    ([∗ set] z ∈ A, top_frag (fs_gamma_L γfs) z (img_node P sb z)) -∗
    (* [ireg_alloc]'s payout, verbatim: the fragment at a live inum, the
       marker at a free one *)
    ([∗ set] z ∈ region_inums icfg_nib,
       ireg_out γi (mword_of_int z : mword 32) (fs_dinode P sb z)) -∗
    ([∗ set] z ∈ A, dlinks γfs z (fs_dinode P sb z)
                      (img_blkmap P (fs_dinode P sb z))
                      (fs_data_of P (fs_dinode P sb z))) -∗
    (* [fs_boot_ghosts]' block big-op, cut down to [C] by the era fupd's
       own peels *)
    ([∗ set] b ∈ C, fsblock (fs_bytes γfs) b (P b)) -∗
    ipool_rows γfs γi cov (sb_logstart sb) (region_inums icfg_nib)
      ∗ ([∗ set] b ∈ C ∖ fs_live_blocks P sb A,
           fsblock (fs_bytes γfs) b (P b)).
  Proof.
    intros Hwf Hrf Hrnl Hfull Hnin Hnib HA Hcov HcovC.
    iIntros "Hcnt Hmir Hoff Hdv Hfv Htop Hout Hdlk Hblk".
    (* ---- the pure preliminaries, all from the sweeps' lookup specs --- *)
    pose proof (fsimg_wf_sb P sb Hwf) as Hsb.
    destruct (fsimg_wf_used P sb Hwf) as (u & _ & Hnd & _).
    assert (HAR : forall z : Z, z ∈ A -> z ∈ region_inums icfg_nib).
    { intros z Hz. apply region_inums_spec. apply HA in Hz. lia. }
    assert (HARs : A ⊆ region_inums icfg_nib)
      by (apply elem_of_subseteq; exact HAR).
    assert (Hty : forall z : Z, z ∈ A ->
              bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
      by (intros z Hz; apply HA in Hz; tauto).
    assert (Hran : forall z : Z, z ∈ A -> 0 <= z < FsImg.sb_ninodes sb)
      by (intros z Hz; apply HA in Hz; tauto).
    assert (Hok : forall z : Z, z ∈ A -> fs_inode_ok P sb (fs_dinode P sb z))
      by (intros z Hz;
          exact (fsimg_wf_inode P sb z Hwf (Hran z Hz) (Hty z Hz))).
    assert (Hinj : forall z : Z, z ∈ A -> fs_slot_inj P (fs_dinode P sb z))
      by (intros z Hz;
          exact (fsimg_wf_slot_inj P sb z Hwf (Hran z Hz) (Hty z Hz))).
    assert (Hdir : forall z : Z, z ∈ A ->
              bv_unsigned (di_type (fs_dinode P sb z)) = T_DIR_z ->
              fs_dir_ok P sb z (fs_dinode P sb z))
      by (intros z Hz Hd; exact (fsimg_wf_dir P sb z Hwf (Hran z Hz) Hd)).
    (* THE THREE RECORD-ONLY FACTS (durable-disk 2b-inode-3), each off the
       image sweep that already proves it: the type enumeration is
       [FsImg.fio_type], the nlink bound is L4 at the region's width, and a
       directory's 16-divisible size is [FsImg.fdo_gran]. *)
    assert (Hrl : forall z : Z, z ∈ A -> inode_rec_local (fs_dinode P sb z)).
    { intros z Hz. split_and!.
      - right. exact (fio_type P sb (fs_dinode P sb z) (Hok z Hz)).
      - apply (fs_region_nlink_short P sb icfg_nib z Hrnl).
        destruct (Hran z Hz) as [Hlo Hhi]. lia.
      - intros Hd. exact (fdo_gran P sb z (fs_dinode P sb z) (Hdir z Hz Hd)). }
    (* the FREE arm's fact: outside [A] the record is typed 0, whether it is
       below [ninodes] (by [A]'s characterisation) or in the tail (W's
       companion [fs_region_free]) *)
    assert (Hfree : forall z : Z, z ∈ region_inums icfg_nib -> z ∉ A ->
              bv_unsigned (di_type (fs_dinode P sb z)) = 0).
    { intros z Hz Hna. apply region_inums_spec in Hz.
      destruct (Z_lt_ge_dec z (FsImg.sb_ninodes sb)) as [Hlt|Hge].
      - destruct (decide (bv_unsigned (di_type (fs_dinode P sb z)) = 0))
          as [H0|H0]; [exact H0 |].
        exfalso. apply Hna, HA. split; [lia | exact H0].
      - exact (fs_region_free_spec P sb icfg_nib z Hrf
                 ltac:(lia) ltac:(lia) ltac:(lia)). }
    (* the carve's two premises *)
    assert (Hsub : forall i : Z, i ∈ elements A ->
              fs_inode_blocks_set P sb i ⊆ C).
    { intros i Hi. apply elem_of_elements in Hi.
      exact (fs_inode_blocks_set_sub P sb i C (Hok i Hi) HcovC). }
    assert (Hdisj : forall i j : Z, i ∈ elements A -> j ∈ elements A ->
              i <> j ->
              fs_inode_blocks_set P sb i ## fs_inode_blocks_set P sb j).
    { intros i j Hi Hj Hne.
      apply elem_of_elements in Hi. apply elem_of_elements in Hj.
      exact (fs_inode_blocks_disjoint P sb i j Hnd (Hran i Hi) (Hran j Hj)
               Hne (Hty i Hi) (Hty j Hj)). }
    (* ---- the ledger columns, shifted onto the pool's keys ------------ *)
    iDestruct (region_key_shift icfg_nib (fun z => icnt_half z 0%nat) Hnib
                 with "Hcnt") as "Hcnt".
    iDestruct (region_key_shift icfg_nib (fun z => frzm_h z false) Hnib
                 with "Hmir") as "Hmir".
    iDestruct (region_key_shift icfg_nib (fun z => ifreeze_off z) Hnib
                 with "Hoff") as "Hoff".
    (* ---- the blocks, carved ------------------------------------------ *)
    rewrite /fs_live_blocks.
    iDestruct (big_sepS_carve
                 (fun b => fsblock (fs_bytes γfs) b (P b))%I
                 C (elements A) (fs_inode_blocks_set P sb)
                 (NoDup_elements A) Hsub Hdisj with "Hblk") as "[Hpc Hrem]".
    iSplitR "Hrem"; [| iExact "Hrem"].
    iDestruct (big_sepS_of_elements
                 (fun i => [∗ set] b ∈ fs_inode_blocks_set P sb i,
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
                (fs_dinode P sb z) (Hfree z Hz1 Hz2) with "H"). }
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
    (* the era's abstract value needs no split: only the LIVE inums' arrive *)
    iRename "Htop" into "HtopA".
    (* ---- the allocated arm, one named application per inum ----------- *)
    iDestruct (big_sepS_sep_2 with "HoutA Hdlk") as "Ha".
    iDestruct (big_sepS_sep_2 with "Ha Hpc") as "Ha".
    iDestruct (big_sepS_sep_2 with "Ha HdvA") as "Ha".
    iDestruct (big_sepS_sep_2 with "Ha HfvA") as "Ha".
    iDestruct (big_sepS_sep_2 with "Ha HtopA") as "Ha".
    iApply (ipool_alloc γfs γi cov (sb_logstart sb)
              (region_inums icfg_nib) A HARs
              with "Hcnt Hmir Hoff [Ha] Hmk HdvF HfvF").
    iApply (big_sepS_mono with "Ha"). intros z Hz.
    pose proof (Hrl z Hz) as Hrlz.
    rewrite (region_inum_faithful icfg_nib z Hnib (HAR z Hz)).
    rewrite /fs_inode_blocks_set.
    iIntros "[[[[[Hreg Hdl] Hblks] Hdv] Hfv] Htopz]".
    iExists (fs_dinode P sb z), (img_blkmap P (fs_dinode P sb z)),
            (fs_data_of P (fs_dinode P sb z)).
    iSplitR.
    { iPureIntro.
      exact (img_inode_ok P sb cov (sb_logstart sb) (fs_dinode P sb z)
               (fs_dinode_wf P sb z) Hsb eq_refl Hfull Hcov
               (Hok z Hz) (Hty z Hz) (Hinj z Hz)). }
    iSplitR; [iPureIntro; exact Hrlz |].
    iSplitR.
    { iPureIntro.
      exact (img_dir_ok P sb z (fs_dinode P sb z) icfg_nib Hnin
               (Hdir z Hz)). }
    iSplitR.
    { iPureIntro. intros Hd Hnl.
      exact (fsimg_wf_dots P sb z Hwf (Hran z Hz) Hd Hd Hnl). }
    iSplitR.
    { iPureIntro.
      exact (img_dir_orphan_clean P sb (fs_dinode P sb z) (Hok z Hz)). }
    iSplitR.
    { iPureIntro.
      exact (img_dir_uniq P sb z (fs_dinode P sb z) (Hdir z Hz)). }
    iSplitL "Hdl"; [iExact "Hdl" |].
    iDestruct (img_inode_blocks_res γfs P sb (fs_dinode P sb z)
                 (fs_dinode_wf P sb z) Hfull (Hok z Hz) (Hinj z Hz)
                 with "Hblks") as "[Hblks Hind]".
    iSplitL "Hreg".
    { iApply (ireg_out_alloc_inv γi (mword_of_int z : mword 32)
                (fs_dinode P sb z) (Hty z Hz) with "Hreg"). }
    iSplitL "Hind"; [iExact "Hind" |].
    iSplitL "Hblks"; [iExact "Hblks" |].
    iSplitL "Htopz"; [rewrite /img_node; iExact "Htopz" |].
    iSplitL "Hdv"; [iExact "Hdv" | iExact "Hfv"].
  Qed.

  (* ==================================================================== *)
  (*  THE [dir_links] PRODUCER (stage-(d) item i)                          *)
  (* ==================================================================== *)

  (*  [ipool_alloc_of_image] above takes the [dir_links] big-op as a PREMISE
      because nothing could produce it: [DirLinks.dir_links_of_plain] wants
      one [IcacheRef.ilink] per live non-self record of each image directory
      and stage A's all-plain ledger ([link_auth z 0 ...]) excluded every
      fragment.  Stage B mints them ([IcacheBoot.link_boot_mint_w] at
      [W := FsImg.fs_link_count P sb]) and this is where they are SPENT.

      THE BOOKKEEPING PROBLEM AND ITS SHAPE.  The mint is per NAMED inum --
      [W z] tickets filed against [z]'s own authority -- while the payload
      is per DIRECTORY: [dir_links z' dn data] consumes one ticket for each
      of [z']'s records, at the inum that record NAMES.  So the supply has
      to be reindexed across directories.  It is done in TWO moves, neither
      of which walks a big-op by search:

        (1) [big_sepS_tick_route] distributes the per-inum PILES onto the
            image's flat ticket LIST ([FsImg.fs_all_tickets]) by ONE
            induction on that list, peeling one pile element per ticket.
            Its arithmetic premise is [fs_tick_count L z <= W z], which at
            [W := fs_link_count P sb] is an equality by definition -- the
            count function IS the pile size, so no counting argument is
            needed anywhere.
        (2) the list is a [mjoin] of per-inum [omap]s, so
            [big_sepL_mjoin] + [big_sepL_omap_match] put each directory's
            sublist back at its own record indices, which is exactly
            [dir_links_of_plain]'s input shape.                            *)

  Lemma big_sepL_mjoin {A : Type} (Φ : A -> iProp Σ) (ls : list (list A)) :
    ([∗ list] x ∈ mjoin ls, Φ x) ⊢ [∗ list] l ∈ ls, [∗ list] x ∈ l, Φ x.
  Proof.
    induction ls as [| l ls IH]; [iIntros "_"; done |].
    rewrite mjoin_cons big_sepL_app big_sepL_cons.
    iIntros "[H1 H2]". iSplitL "H1"; [iExact "H1" |]. iApply (IH with "H2").
  Qed.

  Lemma big_sepL_to_set (Φ : Z -> iProp Σ) (l : list Z) :
    base.NoDup l -> ([∗ list] x ∈ l, Φ x) ⊢ [∗ set] x ∈ list_to_set l, Φ x.
  Proof. intros Hnd. rewrite -(big_sepS_list_to_set Φ l Hnd) //. Qed.

  (* [omap]'s big-op, back at the SOURCE list's indices.  Stated with the
     TARGET predicate abstract and two pointwise premises rather than with a
     [match] in the conclusion: at a [Some] slot the caller turns the ticket
     into the record's payload, at a [None] slot it owes an emp-valid
     payload -- which is literally what [DirLinks.dir_link_at] is at a
     record that bears no ticket. *)
  Lemma big_sepL_omap_mono {A B : Type} (f : A -> option B) (l : list A)
      (Φ : B -> iProp Σ) (Ψ : A -> iProp Σ) :
    (forall (a : A) (b : B), f a = Some b -> Φ b ⊢ Ψ a) ->
    (forall a : A, f a = None -> ⊢ Ψ a) ->
    ([∗ list] x ∈ omap f l, Φ x) ⊢ [∗ list] a ∈ l, Ψ a.
  Proof.
    intros HS HN. induction l as [| a l IH]; [iIntros "_"; done |].
    rewrite big_sepL_cons.
    destruct (f a) as [b |] eqn:Hf.
    - assert (Hc : omap f (a :: l) = b :: omap f l).
      { cbn [omap list_omap]. rewrite Hf. reflexivity. }
      rewrite Hc big_sepL_cons. iIntros "[H1 H2]".
      iSplitL "H1"; [iApply (HS a b Hf); iExact "H1" |].
      iApply (IH with "H2").
    - assert (Hc : omap f (a :: l) = omap f l).
      { cbn [omap list_omap]. rewrite Hf. reflexivity. }
      rewrite Hc. iIntros "H".
      iSplitR; [iApply (HN a Hf) |]. iApply (IH with "H").
  Qed.

  (* a pile's size is all that matters, not where its index list starts *)
  Lemma big_sepL_seq_shift (Ψ : iProp Σ) (n j k : nat) :
    ([∗ list] _ ∈ seq j n, Ψ) ⊢ [∗ list] _ ∈ seq k n, Ψ.
  Proof.
    revert j k. induction n as [| n IH]; intros j k; [iIntros "_"; done |].
    replace (seq j (S n)) with (j :: seq (S j) n) by (reflexivity).
    replace (seq k (S n)) with (k :: seq (S k) n) by (reflexivity).
    rewrite !big_sepL_cons. iIntros "[H1 H2]".
    iSplitL "H1"; [iExact "H1" |]. iApply (IH (S j) (S k) with "H2").
  Qed.

  (* **THE ROUTING.**  Per-inum piles in, the flat demand list out.  ONE
     induction on [L]; the piles are re-formed at a decremented [W] at each
     step, so no big-op is ever walked by a proof search. *)
  Lemma big_sepS_tick_route (Phi : Z -> iProp Σ) (L : list Z) (P : gset Z)
      (W : Z -> nat) :
    (forall t : Z, t ∈ L -> t ∈ P) ->
    (forall z : Z, (fs_tick_count L z <= W z)%nat) ->
    ([∗ set] z ∈ P, [∗ list] _ ∈ seq 0 (W z), Phi z) ⊢ [∗ list] t ∈ L, Phi t.
  Proof.
    revert W. induction L as [| t L IH]; intros W HP HW.
    { iIntros "_". done. }
    assert (HtP : t ∈ P) by (apply HP, elem_of_list_here).
    assert (HP' : forall x : Z, x ∈ L -> x ∈ P)
      by (intros x Hx; apply HP, elem_of_list_further, Hx).
    assert (Ht1 : (1 <= W t)%nat).
    { pose proof (HW t) as H. rewrite fs_tick_count_cons in H.
      rewrite decide_True in H; [lia | reflexivity]. }
    assert (HW' : forall z : Z,
              (fs_tick_count L z
               <= (if decide (z = t) then (W t - 1)%nat else W z))%nat).
    { intros z. destruct (decide (z = t)) as [-> | Hne].
      - pose proof (HW t) as H. rewrite fs_tick_count_cons in H.
        rewrite decide_True in H; [lia | reflexivity].
      - pose proof (HW z) as H. rewrite fs_tick_count_cons in H.
        rewrite decide_False in H; [lia |].
        intros Heq. exact (Hne (eq_sym Heq)). }
    rewrite (big_sepS_delete _ P t HtP) big_sepL_cons.
    replace (W t) with (S (W t - 1))%nat by (lia).
    replace (seq 0 (S (W t - 1))) with (0%nat :: seq 1 (W t - 1))
      by (reflexivity).
    rewrite big_sepL_cons.
    iIntros "[[Htk Ht2] Hrest]".
    iSplitL "Htk"; [iExact "Htk" |].
    iApply (IH (fun z : Z => if decide (z = t) then (W t - 1)%nat else W z)
              HP' HW').
    rewrite (big_sepS_delete _ P t HtP). cbv beta.
    iSplitL "Ht2".
    { rewrite decide_True; [| reflexivity].
      iApply (big_sepL_seq_shift (Phi t) (W t - 1) 1 0 with "Ht2"). }
    iApply (big_sepS_mono with "Hrest"). intros z Hz.
    apply elem_of_difference in Hz as [_ Hz].
    rewrite decide_False; [done |].
    intros ->. apply Hz, elem_of_singleton. reflexivity.
  Qed.

  (* **ONE DIRECTORY'S PAYLOAD**, out of its own ticket sublist.  Every pure
     fact is a lookup spec: W9's [nlink = 1] discharges [DirView.dlc_bound]
     at the all-false flavour map ([dlc_bound_le1]), W9's [z = ROOTINO] is
     [DirLinks.dir_par_tie]'s root exclusion, and a NON-directory's sublist
     is [] so its payload is [DirLinks.dir_links_not_dir]. *)
  Lemma dir_links_of_tickets (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
    fsimg_wf P sb = true -> 0 <= z < FsImg.sb_ninodes sb ->
    ([∗ list] t ∈ fs_dir_tickets_at P sb z, ilink t) -∗
    dir_links z (fs_dinode P sb z) (fs_data_of P (fs_dinode P sb z)).
  Proof.
    intros Hwf Hran.
    rewrite /fs_dir_tickets_at /fs_dir_tickets. cbv zeta.
    destruct (bv_unsigned (di_type (fs_dinode P sb z)) =? T_DIR_z) eqn:Hty.
    - apply Z.eqb_eq in Hty.
      assert (Hnl : bv_unsigned (di_nlink (fs_dinode P sb z)) = 1)
        by exact (fsimg_wf_dir_nlink P sb z Hwf Hran Hty).
      assert (Hrt : bv_unsigned (di_nlink (fs_dinode P sb z)) <> 0 ->
                    (2 <= dir_nrec (bv_unsigned (di_size (fs_dinode P sb z))))%nat ->
                    z = dl_root).
      { intros _ _. rewrite (fsimg_wf_dir_root P sb z Hwf Hran Hty).
        reflexivity. }
      (* the ticket guard IS [dir_link_at]'s guard, so ONE [destruct] on it
         serves the record's payload and the ticket's [option] together *)
      assert (HS : forall (k : nat) (t : Z),
                fs_rec_ticket P z (fs_dinode P sb z) k = Some t ->
                ilink t ⊢ dir_link_at z (fs_dinode P sb z)
                            (fs_data_of P (fs_dinode P sb z)) k).
      { intros k t. rewrite /fs_rec_ticket /dir_link_at. cbv zeta.
        destruct (dir_liveb (fs_data_of P (fs_dinode P sb z)) k
                  && negb (bool_decide
                             (bv_unsigned
                                (dir_inum (fs_data_of P (fs_dinode P sb z)) k)
                              = z))).
        - intros Hk. injection Hk as <-. iIntros "H". iLeft. iExact "H".
        - discriminate. }
      assert (HN : forall k : nat,
                fs_rec_ticket P z (fs_dinode P sb z) k = None ->
                ⊢ dir_link_at z (fs_dinode P sb z)
                    (fs_data_of P (fs_dinode P sb z)) k).
      { intros k. rewrite /fs_rec_ticket /dir_link_at. cbv zeta.
        destruct (dir_liveb (fs_data_of P (fs_dinode P sb z)) k
                  && negb (bool_decide
                             (bv_unsigned
                                (dir_inum (fs_data_of P (fs_dinode P sb z)) k)
                              = z))).
        - discriminate.
        - intros _. done. }
      iIntros "H".
      iApply (dir_links_of_plain z (fs_dinode P sb z)
                (fs_data_of P (fs_dinode P sb z)) Hty
                (dlc_bound_le1 (fun _ => false) (fs_dinode P sb z)
                   (fs_data_of P (fs_dinode P sb z)) ltac:(lia))
                Hrt with "[H]").
      iApply (big_sepL_omap_mono _ _ _ _ HS HN with "H").
    - assert (Hne : bv_unsigned (di_type (fs_dinode P sb z)) <> T_DIR_z)
        by (apply Z.eqb_neq; exact Hty).
      iIntros "_".
      iApply (dir_links_not_dir z (fs_dinode P sb z)
                (fs_data_of P (fs_dinode P sb z)) Hne).
  Qed.

  (* **THE PRODUCER, off the flat ticket list.** *)
  Lemma dir_links_of_image (P : Z -> list (bv 8)) (sb : fs_sb) (A : gset Z) :
    fsimg_wf P sb = true ->
    (forall z : Z, z ∈ A -> 0 <= z < FsImg.sb_ninodes sb) ->
    ([∗ list] t ∈ fs_all_tickets P sb, ilink t) -∗
    [∗ set] z ∈ A, dir_links z (fs_dinode P sb z)
                     (fs_data_of P (fs_dinode P sb z)).
  Proof.
    intros Hwf HA. iIntros "H".
    rewrite /fs_all_tickets.
    iDestruct (big_sepL_mjoin (fun t => ilink t) with "H") as "H".
    rewrite big_sepL_fmap.
    (* one directory at a time, while still indexed by the sweep's [seq] *)
    iAssert ([∗ list] i ∈ seq 0 (Z.to_nat (FsImg.sb_ninodes sb)),
               dir_links (Z.of_nat i) (fs_dinode P sb (Z.of_nat i))
                 (fs_data_of P (fs_dinode P sb (Z.of_nat i))))%I
      with "[H]" as "H".
    { iApply (big_sepL_mono with "H"). intros idx i Hi.
      apply lookup_seq in Hi as [-> Hilt]. iIntros "Ht".
      iApply (dir_links_of_tickets P sb (Z.of_nat (0 + idx)) Hwf
                ltac:(lia) with "Ht"). }
    (* ...then as a SET, then cut down to [A] *)
    iAssert ([∗ list] z ∈ (Z.of_nat <$> seq 0 (Z.to_nat (FsImg.sb_ninodes sb))),
               dir_links z (fs_dinode P sb z)
                 (fs_data_of P (fs_dinode P sb z)))%I with "[H]" as "H".
    { rewrite big_sepL_fmap. iExact "H". }
    assert (Hnd : base.NoDup
                    (Z.of_nat <$> seq 0 (Z.to_nat (FsImg.sb_ninodes sb)))).
    { apply NoDup_fmap_2_strong;
        [intros a b _ _ Hab; lia | apply NoDup_seq]. }
    iDestruct (big_sepL_to_set _ _ Hnd with "H") as "H".
    assert (Hsub : A ⊆ list_to_set
                        (Z.of_nat <$> seq 0 (Z.to_nat (FsImg.sb_ninodes sb)))).
    { apply elem_of_subseteq. intros z Hz.
      apply elem_of_list_to_set, elem_of_list_fmap.
      exists (Z.to_nat z). pose proof (HA z Hz) as Hr.
      assert (Hz0 : 0 <= z) by (lia).
      split; [rewrite (Z2Nat.id z Hz0); reflexivity |].
      apply elem_of_seq. lia. }
    iDestruct (big_sepS_split_sub _ _ A Hsub with "H") as "[H _]".
    iExact "H".
  Qed.

  (* ==================================================================== *)
  (*  THE BRIDGE, SPENT: [ireg_alloc]'s THREE WIDENED IMAGE PREMISES        *)
  (* ==================================================================== *)

  (*  [IcacheBoot.ireg_alloc] states its image obligations at the record it
      DECODED ([IcacheBoot.image_dinode dss z]); [FsImg]'s sweeps state
      theirs at [fs_dinode P sb z].  [image_dinode_fs_dinode] above is the
      tie, and this is where it is spent: at [W := FsImg.fs_link_count P sb]
      the three stage-B premises are exactly W9's three readings.
      (The two STAGE-A premises, [image_free_nlink] (L3) and
      [image_nlink_short] (L4), are NOT here: neither is a conjunct of
      [fsimg_wf] -- W3 sweeps only the LIVE records -- so they still owe
      their own image sweeps.  Recorded, not smuggled.) *)
  Lemma image_link_premises (P : Z -> list (bv 8)) (sb : fs_sb)
      (dss : list (list dinode)) (nib : nat) :
    fsimg_wf P sb = true ->
    length dss = nib -> Forall diblk_wf dss ->
    (forall bi : nat, (bi < nib)%nat ->
       P (FsImg.sb_inodestart sb + Z.of_nat bi) = diblk_bytes (dss !!! bi)) ->
    16 * Z.of_nat nib <= 2 ^ 32 ->
    image_link_le (fs_link_count P sb) dss nib
    /\ image_dir_wl0 (fs_link_count P sb) dss nib.
  Proof.
    intros Hwf Hl Hdwf He Hnib.
    assert (Hbr : forall z : Z, z ∈ region_inums nib ->
              image_dinode dss z = fs_dinode P sb z).
    { intros z Hz. apply region_inums_spec in Hz.
      exact (image_dinode_fs_dinode P sb dss nib z Hl Hdwf He Hz Hnib). }
    split.
    { intros z Hz. rewrite (Hbr z Hz).
      pose proof (fsimg_wf_link_le P sb z Hwf).
      pose proof (proj1 (bv_unsigned_in_range _
                           (di_nlink (fs_dinode P sb z)))). lia. }
    { intros z Hz Hty. rewrite (Hbr z Hz) in Hty.
      apply (fsimg_wf_link_dir P sb z Hwf).
      (* [InodeRegion.ireg_dir_ty] and [DirView.T_DIR_z] are the same 1 *)
      rewrite Hty. reflexivity. }
  Qed.

  (* **THE FORM [fs_cfg_alloc] USES**: straight off
     [IcacheBoot.link_boot_mint_w]'s second column. *)
  Lemma dir_links_of_region (P : Z -> list (bv 8)) (sb : fs_sb) (A : gset Z) :
    fsimg_wf P sb = true ->
    FsImg.sb_ninodes sb <= 16 * Z.of_nat icfg_nib ->
    (forall z : Z, z ∈ A -> 0 <= z < FsImg.sb_ninodes sb) ->
    ([∗ set] z ∈ region_inums icfg_nib,
       [∗ list] _ ∈ seq 0 (fs_link_count P sb z), ilink z) -∗
    [∗ set] z ∈ A, dir_links z (fs_dinode P sb z)
                     (fs_data_of P (fs_dinode P sb z)).
  Proof.
    intros Hwf Hnin HA. iIntros "H".
    iApply (dir_links_of_image P sb A Hwf HA).
    iApply (big_sepS_tick_route (fun z => ilink z) (fs_all_tickets P sb)
              (region_inums icfg_nib) (fs_link_count P sb) with "H").
    - intros t Ht.
      pose proof (fs_all_tickets_range P sb t (fsimg_wf_dirs P sb Hwf) Ht).
      apply region_inums_spec. lia.
    - intros z. unfold fs_link_count. lia.
  Qed.

  (* ================================================================== *)
  (*  THE SAME SUPPLY, NAME-KEYED: [FsStateInode.ent_toks]               *)
  (*  (durable-disk 2b-inode-5)                                          *)
  (* ================================================================== *)

  (*  THE COUNTING RA's tokens are what the payload carries from here on,
      and they are keyed by NAME ([dir_entries], i.e. [FsTree.dir_view])
      where the image's ticket supply is keyed by RECORD INDEX
      ([FsImg.fs_rec_ticket]).  No counting argument is needed to bridge
      them: [dir_view] is itself an [omap] over the SAME [seq 0 nrec], so
      the two supplies are two [omap]s over one index list and the
      reindexing is one induction with a per-index obligation.

      THE PER-INDEX OBLIGATION IS EXACTLY THE SELF EXEMPTION.  A record
      bears a ticket iff it is live and does not name its own home;
      [FsStateInode.ent_tokenless] exempts an entry iff it names its own
      home (or is an orphan's [".."], which no image directory is -- W9
      pins every image directory at [nlink = 1]).  So at a winning record
      the ticket IS the token, and at a self record neither side owes
      anything. *)

  (* TWO [omap]s OVER ONE INDEX LIST. *)
  (* the same, with the index's MEMBERSHIP in hand -- which is what makes
     "this record is inside the directory's record range" available to the
     per-record obligation. *)
  Lemma big_sepL_omap_pair_in {A B C : Type}
      (f : A -> option B) (g : A -> option C) (l : list A)
      (Phi : B -> iProp Σ) (Psi : C -> iProp Σ) :
    (forall (a : A) (b : B) (c : C),
       a ∈ l -> f a = Some b -> g a = Some c -> Phi b ⊢ Psi c) ->
    (forall (a : A) (c : C),
       a ∈ l -> f a = None -> g a = Some c -> ⊢ Psi c) ->
    ([∗ list] x ∈ omap f l, Phi x) ⊢ [∗ list] y ∈ omap g l, Psi y.
  Proof.
    induction l as [| a l IH]; intros HS HN; [iIntros "_"; done |].
    assert (Hcf : omap f (a :: l)
                  = match f a with
                    | Some b => b :: omap f l
                    | None => omap f l
                    end)
      by (cbn [omap list_omap]; destruct (f a); reflexivity).
    assert (Hcg : omap g (a :: l)
                  = match g a with
                    | Some c => c :: omap g l
                    | None => omap g l
                    end)
      by (cbn [omap list_omap]; destruct (g a); reflexivity).
    assert (HS' : forall (x : A) (b : B) (c : C),
                    x ∈ l -> f x = Some b -> g x = Some c -> Phi b ⊢ Psi c)
      by (intros x b c Hx; apply HS; by apply elem_of_cons; right).
    assert (HN' : forall (x : A) (c : C),
                    x ∈ l -> f x = None -> g x = Some c -> ⊢ Psi c)
      by (intros x c Hx; apply HN; by apply elem_of_cons; right).
    assert (Ha : a ∈ a :: l) by (apply elem_of_cons; by left).
    rewrite Hcf Hcg.
    destruct (f a) as [b |] eqn:Hf; destruct (g a) as [c |] eqn:Hg.
    - rewrite !big_sepL_cons. iIntros "[H1 H2]".
      iSplitL "H1"; [iApply (HS a b c Ha Hf Hg); iExact "H1" |].
      iApply (IH HS' HN' with "H2").
    - rewrite big_sepL_cons. iIntros "[_ H2]". iApply (IH HS' HN' with "H2").
    - rewrite big_sepL_cons. iIntros "H".
      iSplitR; [iApply (HN a c Ha Hf Hg) |]. iApply (IH HS' HN' with "H").
    - iIntros "H". iApply (IH HS' HN' with "H").
  Qed.

  Lemma big_sepL_omap_pair {A B C : Type}
      (f : A -> option B) (g : A -> option C) (l : list A)
      (Phi : B -> iProp Σ) (Psi : C -> iProp Σ) :
    (forall (a : A) (b : B) (c : C),
       f a = Some b -> g a = Some c -> Phi b ⊢ Psi c) ->
    (forall (a : A) (c : C), f a = None -> g a = Some c -> ⊢ Psi c) ->
    ([∗ list] x ∈ omap f l, Phi x) ⊢ [∗ list] y ∈ omap g l, Psi y.
  Proof.
    intros HS HN. induction l as [| a l IH]; [iIntros "_"; done |].
    assert (Hcf : omap f (a :: l)
                  = match f a with
                    | Some b => b :: omap f l
                    | None => omap f l
                    end)
      by (cbn [omap list_omap]; destruct (f a); reflexivity).
    assert (Hcg : omap g (a :: l)
                  = match g a with
                    | Some c => c :: omap g l
                    | None => omap g l
                    end)
      by (cbn [omap list_omap]; destruct (g a); reflexivity).
    rewrite Hcf Hcg.
    destruct (f a) as [b |] eqn:Hf; destruct (g a) as [c |] eqn:Hg.
    - rewrite !big_sepL_cons. iIntros "[H1 H2]".
      iSplitL "H1"; [iApply (HS a b c Hf Hg); iExact "H1" |].
      iApply (IH with "H2").
    - rewrite big_sepL_cons. iIntros "[_ H2]". iApply (IH with "H2").
    - rewrite big_sepL_cons. iIntros "H".
      iSplitR; [iApply (HN a c Hf Hg) |]. iApply (IH with "H").
    - iIntros "H". iApply (IH with "H").
  Qed.

  (* ---- [dir_view]'s association list has distinct KEYS --------------- *)

  (* two records that both WIN cannot share a name: the later one's own
     win condition says no earlier live record carries it *)
  Lemma dir_wins_bname_ne (data : nat -> list (bv 8)) (j k : nat) :
    (j < k)%nat -> dir_wins data j = true -> dir_wins data k = true ->
    dir_bname data j <> dir_bname data k.
  Proof.
    intros Hjk Hj Hk Heq.
    apply dir_wins_true in Hk as [_ Hnone].
    apply dir_wins_true in Hj as [Hlj _].
    assert (Hm : dir_match data j (dir_bname data k))
      by (split; [exact Hlj | exact Heq]).
    exact (proj1 (dir_first_None data k (dir_bname data k)) Hnone j Hjk Hm).
  Qed.

  Lemma dir_entry_fst (data : nat -> list (bv 8)) (l : list nat) :
    (omap (dir_entry data) l).*1
    = omap (fun k => if dir_wins data k then Some (dir_bname data k) else None)
           l.
  Proof.
    induction l as [| k l IH]; [reflexivity |].
    cbn [omap list_omap]. rewrite {1}/dir_entry.
    destruct (dir_wins data k); [| exact IH].
    cbn [fmap list_fmap fst]. rewrite IH //.
  Qed.

  Lemma dir_wins_names_nodup (data : nat -> list (bv 8)) (j n : nat) :
    base.NoDup
      (omap (fun k => if dir_wins data k then Some (dir_bname data k) else None)
            (seq j n)).
  Proof.
    revert j. induction n as [| n IH]; intros j; [apply NoDup_nil_2 |].
    replace (seq j (S n)) with (j :: seq (S j) n) by reflexivity.
    cbn [omap list_omap].
    destruct (dir_wins data j) eqn:Hw; [| exact (IH (S j))].
    apply NoDup_cons_2; [| exact (IH (S j))].
    intros Hin. apply elem_of_list_omap in Hin as (k & Hk & Hkeq).
    apply elem_of_seq in Hk.
    destruct (dir_wins data k) eqn:Hwk; [| discriminate Hkeq].
    injection Hkeq as Hkeq.
    exact (dir_wins_bname_ne data j k ltac:(lia) Hw Hwk (eq_sym Hkeq)).
  Qed.

  Lemma dir_entry_names_nodup (data : nat -> list (bv 8)) (nrec : nat) :
    base.NoDup ((omap (dir_entry data) (seq 0 nrec)).*1).
  Proof. rewrite dir_entry_fst. apply dir_wins_names_nodup. Qed.

  (* ---- EVERY TICKETED RECORD OF THE IMAGE IS A NAME RECORD ----------
     -- so its PARENT REGISTER unit is [Some z], and W9's (T) then makes
     that [Some ROOTINO] at every ticket in the image.  A dot record of a
     directory names the directory itself: ["."] by W6's [fdo_dot] at any
     directory, [".."] by W7 at the root, which W9's (T) says is the only
     directory there is.  A record that names its own home carries no
     ticket, so a ticketed record's name is neither. *)
  Lemma img_ticket_par (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) (k : nat) :
    fsimg_wf P sb = true -> 0 <= z < FsImg.sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb z)) = T_DIR_z ->
    (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb z))))%nat ->
    dir_live (fs_data_of P (fs_dinode P sb z)) k ->
    bv_unsigned (dir_inum (fs_data_of P (fs_dinode P sb z)) k) <> z ->
    FsStateInode.ent_par_val z
      (dir_bname (fs_data_of P (fs_dinode P sb z)) k) = Some ROOTINO.
  Proof.
    intros Hwf Hran Hty Hk Hlive Hne.
    pose proof (fsimg_wf_dir P sb z Hwf Hran Hty) as Hdok.
    pose proof (fdo_unique P sb z (fs_dinode P sb z) Hdok) as Hu.
    pose proof (dir_view_live (fs_data_of P (fs_dinode P sb z))
                  (dir_nrec (bv_unsigned (di_size (fs_dinode P sb z))))
                  k Hu Hk Hlive) as Hlk.
    pose proof (fsimg_wf_dir_root P sb z Hwf Hran Hty) as Hzr.
    assert (Hnd : dir_bname (fs_data_of P (fs_dinode P sb z)) k <> DOT).
    { intros Hc. rewrite Hc in Hlk.
      rewrite (fdo_dot P sb z (fs_dinode P sb z) Hdok) in Hlk.
      injection Hlk as Hlk. exact (Hne (eq_sym Hlk)). }
    assert (Hndd : dir_bname (fs_data_of P (fs_dinode P sb z)) k <> DOTDOT).
    { intros Hc. rewrite Hc in Hlk.
      pose proof (fs_root_wf_dotdot P sb (fsimg_wf_root P sb Hwf)) as Hrd.
      rewrite /fs_file_data -Hzr in Hrd.
      rewrite Hrd in Hlk. injection Hlk as Hlk.
      apply Hne. rewrite -Hlk Hzr //. }
    rewrite (FsStateInode.ent_par_val_name z
               (dir_bname (fs_data_of P (fs_dinode P sb z)) k) Hnd Hndd) Hzr //.
  Qed.

  (* ---- ONE DIRECTORY'S TOKENS, out of its own ticket sublist --------- *)

  Lemma ent_toks_of_tickets (gfs : fs_names) (P : Z -> list (bv 8))
      (sb : fs_sb) (z : Z) :
    fsimg_wf P sb = true -> 0 <= z < FsImg.sb_ninodes sb ->
    ([∗ list] t ∈ fs_dir_tickets_at P sb z,
       FsStateLink.link_tok (fs_gamma_L gfs) t
       ∗ FsStateLink.par_tok (fs_gamma_L gfs) t (Some ROOTINO)) -∗
    FsStateInode.ent_toks (fs_gamma_L gfs) z (img_node P sb z).
  Proof.
    intros Hwf Hran.
    rewrite /fs_dir_tickets_at /fs_dir_tickets. cbv zeta.
    destruct (bv_unsigned (di_type (fs_dinode P sb z)) =? T_DIR_z) eqn:Htyb.
    - apply Z.eqb_eq in Htyb.
      assert (Hnz : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
        by (rewrite Htyb /T_DIR_z; lia).
      pose proof (fsimg_wf_inode P sb z Hwf Hran Hnz) as Hiok.
      pose proof (fs_dinode_wf P sb z) as Hdwf.
      assert (Hholes : blk_holes_zero (img_blkmap P (fs_dinode P sb z))
                         (fs_data_of P (fs_dinode P sb z))).
      { intros i Hi H0. apply fs_data_of_holes.
        rewrite <- (img_blkmap_get P (fs_dinode P sb z) i Hdwf Hi). exact H0. }
      assert (Hsz : bv_unsigned (di_size (fs_dinode P sb z))
                    <= Z.of_nat MAXFILE * Z.of_nat BSIZE).
      { rewrite MAXFILE_FS BSIZE_BSIZEz.
        exact (fio_size P sb (fs_dinode P sb z) Hiok). }
      assert (Hents : dir_entries (img_node P sb z)
                      = dir_view (fs_data_of P (fs_dinode P sb z))
                          (dir_nrec (bv_unsigned (di_size (fs_dinode P sb z))))).
      { rewrite /img_node
          (dir_entries_era_node (fs_dinode P sb z)
             (img_blkmap P (fs_dinode P sb z))
             (fs_data_of P (fs_dinode P sb z)) Hholes Hsz).
        rewrite bool_decide_eq_true_2 //. }
      assert (Hnl : bv_unsigned (di_nlink (fs_dinode P sb z)) = 1)
        by exact (fsimg_wf_dir_nlink P sb z Hwf Hran Htyb).
      assert (Horph : fn_orphan (img_node P sb z) = false).
      { rewrite /img_node fn_orphan_era_node. apply bool_decide_eq_false_2.
        rewrite Hnl. cbn. lia. }
      rewrite /FsStateInode.ent_toks Hents Horph /dir_view.
      rewrite (big_sepM_list_to_map
                 (fun s t => FsStateInode.ent_tok (fs_gamma_L gfs) z false s t)
                 _ (dir_entry_names_nodup _ _)).
      iIntros "H".
      iApply (big_sepL_omap_pair_in
                (fs_rec_ticket P z (fs_dinode P sb z))
                (dir_entry (fs_data_of P (fs_dinode P sb z)))
                (seq 0 (dir_nrec (bv_unsigned (di_size (fs_dinode P sb z)))))
                (fun t => (FsStateLink.link_tok (fs_gamma_L gfs) t
                           ∗ FsStateLink.par_tok (fs_gamma_L gfs) t
                               (Some ROOTINO))%I)
                (fun e => FsStateInode.ent_tok (fs_gamma_L gfs) z false e.1 e.2)
                with "H").
      + (* a WINNING record that is not a self record: the ticket IS the
           token *)
        intros k t e Hkin. rewrite /fs_rec_ticket /dir_entry. cbv zeta.
        destruct (dir_wins (fs_data_of P (fs_dinode P sb z)) k) eqn:Hw;
          [| intros _ Hc; discriminate Hc].
        destruct (dir_liveb (fs_data_of P (fs_dinode P sb z)) k
                  && negb (bool_decide
                             (bv_unsigned
                                (dir_inum (fs_data_of P (fs_dinode P sb z)) k)
                              = z))) eqn:Hg;
          [| intros Hc; discriminate Hc].
        intros Ht He. injection Ht as <-. injection He as <-.
        apply andb_true_iff in Hg as [Hlvb Hne].
        apply negb_true_iff, bool_decide_eq_false in Hne.
        apply dir_wins_true in Hw as [Hlv _].
        apply elem_of_seq in Hkin.
        cbn [fst snd].
        rewrite -(img_ticket_par P sb z k Hwf Hran Htyb
                    ltac:(lia) Hlv Hne).
        iIntros "[Ht Hp]".
        iApply (FsStateInode.ent_tok_of_link (fs_gamma_L gfs) z false
                  (dir_bname (fs_data_of P (fs_dinode P sb z)) k)
                  (bv_unsigned (dir_inum (fs_data_of P (fs_dinode P sb z)) k))
                  ltac:(intros _; reflexivity) with "Ht Hp").
      + (* a SELF record: no ticket, and no token owed either *)
        intros k e _. rewrite /fs_rec_ticket /dir_entry. cbv zeta.
        destruct (dir_wins (fs_data_of P (fs_dinode P sb z)) k) eqn:Hw;
          [| intros _ Hc; discriminate Hc].
        apply dir_wins_true in Hw as [Hlv _].
        destruct (dir_liveb (fs_data_of P (fs_dinode P sb z)) k
                  && negb (bool_decide
                             (bv_unsigned
                                (dir_inum (fs_data_of P (fs_dinode P sb z)) k)
                              = z))) eqn:Hg;
          [intros Hc; discriminate Hc |].
        intros _ He. injection He as <-.
        apply andb_false_iff in Hg as [Hd | Hs].
        { exfalso. rewrite (proj2 (dir_liveb_true _ _) Hlv) in Hd.
          discriminate Hd. }
        apply negb_false_iff, bool_decide_eq_true in Hs.
        cbn [fst snd]. rewrite Hs.
        rewrite (FsStateInode.ent_tok_self (fs_gamma_L gfs) z false
                   (dir_bname (fs_data_of P (fs_dinode P sb z)) k)).
        done.
    - assert (Hne : bv_unsigned (di_type (fs_dinode P sb z)) <> T_DIR_z)
        by (apply Z.eqb_neq; exact Htyb).
      iIntros "_".
      rewrite /FsStateInode.ent_toks /img_node
        /dir_entries /fn_is_dir /fn_type era_node_rec.
      rewrite (bool_decide_eq_false_2 _ Hne) big_sepM_empty. done.
  Qed.

  (* ---- ...and the whole image's, off the flat ticket list ------------ *)

  Lemma ent_toks_of_image (gfs : fs_names) (P : Z -> list (bv 8))
      (sb : fs_sb) (A : gset Z) :
    fsimg_wf P sb = true ->
    (forall z : Z, z ∈ A -> 0 <= z < FsImg.sb_ninodes sb) ->
    ([∗ list] t ∈ fs_all_tickets P sb,
       FsStateLink.link_tok (fs_gamma_L gfs) t
       ∗ FsStateLink.par_tok (fs_gamma_L gfs) t (Some ROOTINO)) -∗
    [∗ set] z ∈ A, FsStateInode.ent_toks (fs_gamma_L gfs) z (img_node P sb z).
  Proof.
    intros Hwf HA. iIntros "H".
    rewrite /fs_all_tickets.
    iDestruct (big_sepL_mjoin
                 (fun t => (FsStateLink.link_tok (fs_gamma_L gfs) t
                            ∗ FsStateLink.par_tok (fs_gamma_L gfs) t
                                (Some ROOTINO))%I) with "H")
      as "H".
    rewrite big_sepL_fmap.
    iAssert ([∗ list] i ∈ seq 0 (Z.to_nat (FsImg.sb_ninodes sb)),
               FsStateInode.ent_toks (fs_gamma_L gfs) (Z.of_nat i)
                 (img_node P sb (Z.of_nat i)))%I with "[H]" as "H".
    { iApply (big_sepL_mono with "H"). intros idx i Hi.
      apply lookup_seq in Hi as [-> Hilt]. iIntros "Ht".
      iApply (ent_toks_of_tickets gfs P sb (Z.of_nat (0 + idx)) Hwf
                ltac:(lia) with "Ht"). }
    iAssert ([∗ list] z ∈ (Z.of_nat <$> seq 0 (Z.to_nat (FsImg.sb_ninodes sb))),
               FsStateInode.ent_toks (fs_gamma_L gfs) z (img_node P sb z))%I
      with "[H]" as "H".
    { rewrite big_sepL_fmap. iExact "H". }
    assert (Hnd : base.NoDup
                    (Z.of_nat <$> seq 0 (Z.to_nat (FsImg.sb_ninodes sb)))).
    { apply NoDup_fmap_2_strong;
        [intros a b _ _ Hab; lia | apply NoDup_seq]. }
    iDestruct (big_sepL_to_set _ _ Hnd with "H") as "H".
    assert (Hsub : A ⊆ list_to_set
                        (Z.of_nat <$> seq 0 (Z.to_nat (FsImg.sb_ninodes sb)))).
    { apply elem_of_subseteq. intros z Hz.
      apply elem_of_list_to_set, elem_of_list_fmap.
      exists (Z.to_nat z). pose proof (HA z Hz) as Hr.
      assert (Hz0 : 0 <= z) by (lia).
      split; [rewrite (Z2Nat.id z Hz0); reflexivity |].
      apply elem_of_seq. lia. }
    iDestruct (big_sepS_split_sub _ _ A Hsub with "H") as "[H _]".
    iExact "H".
  Qed.

  (* **THE FORM [fs_cfg_alloc] USES**: per-inum piles in, the directories'
     name-keyed token maps out. *)
  Lemma ent_toks_of_region (gfs : fs_names) (P : Z -> list (bv 8))
      (sb : fs_sb) (A : gset Z) :
    fsimg_wf P sb = true ->
    FsImg.sb_ninodes sb <= 16 * Z.of_nat icfg_nib ->
    (forall z : Z, z ∈ A -> 0 <= z < FsImg.sb_ninodes sb) ->
    ([∗ set] z ∈ region_inums icfg_nib,
       [∗ list] _ ∈ seq 0 (fs_link_count P sb z),
         (FsStateLink.link_tok (fs_gamma_L gfs) z
          ∗ FsStateLink.par_tok (fs_gamma_L gfs) z (Some ROOTINO))) -∗
    [∗ set] z ∈ A, FsStateInode.ent_toks (fs_gamma_L gfs) z (img_node P sb z).
  Proof.
    intros Hwf Hnin HA. iIntros "H".
    iApply (ent_toks_of_image gfs P sb A Hwf HA).
    iApply (big_sepS_tick_route
              (fun z => (FsStateLink.link_tok (fs_gamma_L gfs) z
                         ∗ FsStateLink.par_tok (fs_gamma_L gfs) z
                             (Some ROOTINO))%I)
              (fs_all_tickets P sb)
              (region_inums icfg_nib) (fs_link_count P sb) with "H").
    - intros t Ht.
      pose proof (fs_all_tickets_range P sb t (fsimg_wf_dirs P sb Hwf) Ht).
      apply region_inums_spec. lia.
    - intros z. unfold fs_link_count. lia.
  Qed.

  (* **ALL FIVE CLAUSES OF [ireg_alloc]'s DECODING SLOT**, which is what
      [fs_cfg_alloc] actually has to hand over.  [image_link_premises] above
      supplies the three STAGE-B ones; the two STAGE-A ones (fs-cfg-boot.md
      (d1) debt B) are (L3) [image_free_nlink] and (L4) [image_nlink_short],
      and they are NOT readings of [fsimg_wf]: W3 skips a type-0 record
      entirely, so the free records' link counts are unswept, and nothing
      bounds [nlink] above.  They come off the region-wide sweep
      [FsImg.fs_region_nlink] instead -- region-wide because [ireg_alloc]
      states both over [region_inums nib] and the [[ninodes, 16*nib)] tail's
      (L3) cannot be recovered from [fs_region_free] without circularity
      (that clause is about a type-0 record's [nlink], which is exactly what
      (L3) says).  The conjunction's ORDER is [ireg_alloc]'s own. *)
  Lemma image_ireg_premises (P : Z -> list (bv 8)) (sb : fs_sb)
      (dss : list (list dinode)) (nib : nat) :
    fsimg_wf P sb = true -> fs_region_wf P sb nib = true ->
    (* CONJUNCT (14), spent here for the second time (durable-disk C-3c):
       [IcacheBoot.image_bare] is what makes a free inum's parked node
       [InodeRegion.free_node] of its record. *)
    fs_region_bare P sb nib = true ->
    length dss = nib -> Forall diblk_wf dss ->
    (forall bi : nat, (bi < nib)%nat ->
       P (FsImg.sb_inodestart sb + Z.of_nat bi) = diblk_bytes (dss !!! bi)) ->
    16 * Z.of_nat nib <= 2 ^ 32 ->
    image_free_nlink dss nib /\ image_nlink_short dss nib /\
    image_link_le (fs_link_count P sb) dss nib
    /\ image_dir_wl0 (fs_link_count P sb) dss nib
    /\ image_ty_ok dss nib
    /\ image_nlink_at (fun z => fn_nlink (img_node P sb z)) dss nib
    /\ image_bare dss nib
    /\ image_rec_at (fun z => fs_dinode P sb z) dss nib.
  Proof.
    intros Hwf Hrw Hbare Hl Hdwf He Hnib.
    assert (Hbr : forall z : Z, z ∈ region_inums nib ->
              image_dinode dss z = fs_dinode P sb z).
    { intros z Hz. apply region_inums_spec in Hz.
      exact (image_dinode_fs_dinode P sb dss nib z Hl Hdwf He Hz Hnib). }
    split.
    { intros z Hz Hty. rewrite (Hbr z Hz). rewrite (Hbr z Hz) in Hty.
      apply region_inums_spec in Hz.
      exact (fs_region_nlink_free P sb nib z (fs_region_wf_nlink _ _ _ Hrw)
               Hz Hty). }
    split.
    { intros z Hz. rewrite (Hbr z Hz). apply region_inums_spec in Hz.
      exact (fs_region_nlink_short P sb nib z (fs_region_wf_nlink _ _ _ Hrw)
               Hz). }
    destruct (image_link_premises P sb dss nib Hwf Hl Hdwf He Hnib)
      as (Hle & Hw0).
    split; [exact Hle |]. split; [exact Hw0 |].
    (* THE LINK RA's TIE (durable-disk 2b-inode-4) is [Hbr] and nothing
       else: [img_node]'s record IS [fs_dinode P sb z] ([era_node_rec]). *)
    split.
    2:{ split.
        { intros z Hz.
          rewrite /ireg_nl /fn_nlink /img_node era_node_rec (Hbr z Hz).
          reflexivity. }
        split.
        (* (14) AT THE DECODED RECORD (durable-disk C-3c): [img_node_bare] is
           the sweep, and [InodeRegion.ireg_bare_of_fn_bare] reads the two
           record clauses off it. *)
        { intros z Hz Hty. rewrite (Hbr z Hz). rewrite (Hbr z Hz) in Hty.
          apply region_inums_spec in Hz.
          exact (ireg_bare_of_fn_bare (img_node P sb z)
                   (img_node_bare P sb nib z Hbare
                      (fs_region_wf_nlink _ _ _ Hrw) Hz Hty)). }
        (* ...and the record function the park is indexed by IS the image's *)
        { intros z Hz. rewrite (Hbr z Hz). reflexivity. } }
    (* (L5), the TYPE ENUMERATION (durable-disk 2b-inode-3).  Two arms and
       no new sweep: below [ninodes] a record is either free (type 0) or
       live, and [FsImg.fio_type] is exactly the enumeration at a live one;
       at or above [ninodes] the [fs_region_free] half of [fs_region_wf]
       says the type is 0.  [InodeRegion]'s three constants and
       [DirView]/[FsImg]'s three are the same 1/2/3, by conversion. *)
    intros z Hz. rewrite (Hbr z Hz). apply region_inums_spec in Hz.
    destruct (decide (bv_unsigned (di_type (fs_dinode P sb z)) = 0))
      as [H0 | Hnz]; [by left |].
    destruct (Z_lt_ge_dec z (FsImg.sb_ninodes sb)) as [Hlt | Hge].
    - destruct (fio_type P sb (fs_dinode P sb z)
                  (fsimg_wf_inode P sb z Hwf ltac:(lia) Hnz))
        as [Hd | [Hf | Hv]]; [by right; left | by right; right; left
                             | by right; right; right].
    - exfalso. apply Hnz.
      exact (fs_region_free_spec P sb nib z (fs_region_wf_free _ _ _ Hrw)
               ltac:(lia) ltac:(lia) ltac:(lia)).
  Qed.

End FsCfgBootPool.

(* ====================================================================== *)
(*  THE INODE REGION'S BLOCKS, AS A SET                                    *)
(* ====================================================================== *)

(*  [IcacheBoot.ireg_alloc] wants the region's [fs_chalf] halves as a
    [[∗ list] bi ∈ seq 0 nib]; [FsBoot.fs_boot_ghosts] hands out a
    [[∗ set] b ∈ cov].  This is the set the era fupd peels off [cov] for it,
    and [ireg_blk_of_set] below is the one conversion.  ([LogDefs] already
    has the log region's twin, [log_region_set].)                          *)
Definition ireg_blk_set (ist : Z) (nib : nat) : gset Z :=
  list_to_set ((fun bi : nat => ist + Z.of_nat bi) <$> seq 0 nib).

Lemma ireg_blk_list_nodup (ist : Z) (nib : nat) :
  base.NoDup ((fun bi : nat => ist + Z.of_nat bi) <$> seq 0 nib).
Proof.
  apply NoDup_fmap_2_strong; [intros x y _ _ H; lia | apply NoDup_seq].
Qed.

Lemma ireg_blk_set_spec (ist : Z) (nib : nat) (b : Z) :
  b ∈ ireg_blk_set ist nib <-> ist <= b < ist + Z.of_nat nib.
Proof.
  rewrite /ireg_blk_set elem_of_list_to_set elem_of_list_fmap. split.
  - intros (bi & -> & Hbi). apply elem_of_seq in Hbi. lia.
  - intros Hb. exists (Z.to_nat (b - ist)).
    split; [lia | apply elem_of_seq; lia].
Qed.

(*  THE BLOCKS THE ERA FUPD SPENDS, as one set, so that
    [fs_kit_fsinit_ghost]'s coverage remainder is statable: block 1 (to
    fsinit), the log region (to initlog), the inode region (into
    [ireg_inv]), the bitmap block AND the whole free pool (into
    [BitmapInv.bitmap_inv], debt (D)), and every live inode's own blocks
    (into the pool).  What is LEFT in the remainder is whatever [cov] holds
    that the file system's own geometry does not name -- at the literal
    image, nothing.                                                        *)
Definition fs_kit_spent (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (A : gset Z) : gset Z :=
  ({[ (1:Z) ]} ∪ log_region_set (sb_logstart sb)
     ∪ ireg_blk_set (FsImg.sb_inodestart sb) nib
     ∪ fs_bitmap_spent P sb)
  ∪ fs_live_blocks P sb A.

Section FsCfgBootBitmap.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.

  (*  DEBT (D) PAID.  The whole of [BitmapInv.bitmap_res], out of the
      remainder the stocking carve leaves and nothing else: no new image
      sweep, and the era fupd still computes nothing. *)
  Lemma bitmap_res_of_image (γfs : fs_names) (P : Z -> list (bv 8))
      (sb : fs_sb) :
    fsimg_wf P sb = true ->
    fs_blocks_full P ->
    ([∗ set] b ∈ fs_bitmap_spent P sb, fsblock (fs_bytes γfs) b (P b)) -∗
    bitmap_res γfs (FsImg.sb_bmapstart sb) (FsImg.sb_size sb)
      (FsImg.fs_bmap_set BSIZE (P (FsImg.sb_bmapstart sb))).
  Proof.
    intros Hwf Hfull. iIntros "H".
    pose proof (fsimg_wf_sb P sb Hwf) as Hsb.
    destruct (fsimg_wf_used P sb Hwf) as (u & _ & _ & Hbw).
    (* the bitmap block is below the data region, so it is not in the pool *)
    assert (Hdj : {[ FsImg.sb_bmapstart sb ]}
                  ## free_set (FsImg.sb_size sb)
                       (FsImg.fs_bmap_set BSIZE (P (FsImg.sb_bmapstart sb)))).
    { apply disjoint_singleton_l. intros Hin.
      apply elem_of_free_set in Hin as [Hran Hnu].
      destruct (fs_bmap_set_free P sb u (FsImg.sb_bmapstart sb) Hsb Hbw
                  Hran Hnu) as [Hge _].
      unfold fs_data_start in Hge. lia. }
    (* the byte-level equation, at the block's own bits *)
    assert (Hbytes : bitmap_bytes
                       (FsImg.fs_bmap_set BSIZE (P (FsImg.sb_bmapstart sb)))
                     = P (FsImg.sb_bmapstart sb)).
    { rewrite /bitmap_bytes.
      apply bm_bytes_fs_bmap_set. apply Hfull. }
    rewrite /fs_bitmap_spent (big_sepS_union _ _ _ Hdj) big_sepS_singleton.
    iDestruct "H" as "[Hbm Hpool]".
    rewrite bitmap_res_open Hbytes.
    iSplitL "Hbm"; [iExact "Hbm" |].
    iApply free_pool_intro.
    iApply (big_sepS_mono with "Hpool"). intros b Hb.
    iIntros "Hf". iExists (P b). rewrite -gamma_blk_owned. iExact "Hf".
  Qed.

End FsCfgBootBitmap.


(* ====================================================================== *)
(*  THE TWO BOOT KITS (ruling R6), GHOST ROWS ONLY                         *)
(* ====================================================================== *)

(* [fs_cfg_alloc]'s former mask premise, NAMED.  It was there for the era-0
   /init pins' mint ([dv_lend_mint] opens the inode region), which lane
   E-unpin removed, so [fs_cfg_alloc] no longer takes a mask premise and this
   lemma has NO CALLER today.  Kept because it is the recorded answer to a
   trap that will recur: [BootShared] does not import [InodeRegion], so it
   cannot spell [iregN]; and an inline [ltac:(solve_ndisj)] inside the
   application term is elaborated before the conclusion is unified, which
   stopped working when the era fupd's post grew its B3 rows.  A named lemma
   is neither. *)
Lemma fs_cfg_iregN_top : (↑iregN : coPset) ⊆ ⊤.
Proof. solve_ndisj. Qed.

Section FsCfgBootEra.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !irefslotG Σ}.
  (* B3's two file-system-state cameras are both [Xv6G.xv6G] MEMBERS now
     ([fsTopG] since durable-disk 2b-inode-3, [fsLinkG] since 2b-inode-4),
     so this file -- which is ABOVE the bundle -- binds [xv6G] and NEITHER
     member (durable-notes, "ONE BUNDLE PER GHOST CLASS"). *)
  Context `{GEN : GenId}.

  (* ---- two list/set conversions the era fupd needs -------------------- *)

  Lemma ireg_blk_of_set (Phi : Z -> iProp Σ) (ist : Z) (nib : nat) :
    ([∗ set] b ∈ ireg_blk_set ist nib, Phi b)
    ⊢ [∗ list] bi ∈ seq 0 nib, Phi (ist + Z.of_nat bi).
  Proof.
    rewrite /ireg_blk_set
            (big_sepS_list_to_set Phi _ (ireg_blk_list_nodup ist nib)).
    rewrite big_sepL_fmap //.
  Qed.

  Lemma region_of_seq (Phi : Z -> iProp Σ) (nib : nat) :
    ([∗ list] k ∈ seq 0 (16 * nib), Phi (Z.of_nat k))
    ⊢ [∗ set] z ∈ region_inums nib, Phi z.
  Proof.
    rewrite /region_inums
            (big_sepS_list_to_set Phi _ (region_list_nodup nib)).
    rewrite big_sepL_fmap //.
  Qed.

  (* ==================================================================== *)
  (*  KIT 1 -- WHAT main SPENDS BEFORE +0x9e                               *)
  (* ==================================================================== *)

  (*  Consumed by [IcacheBoot.icache_boot_at] (after iinit, main+0x92),
      [BioInitAt.bio_init_at] (on binit's post, main+0x8e) and the four
      [WpLockAt.newlock_at]s (kmem / virtio_disk / itable / pr) that
      [ProofMain.mn_grp_fs] runs between +0x8e and +0xa2.  ONE opaque
      definition at the ambient names, [FsReady.fs_ready]'s own argument
      applied to the boot side; open it with [fs_kit_icache_open].

      *** WHAT (d2b) MUST ADJOIN, AND FROM WHERE ***  Every row below is a
      GHOST row, because [fs_cfg_alloc] holds no memory at all.  The
      PHYSICAL halves of the same three constructors join at the assembly
      site, and none of them can come from here:

        (P1) [icache_boot_at]'s five physical premises -- [itable_lock ↦₄ 0],
             [lock_name itable_lock "itable"], [lock_cpu itable_lock ↦₈ 0],
             the fifty [SleepLock.sl_fresh (i_lock (ientry k)) "inode"] and
             the fifty [IcacheInv.ientry_raw k].  Producer:
             [BootShared.boot_bss_carve]'s .bss rows plus iinit's own
             postcondition (the [sl_fresh]es exist only after [iinit] runs,
             fs-cfg-boot.md "What must NOT move here").
        (P2) [bio_init_at]'s physical premises -- [bcache_addr ↦₄ 0], its
             name and cpu cells, the thirty [sl_fresh (buf_lock (era_node k))]
             and the thirty zeroed [struct buf] rows, and
             [BcacheInv.bcache_lru bhead (blist 0 NBUF)].  Producer: binit's
             postcondition + [boot_bss_carve].
        (P3) each [newlock_at]'s three cells ([lk ↦₄ 0], [lock_name lk s],
             [lock_cpu lk ↦₈ 0]) and its RESOURCE: [KallocInv.kmem_res] for
             kmem (kinit's post), [DiskInv.disk_res] for virtio_disk
             ([SpecMainSecondary]'s [disk_res_boot], already at
             ProofMain.v:1346-1351), [SpecPrintk.pr_res] for pr.
        (P4) [IrefSlots.iref_slots_auth] and [iref_slots IREFSLOTS] -- NOT
             minted here: their home is [IrefSlots.iref_slots_alloc], run
             inside [BootShared.boot_shared_alloc] beside the [irefslotG]
             instance it returns.  [icache_boot_at] wants the auth; fsinit
             wants one [iref_slot] unit.  Adjoin both from the existing
             boot-shared row.

      The three PERSISTENT products of these constructors ([bio_ctx],
      [is_itable2], [itable_inv], [ic_escrows], [ic_sleeplocks], the three
      locks) go on to [SpecMainSecondary.main_deposit], not into a kit.   *)
  Definition fs_kit_icache (ICFG : icfg) (FSC : fscfg) : iProp Σ :=
    ((* --- [icache_boot_at]'s ghost premises, in its own order --- *)
     own icfg_iref (● (∅ : gmap nat (Qp * positive)) : icacheUR) ∗
     ([∗ list] k ∈ seq 0 (NINODE + NINODE), live_frac k 1%Qp) ∗
     ([∗ list] k ∈ seq 0 NINODE,
        sl_free_tok (icfg_isl k) ∗ slh_auth (icfg_isl k) None) ∗
     (* THE STOCKED POOL (R5): image-accurate before [userinit] runs, so
        that [iget] inside [namei("/")] can move the root's bundle out of
        it.  This is the row [ipool_alloc_of_image] produces. *)
     ipool_rows fsc_fs fsc_ireg fsc_cov fsc_logst (region_inums icfg_nib) ∗
     (* ...and the pool's RESIDENCY KEY, whole (durable-disk B''-esc):
        [icache_boot_at] is what turns the pair into the pool's invariant
        plus the itable lock's [ipool] conjunct. *)
     ghost_var icfg_pool 1 (∅ : gset Z) ∗
     (* ...and its IN-TRANSITION twin (durable-disk C-3b), whole: the pool
        invariant's partition needs both keys. *)
     ghost_var icfg_pext 1 (∅ : gset Z) ∗
     lock_free_tok fsc_itlock ∗
     ([∗ list] k ∈ seq 0 NINODE, ic_tok fsc_ic k) ∗
     ([∗ list] k ∈ seq 0 NINODE, ic_mid fsc_ic k) ∗
     (* the identification family at DUMMY recorded values: [ic_id] is a
        plain [ghost_var] and [icache_boot_at] re-tags every slot to the
        dev/inum words the entry cells actually hold ([ic_id_set]), so the
        era owes no image premise for it (scout verdict 3). *)
     ([∗ list] k ∈ seq 0 NINODE,
        ∃ (v : bool) (d n : mword 32), ic_id fsc_ic k 1 v d n) ∗
     (* --- [bio_init_at]'s ghost premises --- *)
     bio_free_tok fsc_bio ∗
     ([∗ set] b ∈ fsc_cov,
        pool_blk (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) b) ∗
     (* --- the four [newlock_at] ghosts --- *)
     lock_free_tok fsc_kalloc ∗
     lock_free_tok fsc_dlock ∗
     lock_free_tok fsc_printk ∗
     (* --- kinit's page count, at zero: the pair [fsc_kpages] names --- *)
     kalloc_avail fsc_kpages (Some 0%nat) ∗
     kmem_avail_auth fsc_kpages 0%nat ∗
     (* ...AND THE LOCK-WINDOW PIN (durable-disk B''-tx5), one WHOLE element
        per SLOT at [None]: [icache_boot_at]'s escrow loop puts one into
        each arm it builds.  LAST, so no destructuring pattern above moved. *)
     ([∗ list] k ∈ seq 0 NINODE, hpn_full k None) ∗
     (* ...AND THE POOL'S TRANSIT LEDGER (durable-disk C-4), whole and empty.
        LAST, for the pin's reason verbatim. *)
     ghost_var icfg_ptrn 1 (∅ : gmap Z (nat * Qp)) ∗
     (* ...AND THE POOL'S CORPSE LEDGER (durable-disk C-7), whole and empty:
        the image has no corpses.  LAST, for the transit ledger's reason. *)
     ghost_map_auth icfg_pcrp 1 (∅ : gmap Z icorpse))%I.

  Lemma fs_kit_icache_open (ICFG : icfg) (FSC : fscfg) :
    fs_kit_icache ICFG FSC -∗
      own icfg_iref (● (∅ : gmap nat (Qp * positive)) : icacheUR) ∗
      ([∗ list] k ∈ seq 0 (NINODE + NINODE), live_frac k 1%Qp) ∗
      ([∗ list] k ∈ seq 0 NINODE,
         sl_free_tok (icfg_isl k) ∗ slh_auth (icfg_isl k) None) ∗
      ipool_rows fsc_fs fsc_ireg fsc_cov fsc_logst (region_inums icfg_nib) ∗
      ghost_var icfg_pool 1 (∅ : gset Z) ∗
      ghost_var icfg_pext 1 (∅ : gset Z) ∗
      lock_free_tok fsc_itlock ∗
      ([∗ list] k ∈ seq 0 NINODE, ic_tok fsc_ic k) ∗
      ([∗ list] k ∈ seq 0 NINODE, ic_mid fsc_ic k) ∗
      ([∗ list] k ∈ seq 0 NINODE,
         ∃ (v : bool) (d n : mword 32), ic_id fsc_ic k 1 v d n) ∗
      bio_free_tok fsc_bio ∗
      ([∗ set] b ∈ fsc_cov,
         pool_blk (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) b) ∗
      lock_free_tok fsc_kalloc ∗
      lock_free_tok fsc_dlock ∗
      lock_free_tok fsc_printk ∗
      kalloc_avail fsc_kpages (Some 0%nat) ∗
      kmem_avail_auth fsc_kpages 0%nat ∗
      ([∗ list] k ∈ seq 0 NINODE, hpn_full k None) ∗
      ghost_var icfg_ptrn 1 (∅ : gmap Z (nat * Qp)) ∗
      ghost_map_auth icfg_pcrp 1 (∅ : gmap Z icorpse).
  Proof. iIntros "H". iExact "H". Qed.

  (* ==================================================================== *)
  (*  KIT 2 -- WHAT MUST SURVIVE TO forkret'S FIRST ARM                    *)
  (* ==================================================================== *)

  (*  [SpecFsinit.wp_fsinit_sconf_body]'s exclusive premise pile, restricted
      to the rows a fupd that holds NO MEMORY can mint.  Transported by
      widening [FirstTok.first_tok]'s left disjunct (fs-cfg-boot.md
      "Transport to forkret's first arm"); the name says GHOST so the split
      against the physical rows is explicit at the call site.

      *** WHAT (d2b) MUST ADJOIN, AND FROM WHERE ***

        (A) THE RAW CELLS fsinit and initlog write: the 32 [.bss] bytes at
            [&sb] ([∗ list] i ∈ seq 0 32, pa_add sb_base i ↦ₘ _), and
            [log_addr ↦₄ _], [lock_name_field log_addr], [lock_cpu log_addr],
            [l_start], [l_dev], [l_out], [l_cmt], [l_ncommit], [lh_n_pa],
            the thirty [lh_block i].  Producer:
            [BootShared.boot_bss_carve] / [boot_shared_alloc]'s globals row.
        (B) [LogDefs.log_mirror_born].  Producer:
            [BootShared.boot_shared_alloc] -- it is the ERA's mirror
            variable ([RiscvPtsto.mirror_name] = [era_mirror_name
            riscv_eraGS]), which [RiscvAdequacy] mints at power-on AT THE
            PICTURE OF THE DISK THE ERA BOOTS ON and whose other half its
            custody hook puts straight into [FsCrash.P_fs] (durable-disk
            1a), so this fupd cannot mint it and must not try to.
        (C) [IrefSlots.iref_slot] (one unit, for ireclaim's iget/iput pair)
            and [BioDefs.bslots 35].  Producers: the boot-shared
            [iref_slots IREFSLOTS] row, and [bio_init_at]'s POSTCONDITION
            ([bslots BSLOTS_FS] is produced at main+0x8e, not at the era) --
            so the [bslots] must be carried from kit 1's consumption site.
        (D) PAID, and it is a row below rather than an owed one:
            [BitmapInv.bitmap_inv], allocated in the era fupd from
            [BitmapInv.bitmap_res] at [used := FsImg.fs_bmap_set BSIZE
            (P fsc_bmapstart)], the bitmap block's OWN bit set.  Built by
            [bitmap_res_of_image] out of the coverage remainder, which is
            why [fs_kit_spent] now names [fs_bitmap_spent] (the bitmap
            block plus the whole free pool) -- those leave the remainder
            and enter the invariant.  Taking [used] to be the block's own
            bits is what makes the byte-level equation
            [P bmapstart = bitmap_bytes used] a THEOREM
            ([FsImg.bm_bytes_fs_bmap_set]) rather than a new image sweep.
        (E) [FsCrash.fs_crash_seam] and [RiscvPtsto.gen_cert] are
            PERSISTENT and reach fsinit through [main_deposit], not a kit.

      [ireg_inv] is persistent and also travels via [main_deposit]; it is
      here because THIS is where it is produced and it is cheap to carry. *)
  Definition fs_kit_fsinit_ghost (ICFG : icfg) (FSC : fscfg)
      (P : Z -> list (bv 8)) (Rspent : gset Z) : iProp Σ :=
    ((* the log's four gnames at genesis, AT [icfg_log] -- which is what
        makes fsinit's post assemble into [FsReady.fs_ready] *)
     log_free_tok icfg_log ∗
     (* the boot shelter, carried through fsinit into ireclaim *)
     ireg_boot ∗
     ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib ∗
     (* block 1: the superblock's own block, whose bytes pin what bread
        returns to the image *)
     fsblock (fs_bytes fsc_fs) 1 (P 1) ∗
     (* initlog's FsBlocks material.  [L]/[D] are universally quantified in
        [SpecFsinit]'s contract, so an existential here is exactly right --
        with the ONE pure fact the era's own mint establishes and initlog
        needs (durable-disk 1a): the logged view IS the image, block by
        block, on the covered range.  The era's mirror is born at that same
        image, so [L] and the mirror are two readings of one thing, which is
        what turns the boot [log_state] pack's row (b) into computation. *)
     (∃ (L : gmap Z (list (bv 8))) (D : gmap Z bool),
        ⌜forall b : Z, b ∈ fsc_cov -> L !! b = Some (P b)⌝ ∗
        ghost_map_auth (fs_cache fsc_fs) 1 L ∗
        ghost_map_auth (fs_dirty fsc_fs) 1 D) ∗
     ([∗ set] z ∈ fsc_cov, z ↪[fs_dirty fsc_fs]{#(1/2)} false) ∗
     (* the log region, split as [initlog] wants it *)
     fs_chalf fsc_fs (log_hdr_bno fsc_logst) (P (log_hdr_bno fsc_logst)) ∗
     ([∗ list] i ∈ seq 0 LOGBLOCKS,
        ∃ bs : list (bv 8), fs_chalf fsc_fs (log_slot_bno fsc_logst i) bs) ∗
     (* THE BITMAP, row (D): its INVARIANT.  The block itself at its own bit
        set, plus the free pool, are carved out of the coverage remainder by
        [bitmap_res_of_image] in the era fupd and go straight into
        [BitmapInv.bitmap_inv] ([bitmap_inv_alloc]); the set is forgotten
        there and nothing downstream ever names it.  Persistent, like
        [ireg_inv] above. *)
     bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size ∗
     (* THE COVERAGE REMAINDER, PAIRED: everything [cov] holds that the era
        did not spend.  At an image whose [cov] is exactly its own block
        range this is empty; it is kept because [cov] is a parameter. *)
     ([∗ set] b ∈ fsc_cov ∖ Rspent,
        fsblock (fs_bytes fsc_fs) b (P b)))%I.

  Lemma fs_kit_fsinit_ghost_open (ICFG : icfg) (FSC : fscfg)
      (P : Z -> list (bv 8)) (Rspent : gset Z) :
    fs_kit_fsinit_ghost ICFG FSC P Rspent -∗
      log_free_tok icfg_log ∗
      ireg_boot ∗
      ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib ∗
      fsblock (fs_bytes fsc_fs) 1 (P 1) ∗
      (∃ (L : gmap Z (list (bv 8))) (D : gmap Z bool),
         ⌜forall b : Z, b ∈ fsc_cov -> L !! b = Some (P b)⌝ ∗
         ghost_map_auth (fs_cache fsc_fs) 1 L ∗
         ghost_map_auth (fs_dirty fsc_fs) 1 D) ∗
      ([∗ set] z ∈ fsc_cov, z ↪[fs_dirty fsc_fs]{#(1/2)} false) ∗
      fs_chalf fsc_fs (log_hdr_bno fsc_logst) (P (log_hdr_bno fsc_logst)) ∗
      ([∗ list] i ∈ seq 0 LOGBLOCKS,
         ∃ bs : list (bv 8), fs_chalf fsc_fs (log_slot_bno fsc_logst i) bs) ∗
      bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size ∗
      ([∗ set] b ∈ fsc_cov ∖ Rspent,
         fsblock (fs_bytes fsc_fs) b (P b)).
  Proof. iIntros "H". iExact "H". Qed.

  (* ==================================================================== *)
  (*  KIT 1'S TWO EARLY PEELS (stage (e))                                  *)
  (* ==================================================================== *)

  (*  Three of kit 1's fifteen rows are spent BEFORE the inode-cache group:
      the "pr" lock's ghost at main+0x6a ([ProofMain.mn_grp_printk]) and the
      "kmem" lock's ghost plus kinit's genesis page count at main+0x6e
      ([ProofMain.mn_grp_kvm], through [SpecKinit]'s three premises -- debt
      (E)).  They are peeled as NAMED units rather than by opening the kit
      at main's top and handing eleven loose rows to one group: a walk group
      that names one opaque row says what it takes, and nothing has to carry
      another group's material past its own call.                          *)
  Definition fs_kit_printk (ICFG : icfg) (FSC : fscfg) : iProp Σ :=
    lock_free_tok fsc_printk.

  Definition fs_kit_kalloc (ICFG : icfg) (FSC : fscfg) : iProp Σ :=
    (lock_free_tok fsc_kalloc ∗
     kalloc_avail fsc_kpages (Some 0%nat) ∗
     kmem_avail_auth fsc_kpages 0%nat)%I.

  (*  ...and what is left, which is what [icache_boot_at] / [bio_init_at] /
      the vdisk [newlock_at] take between main+0x8e and +0xa2.             *)
  Definition fs_kit_icache_rest (ICFG : icfg) (FSC : fscfg) : iProp Σ :=
    (own icfg_iref (● (∅ : gmap nat (Qp * positive)) : icacheUR) ∗
     ([∗ list] k ∈ seq 0 (NINODE + NINODE), live_frac k 1%Qp) ∗
     ([∗ list] k ∈ seq 0 NINODE,
        sl_free_tok (icfg_isl k) ∗ slh_auth (icfg_isl k) None) ∗
     ipool_rows fsc_fs fsc_ireg fsc_cov fsc_logst (region_inums icfg_nib) ∗
     ghost_var icfg_pool 1 (∅ : gset Z) ∗
     (* ...and its IN-TRANSITION twin (durable-disk C-3b), whole: the pool
        invariant's partition needs both keys. *)
     ghost_var icfg_pext 1 (∅ : gset Z) ∗
     lock_free_tok fsc_itlock ∗
     ([∗ list] k ∈ seq 0 NINODE, ic_tok fsc_ic k) ∗
     ([∗ list] k ∈ seq 0 NINODE, ic_mid fsc_ic k) ∗
     ([∗ list] k ∈ seq 0 NINODE,
        ∃ (v : bool) (d n : mword 32), ic_id fsc_ic k 1 v d n) ∗
     bio_free_tok fsc_bio ∗
     ([∗ set] b ∈ fsc_cov,
        pool_blk (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) b) ∗
     lock_free_tok fsc_dlock ∗
     (* ...AND THE LOCK-WINDOW PIN (durable-disk B''-tx5), one WHOLE element
        per SLOT at [None]: [icache_boot_at]'s escrow loop puts one into
        each arm it builds.  LAST, so no destructuring pattern above moved. *)
     ([∗ list] k ∈ seq 0 NINODE, hpn_full k None) ∗
     (* ...AND THE POOL'S TRANSIT LEDGER (durable-disk C-4), whole and empty.
        LAST, for the pin's reason verbatim. *)
     ghost_var icfg_ptrn 1 (∅ : gmap Z (nat * Qp)) ∗
     (* ...AND THE POOL'S CORPSE LEDGER (durable-disk C-7), whole and empty:
        the image has no corpses.  LAST, for the transit ledger's reason. *)
     ghost_map_auth icfg_pcrp 1 (∅ : gmap Z icorpse))%I.

  Lemma fs_kit_icache_split (ICFG : icfg) (FSC : fscfg) :
    fs_kit_icache ICFG FSC -∗
      fs_kit_printk ICFG FSC ∗ fs_kit_kalloc ICFG FSC ∗
      fs_kit_icache_rest ICFG FSC.
  Proof.
    iIntros "H".
    iDestruct (fs_kit_icache_open with "H")
      as "(Hiref & Hlive & Hislg & Hipool & Hpkey & Hxkey & Hitlk & Htok & Hmid & Hgid &
           Hbio & Hpool & Hkmlk & Hdllk & Hprlk & Hkav & Hkauth & Hhpn & Htkey & Hckey)".
    rewrite /fs_kit_printk /fs_kit_kalloc /fs_kit_icache_rest.
    iFrame "Hprlk Hkmlk Hkav Hkauth Hiref Hlive Hislg Hipool Hpkey Hxkey Hitlk Htok
            Hmid Hgid Hbio Hpool Hdllk Hhpn Htkey Hckey".
  Qed.

  Lemma fs_kit_kalloc_open (ICFG : icfg) (FSC : fscfg) :
    fs_kit_kalloc ICFG FSC -∗
      lock_free_tok fsc_kalloc ∗
      kalloc_avail fsc_kpages (Some 0%nat) ∗
      kmem_avail_auth fsc_kpages 0%nat.
  Proof. iIntros "H". iExact "H". Qed.

  Lemma fs_kit_icache_rest_open (ICFG : icfg) (FSC : fscfg) :
    fs_kit_icache_rest ICFG FSC -∗
      own icfg_iref (● (∅ : gmap nat (Qp * positive)) : icacheUR) ∗
      ([∗ list] k ∈ seq 0 (NINODE + NINODE), live_frac k 1%Qp) ∗
      ([∗ list] k ∈ seq 0 NINODE,
         sl_free_tok (icfg_isl k) ∗ slh_auth (icfg_isl k) None) ∗
      ipool_rows fsc_fs fsc_ireg fsc_cov fsc_logst (region_inums icfg_nib) ∗
      ghost_var icfg_pool 1 (∅ : gset Z) ∗
      ghost_var icfg_pext 1 (∅ : gset Z) ∗
      lock_free_tok fsc_itlock ∗
      ([∗ list] k ∈ seq 0 NINODE, ic_tok fsc_ic k) ∗
      ([∗ list] k ∈ seq 0 NINODE, ic_mid fsc_ic k) ∗
      ([∗ list] k ∈ seq 0 NINODE,
         ∃ (v : bool) (d n : mword 32), ic_id fsc_ic k 1 v d n) ∗
      bio_free_tok fsc_bio ∗
      ([∗ set] b ∈ fsc_cov,
         pool_blk (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) b) ∗
      lock_free_tok fsc_dlock ∗
      ([∗ list] k ∈ seq 0 NINODE, hpn_full k None) ∗
      ghost_var icfg_ptrn 1 (∅ : gmap Z (nat * Qp)) ∗
      ghost_map_auth icfg_pcrp 1 (∅ : gmap Z icorpse).
  Proof. iIntros "H". iExact "H". Qed.

  (*  THE ONE ROW OF KIT 2 THAT main ITSELF NEEDS, peeled without spending
      the kit.  [ireg_inv] is PERSISTENT, so this is a duplication, not a
      split: [SpecUserinit]'s namei corner takes it as one of the four
      inode-cache rows (stage (e)), while the kit as a whole rides on to
      forkret's [fsinit] (stage (f)).  Stated as its own lemma so neither
      site has to know the kit's ordering.                                *)
  Lemma fs_kit_fsinit_ghost_ireg (ICFG : icfg) (FSC : fscfg)
      (P : Z -> list (bv 8)) (Rspent : gset Z) :
    fs_kit_fsinit_ghost ICFG FSC P Rspent -∗
      ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib ∗
      fs_kit_fsinit_ghost ICFG FSC P Rspent.
  Proof.
    iIntros "H".
    iDestruct (fs_kit_fsinit_ghost_open with "H")
      as "(Hlog & Hboot & #Hireg & Hb1 & Hauths & Hdty & Hhdr & Hslots &
           Hbmres & Hrem)".
    iSplitR; [iExact "Hireg" |].
    rewrite /fs_kit_fsinit_ghost.
    iFrame "Hireg Hlog Hboot Hb1 Hauths Hdty Hhdr Hslots Hbmres Hrem".
  Qed.

  (* ...and the same peel for the equally-persistent BITMAP row, so a
     boot client (ProofMain's [first_boot_persist] assembly) reads it off
     the kit without knowing the kit's layout. *)
  Lemma fs_kit_fsinit_ghost_bitmap (ICFG : icfg) (FSC : fscfg)
      (P : Z -> list (bv 8)) (Rspent : gset Z) :
    fs_kit_fsinit_ghost ICFG FSC P Rspent -∗
      bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size ∗
      fs_kit_fsinit_ghost ICFG FSC P Rspent.
  Proof.
    iIntros "H".
    iDestruct (fs_kit_fsinit_ghost_open with "H")
      as "(Hlog & Hboot & #Hireg & Hb1 & Hauths & Hdty & Hhdr & Hslots &
           #Hbmres & Hrem)".
    iSplitR; [iExact "Hbmres" |].
    rewrite /fs_kit_fsinit_ghost.
    iFrame "Hireg Hlog Hboot Hb1 Hauths Hdty Hhdr Hslots Hbmres Hrem".
  Qed.

  (* ==================================================================== *)
  (*  THE ERA FUPD                                                        *)
  (* ==================================================================== *)

  (*  THE POINT.  [IcacheRef.icfg] and [FsCfg.fscfg] reach every proof as
      superclass fields of [FileInvDefs.fileG], an ambient assumption of
      [Main.xv6_boot_era] and of both adequacy theorems, so they are fixed
      before any fupd runs -- and NOTHING in the tree ever produced one.
      This lemma produces both, at the image's own geometry, and hands back
      every ghost the boot chain will need at them.  It runs inside
      [BootShared.boot_shared_alloc] (scout verdict 1: nothing in
      [BootShared.v] uses [fileG], so the new instance lands in the existing
      existential row beside [fdslotG]/[irefslotG]/[pavG]) and the caller
      rebuilds the class with [FileInvDefs.fileG_of].

      IT COMPUTES NOTHING (R3): every image fact is a hypothesis, and the
      geometry fields are instantiated at the parsed superblock's own
      projections (R2).  [γd]/[γv] are REUSED, not re-minted (step 1).

      THE ORDER IS FORCED, and it is the plan's steps 1-6:
        (1) the log's gnames, so [icfg_log] can be filled;
        (2) [IcacheRef.icfg_alloc] at the four ALL-PLAIN boot maps -> ICFG;
        (3) stage B: [link_boot_split] then [link_boot_mint_w] at
            [W := FsImg.fs_link_count] -> the ledger authorities at the
            image's counts AND the [ilink] tickets [dir_links] needs
            (the boot-map-split route is a measured >60 s [linkElemUR]
            conversion -- do not retry it);
        (4) [FsBoot.fs_boot_ghosts] -> γfs and the block ghosts;
        (5) THREE PEELS off [cov], because [ireg_alloc] must run before the
            pool and consumes the inode region's halves;
        (6) [ireg_alloc] -> γi + [ireg_inv] + the [ireg_out] payout,
            restated at [fs_dinode] by [image_dinode_fs_dinode];
        (7) [dir_links_of_region] + [ipool_alloc_of_image] -> the stocked
            pool;
        (8) the gname-only mints, and FSC.                                *)
  (* ---- THE ERA'S INITIAL INODE MAP (durable-disk 2b-A / B3) ----------
     Every inum of the inode region at the ZERO node: no blocks, no
     indirect, size 0, nlink 0, type 0 ([FsStateInode.fn_zero]).  It is NOT
     the image's inode map, and it does not claim to be -- nothing ties
     [γtop] to any bytes yet, because no [inode_owned] at [Γ_L] exists in
     the tree.  What it IS is the only shape from which the family can ever
     GROW: [fsLinkUR = gmapUR Z (authR natUR)] has no authority over which
     KEYS exist, so a family allocated at [ε] can never be extended (nothing
     mints [{[i := ● n]}] out of nothing), while [● 0] at every inum can be
     raised to the record's real [nlink] with the auth in hand
     ([nat_local_update]).  Stage 4 replaces the whole allocation with
     [FsState.fs_state_mint] off [P_wf], which is why no image decode is
     built here. *)
  Definition fs_boot_inodes (nib : nat) : gmap Z fs_node :=
    gset_to_gmap fn_zero (region_inums nib).

  Lemma fs_boot_inodes_no_ents (nib : nat) (i : Z) (n : fs_node) :
    fs_boot_inodes nib !! i = Some n -> dir_entries n = ∅.
  Proof.
    rewrite /fs_boot_inodes. intros Hi.
    apply lookup_gset_to_gmap_Some in Hi as [_ Heq].
    rewrite -Heq. exact (dir_entries_bare fn_zero fn_bare_zero).
  Qed.

  (* THE BOOT'S OWN OBLIGATION, DISCHARGED.  [✓ link_elem I] is the
     tokens-<=-nlink law of the initial map -- the fact [FsState.fs_links_valid]
     READS OFF the durable instance at the mint, and which the boot, having no
     durable instance, owes.  At the zero map it is free: no node has an entry,
     so no token exists and every inum's auth stands alone. *)
  Lemma fs_boot_inodes_ok (nib : nat) :
    link_elem_ok (fs_boot_inodes nib) (fun _ => ∅).
  Proof.
    intros i n Hi. rewrite /fn_par_ok gmultiset_size_empty. lia.
  Qed.

  Lemma fs_boot_inodes_valid (nib : nat) :
    ✓ link_elem (fs_boot_inodes nib) (fun _ => ∅).
  Proof.
    apply link_elem_valid_no_ents. exact (fs_boot_inodes_no_ents nib).
  Qed.

  (* the era's initial top map, as a big-op over the region's inums --
     which is the shape the pool's stocking takes (durable-disk
     2b-inode-3) *)
  Lemma big_sepM_img_nodes (Φ : Z -> fs_node -> iProp Σ)
      (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) :
    ([∗ map] i ↦ n ∈ img_nodes P sb nib, Φ i n)
    ⊣⊢ ([∗ set] z ∈ region_inums nib, Φ z (img_node P sb z)).
  Proof.
    rewrite /img_nodes.
    rewrite (big_sepM_list_to_map Φ _ (img_nodes_nodup P sb nib)).
    rewrite big_sepL_fmap /=.
    rewrite big_sepS_elements //.
  Qed.

  (* ...and the LINK family in the shape [IcacheBoot.ireg_alloc] takes
     (durable-disk 2b-inode-4): one authority per region inum, standing at
     the image record's own [nlink], with every token still at home.
     [FsState.fs_boot_alloc_full] allocates it at [img_nodes] and owes NO
     validity -- nothing is outstanding -- so no image sweep is spent here;
     the links step, which hands a directory's tokens to its checked-out
     payload, is what makes W9 + conjunct (13) [FsImg.fs_links_eq] come
     due. *)
  (* THE IMAGE'S REGISTER CHOICE: every unit at an inum comes from the ONE
     directory a well-formed image has (W9's (T)), so the pile is [nlink]
     copies of [Some ROOTINO].  Its SIZE is what [InodeRegion.ireg_par]'s
     bound reads; the values are what the entries demand. *)
  Definition img_par (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z)
    : gmultiset (option Z) :=
    FsStateLink.par_reps (fn_nlink (img_node P sb z)) (Some ROOTINO).

  Lemma ireg_lnks_of_image (γfs : fs_names)
      (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) :
    fsimg_wf P sb = true ->
    fs_links_full (fs_link γfs) (img_nodes P sb nib) (img_par P sb) -∗
    ([∗ set] z ∈ region_inums nib,
       ireg_lnk_at γfs z (fn_nlink (img_node P sb z)))
    ∗ ([∗ set] z ∈ region_inums nib,
         [∗ list] _ ∈ seq 0 (fs_link_count P sb z),
           (FsStateLink.link_tok (fs_gamma_L γfs) z
            ∗ FsStateLink.par_tok (fs_gamma_L γfs) z (Some ROOTINO))).
  Proof.
    intros Hwf.
    (* THE ONE ARITHMETIC FACT, AND IT IS W9's (durable-disk 2b-inode-5).
       At every inum the image's ticket demand is at most the record's own
       [nlink] ([FsImg.fsimg_wf_link_le], W9's first clause, extended off
       the sweep's range by [fs_link_count_out]); at the ROOT there is one
       unit of SLACK on top of it, because the root's [".."] is a SELF
       record and pays for nothing while W9 pins the root at count 0 and
       [nlink = 1].  That slack IS the keep-alive token. *)
    assert (Hle : forall z : Z,
              (fs_link_count P sb z
               + (if bool_decide (z = InodeRegion.ireg_root) then 1 else 0)
               <= fn_nlink (img_node P sb z))%nat).
    { intros z.
      pose proof (fsimg_wf_link_le P sb z Hwf) as Hc.
      pose proof (proj1 (bv_unsigned_in_range _
                           (di_nlink (fs_dinode P sb z)))) as Hnn.
      rewrite /fn_nlink /img_node era_node_rec.
      destruct (bool_decide (z = InodeRegion.ireg_root)) eqn:Hr.
      - apply bool_decide_eq_true in Hr.
        destruct (fsimg_wf_root_link P sb Hwf) as [Hc0 Hnl].
        assert (Hz1 : z = ROOTINO) by (rewrite Hr; reflexivity).
        rewrite Hz1 Hc0 Hnl. lia.
      - lia. }
    assert (Hpc : forall z : Z,
              (fs_link_count P sb z <= fn_nlink (img_node P sb z))%nat).
    { intros z. pose proof (Hle z). lia. }
    rewrite /fs_links_full.
    rewrite (big_sepM_img_nodes
               (fun i n => own (fs_link γfs)
                             (link_full_elem i (fn_nlink n) (img_par P sb i)))
               P sb nib).
    rewrite -big_sepS_sep.
    iIntros "H". iApply (big_sepS_mono with "H"). intros z _.
    rewrite (link_full_split (fs_gamma_L γfs) z (fn_nlink (img_node P sb z))
               (img_par P sb z)).
    iIntros "[[Ha Ht] [Hpa Hpt]]".
    iDestruct (FsStateLink.link_toks_le_split (fs_gamma_L γfs) z
                 (fn_nlink (img_node P sb z))
                 (fs_link_count P sb z
                  + (if bool_decide (z = InodeRegion.ireg_root)
                     then 1%nat else 0%nat))
                 (Hle z) with "Ht") as "[Ht _]".
    iEval (rewrite FsStateLink.link_toks_split) in "Ht".
    iDestruct "Ht" as "[Htc Htk]".
    rewrite /img_par.
    iDestruct (FsStateLink.par_toks_le_split (fs_gamma_L γfs) z
                 (fn_nlink (img_node P sb z)) (fs_link_count P sb z)
                 (Some ROOTINO) (Hpc z) with "Hpt") as "[Hpt _]".
    rewrite /ireg_lnk_at /InodeRegion.ireg_keep /InodeRegion.ireg_par.
    iSplitR "Htc Hpt".
    - iFrame "Ha". iSplitR "Hpa".
      + destruct (bool_decide (z = InodeRegion.ireg_root));
          [iExact "Htk" | iClear "Htk"; done].
      + iExists (FsStateLink.par_reps (fn_nlink (img_node P sb z))
                   (Some ROOTINO)).
        iFrame "Hpa". iPureIntro. rewrite FsStateLink.par_reps_size. lia.
    - rewrite big_sepL_sep.
      iSplitL "Htc"; [iApply (FsStateLink.link_toks_list with "Htc") |].
      iApply (FsStateLink.par_toks_list with "Hpt").
  Qed.

  Lemma fs_cfg_alloc (γd : uart_names) (γv : disk_names)
      (dk : Z -> bv 8) (ndisk : nat) (sb : fs_sb) (cov : gset Z)
      (nib : nat) (E : coPset) :
    (* ---- the image, all as hypotheses (R3) ---- *)
    fsimg_wf (fs_blocks dk) sb = true ->
    fs_region_wf (fs_blocks dk) sb nib = true ->
    (* CONJUNCT (14) (durable-disk lane A): a free slot's record is BARE.
       It is what makes the locked registry's boot row true at a FREE inum
       -- [inode_local]'s size and coverage clauses would be false of a
       garbage type-0 record -- and it is cited at the literal image by
       [FsImgCheck.fsimg_region_bare], so the adequacy cone pays nothing. *)
    fs_region_bare (fs_blocks dk) sb nib = true ->
    FsImg.sb_ninodes sb <= 16 * Z.of_nat nib ->
    16 * Z.of_nat nib <= 2 ^ 32 ->
    (0 < nib)%nat ->
    (* the inode region is EXACTLY [[inodestart, bmapstart)]: mkfs rounds
       [ninodes] up to a whole block, and this is the equation that makes
       the block layout below linear. *)
    Z.of_nat nib = FsImg.sb_ninodes sb / 16 + 1 ->
    (* ---- R4's coverage corners ---- *)
    fs_cov_in cov ndisk ->
    (forall b : Z, 1 <= b < fs_data_start sb -> b ∈ cov) ->
    (forall b : Z, fs_data_start sb <= b < sb_size sb -> b ∈ cov) ->
    disk_bytes γv 0 (disk_read dk 0 ndisk) -∗
    (* THE BIO SLOT SUPPLY, THREADED IN.  Its ghost name is canonical
       ([Xv6Cameras.bioslot_name]), so it exists before this era fupd runs
       and [BioDefs.bslots_alloc] is what mints it -- one layer up, beside
       the other name-carrying classes.  Both halves come in because
       [BioInitAt.bio_free_tok] carries both. *)
    bslots_auth -∗ bslots BSLOTS_FS ={E}=∗
    ∃ (ICFG : icfg) (FSC : fscfg),
      (* ---- durable-disk 2b-inode-3: THE TOP MAP IS ROUTED, NOT HANDED
         OUT.  It is allocated at the IMAGE's node map ([img_nodes]) rather
         than at the zero map, its AUTHORITY goes into
         [InodeRegion.ftop_inv] (which [ireg_inv] then carries, so every fs
         contract in the cone has it), and its per-inum FRAGMENTS go into
         the free pool -- tied inside [IcacheEscrow.ipool_alloc] at a live
         inum, untied on the marker arm at a free one.  Nothing about the
         top map leaves this lemma any more.

         AND SO IS THE LINK FAMILY, since durable-disk 2b-inode-4: it is
         allocated at the IMAGE's records in its FULL shape (each inum's
         authority at that record's [nlink], with all its tokens still at
         home) and routed into the inode region, where the RA's law is
         readable.  Neither ghost leaves this lemma. *)
      (* ---- durable-disk lane E-unpin: THE ERA-0 /init PINS ARE GONE.
         This post used to carry [dv_pin ROOTINO ...] and [fv_pin 7 ...] --
         "the root's contents are mkfs's" and "/init is inum 7 with the
         tracked bytes" -- minted by cutting root's dview lend and inum 7's
         fview lend inside the proof.  They are image-CONTENT facts, false
         at any era after a crash, and they made the adequacy theorem carry
         hard-coded content hooks for no durability reason.  Removed from
         the boot chain (era 0 included); the era's file system is minted
         from the durable snapshot and the boot chain uses the generic exec
         contract at whatever inum 7 holds.  The pinned-lookup theorems that
         consumed them are kept in the tree but commented out of
         [iris/_CoqProject], for the fs-syscall-specs project to port; see
         claude-notes/projects/namei-pinned-lookup.md's banner. *)
      ⌜icfg_dev = ROOTDEV⌝ ∗ ⌜icfg_nib = nib⌝ ∗
      ⌜icfg_ist = FsImg.sb_inodestart sb⌝ ∗
      ⌜fsc_uart = γd⌝ ∗ ⌜fsc_disk = γv⌝ ∗ ⌜fsc_cov = cov⌝ ∗
      ⌜fsc_logst = sb_logstart sb⌝ ∗
      ⌜fsc_bmapstart = FsImg.sb_bmapstart sb⌝ ∗
      ⌜fsc_size = sb_size sb⌝ ∗ ⌜fsc_ninodes = FsImg.sb_ninodes sb⌝ ∗
      fs_kit_icache ICFG FSC ∗
      fs_kit_fsinit_ghost ICFG FSC (fs_blocks dk)
        (fs_kit_spent (fs_blocks dk) sb nib (fs_live_set (fs_blocks dk) sb)).
  Proof.
    intros Hwf Hrw Hbare Hnin Hnib32 Hnib0 Hnibeq Hcovin Hcovmeta Hcovdata.
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
            γlog (FsImg.sb_inodestart sb)
            (link_boot_map_valid _) (icnt_boot_map_valid _)
            (frzo_boot_map_valid _) (frzm_boot_map_valid _)
            (dview_boot_map_valid _) (fview_boot_map_valid _))
      as (ICFG g0) "(%Hdev & %Hnibq & %Hlogq & %Histq & Hiref & Hlive &
                     Hlk & Hcnt & Hfrzo & Hfrzm & Hdv & Hfv & Hboot & Hep &
                     Hisl & Hrauth & Hlkauth & Hpkey & Hxkey & Hhpn & Htkey &
                     Hckey)".
    (* the lock-window pin's boot map, fanned out one whole element per slot
       (durable-disk B''-tx5) *)
    iDestruct (hpn_boot_split with "Hhpn") as "Hhpn".
    (* every ambient form below is stated at [icfg_nib]; make the caller's
       [nib] BE it, so no lemma has to be re-instantiated *)
    symmetry in Hnibq. subst nib.
    (* ---- the pure geometry, off [fs_sb_ok] alone -------------------- *)
    pose proof (fsimg_wf_sb _ _ Hwf) as Hsb.
    pose proof (sbo_logstart sb Hsb) as Hls.
    pose proof (sbo_nlog sb Hsb) as Hnl.
    pose proof (sbo_inodestart sb Hsb) as Hist.
    pose proof (sbo_bmapstart sb Hsb) as Hbms.
    assert (Hfull : fs_blocks_full (fs_blocks dk))
      by (intros b; apply fs_blocks_length).
    assert (Hds : fs_data_start sb
                  = FsImg.sb_inodestart sb + Z.of_nat icfg_nib + 1)
      by (rewrite /fs_data_start; lia).
    assert (HlogI : forall b : Z, b ∈ log_region_set (sb_logstart sb) ->
              1 < b < FsImg.sb_inodestart sb).
    { intros b Hb. pose proof (log_region_bound (sb_logstart sb) b Hb).
      unfold LOGBLOCKS in *. lia. }
    assert (HiregI : forall b : Z,
              b ∈ ireg_blk_set (FsImg.sb_inodestart sb) icfg_nib ->
              FsImg.sb_inodestart sb <= b < fs_data_start sb).
    { intros b Hb. apply ireg_blk_set_spec in Hb. lia. }
    assert (H1lt : 1 < fs_data_start sb) by lia.
    (* the three peels, each a subset of what is left of [cov] *)
    assert (H1cov : ({[ (1:Z) ]} : gset Z) ⊆ cov).
    { apply elem_of_subseteq. intros b Hb.
      apply elem_of_singleton in Hb as ->. apply Hcovmeta. lia. }
    assert (Hlogcov : log_region_set (sb_logstart sb)
                      ⊆ cov ∖ ({[ (1:Z) ]} : gset Z)).
    { apply elem_of_subseteq. intros b Hb. pose proof (HlogI b Hb).
      apply elem_of_difference. split; [apply Hcovmeta; lia |].
      rewrite elem_of_singleton. lia. }
    (* THE HOME SET, and the two facts the flipped mint's peel needs
       (durable-disk 1c-flip step 1): it is a subset of [cov], and block 1
       -- the superblock -- is in it, so its resource is the EXCLUSIVE byte
       run rather than a cache half. *)
    assert (Hhomesub : fs_home_set cov (sb_logstart sb) ⊆ cov).
    { rewrite /fs_home_set. apply elem_of_subseteq. intros b Hb.
      apply elem_of_difference in Hb as [Hc _]. exact Hc. }
    assert (H1home : ({[ (1:Z) ]} : gset Z)
                     ⊆ fs_home_set cov (sb_logstart sb)).
    { rewrite /fs_home_set. apply elem_of_subseteq. intros b Hb.
      apply elem_of_singleton in Hb as ->. apply elem_of_difference.
      split; [apply Hcovmeta; lia |]. intros Hc. pose proof (HlogI 1 Hc). lia. }
    (* the mint's [cov]-minus-home half IS the log region *)
    assert (Hcancel : cov ∖ fs_home_set cov (sb_logstart sb)
                      = log_region_set (sb_logstart sb)).
    { rewrite /fs_home_set. apply set_eq. intros x. split.
      - intros Hx. apply elem_of_difference in Hx as [Hc Hn].
        destruct (decide (x ∈ log_region_set (sb_logstart sb))) as [Hr | Hr];
          [exact Hr |].
        exfalso. apply Hn. apply elem_of_difference. split; assumption.
      - intros Hx. apply elem_of_difference.
        split; [apply Hcovmeta; pose proof (HlogI x Hx); lia |].
        intros Hd. apply elem_of_difference in Hd as [_ Hn]. exact (Hn Hx). }
    (* ...and peeling block 1 off the home set leaves exactly the set the
       old [cov]-first peel left *)
    assert (Hsetcomm : fs_home_set cov (sb_logstart sb)
                         ∖ ({[ (1:Z) ]} : gset Z)
                       = (cov ∖ ({[ (1:Z) ]} : gset Z))
                           ∖ log_region_set (sb_logstart sb)).
    { rewrite /fs_home_set !difference_difference_l_L. f_equal.
      apply union_comm_L. }
    assert (Hiregcov : ireg_blk_set (FsImg.sb_inodestart sb) icfg_nib
                       ⊆ (cov ∖ ({[ (1:Z) ]} : gset Z))
                           ∖ log_region_set (sb_logstart sb)).
    { apply elem_of_subseteq. intros b Hb. pose proof (HiregI b Hb).
      apply elem_of_difference. split.
      - apply elem_of_difference. split; [apply Hcovmeta; lia |].
        rewrite elem_of_singleton. lia.
      - intros Hc. pose proof (HlogI b Hc). lia. }
    assert (HcovC : forall b : Z, fs_data_start sb <= b < sb_size sb ->
              b ∈ ((cov ∖ ({[ (1:Z) ]} : gset Z))
                     ∖ log_region_set (sb_logstart sb))
                    ∖ ireg_blk_set (FsImg.sb_inodestart sb) icfg_nib).
    { intros b Hb. apply elem_of_difference. split.
      - apply elem_of_difference. split.
        + apply elem_of_difference. split; [apply Hcovdata; exact Hb |].
          rewrite elem_of_singleton. lia.
        + intros Hc. pose proof (HlogI b Hc). lia.
      - intros Hc. pose proof (HiregI b Hc). lia. }
    (* ---- 3. STAGE B: the ledger at the image's link counts ---------- *)
    iDestruct (link_boot_split (region_inums icfg_nib) with "Hlk") as "Hlk".
    iEval (rewrite big_sepS_sep) in "Hlk".
    iDestruct "Hlk" as "[Hla Hoff]".
    iMod (link_boot_mint_w (fs_link_count (fs_blocks dk) sb)
            (region_inums icfg_nib) with "Hla") as "Hla".
    iEval (rewrite big_sepS_sep) in "Hla".
    iDestruct "Hla" as "[Hla Htk]".
    iDestruct (icnt_boot_split (region_inums icfg_nib) with "Hcnt") as "Hcnt".
    iEval (rewrite big_sepS_sep) in "Hcnt".
    iDestruct "Hcnt" as "[HcntR HcntP]".
    iDestruct (frzo_boot_split (region_inums icfg_nib) with "Hfrzo")
      as "Hrcpt".
    iDestruct (frzm_boot_split (region_inums icfg_nib) with "Hfrzm")
      as "Hmir".
    iEval (rewrite big_sepS_sep) in "Hmir".
    iDestruct "Hmir" as "[HmirR HmirP]".
    (* THE CONTENTS GHOST, MINTED AT [∅] AND SET TO THE IMAGE'S TRUTH
       (namei-pinned-lookup.md §9 W3).  [icfg_alloc] cannot mint the values
       -- it knows nothing about the image -- and it does not have to:
       [dv_hold] is the WHOLE element, so each inum's move is a free
       own-update with no ordering constraint against the region, the pool
       or anything else. *)
    (* N-4 PHASE B: the stocking's mover STAYS the plain [dv_set] -- no lend
       can exist here, because the column is stocked NONE at every inum by
       [IcacheBoot.ireg_alloc] below and no licence has been spent yet, so
       the ¾ arm is unreachable and the mask-carrying [dv_set_rt] would buy
       nothing.
       N-5.1 (W5a): the sweep now stops at the WHOLE [dv_hold].  The ride is
       taken AFTER [ireg_alloc], because that is where root's mint licence
       and [ireg_inv] arrive and the mint needs the whole element in hand;
       every other inum takes [dv_ride_of_hold] there, exactly as before. *)
    iDestruct (dv_boot_split (region_inums icfg_nib) with "Hdv") as "Hdv".
    iAssert (|==> [∗ set] z ∈ region_inums icfg_nib,
                    dv_hold z (dv_of (fs_dinode (fs_blocks dk) sb z)
                                 (fs_data_of (fs_blocks dk)
                                    (fs_dinode (fs_blocks dk) sb z))))%I
      with "[Hdv]" as ">Hdv".
    { iApply big_sepS_bupd. iApply (big_sepS_mono with "Hdv").
      intros z _. iIntros "H".
      iApply (dv_set z ∅
                (dv_of (fs_dinode (fs_blocks dk) sb z)
                       (fs_data_of (fs_blocks dk)
                          (fs_dinode (fs_blocks dk) sb z)))
               with "H"). }
    (* ...AND THE PER-FILE CONTENTS GHOST, THE SAME SWEEP (N-5.2A, D-52b).
       Same [∅]-to-image move, same whole ownership, same stop at the WHOLE
       [fv_hold] so that inum 7's lend can be cut after [ireg_alloc]. *)
    iDestruct (fv_boot_split (region_inums icfg_nib) with "Hfv") as "Hfv".
    iAssert (|==> [∗ set] z ∈ region_inums icfg_nib,
                    fv_hold z (fv_of (fs_dinode (fs_blocks dk) sb z)
                                 (fs_data_of (fs_blocks dk)
                                    (fs_dinode (fs_blocks dk) sb z))))%I
      with "[Hfv]" as ">Hfv".
    { iApply big_sepS_bupd. iApply (big_sepS_mono with "Hfv").
      intros z _. iIntros "H".
      iApply (fv_set z []
                (fv_of (fs_dinode (fs_blocks dk) sb z)
                       (fs_data_of (fs_blocks dk)
                          (fs_dinode (fs_blocks dk) sb z)))
               with "H"). }
    iDestruct (region_of_seq (fun z => mono_nat_auth_own (icfg_iep z) 1 0)
                 icfg_nib with "Hep") as "Hep".
    iDestruct (live_boot_split g0 with "Hlive") as "Hlive".
    (* ---- 4. the block layer's ghosts -------------------------------- *)
    (* B3: the two file-system-state ghosts first, so [fs_boot_ghosts] can
       put their names in [γfs] (the block layer allocates neither). *)
    (* durable-disk 2b-inode-4: BOTH maps at the IMAGE's node map now.  The
       TOP map is a plain [ghost_map] and owes no validity; the LINK family
       is allocated in its FULL shape -- every inum's authority at the
       record's own [nlink] with all its tokens still at home -- which owes
       no validity either, because nothing is outstanding.  It is routed
       into [IcacheBoot.ireg_alloc] below and no longer leaves this lemma;
       W9 + conjunct (13) [FsImg.fs_links_eq] come due only when the links
       step hands a directory's tokens to its checked-out payload. *)
    iMod (fs_boot_alloc_full (img_nodes (fs_blocks dk) sb icfg_nib)
            (img_nodes (fs_blocks dk) sb icfg_nib) (img_par (fs_blocks dk) sb))
      as (γlk γtp) "(Htopa & Htopf & Hlnk)".
    iMod (fs_boot_ghosts γv dk ndisk cov (fs_home_set cov (sb_logstart sb))
            ROOTDEV γlk γtp E Hcovin Hhomesub with "Hdisk")
      as (γfs) "(%Hlk & %Htp & Hpool & HaL & HaD & #Hbinv & Hdty & Hfsb & Hchl)".
    (* ---- durable-disk 2b-inode-3: THE TOP MAP IS ROUTED HERE ---------
       Its AUTHORITY becomes [InodeRegion.ftop_inv], the invariant
       [ireg_inv] carries from here on -- that is what makes a checked-out
       holder able to RETAG its [top_frag] at a write, which is the whole
       reason the fragment can ride in the payload.  Its FRAGMENTS become
       the free pool's, one per region inum, tied at a live inum and untied
       on the marker arm.  Neither leaves this lemma. *)
    iEval (rewrite -Htp) in "Htopa".
    iEval (rewrite -Htp) in "Htopf".
    iMod (ftop_alloc E γfs (img_nodes (fs_blocks dk) sb icfg_nib)
            (img_nodes_local (fs_blocks dk) sb cov icfg_nib Hwf Hrw Hbare
               Hfull Hnin Hcovdata)
            with "Htopa Hlkauth") as "#Hftopi".
    iEval (rewrite (big_sepM_img_nodes
                      (fun i n => top_frag (fs_gamma_L γfs) i n)
                      (fs_blocks dk) sb icfg_nib)) in "Htopf".
    (* ---- durable-disk C-3c: THE FREE INUMS' FRAGMENTS GO TO THE REGION ---
       A free inum's [top_frag] now parks WITH its record ([InodeRegion.
       ireg_top_park]), tied at the node the record determines, so that the
       commit's collection can build a whole [FsStateEra.inode_owned_era]
       there (FsCollect's supplier (D)).  Only the LIVE inums' fragments go
       on to the pool, where they ride tied inside [ipool_shape_alloc]. *)
    assert (HAsub : fs_live_set (fs_blocks dk) sb ⊆ region_inums icfg_nib).
    { apply elem_of_subseteq. intros z Hz.
      apply (fs_live_set_elem_of (fs_blocks dk) sb z) in Hz.
      apply region_inums_spec. lia. }
    iDestruct (big_sepS_split_sub _ (region_inums icfg_nib)
                 (fs_live_set (fs_blocks dk) sb) HAsub with "Htopf")
      as "[Htopf Htopreg]".
    iAssert ([∗ set] z ∈ region_inums icfg_nib,
               ireg_top_boot γfs (fun z => fs_dinode (fs_blocks dk) sb z) z)%I
      with "[Htopreg]" as "Htopreg".
    { rewrite {2}(union_difference_L (fs_live_set (fs_blocks dk) sb)
                    (region_inums icfg_nib) HAsub).
      rewrite big_sepS_union; [| set_solver].
      iSplitR "Htopreg".
      { iApply big_sepS_intro. iModIntro. iIntros (z Hz).
        iApply (ireg_top_boot_live γfs
                  (fun z => fs_dinode (fs_blocks dk) sb z) z).
        apply (fs_live_set_elem_of (fs_blocks dk) sb z) in Hz. tauto. }
      iApply (big_sepS_mono with "Htopreg"). intros z Hz.
      apply elem_of_difference in Hz as [Hz1 Hz2].
      pose proof (proj1 (region_inums_spec icfg_nib z) Hz1) as Hzr.
      (* the region's TAIL is free too: below [ninodes] "not live" IS
         "type 0", and at or above it [fs_region_free] says so outright *)
      assert (Hty : bv_unsigned (di_type (fs_dinode (fs_blocks dk) sb z)) = 0).
      { destruct (decide
            (bv_unsigned (di_type (fs_dinode (fs_blocks dk) sb z)) = 0))
          as [H0 | Hnz]; [exact H0 |]. exfalso.
        destruct (Z_lt_ge_dec z (FsImg.sb_ninodes sb)) as [Hlt | Hge].
        - apply Hz2. apply (fs_live_set_elem_of (fs_blocks dk) sb z).
          split; [lia | exact Hnz].
        - apply Hnz.
          exact (fs_region_free_spec (fs_blocks dk) sb icfg_nib z
                   (fs_region_wf_free _ _ _ Hrw)
                   ltac:(lia) ltac:(lia) ltac:(lia)). }
      iIntros "H". rewrite /ireg_top_boot decide_True; [| exact Hty].
      rewrite -(free_node_of_bare (img_node (fs_blocks dk) sb z)
                  (img_node_bare (fs_blocks dk) sb icfg_nib z Hbare
                     (fs_region_wf_nlink _ _ _ Hrw)
                     Hzr Hty)).
      iExact "H". }
    (* ---- durable-disk 2b-inode-4: THE LINK FAMILY IS ROUTED HERE TOO,
       into the inode region, which is where the RA's law has to be
       READABLE ([IgetLic]'s licence (a) turns a directory record's token
       into "the target is allocated" at the TARGET's authority, and the
       presenter does not hold the target).  Nothing about it leaves this
       lemma any more. *)
    iEval (rewrite -Hlk) in "Hlnk".
    iDestruct (ireg_lnks_of_image γfs (fs_blocks dk) sb icfg_nib Hwf
                 with "Hlnk") as "[Hlnks Hetk]".
    (* ---- 5. THE PEELS ------------------------------------------------
       THE MINT ALREADY SPLIT THE LOG REGION OFF (durable-disk 1c-flip):
       [Hchl] is the log's own storage, at the parked cache halves
       [log_state] wants, and [Hfsb] is every HOME block at its exclusive
       byte run.  So the log peel is gone from here and the other two run
       over the home set. *)
    rewrite Hcancel.
    iDestruct (fs_log_region_split γfs dk (sb_logstart sb) with "Hchl")
      as "[Hhdr Hslots]".
    iDestruct (big_sepS_split_sub _ _ ({[ (1:Z) ]} : gset Z) H1home
                 with "Hfsb") as "[Hb1 Hblk]".
    iEval (rewrite Hsetcomm) in "Hblk".
    iDestruct (big_sepS_split_sub _ _
                 (ireg_blk_set (FsImg.sb_inodestart sb) icfg_nib)
                 Hiregcov with "Hblk") as "[Hbireg HfsbC]".
    iEval (rewrite big_sepS_singleton) in "Hb1".
    iDestruct (ireg_blk_of_set (fun b => fsblock (fs_bytes γfs) b (fs_blocks dk b))
                 (FsImg.sb_inodestart sb) icfg_nib with "Hbireg")
      as "Hbireg".
    (* ---- 6. THE INODE REGION ---------------------------------------- *)
    iAssert (ireg_boot) with "[Hboot]" as "Hboot".
    { rewrite /ireg_boot /ity_pending. iExact "Hboot". }
    iMod (ireg_alloc E γfs (FsImg.sb_inodestart sb) icfg_nib
            (fs_home_set cov (sb_logstart sb))
            (fun bi : nat =>
               fs_blocks dk (FsImg.sb_inodestart sb + Z.of_nat bi))
            (fs_link_count (fs_blocks dk) sb)
            (fun z => fn_nlink (img_node (fs_blocks dk) sb z))
            (fun z => fs_dinode (fs_blocks dk) sb z)
            Hnib32 eq_refl
            ltac:(intros bi _; rewrite fs_blocks_length; reflexivity)
            ltac:(intros dss Hdl Hdwf Hde;
                  exact (image_ireg_premises (fs_blocks dk) sb dss icfg_nib
                           Hwf Hrw Hbare Hdl Hdwf Hde Hnib32))
            with "Hla Hlnks HcntR Hrcpt HmirR Hep Htopreg Hbireg Hbinv Hftopi Hboot Hrauth")
      as (γi dss) "(%Hdl & %Hdwf & %Hde & Hireginv & Hboot & Hlics & Hflics &
                    Hout)".
    iDestruct "Hireginv" as "#Hireginv".
    (* ================================================================== *)
    (* ---- durable-disk lane E-unpin: NO LEND IS CUT AT BOOT ---------
       [ireg_alloc] has just stocked the lend column NONE at every inum and
       paid out the per-inum dview and fview MINT LICENCES.  Boot used to
       spend two of them here -- [ROOTINO]'s dview licence and inum 7's
       fview licence -- to carry the era-0 /init pins out of this fupd.
       Those pins are gone (see the post above), so EVERY licence is
       dropped and every inum's ride goes in WHOLE, by [dv_ride_of_hold] /
       [fv_ride_of_hold], exactly as every non-root inum's already did.
       [InodeRegion.dv_lend_mint]/[fv_lend_mint] thereby lose their only
       call sites; they stay in [InodeRegion.v] as lemmas. *)
    iClear "Hlics". iClear "Hflics".
    iAssert ([∗ set] z ∈ region_inums icfg_nib,
               dv_ride z (dv_of (fs_dinode (fs_blocks dk) sb z)
                            (fs_data_of (fs_blocks dk)
                               (fs_dinode (fs_blocks dk) sb z))))%I
      with "[Hdv]" as "Hdv".
    { iApply (big_sepS_mono with "Hdv"). intros z _. iIntros "H".
      iApply (dv_ride_of_hold with "H"). }
    iAssert ([∗ set] z ∈ region_inums icfg_nib,
               fv_ride z (fv_of (fs_dinode (fs_blocks dk) sb z)
                            (fs_data_of (fs_blocks dk)
                               (fs_dinode (fs_blocks dk) sb z))))%I
      with "[Hfv]" as "Hfv".
    { iApply (big_sepS_mono with "Hfv"). intros z _. iIntros "H".
      iApply (fv_ride_of_hold with "H"). }
    (* the payout is at the DECODED record; restate it at [FsImg]'s own *)
    iAssert ([∗ set] z ∈ region_inums icfg_nib,
               ireg_out γi (mword_of_int z : mword 32)
                 (fs_dinode (fs_blocks dk) sb z))%I with "[Hout]" as "Hout".
    { iApply (big_sepS_mono with "Hout"). intros z Hz.
      rewrite (image_dinode_fs_dinode (fs_blocks dk) sb dss icfg_nib z
                 Hdl Hdwf Hde (proj1 (region_inums_spec icfg_nib z) Hz)
                 Hnib32) //. }
    (* ---- 7. the tickets, spent; then the pool ----------------------- *)
    assert (HAran : forall z : Z, z ∈ fs_live_set (fs_blocks dk) sb ->
              0 <= z < FsImg.sb_ninodes sb).
    { intros z Hz. apply (fs_live_set_elem_of (fs_blocks dk) sb z) in Hz.
      tauto. }
    iDestruct (dir_links_of_region (fs_blocks dk) sb
                 (fs_live_set (fs_blocks dk) sb) Hwf Hnin HAran with "Htk")
      as "Hdlk".
    (* ...and the SAME supply at the counting RA (durable-disk 2b-inode-5),
       routed out of the per-inum piles [ireg_lnks_of_image] left over
       after the region kept the authorities and the root's keep-alive. *)
    iDestruct (ent_toks_of_region γfs (fs_blocks dk) sb
                 (fs_live_set (fs_blocks dk) sb) Hwf Hnin HAran with "Hetk")
      as "Hetks".
    iDestruct (big_sepS_sep_2 with "Hdlk Hetks") as "Hdlk".
    iAssert ([∗ set] z ∈ fs_live_set (fs_blocks dk) sb,
               dlinks γfs z (fs_dinode (fs_blocks dk) sb z)
                 (img_blkmap (fs_blocks dk) (fs_dinode (fs_blocks dk) sb z))
                 (fs_data_of (fs_blocks dk) (fs_dinode (fs_blocks dk) sb z)))%I
      with "[Hdlk]" as "Hdlk".
    { iApply (big_sepS_mono with "Hdlk"). intros z _.
      iIntros "[H1 H2]". iApply (dlinks_intro with "H1 H2"). }
    iDestruct (ipool_alloc_of_image γfs γi (fs_blocks dk) sb cov
                 (((cov ∖ ({[ (1:Z) ]} : gset Z))
                     ∖ log_region_set (sb_logstart sb))
                    ∖ ireg_blk_set (FsImg.sb_inodestart sb) icfg_nib)
                 (fs_live_set (fs_blocks dk) sb)
                 Hwf (fs_region_wf_free _ _ _ Hrw)
                 (fs_region_wf_nlink _ _ _ Hrw) Hfull Hnin Hnib32
                 (fs_live_set_elem_of (fs_blocks dk) sb) Hcovdata HcovC
                 with "HcntP HmirP Hoff Hdv Hfv Htopf Hout Hdlk HfsbC")
      as "[Hipool Hrem]".
    (* ---- 7b. DEBT (D): the bitmap block and the free pool ------------ *)
    (* every member of [fs_bitmap_spent] survives all four peels: it is
       either the bitmap block (metadata, above the inode region and below
       the data region) or a free DATA block, and a free block is in no
       inode's block set because W4's used set contains every live inode's
       blocks and W5 says a clear bit is outside it. *)
    assert (HAl : forall z : Z, z ∈ fs_live_set (fs_blocks dk) sb ->
              0 <= z < FsImg.sb_ninodes sb
              /\ bv_unsigned (di_type (fs_dinode (fs_blocks dk) sb z)) <> 0)
      by (intros z Hz;
          exact (proj1 (fs_live_set_elem_of (fs_blocks dk) sb z) Hz)).
    assert (Hbmsub : fs_bitmap_spent (fs_blocks dk) sb
                     ⊆ ((((cov ∖ ({[ (1:Z) ]} : gset Z))
                            ∖ log_region_set (sb_logstart sb))
                           ∖ ireg_blk_set (FsImg.sb_inodestart sb) icfg_nib)
                          ∖ fs_live_blocks (fs_blocks dk) sb
                              (fs_live_set (fs_blocks dk) sb))).
    { apply elem_of_subseteq. intros b Hb.
      destruct (fsimg_wf_used (fs_blocks dk) sb Hwf) as (u & Hus & _ & _).
      assert (Hlive : b ∈ fs_live_blocks (fs_blocks dk) sb
                            (fs_live_set (fs_blocks dk) sb) -> b ∈ u)
        by (apply (fs_live_blocks_used (fs_blocks dk) sb _ u b Hus HAl)).
      destruct (fs_bitmap_spent_bound (fs_blocks dk) sb u b Hwf Hus Hb)
        as [-> | [Hran Hnu]].
      - (* the bitmap block: [inodestart + nib], i.e. just past the inode
           region and just below the data region *)
        assert (Hbmeq : FsImg.sb_bmapstart sb
                        = FsImg.sb_inodestart sb + Z.of_nat icfg_nib)
          by (unfold fs_data_start in Hds; lia).
        assert (Hbm1 : 1 <= FsImg.sb_bmapstart sb)
          by (unfold fs_data_start in H1lt; lia).
        rewrite !elem_of_difference. split_and!.
        + apply Hcovmeta. unfold fs_data_start. lia.
        + rewrite elem_of_singleton. lia.
        + intros Hc. pose proof (HlogI _ Hc). lia.
        + intros Hc. apply ireg_blk_set_spec in Hc. lia.
        + intros Hc.
          destruct (fs_live_blocks_range (fs_blocks dk) sb _ _ Hwf HAl Hc)
            as [Hge _].
          unfold fs_data_start in Hge. lia.
      - (* a free data block *)
        rewrite !elem_of_difference. split_and!.
        + apply Hcovdata. lia.
        + rewrite elem_of_singleton. lia.
        + intros Hc. pose proof (HlogI _ Hc). lia.
        + intros Hc. pose proof (HiregI _ Hc). lia.
        + intros Hc. exact (Hnu (Hlive Hc)). }
    iDestruct (big_sepS_split_sub
                 (fun b => fsblock (fs_bytes γfs) b (fs_blocks dk b))%I
                 _ (fs_bitmap_spent (fs_blocks dk) sb) Hbmsub with "Hrem")
      as "[Hbmspent Hrem]".
    iDestruct (bitmap_res_of_image γfs (fs_blocks dk) sb Hwf Hfull
                 with "Hbmspent") as "Hbmres".
    iMod (bitmap_inv_alloc E with "Hbinv Hbmres") as "#Hbmres".
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
               cov (sb_logstart sb) (FsImg.sb_bmapstart sb)
               (sb_size sb) (FsImg.sb_ninodes sb)).
    rewrite /fs_kit_icache /fs_kit_fsinit_ghost.
    cbn [fsc_printk fsc_kalloc fsc_kpages fsc_uart fsc_disk fsc_dlock
         fsc_bio fsc_fs fsc_ireg fsc_ic fsc_itlock fsc_cov fsc_logst
         fsc_bmapstart fsc_size fsc_ninodes].
    rewrite Hdev Histq Hlogq.
    (* the coverage remainder's set, as the kit spells it *)
    assert (Hset : (((((cov ∖ ({[ (1:Z) ]} : gset Z))
                         ∖ log_region_set (sb_logstart sb))
                        ∖ ireg_blk_set (FsImg.sb_inodestart sb) icfg_nib)
                       ∖ fs_live_blocks (fs_blocks dk) sb
                           (fs_live_set (fs_blocks dk) sb))
                      ∖ fs_bitmap_spent (fs_blocks dk) sb)
                   = cov ∖ fs_kit_spent (fs_blocks dk) sb icfg_nib
                             (fs_live_set (fs_blocks dk) sb)).
    { apply set_eq. intros b. rewrite /fs_kit_spent.
      (* THE COUNTS ARE SPELLED OUT.  A [!] runs one FULL failing pass per
         lemma, and here that pass is a whole-goal setoid traversal dragging
         the [elem_of] instance chain over five computed carriers
         ([log_region_set], [ireg_blk_set], [fs_live_blocks],
         [fs_bitmap_spent]) -- 6.1 s for a goal with exactly six differences
         (five on the left, one on the right) and four unions.  See
         claude-notes/optimization.md, "a [!] in [rewrite] always pays one
         FULL failing pass". *)
      rewrite 6!elem_of_difference 4!elem_of_union. tauto. }
    rewrite Hset.
    (* ---- B3: NEITHER era ghost is in the post any more (durable-disk
       2b-inode-3 / 2b-inode-4): the top map is routed into [ftop_inv] and
       the free pool, the link family into the inode region. ---- *)
    (* ---- the ten ties ---- *)
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
    (* ---- kit 1 ---- *)
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
    (* ---- kit 2 ---- *)
    iSplitL "Hlogtok"; [iExact "Hlogtok" |].
    iSplitL "Hboot"; [iExact "Hboot" |].
    (* [ireg_inv] is persistent and was moved to the intuitionistic context
       at the boot mint (W5a), so this row is an [iSplitR] now. *)
    iSplitR; [iExact "Hireginv" |].
    iSplitL "Hb1"; [iExact "Hb1" |].
    iSplitL "HaL HaD".
    { iExists (fs_C0 dk cov), (fs_D0 dk cov).
      iSplitR; [iPureIntro; exact (fs_C0_lookup dk cov) |].
      iSplitL "HaL"; [iExact "HaL" | iExact "HaD"]. }
    iSplitL "Hdty"; [iExact "Hdty" |].
    iSplitL "Hhdr"; [iExact "Hhdr" |].
    iSplitL "Hslots"; [iExact "Hslots" |].
    iSplitL "Hbmres"; [iExact "Hbmres" | iExact "Hrem"].
  Qed.

End FsCfgBootEra.

(* ---------------------------------------------------------------------- *)
(* WHAT THE ERA'S DISK MUST BE, for the file system's boot-era mint to run. *)
(*                                                                        *)
(* [FsCfgBoot.fs_cfg_alloc]'s nine pure premises, bundled: two image        *)
(* sweeps ([FsImg.fsimg_wf] = W1-W9, and [FsImg.fs_region_wf] = the whole   *)
(* [16*nib] inode region's L3/L4 and free tail), four geometry facts about  *)
(* [nib], and ruling R4's three coverage corners.  Bundled because both     *)
(* adequacy theorems now carry it and a nine-premise theorem statement is   *)
(* not readable; the projections are in [fs_cfg_alloc]'s own order.         *)
(*                                                                        *)
(* IT COMPUTES NOTHING (ruling R3): the era fupd takes every image fact as  *)
(* a hypothesis, and the literal-image discharge lives in                   *)
(* [FsAdequacyImg.v] off [FsImgCheck]'s citations -- deliberately NOT on    *)
(* this file's cone, nor on [SystemAdequacy]'s.                             *)
(* ---------------------------------------------------------------------- *)
Definition fs_boot_image_wf (dk : Z -> bv 8) (ndisk : nat)
    (sb : fs_sb) (nib : nat) (cov : gset Z) : Prop :=
  FsImg.fsimg_wf (FsCrash.fs_blocks dk) sb = true
  /\ FsImg.fs_region_wf (FsCrash.fs_blocks dk) sb nib = true
  /\ FsImg.sb_ninodes sb <= 16 * Z.of_nat nib
  /\ 16 * Z.of_nat nib <= 2 ^ 32
  /\ (0 < nib)%nat
  (* the inode region is EXACTLY [[inodestart, bmapstart)]: mkfs rounds
     [ninodes] up to a whole block *)
  /\ Z.of_nat nib = FsImg.sb_ninodes sb / 16 + 1
  /\ FsBoot.fs_cov_in cov ndisk
  /\ (forall b : Z, 1 <= b < FsImg.fs_data_start sb -> b ∈ cov)
  /\ (forall b : Z, FsImg.fs_data_start sb <= b < FsImg.sb_size sb -> b ∈ cov)
  (* ---- THE THREE STAGE-(f) CONJUNCTS (fs-cfg-boot.md (f-1)) ----
     (10) BLOCK 1'S BYTES ARE THE RECORD.  [FsImg.fsimg_wf] is arithmetic on
     [sb] ALONE -- W1 never looks at block 1 -- so nothing in the tree said
     the superblock on the disk IS the superblock the configuration was
     minted from.  [FsImg.fs_parse_sb] is exactly that reading, it is what
     [SpecFsinit]'s premise (a) needs, and [FsImgCheck.fsimg_parse_sb]
     ALREADY proves it at the literal image -- so this costs the adequacy
     cone no new computation.
     (11) the [ushort] bound [FsReady.fs_geom_ok]'s [fgo_ushort] wants,
     tighter than the [2^32] the era threads (208 <= 65536 at the image).
     (12) the disk image is no larger than [size] blocks, which is what
     turns [FsBoot.fs_cov_in] into [IcacheInv.cov_below] (and, with W1's
     [size <= 8*BSIZE], into [LogInv.cov_ok]).  1024*2000 = 2048000. *)
  /\ FsImg.fs_parse_sb (FsCrash.fs_blocks dk) = Some sb
  /\ 16 * Z.of_nat nib <= 2 ^ 16
  /\ Z.of_nat ndisk <= 1024 * FsImg.sb_size sb
  (* ---- (13) THE FILE-NLINK EQUALITY SWEEP (durable-disk stage G1) ----
     [FsImg.fs_links_eq]: every live FILE inode's [nlink] EQUALS the number
     of directory entries naming it.  [fsimg_wf]'s W3 only bounds it from
     below, and the boot establishment of stage G1's abstract-view row (a)
     needs the equality: [FsWfImg.fsimg_durable_wf] concludes
     [FsWf.fs_durable_wf_body] of the image's committed view from
     [fsimg_wf + fs_links_eq + fs_region_wf + parse], and that view is the
     row's [A] at era 0.  Cited at the literal image by
     [FsImgCheck.fsimg_links_eq], exactly as (10) cites [fsimg_parse_sb], so
     this costs the adequacy cone no new computation. *)
  /\ FsImg.fs_links_eq (FsCrash.fs_blocks dk) sb = true
  (* ---- (14)/(15) THE TWO DURABLE-SIDE SWEEPS (durable-disk lane C) ----
     Both are consumed by [FsDurImg], whose header (2)/(3) says why each is
     needed and neither derivable: (14) [FsImg.fs_region_bare] -- every
     type-0 record of the region has zero size and thirteen zero addresses,
     which is what makes [FsStateInode.inode_local] true of a FREE record
     and what makes a free inum's node own NO block; (15)
     [FsImg.fs_root_no_self] -- no live record of the root names the root
     under a name other than ["."] or [".."], which reconciles the image's
     ticket discipline with the link RA's and so proves
     [FsDurImg.img_link_valid].  They ride in this bundle rather than as
     two extra premises on every consumer because the bundle is what both
     adequacy theorems already carry; cited at the literal image by
     [FsImgCheck.fsimg_region_bare] / [fsimg_root_no_self], exactly as
     (1)/(2)/(10)/(13) are, so the adequacy cone gains no computation.
     THEY GO LAST, so that no existing destructuring pattern moves
     (durable-notes.md, "when a new conjunct goes into a predicate forty
     proofs destructure, put it LAST"). *)
  /\ FsImg.fs_region_bare (FsCrash.fs_blocks dk) sb nib = true
  /\ FsImg.fs_root_no_self (FsCrash.fs_blocks dk) sb = true.

(* ====================================================================== *)
(*  THE FILE SYSTEM'S BOOT-ERA OUTPUT, AS ONE ROW.                         *)
(*                                                                        *)
(*  BYTE-IDENTICAL TO [fs_cfg_alloc]'s conclusion body (ten ties, then the *)
(*  two kits, in that order), which is what makes                          *)
(*  [BootShared.boot_shared_alloc]'s wiring one [iExact] -- and what makes *)
(*  stage (e)'s reading of it the same destructuring the era fupd's own    *)
(*  post has.  [ICFG]/[FSC] are parameters rather than resolved from an    *)
(*  ambient class: the caller passes [fileG]'s own two projections, so     *)
(*  every row is stated AT THE INSTANCE the boot chain is applied at.      *)
(*                                                                        *)
(*  IT LIVES HERE, not in [BootShared.v], because stage (e) threads it     *)
(*  through [SpecMain] -> [BootChain] into [ProofMain.mn_grp_fs], and      *)
(*  both of those files sit BELOW [BootShared].  [BootShared] imports this *)
(*  file already.                                                          *)
(* ====================================================================== *)
Definition fs_boot_supply `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}
    (ICFG : icfg) (FSC : fscfg) (dk : Z -> bv 8)
    (sb : fs_sb) (nib : nat) (cov : gset Z)
    (γd : uart_names) (γv : disk_names) : iProp Σ :=
  (⌜icfg_dev = InodeInv.ROOTDEV⌝ ∗ ⌜icfg_nib = nib⌝ ∗
   ⌜icfg_ist = FsImg.sb_inodestart sb⌝ ∗
   ⌜fsc_uart = γd⌝ ∗ ⌜fsc_disk = γv⌝ ∗ ⌜fsc_cov = cov⌝ ∗
   ⌜fsc_logst = FsImg.sb_logstart sb⌝ ∗
   ⌜fsc_bmapstart = FsImg.sb_bmapstart sb⌝ ∗
   ⌜fsc_size = FsImg.sb_size sb⌝ ∗ ⌜fsc_ninodes = FsImg.sb_ninodes sb⌝ ∗
   fs_kit_icache ICFG FSC ∗
   fs_kit_fsinit_ghost ICFG FSC (FsCrash.fs_blocks dk)
     (fs_kit_spent (FsCrash.fs_blocks dk) sb nib
        (FsImg.fs_live_set (FsCrash.fs_blocks dk) sb)))%I.
