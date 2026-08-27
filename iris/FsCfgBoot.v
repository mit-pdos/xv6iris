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
Require Import DiskPtsto.      (* [disk_names]  *)
Require Import FsBlocks.
Require Import DinodeEnc.
Require Import DirView.
Require Import FsTree.        (* [dir_wins] / [dir_entry] -- the view is an [omap] *)
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
(* THE BOOT KITS moved to [FsCfgKits.v] -- their STATEMENT is vocabulary every
   consumption site names, while the era fupd BELOW is the one-site proof that
   boot can produce them ([LogDefs] vs [LogInv], same split, same reason).
   EXPORTED, so every existing spelling of a kit name still resolves here. *)
Require Export FsCfgKits.
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

  Lemma big_sepL_to_set (Φ : Z -> iProp Σ) (l : list Z) :
    base.NoDup l -> ([∗ list] x ∈ l, Φ x) ⊢ [∗ set] x ∈ list_to_set l, Φ x.
  Proof. intros Hnd. rewrite -(big_sepS_list_to_set Φ l Hnd) //. Qed.

  (* [omap]'s big-op, back at the SOURCE list's indices.  Stated with the
     TARGET predicate abstract and two pointwise premises rather than with a
     [match] in the conclusion: at a [Some] slot the caller turns the ticket
     into the record's payload, at a [None] slot it owes an emp-valid
     payload. *)
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

Section FsCfgBootBitmap.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}.

End FsCfgBootBitmap.


(* ====================================================================== *)
(*  THE TWO BOOT KITS (ruling R6), GHOST ROWS ONLY                         *)
(* ====================================================================== *)

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

  (* ---- THE ERA MINT IS THE SNAPSHOT'S (durable-disk lanes E-mint /
     E-himg / H5) ------
     [FsCfgSnap.fs_cfg_alloc_snap] mints the era's file-system instance from
     the DURABLE SNAPSHOT and needs no image at any era; era 0 is not a
     reading either -- [BootShared.boot_shared_alloc] calls the snapshot
     mint at EVERY era, and what the IMAGE still does is produce the FIRST
     snapshot, once, at the top-level theorem
     ([FsDurImg.img_snap_ok] through [img_P_dur_alloc]).

     THE IMAGE ROUTING THIS FILE USED TO CARRY IS SWEPT (lane H5): the
     twenty-six lemmas whose only reader was the deleted era-0 corollary --
     [ipool_alloc_of_image], [ireg_lnks_of_image], [bitmap_res_of_image],
     [image_ireg_premises], [ent_toks_of_image]/[_region]/[_tickets],
     [fs_kit_spent], [fs_live_blocks_*], [fs_boot_inodes_*], the
     [big_sepL_omap_*] family and their neighbours -- are gone, computed as
     a fixpoint over "no reference outside its own body".  Their snapshot
     twins are [FsCfgSnap]'s [ipool_alloc_of_snap], [snap_link_route],
     [bitmap_res_of_snap], [snap_ireg_premises], [snap_inode_ok] and
     [snap_spent].  What stays, because [FsDurImg] and [FsCollectImg] read
     it, is [img_node]/[img_nodes] and the [img_inode_*] readings. *)

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
(* [SystemAdequacy.v] off [FsImgCheck]'s citations -- deliberately NOT on   *)
(* this file's cone.                                                        *)
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
     needs the equality: the image discharge concluded the durable
     invariant of the image's committed view from
     [fsimg_wf + fs_links_eq + fs_region_wf + parse], and that view is the
     row's [A] at era 0.  (Both the invariant and that discharge are gone
     with the pure wf layer, ruling 3; the equality is still what row (a)
     needs.)  Cited at the literal image by
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

(* ---------------------------------------------------------------------- *)
(* WHAT THE ERA'S DISK MUST BE AT EVERY LATER BOOT (durable-disk lane      *)
(* E-himg), and it is not an image hypothesis at all.                      *)
(*                                                                        *)
(* [fs_boot_image_wf] above is a claim about mkfs's bytes, and asserting   *)
(* it at EVERY era is refutable -- nothing proves that xv6's own writes    *)
(* leave the disk mkfs-shaped.  What a boot actually needs is the DURABLE  *)
(* SNAPSHOT, which [FsCrash.P_fs] carries across every power cycle and     *)
(* [SystemAdequacy.fs_boot_pure] delivers into each boot: the committed    *)
(* view IS a file system, and the era's configuration is that state's OWN  *)
(* superblock.                                                            *)
(*                                                                        *)
(* THE ROWS.  (1)/(2) the era's configuration is the snapshot's -- [sb]    *)
(* and [nib] are not free parameters any more, they are read off [S].      *)
(* (3)/(4) the snapshot itself, at the committed view as a BLOCK VIEW      *)
(* ([Pb]) rather than as a map: that is what the mint takes.  (5)/(6)/(7)  *)
(* the on-disk header, and exactly where [Pb] differs from the raw disk -- *)
(* on the header's write set, where it holds the LOGGED value; off it, the *)
(* two agree.  That difference is [FsBlocks]' exception set, which         *)
(* [initlog] empties and seals.  (8)/(9) the covered range, which is FIXED *)
(* across power cycles and therefore CANNOT come from the snapshot: both   *)
(* are era-independent facts about [cov] and about a [logstart] that       *)
(* [FsImg.sbo_logstart] pins at 2, discharged once at the initial machine. *)
(* ---------------------------------------------------------------------- *)
Definition fs_boot_snap_wf (dk : Z -> bv 8) (ndisk : nat)
    (S : FsState.fs_state_rec) (Pb : Z -> list (bv 8))
    (sb : fs_sb) (nib : nat) (cov : gset Z) : Prop :=
  sb = FsState.fss_sb S
  /\ Z.of_nat nib = FsImg.sb_ninodes sb / 16 + 1
  /\ FsDurSnap.snap_ok S
       (fs_restrict Pb (fs_home_set cov (FsImg.sb_logstart sb)))
  /\ (forall b : Z, length (Pb b) = BSIZE)
  /\ FsCrash.hdr_wf (FsCrash.fs_blocks dk) cov (FsImg.sb_logstart sb)
  /\ (forall b : Z,
        b ∈ fs_home_set cov (FsImg.sb_logstart sb) ->
        b ∉ FsCrash.hdr_wset (FsCrash.fs_blocks dk) (FsImg.sb_logstart sb) ->
        Pb b = FsCrash.fs_blocks dk b)
  /\ (forall (i : nat) (b : Z),
        (hdr_dec (FsCrash.fs_blocks dk
                    (log_hdr_bno (FsImg.sb_logstart sb)))).2 !! i = Some b ->
        Pb b = FsCrash.fs_blocks dk (log_slot_bno (FsImg.sb_logstart sb) i))
  /\ FsBoot.fs_cov_in cov ndisk
  /\ log_region_set (FsImg.sb_logstart sb) ⊆ cov.

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
(*  THE SPENT SET, THE BYTE VIEW'S VALUE AND THE EXCEPTION SET ARE
    PARAMETERS since durable-disk lane E-himg.  They used to be SPELLED at
    the image's own carve, at the raw disk and at [∅] -- true only of a boot
    whose on-disk log header is clean.  The era's mint chooses the first two
    ([FsCfgSnap.snap_spent] and the committed view [FsCrash.fs_rec_view])
    and the third is the header's own write set; nothing between here and
    [FirstTok.first_fsinit] reads any of them, so all three travel
    existentially. *)
Definition fs_boot_supply `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ}
    (ICFG : icfg) (FSC : fscfg) (dk : Z -> bv 8)
    (sb : fs_sb) (nib : nat) (cov : gset Z)
    (γd : uart_names) (γv : disk_names)
    (Rspent : gset Z) (Pb : Z -> list (bv 8)) (Xexc : gset Z) : iProp Σ :=
  (⌜icfg_dev = InodeInv.ROOTDEV⌝ ∗ ⌜icfg_nib = nib⌝ ∗
   ⌜icfg_ist = FsImg.sb_inodestart sb⌝ ∗
   ⌜fsc_uart = γd⌝ ∗ ⌜fsc_disk = γv⌝ ∗ ⌜fsc_cov = cov⌝ ∗
   ⌜fsc_logst = FsImg.sb_logstart sb⌝ ∗
   ⌜fsc_bmapstart = FsImg.sb_bmapstart sb⌝ ∗
   ⌜fsc_size = FsImg.sb_size sb⌝ ∗ ⌜fsc_ninodes = FsImg.sb_ninodes sb⌝ ∗
   fs_kit_icache ICFG FSC ∗
   fs_kit_fsinit_ghost ICFG FSC (FsCrash.fs_blocks dk) Rspent Pb Xexc)%I.
