(* ====================================================================== *)
(* FsDurImg.v -- THE DURABLE FILE SYSTEM, BUILT FROM AN IMAGE              *)
(*                                                                        *)
(* durable-disk 2c-img, leaf 2.  Design of record:                        *)
(* claude-notes/design/fs-state.md sections 1-4;                          *)
(* claude-notes/projects/durable-disk.md item 2c, finding (iv).           *)
(*                                                                        *)
(* [FsCrash.P_fs_alloc] fills the durable byte map [riscv_dview_name] with *)
(* [LogDefs.fs_dbytes D0] -- the flat byte elements of the boot era's      *)
(* committed BLOCK view, which at a clean image is                        *)
(* [fs_restrict (fs_blocks dk) (fs_home_set cov logstart)].  Stage 2c's    *)
(* [P_wf] is not that blob but [FsState.fs_view Gamma_D].  THIS FILE IS    *)
(* THE ONE CONVERSION, and it is where the image is decoded.               *)
(*                                                                        *)
(* IT COMPUTES NOTHING AND NAMES NO LITERAL IMAGE (ruling R3, as           *)
(* [FsCfgBoot] follows it): every image fact arrives as a HYPOTHESIS, in   *)
(* [FsCfgBoot.fs_boot_image_wf]'s own vocabulary, and both adequacy        *)
(* theorems already carry that bundle.  The literal-image discharge stays  *)
(* in [FsImgCheck.v]/[FsAdequacyImg.v] and does not move.                  *)
(*                                                                        *)
(* THREE THINGS A READER SHOULD KNOW BEFORE ANYTHING ELSE.                 *)
(*                                                                        *)
(* (1) [Gamma_D] IS [FsBytesGamma.fs_gamma_L] AT A DURABLE NAME BUNDLE.    *)
(*     [fs_gamma_L] reads exactly three fields of [FsBlocks.fs_names] --   *)
(*     [fs_bytes], [fs_link], [fs_top] -- so filling those three with the  *)
(*     DURABLE gnames makes [Gamma_D] an instance of the same constructor  *)
(*     ([fs_gamma_dur] below is [reflexivity]), and every lemma the tree   *)
(*     states at [fs_gamma_L] -- [FsStateEra.inode_blocks_era],            *)
(*     [FsStateEra.ind_res_era], [FsImgBridge.img_inode_blocks_res] --     *)
(*     applies verbatim at the durable view.  None of those three opens an *)
(*     invariant or reads the logged view; each is pure resource           *)
(*     shuffling over [FsBytesGamma.gamma_blk_owned].                      *)
(*     THE PROPER FIX is to make those three Gamma-GENERIC (they use only  *)
(*     [gamma_blk_owned]), which this additive lane could not do; the      *)
(*     bundle below is the standing workaround and should go when they     *)
(*     move.  The two cache-side fields are never read and are filled with *)
(*     the byte gname rather than fresh ones, so nothing is allocated.     *)
(*                                                                        *)
(* (2) THE FREE RECORDS NEED THEIR OWN SWEEP, and the 2026-08-24 survey    *)
(*     did not price it.  [FsState.fs_inodes] iterates [inode_owned] over  *)
(*     the WHOLE inode map, and [inode_owned] carries                      *)
(*     [FsStateInode.inode_local].  At a LIVE inum that is                 *)
(*     [FsStateEra.inode_local_of_ok_rec] off W3/W6/W8 as [FsCfgBoot]      *)
(*     already does it; at a FREE one (type 0) NOTHING in [fsimg_wf] or    *)
(*     [fs_region_wf] constrains the record's [size] or [addrs], so        *)
(*     [inl_size] and [inl_covers] are not derivable.  Both would be false *)
(*     of a garbage type-0 record.  [fs_region_bare] below is the missing  *)
(*     sweep, in [FsImg.fs_region_free]'s own idiom and reading the same   *)
(*     thirteen inode blocks; it is a PREMISE here and its literal-image   *)
(*     discharge is one [vm_compute] row in [FsImgCheck.v] (owed).         *)
(*                                                                        *)
(* (3) THE LINK FAMILY'S VALIDITY IS A PREMISE, and that is the lane's     *)
(*     main finding.  [FsState.fs_boot_alloc_at] needs                     *)
(*     [✓ FsState.link_elem I]; [FsState.v]'s header says a map read off   *)
(*     the image discharges it from W9 ([FsImg.fs_links_wf]) plus conjunct *)
(*     (13) ([FsImg.fs_links_eq]).  Those are the right raw material and   *)
(*     they do NOT close it as they stand.  Section 10 takes the           *)
(*     reduction as far as they do go -- W9 forces the image to have       *)
(*     EXACTLY ONE directory (the root), so the whole family is one        *)
(*     authority per inum, composed with the root's outgoing tokens, and   *)
(*     [img_link_valid] leaves ONE inclusion in [fsLinkUR], the survey's   *)
(*     (iv)(c) ticket bridge -- and its header names the two places the    *)
(*     image's ticket discipline and [FsStateInode.ent_tokenless]          *)
(*     disagree.  Until that lands, [✓ link_elem …] is a premise here.     *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac excl.
From iris.base_logic.lib Require Import iprop own ghost_map.
Require Import SailStdpp.Operators_mwords.
Require Import RiscvPtsto.
(* EARLY, before the block layer: [FsState] exports four names that collide
   with live ones ([fs_view], [link_auth], [byte_range], [blk_owned]) and
   the LAST import wins -- durable-notes.md. *)
Require Import FsState.
Require Import BioDefs.
Require Import BitmapEnc.
Require Import DinodeEnc.
Require Import DirView.
Require Import FsTree.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IcacheEscrow.    (* [region_inums] *)
Require Import IcacheBoot.      (* [diblk_bytes_surj] *)
Require Import FsBlocks.
Require Import FsBoot.          (* [big_sepS_carve] / [big_sepS_split_sub] *)
Require Import FsCrash.
Require Import LogDefs.
Require Import FsImg.
Require Import FsImgBridge.
Require Import FsStateBitmap.
Require Import FsStateEra.
Require Import FsBytesGamma.
Require Import FsCfgBoot.       (* [img_nodes] / [fs_boot_image_wf] *)
Require Import Xv6G.
(* LAST: it re-exports [FsStateDefs], whose [byte_range]/[blk_owned] must
   win over the block layer's twins. *)
Require Import FsDurBytes.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1.  THE MISSING IMAGE SWEEP: A FREE RECORD IS BARE                    *)
(* ===================================================================== *)

(* one type-0 record's shape: zero size and thirteen zero addresses.  With
   [FsImg.fs_region_nlink]'s L3 ([nlink = 0] at a type-0 record) beside it
   this is exactly [FsStateInode.fn_bare] of the node the image decodes. *)
Definition fs_rec_bare (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) : bool :=
  let dn := fs_dinode P sb z in
  (bv_unsigned (di_size dn) =? 0)
  && List.forallb (fun a : bv 32 => bv_unsigned a =? 0) (di_addrs dn).

(* ...over the whole region, in [FsImg.fs_region_free]'s idiom *)
Definition fs_region_bare (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
  : bool :=
  List.forallb
    (fun i => let z := Z.of_nat i in
              if bv_unsigned (di_type (fs_dinode P sb z)) =? 0
              then fs_rec_bare P sb z else true)
    (seq 0 (16 * nib)%nat).

Lemma fs_region_bare_size (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (z : Z) :
  fs_region_bare P sb nib = true -> 0 <= z < 16 * Z.of_nat nib ->
  bv_unsigned (di_type (fs_dinode P sb z)) = 0 ->
  bv_unsigned (di_size (fs_dinode P sb z)) = 0.
Proof.
  intros H Hz Hty.
  assert (Hzid : Z.of_nat (Z.to_nat z) = z) by lia.
  pose proof (forallb_seq _ (16 * nib)%nat (Z.to_nat z) H ltac:(lia)) as Hk.
  cbv beta zeta in Hk. rewrite Hzid in Hk.
  rewrite (proj2 (Z.eqb_eq _ _) Hty) in Hk.
  rewrite /fs_rec_bare in Hk. cbv zeta in Hk.
  apply andb_true_iff in Hk as [Hs _]. apply Z.eqb_eq. exact Hs.
Qed.

Lemma fs_region_bare_addr (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (z : Z) (k : nat) :
  fs_region_bare P sb nib = true -> 0 <= z < 16 * Z.of_nat nib ->
  bv_unsigned (di_type (fs_dinode P sb z)) = 0 -> (k < 13)%nat ->
  bv_unsigned (di_addrs (fs_dinode P sb z) !!! k) = 0.
Proof.
  intros H Hz Hty Hk.
  assert (Hzid : Z.of_nat (Z.to_nat z) = z) by lia.
  pose proof (forallb_seq _ (16 * nib)%nat (Z.to_nat z) H ltac:(lia)) as Hq.
  cbv beta zeta in Hq. rewrite Hzid in Hq.
  rewrite (proj2 (Z.eqb_eq _ _) Hty) in Hq.
  rewrite /fs_rec_bare in Hq. cbv zeta in Hq.
  apply andb_true_iff in Hq as [_ Ha].
  rewrite List.forallb_forall in Ha.
  assert (Hlen : length (di_addrs (fs_dinode P sb z)) = 13%nat)
    by exact (fs_dinode_wf P sb z).
  destruct (lookup_lt_is_Some_2 (di_addrs (fs_dinode P sb z)) k
              ltac:(lia)) as [a Ha'].
  rewrite (list_lookup_total_correct _ _ _ Ha').
  apply Z.eqb_eq. apply Ha.
  apply elem_of_list_In, elem_of_list_lookup_2 with k. exact Ha'.
Qed.

(* ===================================================================== *)
(*  2.  THE IMAGE'S NODE, READ                                            *)
(* ===================================================================== *)

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

(* ===================================================================== *)
(*  3.  THE DURABLE VIEW, AS AN INSTANCE OF THE ERA'S CONSTRUCTOR         *)
(* ===================================================================== *)

Section DurImg.
  Context `{!riscvGS Σ, !xv6G Σ}.

  (* THE DURABLE NAME BUNDLE -- header (1).  [fs_gamma_L] reads exactly
     [fs_bytes], [fs_link] and [fs_top]; the two cache-side fields are
     never read, so they are filled with the byte gname rather than with
     fresh ones and nothing is allocated. *)
  Definition fs_dur_bundle (g : gname) (Gd : fs_dur_names) : fs_names :=
    MkFsNames g g g (fdn_link Gd) (fdn_top Gd).

  Lemma fs_gamma_dur (g : gname) (Gd : fs_dur_names) :
    fs_gamma_L (fs_dur_bundle g Gd) = fs_gamma_D g Gd.
  Proof. reflexivity. Qed.

  (* ...so the block layer's own block ownership IS the durable view's *)
  Lemma dur_blk_owned (g : gname) (Gd : fs_dur_names) (b : Z)
      (bs : list (bv 8)) :
    blk_owned (fs_gamma_D g Gd) b bs ⊣⊢ fsblock g b bs.
  Proof.
    rewrite -(fs_gamma_dur g Gd).
    exact (gamma_blk_owned (fs_dur_bundle g Gd) b bs).
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  4.  ONE LIVE INODE'S FOOTPRINT                                     *)
  (*                                                                      *)
  (*  [FsImgBridge.img_inode_blocks_res] turns one inode's block SET into *)
  (*  [InodeInv]'s slot-keyed pair; [FsStateEra.inode_blocks_era] /       *)
  (*  [ind_res_era] read that pair as the era vocabulary's own.  Both are *)
  (*  stated at [fs_gamma_L], and the bundle above is what makes them     *)
  (*  apply at [Gamma_D].                                                 *)
  (* ------------------------------------------------------------------ *)

  Lemma img_inode_phi_res (g : gname) (Gd : fs_dur_names)
      (P : Z -> list (bv 8)) (sb : fs_sb) (cov : gset Z) (nib : nat) (z : Z) :
    fsimg_wf P sb = true -> fs_region_nlink P sb nib = true ->
    fs_blocks_full P ->
    FsImg.sb_ninodes sb <= 16 * Z.of_nat nib ->
    (forall b : Z, fs_data_start sb <= b < sb_size sb -> b ∈ cov) ->
    0 <= z < FsImg.sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
    ([∗ set] b ∈ fs_inode_blocks_set P sb z,
       blk_owned (fs_gamma_D g Gd) b (P b)) -∗
    ([∗ map] k ↦ bs ∈ fn_blk (img_node P sb z),
       blk_owned (fs_gamma_D g Gd) (fn_naddr (img_node P sb z) k) bs)
      ∗ ind_owned (fs_gamma_D g Gd) (img_node P sb z).
  Proof.
    intros Hwf Hrnl Hfull Hnin Hcov Hran Hty.
    pose proof (fsimg_wf_inode P sb z Hwf Hran Hty) as Hok.
    pose proof (fsimg_wf_slot_inj P sb z Hwf Hran Hty) as Hinj.
    pose proof (img_inode_local_live P sb cov nib z Hwf Hrnl Hfull Hnin Hcov
                  Hran Hty) as Hl.
    pose proof (node_shape_ok_of_inode_ok cov (sb_logstart sb)
                  (fs_dinode P sb z) (img_blkmap P (fs_dinode P sb z))
                  (fs_data_of P (fs_dinode P sb z))
                  (img_inode_ok_at P sb cov z Hwf Hfull Hcov Hran Hty))
      as Hshape.
    assert (Hbm : bm_of (img_node P sb z) = img_blkmap P (fs_dinode P sb z))
      by exact (bm_of_era_node _ _ _ Hshape).
    iIntros "H".
    (* to the block layer's own spelling of a block *)
    iAssert ([∗ set] b ∈ fs_inode_blocks_set P sb z,
               fsblock (fs_bytes (fs_dur_bundle g Gd)) b (P b))%I
      with "[H]" as "H".
    { iApply (big_sepS_mono with "H"). intros b _. rewrite dur_blk_owned //. }
    rewrite /fs_inode_blocks_set.
    iDestruct (img_inode_blocks_res (fs_dur_bundle g Gd) P sb
                 (fs_dinode P sb z) (fs_dinode_wf P sb z) Hfull Hok Hinj
                 with "H") as "[Hb Hi]".
    rewrite -(fs_gamma_dur g Gd).
    rewrite -(inode_blocks_era (fs_dur_bundle g Gd) z (img_node P sb z) Hl).
    rewrite -(ind_res_era (fs_dur_bundle g Gd) (img_node P sb z)).
    iSplitL "Hb"; [| rewrite Hbm; iExact "Hi"].
    rewrite Hbm.
    rewrite (inode_blocks_data_ext (fs_dur_bundle g Gd)
               (img_blkmap P (fs_dinode P sb z))
               (fs_data_of P (fs_dinode P sb z))
               (fn_data (img_node P sb z))); [iExact "Hb" |].
    intros k Hk. symmetry. exact (fn_data_era_node _ _ _ k Hshape Hk).
  Qed.

End DurImg.

(* ===================================================================== *)
(*  5.  THE INODE REGION'S RECORDS                                        *)
(*                                                                        *)
(*  [FsStateInode.rec_owned_at_diblk] is the sixteen-fold split of ONE    *)
(*  inode block at the region's own numbering; this is that at the        *)
(*  image's decoded records, and then over the whole region.  Nothing     *)
(*  here reads a ghost name, so the section binds a bare [Σ].             *)
(* ===================================================================== *)

Section DurImgRec.
  Context {Σ : gFunctors}.
  Implicit Types Gam : fs_view_names Σ.

  (* a range of [m * n], as [n] runs of [m].  Generic; it belongs beside
     [FsStateInode.big_sepL_seq0] and should move there. *)
  Lemma big_sepL_seq_chunks (Phi : nat -> iProp Σ) (m n : nat) :
    ([∗ list] i ∈ seq 0 n, [∗ list] k ∈ seq 0 m, Phi (m * i + k)%nat)
    ⊣⊢ ([∗ list] j ∈ seq 0 (m * n), Phi j).
  Proof.
    induction n as [| n IH].
    - rewrite Nat.mul_0_r //.
    - rewrite seq_S big_sepL_app big_sepL_cons big_sepL_nil right_id.
      rewrite Nat.add_0_l IH.
      replace (m * S n)%nat with (m * n + m)%nat by lia.
      rewrite seq_app big_sepL_app.
      apply bi.sep_proper; [done |].
      replace (seq (0 + m * n)%nat m) with (seq (m * n + 0)%nat m)
        by (f_equal; lia).
      rewrite -(fmap_add_seq (m * n)%nat 0%nat m) big_sepL_fmap.
      apply big_sepL_proper. intros k j Hk.
      apply lookup_seq in Hk as [-> _]. rewrite Nat.add_0_l //.
  Qed.

  (* ONE INODE BLOCK'S SIXTEEN RECORDS.  The block's bytes decode to SOME
     record list ([IcacheBoot.diblk_bytes_surj], which needs only the
     block's length), and [FsImg.fs_dinode_of_diblk] says that list's slot
     [k] IS the record [FsImg]'s own reader produces at inum [16*bi + k]. *)
  Lemma img_recs_of_block Gam (P : Z -> list (bv 8)) (sb : fs_sb)
      (nib bi : nat) :
    fs_blocks_full P -> (bi < nib)%nat -> 16 * Z.of_nat nib <= 2 ^ 32 ->
    blk_owned Gam (FsImg.sb_inodestart sb + Z.of_nat bi)
                  (P (FsImg.sb_inodestart sb + Z.of_nat bi))
    ⊢ [∗ list] k ∈ seq 0 16,
        rec_owned Gam sb (Z.of_nat (16 * bi + k)%nat)
                  (fs_dinode P sb (Z.of_nat (16 * bi + k)%nat)).
  Proof.
    intros Hfull Hbi Hnib.
    destruct (diblk_bytes_surj
                (P (FsImg.sb_inodestart sb + Z.of_nat bi)) (Hfull _))
      as (ds & Hdwf & Hde).
    iIntros "Hb". rewrite /blk_owned. iDestruct "Hb" as "[_ Hb]".
    rewrite Hde.
    rewrite (rec_owned_at_diblk Gam (FsImg.sb_inodestart sb) (Z.of_nat bi)
               ds Hdwf).
    iApply (big_sepL_mono with "Hb"). intros j k Hk.
    apply lookup_seq in Hk as [-> Hlt].
    (* the inum, and the two arithmetic readings of it *)
    assert (Hz : Z.of_nat (16 * bi + j)%nat = 16 * Z.of_nat bi + Z.of_nat j)
      by lia.
    assert (Hrng : 0 <= Z.of_nat (16 * bi + j)%nat < 2 ^ 32) by lia.
    assert (Hbv : bv_unsigned (fs_inum_bv (Z.of_nat (16 * bi + j)%nat))
                  = Z.of_nat (16 * bi + j)%nat).
    { rewrite /fs_inum_bv. apply Z_to_bv_small.
      assert (Hm : bv_modulus 32 = 2 ^ 32) by (vm_compute; reflexivity).
      rewrite Hm. lia. }
    assert (Hslot : islot (fs_inum_bv (Z.of_nat (16 * bi + j)%nat)) = j).
    { rewrite /islot Hbv Hz.
      rewrite (Z.mul_comm 16 (Z.of_nat bi)) Z.add_comm Z_mod_plus_full.
      rewrite Z.mod_small; [lia | lia]. }
    assert (Hblk : P (IBLOCK (fs_inum_bv (Z.of_nat (16 * bi + j)%nat))
                             (FsImg.sb_inodestart sb))
                   = diblk_bytes ds).
    { rewrite /IBLOCK Hbv Hz.
      assert (Hd : (16 * Z.of_nat bi + Z.of_nat j) `div` 16 = Z.of_nat bi).
      { rewrite (Z.mul_comm 16 (Z.of_nat bi)) Z.div_add_l; [| lia].
        rewrite (Z.div_small (Z.of_nat j) 16); lia. }
      rewrite Hd. replace (Z.of_nat bi + FsImg.sb_inodestart sb)
        with (FsImg.sb_inodestart sb + Z.of_nat bi) by lia.
      exact Hde. }
    rewrite (rec_owned_sb Gam sb (Z.of_nat (16 * bi + j)%nat) _ Hrng).
    rewrite (fs_dinode_of_diblk P sb (Z.of_nat (16 * bi + j)%nat) ds
               Hdwf Hblk) Hslot Hz //.
  Qed.

  (* ...and the whole region, at the region's inum set *)
  Lemma img_recs_of_region Gam (P : Z -> list (bv 8)) (sb : fs_sb)
      (nib : nat) :
    fs_blocks_full P -> 16 * Z.of_nat nib <= 2 ^ 32 ->
    ([∗ list] bi ∈ seq 0 nib,
       blk_owned Gam (FsImg.sb_inodestart sb + Z.of_nat bi)
                     (P (FsImg.sb_inodestart sb + Z.of_nat bi)))
    ⊢ [∗ set] z ∈ region_inums nib, rec_owned Gam sb z (fs_dinode P sb z).
  Proof.
    intros Hfull Hnib.
    iIntros "H".
    iAssert ([∗ list] bi ∈ seq 0 nib, [∗ list] k ∈ seq 0 16,
               rec_owned Gam sb (Z.of_nat (16 * bi + k)%nat)
                         (fs_dinode P sb (Z.of_nat (16 * bi + k)%nat)))%I
      with "[H]" as "H".
    { iApply (big_sepL_mono with "H"). intros j bi Hbi.
      apply lookup_seq in Hbi as [-> Hlt].
      iApply (img_recs_of_block Gam P sb nib j Hfull Hlt Hnib). }
    rewrite (big_sepL_seq_chunks
               (fun j => rec_owned Gam sb (Z.of_nat j) (fs_dinode P sb (Z.of_nat j)))
               16 nib).
    iApply (region_of_seq
              (fun z => rec_owned Gam sb z (fs_dinode P sb z)) nib with "H").
  Qed.

End DurImgRec.

(* ===================================================================== *)
(*  6.  THE WHOLE INODE MAP'S FOOTPRINT                                   *)
(* ===================================================================== *)

Section DurImgInodes.
  Context `{!riscvGS Σ, !xv6G Σ}.

  (* the free arm's fact: outside the live set the record is typed 0,
     whether it is below [ninodes] (by [FsImg.fs_live_set_elem_of]) or in
     the [[ninodes, 16*nib)] tail ([FsImg.fs_region_free]).  Verbatim
     [FsCfgBoot.ipool_alloc_of_image]'s. *)
  Lemma img_free_ty (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) (z : Z) :
    fs_region_free P sb nib = true ->
    z ∈ region_inums nib -> z ∉ fs_live_set P sb ->
    bv_unsigned (di_type (fs_dinode P sb z)) = 0.
  Proof.
    intros Hrf Hz Hna. apply region_inums_spec in Hz.
    destruct (Z_lt_ge_dec z (FsImg.sb_ninodes sb)) as [Hlt | Hge].
    - destruct (decide (bv_unsigned (di_type (fs_dinode P sb z)) = 0))
        as [H0 | H0]; [exact H0 |].
      exfalso. apply Hna, fs_live_set_elem_of. split; [lia | exact H0].
    - exact (fs_region_free_spec P sb nib z Hrf
               ltac:(lia) ltac:(lia) ltac:(lia)).
  Qed.

  (* THE INODE MAP'S PHI HALF.  The records come from the inode region's
     own blocks (section 5); the data blocks come one live inode at a time
     out of [FsBoot.big_sepS_carve]'s cut; a FREE inum owns neither, which
     is what the bare sweep buys. *)
  Lemma img_inodes_phi (g : gname) (Gd : fs_dur_names)
      (P : Z -> list (bv 8)) (sb : fs_sb) (cov : gset Z) (nib : nat) :
    fsimg_wf P sb = true -> fs_region_wf P sb nib = true ->
    fs_region_bare P sb nib = true -> fs_blocks_full P ->
    FsImg.sb_ninodes sb <= 16 * Z.of_nat nib ->
    (forall b : Z, fs_data_start sb <= b < sb_size sb -> b ∈ cov) ->
    ([∗ set] z ∈ region_inums nib,
       rec_owned (fs_gamma_D g Gd) sb z (fs_dinode P sb z)) -∗
    ([∗ set] i ∈ fs_live_set P sb,
       [∗ set] b ∈ fs_inode_blocks_set P sb i,
         blk_owned (fs_gamma_D g Gd) b (P b)) -∗
    [∗ map] i ↦ n ∈ img_nodes P sb nib,
      inode_phi (fs_gamma_D g Gd) sb i n.
  Proof.
    intros Hwf Hrw Hbare Hfull Hnin Hcov.
    pose proof (fs_region_wf_free _ _ _ Hrw) as Hrf.
    pose proof (fs_region_wf_nlink _ _ _ Hrw) as Hrnl.
    assert (HAsub : fs_live_set P sb ⊆ region_inums nib).
    { apply elem_of_subseteq. intros z Hz.
      apply fs_live_set_elem_of in Hz as [Hran _].
      apply region_inums_spec. lia. }
    iIntros "Hrec Hblk".
    (* the LIVE arm, one named application per inum *)
    iAssert ([∗ set] z ∈ fs_live_set P sb,
               (([∗ map] k ↦ bs ∈ fn_blk (img_node P sb z),
                   blk_owned (fs_gamma_D g Gd) (fn_naddr (img_node P sb z) k) bs)
                ∗ ind_owned (fs_gamma_D g Gd) (img_node P sb z)))%I
      with "[Hblk]" as "HpA".
    { iApply (big_sepS_mono with "Hblk"). intros z Hz.
      apply fs_live_set_elem_of in Hz as [Hran Hty].
      iApply (img_inode_phi_res g Gd P sb cov nib z Hwf Hrnl Hfull Hnin
                Hcov Hran Hty). }
    (* the FREE arm: a bare node owns no block and has no indirect block *)
    iAssert ([∗ set] z ∈ region_inums nib ∖ fs_live_set P sb,
               (([∗ map] k ↦ bs ∈ fn_blk (img_node P sb z),
                   blk_owned (fs_gamma_D g Gd) (fn_naddr (img_node P sb z) k) bs)
                ∗ ind_owned (fs_gamma_D g Gd) (img_node P sb z)))%I
      as "HpF".
    { iApply big_sepS_intro. iModIntro. iIntros (z Hz).
      apply elem_of_difference in Hz as [Hz1 Hz2].
      pose proof (img_free_ty P sb nib z Hrf Hz1 Hz2) as Hty0.
      pose proof (img_node_bare P sb nib z Hbare Hrnl
                    (proj1 (region_inums_spec nib z) Hz1) Hty0) as Hb.
      pose proof Hb as (_ & _ & Hblk0 & _ & _).
      rewrite Hblk0 big_sepM_empty.
      rewrite (ind_owned_none (fs_gamma_D g Gd) (img_node P sb z)
                 (fn_bare_indb _ Hb)).
      by iSplit. }
    (* the two arms, back as one big-op over the region *)
    iDestruct (big_sepS_union with "[$HpA $HpF]") as "Hp";
      [set_solver |].
    rewrite -(union_difference_L (fs_live_set P sb) (region_inums nib) HAsub).
    (* ...beside the records, and that pair IS [inode_phi] *)
    iDestruct (big_sepS_sep_2 with "Hrec Hp") as "Hphi".
    rewrite (big_sepM_img_nodes
               (fun i n => inode_phi (fs_gamma_D g Gd) sb i n) P sb nib).
    iApply (big_sepS_mono with "Hphi"). intros z _.
    iIntros "H". iExact "H".
  Qed.

End DurImgInodes.

(* ===================================================================== *)
(*  7.  THE BITMAP BLOCK AND THE FREE POOL                                *)
(*                                                                        *)
(*  [FsCfgBoot.bitmap_res_of_image] at [Gamma] instead of at              *)
(*  [BitmapInv.bitmap_res]: same two pieces, same [used] set (the block's *)
(*  OWN bits, so the byte-level equation is [FsImg.bm_bytes_fs_bmap_set]  *)
(*  and no image sweep is added), same disjointness argument.             *)
(* ===================================================================== *)

Section DurImgBitmap.
  Context {Σ : gFunctors}.

  Lemma img_free_bitmap (Gam : fs_view_names Σ) (P : Z -> list (bv 8))
      (sb : fs_sb) :
    fsimg_wf P sb = true -> fs_blocks_full P ->
    ([∗ set] b ∈ fs_bitmap_spent P sb, blk_owned Gam b (P b))
    ⊢ free_bitmap Gam sb
        (FsImg.fs_bmap_set BSIZE (P (FsImg.sb_bmapstart sb))).
  Proof.
    intros Hwf Hfull.
    pose proof (fsimg_wf_sb P sb Hwf) as Hsb.
    destruct (fsimg_wf_used P sb Hwf) as (u & _ & _ & Hbw).
    (* the bitmap block is below the data region, so it is not in the pool *)
    assert (Hdj : ({[ FsImg.sb_bmapstart sb ]} : gset Z)
                  ## free_set (FsImg.sb_size sb)
                       (FsImg.fs_bmap_set BSIZE (P (FsImg.sb_bmapstart sb)))).
    { apply disjoint_singleton_l. intros Hin.
      apply elem_of_free_set in Hin as [Hran Hnu].
      destruct (fs_bmap_set_free P sb u (FsImg.sb_bmapstart sb) Hsb Hbw
                  Hran Hnu) as [Hge _].
      unfold fs_data_start in Hge. lia. }
    assert (Hbytes : bm_bytes BSIZE
                       (FsImg.fs_bmap_set BSIZE (P (FsImg.sb_bmapstart sb)))
                     = P (FsImg.sb_bmapstart sb))
      by (apply bm_bytes_fs_bmap_set; apply Hfull).
    rewrite /fs_bitmap_spent (big_sepS_union _ _ _ Hdj) big_sepS_singleton.
    iIntros "[Hbm Hpool]".
    rewrite /free_bitmap /free_bitmap_at Hbytes.
    iSplitL "Hbm"; [iExact "Hbm" |].
    iApply free_pool_intro.
    iApply (big_sepS_mono with "Hpool"). intros b Hb.
    iIntros "Hf". by iExists (P b).
  Qed.

  (* THE RESTRICTED VIEW, AS A BIG-OP OVER ITS SET.  [LogDefs.fs_restrict]
     is [set_to_map], i.e. [list_to_map] over the set's elements, so this
     is [FsCfgBoot.big_sepM_img_nodes]' proof at a different map.  It
     belongs beside [fs_restrict]'s own theory in [LogDefs.v]. *)
  Lemma fs_restrict_keys (P : Z -> list (bv 8)) (S : gset Z) :
    ((fun b : Z => (b, P b)) <$> elements S).*1 = elements S.
  Proof.
    rewrite -list_fmap_compose.
    rewrite (list_fmap_ext _ id); [apply list_fmap_id | intros; reflexivity].
  Qed.

  Lemma big_sepM_fs_restrict (Phi : Z -> list (bv 8) -> iProp Σ)
      (P : Z -> list (bv 8)) (S : gset Z) :
    ([∗ map] b ↦ bs ∈ fs_restrict P S, Phi b bs)
    ⊣⊢ ([∗ set] b ∈ S, Phi b (P b)).
  Proof.
    rewrite /fs_restrict /set_to_map.
    assert (Hnd : base.NoDup (((fun b : Z => (b, P b)) <$> elements S).*1))
      by (rewrite fs_restrict_keys; apply NoDup_elements).
    rewrite (big_sepM_list_to_map Phi _ Hnd).
    rewrite big_sepL_fmap /=.
    rewrite big_sepS_elements //.
  Qed.

End DurImgBitmap.

(* ===================================================================== *)
(*  8.  THE IMAGE'S ABSTRACT STATE, AND THE BLOCKS IT OWNS                *)
(* ===================================================================== *)

(* the state [fs_view Gamma_D] binds at boot.  Every field is a FUNCTION of
   the image: the parsed superblock, block 1's raw bytes (there is no
   superblock encoder in the tree, so [FsState.fs_state_rec] carries the
   bytes), the region's decoded nodes, and the bitmap block's own bit set. *)
Definition img_state (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
  : fs_state_rec :=
  MkFsS sb (P SB_BNO) (img_nodes P sb nib)
        (FsImg.fs_bmap_set BSIZE (P (FsImg.sb_bmapstart sb))).

(* ...and the blocks its footprint covers: the superblock, the inode
   region, the bitmap block and the whole free pool, and every live
   inode's own blocks.  [FsCfgBoot.fs_kit_spent] MINUS the log region,
   which is outside the home set to begin with. *)
Definition img_owned (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
  : gset Z :=
  ({[ (1:Z) ]} ∪ ireg_blk_set (FsImg.sb_inodestart sb) nib
     ∪ fs_bitmap_spent P sb)
  ∪ fs_live_blocks P sb (fs_live_set P sb).

(* ===================================================================== *)
(*  9.  THE DURABLE INSTANCE, FROM THE IMAGE                              *)
(* ===================================================================== *)

Section DurImgMain.
  Context `{!riscvGS Σ, !xv6G Σ}.

  Lemma fs_dur_of_image (g : gname) (dk : Z -> bv 8) (ndisk : nat)
      (sb : fs_sb) (nib : nat) (cov : gset Z) :
    fs_boot_image_wf dk ndisk sb nib cov ->
    (* the missing image sweep -- header (2) *)
    fs_region_bare (fs_blocks dk) sb nib = true ->
    (* the link family's own law at the image's map -- header (3) *)
    ✓ link_elem (img_nodes (fs_blocks dk) sb nib) ->
    fs_dbelems g (fs_dbytes (fs_restrict (fs_blocks dk)
                              (fs_home_set cov (FsImg.sb_logstart sb))))
    ⊢ |==> ∃ Gd : fs_dur_names,
        ghost_map_auth (fdn_top Gd) 1 (img_nodes (fs_blocks dk) sb nib)
        ∗ fs_state (fs_gamma_D g Gd) (img_state (fs_blocks dk) sb nib)
        ∗ ([∗ set] b ∈ fs_home_set cov (FsImg.sb_logstart sb)
                       ∖ img_owned (fs_blocks dk) sb nib,
             blk_owned (fs_gamma_D g Gd) b (fs_blocks dk b)).
  Proof.
    intros (Hwf & Hrw & Hnin & Hnib32 & Hnibpos & Hnibq & Hcovin & Hcovmeta
            & Hcovdata & Hparse & Hnib16 & Hndisk & Hlinkeq) Hbare Hlink.
    (* ---- the pure geometry, off [fs_sb_ok] alone -------------------- *)
    pose proof (fsimg_wf_sb _ _ Hwf) as Hsb.
    pose proof (sbo_logstart sb Hsb) as Hls.
    pose proof (sbo_nlog sb Hsb) as Hnl.
    pose proof (sbo_inodestart sb Hsb) as Hist.
    pose proof (sbo_bmapstart sb Hsb) as Hbms.
    pose proof (sbo_ninodes sb Hsb) as Hni. unfold FsImg.ROOTINO in Hni.
    assert (Hfull : fs_blocks_full (fs_blocks dk))
      by (intros b; apply fs_blocks_length).
    assert (Hds : fs_data_start sb
                  = FsImg.sb_inodestart sb + Z.of_nat nib + 1)
      by (rewrite /fs_data_start; lia).
    assert (HlogI : forall b : Z,
              b ∈ log_region_set (FsImg.sb_logstart sb) ->
              1 < b < FsImg.sb_inodestart sb).
    { intros b Hb.
      pose proof (log_region_bound (FsImg.sb_logstart sb) b Hb).
      unfold LOGBLOCKS in *. lia. }
    assert (HiregI : forall b : Z,
              b ∈ ireg_blk_set (FsImg.sb_inodestart sb) nib ->
              FsImg.sb_inodestart sb <= b < fs_data_start sb).
    { intros b Hb. apply ireg_blk_set_spec in Hb. lia. }
    (* ---- the three peels, each a subset of what is left ------------- *)
    assert (H1home : ({[ (1:Z) ]} : gset Z)
                     ⊆ fs_home_set cov (FsImg.sb_logstart sb)).
    { rewrite /fs_home_set. apply elem_of_subseteq. intros b Hb.
      apply elem_of_singleton in Hb as ->. apply elem_of_difference.
      split; [apply Hcovmeta; lia |].
      intros Hc. pose proof (HlogI 1 Hc). lia. }
    assert (Hiregsub : ireg_blk_set (FsImg.sb_inodestart sb) nib
                       ⊆ fs_home_set cov (FsImg.sb_logstart sb)
                         ∖ ({[ (1:Z) ]} : gset Z)).
    { apply elem_of_subseteq. intros b Hb. pose proof (HiregI b Hb).
      rewrite /fs_home_set. apply elem_of_difference. split.
      - apply elem_of_difference. split; [apply Hcovmeta; lia |].
        intros Hc. pose proof (HlogI b Hc). lia.
      - rewrite elem_of_singleton. lia. }
    assert (HcovC : forall b : Z, fs_data_start sb <= b < FsImg.sb_size sb ->
              b ∈ (fs_home_set cov (FsImg.sb_logstart sb)
                     ∖ ({[ (1:Z) ]} : gset Z))
                    ∖ ireg_blk_set (FsImg.sb_inodestart sb) nib).
    { intros b Hb. apply elem_of_difference. split.
      - rewrite /fs_home_set. apply elem_of_difference. split.
        + apply elem_of_difference. split; [apply Hcovdata; exact Hb |].
          intros Hc. pose proof (HlogI b Hc). lia.
        + rewrite elem_of_singleton. lia.
      - intros Hc. pose proof (HiregI b Hc). lia. }
    (* ---- the carve's own two premises ------------------------------- *)
    destruct (fsimg_wf_used (fs_blocks dk) sb Hwf) as (u & Hus & Hnd & _).
    assert (HAl : forall z : Z, z ∈ fs_live_set (fs_blocks dk) sb ->
              0 <= z < FsImg.sb_ninodes sb
              /\ bv_unsigned (di_type (fs_dinode (fs_blocks dk) sb z)) <> 0)
      by (intros z Hz; exact (proj1 (fs_live_set_elem_of _ _ z) Hz)).
    assert (Hsub : forall i : Z, i ∈ elements (fs_live_set (fs_blocks dk) sb) ->
              fs_inode_blocks_set (fs_blocks dk) sb i
              ⊆ (fs_home_set cov (FsImg.sb_logstart sb)
                   ∖ ({[ (1:Z) ]} : gset Z))
                  ∖ ireg_blk_set (FsImg.sb_inodestart sb) nib).
    { intros i Hi. apply elem_of_elements in Hi.
      destruct (HAl i Hi) as [Hran Hty].
      apply (fs_inode_blocks_set_sub (fs_blocks dk) sb i _
               (fsimg_wf_inode _ sb i Hwf Hran Hty) HcovC). }
    assert (Hdisj : forall i j : Z,
              i ∈ elements (fs_live_set (fs_blocks dk) sb) ->
              j ∈ elements (fs_live_set (fs_blocks dk) sb) -> i <> j ->
              fs_inode_blocks_set (fs_blocks dk) sb i
              ## fs_inode_blocks_set (fs_blocks dk) sb j).
    { intros i j Hi Hj Hne.
      apply elem_of_elements in Hi. apply elem_of_elements in Hj.
      destruct (HAl i Hi) as [Hrani Htyi].
      destruct (HAl j Hj) as [Hranj Htyj].
      exact (fs_inode_blocks_disjoint (fs_blocks dk) sb i j Hnd Hrani Hranj
               Hne Htyi Htyj). }
    (* ---- the bitmap's own subset (verbatim [fs_cfg_alloc]'s) -------- *)
    assert (Hbmeq : FsImg.sb_bmapstart sb
                    = FsImg.sb_inodestart sb + Z.of_nat nib)
      by (unfold fs_data_start in Hds; lia).
    assert (Hbmsub : fs_bitmap_spent (fs_blocks dk) sb
                     ⊆ ((fs_home_set cov (FsImg.sb_logstart sb)
                           ∖ ({[ (1:Z) ]} : gset Z))
                          ∖ ireg_blk_set (FsImg.sb_inodestart sb) nib)
                         ∖ fs_live_blocks (fs_blocks dk) sb
                             (fs_live_set (fs_blocks dk) sb)).
    { apply elem_of_subseteq. intros b Hb.
      assert (Hlive : b ∈ fs_live_blocks (fs_blocks dk) sb
                            (fs_live_set (fs_blocks dk) sb) -> b ∈ u)
        by (apply (fs_live_blocks_used (fs_blocks dk) sb _ u b Hus HAl)).
      destruct (fs_bitmap_spent_bound (fs_blocks dk) sb u b Hwf Hus Hb)
        as [-> | [Hran Hnu]].
      - apply elem_of_difference. split.
        + apply elem_of_difference. split.
          * rewrite /fs_home_set. apply elem_of_difference. split.
            { apply elem_of_difference. split.
              - apply Hcovmeta. unfold fs_data_start. lia.
              - intros Hc. pose proof (HlogI _ Hc). lia. }
            rewrite elem_of_singleton. lia.
          * intros Hc. apply ireg_blk_set_spec in Hc. lia.
        + intros Hc.
          destruct (fs_live_blocks_range (fs_blocks dk) sb _ _ Hwf HAl Hc)
            as [Hge _]. unfold fs_data_start in Hge. lia.
      - apply elem_of_difference. split.
        + apply elem_of_difference. split.
          * rewrite /fs_home_set. apply elem_of_difference. split.
            { apply elem_of_difference. split.
              - apply Hcovdata. lia.
              - intros Hc. pose proof (HlogI b Hc). lia. }
            rewrite elem_of_singleton. lia.
          * intros Hc. pose proof (HiregI b Hc). lia.
        + intros Hc. exact (Hnu (Hlive Hc)). }
    (* ---- the residual, as one set ----------------------------------- *)
    assert (Hset : ((((fs_home_set cov (FsImg.sb_logstart sb)
                         ∖ ({[ (1:Z) ]} : gset Z))
                        ∖ ireg_blk_set (FsImg.sb_inodestart sb) nib)
                       ∖ fs_live_blocks (fs_blocks dk) sb
                           (fs_live_set (fs_blocks dk) sb))
                      ∖ fs_bitmap_spent (fs_blocks dk) sb)
                   = fs_home_set cov (FsImg.sb_logstart sb)
                       ∖ img_owned (fs_blocks dk) sb nib).
    { apply set_eq. intros b. rewrite /img_owned.
      rewrite 5!elem_of_difference 3!elem_of_union. tauto. }
    (* ================================================================ *)
    iIntros "Hd".
    (* the two durable gnames -- the CLIENT allocates them (2c-names) *)
    iMod (fs_boot_alloc_at (img_nodes (fs_blocks dk) sb nib)
            (img_nodes (fs_blocks dk) sb nib) Hlink)
      as (gl gt) "(Htopa & _ & Hlnk)".
    iModIntro. iExists (MkFsDurNames gl gt).
    iSplitL "Htopa"; [iExact "Htopa" |].
    (* the flat elements, as one exclusive run per home block *)
    assert (Hlen : forall b bs,
              fs_restrict (fs_blocks dk)
                (fs_home_set cov (FsImg.sb_logstart sb)) !! b = Some bs ->
              length bs = BSIZE).
    { intros b bs Hb. apply fs_restrict_lookup_Some in Hb as [_ ->].
      apply fs_blocks_length. }
    rewrite (fs_dbelems_dbytes g (MkFsDurNames gl gt) _ Hlen).
    rewrite (big_sepM_fs_restrict
               (fun b bs => blk_owned (fs_gamma_D g (MkFsDurNames gl gt)) b bs)
               (fs_blocks dk) (fs_home_set cov (FsImg.sb_logstart sb))).
    (* ---- peel block 1 ---------------------------------------------- *)
    iDestruct (big_sepS_split_sub _ _ ({[ (1:Z) ]} : gset Z) H1home
                 with "Hd") as "[Hb1 Hd]".
    rewrite big_sepS_singleton.
    (* ---- peel the inode region, and decode its records -------------- *)
    iDestruct (big_sepS_split_sub _ _
                 (ireg_blk_set (FsImg.sb_inodestart sb) nib) Hiregsub
                 with "Hd") as "[Hbireg Hd]".
    iDestruct (ireg_blk_of_set
                 (fun b => blk_owned (fs_gamma_D g (MkFsDurNames gl gt)) b
                             (fs_blocks dk b))
                 (FsImg.sb_inodestart sb) nib with "Hbireg") as "Hbireg".
    iDestruct (img_recs_of_region (fs_gamma_D g (MkFsDurNames gl gt))
                 (fs_blocks dk) sb nib Hfull Hnib32 with "Hbireg") as "Hrec".
    (* ---- carve the live inodes' blocks ------------------------------ *)
    iDestruct (big_sepS_carve
                 (fun b => blk_owned (fs_gamma_D g (MkFsDurNames gl gt)) b
                             (fs_blocks dk b))%I
                 _ (elements (fs_live_set (fs_blocks dk) sb))
                 (fs_inode_blocks_set (fs_blocks dk) sb)
                 (NoDup_elements _) Hsub Hdisj with "Hd") as "[Hpc Hd]".
    iDestruct (big_sepS_of_elements
                 (fun i => [∗ set] b ∈ fs_inode_blocks_set (fs_blocks dk) sb i,
                             blk_owned (fs_gamma_D g (MkFsDurNames gl gt)) b
                               (fs_blocks dk b))%I
                 (fs_live_set (fs_blocks dk) sb) with "Hpc") as "Hpc".
    (* the carve's remainder, at the folded spelling of the live set *)
    iAssert ([∗ set] b ∈ ((fs_home_set cov (FsImg.sb_logstart sb)
                             ∖ ({[ (1:Z) ]} : gset Z))
                            ∖ ireg_blk_set (FsImg.sb_inodestart sb) nib)
                           ∖ fs_live_blocks (fs_blocks dk) sb
                               (fs_live_set (fs_blocks dk) sb),
               blk_owned (fs_gamma_D g (MkFsDurNames gl gt)) b
                 (fs_blocks dk b))%I with "[Hd]" as "Hd";
      [iExact "Hd" |].
    (* ---- peel the bitmap block and the free pool -------------------- *)
    iDestruct (big_sepS_split_sub _ _ (fs_bitmap_spent (fs_blocks dk) sb)
                 Hbmsub with "Hd") as "[Hbm Hd]".
    iDestruct (img_free_bitmap (fs_gamma_D g (MkFsDurNames gl gt))
                 (fs_blocks dk) sb Hwf Hfull with "Hbm") as "Hbm".
    iEval (rewrite Hset) in "Hd".
    iSplitR "Hd"; [| iExact "Hd"].
    (* ================================================================ *)
    (* ---- the inode map's phi half ---------------------------------- *)
    iDestruct (img_inodes_phi g (MkFsDurNames gl gt) (fs_blocks dk) sb cov nib
                 Hwf Hrw Hbare Hfull Hnin Hcovdata with "Hrec Hpc") as "Hphi".
    (* ---- assemble ---------------------------------------------------- *)
    iApply (fs_state_of (fs_gamma_D g (MkFsDurNames gl gt))
              (img_state (fs_blocks dk) sb nib) with "[Hb1 Hphi Hbm] Hlnk []").
    { rewrite /fs_footprint /img_state.
      cbn [fss_sb fss_sbb fss_inodes fss_used].
      iSplitL "Hb1"; [iExact "Hb1" |].
      iSplitL "Hphi"; [iExact "Hphi" |].
      rewrite /free_bitmap /free_bitmap_at.
      iDestruct "Hbm" as "[Hbmb Hpool]". iFrame. }
    rewrite /fs_pure /img_state.
    cbn [fss_sb fss_sbb fss_inodes fss_used].
    iSplitR; [iPureIntro; exact Hparse |].
    rewrite (big_sepM_img_nodes
               (fun i n => ⌜inode_local i n⌝%I) (fs_blocks dk) sb nib).
    iApply big_sepS_intro. iModIntro. iIntros (z Hz). iPureIntro.
    exact (img_inode_local (fs_blocks dk) sb cov nib z Hwf Hrw Hbare Hfull
             Hnin Hcovdata Hz).
  Qed.

  (* ...and the shape [P_wf] is stated in.  [FsState.fs_view] binds the
     state existentially, so the residual is what a caller must still
     account for.  THE RESIDUAL IS NOT OPTIONAL: at the mkfs image it is
     empty (durable-disk 2c's survey (iii) -- home is [{1} ∪ [33,2000)],
     block 0 and the log region are outside it, and [img_owned] covers the
     rest: W5 makes every used data block a live inode's and every unused
     one a member of [free_set]), but nothing makes exactness true of an
     arbitrary reachable state, and returning the leftover elements is
     what keeps [P_wf] honest without a domain sweep.  Its BLOCK-map
     reading is [fs_restrict (fs_blocks dk) (home ∖ img_owned …)], through
     [big_sepM_fs_restrict]. *)
  Corollary fs_dur_view_of_image (g : gname) (dk : Z -> bv 8) (ndisk : nat)
      (sb : fs_sb) (nib : nat) (cov : gset Z) :
    fs_boot_image_wf dk ndisk sb nib cov ->
    fs_region_bare (fs_blocks dk) sb nib = true ->
    ✓ link_elem (img_nodes (fs_blocks dk) sb nib) ->
    fs_dbelems g (fs_dbytes (fs_restrict (fs_blocks dk)
                              (fs_home_set cov (FsImg.sb_logstart sb))))
    ⊢ |==> ∃ Gd : fs_dur_names,
        FsState.fs_view (fs_gamma_D g Gd)
        ∗ ([∗ set] b ∈ fs_home_set cov (FsImg.sb_logstart sb)
                       ∖ img_owned (fs_blocks dk) sb nib,
             blk_owned (fs_gamma_D g Gd) b (fs_blocks dk b)).
  Proof.
    intros Himg Hbare Hlink.
    iIntros "Hd".
    iMod (fs_dur_of_image g dk ndisk sb nib cov Himg Hbare Hlink with "Hd")
      as (Gd) "(Htopa & Hst & Hrem)".
    iModIntro. iExists Gd. iFrame "Hrem".
    rewrite /FsState.fs_view. iExists (img_state (fs_blocks dk) sb nib).
    iFrame "Hst". iExact "Htopa".
  Qed.

End DurImgMain.

(* ===================================================================== *)
(* 10.  THE LINK FAMILY'S VALIDITY, REDUCED TO THE ROOT'S OWN ENTRIES     *)
(*                                                                        *)
(*  [FsState.fs_boot_alloc_at]'s premise [✓ link_elem I] is the           *)
(*  tokens-<=-nlink law of the initial map -- the fact                    *)
(*  [FsState.fs_links_valid] READS OFF a durable instance and which the   *)
(*  boot, having none, owes.  [FsState.v]'s header says W9                *)
(*  ([FsImg.fs_links_wf]) plus conjunct (13) ([FsImg.fs_links_eq])        *)
(*  discharge it at the image.  THAT IS OPTIMISTIC AS IT STANDS, and this *)
(*  section says exactly how far those two get.                          *)
(*                                                                        *)
(*  W9 DOES give the structural half outright, and it is a strong fact:   *)
(*  at every live inum which is a DIRECTORY, W9 forces [z = ROOTINO], so  *)
(*  the mkfs image has EXACTLY ONE directory and every other node's entry *)
(*  map is empty ([img_dir_entries_empty]).  The family therefore splits  *)
(*  as "one authority per inum" times "the root's outgoing tokens"        *)
(*  ([link_elem_split] + [ent_ops_one]), and since the all-at-home        *)
(*  family [FsState.link_full_map] is valid unconditionally, validity     *)
(*  follows from ONE inclusion in [fsLinkUR]                              *)
(*  ([link_elem_valid_of_root]).                                          *)
(*                                                                        *)
(*  WHAT IS LEFT is that inclusion -- the root's outgoing tokens are      *)
(*  covered by the inodes' own [nlink]s -- i.e. the survey's (iv)(c)      *)
(*  bridge                                                                *)
(*  from the image's TICKET counting to [FsStateInode.ent_toks].  It is   *)
(*  not a corollary of W9 + (13), for two reasons, and both are about the *)
(*  two counting disciplines disagreeing rather than about arithmetic:    *)
(*                                                                        *)
(*   - [FsImg.fs_rec_ticket] exempts a record naming ITS OWN HOME under   *)
(*     ANY name; [FsStateInode.ent_tokenless] exempts only ["."] and a    *)
(*     [".."] that is orphaned or self-naming.  A root record named       *)
(*     "foo" pointing at the root would owe a token here and pay no       *)
(*     ticket there, and nothing in [fsimg_wf] rules it out.              *)
(*   - the ticket count is per RECORD INDEX while [dir_entries] is a      *)
(*     first-match scan by NAME, so the two agree only through W6's       *)
(*     [FsTree.dir_names_unique], which has to be carried through the     *)
(*     count.                                                             *)
(*                                                                        *)
(*  So the inclusion is a PREMISE of [img_link_valid], stated in the RA's *)
(*  own language, and it is what a later stage has to prove (or what one  *)
(*  more image sweep -- no live non-dot record of the root names the      *)
(*  root -- would make derivable from (13)).                              *)
(* ===================================================================== *)

(* one inode's outgoing tokens, as ONE resource-algebra element: the
   second half of [FsStateInode.link_elem_node] *)
Definition ent_ops (i : Z) (n : fs_node) : fsLinkUR :=
  [^op map] s ↦ t ∈ dir_entries n, ent_elem i (fn_orphan n) s t.

(* ...and the two halves of [FsState.link_full_map] *)
Definition link_auths (I : gmap Z fs_node) : fsLinkUR :=
  [^op map] i ↦ n ∈ I, link_auth_elem i (fn_nlink n).
Definition link_toks_of (I : gmap Z fs_node) : fsLinkUR :=
  [^op map] i ↦ n ∈ I, link_tok_elem i (fn_nlink n).

Lemma link_full_map_split (I : gmap Z fs_node) :
  link_full_map I ≡ link_auths I ⋅ link_toks_of I.
Proof.
  rewrite /link_full_map /link_auths /link_toks_of -big_opM_op //.
Qed.

Lemma link_elem_split (I : gmap Z fs_node) :
  link_elem I ≡ link_auths I ⋅ ([^op map] i ↦ n ∈ I, ent_ops i n).
Proof.
  rewrite /link_elem /link_auths /link_elem_node -big_opM_op //.
Qed.

Lemma ent_ops_empty (i : Z) (n : fs_node) :
  dir_entries n = ∅ -> ent_ops i n = ε.
Proof. rewrite /ent_ops. intros ->. rewrite big_opM_empty //. Qed.

(* AT MOST ONE NODE HAS ENTRIES, so the whole family's token half is that
   one node's *)
Lemma ent_ops_one (I : gmap Z fs_node) (d : Z) (nd : fs_node) :
  I !! d = Some nd ->
  (forall i n, I !! i = Some n -> i <> d -> dir_entries n = ∅) ->
  ([^op map] i ↦ n ∈ I, ent_ops i n) ≡ ent_ops d nd.
Proof.
  intros Hd Hrest.
  rewrite (big_opM_delete (fun i n => ent_ops i n) I d nd Hd).
  rewrite (big_opM_proper (fun i n => ent_ops i n)
             (fun (_ : Z) (_ : fs_node) => ε) (delete d I)); last first.
  { intros i n Hi. apply lookup_delete_Some in Hi as [Hne Hi].
    rewrite (ent_ops_empty i n (Hrest i n Hi ltac:(congruence))) //. }
  rewrite big_opM_unit right_id //.
Qed.

(* THE REDUCTION.  [FsState.link_full_map_valid] is unconditional, and
   validity is downward closed, so the whole obligation is one inclusion. *)
Lemma link_elem_valid_of_root (I : gmap Z fs_node) (d : Z) (nd : fs_node) :
  I !! d = Some nd ->
  (forall i n, I !! i = Some n -> i <> d -> dir_entries n = ∅) ->
  ent_ops d nd ≼ link_toks_of I ->
  ✓ link_elem I.
Proof.
  intros Hd Hrest [x Hx].
  apply (cmra_valid_included (link_elem I) (link_full_map I)
           (link_full_map_valid I)).
  rewrite link_full_map_split link_elem_split (ent_ops_one I d nd Hd Hrest).
  rewrite Hx. exists x. rewrite assoc //.
Qed.

(* ---- the image's own instance --------------------------------------- *)

Lemma img_nodes_lookup_inv (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (z : Z) (n : fs_node) :
  img_nodes P sb nib !! z = Some n ->
  z ∈ region_inums nib /\ n = img_node P sb z.
Proof.
  intros Hz. rewrite /img_nodes in Hz.
  apply elem_of_list_to_map_2 in Hz.
  apply elem_of_list_fmap in Hz as (y & Heq & Hy).
  injection Heq as -> ->. split; [| reflexivity].
  by apply elem_of_elements.
Qed.

(* W9's STRUCTURAL HALF: the image has exactly one directory, the root. *)
Lemma img_dir_entries_empty (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (z : Z) :
  fsimg_wf P sb = true -> fs_region_wf P sb nib = true ->
  z ∈ region_inums nib -> z <> FsImg.ROOTINO ->
  dir_entries (img_node P sb z) = ∅.
Proof.
  intros Hwf Hrw Hz Hne. apply region_inums_spec in Hz.
  rewrite /dir_entries.
  destruct (fn_is_dir (img_node P sb z)) eqn:Hd; [| reflexivity].
  exfalso.
  assert (Hty : bv_unsigned (di_type (fs_dinode P sb z)) = T_DIR_z)
    by exact (proj1 (bool_decide_eq_true _) Hd).
  assert (Hran : 0 <= z < FsImg.sb_ninodes sb).
  { split; [lia |].
    destruct (Z_lt_ge_dec z (FsImg.sb_ninodes sb)) as [Hlt | Hge];
      [exact Hlt |].
    exfalso.
    rewrite (fs_region_free_spec P sb nib z (fs_region_wf_free _ _ _ Hrw)
               ltac:(lia) ltac:(lia) ltac:(lia)) in Hty.
    rewrite /T_DIR_z in Hty. discriminate. }
  destruct (proj2 (fs_links_wf_at P sb z (fsimg_wf_links P sb Hwf) Hran) Hty)
    as (_ & _ & Hroot).
  exact (Hne Hroot).
Qed.

Lemma img_link_valid (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) :
  fsimg_wf P sb = true -> fs_region_wf P sb nib = true ->
  FsImg.sb_ninodes sb <= 16 * Z.of_nat nib ->
  (* THE ONE OBLIGATION LEFT -- see this section's header *)
  ent_ops FsImg.ROOTINO (img_node P sb FsImg.ROOTINO)
    ≼ link_toks_of (img_nodes P sb nib) ->
  ✓ link_elem (img_nodes P sb nib).
Proof.
  intros Hwf Hrw Hnin Hincl.
  pose proof (sbo_ninodes sb (fsimg_wf_sb P sb Hwf)) as Hni.
  unfold FsImg.ROOTINO in Hni.
  assert (Hrootin : FsImg.ROOTINO ∈ region_inums nib)
    by (apply region_inums_spec; rewrite /FsImg.ROOTINO; lia).
  apply (link_elem_valid_of_root _ FsImg.ROOTINO
           (img_node P sb FsImg.ROOTINO)
           (img_nodes_lookup P sb nib FsImg.ROOTINO Hrootin)); [| exact Hincl].
  intros i n Hi Hne.
  destruct (img_nodes_lookup_inv P sb nib i n Hi) as [Hin ->].
  exact (img_dir_entries_empty P sb nib i Hwf Hrw Hin Hne).
Qed.
