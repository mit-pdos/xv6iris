(* ====================================================================== *)
(* FsImgBridge.v -- FROM AN IMAGE'S BYTES TO THE ICACHE'S PURE RECORD      *)
(*                                                                        *)
(* [FsImg.v] reads a disk image: [fs_dinode] decodes a record,            *)
(* [fs_ind_ents] its indirect entries, [fs_data_of] its content, and       *)
(* [fsimg_wf]'s eight boolean clauses (W1-W8) say the image is well        *)
(* formed.  The icache's pool speaks a different vocabulary:              *)
(* [InodeInv.blkmap] + [InodeLock.inode_ok] + [DirView]'s four [dir_*]     *)
(* conjuncts ([IcacheBoot.ipool_shape_alloc]'s premise list).  THIS FILE   *)
(* IS THE ONE TRANSLATION, and it is what [IcacheBoot.ipool_alloc]'s       *)
(* allocated arm must be instantiated at.                                 *)
(*                                                                        *)
(* IT NAMES NO LITERAL IMAGE.  Everything is universally quantified over   *)
(* the block-content function [P], the superblock [sb] and the record      *)
(* [dn], so a proof file may import it; the literal image's own            *)
(* [vm_compute]s stay in [FsImgCheck.v], which this file does not import   *)
(* (nor may it -- the era fupd receives every image fact as a HYPOTHESIS;  *)
(* claude-notes/projects/fs-cfg-boot.md, ruling R3).                      *)
(*                                                                        *)
(* THREE THINGS A READER WOULD OTHERWISE RE-DERIVE.                       *)
(*                                                                        *)
(* (1) [InodeInv.bm_slot]'s IMAGE READING IS [FsImg.fs_slot], not a new    *)
(*     definition: [FS_MAXFILE] and [InodeInv.MAXFILE] are the same        *)
(*     literal ([maxfile_eq] below), so the two are convertible, and       *)
(*     re-deriving [fs_slot]'s injectivity here would cost 636 s of        *)
(*     [vm_compute] at the leaf (measured) instead of riding W4's          *)
(*     [NoDup (fs_used_blocks)] for free ([FsImg.fsimg_wf_slot_inj]).      *)
(*     CONVERTIBLE IS NOT SYNTACTICALLY EQUAL: a [rewrite] or a [destruct  *)
(*     (decide ...)] written at one of the two constants does not fire on  *)
(*     the other, which is why the proofs below convert explicitly.        *)
(*                                                                        *)
(* (2) INJECTIVITY IS NOT IN W3.  [fs_inode_ok] places every named block   *)
(*     in the data region and zeroes every unnamed slot; it says nothing   *)
(*     about two slots of ONE inode naming ONE block, which is             *)
(*     [blkmap_wf]'s fifth conjunct.  W5 (the bitmap) is the free pool's   *)
(*     fact and contributes nothing here.  It is W4, reindexed by          *)
(*     [FsImg.fs_used_nodup_slot_inj], and it arrives as a premise.        *)
(*                                                                        *)
(* (3) [dir_dots_ix] IS NOT DERIVABLE FROM W1-W7 -- W6/W7 pin the dots     *)
(*     through [DirView.dir_first] (the scan [dirlookup] performs), not by *)
(*     INDEX.  That is why W8 ([FsImg.fs_dots_wf]) exists, and             *)
(*     [FsImg.fs_dots_wf_ok] already concludes [dir_dots_ix] outright, so  *)
(*     there is nothing for this file to do about it.                      *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions.
From stdpp.bitvector Require Import definitions.
Require Import SailStdpp.Values.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import FsBlocks.
Require Import DinodeEnc.
Require Import DirView.
Require Import FsTree.
Require Import LogInv.
Require Import BioDefs.
Require Import Xv6G.
Require Import FsImg.
Require Import InodeInv.
Require Import InodeLock.

Local Open Scope Z_scope.

(* the two spellings of 268 (see (1) above) *)
Lemma maxfile_eq : MAXFILE = FS_MAXFILE.
Proof. reflexivity. Qed.

(* ====================================================================== *)
(*  A.  THE MISSING VOCABULARY: an image record's [blkmap]                 *)
(* ====================================================================== *)

(* [InodeLock.inode_ok] is stated over a [blkmap] and a [data] function;
   the image side has [di_addrs] and [fs_ind_ents].  This is the one
   translation, and it is what [ipool_alloc]'s [∃ bm] is instantiated at.
   [data] needs no new definition: [FsImg.fs_data_of] IS it. *)
Definition img_blkmap (P : Z -> list (bv 8)) (dn : dinode) : blkmap :=
  MkBlkmap (take FS_NDIRECT (di_addrs dn))
           (di_addrs dn !!! 12%nat)
           ((fun z => Z_to_bv 32 z) <$> fs_ind_ents P dn).

Lemma img_blkmap_ind (P : Z -> list (bv 8)) (dn : dinode) :
  bm_ind (img_blkmap P dn) = di_addrs dn !!! 12%nat.
Proof. reflexivity. Qed.

(* ---- A1: the thirteen cells ------------------------------------------ *)

Lemma img_blkmap_cells (P : Z -> list (bv 8)) (dn : dinode) :
  dinode_wf dn -> bm_cells (img_blkmap P dn) = di_addrs dn.
Proof.
  intros Hwf. unfold dinode_wf in Hwf.
  unfold bm_cells, img_blkmap. cbn [bm_dir bm_ind bm_ent].
  assert (Hl : length (drop FS_NDIRECT (di_addrs dn)) = 1%nat)
    by (rewrite length_drop, Hwf; reflexivity).
  destruct (drop FS_NDIRECT (di_addrs dn)) as [|a [|b t]] eqn:Hd;
    [ simpl in Hl; lia | | simpl in Hl; lia ].
  assert (Ha : di_addrs dn !!! 12%nat = a).
  { apply list_lookup_total_correct.
    replace 12%nat with (FS_NDIRECT + 0)%nat by reflexivity.
    rewrite <- lookup_drop, Hd. reflexivity. }
  rewrite Ha. rewrite <- Hd. apply take_drop.
Qed.

(* ---- A2: the two lengths --------------------------------------------- *)

Lemma img_blkmap_dirlen (P : Z -> list (bv 8)) (dn : dinode) :
  dinode_wf dn -> length (bm_dir (img_blkmap P dn)) = NDIRECT.
Proof.
  intros Hwf. unfold dinode_wf in Hwf.
  unfold img_blkmap. cbn [bm_dir]. rewrite length_take, Hwf. reflexivity.
Qed.

Lemma img_blkmap_entlen (P : Z -> list (bv 8)) (dn : dinode) :
  length (bm_ent (img_blkmap P dn)) = NINDIRECT.
Proof.
  unfold img_blkmap. cbn [bm_ent].
  rewrite length_fmap, fs_ind_ents_length. reflexivity.
Qed.

(* ---- A3: an indirect entry is a 32-bit number ------------------------ *)

Lemma img_ent_bound (P : Z -> list (bv 8)) (dn : dinode) (j : nat) :
  (j < FS_NINDIRECT)%nat -> 0 <= fs_ind_ents P dn !!! j < 2 ^ 32.
Proof.
  intros Hj. unfold fs_ind_ents. cbv zeta.
  destruct (bv_unsigned (di_addrs dn !!! 12%nat) =? 0) eqn:E.
  - rewrite list_lookup_total_alt, (lookup_replicate_2 _ _ _ Hj).
    simpl. lia.
  - rewrite list_lookup_total_alt, list_lookup_fmap,
            (lookup_seq_lt _ _ _ Hj).
    simpl. unfold fs_le_at.
    pose proof (assemble_bytes_bound
                  ((fun k => P (bv_unsigned (di_addrs dn !!! 12%nat))
                               !!! (4 * j + k)%nat) <$> seq 0 4)) as Hb.
    rewrite length_fmap, length_seq in Hb. exact Hb.
Qed.

(* ---- A4: the map reads the image's own addresses --------------------- *)

Lemma img_blkmap_get (P : Z -> list (bv 8)) (dn : dinode) (k : nat) :
  dinode_wf dn -> (k < MAXFILE)%nat ->
  bv_unsigned (blkmap_get (img_blkmap P dn) k) = fs_blk_addr P dn k.
Proof.
  intros Hwf Hk. unfold dinode_wf in Hwf. unfold MAXFILE in Hk.
  unfold blkmap_get, fs_blk_addr, img_blkmap, NDIRECT, FS_NDIRECT.
  cbn [bm_dir bm_ind bm_ent]. cbv zeta.
  destruct (Nat.ltb_spec k 12) as [Hd|Hd].
  - rewrite decide_True by lia.
    rewrite !list_lookup_total_alt, lookup_take by exact Hd. reflexivity.
  - rewrite decide_False by lia.
    rewrite list_lookup_total_alt, list_lookup_fmap.
    rewrite (list_lookup_lookup_total_lt (fs_ind_ents P dn) (k - 12)%nat)
      by (rewrite fs_ind_ents_length; unfold FS_NINDIRECT; lia).
    simpl. apply Z_to_bv_small.
    replace (k - 12)%nat with (k - FS_NDIRECT)%nat by reflexivity.
    apply img_ent_bound. unfold FS_NDIRECT, FS_NINDIRECT. lia.
Qed.

(* [bm_slot]'s image reading IS [FsImg.fs_slot] -- see (1) in the header *)
Lemma img_blkmap_slot (P : Z -> list (bv 8)) (dn : dinode) (i : nat) :
  dinode_wf dn -> (i <= MAXFILE)%nat ->
  bv_unsigned (bm_slot (img_blkmap P dn) i) = fs_slot P dn i.
Proof.
  intros Hwf Hi. unfold bm_slot.
  destruct (decide (i = MAXFILE)) as [->|Hne].
  - unfold fs_slot. rewrite decide_True by reflexivity. reflexivity.
  - rewrite (img_blkmap_get P dn i Hwf ltac:(lia)).
    unfold fs_slot. rewrite decide_False by (intros Hc; exact (Hne Hc)).
    reflexivity.
Qed.

(* ---- A5: no indirect block => no entries ----------------------------- *)

Lemma img_blkmap_noind (P : Z -> list (bv 8)) (dn : dinode) :
  bv_unsigned (bm_ind (img_blkmap P dn)) = 0 ->
  bm_ent (img_blkmap P dn) = replicate NINDIRECT (bv_0 32).
Proof.
  unfold img_blkmap. cbn [bm_ind bm_ent]. intros H0.
  unfold fs_ind_ents. cbv zeta.
  rewrite (proj2 (Z.eqb_eq _ _) H0), fmap_replicate.
  unfold FS_NINDIRECT, NINDIRECT. f_equal.
  apply bv_eq. vm_compute. reflexivity.
Qed.

(* ====================================================================== *)
(*  B.  THE GEOMETRY FACTS, from [fs_sb_ok] alone                          *)
(* ====================================================================== *)

Lemma log_region_bound (ls b : Z) :
  b ∈ log_region_set ls -> ls <= b <= ls + Z.of_nat LOGBLOCKS.
Proof.
  unfold log_region_set. rewrite elem_of_union. intros [Hs | Hh].
  - rewrite elem_of_list_to_set, elem_of_list_fmap in Hs.
    destruct Hs as (i & -> & Hi). apply elem_of_seq in Hi.
    unfold log_slot_bno. lia.
  - apply elem_of_singleton in Hh. unfold log_hdr_bno in Hh. lia.
Qed.

(* the data region starts ABOVE the log region -- which is what makes
   [blkmap_wf]'s "not a log block" clause free for every image block *)
Lemma img_data_above_log (sb : fs_sb) :
  fs_sb_ok sb -> sb_logstart sb + Z.of_nat LOGBLOCKS < fs_data_start sb.
Proof.
  intros Hok.
  pose proof (sbo_logstart sb Hok) as H1.
  pose proof (sbo_nlog sb Hok) as H2.
  pose proof (sbo_inodestart sb Hok) as H3.
  pose proof (sbo_bmapstart sb Hok) as H4.
  pose proof (sbo_ninodes sb Hok) as H5. unfold FsImg.ROOTINO in H5.
  assert (Hdi : 0 <= FsImg.sb_ninodes sb / 16) by (apply Z.div_pos; lia).
  unfold fs_data_start, LOGBLOCKS. lia.
Qed.

(* ---- B2: every NONZERO slot is a data-region block ------------------- *)

Lemma img_slot_range (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode)
    (i : nat) :
  fs_inode_ok P sb dn -> (i <= MAXFILE)%nat -> fs_slot P dn i <> 0 ->
  fs_data_start sb <= fs_slot P dn i < sb_size sb.
Proof.
  intros Hok Hi Hnz. unfold MAXFILE in Hi.
  unfold fs_slot in Hnz |- *.
  destruct (decide (i = FS_MAXFILE)) as [->|Hne].
  - (* the indirect block *)
    apply (fio_ind P sb dn Hok).
    destruct (Z_le_gt_dec (fs_nblk (bv_unsigned (di_size dn)))
                (Z.of_nat FS_NDIRECT)) as [Hle|Hgt]; [| lia].
    exfalso. apply Hnz. exact (fio_ind_zero P sb dn Hok Hle).
  - unfold fs_blk_addr in Hnz |- *.
    destruct (Nat.ltb_spec i FS_NDIRECT) as [Hd|Hd].
    + (* a direct entry *)
      apply (fio_direct P sb dn Hok i Hd).
      destruct (Z_lt_ge_dec (Z.of_nat i)
                  (fs_nblk (bv_unsigned (di_size dn)))) as [Hlt|Hge];
        [exact Hlt |].
      exfalso. apply Hnz. exact (fio_direct_zero P sb dn Hok i Hd ltac:(lia)).
    + (* an indirect entry *)
      assert (Hj : (i - FS_NDIRECT < FS_NINDIRECT)%nat)
        by (unfold FS_MAXFILE, FS_NDIRECT, FS_NINDIRECT in *; lia).
      apply (fio_ent P sb dn Hok _ Hj).
      destruct (Z_lt_ge_dec (Z.of_nat (i - FS_NDIRECT))
                  (fs_nblk (bv_unsigned (di_size dn)) - Z.of_nat FS_NDIRECT))
        as [Hlt|Hge]; [exact Hlt |].
      exfalso. apply Hnz.
      apply (fio_ent_zero P sb dn Hok _ Hj). lia.
Qed.

(* ====================================================================== *)
(*  C.  [blkmap_wf]                                                        *)
(* ====================================================================== *)

Lemma img_blkmap_wf (P : Z -> list (bv 8)) (sb : fs_sb) (cov : gset Z)
    (logstart : Z) (dn : dinode) :
  dinode_wf dn -> fs_sb_ok sb -> logstart = sb_logstart sb ->
  (forall b : Z, fs_data_start sb <= b < sb_size sb -> b ∈ cov) ->
  fs_inode_ok P sb dn -> fs_slot_inj P dn ->
  blkmap_wf cov logstart (img_blkmap P dn).
Proof.
  intros Hwf Hsb Hls Hcov Hok Hinj. subst logstart.
  pose proof (img_data_above_log sb Hsb) as Hab.
  split; [exact (img_blkmap_dirlen P dn Hwf) |].
  split; [exact (img_blkmap_entlen P dn) |].
  split; [exact (img_blkmap_noind P dn) |].
  split.
  - intros i Hi Hnz.
    rewrite (img_blkmap_slot P dn i Hwf Hi) in Hnz |- *.
    pose proof (img_slot_range P sb dn i Hok Hi Hnz) as Hr.
    split; [exact (Hcov _ Hr) |].
    intros Hc. pose proof (log_region_bound _ _ Hc) as Hlb. lia.
  - intros i j Hi Hj Hnz Heq.
    rewrite maxfile_eq in Hi, Hj.
    apply (Hinj i j Hi Hj).
    + rewrite <- (img_blkmap_slot P dn i Hwf ltac:(rewrite maxfile_eq; exact Hi)).
      exact Hnz.
    + rewrite <- (img_blkmap_slot P dn i Hwf
                    ltac:(rewrite maxfile_eq; exact Hi)),
              <- (img_blkmap_slot P dn j Hwf
                    ltac:(rewrite maxfile_eq; exact Hj)), Heq.
      reflexivity.
Qed.

(* ====================================================================== *)
(*  D.  [inode_ok] -- the whole pure record                                *)
(* ====================================================================== *)

Lemma img_inode_ok (P : Z -> list (bv 8)) (sb : fs_sb) (cov : gset Z)
    (logstart : Z) (dn : dinode) :
  dinode_wf dn -> fs_sb_ok sb -> logstart = sb_logstart sb ->
  fs_blocks_full P ->
  (forall b : Z, fs_data_start sb <= b < sb_size sb -> b ∈ cov) ->
  fs_inode_ok P sb dn -> bv_unsigned (di_type dn) <> 0 ->
  fs_slot_inj P dn ->
  inode_ok cov logstart dn (img_blkmap P dn) (fs_data_of P dn).
Proof.
  intros Hwf Hsb Hls Hfull Hcov Hok Hty Hinj.
  split;
    [exact (img_blkmap_wf P sb cov logstart dn Hwf Hsb Hls Hcov Hok Hinj) |].
  split.
  - (* bm_covers *)
    intros i Hi Hlt.
    rewrite (img_blkmap_get P dn i Hwf Hi).
    assert (Hi' : (i < FS_MAXFILE)%nat)
      by (unfold MAXFILE, FS_MAXFILE in *; lia).
    assert (Hlt' : Z.of_nat i * BSIZE_z < bv_unsigned (di_size dn))
      by (rewrite BSIZE_z_nat in Hlt; exact Hlt).
    pose proof (fs_inode_ok_blk P sb dn i Hok Hi' Hlt') as Hb.
    pose proof (fs_sb_ok_meta sb Hsb) as (Hm1 & Hm2 & Hm3).
    unfold fs_blk_addr in Hb |- *. lia.
  - split; [symmetry; exact (img_blkmap_cells P dn Hwf) |].
    split; [exact Hty |].
    split.
    + (* the size cap *)
      pose proof (fio_size P sb dn Hok) as Hsz.
      replace (Z.of_nat MAXFILE * Z.of_nat BSIZE)
        with (Z.of_nat FS_MAXFILE * BSIZE_z) by (vm_compute; reflexivity).
      exact Hsz.
    + split.
      * (* blk_holes_zero *)
        intros i Hi H0. apply fs_data_of_holes.
        rewrite <- (img_blkmap_get P dn i Hwf Hi). exact H0.
      * (* inode_sized *)
        intros i _. exact (fs_data_of_sized P dn Hfull i).
Qed.

(* ====================================================================== *)
(*  E.  THE THREE [dir_*] CONJUNCTS W6 CARRIES                             *)
(*                                                                        *)
(*  The FOURTH, [dir_dots_ix], is [FsImg.fs_dots_wf_ok] / W8 outright --   *)
(*  see (3) in the header.                                                *)
(* ====================================================================== *)

Lemma img_dir_ok (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) (dn : dinode)
    (nib : nat) :
  FsImg.sb_ninodes sb <= 16 * Z.of_nat nib ->
  (bv_unsigned (di_type dn) = T_DIR_z -> fs_dir_ok P sb i dn) ->
  dir_ok nib dn (fs_data_of P dn).
Proof.
  intros Hnib H Hty.
  exact (fs_dir_ok_inums P sb i dn nib (H Hty) Hnib).
Qed.

Lemma img_dir_uniq (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) (dn : dinode) :
  (bv_unsigned (di_type dn) = T_DIR_z -> fs_dir_ok P sb i dn) ->
  dir_uniq dn (fs_data_of P dn).
Proof. intros H Hty. exact (fdo_unique P sb i dn (H Hty)). Qed.

(* FREE, for every ALLOCATED inum: W3's [1 <= nlink] makes the orphan
   clause vacuous.  (A free inum takes [dir_orphan_clean_free].) *)
Lemma img_dir_orphan_clean (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode) :
  fs_inode_ok P sb dn -> dir_orphan_clean dn (fs_data_of P dn).
Proof.
  intros Hok. apply dir_orphan_clean_live.
  pose proof (fio_nlink P sb dn Hok). lia.
Qed.

(* ====================================================================== *)
(*  F.  THE SLOT-TO-BLOCK-LIST BRIDGE                                      *)
(* ====================================================================== *)

(* [ipool_alloc]'s resources arrive keyed by BLOCK NUMBER, and the only
   per-inode block list the image layer owns is [FsImg.fs_inode_blocks]
   (W4's summand).  Nothing connects a nonzero SLOT to that list; this is
   it, generic in the block count, every case one [fio_*_zero]
   contrapositive.  ([FsImg.fs_inode_blocks_range] is the converse.) *)
Lemma img_slot_in_inode_blocks (P : Z -> list (bv 8)) (sb : fs_sb)
    (dn : dinode) (i : nat) :
  fs_inode_ok P sb dn -> (i <= FS_MAXFILE)%nat -> fs_slot P dn i <> 0 ->
  fs_slot P dn i ∈ fs_inode_blocks P dn.
Proof.
  intros Hok Hi Hnz.
  unfold fs_inode_blocks. cbv zeta.
  unfold fs_slot in Hnz |- *.
  destruct (decide (i = FS_MAXFILE)) as [->|Hne].
  - assert (Hgt : Z.of_nat FS_NDIRECT < fs_nblk (bv_unsigned (di_size dn))).
    { destruct (Z_le_gt_dec (fs_nblk (bv_unsigned (di_size dn)))
                  (Z.of_nat FS_NDIRECT)) as [Hle|Hgt]; [| lia].
      exfalso. apply Hnz. exact (fio_ind_zero P sb dn Hok Hle). }
    rewrite (proj2 (Z.ltb_lt _ _) Hgt).
    apply elem_of_app. left. apply elem_of_list_singleton. reflexivity.
  - unfold fs_blk_addr in Hnz |- *.
    destruct (Nat.ltb_spec i FS_NDIRECT) as [Hd|Hd].
    + assert (Hlt : Z.of_nat i < fs_nblk (bv_unsigned (di_size dn))).
      { destruct (Z_lt_ge_dec (Z.of_nat i)
                    (fs_nblk (bv_unsigned (di_size dn)))) as [H|H];
          [exact H |].
        exfalso. apply Hnz.
        exact (fio_direct_zero P sb dn Hok i Hd ltac:(lia)). }
      apply elem_of_app. right. apply elem_of_app. left.
      apply elem_of_list_fmap. exists i. split; [reflexivity |].
      assert (Hmin : Z.of_nat i < Z.min (fs_nblk (bv_unsigned (di_size dn)))
                                        (Z.of_nat FS_NDIRECT)).
      { apply Z.min_glb_lt; [exact Hlt |].
        unfold FS_NDIRECT in Hd |- *. lia. }
      apply elem_of_seq. split; [lia |]. rewrite Nat.add_0_l.
      apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. exact Hmin.
    + assert (Hj : (i - FS_NDIRECT < FS_NINDIRECT)%nat)
        by (unfold FS_MAXFILE, FS_NDIRECT, FS_NINDIRECT in *; lia).
      assert (Hlt : Z.of_nat (i - FS_NDIRECT)
                    < fs_nblk (bv_unsigned (di_size dn))
                      - Z.of_nat FS_NDIRECT).
      { destruct (Z_lt_ge_dec (Z.of_nat (i - FS_NDIRECT))
                    (fs_nblk (bv_unsigned (di_size dn))
                     - Z.of_nat FS_NDIRECT)) as [H|H]; [exact H |].
        exfalso. apply Hnz.
        exact (fio_ent_zero P sb dn Hok (i - FS_NDIRECT)%nat Hj ltac:(lia)). }
      apply elem_of_app. right. apply elem_of_app. right.
      apply elem_of_list_fmap. exists (i - FS_NDIRECT)%nat.
      split; [reflexivity |].
      apply elem_of_seq. split; [lia |]. rewrite Nat.add_0_l.
      apply Nat2Z.inj_lt. rewrite Z2Nat.id by lia. exact Hlt.
Qed.

(* ---------------------------------------------------------------------- *)
(*  from here down: ssreflect's [rewrite] (via proofmode), which rejects   *)
(*  both [rewrite a, b] and [rewrite a by tac] -- the style everything     *)
(*  above is written in.  Everything above is pure.                       *)
(* ---------------------------------------------------------------------- *)
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import iprop ghost_map.

(* proofmode re-opens [nat_scope] on top: [=?] and [<=] would silently
   become the nat ones. *)
Local Open Scope Z_scope.

(* ====================================================================== *)
(*  G.  THE RESOURCE HALF: block-granular ghosts -> [inode_blocks]         *)
(* ====================================================================== *)

Section ImageRes.
  Context `{!riscvGS Σ, !xv6G Σ}.

  (* [InodeInv.inode_blocks_of_blocks] AT AN IMAGE RECORD.  Still generic
     in the block count, in [P] and in the inode; the [∗ set] on the left
     is exactly the pair [FsBoot.fs_boot_ghosts] hands over for the blocks
     of ONE inode (which [FsBoot.big_sepS_carve] cuts out of [cov] using
     [FsImg.fs_inode_blocks_disjoint]).

     [ind_res]'s content half needs no premise beyond [fs_blocks_full]:
     [FsImg.fs_ind_bytes_round_trip] says the indirect block's bytes ARE
     [BlockWords.ind_bytes] of the entry list this [blkmap] carries. *)
  Lemma img_inode_blocks_res (γfs : fs_names) (P : Z -> list (bv 8))
      (sb : fs_sb) (dn : dinode) :
    dinode_wf dn -> fs_blocks_full P ->
    fs_inode_ok P sb dn -> fs_slot_inj P dn ->
    ([∗ set] b ∈ (list_to_set (fs_inode_blocks P dn) : gset Z),
       fsblock (fs_bytes γfs) b (P b) ∗ blk_own γfs b) -∗
    inode_blocks γfs (img_blkmap P dn) (fs_data_of P dn)
      ∗ ind_res γfs (img_blkmap P dn).
  Proof.
    intros Hwf Hfull Hok Hinj.
    apply (inode_blocks_of_blocks γfs (img_blkmap P dn)
             (list_to_set (fs_inode_blocks P dn)) P (fs_data_of P dn)).
    - intros i j Hi Hj Hnz Heq.
      rewrite maxfile_eq in Hi Hj.
      apply (Hinj i j Hi Hj).
      + rewrite -(img_blkmap_slot P dn i Hwf ltac:(rewrite maxfile_eq; exact Hi)).
        exact Hnz.
      + rewrite -(img_blkmap_slot P dn i Hwf
                     ltac:(rewrite maxfile_eq; exact Hi))
                -(img_blkmap_slot P dn j Hwf
                     ltac:(rewrite maxfile_eq; exact Hj)) Heq.
        reflexivity.
    - intros i Hi Hnz.
      rewrite (img_blkmap_slot P dn i Hwf Hi) in Hnz *.
      apply elem_of_list_to_set.
      rewrite maxfile_eq in Hi.
      exact (img_slot_in_inode_blocks P sb dn i Hok Hi Hnz).
    - intros i Hi Hnz.
      rewrite (img_blkmap_get P dn i Hwf Hi) in Hnz *.
      rewrite fs_data_of_addr.
      destruct (fs_blk_addr P dn i =? 0) eqn:E; [| reflexivity].
      exfalso. apply Hnz, Z.eqb_eq, E.
    - rewrite img_blkmap_ind. intros Hnz.
      exact (fs_ind_bytes_round_trip P dn Hfull Hnz).
  Qed.

End ImageRes.
