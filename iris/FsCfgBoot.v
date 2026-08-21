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
(* the four name records [fscfg] carries and this file must be able to spell *)
Require Import WpUart.         (* [uart_names]  *)
Require Import VirtioModel.    (* [disk_read]    *)
Require Import DiskPtsto.      (* [disk_names]  *)
Require Import BioDefs.        (* [bio_names]   *)
Require Import FsBlocks.
Require Import DinodeEnc.
Require Import DirView.
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
Require Import FsImg.
Require Import FsImgBridge.
Require Import FsCfg.          (* the record this file finally gives a value *)
Require Import Xv6G.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Local Open Scope Z_scope.

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
(*  [BitmapInv.bitmap_res] is three things, and boot has all three in the   *)
(*  coverage remainder: the pure [bitmap_ok] (W5 plus R4's data-region      *)
(*  corner), the bitmap block AT [bitmap_bytes used], and one               *)
(*  [fsblock]/[blk_own] pair per CLEAR bit below [size].                    *)
(*                                                                        *)
(*  [used] IS THE BLOCK'S OWN BIT SET ([FsImg.fs_bmap_set]) rather than     *)
(*  "the used set ∪ the metadata blocks": at the block's own bits the       *)
(*  byte-level equation is a theorem ([FsImg.bm_bytes_fs_bmap_set]) and no  *)
(*  new image sweep exists, where the reconstructed set would additionally  *)
(*  need the 6192 bits above [size] swept clear.  Nothing distinguishes     *)
(*  the two: [bitmap_ok] quantifies over [x < size] and [free_set]          *)
(*  intersects [seqZ 0 size].                                              *)
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
     [fsblock] halves [FsBoot.fs_boot_ghosts] mints ([fs_blocks dk b] at
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
     [fsblock] halves, and the log region's and block 1's go to fsinit.
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
    (* [ireg_alloc]'s payout, verbatim: the fragment at a live inum, the
       marker at a free one *)
    ([∗ set] z ∈ region_inums icfg_nib,
       ireg_out γi (mword_of_int z : mword 32) (fs_dinode P sb z)) -∗
    ([∗ set] z ∈ A, dir_links z (fs_dinode P sb z)
                      (fs_data_of P (fs_dinode P sb z))) -∗
    (* [fs_boot_ghosts]' two block big-ops, UNPAIRED as it hands them over,
       and cut down to [C] by the era fupd's own peels *)
    ([∗ set] b ∈ C, fsblock γfs b (P b)) -∗
    ([∗ set] b ∈ C, blk_own γfs b) -∗
    ipool γfs γi cov (sb_logstart sb) (region_inums icfg_nib)
      ∗ ([∗ set] b ∈ C ∖ fs_live_blocks P sb A,
           fsblock γfs b (P b) ∗ blk_own γfs b).
  Proof.
    iIntros (Hwf Hrf Hfull Hnin Hnib HA Hcov HcovC)
            "Hcnt Hmir Hoff Hdv Hout Hdlk Hfsb Hown".
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
    (* ---- the blocks: PAIRED ONCE, then carved ------------------------ *)
    iDestruct (big_sepS_sep_2 with "Hfsb Hown") as "Hblk".
    rewrite /fs_live_blocks.
    iDestruct (big_sepS_carve
                 (fun b => fsblock γfs b (P b) ∗ blk_own γfs b)%I
                 C (elements A) (fs_inode_blocks_set P sb)
                 (NoDup_elements A) Hsub Hdisj with "Hblk") as "[Hpc Hrem]".
    iSplitR "Hrem"; [| iExact "Hrem"].
    iDestruct (big_sepS_of_elements
                 (fun i => [∗ set] b ∈ fs_inode_blocks_set P sb i,
                             (fsblock γfs b (P b) ∗ blk_own γfs b))%I A
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
    (* ---- the allocated arm, one named application per inum ----------- *)
    iDestruct (big_sepS_sep_2 with "HoutA Hdlk") as "Ha".
    iDestruct (big_sepS_sep_2 with "Ha Hpc") as "Ha".
    iDestruct (big_sepS_sep_2 with "Ha HdvA") as "Ha".
    iApply (ipool_alloc γfs γi cov (sb_logstart sb)
              (region_inums icfg_nib) A HARs
              with "Hcnt Hmir Hoff [Ha] Hmk HdvF").
    iApply (big_sepS_mono with "Ha"). intros z Hz.
    rewrite (region_inum_faithful icfg_nib z Hnib (HAR z Hz)).
    rewrite /fs_inode_blocks_set.
    iIntros "[[[Hreg Hdl] Hblks] Hdv]".
    iExists (fs_dinode P sb z), (img_blkmap P (fs_dinode P sb z)),
            (fs_data_of P (fs_dinode P sb z)).
    iSplitR.
    { iPureIntro.
      exact (img_inode_ok P sb cov (sb_logstart sb) (fs_dinode P sb z)
               (fs_dinode_wf P sb z) Hsb eq_refl Hfull Hcov
               (Hok z Hz) (Hty z Hz) (Hinj z Hz)). }
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
    iSplitL "Hblks"; [iExact "Hblks" | iExact "Hdv"].
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
    /\ image_dir_wl0 (fs_link_count P sb) dss nib
    /\ image_root_alive (fs_link_count P sb) dss nib.
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
    split.
    { intros z Hz Hty. rewrite (Hbr z Hz) in Hty.
      apply (fsimg_wf_link_dir P sb z Hwf).
      (* [InodeRegion.ireg_dir_ty] and [DirView.T_DIR_z] are the same 1 *)
      rewrite Hty. reflexivity. }
    { intros z Hz Hroot.
      destruct (fsimg_wf_root_link P sb Hwf) as [Hc Hnl].
      assert (Hz1 : z = ROOTINO) by (rewrite Hroot; reflexivity).
      rewrite (Hbr z Hz) Hz1 Hnl Hc. lia. }
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
    length dss = nib -> Forall diblk_wf dss ->
    (forall bi : nat, (bi < nib)%nat ->
       P (FsImg.sb_inodestart sb + Z.of_nat bi) = diblk_bytes (dss !!! bi)) ->
    16 * Z.of_nat nib <= 2 ^ 32 ->
    image_free_nlink dss nib /\ image_nlink_short dss nib /\
    image_root_alive (fs_link_count P sb) dss nib /\
    image_link_le (fs_link_count P sb) dss nib
    /\ image_dir_wl0 (fs_link_count P sb) dss nib.
  Proof.
    intros Hwf Hrw Hl Hdwf He Hnib.
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
    (* [image_link_premises] lists them in ITS order; [ireg_alloc]'s slot
       wants root-alive first. *)
    destruct (image_link_premises P sb dss nib Hwf Hl Hdwf He Hnib)
      as (Hle & Hw0 & Hrt).
    split; [exact Hrt |]. split; [exact Hle | exact Hw0].
  Qed.

End FsCfgBootPool.

(* ====================================================================== *)
(*  THE INODE REGION'S BLOCKS, AS A SET                                    *)
(* ====================================================================== *)

(*  [IcacheBoot.ireg_alloc] wants the region's [fsblock] halves as a
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

  (*  DEBT (D) PAID.  The whole of [BitmapInv.bitmap_res], out of the paired
      remainder the stocking carve leaves and nothing else: no new image
      sweep, and the era fupd still computes nothing.  The bitmap block's
      own [blk_own] is dropped -- [bitmap_res] does not hold one for it, and
      nothing may: the block is the invariant's own storage, not a client
      block. *)
  Lemma bitmap_res_of_image (γfs : fs_names) (P : Z -> list (bv 8))
      (sb : fs_sb) (cov : gset Z) :
    fsimg_wf P sb = true ->
    fs_blocks_full P ->
    (forall b : Z, fs_data_start sb <= b < FsImg.sb_size sb -> b ∈ cov) ->
    ([∗ set] b ∈ fs_bitmap_spent P sb,
       fsblock γfs b (P b) ∗ blk_own γfs b) -∗
    bitmap_res γfs (FsImg.sb_bmapstart sb) cov (FsImg.sb_logstart sb)
      (FsImg.sb_size sb) (FsImg.fs_bmap_set BSIZE (P (FsImg.sb_bmapstart sb))).
  Proof.
    intros Hwf Hfull Hcovd. iIntros "H".
    pose proof (fsimg_wf_sb P sb Hwf) as Hsb.
    destruct (fsimg_wf_used P sb Hwf) as (u & _ & _ & Hbw).
    pose proof (fs_sb_ok_meta sb Hsb) as (Hm1 & Hm2 & Hm3).
    (* the log region sits strictly below the inode region, hence strictly
       below every block the pool or the bitmap block occupies *)
    assert (HlogI : forall z : Z, z ∈ log_region_set (FsImg.sb_logstart sb) ->
              1 < z < FsImg.sb_inodestart sb).
    { intros z Hz. pose proof (log_region_bound (FsImg.sb_logstart sb) z Hz).
      pose proof (sbo_logstart sb Hsb). pose proof (sbo_nlog sb Hsb).
      pose proof (sbo_inodestart sb Hsb). unfold LOGBLOCKS in *. lia. }
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
    (* ...and the pure half *)
    assert (Hok : bitmap_ok cov (FsImg.sb_logstart sb) (FsImg.sb_size sb)
                            (FsImg.fs_bmap_set BSIZE
                               (P (FsImg.sb_bmapstart sb)))).
    { intros x Hx Hnu.
      destruct (fs_bmap_set_free P sb u x Hsb Hbw Hx Hnu) as [Hge _].
      split; [apply Hcovd; lia |].
      intros Hlog. pose proof (HlogI x Hlog). lia. }
    rewrite /fs_bitmap_spent (big_sepS_union _ _ _ Hdj) big_sepS_singleton.
    iDestruct "H" as "[[Hbm _] Hpool]".
    rewrite /bitmap_res Hbytes.
    iSplitR; [iPureIntro; exact Hok |].
    iSplitL "Hbm"; [iExact "Hbm" |].
    rewrite /free_pool.
    iApply (big_sepS_mono with "Hpool"). intros b Hb.
    iIntros "[Hf Ho]".
    iApply (free_blk_intro γfs b (P b) (Hfull b) with "Hf Ho").
  Qed.

End FsCfgBootBitmap.


(* ====================================================================== *)
(*  THE TWO BOOT KITS (ruling R6), GHOST ROWS ONLY                         *)
(* ====================================================================== *)

Section FsCfgBootEra.
  Context `{!riscvGS Σ, !xv6G Σ, !bioslotG Σ, !irefslotG Σ}.
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
             name and cpu cells, the thirty [sl_fresh (buf_lock (bnode k))]
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
     ipool fsc_fs fsc_ireg fsc_cov fsc_logst (region_inums icfg_nib) ∗
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
     kmem_avail_auth fsc_kpages 0%nat)%I.

  Lemma fs_kit_icache_open (ICFG : icfg) (FSC : fscfg) :
    fs_kit_icache ICFG FSC -∗
      own icfg_iref (● (∅ : gmap nat (Qp * positive)) : icacheUR) ∗
      ([∗ list] k ∈ seq 0 (NINODE + NINODE), live_frac k 1%Qp) ∗
      ([∗ list] k ∈ seq 0 NINODE,
         sl_free_tok (icfg_isl k) ∗ slh_auth (icfg_isl k) None) ∗
      ipool fsc_fs fsc_ireg fsc_cov fsc_logst (region_inums icfg_nib) ∗
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
      kmem_avail_auth fsc_kpages 0%nat.
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
        (B) [LogDefs.log_mirror_full].  Producer:
            [BootShared.boot_shared_alloc] -- it is the ERA's mirror
            variable ([RiscvPtsto.mirror_name] = [era_mirror_name
            riscv_eraGS], minted by [RiscvAdequacy] at power-on and handed
            through [power_boot_res] at BootShared.v:874/1020), so this fupd
            cannot mint it and must not try to.
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
     fsblock fsc_fs 1 (P 1) ∗
     (* initlog's FsBlocks material.  [L]/[D] are universally quantified in
        [SpecFsinit]'s contract, so an existential here is exactly right. *)
     (∃ (L : gmap Z (list (bv 8))) (D : gmap Z bool),
        ghost_map_auth (fs_L fsc_fs) 1 L ∗
        ghost_map_auth (fs_dirty fsc_fs) 1 D) ∗
     ([∗ set] z ∈ fsc_cov, z ↪[fs_dirty fsc_fs]{#(1/2)} false) ∗
     (* the log region, split as [initlog] wants it *)
     fsblock fsc_fs (log_hdr_bno fsc_logst) (P (log_hdr_bno fsc_logst)) ∗
     ([∗ list] i ∈ seq 0 LOGBLOCKS,
        ∃ bs : list (bv 8), fsblock fsc_fs (log_slot_bno fsc_logst i) bs) ∗
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
        fsblock fsc_fs b (P b) ∗ blk_own fsc_fs b))%I.

  Lemma fs_kit_fsinit_ghost_open (ICFG : icfg) (FSC : fscfg)
      (P : Z -> list (bv 8)) (Rspent : gset Z) :
    fs_kit_fsinit_ghost ICFG FSC P Rspent -∗
      log_free_tok icfg_log ∗
      ireg_boot ∗
      ireg_inv fsc_ireg fsc_fs icfg_ist icfg_nib ∗
      fsblock fsc_fs 1 (P 1) ∗
      (∃ (L : gmap Z (list (bv 8))) (D : gmap Z bool),
         ghost_map_auth (fs_L fsc_fs) 1 L ∗
         ghost_map_auth (fs_dirty fsc_fs) 1 D) ∗
      ([∗ set] z ∈ fsc_cov, z ↪[fs_dirty fsc_fs]{#(1/2)} false) ∗
      fsblock fsc_fs (log_hdr_bno fsc_logst) (P (log_hdr_bno fsc_logst)) ∗
      ([∗ list] i ∈ seq 0 LOGBLOCKS,
         ∃ bs : list (bv 8), fsblock fsc_fs (log_slot_bno fsc_logst i) bs) ∗
      bitmap_inv fsc_fs fsc_bmapstart fsc_cov fsc_logst fsc_size ∗
      ([∗ set] b ∈ fsc_cov ∖ Rspent,
         fsblock fsc_fs b (P b) ∗ blk_own fsc_fs b).
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
     ipool fsc_fs fsc_ireg fsc_cov fsc_logst (region_inums icfg_nib) ∗
     lock_free_tok fsc_itlock ∗
     ([∗ list] k ∈ seq 0 NINODE, ic_tok fsc_ic k) ∗
     ([∗ list] k ∈ seq 0 NINODE, ic_mid fsc_ic k) ∗
     ([∗ list] k ∈ seq 0 NINODE,
        ∃ (v : bool) (d n : mword 32), ic_id fsc_ic k 1 v d n) ∗
     bio_free_tok fsc_bio ∗
     ([∗ set] b ∈ fsc_cov,
        pool_blk (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) b) ∗
     lock_free_tok fsc_dlock)%I.

  Lemma fs_kit_icache_split (ICFG : icfg) (FSC : fscfg) :
    fs_kit_icache ICFG FSC -∗
      fs_kit_printk ICFG FSC ∗ fs_kit_kalloc ICFG FSC ∗
      fs_kit_icache_rest ICFG FSC.
  Proof.
    iIntros "H".
    iDestruct (fs_kit_icache_open with "H")
      as "(Hiref & Hlive & Hislg & Hipool & Hitlk & Htok & Hmid & Hgid &
           Hbio & Hpool & Hkmlk & Hdllk & Hprlk & Hkav & Hkauth)".
    rewrite /fs_kit_printk /fs_kit_kalloc /fs_kit_icache_rest.
    iFrame "Hprlk Hkmlk Hkav Hkauth Hiref Hlive Hislg Hipool Hitlk Htok
            Hmid Hgid Hbio Hpool Hdllk".
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
      ipool fsc_fs fsc_ireg fsc_cov fsc_logst (region_inums icfg_nib) ∗
      lock_free_tok fsc_itlock ∗
      ([∗ list] k ∈ seq 0 NINODE, ic_tok fsc_ic k) ∗
      ([∗ list] k ∈ seq 0 NINODE, ic_mid fsc_ic k) ∗
      ([∗ list] k ∈ seq 0 NINODE,
         ∃ (v : bool) (d n : mword 32), ic_id fsc_ic k 1 v d n) ∗
      bio_free_tok fsc_bio ∗
      ([∗ set] b ∈ fsc_cov,
         pool_blk (fs_view fsc_fs fsc_disk icfg_dev fsc_cov) b) ∗
      lock_free_tok fsc_dlock.
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
  Lemma fs_cfg_alloc (γd : uart_names) (γv : disk_names)
      (dk : Z -> bv 8) (ndisk : nat) (sb : fs_sb) (cov : gset Z)
      (nib : nat) (E : coPset) :
    (* ---- the image, all as hypotheses (R3) ---- *)
    fsimg_wf (fs_blocks dk) sb = true ->
    fs_region_wf (fs_blocks dk) sb nib = true ->
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
    (* ---- N-5.1 (W5a): THE BOOT MINT'S MASK ----
       The stocking mint below fires [InodeRegion.dv_lend_mint], which opens
       the inode region.  [ireg_alloc] allocates [iregN] a few lines EARLIER
       in the same chain, so the handle exists; what the era fupd did not
       say before is that its own mask can hold the region's namespace.  The
       one caller ([BootShared.boot_shared_alloc]) runs this at [⊤]. *)
    ↑iregN ⊆ E ->
    disk_bytes γv 0 (disk_read dk 0 ndisk) -∗
    (* THE BIO SLOT SUPPLY, THREADED IN.  Its ghost name is canonical
       ([Xv6Cameras.bioslot_name]), so it exists before this era fupd runs
       and [BioDefs.bslots_alloc] is what mints it -- one layer up, beside
       the other name-carrying classes.  Both halves come in because
       [BioInitAt.bio_free_tok] carries both. *)
    bslots_auth -∗ bslots BSLOTS_FS ={E}=∗
    ∃ (ICFG : icfg) (FSC : fscfg),
      (* ---- N-5.1 (W5a): ROOT'S PIN, THE ONE NEW CONJUNCT ----
         The stocking spends [ROOTINO]'s mint licence while it still holds
         the root directory's contents element WHOLE, so the pin leaves boot
         naming the IMAGE's root contents.  It is the first conjunct rather
         than the last so that a caller with no consumer drops it in one
         step and the ten ties + two kits below stay byte-identical to
         [fs_boot_supply].  Its client is [NameiInitPinned.v], which turns
         it into [DirViewPin.dv_pin_ent] at [("init", 7)]. *)
      dv_pin (bv_unsigned InodeInv.ROOTINO)
        (dv_of (fs_dinode (fs_blocks dk) sb (bv_unsigned InodeInv.ROOTINO))
               (fs_data_of (fs_blocks dk)
                  (fs_dinode (fs_blocks dk) sb
                     (bv_unsigned InodeInv.ROOTINO)))) ∗
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
    intros Hwf Hrw Hnin Hnib32 Hnib0 Hnibeq Hcovin Hcovmeta Hcovdata HiregE.
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
            γlog (FsImg.sb_inodestart sb)
            (link_boot_map_valid _) (icnt_boot_map_valid _)
            (frzo_boot_map_valid _) (frzm_boot_map_valid _)
            (dview_boot_map_valid _))
      as (ICFG g0) "(%Hdev & %Hnibq & %Hlogq & %Histq & Hiref & Hlive &
                     Hlk & Hcnt & Hfrzo & Hfrzm & Hdv & Hboot & Hep & Hisl &
                     Hrauth)".
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
    iDestruct (region_of_seq (fun z => mono_nat_auth_own (icfg_iep z) 1 0)
                 icfg_nib with "Hep") as "Hep".
    iDestruct (live_boot_split g0 with "Hlive") as "Hlive".
    (* ---- 4. the block layer's ghosts -------------------------------- *)
    iMod (fs_boot_ghosts γv dk ndisk cov ROOTDEV E Hcovin with "Hdisk")
      as (γfs) "(Hpool & HaL & HaD & Hdty & Hfsb & Hown)".
    (* ---- 5. THE THREE PEELS ----------------------------------------- *)
    iDestruct (big_sepS_sep_2 with "Hfsb Hown") as "Hblk".
    iDestruct (big_sepS_split_sub _ cov ({[ (1:Z) ]} : gset Z) H1cov
                 with "Hblk") as "[Hb1 Hblk]".
    iDestruct (big_sepS_split_sub _ _ (log_region_set (sb_logstart sb))
                 Hlogcov with "Hblk") as "[Hblog Hblk]".
    iDestruct (big_sepS_split_sub _ _
                 (ireg_blk_set (FsImg.sb_inodestart sb) icfg_nib)
                 Hiregcov with "Hblk") as "[Hbireg Hblk]".
    iEval (rewrite big_sepS_singleton) in "Hb1".
    iDestruct "Hb1" as "[Hb1 _]".
    iEval (rewrite big_sepS_sep) in "Hblog".
    iDestruct "Hblog" as "[Hblog _]".
    iDestruct (fs_log_region_split γfs dk (sb_logstart sb) with "Hblog")
      as "[Hhdr Hslots]".
    iEval (rewrite big_sepS_sep) in "Hbireg".
    iDestruct "Hbireg" as "[Hbireg _]".
    iDestruct (ireg_blk_of_set (fun b => fsblock γfs b (fs_blocks dk b))
                 (FsImg.sb_inodestart sb) icfg_nib with "Hbireg")
      as "Hbireg".
    iEval (rewrite big_sepS_sep) in "Hblk".
    iDestruct "Hblk" as "[HfsbC HownC]".
    (* ---- 6. THE INODE REGION ---------------------------------------- *)
    iAssert (ireg_boot) with "[Hboot]" as "Hboot".
    { rewrite /ireg_boot /ity_pending. iExact "Hboot". }
    iMod (ireg_alloc E γfs (FsImg.sb_inodestart sb) icfg_nib
            (fun bi : nat =>
               fs_blocks dk (FsImg.sb_inodestart sb + Z.of_nat bi))
            (fs_link_count (fs_blocks dk) sb) Hnib32 eq_refl
            ltac:(intros bi _; rewrite fs_blocks_length; reflexivity)
            ltac:(intros dss Hdl Hdwf Hde;
                  exact (image_ireg_premises (fs_blocks dk) sb dss icfg_nib
                           Hwf Hrw Hdl Hdwf Hde Hnib32))
            with "Hla HcntR Hrcpt HmirR Hep Hbireg Hboot Hrauth")
      as (γi dss) "(%Hdl & %Hdwf & %Hde & Hireginv & Hboot & Hlics & Hout)".
    iDestruct "Hireginv" as "#Hireginv".
    (* ================================================================== *)
    (* ---- N-5.1 (W5a): THE BOOT MINT -------------------------------- *)
    (* [ireg_alloc] has just stocked the lend column NONE at every inum and
       paid out the per-inum MINT LICENCES; the stocking still holds every
       directory's contents element WHOLE (the sweep above stopped at
       [dv_hold] for exactly this).  So this is the one instant at which
       root's lend can be cut: spend [ROOTINO]'s licence here, park the ¾
       ride arm on the custody chain from now on, and carry the pin out with
       the era fupd's post.
       ORDER, checked: [ireg_inv] and the licences BOTH arrive from the line
       above, and the pool ([ipool_alloc_of_image]) has not run yet, so the
       ride the pool parks is already the post-mint one -- nothing has to be
       renegotiated downstream.  Every OTHER inum's licence is dropped: no
       consumer, and the licence is affine.  (A runtime mint window is
       future work; see namei-pinned-lookup.md §11.5.) *)
    assert (Hrz : bv_unsigned InodeInv.ROOTINO = 1)
      by (vm_compute; reflexivity).
    assert (Hrootin : bv_unsigned InodeInv.ROOTINO ∈ region_inums icfg_nib)
      by (apply region_inums_spec; rewrite Hrz; lia).
    assert (Hrootdom : dvl_dom (bv_unsigned InodeInv.ROOTINO))
      by (rewrite /dvl_dom Hrz; lia).
    iDestruct (big_sepS_delete _ _ _ Hrootin with "Hlics") as "[Hlicr Hlics]".
    iClear "Hlics".
    iDestruct (big_sepS_delete _ _ _ Hrootin with "Hdv") as "[Hdvr Hdv]".
    iMod (dv_lend_mint E γi γfs (FsImg.sb_inodestart sb) icfg_nib
            (bv_unsigned InodeInv.ROOTINO)
            (dv_of (fs_dinode (fs_blocks dk) sb (bv_unsigned InodeInv.ROOTINO))
                   (fs_data_of (fs_blocks dk)
                      (fs_dinode (fs_blocks dk) sb
                         (bv_unsigned InodeInv.ROOTINO))))
            HiregE Hrootdom
            with "Hireginv Hlicr Hdvr") as "[Hrider Hpinr]".
    (* the custody chain, back as ONE big-op: the ¾ arm at root, the whole
       arm everywhere else *)
    iAssert ([∗ set] z ∈ region_inums icfg_nib,
               dv_ride z (dv_of (fs_dinode (fs_blocks dk) sb z)
                            (fs_data_of (fs_blocks dk)
                               (fs_dinode (fs_blocks dk) sb z))))%I
      with "[Hdv Hrider]" as "Hdv".
    { rewrite (big_sepS_delete _ (region_inums icfg_nib)
                 (bv_unsigned InodeInv.ROOTINO) Hrootin).
      iSplitL "Hrider"; [rewrite /dv_ride; iRight; iExact "Hrider" |].
      iApply (big_sepS_mono with "Hdv"). intros z _. iIntros "H".
      iApply (dv_ride_of_hold with "H"). }
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
    iDestruct (ipool_alloc_of_image γfs γi (fs_blocks dk) sb cov
                 (((cov ∖ ({[ (1:Z) ]} : gset Z))
                     ∖ log_region_set (sb_logstart sb))
                    ∖ ireg_blk_set (FsImg.sb_inodestart sb) icfg_nib)
                 (fs_live_set (fs_blocks dk) sb)
                 Hwf (fs_region_wf_free _ _ _ Hrw) Hfull Hnin Hnib32
                 (fs_live_set_elem_of (fs_blocks dk) sb) Hcovdata HcovC
                 with "HcntP HmirP Hoff Hdv Hout Hdlk HfsbC HownC")
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
                 (fun b => fsblock γfs b (fs_blocks dk b) ∗ blk_own γfs b)%I
                 _ (fs_bitmap_spent (fs_blocks dk) sb) Hbmsub with "Hrem")
      as "[Hbmspent Hrem]".
    iDestruct (bitmap_res_of_image γfs (fs_blocks dk) sb cov Hwf Hfull
                 Hcovdata with "Hbmspent") as "Hbmres".
    iMod (bitmap_inv_alloc E with "Hbmres") as "#Hbmres".
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
      rewrite !elem_of_difference !elem_of_union. tauto. }
    rewrite Hset.
    (* ---- N-5.1 (W5a): root's pin, the post's first conjunct ---- *)
    iSplitL "Hpinr"; [iExact "Hpinr" |].
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
    iSplitL "Hiref Hlive Hisl Hipool Hitlk Htok Hmid Hgid Hbio Hpool
             Hkmlk Hdllk Hprlk Hkav Hkauth".
    { iSplitL "Hiref"; [iExact "Hiref" |].
      iSplitL "Hlive"; [iExact "Hlive" |].
      iSplitL "Hisl"; [iExact "Hisl" |].
      iSplitL "Hipool"; [iExact "Hipool" |].
      iSplitL "Hitlk"; [iExact "Hitlk" |].
      iSplitL "Htok"; [iExact "Htok" |].
      iSplitL "Hmid"; [iExact "Hmid" |].
      iSplitL "Hgid"; [iExact "Hgid" |].
      iSplitL "Hbio"; [iExact "Hbio" |].
      iSplitL "Hpool"; [iExact "Hpool" |].
      iSplitL "Hkmlk"; [iExact "Hkmlk" |].
      iSplitL "Hdllk"; [iExact "Hdllk" |].
      iSplitL "Hprlk"; [iExact "Hprlk" |].
      iSplitL "Hkav"; [iExact "Hkav" | iExact "Hkauth"]. }
    (* ---- kit 2 ---- *)
    iSplitL "Hlogtok"; [iExact "Hlogtok" |].
    iSplitL "Hboot"; [iExact "Hboot" |].
    (* [ireg_inv] is persistent and was moved to the intuitionistic context
       at the boot mint (W5a), so this row is an [iSplitR] now. *)
    iSplitR; [iExact "Hireginv" |].
    iSplitL "Hb1"; [iExact "Hb1" |].
    iSplitL "HaL HaD".
    { iExists (fs_L0 dk cov), (fs_D0 dk cov).
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
  /\ Z.of_nat ndisk <= 1024 * FsImg.sb_size sb.

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
