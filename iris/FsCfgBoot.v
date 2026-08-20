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
(* as a HYPOTHESIS (ruling R3): [FsImg]'s eight boolean sweeps are         *)
(* instantiated at the literal image in [FsImgCheck.v] (~212 s of          *)
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
From iris.base_logic.lib Require Import invariants own ghost_map ghost_var.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto RiscvModelBytes.
Require Import FsBlocks.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import DirView.
Require Import DirLinks.
Require Import FsTree.
Require Import FsCrash.
Require Import LogInv.
Require Import InodeInv.
Require Import InodeLock.
Require Import InodeRegion.
Require Import IrefSlots.
Require Import IcacheInv.
Require Import IcacheEscrow.
Require Import IcacheBoot.
Require Import FsBoot.
Require Import FsImg.
Require Import FsImgBridge.
Require Import Xv6G.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

Local Open Scope Z_scope.

(* THE BLOCKS THE LIVE INODES BETWEEN THEM CLAIM.  The carve's own
   spelling, so the remainder [cov ∖ fs_live_blocks P sb A] -- which
   carries the log region, the inode region, the bitmap block and the free
   pool onward to [bio_init]/[initlog]/[ireg_alloc] -- is statable. *)
Definition fs_live_blocks (P : Z -> list (bv 8)) (sb : fs_sb) (A : gset Z)
  : gset Z := ⋃ (fs_inode_blocks_set P sb <$> elements A).

Section FsCfgBootPool.
  Context `{!riscvGS Σ, !xv6G Σ, ICFG : icfg, !irefslotG Σ}.
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
  Lemma ipool_alloc_of_image (γfs : fs_names) (γi : gname)
      (P : Z -> list (bv 8)) (sb : fs_sb) (cov A : gset Z) :
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
    (* the three uncached ledger columns, at [IcacheRef]'s boot splits' own
       keys (plain [Z] over the region; [region_key_shift] is the bridge to
       the pool's [mword] round trip) *)
    ([∗ set] z ∈ region_inums icfg_nib, icnt_half z 0%nat) -∗
    ([∗ set] z ∈ region_inums icfg_nib, frzm_h z false) -∗
    ([∗ set] z ∈ region_inums icfg_nib, ifreeze_off z) -∗
    (* [ireg_alloc]'s payout, verbatim: the fragment at a live inum, the
       marker at a free one *)
    ([∗ set] z ∈ region_inums icfg_nib,
       ireg_out γi (mword_of_int z : mword 32) (fs_dinode P sb z)) -∗
    ([∗ set] z ∈ A, dir_links z (fs_dinode P sb z)
                      (fs_data_of P (fs_dinode P sb z))) -∗
    (* [fs_boot_ghosts]' two block big-ops, UNPAIRED as it hands them over *)
    ([∗ set] b ∈ cov, fsblock γfs b (P b)) -∗
    ([∗ set] b ∈ cov, blk_own γfs b) -∗
    ipool γfs γi cov (sb_logstart sb) (region_inums icfg_nib)
      ∗ ([∗ set] b ∈ cov ∖ fs_live_blocks P sb A,
           fsblock γfs b (P b) ∗ blk_own γfs b).
  Proof.
    iIntros (Hwf Hrf Hfull Hnin Hnib HA Hcov)
            "Hcnt Hmir Hoff Hout Hdlk Hfsb Hown".
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
              fs_inode_blocks_set P sb i ⊆ cov).
    { intros i Hi. apply elem_of_elements in Hi.
      exact (fs_inode_blocks_set_sub P sb i cov (Hok i Hi) Hcov). }
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
                 cov (elements A) (fs_inode_blocks_set P sb)
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
    (* ---- the allocated arm, one named application per inum ----------- *)
    iDestruct (big_sepS_sep_2 with "HoutA Hdlk") as "Ha".
    iDestruct (big_sepS_sep_2 with "Ha Hpc") as "Ha".
    iApply (ipool_alloc γfs γi cov (sb_logstart sb)
              (region_inums icfg_nib) A HARs
              with "Hcnt Hmir Hoff [Ha] Hmk").
    iApply (big_sepS_mono with "Ha"). intros z Hz.
    rewrite (region_inum_faithful icfg_nib z Hnib (HAR z Hz)).
    rewrite /fs_inode_blocks_set.
    iIntros "[[Hreg Hdl] Hblks]".
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
    iSplitL "Hind"; [iExact "Hind" | iExact "Hblks"].
  Qed.

End FsCfgBootPool.
