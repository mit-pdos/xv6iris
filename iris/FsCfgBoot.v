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

End FsCfgBootPool.
