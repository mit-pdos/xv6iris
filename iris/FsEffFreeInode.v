(* FsEffFreeInode.v -- durable-disk stage F2, effect 7: freeing an
   orphan inode (iput's reclaim, fused with its truncation). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import RiscvModelBytes.
Require Import BioDefs.
Require Import DirentEnc.
Require Import DinodeEnc.
Require Import BitmapEnc.
Require Import InodeDefs.
Require Import DirView.
Require Import FsTree.
Require Import FsImg.
Require Import FsWf.
Require Import FsEffBase.

Local Open Scope Z_scope.

Section EffFreeInode.
  Context (P : Z -> list (bv 8)) (sb : fs_sb).
  Context (Hp : fs_parse_sb P = Some sb).
  Context (Hsb : fs_sb_wf sb = true).
  Context (HW3 : fs_inodes_dwf P sb = true).
  Context (u : gset Z) (Hu : fs_used_set P sb = Some u).
  Context (Hbm : fs_bitmap_wf P sb u = true).
  Context (HW7 : fs_root_wf P sb = true).
  Context (HW8 : fs_dots_all P sb = true).
  Context (nib : nat) (Hnibz : Z.of_nat nib = sb_ninodes sb / 16 + 1).
  Context (Hreg : fs_region_wf P sb nib = true).
  Context (rd : gset Z) (Hrd : fs_rdirs P sb rd).
  Context (Hdok : forall z : Z, z ∈ rd ->
              fs_dir_ok P sb z (fs_dinode P sb z)).
  Context (Hlkg : fs_links_gen P sb rd).
  Context (Horph : fs_orphans_empty P sb rd).

  Set Default Proof Using "All".

  Let Hok : fs_sb_ok sb := fs_sb_wf_ok sb Hsb.
  Let t : fstree := tree_of_disk P sb.

  Local Notation Hnib16 := (Hnib16 P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation Hnin_le := (Hnin_le P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation Hnin1 := (Hnin1 P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation Hnd := (Hnd P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation dok_at := (dok_at P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation used_elem := (used_elem P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation blocks_range := (blocks_range P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation blocks_cross := (blocks_cross P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation slot_inj_at := (slot_inj_at P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation fs_slot_blk := (fs_slot_blk P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation inode_untouched := (inode_untouched P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation node_at_untouched := (node_at_untouched P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation tickets_at_untouched := (tickets_at_untouched P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation tree_ent_char := (tree_ent_char P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation rd_record_step := (rd_record_step P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation rd_iff := (rd_iff P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation root_in_rd := (root_in_rd P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation rtick_of_record := (rtick_of_record P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation dwf_bool_at := (dwf_bool_at P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation dots_bool_at := (dots_bool_at P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation fs_nblk_gt := (fs_nblk_gt P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation blk_addr_covered := (blk_addr_covered P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation tree_ent_nondir := (tree_ent_nondir P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation tree_ent_untouched := (tree_ent_untouched P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation dir_ok_untouched := (dir_ok_untouched P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation dots_only_untouched := (dots_only_untouched P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation root_wf_untouched := (root_wf_untouched P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation reach_iff_of_ent := (reach_iff_of_ent P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation elem_mjoin_seq := (elem_mjoin_seq P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation NoDup_mjoin_sub := (NoDup_mjoin_sub P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation mjoin_seq_split := (mjoin_seq_split P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation old_bit_iff := (old_bit_iff P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation bitmap_wf_of_set := (bitmap_wf_of_set P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation used_drop := (used_drop P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation rtick_inv := (rtick_inv P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation rtick_unreachable := (rtick_unreachable P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation rtick_free := (rtick_free P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation zeroed_ind_ents := (zeroed_ind_ents P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation zeroed_blocks_nil := (zeroed_blocks_nil P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation zeroed_dwf := (zeroed_dwf P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation fs_nblk_between := (fs_nblk_between P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation dirent_written := (dirent_written P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation dirent_zeroed := (dirent_zeroed P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation tick_omap_write := (tick_omap_write P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation tree_ent_dir_eq := (tree_ent_dir_eq P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation root_wf_intro := (root_wf_intro P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation dots_flat := (dots_flat P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).

  (* THE INODE-REGION BOUND that every [Hdec] case split asks for.  Written
     inline as [ltac:(lia)] it is a general-purpose closer at a ~180-
     hypothesis site whose goal carries a division: 2-4 s PER SITE, and
     there are dozens.  [match goal] finds the range hypothesis whatever it
     is called there and hands the answer over as a term; the [lia] arm is
     the fallback for the few sites that have no such hypothesis. *)
  Local Ltac irng :=
    match goal with
    | H : 0 <= ?z < sb_ninodes sb |- 0 <= ?z < _ =>
        exact (iblk_z_range sb z H)
    | H : 0 < ?z < sb_ninodes sb |- 0 <= ?z < _ =>
        exact (iblk_z_range sb z
                 (conj (Z.lt_le_incl _ _ (proj1 H)) (proj2 H)))
    | _ => lia
    end.

  (* ==================================================================== *)
  (*  16.  EFFECT 7 -- FREEING AN ORPHAN INODE                             *)
  (*                                                                       *)
  (*  iput's reclaim, fused with its truncation (a directory must lose     *)
  (*  its dots and its type IN ONE effect: a typed dir without dots, or    *)
  (*  a dotted dir of size zero, violates W8 -- there is no wf state       *)
  (*  between).  The freed blocks' bits clear in the same step.            *)
  (* ==================================================================== *)

  Definition eff_free_inode (i : Z) : Z -> list (bv 8) :=
    fs_upd (eff_dinode P sb i (di_free_v (fs_dinode P sb i)))
      (sb_bmapstart sb)
      (bm_bytes BSIZE
         (fs_bmap_set BSIZE (P (sb_bmapstart sb))
          ∖ list_to_set (fs_inode_blocks P (fs_dinode P sb i)))).

  Lemma eff_free_inode_wf (i : Z) :
    0 <= i < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
    ~ fs_reachable P sb i ->
    fs_durable_wf_view (eff_free_inode i).
  Proof.
    intros Hi Hlive Hunreach.
    set (dn := fs_dinode P sb i) in *.
    set (dn' := di_free_v dn).
    set (P' := eff_free_inode i).
    assert (Htype' : bv_unsigned (di_type dn') = 0).
    { unfold dn'. cbn [di_type di_free_v].
      change (bv_unsigned (bv_0 16)) with 0. reflexivity. }
    assert (Haddrs' : di_addrs dn' = replicate 13 (bv_0 32)) by reflexivity.
    assert (Hnlink' : di_nlink dn' = di_nlink dn) by reflexivity.
    assert (Hsize' : di_size dn' = bv_0 32) by reflexivity.
    assert (Hwf' : dinode_wf dn') by (apply di_free_v_wf).
    destruct (fs_sb_ok_meta sb Hok) as (Hm1 & Hm2 & Hm3).
    pose proof Hnin_le as HninN.
    assert (HiN : 0 <= i < 16 * (sb_ninodes sb / 16 + 1)) by lia.
    destruct (iblock_bounds sb Hok i HiN) as (Hib1 & Hib2 & Hib3).
    assert (Hiroot : i <> ROOTINO).
    { intros ->. apply Hunreach.
      exact (rch_refl t ROOTINO). }
    assert (Hird : i ∉ rd).
    { intros Hc. destruct (proj1 (Hrd i) Hc) as (_ & _ & Hre).
      exact (Hunreach Hre). }
    (* the orphan's nlink is zero *)
    assert (Hnl0 : bv_unsigned (di_nlink dn) = 0).
    { pose proof (Hlkg i Hi Hlive) as Hcnt. cbv zeta in Hcnt.
      fold dn in Hcnt.
      rewrite (rtick_unreachable i Hunreach) in Hcnt.
      rewrite (bool_decide_eq_false_2 (i = ROOTINO) Hiroot) in Hcnt.
      assert (Hif : (if bool_decide (bv_unsigned (di_type dn) = T_DIR_z)
                     then 0 else 0) = 0)
        by (destruct (bool_decide (bv_unsigned (di_type dn) = T_DIR_z));
            reflexivity).
      rewrite Hif in Hcnt. rewrite Hcnt. reflexivity. }
    assert (HoutA : forall b : Z,
              b <> sb_bmapstart sb ->
              b <> IBLOCK (fs_inum_bv i) (sb_inodestart sb) ->
              P' b = P b).
    { intros b Hb1 Hb2. unfold P', eff_free_inode.
      rewrite fs_upd_ne by exact Hb1.
      apply (eff_dinode_out sb). exact Hb2. }
    assert (HsbU : P' SB_BNO = P SB_BNO).
    { apply HoutA; unfold SB_BNO, fs_data_start in *; lia. }
    assert (HbmB : P' (sb_bmapstart sb)
                   = bm_bytes BSIZE
                       (fs_bmap_set BSIZE (P (sb_bmapstart sb))
                        ∖ list_to_set (fs_inode_blocks P dn))).
    { unfold P', eff_free_inode. apply fs_upd_at. }
    assert (Hdec : forall z : Z, 0 <= z < 16 * (sb_ninodes sb / 16 + 1) ->
              fs_dinode P' sb z
              = if decide (z = i) then dn' else fs_dinode P sb z).
    { intros z Hz.
      transitivity (fs_dinode (eff_dinode P sb i dn') sb z).
      - apply fs_dinode_ext. unfold P', eff_free_inode.
        apply fs_upd_ne.
        destruct (iblock_bounds sb Hok z Hz) as (Hz1 & Hz2 & Hz3). lia.
      - exact (eff_dinode_dec sb Hok P i dn' z Hwf' HiN Hz). }
    assert (Hunt : forall z : Z, 0 <= z < sb_ninodes sb ->
              bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
              fs_ind_ents P' (fs_dinode P sb z)
              = fs_ind_ents P (fs_dinode P sb z)
              /\ (forall k : nat,
                    fs_data_of P' (fs_dinode P sb z) k
                    = fs_data_of P (fs_dinode P sb z) k)
              /\ fs_inode_blocks P' (fs_dinode P sb z)
                 = fs_inode_blocks P (fs_dinode P sb z)
              /\ fs_inode_dwf P' sb (fs_dinode P sb z)
                 = fs_inode_dwf P sb (fs_dinode P sb z)).
    { intros z Hz Hnz. apply inode_untouched; try assumption.
      intros b Hb. apply HoutA;
        pose proof (blocks_range z b Hz Hnz Hb) as Hbr;
        unfold fs_data_start in Hbr; lia. }
    (* [i]'s edges die; everything else is unmoved *)
    assert (Hentio : forall f : fname,
              tree_ent (tree_of_disk P' sb) i f = None).
    { intros f. apply (tree_ent_nondir P').
      rewrite (Hdec i HiN), decide_True by reflexivity.
      rewrite Htype'. unfold T_DIR_z. lia. }
    assert (Hentkeep : forall (j : Z) (f : fname), j <> i ->
              tree_ent (tree_of_disk P' sb) j f = tree_ent t j f).
    { intros j f Hji.
      apply tree_ent_untouched. intros Hjr.
      apply node_at_untouched; [exact Hjr | |].
      - rewrite (Hdec j ltac:(irng)), decide_False by exact Hji.
        reflexivity.
      - intros Hjl k Hk.
        destruct (Hunt j Hjr Hjl) as (_ & Hdata & _ & _).
        exact (Hdata k). }
    assert (Hreach : forall z : Z,
              fs_reachable P' sb z <-> fs_reachable P sb z).
    { intros z. unfold fs_reachable. split.
      - apply (rch_mono t (tree_of_disk P' sb) ROOTINO).
        intros j f w Hj' Hj He'.
        destruct (decide (j = i)) as [-> | Hji].
        + rewrite Hentio in He'. discriminate.
        + rewrite (Hentkeep j f Hji) in He'. exact He'.
      - apply (rch_mono (tree_of_disk P' sb) t ROOTINO).
        intros j f w Hj Hj' He.
        assert (Hji : j <> i)
          by (intros ->; exact (Hunreach Hj)).
        rewrite (Hentkeep j f Hji). exact He. }
    assert (Htyp : forall w : Z, 0 <= w < sb_ninodes sb -> w <> i ->
              bv_unsigned (di_type (fs_dinode P' sb w))
              = bv_unsigned (di_type (fs_dinode P sb w))).
    { intros w Hw Hne. rewrite (Hdec w ltac:(irng)).
      rewrite decide_False by exact Hne. reflexivity. }
    (* the supply is unmoved: the orphan's segment was already outside *)
    assert (Hsupply : fs_rtickets P' sb rd = fs_rtickets P sb rd).
    { unfold fs_rtickets. apply tick_mjoin_ext.
      intros x Hx. cbv beta.
      destruct (bool_decide (Z.of_nat x ∈ rd)) eqn:Hg; [| reflexivity].
      apply bool_decide_eq_true_1 in Hg.
      destruct (proj1 (Hrd _) Hg) as (Hxr & Hxty & _).
      assert (Hxi : Z.of_nat x <> i)
        by (intros Hc; rewrite Hc in Hg; exact (Hird Hg)).
      assert (Hxl : bv_unsigned (di_type (fs_dinode P sb (Z.of_nat x))) <> 0)
        by (rewrite Hxty; unfold T_DIR_z; discriminate).
      apply tickets_at_untouched; [exact Hxr | |].
      - rewrite (Hdec (Z.of_nat x) (iblk_ix_range sb x (proj2 Hx))),
          decide_False by exact Hxi.
        reflexivity.
      - intros _ k Hk.
        destruct (Hunt _ Hxr Hxl) as (_ & Hdata & _ & _).
        exact (Hdata k). }
    destruct (used_drop P' i Hi Hlive) as (u'' & Hu'' & Hu''mem).
    { intros z Hz Hne.
      rewrite (Hdec z ltac:(irng)), decide_False by exact Hne.
      destruct (bv_unsigned (di_type (fs_dinode P sb z)) =? 0) eqn:Ez;
        [reflexivity |].
      destruct (Hunt z Hz (proj1 (Z.eqb_neq _ _) Ez)) as (_ & _ & Hbl & _).
      exact Hbl. }
    { rewrite (Hdec i HiN), decide_True by reflexivity.
      rewrite Htype'. reflexivity. }
    exists sb. split.
    { rewrite (fs_parse_sb_ext P P' HsbU). exact Hp. }
    constructor.
    - exact Hsb.
    - apply fs_inodes_dwf_intro. intros z Hz Hnz'.
      rewrite (Hdec z ltac:(irng)) in Hnz' |- *.
      destruct (decide (z = i)) as [-> | Hne].
      { exfalso. exact (Hnz' Htype'). }
      destruct (Hunt z Hz Hnz') as (_ & _ & _ & Hdwf).
      rewrite Hdwf. exact (dwf_bool_at z Hz Hnz').
    - exists u''. split; [exact Hu'' |].
      apply (bitmap_wf_of_set P' u''
               (fs_bmap_set BSIZE (P (sb_bmapstart sb))
                ∖ list_to_set (fs_inode_blocks P dn))); [exact HbmB |].
      intros b Hb.
      rewrite elem_of_difference, elem_of_list_to_set.
      rewrite (old_bit_iff b Hb), (Hu''mem b).
      assert (Hmeta : b < fs_data_start sb ->
                ~ b ∈ fs_inode_blocks P dn).
      { intros Hlt Hin.
        pose proof (blocks_range i b Hi Hlive Hin). lia. }
      tauto.
    - apply root_wf_untouched.
      + rewrite (Hdec ROOTINO (iblk_root_range sb Hnin1)).
        rewrite decide_False
          by (intros Hc; exact (Hiroot (eq_sym Hc))).
        reflexivity.
      + intros k Hk.
        assert (Hrl : bv_unsigned (di_type (fs_dinode P sb ROOTINO)) <> 0).
        { rewrite (fs_root_wf_type P sb HW7). unfold T_DIR_z. lia. }
        destruct (Hunt ROOTINO
                    ltac:(pose proof Hnin1; unfold ROOTINO; lia) Hrl)
          as (_ & Hdata & _ & _).
        exact (Hdata k).
    - apply fs_dots_all_intro. intros z Hz Hdty.
      rewrite (Hdec z ltac:(irng)) in Hdty |- *.
      destruct (decide (z = i)) as [-> | Hne].
      { exfalso. rewrite Htype' in Hdty. unfold T_DIR_z in Hdty. lia. }
      assert (Hzl : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
        by (rewrite Hdty; unfold T_DIR_z; discriminate).
      destruct (Hunt z Hz Hzl) as (_ & Hdata & _ & _).
      apply (fs_dots_wf_win P P' z (fs_dinode P sb z) (fs_dinode P sb z)).
      + lia.
      + apply (dir_win_agree_blocks _ _ FS_MAXFILE);
          [intros k Hk; exact (Hdata k) | unfold FS_MAXFILE, BSIZE; lia].
      + apply (dir_win_agree_blocks _ _ FS_MAXFILE);
          [intros k Hk; exact (Hdata k) | unfold FS_MAXFILE, BSIZE; lia].
      + exact (dots_bool_at z Hz Hdty).
    - exists nib. split; [exact Hnibz |].
      apply fs_region_wf_intro.
      + intros z Hz Hzn.
        rewrite (Hdec z ltac:(irng)).
        rewrite decide_False by lia.
        apply (fs_region_free_spec P sb nib z
                 (fs_region_wf_free P sb nib Hreg)); lia.
      + intros z Hz Hfree.
        rewrite (Hdec z ltac:(irng)) in Hfree |- *.
        destruct (decide (z = i)) as [-> | Hne].
        * rewrite Hnlink'. exact Hnl0.
        * apply (fs_region_nlink_free P sb nib z
                   (fs_region_wf_nlink P sb nib Hreg)); [lia | exact Hfree].
      + intros z Hz.
        rewrite (Hdec z ltac:(irng)).
        destruct (decide (z = i)) as [-> | Hne].
        * rewrite Hnlink'.
          apply (fs_region_nlink_short P sb nib i
                   (fs_region_wf_nlink P sb nib Hreg)). lia.
        * apply (fs_region_nlink_short P sb nib z
                   (fs_region_wf_nlink P sb nib Hreg)). lia.
    - exists rd.
      split; [| split; [| split]].
      + intros z. rewrite (Hrd z).
        destruct (decide (0 <= z < sb_ninodes sb)) as [Hzr | Hzr].
        * destruct (decide (z = i)) as [-> | Hne].
          { split.
            - intros (_ & _ & Hre). exfalso. exact (Hunreach Hre).
            - intros (_ & Hty' & _). exfalso.
              rewrite (Hdec i HiN), decide_True in Hty' by reflexivity.
              rewrite Htype' in Hty'. unfold T_DIR_z in Hty'. lia. }
          rewrite (Htyp z Hzr Hne).
          split; intros (A & B & C); (split; [exact A |]);
            (split; [exact B |]).
          -- apply (Hreach z). exact C.
          -- apply (Hreach z) in C. exact C.
        * split; intros (A & _); [lia | lia].
      + intros z Hz.
        destruct (proj1 (Hrd z) Hz) as (Hzr & Hzty & _).
        assert (Hne : z <> i)
          by (intros Hc; rewrite Hc in Hz; exact (Hird Hz)).
        assert (Hzl : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
          by (rewrite Hzty; unfold T_DIR_z; discriminate).
        destruct (Hunt z Hzr Hzl) as (_ & Hdata & _ & _).
        apply dir_ok_untouched; [exact Hz | | |].
        * rewrite (Hdec z ltac:(irng)), decide_False by exact Hne.
          reflexivity.
        * intros k Hk. exact (Hdata k).
        * intros w Hw Hwl Hw0.
          destruct (decide (w = i)) as [-> | Hwne].
          -- intros Hre. exact (Hunreach Hre).
          -- exfalso. apply Hwl. rewrite <- (Htyp w Hw Hwne). exact Hw0.
      + intros z Hz. cbv zeta.
        rewrite (Hdec z ltac:(irng)).
        unfold fs_rtick. rewrite Hsupply.
        destruct (decide (z = i)) as [-> | Hne].
        * intros Hc. exfalso. exact (Hc Htype').
        * exact (Hlkg z Hz).
      + intros z Hz Hty' Hnin.
        rewrite (Hdec z ltac:(irng)) in Hty' |- *.
        destruct (decide (z = i)) as [-> | Hne].
        { exfalso. rewrite Htype' in Hty'. unfold T_DIR_z in Hty'. lia. }
        assert (Hzl : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
          by (rewrite Hty'; unfold T_DIR_z; discriminate).
        destruct (Hunt z Hz Hzl) as (_ & Hdata & _ & _).
        apply (dots_only_untouched P' (fs_dinode P sb z)).
        * exact (fdi_size _ _ _ (dok_at z Hz Hzl)).
        * intros k Hk. exact (Hdata k).
        * exact (Horph z Hz Hty' Hnin).
  Qed.

End EffFreeInode.

(* the [fs_durable_wf_view]-level wrappers -- the shape stage G2
   consumes: the invariant of the OLD view, the decode-level
   preconditions, the invariant of the updated view. *)

Lemma eff_free_inode_wfv (P : Z -> list (bv 8)) (sb : fs_sb)
    (i : Z) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  ~ fs_reachable P sb i ->
  fs_durable_wf_view (eff_free_inode P sb i).
Proof.
  intros Hv Hp. intros.
  destruct Hv as (sb0 & Hp0 & Hsw).
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
  destruct HW45 as (u & Hu & Hbm).
  destruct Hregx as (nib & Hnibz & Hreg).
  destruct HW9 as (rd & Hrd & Hdok & Hlkg & Horph).
  apply (eff_free_inode_wf P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph); assumption.
Qed.
