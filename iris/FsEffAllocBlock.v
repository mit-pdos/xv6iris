(* FsEffAllocBlock.v -- durable-disk stage F2, effect 1: appending a
   fresh content block (bmap+balloc's net at the append slot).  The
   fused indirect-block allocation (fbn = 12) is a follow-up effect. *)
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

Section EffAllocBlock.
  Context (P : Z -> list (bv 8)) (sb : fs_sb).
  Context (Hp : fs_parse_sb P = Some sb).
  Context (Hsb : fs_sb_wf sb = true).
  Context (HW3 : fs_inodes_dwf P sb = true).
  Context (u : gset Z) (Hu : fs_ent_set P sb = Some u).
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
  Local Notation ent_grow := (ent_grow P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation node_at_meta := (node_at_meta P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation tickets_at_meta := (tickets_at_meta P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation dir_ok_meta := (dir_ok_meta P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation dots_only_meta := (dots_only_meta P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation root_wf_meta := (root_wf_meta P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).

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

  Local Lemma omap_none {A B : Type} (f : A -> option B) (l : list A) :
    (forall x : A, x ∈ l -> f x = None) -> omap f l = [].
  Proof.
    induction l as [| a l IH]; intros H; [reflexivity |].
    cbn [omap list_omap].
    rewrite (H a (elem_of_list_here a l)).
    apply IH. intros x Hx. apply H, elem_of_list_further, Hx.
  Qed.

  (* the used set after one live inode's segment GROWS by [fresh] *)

  (* ==================================================================== *)
  (*  22.  EFFECT 1 -- INSTALLING A FRESH BLOCK IN AN EMPTY SLOT           *)
  (*                                                                       *)
  (*  bmap+balloc's net at ANY empty slot: the bitmap bit, the zeroed      *)
  (*  fresh block, and the slot itself -- a direct cell, or an entry of    *)
  (*  the EXISTING indirect block.  THERE IS NO SIZE MOVE (durable-disk    *)
  (*  F3.2): the size is [eff_set_size]'s business, and keeping the two    *)
  (*  apart is exactly what makes the precondition here SLOT EMPTINESS     *)
  (*  instead of the append equation -- with the size fused, preserving    *)
  (*  the coverage clause at [nblk(sz')] forces [fbn = nblk(size)] back.   *)
  (*  It is also what makes [writei]'s partial-failure arms (which install *)
  (*  the block and leave [ip->size] alone) THIS effect verbatim, with no  *)
  (*  chaining.  [iupdate] runs on every path, so the record is re-encoded *)
  (*  either way; on the indirect arm that write is a no-op re-encode.     *)
  (*  Allocating the INDIRECT BLOCK itself is [eff_alloc_ind_block].       *)
  (*                                                                       *)
  (*  THE DATA VIEW DOES NOT MOVE.  An empty slot reads as a block of      *)
  (*  zeroes ([fs_data_of_holes]) and the fresh block IS a block of        *)
  (*  zeroes, so every reader above the block map -- the tree, the ticket  *)
  (*  supply, the dirent windows, the dots -- is literally unchanged, and  *)
  (*  only W3 (the record) and W4/W5 (the used set and its bit) move.      *)
  (* ==================================================================== *)

  Definition eff_alloc_file_block (i : Z) (fbn : nat) (fresh : Z)
    : Z -> list (bv 8) :=
    let dn := fs_dinode P sb i in
    let base :=
      if (fbn <? 12)%nat
      then eff_dinode P sb i
             (di_set_size_addr dn (di_size dn) fbn (Z_to_bv 32 fresh))
      else
        fs_upd (eff_dinode P sb i dn)
          (bv_unsigned (di_addrs dn !!! 12%nat))
          (fs_splice (P (bv_unsigned (di_addrs dn !!! 12%nat)))
             (4 * (fbn - 12)) 4
             (fun t => nth_byte (Z_to_bv 32 fresh) t)) in
    fs_upd
      (fs_upd base (sb_bmapstart sb)
         (bm_bytes BSIZE
            (fs_bmap_set BSIZE (P (sb_bmapstart sb)) ∪ {[fresh]})))
      fresh (replicate BSIZE (bv_0 8)).

  Local Lemma fs_le_at4_range (bs : list (bv 8)) (o : nat) :
    0 <= fs_le_at bs o 4 < 4294967296.
  Proof.
    unfold fs_le_at.
    pose proof (assemble_bytes_bound
                  ((fun j => bs !!! (o + j)%nat) <$> seq 0 4)) as Hb.
    rewrite length_fmap, length_seq in Hb.
    change (2 ^ (8 * Z.of_nat 4)) with 4294967296 in Hb. exact Hb.
  Qed.

  Lemma eff_alloc_file_block_wf (i : Z) (fbn : nat) (fresh : Z) :
    0 <= i < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
    (fbn < FS_MAXFILE)%nat ->
    fs_slot P (fs_dinode P sb i) fbn = 0 ->
    ((12 <= fbn)%nat ->
       bv_unsigned (di_addrs (fs_dinode P sb i) !!! 12%nat) <> 0) ->
    fs_data_start sb <= fresh < sb_size sb -> fresh ∉ u ->
    fs_durable_wf_view (eff_alloc_file_block i fbn fresh)
    (* ...AND THE TRANSPORT (durable-disk F3.5): what the effect did to
       the inode's block map, at the NEW view's own decode.  A chain that
       must re-establish a coverage premise after the step reads it here
       instead of re-deriving the effect's footprint. *)
    /\ (forall k : nat, (k <= FS_MAXFILE)%nat ->
          fs_slot (eff_alloc_file_block i fbn fresh)
            (fs_dinode (eff_alloc_file_block i fbn fresh) sb i) k
          = if decide (k = fbn) then fresh
            else fs_slot P (fs_dinode P sb i) k).
  Proof.
    intros Hi Hlive HfbnM Hslot0 Hibnz Hfr Hfru.
    assert (HDM : (FS_NDIRECT + FS_NINDIRECT)%nat = FS_MAXFILE)
      by reflexivity.
    assert (Hm32 : bv_modulus 32 = 4294967296) by reflexivity.
    set (dn := fs_dinode P sb i) in *.
    set (dn' := if (fbn <? 12)%nat
                then di_set_size_addr dn (di_size dn) fbn (Z_to_bv 32 fresh)
                else dn).
    set (P' := eff_alloc_file_block i fbn fresh).
    pose proof (dok_at i Hi Hlive) as Hdok_i. fold dn in Hdok_i.
    pose proof (fdi_size _ _ _ Hdok_i) as Hcap. fold dn in Hcap.
    pose proof (proj1 (bv_unsigned_in_range _ (di_size dn))) as Hsz0.
    destruct (fs_sb_ok_meta sb Hok) as (Hm1 & Hm2 & Hm3).
    pose proof (sbo_one_bitmap sb Hok) as Hone.
    pose proof Hnin_le as HninN.
    assert (HiN : 0 <= i < 16 * (sb_ninodes sb / 16 + 1)) by lia.
    destruct (iblock_bounds sb Hok i HiN) as (Hibb1 & Hibb2 & Hibb3).
    assert (Hfr0 : fresh <> 0) by (unfold fs_data_start in *; lia).
    assert (Hfru32 : bv_unsigned (Z_to_bv 32 fresh) = fresh)
      by (apply Z_to_bv_small; unfold BSIZE_z in Hone; lia).
    (* the slot is BEYOND the size -- the coverage clause read backwards *)
    assert (Hfbn_ge : fs_nblk (bv_unsigned (di_size dn)) <= Z.of_nat fbn).
    { destruct (Z.le_gt_cases (fs_nblk (bv_unsigned (di_size dn)))
                  (Z.of_nat fbn)) as [Hle | Hgt]; [exact Hle |].
      exfalso.
      pose proof (fs_inode_dok_blk P sb dn fbn Hdok_i HfbnM Hgt) as Hrg.
      rewrite (fs_slot_blk dn fbn HfbnM) in Hslot0.
      unfold fs_data_start in Hrg. lia. }
    (* --- the two arms of the record ----------------------------------- *)
    assert (Hdn'lo : (fbn < 12)%nat ->
              dn' = di_set_size_addr dn (di_size dn) fbn (Z_to_bv 32 fresh)).
    { intros H. unfold dn'.
      rewrite (proj2 (Nat.ltb_lt fbn 12) H). reflexivity. }
    assert (Hdn'hi : (12 <= fbn)%nat -> dn' = dn).
    { intros H. unfold dn'.
      rewrite (proj2 (Nat.ltb_ge fbn 12) H). reflexivity. }
    assert (Hty' : di_type dn' = di_type dn)
      by (unfold dn'; destruct (fbn <? 12)%nat; reflexivity).
    assert (Hnl' : di_nlink dn' = di_nlink dn)
      by (unfold dn'; destruct (fbn <? 12)%nat; reflexivity).
    assert (Hszz' : di_size dn' = di_size dn)
      by (unfold dn'; destruct (fbn <? 12)%nat; reflexivity).
    assert (Hwf' : dinode_wf dn').
    { unfold dn'. destruct (fbn <? 12)%nat.
      - apply di_set_size_addr_wf. exact (fs_dinode_wf P sb i).
      - exact (fs_dinode_wf P sb i). }
    assert (Ha12' : di_addrs dn' !!! 12%nat = di_addrs dn !!! 12%nat).
    { unfold dn'. destruct (Nat.ltb_spec fbn 12) as [Harm | Harm];
        [| reflexivity].
      unfold di_set_size_addr. cbn [di_addrs].
      apply list_lookup_total_insert_ne. lia. }
    (* --- the indirect block ------------------------------------------- *)
    assert (Hib_in : (bv_unsigned (di_addrs dn !!! 12%nat)) <> 0 -> (bv_unsigned (di_addrs dn !!! 12%nat)) ∈ fs_inode_ents P dn).
    { intros Hnz. rewrite <- (fs_slot_max P dn).
      apply (fs_inode_ents_slot P dn);
        [lia | rewrite fs_slot_max; exact Hnz]. }
    assert (Hib_rng : (bv_unsigned (di_addrs dn !!! 12%nat)) <> 0 -> fs_data_start sb <= (bv_unsigned (di_addrs dn !!! 12%nat)) < sb_size sb).
    { intros Hnz. exact (blocks_range i (bv_unsigned (di_addrs dn !!! 12%nat)) Hi Hlive (Hib_in Hnz)). }
    assert (Hibfr : (bv_unsigned (di_addrs dn !!! 12%nat)) <> 0 -> (bv_unsigned (di_addrs dn !!! 12%nat)) <> fresh).
    { intros Hnz Hc. apply Hfru. rewrite <- Hc.
      exact (used_elem i (bv_unsigned (di_addrs dn !!! 12%nat)) Hi Hlive (Hib_in Hnz)). }
    (* --- the touched blocks ------------------------------------------- *)
    assert (HaE : forall b : Z,
              b <> fresh -> b <> sb_bmapstart sb ->
              b <> IBLOCK (fs_inum_bv i) (sb_inodestart sb) ->
              ((12 <= fbn)%nat -> b <> (bv_unsigned (di_addrs dn !!! 12%nat))) ->
              P' b = P b).
    { intros b Hb1 Hb2 Hb3 Hb4. unfold P', eff_alloc_file_block.
      cbv zeta. fold dn.
      rewrite fs_upd_ne by exact Hb1.
      rewrite fs_upd_ne by exact Hb2.
      destruct (Nat.ltb_spec fbn 12) as [Harm | Harm].
      - exact (eff_dinode_out sb _ _ _ _ Hb3).
      - rewrite fs_upd_ne by (apply Hb4; lia).
        exact (eff_dinode_out sb _ _ _ _ Hb3). }
    assert (HsbU : P' SB_BNO = P SB_BNO).
    { apply HaE;
        [ unfold SB_BNO, fs_data_start in *; lia
        | unfold SB_BNO, fs_data_start in *; lia
        | unfold SB_BNO, fs_data_start in *; lia
        | intros Hgt; pose proof (Hib_rng (Hibnz Hgt));
          unfold SB_BNO, fs_data_start in *; lia ]. }
    assert (HbmB : P' (sb_bmapstart sb)
                   = bm_bytes BSIZE
                       (fs_bmap_set BSIZE (P (sb_bmapstart sb))
                        ∪ {[fresh]})).
    { unfold P', eff_alloc_file_block. cbv zeta. fold dn.
      rewrite fs_upd_ne by (unfold fs_data_start in *; lia).
      apply fs_upd_at. }
    assert (HfrB : P' fresh = replicate BSIZE (bv_0 8)).
    { unfold P', eff_alloc_file_block. cbv zeta. fold dn.
      apply fs_upd_at. }
    assert (Hdec : forall z : Z, 0 <= z < 16 * (sb_ninodes sb / 16 + 1) ->
              fs_dinode P' sb z
              = if decide (z = i) then dn' else fs_dinode P sb z).
    { intros z Hz.
      destruct (iblock_bounds sb Hok z Hz) as (Hz1 & Hz2 & Hz3).
      transitivity (fs_dinode (eff_dinode P sb i dn') sb z).
      - apply fs_dinode_ext. unfold P', eff_alloc_file_block. cbv zeta.
        fold dn.
        rewrite fs_upd_ne by (unfold fs_data_start in Hfr; lia).
        rewrite fs_upd_ne by lia.
        destruct (Nat.ltb_spec fbn 12) as [Harm | Harm].
        + rewrite (Hdn'lo Harm). reflexivity.
        + rewrite fs_upd_ne
            by (pose proof (Hib_rng (Hibnz ltac:(lia)));
                unfold fs_data_start in *; lia).
          rewrite (Hdn'hi Harm). reflexivity.
      - exact (eff_dinode_dec sb Hok P i dn' z Hwf' HiN Hz). }
    (* --- the block map: slot [fbn] gains [fresh], nothing else moves --- *)
    assert (Hind_lo : (fbn < 12)%nat ->
              fs_ind_ents P' dn' = fs_ind_ents P dn).
    { intros Harm.
      transitivity (fs_ind_ents P' dn).
      - apply fs_ind_ents_meta12. exact Ha12'.
      - apply fs_ind_ents_ext. intros Hnz12.
        apply HaE.
        + exact (Hibfr Hnz12).
        + pose proof (Hib_rng Hnz12). unfold fs_data_start in *. lia.
        + pose proof (Hib_rng Hnz12). unfold fs_data_start in *. lia.
        + intros Hc. exfalso. lia. }
    assert (Hind_hi : (12 <= fbn)%nat ->
              (forall j : nat, (j < FS_NINDIRECT)%nat ->
                 fs_ind_ents P' dn' !!! j
                 = if decide (j = (fbn - 12)%nat) then fresh
                   else fs_ind_ents P dn !!! j)).
    { intros Harm j Hj.
      pose proof (Hibnz Harm) as Hibnz'.
      assert (HibB : P' (bv_unsigned (di_addrs dn !!! 12%nat))
                     = fs_splice (P (bv_unsigned (di_addrs dn !!! 12%nat))) (4 * (fbn - 12)) 4
                         (fun t => nth_byte (Z_to_bv 32 fresh) t)).
      { unfold P', eff_alloc_file_block. cbv zeta. fold dn.
        rewrite fs_upd_ne by (intros Hc; exact (Hibfr Hibnz' Hc)).
        rewrite fs_upd_ne
          by (pose proof (Hib_rng Hibnz'); unfold fs_data_start in *; lia).
        rewrite (proj2 (Nat.ltb_ge fbn 12) Harm).
        apply fs_upd_at. }
      unfold fs_ind_ents at 1. rewrite Ha12'.
      rewrite (proj2 (Z.eqb_neq (bv_unsigned (di_addrs dn !!! 12%nat)) 0) Hibnz').
      rewrite list_lookup_total_alt, list_lookup_fmap.
      rewrite (lookup_seq_lt 0 FS_NINDIRECT j Hj).
      cbn [fmap option_fmap option_map default from_option id].
      rewrite Nat.add_0_l.
      rewrite HibB.
      destruct (decide (j = (fbn - 12)%nat)) as [-> | Hjne].
      - assert (Hw : Z_to_bv 32 (fs_le_at
                       (fs_splice (P (bv_unsigned (di_addrs dn !!! 12%nat))) (4 * (fbn - 12)) 4
                          (fun t => nth_byte (Z_to_bv 32 fresh) t))
                       (4 * (fbn - 12)) 4)
                     = Z_to_bv 32 fresh).
        { apply fs_le_word_at. intros j0 Hj0.
          rewrite fs_splice_lookup
            by (unfold FS_NINDIRECT, FS_MAXFILE, FS_NDIRECT in *;
                unfold BSIZE; lia).
          rewrite decide_True by lia.
          f_equal. lia. }
        apply (f_equal bv_unsigned) in Hw.
        rewrite Hfru32 in Hw.
        pose proof (fs_le_at4_range
                      (fs_splice (P (bv_unsigned (di_addrs dn !!! 12%nat))) (4 * (fbn - 12)) 4
                         (fun t => nth_byte (Z_to_bv 32 fresh) t))
                      (4 * (fbn - 12))) as Hrng.
        rewrite Z_to_bv_small in Hw by lia.
        exact Hw.
      - assert (Hrhs : fs_ind_ents P dn !!! j
                       = fs_le_at (P (bv_unsigned (di_addrs dn !!! 12%nat)))
                           (4 * j) 4).
        { unfold fs_ind_ents.
          rewrite (proj2 (Z.eqb_neq
                            (bv_unsigned (di_addrs dn !!! 12%nat)) 0)
                     Hibnz').
          rewrite list_lookup_total_alt, list_lookup_fmap.
          rewrite (lookup_seq_lt 0 FS_NINDIRECT j Hj).
          cbn [fmap option_fmap option_map default from_option id].
          rewrite Nat.add_0_l. reflexivity. }
        rewrite Hrhs.
        unfold fs_le_at. f_equal.
        apply list_fmap_ext. intros idx x Hx.
        apply lookup_seq in Hx as [-> Hidx].
        rewrite fs_splice_lookup
          by (unfold FS_NINDIRECT in Hj; unfold BSIZE; lia).
        rewrite decide_False; [reflexivity |].
        intros [H1 H2]. apply Hjne.
        assert (4 * j <= 4 * idx + 4 * j)%nat by lia. lia. }
    (* --- THE SLOT CHARACTERISATION ------------------------------------ *)
    assert (Hslot' : forall k : nat, (k <= FS_MAXFILE)%nat ->
              fs_slot P' dn' k
              = if decide (k = fbn) then fresh else fs_slot P dn k).
    { intros k Hk.
      destruct (decide (k = FS_MAXFILE)) as [-> | HkM].
      { rewrite decide_False by lia. rewrite !fs_slot_max, Ha12'.
        reflexivity. }
      assert (HkL : (k < FS_MAXFILE)%nat) by lia.
      rewrite (fs_slot_lt P' dn' k HkL), (fs_slot_lt P dn k HkL).
      unfold fs_blk_addr.
      destruct (Nat.ltb_spec k FS_NDIRECT) as [Hkd | Hkd].
      - (* a direct cell *)
        destruct (Nat.ltb_spec fbn 12) as [Harm | Harm].
        + assert (Hlo : di_addrs dn'
                        = <[fbn := Z_to_bv 32 fresh]> (di_addrs dn))
            by (rewrite (Hdn'lo Harm); reflexivity).
          assert (Hlen : (fbn < length (di_addrs dn))%nat).
          { pose proof (fs_dinode_wf P sb i) as Hwfo.
            unfold dinode_wf in Hwfo. fold dn in Hwfo.
            rewrite Hwfo. lia. }
          rewrite Hlo.
          destruct (decide (k = fbn)) as [-> | Hne].
          * rewrite (list_lookup_total_insert _ _ _ Hlen). exact Hfru32.
          * rewrite list_lookup_total_insert_ne
              by (intros Hc; exact (Hne (eq_sym Hc))).
            reflexivity.
        + rewrite (Hdn'hi ltac:(lia)).
          rewrite decide_False by (unfold FS_NDIRECT in *; lia).
          reflexivity.
      - (* an indirect entry *)
        assert (Hkj : (k - FS_NDIRECT < FS_NINDIRECT)%nat) by lia.
        destruct (Nat.ltb_spec fbn 12) as [Harm | Harm].
        + rewrite (Hind_lo Harm).
          rewrite decide_False by (unfold FS_NDIRECT in *; lia).
          reflexivity.
        + rewrite (Hind_hi ltac:(lia) (k - FS_NDIRECT)%nat Hkj).
          destruct (decide ((k - FS_NDIRECT)%nat = (fbn - 12)%nat))
            as [He | He].
          * rewrite decide_True by (unfold FS_NDIRECT in *; lia).
            reflexivity.
          * rewrite decide_False by (unfold FS_NDIRECT in *; lia).
            reflexivity. }
    assert (Hslotfbn : fs_slot P' dn' fbn = fresh).
    { rewrite (Hslot' fbn ltac:(lia)), decide_True by reflexivity.
      reflexivity. }
    assert (Hslotne : forall k : nat, (k <= FS_MAXFILE)%nat -> k <> fbn ->
              fs_slot P' dn' k = fs_slot P dn k).
    { intros k Hk Hne.
      rewrite (Hslot' k Hk), decide_False by exact Hne. reflexivity. }
    (* --- the record's own sanity -------------------------------------- *)
    assert (Hdok' : fs_inode_dok P' sb dn').
    { assert (Hdir' : forall k : nat, (k < FS_NDIRECT)%nat ->
                bv_unsigned (di_addrs dn' !!! k)
                = if decide (k = fbn) then fresh
                  else bv_unsigned (di_addrs dn !!! k)).
      { intros k Hk.
        pose proof (Hslot' k ltac:(lia)) as Hs.
        rewrite (fs_slot_direct P' dn' k Hk),
          (fs_slot_direct P dn k Hk) in Hs.
        exact Hs. }
      assert (Hent' : forall j : nat, (j < FS_NINDIRECT)%nat ->
                fs_ind_ents P' dn' !!! j
                = if decide ((FS_NDIRECT + j)%nat = fbn) then fresh
                  else fs_ind_ents P dn !!! j).
      { intros j Hj.
        pose proof (Hslot' (FS_NDIRECT + j)%nat ltac:(lia)) as Hs.
        rewrite (fs_slot_ent P' dn' (FS_NDIRECT + j)%nat
                   ltac:(lia) ltac:(lia)) in Hs.
        rewrite (fs_slot_ent P dn (FS_NDIRECT + j)%nat
                   ltac:(lia) ltac:(lia)) in Hs.
        replace (FS_NDIRECT + j - FS_NDIRECT)%nat with j in Hs by lia.
        exact Hs. }
      constructor; rewrite ?Hty', ?Hszz'.
      - exact (fdi_type _ _ _ Hdok_i).
      - exact Hcap.
      - intros k Hk Hlt. rewrite (Hdir' k Hk).
        rewrite decide_False by (intros ->; lia).
        exact (fdi_direct _ _ _ Hdok_i k Hk Hlt).
      - intros k Hk Hnz. rewrite (Hdir' k Hk) in Hnz |- *.
        destruct (decide (k = fbn)) as [-> | Hne]; [lia |].
        exact (fdi_direct_ok _ _ _ Hdok_i k Hk Hnz).
      - rewrite Ha12'. exact (fdi_ind_ok _ _ _ Hdok_i).
      - rewrite Ha12'. exact (fdi_ind _ _ _ Hdok_i).
      - intros j Hj Hlt. rewrite (Hent' j Hj).
        rewrite decide_False by (intros Hc; lia).
        exact (fdi_ent _ _ _ Hdok_i j Hj Hlt).
      - intros j Hj Hnz. rewrite (Hent' j Hj) in Hnz |- *.
        destruct (decide ((FS_NDIRECT + j)%nat = fbn)) as [He | He];
          [lia |].
        exact (fdi_ent_ok _ _ _ Hdok_i j Hj Hnz). }
    assert (Hdwf' : fs_inode_dwf P' sb dn' = true)
      by exact (fs_inode_dok_dwf P' sb dn' Hdok').
    (* --- the entry list gains exactly [fresh] -------------------------- *)
    assert (Hents' : fs_inode_ents P' dn'
                     ≡ₚ (fs_inode_ents P dn ++ [fresh])%list).
    { apply (fs_inode_ents_upd P P' dn dn' fbn fresh);
        [lia | exact Hfr0 | exact Hslot0 | exact Hslotfbn | exact Hslotne]. }
    (* --- THE DATA VIEW DOES NOT MOVE ---------------------------------- *)
    assert (Hslotinj : fs_slot_inj P dn)
      by (apply (slot_inj_at i Hi Hlive)).
    assert (Hdata_i : forall k : nat,
              fs_data_of P' dn' k = fs_data_of P dn k).
    { intros k. rewrite !fs_data_of_addr.
      destruct (Nat.lt_ge_cases k FS_MAXFILE) as [Hk | Hk].
      2:{ rewrite (fs_blk_addr_high P' dn' k Hk),
            (fs_blk_addr_high P dn k Hk).
          rewrite (proj2 (Z.eqb_neq 1 0) ltac:(lia)). exact HsbU. }
      rewrite <- (fs_slot_lt P' dn' k Hk), <- (fs_slot_lt P dn k Hk).
      destruct (decide (k = fbn)) as [-> | Hne].
      - rewrite Hslotfbn, Hslot0.
        rewrite (proj2 (Z.eqb_neq _ _) Hfr0). cbn [Z.eqb].
        exact HfrB.
      - rewrite (Hslotne k ltac:(lia) Hne).
        destruct (fs_slot P dn k =? 0) eqn:E; [reflexivity |].
        assert (Enz : fs_slot P dn k <> 0) by (apply Z.eqb_neq; exact E).
        assert (Hin : fs_slot P dn k ∈ fs_inode_ents P dn)
          by (apply (fs_inode_ents_slot P dn); [lia | exact Enz]).
        pose proof (blocks_range i _ Hi Hlive Hin) as Hbr.
        apply HaE.
        + intros Hc. apply Hfru. rewrite <- Hc.
          exact (used_elem i _ Hi Hlive Hin).
        + unfold fs_data_start in *. lia.
        + unfold fs_data_start in *. lia.
        + intros Hgt Hc.
          assert (Hkm : k = FS_MAXFILE).
          { apply (Hslotinj k FS_MAXFILE ltac:(lia) ltac:(lia) Enz).
            rewrite fs_slot_max. exact Hc. }
          lia. }
    (* --- everything above the block map is unmoved --------------------- *)
    assert (Hunt : forall z : Z, 0 <= z < sb_ninodes sb -> z <> i ->
              bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
              fs_ind_ents P' (fs_dinode P sb z)
              = fs_ind_ents P (fs_dinode P sb z)
              /\ (forall k : nat,
                    fs_data_of P' (fs_dinode P sb z) k
                    = fs_data_of P (fs_dinode P sb z) k)
              /\ fs_inode_ents P' (fs_dinode P sb z)
                 = fs_inode_ents P (fs_dinode P sb z)
              /\ fs_inode_dwf P' sb (fs_dinode P sb z)
                 = fs_inode_dwf P sb (fs_dinode P sb z)).
    { intros z Hz Hne Hnz. apply inode_untouched; try assumption.
      intros b Hb. pose proof (blocks_range z b Hz Hnz Hb) as Hbr.
      apply HaE.
      - intros ->. apply Hfru. exact (used_elem z _ Hz Hnz Hb).
      - unfold fs_data_start in *. lia.
      - unfold fs_data_start in *. lia.
      - intros Hgt Hc. rewrite Hc in Hb.
        exact (blocks_cross z i _ Hz Hi Hne Hnz Hlive Hb
                 (Hib_in (Hibnz Hgt))). }
    assert (Htypall : forall z : Z, 0 <= z < sb_ninodes sb ->
              di_type (fs_dinode P' sb z) = di_type (fs_dinode P sb z)).
    { intros z Hz. rewrite (Hdec z ltac:(irng)).
      destruct (decide (z = i)) as [-> | Hne]; [exact Hty' | reflexivity]. }
    assert (Htyp : forall z : Z, 0 <= z < sb_ninodes sb ->
              bv_unsigned (di_type (fs_dinode P' sb z))
              = bv_unsigned (di_type (fs_dinode P sb z))).
    { intros z Hz. rewrite (Htypall z Hz). reflexivity. }
    assert (Hszall : forall z : Z, 0 <= z < sb_ninodes sb ->
              di_size (fs_dinode P' sb z) = di_size (fs_dinode P sb z)).
    { intros z Hz. rewrite (Hdec z ltac:(irng)).
      destruct (decide (z = i)) as [-> | Hne]; [exact Hszz' | reflexivity]. }
    assert (Hdatall : forall z : Z, 0 <= z < sb_ninodes sb ->
              bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
              forall k : nat, (k < FS_MAXFILE)%nat ->
                fs_data_of P' (fs_dinode P' sb z) k
                = fs_data_of P (fs_dinode P sb z) k).
    { intros z Hz Hnz k Hk.
      rewrite (Hdec z ltac:(irng)).
      destruct (decide (z = i)) as [-> | Hne]; [exact (Hdata_i k) |].
      destruct (Hunt z Hz Hne Hnz) as (_ & Hdata & _ & _). exact (Hdata k). }
    assert (Htree : forall (j : Z) (f : fname),
              tree_ent (tree_of_disk P' sb) j f = tree_ent t j f).
    { intros j f. apply tree_ent_untouched. intros Hjr.
      apply node_at_meta;
        [ exact Hjr | exact (Htypall j Hjr) | exact (Hszall j Hjr)
        | intros Hjl; exact (Hdatall j Hjr Hjl) ]. }
    pose proof (reach_iff_of_ent P' Htree) as Hreach.
    assert (Hsupply : fs_rtickets P' sb rd = fs_rtickets P sb rd).
    { unfold fs_rtickets. apply tick_mjoin_ext.
      intros x Hx. cbv beta.
      destruct (bool_decide (Z.of_nat x ∈ rd)) eqn:Hg; [| reflexivity].
      apply bool_decide_eq_true_1 in Hg.
      destruct (proj1 (Hrd _) Hg) as (Hxr & Hxty & _).
      apply tickets_at_meta;
        [ exact Hxr | exact (Htypall _ Hxr) | exact (Hszall _ Hxr)
        | intros Hxl; exact (Hdatall _ Hxr Hxl) ]. }
    (* --- W4/W5 --------------------------------------------------------- *)
    destruct (ent_grow P' i fresh Hi Hlive
                ltac:(rewrite (Hdec i HiN), decide_True by reflexivity;
                      rewrite Hty'; exact Hlive)
                ltac:(rewrite (Hdec i HiN), decide_True by reflexivity;
                      exact Hents')
                Hfru
                ltac:(intros z Hz Hne;
                      rewrite (Hdec z ltac:(irng)), decide_False by exact Hne;
                      destruct (bv_unsigned (di_type (fs_dinode P sb z)) =? 0)
                        eqn:Ez; [reflexivity |];
                      destruct (Hunt z Hz Hne (proj1 (Z.eqb_neq _ _) Ez))
                        as (_ & _ & Hbl & _); exact Hbl))
      as (u'' & Hu'' & Hmem'').
    (* --- assemble ------------------------------------------------------ *)
    split.
    2:{ intros k Hk. fold P'.
        rewrite (Hdec i HiN), decide_True by reflexivity.
        exact (Hslot' k Hk). }
    exists sb. split.
    { rewrite (fs_parse_sb_ext P P' HsbU). exact Hp. }
    constructor.
    - exact Hsb.
    - apply fs_inodes_dwf_intro. intros z Hz Hnz'.
      rewrite (Hdec z ltac:(irng)) in Hnz' |- *.
      destruct (decide (z = i)) as [-> | Hne]; [exact Hdwf' |].
      destruct (Hunt z Hz Hne Hnz') as (_ & _ & _ & Hdwf).
      rewrite Hdwf. exact (dwf_bool_at z Hz Hnz').
    - exists u''. split; [exact Hu'' |].
      apply (bitmap_wf_of_set P' u''
               (fs_bmap_set BSIZE (P (sb_bmapstart sb)) ∪ {[fresh]}));
        [exact HbmB |].
      intros b Hb.
      rewrite elem_of_union, elem_of_singleton, (old_bit_iff b Hb).
      rewrite (Hmem'' b). tauto.
    - apply root_wf_meta.
      + apply Htypall. pose proof Hnin1. unfold ROOTINO. lia.
      + apply Hszall. pose proof Hnin1. unfold ROOTINO. lia.
      + apply Hdatall.
        * pose proof Hnin1. unfold ROOTINO. lia.
        * rewrite (fs_root_wf_type P sb HW7). unfold T_DIR_z. lia.
    - apply fs_dots_all_intro. intros z Hz Hdty.
      assert (Hdty0 : bv_unsigned (di_type (fs_dinode P sb z)) = T_DIR_z)
        by (rewrite <- (Htyp z Hz); exact Hdty).
      assert (Hzl : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
        by (rewrite Hdty0; unfold T_DIR_z; discriminate).
      apply (fs_dots_wf_win P P' z (fs_dinode P sb z)
               (fs_dinode P' sb z)).
      + rewrite (Hszall z Hz). reflexivity.
      + apply (dir_win_agree_blocks _ _ FS_MAXFILE);
          [intros k Hk; exact (Hdatall z Hz Hzl k Hk)
          | unfold FS_MAXFILE, BSIZE; lia].
      + apply (dir_win_agree_blocks _ _ FS_MAXFILE);
          [intros k Hk; exact (Hdatall z Hz Hzl k Hk)
          | unfold FS_MAXFILE, BSIZE; lia].
      + exact (dots_bool_at z Hz Hdty0).
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
        { exfalso. rewrite Hty' in Hfree. exact (Hlive Hfree). }
        apply (fs_region_nlink_free P sb nib z
                 (fs_region_wf_nlink P sb nib Hreg)); [lia | exact Hfree].
      + intros z Hz.
        rewrite (Hdec z ltac:(irng)).
        destruct (decide (z = i)) as [-> | Hne].
        * rewrite Hnl'.
          apply (fs_region_nlink_short P sb nib i
                   (fs_region_wf_nlink P sb nib Hreg)). lia.
        * apply (fs_region_nlink_short P sb nib z
                   (fs_region_wf_nlink P sb nib Hreg)). lia.
    - exists rd.
      split; [| split; [| split]].
      + intros z. rewrite (Hrd z).
        destruct (decide (0 <= z < sb_ninodes sb)) as [Hzr | Hzr].
        * rewrite (Htyp z Hzr).
          split; intros (A & B & C); (split; [exact A |]);
            (split; [exact B |]).
          -- apply (Hreach z). exact C.
          -- apply (Hreach z) in C. exact C.
        * split; intros (A & _); [lia | lia].
      + intros z Hz.
        destruct (proj1 (Hrd z) Hz) as (Hzr & Hzty & _).
        assert (Hzl : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
          by (rewrite Hzty; unfold T_DIR_z; discriminate).
        apply dir_ok_meta;
          [ exact Hz | exact (Hszall z Hzr)
          | intros k Hk; exact (Hdatall z Hzr Hzl k Hk) |].
        intros w Hw Hwl Hw0. exfalso. apply Hwl.
        rewrite <- (Htyp w Hw). exact Hw0.
      + intros z Hz. cbv zeta.
        rewrite (Hdec z ltac:(irng)).
        unfold fs_rtick. rewrite Hsupply.
        destruct (decide (z = i)) as [-> | Hne].
        * rewrite Hty', Hnl'. exact (Hlkg i Hz).
        * exact (Hlkg z Hz).
      + intros z Hz Hty0 Hnin.
        assert (Hty1 : bv_unsigned (di_type (fs_dinode P sb z)) = T_DIR_z)
          by (rewrite <- (Htyp z Hz); exact Hty0).
        assert (Hzl : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
          by (rewrite Hty1; unfold T_DIR_z; discriminate).
        apply (dots_only_meta P' (fs_dinode P sb z) (fs_dinode P' sb z)).
        * exact (fdi_size _ _ _ (dok_at z Hz Hzl)).
        * exact (Hszall z Hz).
        * intros k Hk. exact (Hdatall z Hz Hzl k Hk).
        * exact (Horph z Hz Hty1 Hnin).
  Qed.

End EffAllocBlock.

(* the [fs_durable_wf_view]-level wrappers -- the shape stage G2
   consumes: the invariant of the OLD view, the decode-level
   preconditions, the invariant of the updated view. *)

Lemma eff_alloc_file_block_wfv (P : Z -> list (bv 8)) (sb : fs_sb)
    (i : Z) (fbn : nat) (fresh : Z) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  (fbn < FS_MAXFILE)%nat ->
  fs_slot P (fs_dinode P sb i) fbn = 0 ->
  ((12 <= fbn)%nat ->
     bv_unsigned (di_addrs (fs_dinode P sb i) !!! 12%nat) <> 0) ->
  fs_data_start sb <= fresh < sb_size sb ->
  fs_bit (P (sb_bmapstart sb)) fresh = false ->
  fs_durable_wf_view (eff_alloc_file_block P sb i fbn fresh).
Proof.
  intros Hv Hp Hi Hlive HfbnM Hslot Hib Hfr Hbit.
  destruct Hv as (sb0 & Hp0 & Hsw).
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
  destruct HW45 as (u & Hu & Hbm).
  destruct Hregx as (nib & Hnibz & Hreg).
  destruct HW9 as (rd & Hrd & Hdok & Hlkg & Horph).
  assert (Hfru : fresh ∉ u).
  { destruct (fs_sb_ok_meta sb (fs_sb_wf_ok sb Hsb)) as (Hg1 & Hg2 & Hg3).
    destruct (fs_bitmap_wf_free P sb u fresh Hbm
                ltac:(unfold fs_data_start in *; lia) Hbit) as (_ & Hn).
    exact Hn. }
  apply (proj1 (eff_alloc_file_block_wf P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph i fbn fresh Hi Hlive HfbnM Hslot Hib Hfr Hfru)).
Qed.

(* the transport half, at the same premises *)
Lemma eff_alloc_file_block_slot (P : Z -> list (bv 8)) (sb : fs_sb)
    (i : Z) (fbn : nat) (fresh : Z) (k : nat) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  (fbn < FS_MAXFILE)%nat ->
  fs_slot P (fs_dinode P sb i) fbn = 0 ->
  ((12 <= fbn)%nat ->
     bv_unsigned (di_addrs (fs_dinode P sb i) !!! 12%nat) <> 0) ->
  fs_data_start sb <= fresh < sb_size sb ->
  fs_bit (P (sb_bmapstart sb)) fresh = false ->
  (k <= FS_MAXFILE)%nat ->
  fs_slot (eff_alloc_file_block P sb i fbn fresh)
    (fs_dinode (eff_alloc_file_block P sb i fbn fresh) sb i) k
  = if decide (k = fbn) then fresh else fs_slot P (fs_dinode P sb i) k.
Proof.
  intros Hv Hp Hi Hlive HfbnM Hslot Hib Hfr Hbit Hk.
  destruct Hv as (sb0 & Hp0 & Hsw).
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
  destruct HW45 as (u & Hu & Hbm).
  destruct Hregx as (nib & Hnibz & Hreg).
  destruct HW9 as (rd & Hrd & Hdok & Hlkg & Horph).
  assert (Hfru : fresh ∉ u).
  { destruct (fs_sb_ok_meta sb (fs_sb_wf_ok sb Hsb)) as (Hg1 & Hg2 & Hg3).
    destruct (fs_bitmap_wf_free P sb u fresh Hbm
                ltac:(unfold fs_data_start in *; lia) Hbit) as (_ & Hn).
    exact Hn. }
  exact (proj2 (eff_alloc_file_block_wf P sb Hp0 Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph i fbn fresh Hi Hlive HfbnM Hslot Hib Hfr Hfru) k Hk).
Qed.
