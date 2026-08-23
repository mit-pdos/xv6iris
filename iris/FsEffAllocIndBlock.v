(* FsEffAllocIndBlock.v -- durable-disk stage F2, effect 8: crossing a
   file's 12-block boundary, where bmap allocates TWO blocks in one
   transaction.

   WHY IT IS ONE EFFECT AND NOT TWO.  At [fbn = 12] the append needs an
   indirect block AND a data block, and there is no well-formed image
   between them: [FsImg.fio_ind_zero] says a file at [nblk <= 12] has
   indirect pointer 0, so an intermediate view carrying a nonzero
   [di_addrs !!! 12] at [nblk = 12] fails W3 -- and one carrying [nblk =
   13] with an all-zero indirect block fails [fio_ent].  The two
   allocations therefore land as ONE update of the committed view.  This
   is the same "no wf intermediate" argument that fused mkdir's dots
   block into [FsEffCreateEntry.eff_create_dir_entry].

   WHAT THE CODE WRITES ([ProofBmap.v]'s indirect head + tail):

       if((addr = ip->addrs[NDIRECT]) == 0){ addr = balloc(ip->dev);
                                             ip->addrs[NDIRECT] = addr; }
       bp = bread(ip->dev, addr);  a = (uint * )bp->data;
       if((addr = a[bn]) == 0){ addr = balloc(ip->dev);
                                a[bn] = addr; log_write(bp); }

   balloc bzeroes each block it hands back, so the indirect block reaches
   the log as [ind_bytes (bm_ent bmI)] with [bm_ent bmI = replicate
   NINDIRECT (bv_0 32)] ([InodeInv.blkmap_wf]'s "no indirect block => no
   entries" clause on the OLD record, carried through the pointer
   install), and bmap's own [log_write] then commits [ProofBmap]'s
   [ind_bytes (<[q := blk]> (bm_ent bmI))] at [q = fbn - NDIRECT = 0].
   The effect writes that composed content -- the bzeroed entry list with
   entry 0 replaced -- so a G2 consumer matches the op postcondition by
   [reflexivity].  The data block is bzeroed and never written again,
   i.e. [replicate BSIZE (bv_0 8)], the spelling
   [FsEffAllocBlock.eff_alloc_file_block] already uses. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import RiscvModelBytes.
Require Import BioDefs.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import BitmapEnc.
Require Import DirView.
Require Import FsTree.
Require Import FsImg.
Require Import FsWf.
Require Import FsEffBase.

Local Open Scope Z_scope.

Section EffAllocIndBlock.
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
  Local Notation node_at_meta := (node_at_meta P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation tickets_at_meta := (tickets_at_meta P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation dir_ok_meta := (dir_ok_meta P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation dots_only_meta := (dots_only_meta P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation root_wf_meta := (root_wf_meta P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).
  Local Notation ent_grow := (ent_grow P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph) (only parsing).

  (* THE INODE-REGION BOUND that every [Hdec] case split asks for; see
     [FsEffAllocBlock]'s copy and claude-notes/optimization.md. *)
  Local Ltac irng :=
    match goal with
    | H : 0 <= ?z < sb_ninodes sb |- 0 <= ?z < _ =>
        exact (iblk_z_range sb z H)
    | H : 0 < ?z < sb_ninodes sb |- 0 <= ?z < _ =>
        exact (iblk_z_range sb z
                 (conj (Z.lt_le_incl _ _ (proj1 H)) (proj2 H)))
    | _ => lia
    end.

  Local Lemma fs_le_at4_range (bs : list (bv 8)) (o : nat) :
    0 <= fs_le_at bs o 4 < 4294967296.
  Proof.
    unfold fs_le_at.
    pose proof (assemble_bytes_bound
                  ((fun j => bs !!! (o + j)%nat) <$> seq 0 4)) as Hb.
    rewrite length_fmap, length_seq in Hb.
    change (2 ^ (8 * Z.of_nat 4)) with 4294967296 in Hb. exact Hb.
  Qed.

  (* the DECODE of [BlockWords.ind_bytes]: what an image reads back out
     of a block the code laid down entry-wise.  [FsImg.
     fs_ind_bytes_round_trip] is the other direction. *)
  Local Lemma le_at_ind_bytes (l : list (bv 32)) (j : nat) :
    (j < length l)%nat ->
    fs_le_at (ind_bytes l) (4 * j)%nat 4 = bv_unsigned (l !!! j).
  Proof.
    intros Hj.
    assert (Hw : Z_to_bv 32 (fs_le_at (ind_bytes l) (4 * j)%nat 4)
                 = l !!! j).
    { apply fs_le_word_at. intros r Hr.
      rewrite list_lookup_total_alt, (ind_bytes_lookup l j r Hj Hr).
      reflexivity. }
    apply (f_equal bv_unsigned) in Hw.
    assert (Hm32 : bv_modulus 32 = 4294967296) by reflexivity.
    pose proof (fs_le_at4_range (ind_bytes l) (4 * j)%nat) as Hrng.
    rewrite Z_to_bv_small in Hw by lia. exact Hw.
  Qed.

  (* ==================================================================== *)
  (*  23.  EFFECT 8 -- ALLOCATING THE INDIRECT BLOCK ITSELF                *)
  (*                                                                       *)
  (*  bmap's boundary step, and under the beyond-size ruling it is ONE     *)
  (*  block, not two (durable-disk F3.2).  With [fdi_ind_zero] deleted the *)
  (*  state "the indirect block is allocated and bzeroed, no entry points  *)
  (*  anywhere yet" IS well-formed -- that is what forced F2's fused       *)
  (*  two-block effect and what no longer does -- so installing the first  *)
  (*  entry is just [eff_alloc_file_block] at [fbn = 12], whose own        *)
  (*  precondition ("the indirect block exists") this effect establishes.  *)
  (*  Its precondition is SLOT EMPTINESS at the indirect slot, i.e.        *)
  (*  [addrs[NDIRECT] = 0]; no size, no append equation.                   *)
  (* ==================================================================== *)

  Definition eff_alloc_ind_block (i : Z) (fresh_ind : Z)
    : Z -> list (bv 8) :=
    let dn := fs_dinode P sb i in
    fs_upd
      (fs_upd
         (eff_dinode P sb i
            (di_set_size_addr dn (di_size dn) 12 (Z_to_bv 32 fresh_ind)))
         (sb_bmapstart sb)
         (bm_bytes BSIZE
            (fs_bmap_set BSIZE (P (sb_bmapstart sb)) ∪ {[fresh_ind]})))
      fresh_ind (ind_bytes (replicate FS_NINDIRECT (bv_0 32))).

  Lemma eff_alloc_ind_block_wf (i : Z) (fresh_ind : Z) :
    0 <= i < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
    bv_unsigned (di_addrs (fs_dinode P sb i) !!! 12%nat) = 0 ->
    fs_data_start sb <= fresh_ind < sb_size sb ->
    fresh_ind ∉ u ->
    fs_durable_wf_view (eff_alloc_ind_block i fresh_ind)
    /\ (forall k : nat, (k <= FS_MAXFILE)%nat ->
          fs_slot (eff_alloc_ind_block i fresh_ind)
            (fs_dinode (eff_alloc_ind_block i fresh_ind) sb i) k
          = if decide (k = FS_MAXFILE) then fresh_ind
            else fs_slot P (fs_dinode P sb i) k).
  Proof.
    intros Hi Hlive Hibz Hfr Hfru.
    assert (HDM : (FS_NDIRECT + FS_NINDIRECT)%nat = FS_MAXFILE)
      by reflexivity.
    assert (Hm32 : bv_modulus 32 = 4294967296) by reflexivity.
    set (dn := fs_dinode P sb i) in *.
    set (dn' := di_set_size_addr dn (di_size dn) 12 (Z_to_bv 32 fresh_ind)).
    set (P' := eff_alloc_ind_block i fresh_ind).
    pose proof (dok_at i Hi Hlive) as Hdok_i. fold dn in Hdok_i.
    pose proof (fdi_size _ _ _ Hdok_i) as Hcap. fold dn in Hcap.
    pose proof (proj1 (bv_unsigned_in_range _ (di_size dn))) as Hsz0.
    destruct (fs_sb_ok_meta sb Hok) as (Hm1 & Hm2 & Hm3).
    pose proof (sbo_one_bitmap sb Hok) as Hone.
    pose proof Hnin_le as HninN.
    assert (HiN : 0 <= i < 16 * (sb_ninodes sb / 16 + 1)) by lia.
    destruct (iblock_bounds sb Hok i HiN) as (Hibb1 & Hibb2 & Hibb3).
    assert (Hfr0 : fresh_ind <> 0) by (unfold fs_data_start in *; lia).
    assert (Hfru32 : bv_unsigned (Z_to_bv 32 fresh_ind) = fresh_ind)
      by (apply Z_to_bv_small; unfold BSIZE_z in Hone; lia).
    (* no indirect block means the file is at most NDIRECT blocks long *)
    assert (Hnb_le : fs_nblk (bv_unsigned (di_size dn))
                     <= Z.of_nat FS_NDIRECT).
    { destruct (Z.le_gt_cases (fs_nblk (bv_unsigned (di_size dn)))
                  (Z.of_nat FS_NDIRECT)) as [Hle | Hgt]; [exact Hle |].
      exfalso. pose proof (fdi_ind _ _ _ Hdok_i Hgt).
      unfold fs_data_start in *. lia. }
    assert (Hoents : fs_ind_ents P dn = replicate FS_NINDIRECT 0)
      by (unfold fs_ind_ents; rewrite Hibz; reflexivity).
    (* --- the new record ------------------------------------------------ *)
    assert (Hty' : di_type dn' = di_type dn) by reflexivity.
    assert (Hnl' : di_nlink dn' = di_nlink dn) by reflexivity.
    assert (Hszz' : di_size dn' = di_size dn) by reflexivity.
    assert (Hwf' : dinode_wf dn')
      by (apply di_set_size_addr_wf; exact (fs_dinode_wf P sb i)).
    assert (Hlen13 : (12 < length (di_addrs dn))%nat).
    { pose proof (fs_dinode_wf P sb i) as Hwfo.
      unfold dinode_wf in Hwfo. fold dn in Hwfo. rewrite Hwfo. lia. }
    assert (Ha12' : di_addrs dn' !!! 12%nat = Z_to_bv 32 fresh_ind).
    { unfold dn', di_set_size_addr. cbn [di_addrs].
      exact (list_lookup_total_insert _ _ _ Hlen13). }
    assert (Hdirsame : forall k : nat, (k < FS_NDIRECT)%nat ->
              di_addrs dn' !!! k = di_addrs dn !!! k).
    { intros k Hk. unfold dn', di_set_size_addr. cbn [di_addrs].
      apply list_lookup_total_insert_ne. unfold FS_NDIRECT in Hk. lia. }
    (* --- the touched blocks -------------------------------------------- *)
    assert (HaE : forall b : Z,
              b <> fresh_ind -> b <> sb_bmapstart sb ->
              b <> IBLOCK (fs_inum_bv i) (sb_inodestart sb) ->
              P' b = P b).
    { intros b Hb1 Hb2 Hb3. unfold P', eff_alloc_ind_block. cbv zeta.
      fold dn.
      rewrite fs_upd_ne by exact Hb1.
      rewrite fs_upd_ne by exact Hb2.
      exact (eff_dinode_out sb _ _ _ _ Hb3). }
    assert (HsbU : P' SB_BNO = P SB_BNO).
    { apply HaE; unfold SB_BNO, fs_data_start in *; lia. }
    assert (HbmB : P' (sb_bmapstart sb)
                   = bm_bytes BSIZE
                       (fs_bmap_set BSIZE (P (sb_bmapstart sb))
                        ∪ {[fresh_ind]})).
    { unfold P', eff_alloc_ind_block. cbv zeta. fold dn.
      rewrite fs_upd_ne by (unfold fs_data_start in *; lia).
      apply fs_upd_at. }
    assert (HfrB : P' fresh_ind
                   = ind_bytes (replicate FS_NINDIRECT (bv_0 32))).
    { unfold P', eff_alloc_ind_block. cbv zeta. fold dn. apply fs_upd_at. }
    assert (Hdec : forall z : Z, 0 <= z < 16 * (sb_ninodes sb / 16 + 1) ->
              fs_dinode P' sb z
              = if decide (z = i) then dn' else fs_dinode P sb z).
    { intros z Hz.
      destruct (iblock_bounds sb Hok z Hz) as (Hz1 & Hz2 & Hz3).
      transitivity (fs_dinode (eff_dinode P sb i dn') sb z).
      - apply fs_dinode_ext. unfold P', eff_alloc_ind_block. cbv zeta.
        fold dn.
        rewrite fs_upd_ne by (unfold fs_data_start in Hfr; lia).
        rewrite fs_upd_ne by lia. reflexivity.
      - exact (eff_dinode_dec sb Hok P i dn' z Hwf' HiN Hz). }
    (* --- the fresh indirect block is bzeroed, so no entry moves -------- *)
    assert (Hnents : fs_ind_ents P' dn' = replicate FS_NINDIRECT 0).
    { unfold fs_ind_ents. rewrite Ha12', Hfru32.
      rewrite (proj2 (Z.eqb_neq fresh_ind 0) Hfr0).
      rewrite HfrB.
      apply list_eq. intros k. rewrite list_lookup_fmap.
      destruct (Nat.lt_ge_cases k FS_NINDIRECT) as [Hk | Hk].
      - rewrite (lookup_seq_lt 0 FS_NINDIRECT k Hk).
        cbn [fmap option_fmap option_map]. rewrite Nat.add_0_l.
        rewrite (le_at_ind_bytes (replicate FS_NINDIRECT (bv_0 32)) k
                   ltac:(rewrite length_replicate; exact Hk)).
        rewrite lookup_total_replicate_2 by exact Hk.
        rewrite (lookup_replicate_2 _ _ _ Hk). reflexivity.
      - rewrite (lookup_seq_ge 0 FS_NINDIRECT k Hk).
        symmetry. apply lookup_ge_None_2.
        rewrite length_replicate. exact Hk. }
    (* --- THE SLOT CHARACTERISATION ------------------------------------- *)
    assert (Hslot' : forall k : nat, (k <= FS_MAXFILE)%nat ->
              fs_slot P' dn' k
              = if decide (k = FS_MAXFILE) then fresh_ind
                else fs_slot P dn k).
    { intros k Hk.
      destruct (decide (k = FS_MAXFILE)) as [-> | HkM].
      { rewrite fs_slot_max, Ha12'. exact Hfru32. }
      assert (HkL : (k < FS_MAXFILE)%nat) by lia.
      rewrite (fs_slot_lt P' dn' k HkL), (fs_slot_lt P dn k HkL).
      unfold fs_blk_addr.
      destruct (Nat.ltb_spec k FS_NDIRECT) as [Hkd | Hkd].
      - rewrite (Hdirsame k Hkd). reflexivity.
      - rewrite Hnents, Hoents. reflexivity. }
    assert (Hslotmax : fs_slot P' dn' FS_MAXFILE = fresh_ind).
    { rewrite (Hslot' FS_MAXFILE ltac:(lia)), decide_True by reflexivity.
      reflexivity. }
    assert (Hslotne : forall k : nat, (k <= FS_MAXFILE)%nat ->
              k <> FS_MAXFILE -> fs_slot P' dn' k = fs_slot P dn k).
    { intros k Hk Hne.
      rewrite (Hslot' k Hk), decide_False by exact Hne. reflexivity. }
    (* --- the record's own sanity --------------------------------------- *)
    assert (Hdok' : fs_inode_dok P' sb dn').
    { constructor; rewrite ?Hty', ?Hszz'.
      - exact (fdi_type _ _ _ Hdok_i).
      - exact Hcap.
      - intros k Hk Hlt. rewrite (Hdirsame k Hk).
        exact (fdi_direct _ _ _ Hdok_i k Hk Hlt).
      - intros k Hk Hnz. rewrite (Hdirsame k Hk) in Hnz |- *.
        exact (fdi_direct_ok _ _ _ Hdok_i k Hk Hnz).
      - intros _. rewrite Ha12', Hfru32. exact Hfr.
      - intros Hgt. exfalso. lia.
      - intros j Hj Hlt. exfalso. lia.
      - intros j Hj Hnz. exfalso. apply Hnz.
        rewrite Hnents. apply lookup_total_replicate_2. exact Hj. }
    assert (Hdwf' : fs_inode_dwf P' sb dn' = true)
      by exact (fs_inode_dok_dwf P' sb dn' Hdok').
    (* --- the entry list gains exactly [fresh_ind] ---------------------- *)
    assert (Hents' : fs_inode_ents P' dn'
                     ≡ₚ (fs_inode_ents P dn ++ [fresh_ind])%list).
    { apply (fs_inode_ents_upd P P' dn dn' FS_MAXFILE fresh_ind);
        [ lia | exact Hfr0 | rewrite fs_slot_max; exact Hibz
        | exact Hslotmax | exact Hslotne ]. }
    (* --- THE DATA VIEW DOES NOT MOVE ----------------------------------- *)
    assert (Hdata_i : forall k : nat,
              fs_data_of P' dn' k = fs_data_of P dn k).
    { intros k. rewrite !fs_data_of_addr.
      destruct (Nat.lt_ge_cases k FS_MAXFILE) as [Hk | Hk].
      2:{ rewrite (fs_blk_addr_high P' dn' k Hk),
            (fs_blk_addr_high P dn k Hk).
          rewrite (proj2 (Z.eqb_neq 1 0) ltac:(lia)). exact HsbU. }
      rewrite <- (fs_slot_lt P' dn' k Hk), <- (fs_slot_lt P dn k Hk).
      rewrite (Hslotne k ltac:(lia) ltac:(lia)).
      destruct (fs_slot P dn k =? 0) eqn:E; [reflexivity |].
      assert (Enz : fs_slot P dn k <> 0) by (apply Z.eqb_neq; exact E).
      assert (Hin : fs_slot P dn k ∈ fs_inode_ents P dn)
        by (apply (fs_inode_ents_slot P dn); [lia | exact Enz]).
      pose proof (blocks_range i _ Hi Hlive Hin) as Hbr.
      apply HaE.
      - intros Hc. apply Hfru. rewrite <- Hc.
        exact (used_elem i _ Hi Hlive Hin).
      - unfold fs_data_start in *. lia.
      - unfold fs_data_start in *. lia. }
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
      - unfold fs_data_start in *. lia. }
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
    (* --- W4/W5 ---------------------------------------------------------- *)
    destruct (ent_grow P' i fresh_ind Hi Hlive
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
    (* --- assemble ------------------------------------------------------- *)
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
               (fs_bmap_set BSIZE (P (sb_bmapstart sb)) ∪ {[fresh_ind]}));
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

End EffAllocIndBlock.

(* the [fs_durable_wf_view]-level wrapper -- the shape stage G2 consumes:
   the invariant of the OLD view, the decode-level preconditions (the two
   fresh blocks arrive as balloc's own postcondition, a CLEARED bitmap
   bit), the invariant of the updated view. *)

Lemma eff_alloc_ind_block_wfv (P : Z -> list (bv 8)) (sb : fs_sb)
    (i : Z) (fresh_ind : Z) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  bv_unsigned (di_addrs (fs_dinode P sb i) !!! 12%nat) = 0 ->
  fs_data_start sb <= fresh_ind < sb_size sb ->
  fs_bit (P (sb_bmapstart sb)) fresh_ind = false ->
  fs_durable_wf_view (eff_alloc_ind_block P sb i fresh_ind).
Proof.
  intros Hv Hp Hi Hlive Hibz Hfr Hbit.
  destruct Hv as (sb0 & Hp0 & Hsw).
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
  destruct HW45 as (u & Hu & Hbm).
  destruct Hregx as (nib & Hnibz & Hreg).
  destruct HW9 as (rd & Hrd & Hdok & Hlkg & Horph).
  assert (Hfru : fresh_ind ∉ u).
  { destruct (fs_sb_ok_meta sb (fs_sb_wf_ok sb Hsb)) as (Hg1 & Hg2 & Hg3).
    destruct (fs_bitmap_wf_free P sb u fresh_ind Hbm
                ltac:(unfold fs_data_start in *; lia) Hbit) as (_ & Hn).
    exact Hn. }
  apply (proj1 (eff_alloc_ind_block_wf P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph i fresh_ind Hi Hlive Hibz Hfr Hfru)).
Qed.

Lemma eff_alloc_ind_block_slot (P : Z -> list (bv 8)) (sb : fs_sb)
    (i : Z) (fresh_ind : Z) (k : nat) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  bv_unsigned (di_addrs (fs_dinode P sb i) !!! 12%nat) = 0 ->
  fs_data_start sb <= fresh_ind < sb_size sb ->
  fs_bit (P (sb_bmapstart sb)) fresh_ind = false ->
  (k <= FS_MAXFILE)%nat ->
  fs_slot (eff_alloc_ind_block P sb i fresh_ind)
    (fs_dinode (eff_alloc_ind_block P sb i fresh_ind) sb i) k
  = if decide (k = FS_MAXFILE) then fresh_ind
    else fs_slot P (fs_dinode P sb i) k.
Proof.
  intros Hv Hp Hi Hlive Hibz Hfr Hbit Hk.
  destruct Hv as (sb0 & Hp0 & Hsw).
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
  destruct HW45 as (u & Hu & Hbm).
  destruct Hregx as (nib & Hnibz & Hreg).
  destruct HW9 as (rd & Hrd & Hdok & Hlkg & Horph).
  assert (Hfru : fresh_ind ∉ u).
  { destruct (fs_sb_ok_meta sb (fs_sb_wf_ok sb Hsb)) as (Hg1 & Hg2 & Hg3).
    destruct (fs_bitmap_wf_free P sb u fresh_ind Hbm
                ltac:(unfold fs_data_start in *; lia) Hbit) as (_ & Hn).
    exact Hn. }
  exact (proj2 (eff_alloc_ind_block_wf P sb Hp0 Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph i fresh_ind Hi Hlive Hibz Hfr Hfru) k Hk).
Qed.
