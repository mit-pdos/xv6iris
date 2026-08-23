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

Section EffAllocIndBlock.
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

  Local Lemma omap_none {A B : Type} (f : A -> option B) (l : list A) :
    (forall x : A, x ∈ l -> f x = None) -> omap f l = [].
  Proof.
    induction l as [| a l IH]; intros H; [reflexivity |].
    cbn [omap list_omap].
    rewrite (H a (elem_of_list_here a l)).
    apply IH. intros x Hx. apply H, elem_of_list_further, Hx.
  Qed.

  (* SWAPPING ONE SEGMENT OF THE USED-BLOCK JOIN.  The only thing the
     replacement segment may add is blocks that are not used at all, and
     that is what keeps the join duplicate-free. *)
  Local Lemma NoDup_seg_swap (A M B L new : list Z) :
    NoDup (A ++ L ++ B)%list ->
    NoDup M ->
    (forall x : Z, x ∈ M -> x ∈ L \/ x ∈ new) ->
    (forall x : Z, x ∈ new -> x ∉ u) ->
    (forall x : Z, x ∈ (A ++ L ++ B)%list -> x ∈ u) ->
    NoDup (A ++ M ++ B)%list.
  Proof.
    intros Hnd0 HndM Hsub Hnew Hu0.
    apply stdpp.list_relations.NoDup_app in Hnd0 as (HA & HdisjA & Hnd1).
    apply stdpp.list_relations.NoDup_app in Hnd1 as (HL & HdisjL & HB).
    apply stdpp.list_relations.NoDup_app.
    split; [exact HA |]. split.
    - intros x Hx Hx'. apply elem_of_app in Hx' as [Hx' | Hx'].
      + destruct (Hsub x Hx') as [Hin | Hin].
        * apply (HdisjA x Hx). apply elem_of_app. left. exact Hin.
        * apply (Hnew x Hin), Hu0, elem_of_app. left. exact Hx.
      + apply (HdisjA x Hx). apply elem_of_app. right. exact Hx'.
    - apply stdpp.list_relations.NoDup_app.
      split; [exact HndM |]. split; [| exact HB].
      intros x Hx Hx'. destruct (Hsub x Hx) as [Hin | Hin].
      + exact (HdisjL x Hin Hx').
      + apply (Hnew x Hin), Hu0, elem_of_app. right.
        apply elem_of_app. right. exact Hx'.
  Qed.

  (* the used set after one live inode's segment grows by TWO fresh
     blocks, one at each end (the indirect block heads the segment, the
     new data block ends it -- [FsImg.fs_inode_blocks]'s layout) *)
  Local Lemma used_grow2 (P' : Z -> list (bv 8)) (i a b : Z) :
    0 <= i < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
    bv_unsigned (di_type (fs_dinode P' sb i)) <> 0 ->
    fs_inode_blocks P' (fs_dinode P' sb i)
    = (a :: (fs_inode_blocks P (fs_dinode P sb i) ++ [b]))%list ->
    a ∉ u -> b ∉ u -> a <> b ->
    (forall z : Z, 0 <= z < sb_ninodes sb -> z <> i ->
       (if bv_unsigned (di_type (fs_dinode P' sb z)) =? 0 then []
        else fs_inode_blocks P' (fs_dinode P' sb z))
       = (if bv_unsigned (di_type (fs_dinode P sb z)) =? 0 then []
          else fs_inode_blocks P (fs_dinode P sb z))) ->
    exists u'' : gset Z,
      fs_used_set P' sb = Some u''
      /\ (forall c : Z, c ∈ u'' <-> (c ∈ u \/ c = a \/ c = b)).
  Proof.
    intros Hi Hlv Hlv' Hblk Hau Hbu Hab Hsame.
    set (n := Z.to_nat (sb_ninodes sb)).
    set (F := fun x : nat =>
                let dn0 := fs_dinode P sb (Z.of_nat x) in
                if bv_unsigned (di_type dn0) =? 0 then []
                else fs_inode_blocks P dn0).
    set (G := fun x : nat =>
                let dn0 := fs_dinode P' sb (Z.of_nat x) in
                if bv_unsigned (di_type dn0) =? 0 then []
                else fs_inode_blocks P' dn0).
    assert (HFold : fs_used_blocks P sb = mjoin (F <$> seq 0 n))
      by reflexivity.
    assert (HGold : fs_used_blocks P' sb = mjoin (G <$> seq 0 n))
      by reflexivity.
    assert (HFi : F (Z.to_nat i)
                  = fs_inode_blocks P (fs_dinode P sb i)).
    { unfold F. cbv zeta. rewrite Z2Nat.id by lia.
      rewrite (proj2 (Z.eqb_neq _ _) Hlv). reflexivity. }
    assert (HGi : G (Z.to_nat i)
                  = (a :: (fs_inode_blocks P (fs_dinode P sb i)
                           ++ [b]))%list).
    { unfold G. cbv zeta. rewrite Z2Nat.id by lia.
      rewrite (proj2 (Z.eqb_neq _ _) Hlv'). exact Hblk. }
    assert (Hext : forall x : nat, x <> Z.to_nat i -> (x < n)%nat ->
              G x = F x).
    { intros x Hx Hxn. unfold G, F. cbv zeta.
      apply Hsame; [unfold n in Hxn; lia | lia]. }
    set (LA := mjoin (F <$> seq 0 (Z.to_nat i))).
    set (LB := mjoin (F <$> seq (S (Z.to_nat i)) (n - S (Z.to_nat i)))).
    set (L := fs_inode_blocks P (fs_dinode P sb i)).
    assert (HsplF : mjoin (F <$> seq 0 n) = (LA ++ L ++ LB)%list).
    { unfold LA, L, LB.
      rewrite (mjoin_seq_split F n (Z.to_nat i)) by (unfold n; lia).
      rewrite HFi. reflexivity. }
    assert (HsplG : mjoin (G <$> seq 0 n)
                    = (LA ++ (a :: (L ++ [b])) ++ LB)%list).
    { unfold LA, L, LB.
      rewrite (mjoin_seq_split G n (Z.to_nat i)) by (unfold n; lia).
      rewrite HGi.
      rewrite (tick_mjoin_ext F G 0 (Z.to_nat i))
        by (intros x Hx; apply Hext; lia).
      rewrite (tick_mjoin_ext F G (S (Z.to_nat i)) (n - S (Z.to_nat i)))
        by (intros x Hx; apply Hext; lia).
      reflexivity. }
    assert (Hold_mem : forall c : Z,
              c ∈ mjoin (F <$> seq 0 n) <-> c ∈ u).
    { intros c. rewrite (fs_used_set_elem P sb u c Hu).
      rewrite HFold. reflexivity. }
    assert (Hu0 : forall c : Z, c ∈ (LA ++ L ++ LB)%list -> c ∈ u).
    { intros c Hc. apply Hold_mem. rewrite HsplF. exact Hc. }
    assert (HndL : NoDup (LA ++ L ++ LB)%list).
    { pose proof Hnd as Hnd1. rewrite HFold, HsplF in Hnd1. exact Hnd1. }
    assert (HaL : a ∉ L).
    { intros Hc. apply Hau, Hu0, elem_of_app. right.
      apply elem_of_app. left. exact Hc. }
    assert (HbL : b ∉ L).
    { intros Hc. apply Hbu, Hu0, elem_of_app. right.
      apply elem_of_app. left. exact Hc. }
    assert (HndM : NoDup (a :: (L ++ [b]))%list).
    { apply NoDup_cons_2.
      { intros Hc. apply elem_of_app in Hc as [Hc | Hc].
        - exact (HaL Hc).
        - apply elem_of_list_singleton in Hc. exact (Hab Hc). }
      apply stdpp.list_relations.NoDup_app.
      apply stdpp.list_relations.NoDup_app in HndL as (_ & _ & HndLB).
      apply stdpp.list_relations.NoDup_app in HndLB as (HndL0 & _ & _).
      split; [exact HndL0 |]. split.
      - intros x Hx Hx'. apply elem_of_list_singleton in Hx'. subst x.
        exact (HbL Hx).
      - apply NoDup_cons_2; [| apply NoDup_nil_2].
        intros Hc. exact (proj1 (elem_of_nil b) Hc). }
    assert (Hnd' : NoDup (fs_used_blocks P' sb)).
    { rewrite HGold, HsplG.
      apply (NoDup_seg_swap LA (a :: (L ++ [b])) LB L [a; b]);
        [exact HndL | exact HndM | | | exact Hu0].
      - intros x Hx. apply elem_of_cons in Hx as [-> | Hx].
        + right. apply elem_of_list_here.
        + apply elem_of_app in Hx as [Hx | Hx]; [left; exact Hx |].
          apply elem_of_list_singleton in Hx. subst x.
          right. apply elem_of_list_further, elem_of_list_here.
      - intros x Hx. apply elem_of_cons in Hx as [-> | Hx];
          [exact Hau |].
        apply elem_of_list_singleton in Hx. subst x. exact Hbu. }
    destruct (gset_nodup_of_NoDup (fs_used_blocks P' sb) Hnd')
      as (u'' & Hu'').
    exists u''. split; [exact Hu'' |].
    intros c.
    rewrite (gset_nodup_set _ _ Hu'' c).
    rewrite HGold, HsplG.
    rewrite <- (Hold_mem c). rewrite HsplF.
    rewrite !elem_of_app, elem_of_cons, elem_of_app,
      elem_of_list_singleton.
    tauto.
  Qed.

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
  (*  EFFECT 8 -- THE FUSED INDIRECT-BLOCK ALLOCATION                      *)
  (*                                                                       *)
  (*  The append at [fbn = 12]: the inode record gains the indirect        *)
  (*  pointer and the new size, the bitmap gains BOTH bits, the fresh      *)
  (*  data block is bzeroed, and the fresh indirect block carries the      *)
  (*  bzeroed entry list with entry 0 pointing at the data block.         *)
  (* ==================================================================== *)

  Definition eff_alloc_ind_block (i : Z) (fresh_ind fresh_data sz' : Z)
    : Z -> list (bv 8) :=
    let dn := fs_dinode P sb i in
    fs_upd
      (fs_upd
         (fs_upd
            (eff_dinode P sb i
               (di_set_size_addr dn (Z_to_bv 32 sz') 12
                  (Z_to_bv 32 fresh_ind)))
            (sb_bmapstart sb)
            (bm_bytes BSIZE
               (fs_bmap_set BSIZE (P (sb_bmapstart sb))
                ∪ {[fresh_ind]} ∪ {[fresh_data]})))
         fresh_data (replicate BSIZE (bv_0 8)))
      fresh_ind
      (ind_bytes (<[0%nat := Z_to_bv 32 fresh_data]>
                    (replicate FS_NINDIRECT (bv_0 32)))).

  Lemma eff_alloc_ind_block_wf (i : Z) (fresh_ind fresh_data sz' : Z) :
    0 <= i < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
    Z.of_nat 12 = fs_nblk (bv_unsigned (di_size (fs_dinode P sb i))) ->
    fs_nblk sz' = 13 ->
    sz' <= Z.of_nat FS_MAXFILE * BSIZE_z ->
    (bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z ->
       (16 | sz')
       /\ bv_unsigned (di_size (fs_dinode P sb i))
          = Z.of_nat 12 * BSIZE_z) ->
    fs_data_start sb <= fresh_ind < sb_size sb ->
    fs_data_start sb <= fresh_data < sb_size sb ->
    fresh_ind <> fresh_data ->
    fresh_ind ∉ u -> fresh_data ∉ u ->
    fs_durable_wf_view (eff_alloc_ind_block i fresh_ind fresh_data sz').
  Proof.
    intros Hi Hlive Hfbn Hnb' Hcap' Hdirsz Hfri Hfrd Hfrne Hfriu Hfrdu.
    assert (Hm32 : bv_modulus 32 = 4294967296) by reflexivity.
    destruct (fs_sb_ok_meta sb Hok) as (Hm1 & Hm2 & Hm3).
    pose proof (sbo_one_bitmap sb Hok) as Hone.
    set (dn := fs_dinode P sb i) in *.
    set (szo := bv_unsigned (di_size dn)) in *.
    set (P' := eff_alloc_ind_block i fresh_ind fresh_data sz').
    pose proof (dok_at i Hi Hlive) as Hdok_i. fold dn in Hdok_i.
    pose proof (fdi_size _ _ _ Hdok_i) as Hcapo. fold dn in Hcapo.
    pose proof (proj1 (bv_unsigned_in_range _ (di_size dn))) as Hsz0.
    assert (Hszle : szo <= sz').
    { destruct (Z.le_gt_cases szo sz') as [Hle | Hgt]; [exact Hle |].
      exfalso.
      assert (Hmono : fs_nblk sz' <= fs_nblk szo).
      { unfold fs_nblk. apply Z.div_le_mono; unfold BSIZE_z; lia. }
      lia. }
    assert (Hsz'0 : 0 <= sz') by lia.
    assert (Hfri0 : fresh_ind <> 0)
      by (unfold fs_data_start in *; lia).
    assert (Hfrd0 : fresh_data <> 0)
      by (unfold fs_data_start in *; lia).
    assert (Hfriu32 : bv_unsigned (Z_to_bv 32 fresh_ind) = fresh_ind).
    { apply Z_to_bv_small. unfold BSIZE_z in Hone. lia. }
    assert (Hfrdu32 : bv_unsigned (Z_to_bv 32 fresh_data) = fresh_data).
    { apply Z_to_bv_small. unfold BSIZE_z in Hone. lia. }
    assert (Hsz'u32 : bv_unsigned (Z_to_bv 32 sz') = sz').
    { apply Z_to_bv_small. unfold FS_MAXFILE, BSIZE_z in Hcap'. lia. }
    pose proof Hnin_le as HninN.
    assert (HiN : 0 <= i < 16 * (sb_ninodes sb / 16 + 1)) by lia.
    destruct (iblock_bounds sb Hok i HiN) as (Hibi1 & Hibi2 & Hibi3).
    (* the OLD record has no indirect block -- that is what forbids a wf
       intermediate, and what makes the old entry list all zeroes *)
    assert (Hibz : bv_unsigned (di_addrs dn !!! 12%nat) = 0).
    { apply (fdi_ind_zero _ _ _ Hdok_i). fold szo.
      unfold FS_NDIRECT. lia. }
    assert (Hoents0 : fs_ind_ents P dn = replicate FS_NINDIRECT 0).
    { unfold fs_ind_ents. rewrite Hibz. reflexivity. }
    (* the new record *)
    set (dn' := di_set_size_addr dn (Z_to_bv 32 sz') 12
                  (Z_to_bv 32 fresh_ind)).
    assert (Hty' : di_type dn' = di_type dn) by reflexivity.
    assert (Hnl' : di_nlink dn' = di_nlink dn) by reflexivity.
    assert (Hsz'u : bv_unsigned (di_size dn') = sz') by exact Hsz'u32.
    assert (Hwf' : dinode_wf dn')
      by (apply di_set_size_addr_wf, fs_dinode_wf).
    (* the touched blocks *)
    assert (HaE : forall b : Z,
              b <> fresh_ind -> b <> fresh_data ->
              b <> sb_bmapstart sb ->
              b <> IBLOCK (fs_inum_bv i) (sb_inodestart sb) ->
              P' b = P b).
    { intros b Hb1 Hb2 Hb3 Hb4. unfold P', eff_alloc_ind_block.
      cbv zeta. fold dn.
      rewrite fs_upd_ne by exact Hb1.
      rewrite fs_upd_ne by exact Hb2.
      rewrite fs_upd_ne by exact Hb3.
      exact (eff_dinode_out sb _ _ _ _ Hb4). }
    assert (HsbU : P' SB_BNO = P SB_BNO).
    { apply HaE; unfold SB_BNO, fs_data_start in *; lia. }
    assert (HbmB : P' (sb_bmapstart sb)
                   = bm_bytes BSIZE
                       (fs_bmap_set BSIZE (P (sb_bmapstart sb))
                        ∪ {[fresh_ind]} ∪ {[fresh_data]})).
    { unfold P', eff_alloc_ind_block. cbv zeta. fold dn.
      rewrite fs_upd_ne by (unfold fs_data_start in *; lia).
      rewrite fs_upd_ne by (unfold fs_data_start in *; lia).
      apply fs_upd_at. }
    assert (HfrdB : P' fresh_data = replicate BSIZE (bv_0 8)).
    { unfold P', eff_alloc_ind_block. cbv zeta. fold dn.
      rewrite fs_upd_ne by (intros Hc; exact (Hfrne (eq_sym Hc))).
      apply fs_upd_at. }
    assert (HfriB : P' fresh_ind
                    = ind_bytes (<[0%nat := Z_to_bv 32 fresh_data]>
                                   (replicate FS_NINDIRECT (bv_0 32)))).
    { unfold P', eff_alloc_ind_block. cbv zeta. fold dn. apply fs_upd_at. }
    assert (Hdec : forall z : Z, 0 <= z < 16 * (sb_ninodes sb / 16 + 1) ->
              fs_dinode P' sb z
              = if decide (z = i) then dn' else fs_dinode P sb z).
    { intros z Hz.
      destruct (iblock_bounds sb Hok z Hz) as (Hz1 & Hz2 & Hz3).
      transitivity (fs_dinode (eff_dinode P sb i dn') sb z).
      - apply fs_dinode_ext. unfold P', eff_alloc_ind_block. cbv zeta.
        fold dn.
        rewrite fs_upd_ne by (unfold fs_data_start in Hfri; lia).
        rewrite fs_upd_ne by (unfold fs_data_start in Hfrd; lia).
        rewrite fs_upd_ne by lia.
        reflexivity.
      - exact (eff_dinode_dec sb Hok P i dn' z Hwf' HiN Hz). }
    (* the block map: slot 12 gains [fresh_data], nothing else moves *)
    assert (Hents' : forall j : nat, (j < FS_NINDIRECT)%nat ->
              fs_ind_ents P' dn' !!! j
              = if decide (j = 0%nat) then fresh_data else 0).
    { intros j Hj.
      assert (Ha12 : bv_unsigned (di_addrs dn' !!! 12%nat) = fresh_ind).
      { unfold dn', di_set_size_addr. cbn [di_addrs].
        rewrite list_lookup_total_insert
          by (pose proof (fs_dinode_wf P sb i) as Hwfo;
              unfold dinode_wf in Hwfo; fold dn in Hwfo;
              rewrite Hwfo; lia).
        exact Hfriu32. }
      unfold fs_ind_ents. rewrite Ha12.
      rewrite (proj2 (Z.eqb_neq fresh_ind 0) Hfri0).
      rewrite list_lookup_total_alt, list_lookup_fmap.
      rewrite (lookup_seq_lt 0 FS_NINDIRECT j Hj).
      cbn [fmap option_fmap option_map default from_option id].
      rewrite Nat.add_0_l, HfriB.
      assert (Hlen : length (<[0%nat := Z_to_bv 32 fresh_data]>
                               (replicate FS_NINDIRECT (bv_0 32)))
                     = FS_NINDIRECT)
        by (rewrite length_insert, length_replicate; reflexivity).
      rewrite (le_at_ind_bytes _ j ltac:(rewrite Hlen; exact Hj)).
      destruct (decide (j = 0%nat)) as [-> | Hjne].
      - rewrite list_lookup_total_insert
          by (rewrite length_replicate; unfold FS_NINDIRECT; lia).
        exact Hfrdu32.
      - rewrite list_lookup_total_insert_ne
          by (intros Hc; exact (Hjne (eq_sym Hc))).
        rewrite lookup_total_replicate_2 by exact Hj.
        reflexivity. }
    assert (Haddr' : forall x : nat, (x < 13)%nat ->
              di_addrs dn' !!! x
              = if decide (x = 12%nat) then Z_to_bv 32 fresh_ind
                else di_addrs dn !!! x).
    { intros x Hx. unfold dn', di_set_size_addr. cbn [di_addrs].
      destruct (decide (x = 12%nat)) as [-> | Hne].
      - apply list_lookup_total_insert.
        pose proof (fs_dinode_wf P sb i) as Hwfo.
        unfold dinode_wf in Hwfo. fold dn in Hwfo. rewrite Hwfo. lia.
      - apply list_lookup_total_insert_ne.
        intros Hc. exact (Hne (eq_sym Hc)). }
    assert (Hbm_at : forall k0 : nat, k0 <> 12%nat ->
              fs_blk_addr P' dn' k0 = fs_blk_addr P dn k0).
    { intros k0 Hk0.
      unfold fs_blk_addr.
      destruct (Nat.ltb_spec k0 FS_NDIRECT) as [Hk0d | Hk0d].
      - rewrite (Haddr' k0 ltac:(unfold FS_NDIRECT in Hk0d; lia)).
        rewrite decide_False by (unfold FS_NDIRECT in Hk0d; lia).
        reflexivity.
      - destruct (Nat.lt_ge_cases (k0 - FS_NDIRECT) FS_NINDIRECT)
          as [Hk0i | Hk0i].
        + rewrite (Hents' (k0 - FS_NDIRECT)%nat Hk0i).
          rewrite decide_False by (unfold FS_NDIRECT in *; lia).
          rewrite Hoents0, lookup_total_replicate_2 by exact Hk0i.
          reflexivity.
        + rewrite !list_lookup_total_alt.
          rewrite !lookup_ge_None_2; [reflexivity | |];
            rewrite fs_ind_ents_length; exact Hk0i. }
    assert (Hbm_12 : fs_blk_addr P' dn' 12%nat = fresh_data).
    { unfold fs_blk_addr.
      rewrite (proj2 (Nat.ltb_ge 12 FS_NDIRECT) ltac:(unfold FS_NDIRECT; lia)).
      rewrite (Hents' (12 - FS_NDIRECT)%nat
                 ltac:(unfold FS_NDIRECT, FS_NINDIRECT; lia)).
      rewrite decide_True; [reflexivity | unfold FS_NDIRECT; reflexivity]. }
    assert (Hfriok : fs_addr_ok sb fresh_ind = true).
    { unfold fs_addr_ok. apply andb_true_iff.
      split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
    assert (Hfrdok : fs_addr_ok sb fresh_data = true).
    { unfold fs_addr_ok. apply andb_true_iff.
      split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia]. }
    assert (Hdwf' : fs_inode_dwf P' sb dn' = true).
    { unfold fs_inode_dwf. cbv zeta.
      rewrite Hsz'u, Hnb', Hty'.
      apply andb_true_iff. split; [| apply forallb_seq_intro].
      2:{ intros j Hj. cbv beta zeta.
          rewrite (Hents' j Hj).
          destruct (decide (j = 0%nat)) as [-> | Hjne].
          - rewrite (proj2 (Z.ltb_lt _ _)) by (unfold FS_NDIRECT; lia).
            exact Hfrdok.
          - rewrite (proj2 (Z.ltb_ge _ _))
              by (assert (j <> 0%nat) by exact Hjne;
                  unfold FS_NDIRECT; lia).
            reflexivity. }
      apply andb_true_iff. split.
      2:{ (* the indirect cell *)
          rewrite (Haddr' 12%nat ltac:(lia)).
          rewrite decide_True by reflexivity.
          rewrite (proj2 (Z.leb_gt _ _)) by (unfold FS_NDIRECT; lia).
          rewrite Hfriu32. exact Hfriok. }
      apply andb_true_iff. split; [| apply forallb_seq_intro].
      2:{ intros x Hx. cbv beta zeta.
          rewrite (Haddr' x ltac:(unfold FS_NDIRECT in Hx; lia)).
          rewrite decide_False by (unfold FS_NDIRECT in Hx; lia).
          rewrite (proj2 (Z.ltb_lt _ _)) by (unfold FS_NDIRECT in Hx; lia).
          apply (proj2 (fs_addr_ok_spec sb _)).
          apply (fdi_direct _ _ _ Hdok_i x Hx). fold szo.
          unfold FS_NDIRECT in Hx. lia. }
      apply andb_true_iff. split.
      - destruct (fdi_type _ _ _ Hdok_i) as [Ht | [Ht | Ht]];
          fold dn in Ht; rewrite Ht; reflexivity.
      - apply Z.leb_le. exact Hcap'. }
    assert (Hblk' : fs_inode_blocks P' dn'
                    = (fresh_ind :: (fs_inode_blocks P dn ++ [fresh_data]))%list).
    { unfold fs_inode_blocks. cbv zeta.
      rewrite Hsz'u, Hnb'. fold szo. rewrite <- Hfbn.
      rewrite (proj2 (Z.ltb_lt (Z.of_nat FS_NDIRECT) 13))
        by (unfold FS_NDIRECT; lia).
      rewrite (proj2 (Z.ltb_ge (Z.of_nat FS_NDIRECT) (Z.of_nat 12)))
        by (unfold FS_NDIRECT; lia).
      assert (Hm1' : Z.to_nat (Z.min 13 (Z.of_nat FS_NDIRECT)) = 12%nat)
        by (unfold FS_NDIRECT; lia).
      assert (Hm2' : Z.to_nat (Z.min (Z.of_nat 12) (Z.of_nat FS_NDIRECT))
                     = 12%nat)
        by (unfold FS_NDIRECT; lia).
      assert (Hz1 : Z.to_nat (13 - Z.of_nat FS_NDIRECT) = 1%nat)
        by (unfold FS_NDIRECT; lia).
      assert (Hz2 : Z.to_nat (Z.of_nat 12 - Z.of_nat FS_NDIRECT) = 0%nat)
        by (unfold FS_NDIRECT; lia).
      rewrite Hm1', Hm2', Hz1, Hz2.
      rewrite (Haddr' 12%nat ltac:(lia)).
      rewrite decide_True by reflexivity.
      rewrite Hfriu32.
      cbn [seq fmap list_fmap].
      rewrite !app_nil_l, !app_nil_r.
      rewrite (Hents' 0%nat ltac:(unfold FS_NINDIRECT; lia)).
      rewrite decide_True by reflexivity.
      cbn [app].
      (* the direct chunk is unmoved: [di_addrs (fs_dinode ...)] is a
         13-element literal, so the twelve reads convert *)
      f_equal. }
    (* the content blocks *)
    assert (Hdata_old : forall k0 : nat, k0 <> 12%nat ->
              fs_data_of P' dn' k0 = fs_data_of P dn k0).
    { intros k0 Hk0.
      rewrite !fs_data_of_addr, (Hbm_at k0 Hk0).
      destruct (fs_blk_addr P dn k0 =? 0) eqn:E; [reflexivity |].
      pose proof (proj1 (Z.eqb_neq _ _) E) as Hnz.
      destruct (Nat.lt_ge_cases k0 FS_MAXFILE) as [Hk0M | Hk0M].
      - assert (Hin' : fs_blk_addr P dn k0 ∈ fs_inode_blocks P dn).
        { rewrite <- (fs_slot_blk dn k0 Hk0M).
          apply (fs_slot_elem_dok P sb dn); [exact Hdok_i | lia |].
          rewrite (fs_slot_blk dn k0 Hk0M). exact Hnz. }
        pose proof (blocks_range i _ Hi Hlive Hin') as Hbr.
        apply HaE.
        + intros Hc. apply Hfriu. rewrite <- Hc.
          exact (used_elem i _ Hi Hlive Hin').
        + intros Hc. apply Hfrdu. rewrite <- Hc.
          exact (used_elem i _ Hi Hlive Hin').
        + unfold fs_data_start in *; lia.
        + unfold fs_data_start in *; lia.
      - rewrite (fs_blk_addr_high P dn k0 Hk0M). exact HsbU. }
    assert (Hdata_12 : fs_data_of P' dn' 12%nat = replicate BSIZE (bv_0 8)).
    { rewrite fs_data_of_addr, Hbm_12.
      rewrite (proj2 (Z.eqb_neq fresh_data 0) Hfrd0). exact HfrdB. }
    assert (Hunt : forall z : Z, 0 <= z < sb_ninodes sb -> z <> i ->
              bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
              fs_ind_ents P' (fs_dinode P sb z)
              = fs_ind_ents P (fs_dinode P sb z)
              /\ (forall k0 : nat,
                    fs_data_of P' (fs_dinode P sb z) k0
                    = fs_data_of P (fs_dinode P sb z) k0)
              /\ fs_inode_blocks P' (fs_dinode P sb z)
                 = fs_inode_blocks P (fs_dinode P sb z)
              /\ fs_inode_dwf P' sb (fs_dinode P sb z)
                 = fs_inode_dwf P sb (fs_dinode P sb z)).
    { intros z Hz Hni' Hnz. apply inode_untouched; try assumption.
      intros b Hb. apply HaE.
      - intros ->. apply Hfriu. exact (used_elem z _ Hz Hnz Hb).
      - intros ->. apply Hfrdu. exact (used_elem z _ Hz Hnz Hb).
      - pose proof (blocks_range z b Hz Hnz Hb) as Hbr.
        unfold fs_data_start in Hbr. lia.
      - pose proof (blocks_range z b Hz Hnz Hb) as Hbr.
        unfold fs_data_start in Hbr. lia. }
    assert (Htyp : forall z : Z, 0 <= z < sb_ninodes sb ->
              bv_unsigned (di_type (fs_dinode P' sb z))
              = bv_unsigned (di_type (fs_dinode P sb z))).
    { intros z Hz. rewrite (Hdec z ltac:(irng)).
      destruct (decide (z = i)) as [-> | Hzi];
        [rewrite Hty'; reflexivity | reflexivity]. }
    (* the directory readings of [i], when it is one *)
    set (nreco := dir_nrec szo).
    set (nrecn := dir_nrec sz').
    assert (Hdirwin : bv_unsigned (di_type dn) = T_DIR_z ->
              forall q : nat, (q < nreco)%nat ->
                dir_win_agree (fs_data_of P dn) (fs_data_of P' dn') q).
    { intros Hdty q Hq j Hj.
      destruct (Hdirsz Hdty) as (Hgr' & Hsza).
      assert (Hby : (16 * q + j < 12 * BSIZE)%nat).
      { assert (H16 : (16 * nreco <= 12 * BSIZE)%nat).
        { unfold nreco, dir_nrec.
          assert (Z.of_nat (Z.to_nat (szo / 16)) = szo / 16)
            by (apply Z2Nat.id; apply Z.div_pos; lia).
          assert (16 * (szo / 16) <= szo).
          { pose proof (Z.mod_pos_bound szo 16 ltac:(lia)).
            pose proof (Z.div_mod szo 16 ltac:(lia)). lia. }
          assert (Z.of_nat (12 * BSIZE)%nat = Z.of_nat 12 * BSIZE_z)
            by (rewrite Nat2Z.inj_mul, BSIZE_z_nat; reflexivity).
          lia. }
        lia. }
      unfold file_byte.
      assert (Hblt : ((16 * q + j) / BSIZE < 12)%nat).
      { apply Nat.Div0.div_lt_upper_bound. unfold BSIZE in *. lia. }
      rewrite (Hdata_old ((16 * q + j) / BSIZE)%nat ltac:(lia)).
      reflexivity. }
    assert (Hdirdead : bv_unsigned (di_type dn) = T_DIR_z ->
              forall q : nat, (nreco <= q < nrecn)%nat ->
                ~ dir_live (fs_data_of P' dn') q).
    { intros Hdty q Hq.
      destruct (Hdirsz Hdty) as (Hgr' & Hsza).
      destruct Hgr' as (q16 & Hq16).
      assert (Hsz'16 : sz' = 16 * Z.of_nat nrecn).
      { unfold nrecn, dir_nrec.
        rewrite Z2Nat.id by (apply Z.div_pos; lia).
        rewrite Hq16. rewrite Z.div_mul by lia. lia. }
      assert (Hcov' : sz' <= 13 * BSIZE_z).
      { pose proof (fs_nblk_cover sz' Hsz'0) as Hc. rewrite Hnb' in Hc.
        exact Hc. }
      assert (Hq16' : Z.of_nat nreco = szo / 16).
      { unfold nreco, dir_nrec. apply Z2Nat.id. apply Z.div_pos; lia. }
      assert (Hdiv16 : szo / 16 * 16 = szo).
      { rewrite Hsza. unfold BSIZE_z.
        replace (Z.of_nat 12 * 1024) with (Z.of_nat 12 * 64 * 16) by lia.
        rewrite Z.div_mul by lia. lia. }
      assert (Hwinb : forall j : nat, (j < 16)%nat ->
                file_byte (fs_data_of P' dn') (16 * q + j)%nat = bv_0 8).
      { intros j Hj.
        assert (Hlo : (12 * BSIZE <= 16 * q + j)%nat).
        { assert (Z.of_nat (12 * BSIZE)%nat = Z.of_nat 12 * BSIZE_z)
            by (rewrite Nat2Z.inj_mul, BSIZE_z_nat; reflexivity).
          assert (szo <= 16 * Z.of_nat q) by lia.
          hnf. unfold BSIZE_z in *. lia. }
        assert (Hhi : (16 * q + j < 13 * BSIZE)%nat).
        { assert (16 * (Z.of_nat q + 1) <= sz')
            by (unfold nrecn in Hq; lia).
          assert (Z.of_nat (13 * BSIZE)%nat = 13 * BSIZE_z)
            by (rewrite Nat2Z.inj_mul, BSIZE_z_nat; lia).
          lia. }
        unfold file_byte.
        assert (Hbq : ((16 * q + j) / BSIZE)%nat = 12%nat).
        { assert (Heq' : (16 * q + j
                          = 12 * BSIZE + (16 * q + j - 12 * BSIZE))%nat)
            by lia.
          rewrite Heq'.
          exact (proj1 (nat_block_split 12%nat
                          (16 * q + j - 12 * BSIZE)%nat
                          ltac:(unfold BSIZE in *; lia))). }
        rewrite Hbq, Hdata_12.
        apply lookup_total_replicate_2.
        apply Nat.mod_upper_bound. unfold BSIZE. lia. }
      intros Hlv. apply Hlv.
      assert (Hz0 : dir_inum (fs_data_of P' dn') q = de_inum dirent_zero).
      { apply (dir_inum_of_two _ q dirent_zero).
        intros j Hj.
        rewrite (Hwinb j ltac:(lia)).
        rewrite dirent_bytes_zero.
        rewrite lookup_total_replicate_2 by lia.
        rewrite NUL_bv0. reflexivity. }
      rewrite Hz0. exact dirent_zero_free. }
    assert (Hnrecle : (nreco <= nrecn)%nat)
      by (apply dir_nrec_mono; unfold szo; lia).
    (* the tree is edge-for-edge unchanged *)
    assert (Hviewi : bv_unsigned (di_type dn) = T_DIR_z ->
              dir_view (fs_data_of P' dn') nrecn
              = dir_view (fs_data_of P dn) nreco).
    { intros Hdty.
      rewrite (dir_view_dead_ext _ nreco nrecn Hnrecle (Hdirdead Hdty)).
      apply dir_view_agree. intros r Hr.
      exact (Hdirwin Hdty r Hr). }
    assert (Htree : forall (j : Z) (f : fname),
              tree_ent (tree_of_disk P' sb) j f = tree_ent t j f).
    { intros j f.
      destruct (decide (j = i)) as [-> | Hji].
      - destruct (decide (bv_unsigned (di_type dn) = T_DIR_z))
          as [Hdty | Hndty].
        + rewrite (tree_ent_dir_eq P' i Hi)
            by (rewrite (Htyp i Hi); exact Hdty).
          unfold t.
          rewrite (tree_ent_dir_eq P i Hi Hdty).
          unfold fs_file_data.
          rewrite (Hdec i HiN), decide_True by reflexivity.
          rewrite Hsz'u. fold dn. fold szo nreco. fold nrecn.
          rewrite (Hviewi Hdty). reflexivity.
        + rewrite (tree_ent_nondir P' i f).
          * unfold t. rewrite (tree_ent_nondir P i f);
              [reflexivity | exact Hndty].
          * rewrite (Hdec i HiN), decide_True by reflexivity.
            rewrite Hty'. exact Hndty.
      - apply tree_ent_untouched. intros Hjr.
        apply node_at_untouched; [exact Hjr | |].
        + rewrite (Hdec j ltac:(irng)), decide_False by exact Hji.
          reflexivity.
        + intros Hjl k0 Hk0.
          destruct (Hunt j Hjr Hji Hjl) as (_ & Hdata & _ & _).
          exact (Hdata k0). }
    pose proof (reach_iff_of_ent P' Htree) as Hreach.
    (* the ticket supply is list-for-list unchanged *)
    assert (Hsegi : bv_unsigned (di_type dn) = T_DIR_z ->
              fs_dir_tickets P' i dn' = fs_dir_tickets P i dn).
    { intros Hdty. unfold fs_dir_tickets.
      rewrite Hsz'u. fold dn. fold szo nreco. fold nrecn.
      replace nrecn with (nreco + (nrecn - nreco))%nat by lia.
      rewrite seq_app, omap_app.
      assert (Hpad : omap (fs_rec_ticket P' i dn')
                       (seq (0 + nreco) (nrecn - nreco)) = []).
      { apply omap_none. intros x Hx. apply elem_of_seq in Hx.
        unfold fs_rec_ticket. cbv zeta.
        assert (Hz0 : dir_inum (fs_data_of P' dn') x = bv_0 16).
        { destruct (decide (dir_inum (fs_data_of P' dn') x = bv_0 16))
            as [He | Hne']; [exact He |].
          exfalso. exact (Hdirdead Hdty x ltac:(lia) Hne'). }
        rewrite (proj2 (dir_liveb_false _ _) Hz0). reflexivity. }
      rewrite Hpad, app_nil_r.
      apply omap_ext_in. intros q Hq. apply elem_of_seq in Hq.
      unfold fs_rec_ticket. cbv zeta.
      rewrite (dir_liveb_agree _ _ q (Hdirwin Hdty q ltac:(lia))).
      rewrite (dir_inum_agree _ _ q (Hdirwin Hdty q ltac:(lia))).
      reflexivity. }
    assert (Hsupply : fs_rtickets P' sb rd = fs_rtickets P sb rd).
    { unfold fs_rtickets. apply tick_mjoin_ext.
      intros x Hx. cbv beta.
      destruct (bool_decide (Z.of_nat x ∈ rd)) eqn:Hg; [| reflexivity].
      apply bool_decide_eq_true_1 in Hg.
      destruct (proj1 (Hrd _) Hg) as (Hxr & Hxty & _).
      assert (Hxl : bv_unsigned (di_type (fs_dinode P sb (Z.of_nat x))) <> 0)
        by (rewrite Hxty; unfold T_DIR_z; discriminate).
      destruct (decide (Z.of_nat x = i)) as [Heq | Hxi].
      - unfold fs_dir_tickets_at. cbv zeta.
        rewrite Heq, (Hdec i HiN), decide_True by reflexivity.
        rewrite Hty'. fold dn.
        rewrite Heq in Hxty. fold dn in Hxty.
        rewrite (proj2 (Z.eqb_eq _ _) Hxty).
        exact (Hsegi Hxty).
      - apply tickets_at_untouched; [exact Hxr | |].
        + rewrite (Hdec (Z.of_nat x) (iblk_ix_range sb x (proj2 Hx))),
            decide_False by exact Hxi.
          reflexivity.
        + intros _ k0 Hk0.
          destruct (Hunt _ Hxr Hxi Hxl) as (_ & Hdata & _ & _).
          exact (Hdata k0). }
    (* the used set and the bitmap *)
    destruct (used_grow2 P' i fresh_ind fresh_data Hi Hlive)
      as (u'' & Hu'' & Hu''mem).
    { rewrite (Hdec i HiN), decide_True by reflexivity.
      rewrite Hty'. exact Hlive. }
    { rewrite (Hdec i HiN), decide_True by reflexivity.
      fold dn. exact Hblk'. }
    { exact Hfriu. }
    { exact Hfrdu. }
    { exact Hfrne. }
    { intros z Hz Hne.
      rewrite (Hdec z ltac:(irng)), decide_False by exact Hne.
      destruct (bv_unsigned (di_type (fs_dinode P sb z)) =? 0) eqn:Ez;
        [reflexivity |].
      destruct (Hunt z Hz Hne (proj1 (Z.eqb_neq _ _) Ez))
        as (_ & _ & Hbl & _).
      exact Hbl. }
    (* --- assemble ------------------------------------------------------ *)
    exists sb. split.
    { rewrite (fs_parse_sb_ext P P' HsbU). exact Hp. }
    constructor.
    - exact Hsb.
    - apply fs_inodes_dwf_intro. intros z Hz Hnz'.
      rewrite (Hdec z ltac:(irng)) in Hnz' |- *.
      destruct (decide (z = i)) as [-> | Hzi]; [exact Hdwf' |].
      destruct (Hunt z Hz Hzi Hnz') as (_ & _ & _ & Hdwf).
      rewrite Hdwf. exact (dwf_bool_at z Hz Hnz').
    - exists u''. split; [exact Hu'' |].
      apply (bitmap_wf_of_set P' u''
               (fs_bmap_set BSIZE (P (sb_bmapstart sb))
                ∪ {[fresh_ind]} ∪ {[fresh_data]}));
        [exact HbmB |].
      intros b Hb.
      rewrite !elem_of_union, !elem_of_singleton.
      rewrite (old_bit_iff b Hb), (Hu''mem b).
      unfold fs_data_start in Hfri, Hfrd. unfold fs_data_start.
      tauto.
    - (* the root *)
      destruct (decide (i = ROOTINO)) as [-> | Hiroot].
      + pose proof (fs_root_wf_type P sb HW7) as Hrt. fold dn in Hrt.
        apply root_wf_intro.
        * rewrite (Htyp ROOTINO Hi). fold dn. exact Hrt.
        * unfold fs_file_data.
          rewrite (Hdec ROOTINO (iblk_root_range sb Hnin1)).
          rewrite decide_True by reflexivity.
          rewrite Hsz'u. fold dn. fold szo nreco. fold nrecn.
          rewrite (Hviewi Hrt).
          pose proof (fs_root_wf_dotdot P sb HW7) as Hdd.
          unfold fs_file_data in Hdd. fold dn in Hdd.
          fold szo nreco in Hdd. exact Hdd.
      + assert (Hrl : bv_unsigned (di_type (fs_dinode P sb ROOTINO)) <> 0).
        { rewrite (fs_root_wf_type P sb HW7). unfold T_DIR_z. lia. }
        apply root_wf_untouched.
        * rewrite (Hdec ROOTINO (iblk_root_range sb Hnin1)).
          rewrite decide_False by (intros Hc; exact (Hiroot (eq_sym Hc))).
          reflexivity.
        * intros k0 Hk0.
          destruct (Hunt ROOTINO
                      ltac:(pose proof Hnin1; unfold ROOTINO; lia)
                      ltac:(intros Hc; exact (Hiroot (eq_sym Hc))) Hrl)
            as (_ & Hdata & _ & _).
          exact (Hdata k0).
    - (* the dots *)
      apply fs_dots_all_intro. intros z Hz Hdty'.
      rewrite (Hdec z ltac:(irng)) in Hdty' |- *.
      destruct (decide (z = i)) as [-> | Hzi].
      + rewrite Hty' in Hdty'. fold dn in Hdty'.
        apply (fs_dots_wf_win P P' i dn dn').
        * fold szo. rewrite Hsz'u. lia.
        * apply (Hdirwin Hdty' 0%nat).
          destruct (dots_flat i Hi ltac:(fold dn; exact Hdty'))
            as (Hn2 & _). fold dn in Hn2. fold szo nreco in Hn2. lia.
        * apply (Hdirwin Hdty' 1%nat).
          destruct (dots_flat i Hi ltac:(fold dn; exact Hdty'))
            as (Hn2 & _). fold dn in Hn2. fold szo nreco in Hn2. lia.
        * exact (dots_bool_at i Hi ltac:(fold dn; exact Hdty')).
      + assert (Hzl : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
          by (rewrite Hdty'; unfold T_DIR_z; discriminate).
        destruct (Hunt z Hz Hzi Hzl) as (_ & Hdata & _ & _).
        apply (fs_dots_wf_win P P' z (fs_dinode P sb z) (fs_dinode P sb z)).
        * lia.
        * apply (dir_win_agree_blocks _ _ FS_MAXFILE);
            [intros k0 Hk0; exact (Hdata k0)
            | unfold FS_MAXFILE, BSIZE; lia].
        * apply (dir_win_agree_blocks _ _ FS_MAXFILE);
            [intros k0 Hk0; exact (Hdata k0)
            | unfold FS_MAXFILE, BSIZE; lia].
        * exact (dots_bool_at z Hz Hdty').
    - exists nib. split; [exact Hnibz |].
      apply fs_region_wf_intro.
      + intros z Hz Hzn.
        rewrite (Hdec z ltac:(irng)).
        rewrite decide_False by lia.
        apply (fs_region_free_spec P sb nib z
                 (fs_region_wf_free P sb nib Hreg)); lia.
      + intros z Hz Hfree.
        rewrite (Hdec z ltac:(irng)) in Hfree |- *.
        destruct (decide (z = i)) as [-> | Hzi].
        { exfalso. rewrite Hty' in Hfree. exact (Hlive Hfree). }
        apply (fs_region_nlink_free P sb nib z
                 (fs_region_wf_nlink P sb nib Hreg)); [lia | exact Hfree].
      + intros z Hz.
        rewrite (Hdec z ltac:(irng)).
        destruct (decide (z = i)) as [-> | Hzi].
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
        destruct (decide (z = i)) as [-> | Hzi].
        * (* the growing directory's bundle *)
          fold dn in Hzty.
          assert (Hdeci : fs_dinode P' sb i = dn').
          { rewrite (Hdec i HiN), decide_True by reflexivity.
            reflexivity. }
          rewrite Hdeci.
          destruct (Hdok i Hz) as [Hgr Hent Huq Hdot Hdd].
          constructor.
          -- rewrite Hsz'u. exact (proj1 (Hdirsz Hzty)).
          -- intros k0 Hk0 Hlive'.
             rewrite Hsz'u in Hk0. fold nrecn in Hk0.
             destruct (Nat.lt_ge_cases k0 nreco) as [Hk0o | Hk0o].
             2:{ exfalso.
                 exact (Hdirdead Hzty k0 ltac:(lia) Hlive'). }
             assert (Hlv : dir_live (fs_data_of P dn) k0).
             { unfold dir_live in *.
               rewrite (dir_inum_agree _ _ k0 (Hdirwin Hzty k0 Hk0o))
                 in Hlive'.
               exact Hlive'. }
             destruct (Hent k0 ltac:(fold dn; fold szo nreco; exact Hk0o)
                         ltac:(fold dn; exact Hlv)) as (Hran & Hty0).
             fold dn in Hran, Hty0.
             rewrite (dir_inum_agree _ _ k0 (Hdirwin Hzty k0 Hk0o)).
             split; [exact Hran |].
             rewrite (Htyp (bv_unsigned
                              (dir_inum (fs_data_of P dn) k0))
                        ltac:(lia)).
             exact Hty0.
          -- rewrite Hsz'u. fold nrecn.
             intros j k0 Hj Hk0 Hlj Hlk Heq.
             destruct (Nat.lt_ge_cases j nreco) as [Hjo | Hjo].
             2:{ exfalso. exact (Hdirdead Hzty j ltac:(lia) Hlj). }
             destruct (Nat.lt_ge_cases k0 nreco) as [Hk0o | Hk0o].
             2:{ exfalso. exact (Hdirdead Hzty k0 ltac:(lia) Hlk). }
             apply (Huq j k0 ltac:(fold dn; fold szo nreco; exact Hjo)
                      ltac:(fold dn; fold szo nreco; exact Hk0o)).
             ++ unfold dir_live in *.
                rewrite (dir_inum_agree _ _ j (Hdirwin Hzty j Hjo)) in Hlj.
                fold dn. exact Hlj.
             ++ unfold dir_live in *.
                rewrite (dir_inum_agree _ _ k0 (Hdirwin Hzty k0 Hk0o))
                  in Hlk.
                fold dn. exact Hlk.
             ++ fold dn.
                rewrite <- (dir_bname_agree' _ _ j (Hdirwin Hzty j Hjo)).
                rewrite <- (dir_bname_agree' _ _ k0
                              (Hdirwin Hzty k0 Hk0o)).
                exact Heq.
          -- rewrite Hsz'u. fold nrecn. rewrite (Hviewi Hzty).
             fold dn in Hdot. fold szo nreco in Hdot. exact Hdot.
          -- rewrite Hsz'u. fold nrecn. rewrite (Hviewi Hzty).
             fold dn in Hdd. fold szo nreco in Hdd. exact Hdd.
        * assert (Hzl : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
            by (rewrite Hzty; unfold T_DIR_z; discriminate).
          destruct (Hunt z Hzr Hzi Hzl) as (_ & Hdata & _ & _).
          apply dir_ok_untouched; [exact Hz | | |].
          -- rewrite (Hdec z ltac:(irng)), decide_False by exact Hzi.
             reflexivity.
          -- intros k0 Hk0. exact (Hdata k0).
          -- intros w0 Hw0 Hwl Hw0'. exfalso. apply Hwl.
             rewrite <- (Htyp w0 Hw0). exact Hw0'.
      + intros z Hz. cbv zeta.
        rewrite (Hdec z ltac:(irng)).
        unfold fs_rtick. rewrite Hsupply.
        destruct (decide (z = i)) as [-> | Hzi].
        * rewrite Hty', Hnl'. fold dn. exact (Hlkg i Hz).
        * exact (Hlkg z Hz).
      + intros z Hz Hty0 Hnin.
        rewrite (Hdec z ltac:(irng)) in Hty0 |- *.
        destruct (decide (z = i)) as [-> | Hzi].
        { (* an orphan directory crossing the boundary stays dots-only *)
          rewrite Hty' in Hty0. fold dn in Hty0.
          intros k0 Hk02 Hk0n Hlive'.
          rewrite Hsz'u in Hk0n. fold nrecn in Hk0n.
          destruct (Nat.lt_ge_cases k0 nreco) as [Hk0o | Hk0o].
          2:{ exact (Hdirdead Hty0 k0 ltac:(lia) Hlive'). }
          apply (Horph i Hz ltac:(fold dn; exact Hty0) Hnin k0 Hk02
                   ltac:(fold dn; fold szo nreco; exact Hk0o)).
          unfold dir_live in *.
          rewrite (dir_inum_agree _ _ k0 (Hdirwin Hty0 k0 Hk0o)) in Hlive'.
          fold dn. exact Hlive'. }
        assert (Hzl : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
          by (rewrite Hty0; unfold T_DIR_z; discriminate).
        destruct (Hunt z Hz Hzi Hzl) as (_ & Hdata & _ & _).
        apply (dots_only_untouched P' (fs_dinode P sb z)).
        * exact (fdi_size _ _ _ (dok_at z Hz Hzl)).
        * intros k0 Hk0. exact (Hdata k0).
        * exact (Horph z Hz Hty0 Hnin).
  Qed.

End EffAllocIndBlock.

(* the [fs_durable_wf_view]-level wrapper -- the shape stage G2 consumes:
   the invariant of the OLD view, the decode-level preconditions (the two
   fresh blocks arrive as balloc's own postcondition, a CLEARED bitmap
   bit), the invariant of the updated view. *)

Lemma eff_alloc_ind_block_wfv (P : Z -> list (bv 8)) (sb : fs_sb)
    (i : Z) (fresh_ind fresh_data sz' : Z) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  Z.of_nat 12 = fs_nblk (bv_unsigned (di_size (fs_dinode P sb i))) ->
  fs_nblk sz' = 13 ->
  sz' <= Z.of_nat FS_MAXFILE * BSIZE_z ->
  (bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z ->
     (16 | sz')
     /\ bv_unsigned (di_size (fs_dinode P sb i)) = Z.of_nat 12 * BSIZE_z) ->
  fs_data_start sb <= fresh_ind < sb_size sb ->
  fs_data_start sb <= fresh_data < sb_size sb ->
  fresh_ind <> fresh_data ->
  fs_bit (P (sb_bmapstart sb)) fresh_ind = false ->
  fs_bit (P (sb_bmapstart sb)) fresh_data = false ->
  fs_durable_wf_view (eff_alloc_ind_block P sb i fresh_ind fresh_data sz').
Proof.
  intros Hv Hp Hi Hlive Hfbn Hnb Hcap Hdir Hfri Hfrd Hfrne Hbi Hbd.
  destruct Hv as (sb0 & Hp0 & Hsw).
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
  destruct HW45 as (u & Hu & Hbm).
  destruct Hregx as (nib & Hnibz & Hreg).
  destruct HW9 as (rd & Hrd & Hdok & Hlkg & Horph).
  destruct (fs_sb_ok_meta sb (fs_sb_wf_ok sb Hsb)) as (Hg1 & Hg2 & Hg3).
  assert (Hfriu : fresh_ind ∉ u).
  { destruct (fs_bitmap_wf_free P sb u fresh_ind Hbm
                ltac:(unfold fs_data_start in *; lia) Hbi) as (_ & Hn).
    exact Hn. }
  assert (Hfrdu : fresh_data ∉ u).
  { destruct (fs_bitmap_wf_free P sb u fresh_data Hbm
                ltac:(unfold fs_data_start in *; lia) Hbd) as (_ & Hn).
    exact Hn. }
  apply (eff_alloc_ind_block_wf P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph); assumption.
Qed.
