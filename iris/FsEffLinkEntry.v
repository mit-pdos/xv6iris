(* FsEffLinkEntry.v -- durable-disk stage F2, effect 4: linking an
   existing non-directory under a new name. *)
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

Section EffLinkEntry.
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

  (* THE BLOCK-DISJOINTNESS SIDE CONDITIONS of [HaE]: a data block is
     neither inode block (nor the bitmap block).  One bound hypothesis and
     the two [iblock_bounds] readings answer every one of them -- but
     spelled as a bare [lia] it is a general-purpose closer meeting this
     proof's ~180-hypothesis context, and those sentences measured 4-9 s
     EACH.  [match goal] names the bound; [clear -] hands [lia] the two
     region facts it actually uses. *)
  Local Ltac blk_ne d3 i3 :=
    match goal with
    | H : _ <= ?b < _ |- ?b <> _ => clear - H d3 i3; lia
    end.

  (* ==================================================================== *)
  (*  18.  EFFECT 4 -- LINKING AN EXISTING NON-DIRECTORY                   *)
  (* ==================================================================== *)

  Definition eff_link_entry (d : Z) (k : nat) (name : fname) (i : Z)
    : Z -> list (bv 8) :=
    let dnd := fs_dinode P sb d in
    let szd' := Z.max (bv_unsigned (di_size dnd)) (16 * (Z.of_nat k + 1)) in
    let a := fs_blk_addr P dnd (k / 64)%nat in
    fs_upd
      (eff_dinode
         (eff_dinode P sb d (di_set_size dnd (Z_to_bv 32 szd')))
         sb i (di_nlink_inc (fs_dinode P sb i)))
      a
      (fs_splice (P a) (16 * (k mod 64)) 16
         (fun j => dirent_bytes (de_of_name (Z_to_bv 16 i) name) !!! j)).

  Lemma eff_link_entry_wf (d : Z) (k : nat) (name : fname) (i : Z) :
    0 <= d < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
    fs_reachable P sb d ->
    0 < i < sb_ninodes sb -> i < 65536 ->
    (bv_unsigned (di_type (fs_dinode P sb i)) = T_FILE_z
     \/ bv_unsigned (di_type (fs_dinode P sb i)) = T_DEVICE_z) ->
    bv_unsigned (di_nlink (fs_dinode P sb i)) < 32767 ->
    (length name <= 14)%nat -> nonul name ->
    dir_first (fs_file_data P sb d)
      (dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))) name = None ->
    ((k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat
       /\ ~ dir_live (fs_file_data P sb d) k
     \/ k = dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))
       /\ 16 * (Z.of_nat k + 1)
          <= fs_nblk (bv_unsigned (di_size (fs_dinode P sb d))) * BSIZE_z) ->
    fs_durable_wf_view (eff_link_entry d k name i).
  Proof.
    intros Hd Hdty Hdre Hi Hi16 Hity Hnlcap Hlen Hnn Hnone Harm.
    assert (Hm32 : bv_modulus 32 = 4294967296) by reflexivity.
    set (dn := fs_dinode P sb d) in *.
    set (dni := fs_dinode P sb i) in *.
    unfold fs_file_data in Hnone, Harm. fold dn in Hnone, Harm.
    set (szd := bv_unsigned (di_size dn)) in *.
    set (nrec := dir_nrec szd) in *.
    set (data := fs_data_of P dn) in *.
    set (szd' := Z.max szd (16 * (Z.of_nat k + 1))).
    set (dnd' := di_set_size dn (Z_to_bv 32 szd')).
    set (dni' := di_nlink_inc dni).
    set (w := Z_to_bv 16 i).
    set (P' := eff_link_entry d k name i).
    (* -------- basic decode facts about the two new records ------------ *)
    assert (Hdlive : bv_unsigned (di_type dn) <> 0)
      by (rewrite Hdty; unfold T_DIR_z; discriminate).
    assert (Hilive : bv_unsigned (di_type dni) <> 0)
      by (unfold T_FILE_z, T_DEVICE_z in Hity; lia).
    assert (Hinotdir : bv_unsigned (di_type dni) <> T_DIR_z)
      by (unfold T_FILE_z, T_DEVICE_z, T_DIR_z in *; lia).
    assert (Hdi_ne : d <> i)
      by (intros ->; exact (Hinotdir Hdty)).
    assert (Hd_rd : d ∈ rd)
      by (apply (Hrd d); split; [lia | split; [exact Hdty | exact Hdre]]).
    pose proof (Hdok d Hd_rd) as Hddok. fold dn in Hddok.
    pose proof (dok_at d Hd Hdlive) as Hdok_d. fold dn in Hdok_d.
    pose proof (dok_at i ltac:(lia) Hilive) as Hdok_i. fold dni in Hdok_i.
    pose proof (fdi_size _ _ _ Hdok_d) as Hcapd. fold dn in Hcapd.
    pose proof (proj1 (bv_unsigned_in_range _ (di_size dn))) as Hsz0.
    destruct (dots_flat d Hd Hdty) as
      (Hnrec2 & Hlv0 & Hin0 & Hbn0 & Hlv1 & Hbn1).
    fold dn data in Hnrec2, Hlv0, Hin0, Hbn0, Hlv1, Hbn1.
    fold szd nrec in Hnrec2.
    (* the size arithmetic *)
    destruct (fdo_gran _ _ _ _ Hddok) as (qd & Hqd). fold szd in Hqd.
    assert (Hsz16 : szd = 16 * Z.of_nat nrec).
    { unfold nrec, dir_nrec. rewrite Z2Nat.id by (apply Z.div_pos; lia).
      rewrite Hqd. rewrite Z.div_mul by lia. lia. }
    assert (Hszpos : 0 < szd) by lia.
    assert (Hkwin : 16 * (Z.of_nat k + 1) <= fs_nblk szd * BSIZE_z).
    { destruct Harm as [(Hk & _) | (_ & Hk)]; [| exact Hk].
      pose proof (fs_nblk_cover szd ltac:(lia)) as Hcov.
      unfold BSIZE_z in *. lia. }
    assert (Hszd'le : szd <= szd') by (unfold szd'; lia).
    assert (Hszd'win : szd' <= fs_nblk szd * BSIZE_z).
    { unfold szd'. apply Z.max_lub; [| exact Hkwin].
      exact (fs_nblk_cover szd ltac:(lia)). }
    assert (Hnb' : fs_nblk szd' = fs_nblk szd)
      by (apply fs_nblk_between; lia).
    assert (Hszd'cap : szd' <= Z.of_nat FS_MAXFILE * BSIZE_z).
    { pose proof (fs_nblk_max szd ltac:(lia) Hcapd) as Hnm.
      unfold BSIZE_z in *. lia. }
    assert (Hszd'u : bv_unsigned (di_size dnd') = szd').
    { unfold dnd'. cbn [di_size di_set_size]. apply Z_to_bv_small.
      unfold FS_MAXFILE, BSIZE_z in Hszd'cap. lia. }
    assert (Htyd' : di_type dnd' = di_type dn) by reflexivity.
    assert (Haddrd' : di_addrs dnd' = di_addrs dn) by reflexivity.
    assert (Hnlkd' : di_nlink dnd' = di_nlink dn) by reflexivity.
    assert (Htyi' : di_type dni' = di_type dni) by reflexivity.
    assert (Haddri' : di_addrs dni' = di_addrs dni) by reflexivity.
    assert (Hszi' : di_size dni' = di_size dni) by reflexivity.
    assert (Hwfd' : dinode_wf dnd')
      by (apply di_set_size_wf, fs_dinode_wf).
    assert (Hwfi' : dinode_wf dni')
      by (apply di_set_nlink_wf, fs_dinode_wf).
    assert (Hwu : bv_unsigned w = i).
    { unfold w. apply Z_to_bv_small.
      assert (Hm16 : bv_modulus 16 = 65536) by reflexivity. lia. }
    assert (Hwnz : w <> bv_0 16).
    { intros Hc.
      assert (Hc' : bv_unsigned w = 0) by (rewrite Hc; reflexivity).
      lia. }
    (* record count moves *)
    set (nrec' := dir_nrec szd').
    assert (Hnrecle : (nrec <= nrec')%nat)
      by (apply dir_nrec_mono; unfold szd; lia).
    assert (Hnrec'c : (k < nrec)%nat /\ nrec' = nrec
                      \/ k = nrec /\ nrec' = S nrec).
    { destruct Harm as [(Hk & _) | (Hk & _)].
      - left. split; [exact Hk |].
        unfold nrec', szd'.
        replace (Z.max szd (16 * (Z.of_nat k + 1))) with szd; [reflexivity |].
        unfold nrec in Hk. unfold dir_nrec in Hk.
        assert (Hlt : Z.of_nat k < szd / 16).
        { pose proof (Nat2Z.inj_lt k (Z.to_nat (szd / 16))) as Hj.
          rewrite Z2Nat.id in Hj by (apply Z.div_pos; lia).
          apply Hj. exact Hk. }
        rewrite Hqd in Hlt. rewrite Z.div_mul in Hlt by lia. lia.
      - right. split; [exact Hk |].
        unfold nrec', szd'.
        replace (Z.max szd (16 * (Z.of_nat k + 1))) with (szd + 16).
        2:{ rewrite Hk. unfold nrec. unfold dir_nrec.
            rewrite Z2Nat.id by (apply Z.div_pos; lia).
            rewrite Hqd. rewrite Z.div_mul by lia. lia. }
        unfold dir_nrec, nrec, dir_nrec.
        replace ((szd + 16) / 16) with (szd / 16 + 1)
          by (rewrite Hqd; rewrite Z.div_mul by lia;
              replace (qd * 16 + 16) with ((qd + 1) * 16) by lia;
              rewrite Z.div_mul by lia; lia).
        rewrite Z2Nat.inj_add; [lia | apply Z.div_pos; lia | lia]. }
    assert (Hknrec' : (k < nrec')%nat) by (destruct Hnrec'c as [[]|[]]; lia).
    assert (Hk2 : (2 <= k)%nat).
    { destruct Harm as [(Hk & Hfree) | (Hk & _)]; [| lia].
      destruct (decide (2 <= k)%nat) as [Hge | Hlt]; [exact Hge |].
      exfalso. destruct k as [| [| k']]; [| | lia].
      - exact (Hfree Hlv0).
      - exact (Hfree Hlv1). }
    assert (Hnamedot : name <> dot_name).
    { intros ->.
      apply (proj1 (dir_first_None data nrec dot_name) Hnone 0%nat
               ltac:(lia)).
      split; [exact Hlv0 | exact Hbn0]. }
    assert (Hnamedd : name <> dotdot_name).
    { intros ->.
      apply (proj1 (dir_first_None data nrec dotdot_name) Hnone 1%nat
               ltac:(lia)).
      split; [exact Hlv1 | exact Hbn1]. }
    (* the record's block *)
    assert (HkbM : ((k / 64) < FS_MAXFILE)%nat /\
                   Z.of_nat (k / 64) < fs_nblk szd).
    { pose proof (fs_nblk_max szd ltac:(lia) Hcapd) as Hnm.
      assert (Hkb : Z.of_nat (k / 64) < fs_nblk szd).
      { assert (Hkz : Z.of_nat k < 64 * fs_nblk szd)
          by (unfold BSIZE_z in Hkwin; lia).
        rewrite (Nat2Z.inj_div k 64).
        apply Z.div_lt_upper_bound; lia. }
      split; [| exact Hkb]. lia. }
    destruct HkbM as (HkbM & Hkbnb).
    assert (Ha_rng : fs_data_start sb
                     <= fs_blk_addr P dn (k / 64) < sb_size sb)
      by (apply (blk_addr_covered d (k / 64)%nat Hd Hdlive HkbM Hkbnb)).
    assert (Ha0 : fs_blk_addr P dn (k / 64) <> 0)
      by (destruct (fs_sb_ok_meta sb Hok) as (Hx1 & Hx2 & Hx3);
          unfold fs_data_start in *; lia).
    assert (Ha_in : fs_blk_addr P dn (k / 64) ∈ fs_inode_blocks P dn).
    { rewrite <- (fs_slot_blk dn (k / 64)%nat HkbM).
      apply (fs_slot_elem_dok P sb dn); [exact Hdok_d | lia |].
      rewrite (fs_slot_blk dn (k / 64)%nat HkbM). exact Ha0. }
    (* -------- the changed blocks -------------------------------------- *)
    destruct (fs_sb_ok_meta sb Hok) as (Hm1 & Hm2 & Hm3).
    pose proof Hnin_le as HninN.
    assert (HdN : 0 <= d < 16 * (sb_ninodes sb / 16 + 1)) by lia.
    assert (HiN : 0 <= i < 16 * (sb_ninodes sb / 16 + 1)) by lia.
    destruct (iblock_bounds sb Hok d HdN) as (Hibd1 & Hibd2 & Hibd3).
    destruct (iblock_bounds sb Hok i HiN) as (Hibi1 & Hibi2 & Hibi3).
    assert (HaE : forall b : Z,
              b <> fs_blk_addr P dn (k / 64) ->
              b <> IBLOCK (fs_inum_bv d) (sb_inodestart sb) ->
              b <> IBLOCK (fs_inum_bv i) (sb_inodestart sb) ->
              P' b = P b).
    { intros b Hb1 Hb2 Hb3. unfold P', eff_link_entry. cbv zeta.
      fold dn. rewrite fs_upd_ne by exact Hb1.
      rewrite (eff_dinode_out sb) by exact Hb3.
      exact (eff_dinode_out sb _ _ _ _ Hb2). }
    assert (HsbU : P' SB_BNO = P SB_BNO).
    { apply HaE; unfold SB_BNO, fs_data_start in *; lia. }
    assert (HbmU : P' (sb_bmapstart sb) = P (sb_bmapstart sb)).
    { apply HaE; unfold fs_data_start in *; lia. }
    assert (HaB : P' (fs_blk_addr P dn (k / 64))
                  = fs_splice (P (fs_blk_addr P dn (k / 64)))
                      (16 * (k mod 64)) 16
                      (fun j => dirent_bytes (de_of_name w name) !!! j)).
    { unfold P', eff_link_entry. cbv zeta. fold dn. apply fs_upd_at. }
    assert (Hdec : forall z : Z, 0 <= z < 16 * (sb_ninodes sb / 16 + 1) ->
              fs_dinode P' sb z
              = if decide (z = i) then dni'
                else if decide (z = d) then dnd' else fs_dinode P sb z).
    { intros z Hz.
      transitivity (fs_dinode
                      (eff_dinode
                         (eff_dinode P sb d dnd') sb i dni') sb z).
      - apply fs_dinode_ext. unfold P', eff_link_entry. cbv zeta.
        fold dn. fold dnd'. fold dni.
        apply fs_upd_ne.
        destruct (iblock_bounds sb Hok z Hz) as (Hz1 & Hz2 & Hz3).
        unfold fs_data_start in Ha_rng. lia.
      - rewrite (eff_dinode_dec sb Hok _ i dni' z Hwfi' HiN Hz).
        destruct (decide (z = i)) as [-> | Hzi]; [reflexivity |].
        exact (eff_dinode_dec sb Hok P d dnd' z Hwfd' HdN Hz). }
    (* -------- the untouched inodes ------------------------------------ *)
    assert (Hslotinj : fs_slot_inj P dn) by (apply (slot_inj_at d Hd Hdlive)).
    assert (Hother : forall k' : nat, k' <> (k / 64)%nat ->
              fs_blk_addr P dn k' <> 0 ->
              P' (fs_blk_addr P dn k') = P (fs_blk_addr P dn k')).
    { intros k' Hne Hnz.
      destruct (Nat.lt_ge_cases k' FS_MAXFILE) as [Hk' | Hk'].
      - assert (Hrng : fs_data_start sb <= fs_blk_addr P dn k' < sb_size sb).
        { apply (blk_addr_covered d k' Hd Hdlive Hk').
          destruct (Z.lt_ge_cases (Z.of_nat k') (fs_nblk szd)) as [| Hge];
            [assumption |].
          exfalso. apply Hnz.
          destruct (Nat.lt_ge_cases k' FS_NDIRECT) as [Hdk | Hdk].
          - unfold fs_blk_addr.
            rewrite (proj2 (Nat.ltb_lt k' FS_NDIRECT) Hdk).
            exact (fdi_direct_zero _ _ _ Hdok_d k' Hdk Hge).
          - unfold fs_blk_addr.
            rewrite (proj2 (Nat.ltb_ge k' FS_NDIRECT) Hdk).
            apply (fdi_ent_zero _ _ _ Hdok_d (k' - FS_NDIRECT)%nat).
            + unfold FS_MAXFILE, FS_NDIRECT, FS_NINDIRECT in *. lia.
            + rewrite Nat2Z.inj_sub by exact Hdk. fold szd. lia. }
        apply HaE; [| unfold fs_data_start in *; blk_ne Hibd3 Hibi3
                    | unfold fs_data_start in *; blk_ne Hibd3 Hibi3].
        intros Hc.
        apply Hne.
        apply (Hslotinj k' (k / 64)%nat ltac:(lia) ltac:(lia)).
        + rewrite (fs_slot_blk dn k' Hk'). exact Hnz.
        + rewrite (fs_slot_blk dn k' Hk'),
            (fs_slot_blk dn (k / 64)%nat HkbM).
          exact Hc.
      - rewrite (fs_blk_addr_high P dn k' Hk'). exact HsbU. }
    assert (HindD : fs_ind_ents P' dnd' = fs_ind_ents P dn).
    { transitivity (fs_ind_ents P' dn);
        [exact (fs_ind_ents_meta P' dn dnd' Haddrd') |].
      apply fs_ind_ents_ext. intros Hnz12.
      assert (Hin' : bv_unsigned (di_addrs dn !!! 12%nat)
                     ∈ fs_inode_blocks P dn).
      { rewrite <- (fs_slot_max P dn).
        apply (fs_slot_elem_dok P sb dn); [exact Hdok_d | lia |].
        rewrite fs_slot_max. exact Hnz12. }
      pose proof (blocks_range d _ Hd Hdlive Hin') as Hbr.
      apply HaE; [| unfold fs_data_start in *; blk_ne Hibd3 Hibi3
                  | unfold fs_data_start in *; blk_ne Hibd3 Hibi3].
      intros Hc.
      assert (Hfe : fs_slot P dn FS_MAXFILE = fs_slot P dn (k / 64)).
      { rewrite fs_slot_max, (fs_slot_blk dn (k / 64)%nat HkbM). exact Hc. }
      assert (Hnz' : fs_slot P dn FS_MAXFILE <> 0)
        by (rewrite fs_slot_max; exact Hnz12).
      pose proof (Hslotinj FS_MAXFILE (k / 64)%nat ltac:(lia) ltac:(lia)
                    Hnz' Hfe) as Hcc.
      lia. }
    assert (Hunt : forall z : Z, 0 <= z < sb_ninodes sb ->
              z <> d -> z <> i ->
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
    { intros z Hz Hnd' Hni' Hnz. apply inode_untouched; try assumption.
      intros b Hb. apply HaE.
      - intros ->. exact (blocks_cross z d _ Hz Hd Hnd' Hnz Hdlive Hb Ha_in).
      - pose proof (blocks_range z b Hz Hnz Hb) as Hbr.
        unfold fs_data_start in Hbr. clear -Hbr Hibd3 Hibi3. lia.
      - pose proof (blocks_range z b Hz Hnz Hb) as Hbr.
        unfold fs_data_start in Hbr. clear -Hbr Hibd3 Hibi3. lia. }
    (* inode [i]'s readers: only the link count moved *)
    assert (HindI : fs_ind_ents P' dni' = fs_ind_ents P dni).
    { transitivity (fs_ind_ents P' dni);
        [exact (fs_ind_ents_meta P' dni dni' Haddri') |].
      apply fs_ind_ents_ext. intros Hnz12.
      assert (Hin' : bv_unsigned (di_addrs dni !!! 12%nat)
                     ∈ fs_inode_blocks P dni).
      { rewrite <- (fs_slot_max P dni).
        apply (fs_slot_elem_dok P sb dni); [exact Hdok_i | lia |].
        rewrite fs_slot_max. exact Hnz12. }
      pose proof (blocks_range i _ ltac:(lia) Hilive Hin') as Hbr.
      apply HaE; [| unfold fs_data_start in *; blk_ne Hibd3 Hibi3
                  | unfold fs_data_start in *; blk_ne Hibd3 Hibi3].
      intros Hc.
      refine (blocks_cross i d (fs_blk_addr P dn (k / 64)%nat)
                ltac:(lia) Hd ltac:(intros Hcc; exact (Hdi_ne (eq_sym Hcc)))
                Hilive Hdlive _ Ha_in).
      rewrite <- Hc. exact Hin'. }
    assert (HdataI : forall k0 : nat,
              fs_data_of P' dni' k0 = fs_data_of P dni k0).
    { intros k0.
      rewrite (fs_data_of_meta P' dni dni' k0 Haddri').
      apply (fs_data_of_same P P' dni k0);
        [rewrite <- (fs_ind_ents_meta P' dni dni' Haddri'); exact HindI |].
      intros Hnz.
      destruct (Nat.lt_ge_cases k0 FS_MAXFILE) as [Hk0 | Hk0].
      - assert (Hin' : fs_blk_addr P dni k0 ∈ fs_inode_blocks P dni).
        { rewrite <- (fs_slot_blk dni k0 Hk0).
          apply (fs_slot_elem_dok P sb dni); [exact Hdok_i | lia |].
          rewrite (fs_slot_blk dni k0 Hk0). exact Hnz. }
        pose proof (blocks_range i _ ltac:(lia) Hilive Hin') as Hbr.
        apply HaE; [| unfold fs_data_start in *; blk_ne Hibd3 Hibi3
                    | unfold fs_data_start in *; blk_ne Hibd3 Hibi3].
        intros Hc.
        refine (blocks_cross i d (fs_blk_addr P dn (k / 64)%nat)
                  ltac:(lia) Hd ltac:(intros Hcc; exact (Hdi_ne (eq_sym Hcc)))
                  Hilive Hdlive _ Ha_in).
        rewrite <- Hc. exact Hin'.
      - rewrite (fs_blk_addr_high P dni k0 Hk0). exact HsbU. }
    (* -------- the written record, at the view ------------------------- *)
    assert (Hwrit : dir_written_at data (fs_data_of P' dnd') k name w).
    { apply (dirent_written P' dn dnd' k w name Hlen Hnn Haddrd' HindD
               Ha0 HaB Hother). }
    pose proof Hwrit as (Hwz & Hwname & Hwagree).
    assert (Hdead : forall q : nat, (nrec <= q < nrec')%nat -> q <> k ->
              ~ dir_live (fs_data_of P' dnd') q).
    { intros q Hq Hqk. destruct Hnrec'c as [[Hkc He] | [Hkc He]]; lia. }
    assert (Hfreek : (k < nrec)%nat -> ~ dir_live data k).
    { intros Hkn.
      destruct Harm as [(_ & Hfree) | (Hkc & _)]; [exact Hfree | lia]. }
    assert (Hview : dir_view (fs_data_of P' dnd') nrec'
                    = <[name := i]> (dir_view data nrec)).
    { rewrite <- Hwu.
      apply (dir_view_write data (fs_data_of P' dnd') nrec nrec' k name w
               Hnrecle Hknrec' Hwrit Hdead Hfreek Hnone Hwnz). }
    (* -------- the tree edges ------------------------------------------ *)
    assert (Htyp : forall z : Z, 0 <= z < sb_ninodes sb ->
              bv_unsigned (di_type (fs_dinode P' sb z))
              = bv_unsigned (di_type (fs_dinode P sb z))).
    { intros z Hz. rewrite (Hdec z ltac:(irng)).
      destruct (decide (z = i)) as [-> | Hzi];
        [rewrite Htyi'; reflexivity |].
      destruct (decide (z = d)) as [-> | Hzd];
        [rewrite Htyd'; reflexivity | reflexivity]. }
    assert (Hentd : forall f : fname,
              tree_ent (tree_of_disk P' sb) d f
              = <[name := i]> (dir_view data nrec) !! f).
    { intros f.
      rewrite (tree_ent_dir_eq P' d Hd)
        by (rewrite (Htyp d Hd); exact Hdty).
      unfold fs_file_data.
      rewrite (Hdec d ltac:(irng)).
      rewrite decide_False by (intros Hc; exact (Hdi_ne Hc)).
      rewrite decide_True by reflexivity.
      rewrite Hszd'u. fold nrec'. rewrite Hview. reflexivity. }
    assert (Hentt : forall f : fname,
              tree_ent t d f = dir_view data nrec !! f).
    { intros f. unfold t.
      rewrite (tree_ent_dir_eq P d Hd Hdty).
      unfold fs_file_data. fold dn. fold szd nrec data. reflexivity. }
    assert (Hentother : forall (j : Z) (f : fname), j <> d ->
              tree_ent (tree_of_disk P' sb) j f = tree_ent t j f).
    { intros j f Hjd.
      destruct (decide (j = i)) as [-> | Hji].
      - rewrite (tree_ent_nondir P' i f).
        + unfold t. rewrite (tree_ent_nondir P i f); [reflexivity |].
          exact Hinotdir.
        + rewrite (Hdec i HiN), decide_True by reflexivity.
          rewrite Htyi'. exact Hinotdir.
      - apply tree_ent_untouched. intros Hjr.
        apply node_at_untouched; [exact Hjr | |].
        + rewrite (Hdec j ltac:(irng)).
          rewrite decide_False by exact Hji.
          rewrite decide_False by exact Hjd. reflexivity.
        + intros Hjl k0 Hk0.
          destruct (Hunt j Hjr Hjd Hji Hjl) as (_ & Hdata & _ & _).
          exact (Hdata k0). }
    assert (Hnamenone : dir_view data nrec !! name = None).
    { rewrite dir_view_lookup, Hnone. reflexivity. }
    assert (Hfwd : forall z : Z, fs_reachable P sb z ->
              fs_reachable P' sb z).
    { intros z Hz. unfold fs_reachable in *.
      apply (rch_mono (tree_of_disk P' sb) t ROOTINO); [| exact Hz].
      intros j f w0 Hj Hj' He.
      destruct (decide (j = d)) as [-> | Hjd].
      - rewrite Hentd.
        rewrite Hentt in He.
        destruct (decide (f = name)) as [-> | Hfn].
        + rewrite Hnamenone in He. discriminate.
        + rewrite lookup_insert_ne by (intros Hc; exact (Hfn (eq_sym Hc))).
          exact He.
      - rewrite (Hentother j f Hjd). exact He. }
    assert (Hbwd : forall z : Z, fs_reachable P' sb z ->
              fs_reachable P sb z \/ z = i).
    { intros z Hz. unfold fs_reachable in *.
      apply (rch_insert_back t (tree_of_disk P' sb) ROOTINO d i);
        [exact Hdre | | | exact Hz].
      - intros j f w0 Hj Hji He.
        destruct (decide (j = d)) as [-> | Hjd].
        + rewrite Hentd in He.
          destruct (decide (f = name)) as [-> | Hfn].
          * rewrite lookup_insert in He. injection He as He.
            right. exact (eq_sym He).
          * rewrite lookup_insert_ne in He
              by (intros Hc; exact (Hfn (eq_sym Hc))).
            left. rewrite Hentt. exact He.
        + left. rewrite <- (Hentother j f Hjd). exact He.
      - intros f w0 He.
        rewrite (tree_ent_nondir P' i f) in He; [discriminate |].
        rewrite (Hdec i HiN), decide_True by reflexivity.
        rewrite Htyi'. exact Hinotdir. }
    (* -------- the ticket supply --------------------------------------- *)
    assert (Hsegd : forall z : Z,
              Z.of_nat (fs_tick_count (fs_dir_tickets P' d dnd') z)
              = Z.of_nat (fs_tick_count (fs_dir_tickets P d dn) z)
                + Z.of_nat (otick (Some i) z)).
    { intros z. unfold fs_dir_tickets.
      fold data. fold szd nrec. rewrite Hszd'u. fold nrec'.
      rewrite (tick_omap_write (fs_rec_ticket P d dn)
                 (fs_rec_ticket P' d dnd') nrec nrec' k z Hnrecle Hknrec').
      - f_equal. f_equal.
        unfold fs_rec_ticket. cbv zeta.
        rewrite (proj2 (dir_liveb_true _ _)
                   (dir_written_live0 _ _ _ _ _ Hwrit Hwnz)).
        cbn [andb].
        rewrite Hwz, Hwu.
        rewrite bool_decide_eq_false_2 by (intros Hc; lia).
        cbn [negb]. reflexivity.
      - intros q Hq Hqk.
        unfold fs_rec_ticket. cbv zeta.
        rewrite (dir_liveb_agree _ _ q (Hwagree q Hqk)).
        rewrite (dir_inum_agree _ _ q (Hwagree q Hqk)).
        reflexivity.
      - intros q Hq Hqk.
        unfold fs_rec_ticket. cbv zeta.
        assert (Hz0 : dir_inum (fs_data_of P' dnd') q = bv_0 16).
        { destruct (decide (dir_inum (fs_data_of P' dnd') q = bv_0 16))
            as [He | Hne']; [exact He |].
          exfalso. exact (Hdead q Hq Hqk Hne'). }
        rewrite (proj2 (dir_liveb_false _ _) Hz0). reflexivity.
      - intros Hkn.
        unfold fs_rec_ticket. cbv zeta. fold data.
        assert (Hz0 : dir_inum data k = bv_0 16).
        { destruct (decide (dir_inum data k = bv_0 16))
            as [He | Hne']; [exact He |].
          exfalso. exact (Hfreek Hkn Hne'). }
        rewrite (proj2 (dir_liveb_false _ _) Hz0). reflexivity. }
    assert (Hcount : forall z : Z,
              Z.of_nat (fs_rtick P' sb rd z)
              = Z.of_nat (fs_rtick P sb rd z) + Z.of_nat (otick (Some i) z)).
    { intros z. unfold fs_rtick, fs_rtickets.
      rewrite (tick_mjoin_upd
                 (fun x : nat =>
                    if bool_decide (Z.of_nat x ∈ rd)
                    then fs_dir_tickets_at P sb (Z.of_nat x) else [])
                 (fun x : nat =>
                    if bool_decide (Z.of_nat x ∈ rd)
                    then fs_dir_tickets_at P' sb (Z.of_nat x) else [])
                 (Z.to_nat (sb_ninodes sb)) (Z.to_nat d) z
                 ltac:(clear -Hd; lia)).
      - rewrite Z2Nat.id by lia.
        rewrite bool_decide_eq_true_2 by exact Hd_rd.
        unfold fs_dir_tickets_at. cbv zeta.
        rewrite (Hdec d ltac:(irng)).
        rewrite decide_False by (intros Hc; exact (Hdi_ne Hc)).
        rewrite decide_True by reflexivity.
        rewrite Htyd'. fold dn.
        rewrite (proj2 (Z.eqb_eq _ _) Hdty).
        rewrite (Hsegd z). fold dn. lia.
      - intros x Hx Hxm. cbv beta.
        destruct (bool_decide (Z.of_nat x ∈ rd)) eqn:Hg; [| reflexivity].
        apply bool_decide_eq_true_1 in Hg.
        destruct (proj1 (Hrd _) Hg) as (Hxr & Hxty & _).
        assert (Hxd : Z.of_nat x <> d)
          by (intros Hc; apply Hxm; clear -Hc; lia).
        assert (Hxi : Z.of_nat x <> i)
          by (intros Hc; rewrite Hc in Hxty; exact (Hinotdir Hxty)).
        assert (Hxl : bv_unsigned (di_type (fs_dinode P sb (Z.of_nat x)))
                      <> 0)
          by (rewrite Hxty; unfold T_DIR_z; discriminate).
        apply tickets_at_untouched; [exact Hxr | |].
        + rewrite (Hdec (Z.of_nat x) (iblk_ix_range sb x Hx)).
          rewrite decide_False by exact Hxi.
          rewrite decide_False by exact Hxd. reflexivity.
        + intros _ k0 Hk0.
          destruct (Hunt _ Hxr Hxd Hxi Hxl) as (_ & Hdata & _ & _).
          exact (Hdata k0). }
    (* -------- the sweeps ---------------------------------------------- *)
    assert (Hdwfd : fs_inode_dwf P' sb dnd' = true).
    { pose proof (dwf_bool_at d Hd Hdlive) as Hold. fold dn in Hold.
      unfold fs_inode_dwf in Hold |- *. cbv zeta in Hold |- *.
      rewrite HindD, Haddrd', Htyd', Hszd'u, Hnb'.
      fold szd in Hold.
      rewrite !andb_true_iff in Hold |- *.
      destruct Hold as [[[[Ho1 Ho2] Ho3] Ho4] Ho5].
      repeat split; try assumption.
      apply Z.leb_le. lia. }
    assert (Hdwfi : fs_inode_dwf P' sb dni' = true).
    { pose proof (dwf_bool_at i ltac:(lia) Hilive) as Hold.
      fold dni in Hold.
      unfold fs_inode_dwf in Hold |- *. cbv zeta in Hold |- *.
      rewrite HindI, Haddri', Htyi', Hszi'.
      exact Hold. }
    assert (Hblkd : fs_inode_blocks P' dnd' = fs_inode_blocks P dn).
    { unfold fs_inode_blocks. cbv zeta.
      rewrite HindD, Haddrd', Hszd'u, Hnb'. fold szd. reflexivity. }
    assert (Hblki : fs_inode_blocks P' dni' = fs_inode_blocks P dni).
    { unfold fs_inode_blocks. cbv zeta.
      rewrite HindI, Haddri', Hszi'. reflexivity. }
    exists sb. split.
    { rewrite (fs_parse_sb_ext P P' HsbU). exact Hp. }
    constructor.
    - exact Hsb.
    - apply fs_inodes_dwf_intro. intros z Hz Hnz'.
      rewrite (Hdec z ltac:(irng)) in Hnz' |- *.
      destruct (decide (z = i)) as [-> | Hzi]; [exact Hdwfi |].
      destruct (decide (z = d)) as [-> | Hzd]; [exact Hdwfd |].
      destruct (Hunt z Hz Hzd Hzi Hnz') as (_ & _ & _ & Hdwf).
      rewrite Hdwf. exact (dwf_bool_at z Hz Hnz').
    - exists u. split.
      + assert (Hused : fs_used_blocks P' sb = fs_used_blocks P sb).
        { unfold fs_used_blocks. f_equal. apply list_fmap_ext.
          intros idx x Hx. apply lookup_seq in Hx as [-> Hidx].
          cbv beta zeta.
          rewrite (Hdec (Z.of_nat (0 + idx))
                     (iblk_ix_range sb (0 + idx) Hidx)).
          destruct (decide (Z.of_nat (0 + idx) = i)) as [Heq | Hzi].
          { rewrite Heq. fold dni. rewrite Htyi'.
            destruct (bv_unsigned (di_type dni) =? 0); [reflexivity |].
            exact Hblki. }
          destruct (decide (Z.of_nat (0 + idx) = d)) as [Heq | Hzd].
          { rewrite Heq. fold dn. rewrite Htyd'.
            destruct (bv_unsigned (di_type dn) =? 0); [reflexivity |].
            exact Hblkd. }
          destruct (bv_unsigned (di_type (fs_dinode P sb (Z.of_nat (0 + idx))))
                    =? 0) eqn:Ez; [reflexivity |].
          destruct (Hunt (Z.of_nat (0 + idx))
                      (inum_ix_range sb (0 + idx) Hidx) Hzd Hzi
                      (proj1 (Z.eqb_neq _ _) Ez)) as (_ & _ & Hbl & _).
          exact Hbl. }
        unfold fs_used_set. rewrite Hused. exact Hu.
      + unfold fs_bitmap_wf in Hbm |- *. cbv zeta in Hbm |- *.
        rewrite HbmU. exact Hbm.
    - (* the root *)
      destruct (decide (d = ROOTINO)) as [-> | Hdroot].
      + apply root_wf_intro.
        * rewrite (Htyp ROOTINO Hd). exact Hdty.
        * unfold fs_file_data.
          rewrite (Hdec ROOTINO (iblk_root_range sb Hnin1)).
          rewrite decide_False
            by (intros Hc; exact (Hdi_ne Hc)).
          rewrite decide_True by reflexivity.
          rewrite Hszd'u. fold nrec'. rewrite Hview.
          rewrite lookup_insert_ne
            by (intros Hc; exact (Hnamedd Hc)).
          pose proof (fs_root_wf_dotdot P sb HW7) as Hdd.
          unfold fs_file_data in Hdd. fold dn in Hdd.
          fold szd nrec data in Hdd. exact Hdd.
      + assert (Hrl : bv_unsigned (di_type (fs_dinode P sb ROOTINO)) <> 0).
        { rewrite (fs_root_wf_type P sb HW7). unfold T_DIR_z. lia. }
        assert (Hri : ROOTINO <> i).
        { intros Hc. apply Hinotdir. unfold dni. rewrite <- Hc.
          exact (fs_root_wf_type P sb HW7). }
        apply root_wf_untouched.
        * rewrite (Hdec ROOTINO (iblk_root_range sb Hnin1)).
          rewrite decide_False by (intros Hc; exact (Hri Hc)).
          rewrite decide_False by (intros Hc; exact (Hdroot (eq_sym Hc))).
          reflexivity.
        * intros k0 Hk0.
          destruct (Hunt ROOTINO
                      ltac:(pose proof Hnin1; unfold ROOTINO; lia)
                      ltac:(intros Hc; exact (Hdroot (eq_sym Hc)))
                      ltac:(intros Hc; exact (Hri Hc)) Hrl)
            as (_ & Hdata & _ & _).
          exact (Hdata k0).
    - (* the dots *)
      apply fs_dots_all_intro. intros z Hz Hdty'.
      rewrite (Hdec z ltac:(irng)) in Hdty' |- *.
      destruct (decide (z = i)) as [-> | Hzi].
      { exfalso. rewrite Htyi' in Hdty'. exact (Hinotdir Hdty'). }
      destruct (decide (z = d)) as [-> | Hzd].
      + apply (fs_dots_wf_win P P' d dn dnd').
        * fold szd. rewrite Hszd'u. exact Hszd'le.
        * intros j Hj. exact (Hwagree 0%nat ltac:(lia) j Hj).
        * intros j Hj. exact (Hwagree 1%nat ltac:(lia) j Hj).
        * exact (dots_bool_at d Hd Hdty).
      + assert (Hzl : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
          by (rewrite Hdty'; unfold T_DIR_z; discriminate).
        destruct (Hunt z Hz Hzd Hzi Hzl) as (_ & Hdata & _ & _).
        apply (fs_dots_wf_win P P' z (fs_dinode P sb z) (fs_dinode P sb z)).
        * lia.
        * apply (dir_win_agree_blocks _ _ FS_MAXFILE);
            [intros k0 Hk0; exact (Hdata k0)
            | unfold FS_MAXFILE, BSIZE; lia].
        * apply (dir_win_agree_blocks _ _ FS_MAXFILE);
            [intros k0 Hk0; exact (Hdata k0)
            | unfold FS_MAXFILE, BSIZE; lia].
        * exact (dots_bool_at z Hz Hdty').
    - (* the region *)
      exists nib. split; [exact Hnibz |].
      apply fs_region_wf_intro.
      + intros z Hz Hzn.
        rewrite (Hdec z ltac:(irng)).
        rewrite decide_False by lia.
        rewrite decide_False by lia.
        apply (fs_region_free_spec P sb nib z
                 (fs_region_wf_free P sb nib Hreg)); lia.
      + intros z Hz Hfree.
        rewrite (Hdec z ltac:(irng)) in Hfree |- *.
        destruct (decide (z = i)) as [-> | Hzi].
        { exfalso. rewrite Htyi' in Hfree. exact (Hilive Hfree). }
        destruct (decide (z = d)) as [-> | Hzd].
        { exfalso. rewrite Htyd' in Hfree. exact (Hdlive Hfree). }
        apply (fs_region_nlink_free P sb nib z
                 (fs_region_wf_nlink P sb nib Hreg)); [lia | exact Hfree].
      + intros z Hz.
        rewrite (Hdec z ltac:(irng)).
        destruct (decide (z = i)) as [-> | Hzi].
        * unfold dni'. unfold di_nlink_inc.
          cbn [di_nlink di_set_nlink].
          rewrite Z_to_bv_small;
            [pose proof Hnlcap as Hnlx; lia
             | assert (Hm16 : bv_modulus 16 = 65536) by reflexivity;
               pose proof (proj1 (bv_unsigned_in_range _ (di_nlink dni)));
               lia].
        * destruct (decide (z = d)) as [-> | Hzd].
          -- rewrite Hnlkd'.
             apply (fs_region_nlink_short P sb nib d
                      (fs_region_wf_nlink P sb nib Hreg)). lia.
          -- apply (fs_region_nlink_short P sb nib z
                      (fs_region_wf_nlink P sb nib Hreg)). lia.
    - (* the links *)
      exists rd.
      split; [| split; [| split]].
      + intros z. rewrite (Hrd z).
        destruct (decide (0 <= z < sb_ninodes sb)) as [Hzr | Hzr].
        * rewrite (Htyp z Hzr).
          split; intros (A & B & C); (split; [exact A |]);
            (split; [exact B |]).
          -- exact (Hfwd z C).
          -- destruct (Hbwd z C) as [Hre | Heq]; [exact Hre |].
             exfalso. rewrite Heq in B. exact (Hinotdir B).
        * split; intros (A & _); [lia | lia].
      + intros z Hz.
        destruct (proj1 (Hrd z) Hz) as (Hzr & Hzty & _).
        destruct (decide (z = d)) as [-> | Hzd].
        * (* the changed directory's bundle *)
          assert (Hdecd : fs_dinode P' sb d = dnd').
          { rewrite (Hdec d ltac:(irng)).
            rewrite decide_False
              by (intros Hc; exact (Hdi_ne Hc)).
            rewrite decide_True by reflexivity. reflexivity. }
          rewrite Hdecd.
          constructor.
          -- (* gran *)
             rewrite Hszd'u. unfold szd'.
             destruct (Z.max_spec szd (16 * (Z.of_nat k + 1)))
               as [[_ ->] | [_ ->]].
             ++ exists (Z.of_nat k + 1). lia.
             ++ exists qd. exact Hqd.
          -- (* ent *)
             intros k0 Hk0 Hlive'.
             rewrite Hszd'u in Hk0. fold nrec' in Hk0.
             destruct (decide (k0 = k)) as [-> | Hk0k].
             ++ rewrite Hwz, Hwu.
                split; [lia |].
                rewrite (Htyp i ltac:(lia)). fold dni.
                intros Hc. exact (Hilive Hc).
             ++ destruct (dir_written_class data (fs_data_of P' dnd')
                            nrec nrec' k name w k0 Hwrit Hdead Hk0
                            Hlive' Hk0k) as (Hk0n & Hlv).
                rewrite (dir_inum_agree _ _ k0 (Hwagree k0 Hk0k)).
                destruct (fdo_ent _ _ _ _ Hddok k0 Hk0n Hlv)
                  as (Hran & Hty0).
                fold data in Hran, Hty0.
                split; [exact Hran |].
                rewrite (Htyp (bv_unsigned (dir_inum data k0)) ltac:(lia)).
                exact Hty0.
          -- (* unique *)
             rewrite Hszd'u. fold nrec'.
             apply (dir_names_unique_write data _ nrec nrec' k name w);
               [| exact Hnrecle | exact Hknrec' | exact Hdead
                | exact Hnone | exact Hwrit].
             exact (fdo_unique _ _ _ _ Hddok).
          -- (* dot *)
             rewrite Hszd'u. fold nrec'. rewrite Hview.
             rewrite lookup_insert_ne
               by (intros Hc; exact (Hnamedot Hc)).
             exact (fdo_dot _ _ _ _ Hddok).
          -- (* dotdot *)
             rewrite Hszd'u. fold nrec'. rewrite Hview.
             rewrite lookup_insert_ne
               by (intros Hc; exact (Hnamedd Hc)).
             exact (fdo_dotdot _ _ _ _ Hddok).
        * assert (Hzi : z <> i)
            by (intros Hc; rewrite Hc in Hzty; exact (Hinotdir Hzty)).
          assert (Hzl : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
            by (rewrite Hzty; unfold T_DIR_z; discriminate).
          destruct (Hunt z Hzr Hzd Hzi Hzl) as (_ & Hdata & _ & _).
          apply dir_ok_untouched; [exact Hz | | |].
          -- rewrite (Hdec z (iblk_z_range sb z Hzr)).
             rewrite decide_False by exact Hzi.
             rewrite decide_False by exact Hzd. reflexivity.
          -- intros k0 Hk0. exact (Hdata k0).
          -- intros w0 Hw0 Hwl Hw0'. exfalso. apply Hwl.
             rewrite <- (Htyp w0 Hw0). exact Hw0'.
      + (* fs_links_gen *)
        intros z Hz. cbv zeta.
        rewrite (Hdec z ltac:(irng)).
        destruct (decide (z = i)) as [-> | Hzi].
        * rewrite Htyi'. intros Hnz.
          unfold dni'. unfold di_nlink_inc.
          cbn [di_nlink di_set_nlink].
          rewrite Z_to_bv_small
            by (assert (Hm16 : bv_modulus 16 = 65536) by reflexivity;
                pose proof (proj1 (bv_unsigned_in_range _ (di_nlink dni)));
                lia).
          pose proof (Hcount i) as Hc. unfold otick in Hc.
          rewrite bool_decide_eq_true_2 in Hc by reflexivity.
          pose proof (Hlkg i ltac:(lia) Hnz) as Hold. cbv zeta in Hold.
          fold dni in Hold.
          rewrite (bool_decide_eq_false_2
                     (bv_unsigned (di_type dni) = T_DIR_z) Hinotdir)
            in Hold.
          rewrite (bool_decide_eq_false_2
                     (bv_unsigned (di_type dni') = T_DIR_z));
            [| rewrite Htyi'; exact Hinotdir].
          lia.
        * destruct (decide (z = d)) as [-> | Hzd].
          -- rewrite Htyd'. intros Hnz.
             rewrite Hnlkd'.
             pose proof (Hcount d) as Hc. unfold otick in Hc.
             rewrite bool_decide_eq_false_2 in Hc
               by (intros Hcc; exact (Hdi_ne (eq_sym Hcc))).
             pose proof (Hlkg d Hz Hnz) as Hold. cbv zeta in Hold.
             fold dn in Hold.
             destruct (bool_decide (bv_unsigned (di_type dn) = T_DIR_z));
               destruct (bool_decide (d = ROOTINO)); (clear -Hc Hold; lia).
          -- intros Hnz.
             pose proof (Hcount z) as Hc. unfold otick in Hc.
             rewrite bool_decide_eq_false_2 in Hc
               by (intros Hcc; exact (Hzi (eq_sym Hcc))).
             pose proof (Hlkg z Hz Hnz) as Hold. cbv zeta in Hold.
             destruct (bool_decide
                         (bv_unsigned (di_type (fs_dinode P sb z))
                          = T_DIR_z));
               destruct (bool_decide (z = ROOTINO)); (clear -Hc Hold; lia).
      + (* orphans *)
        intros z Hz Hty' Hnin.
        rewrite (Hdec z ltac:(irng)) in Hty' |- *.
        destruct (decide (z = i)) as [-> | Hzi].
        { exfalso. rewrite Htyi' in Hty'. exact (Hinotdir Hty'). }
        destruct (decide (z = d)) as [-> | Hzd].
        { exfalso. exact (Hnin Hd_rd). }
        assert (Hzl : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
          by (rewrite Hty'; unfold T_DIR_z; discriminate).
        destruct (Hunt z Hz Hzd Hzi Hzl) as (_ & Hdata & _ & _).
        apply (dots_only_untouched P' (fs_dinode P sb z)).
        * exact (fdi_size _ _ _ (dok_at z Hz Hzl)).
        * intros k0 Hk0. exact (Hdata k0).
        * exact (Horph z Hz Hty' Hnin).
  Qed.

End EffLinkEntry.

(* the [fs_durable_wf_view]-level wrappers -- the shape stage G2
   consumes: the invariant of the OLD view, the decode-level
   preconditions, the invariant of the updated view. *)

Lemma eff_link_entry_wfv (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (name : fname) (i : Z) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 <= d < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
  fs_reachable P sb d ->
  0 < i < sb_ninodes sb -> i < 65536 ->
  (bv_unsigned (di_type (fs_dinode P sb i)) = T_FILE_z
   \/ bv_unsigned (di_type (fs_dinode P sb i)) = T_DEVICE_z) ->
  bv_unsigned (di_nlink (fs_dinode P sb i)) < 32767 ->
  (length name <= 14)%nat -> nonul name ->
  dir_first (fs_file_data P sb d)
    (dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))) name = None ->
  ((k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat
     /\ ~ dir_live (fs_file_data P sb d) k
   \/ k = dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))
     /\ 16 * (Z.of_nat k + 1)
        <= fs_nblk (bv_unsigned (di_size (fs_dinode P sb d))) * BSIZE_z) ->
  fs_durable_wf_view (eff_link_entry P sb d k name i).
Proof.
  intros Hv Hp. intros.
  destruct Hv as (sb0 & Hp0 & Hsw).
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
  destruct HW45 as (u & Hu & Hbm).
  destruct Hregx as (nib & Hnibz & Hreg).
  destruct HW9 as (rd & Hrd & Hdok & Hlkg & Horph).
  apply (eff_link_entry_wf P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph); assumption.
Qed.
