(* FsEffCreateEntry.v -- durable-disk stage F2, effect 3: creating an
   entry for a FRESH inum -- create/mknod's arm, and mkdir's (which also
   lays down the child's dots block and the parent's extra link). *)
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

Section EffCreateEntry.
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
  (*  20.  EFFECT 3a -- CREATING A NON-DIRECTORY ENTRY                     *)
  (*                                                                       *)
  (*  create/mknod's net: a dirent for a FRESH inum, whose record becomes  *)
  (*  a live dinode of the given type with one link (and the device pair   *)
  (*  for T_DEVICE).                                                       *)
  (* ==================================================================== *)

  Definition eff_create_entry (d : Z) (k : nat) (name : fname) (i : Z)
      (ty maj min : bv 16) : Z -> list (bv 8) :=
    let dnd := fs_dinode P sb d in
    let szd' := Z.max (bv_unsigned (di_size dnd)) (16 * (Z.of_nat k + 1)) in
    let a := fs_blk_addr P dnd (k / 64)%nat in
    fs_upd
      (eff_dinode
         (eff_dinode P sb d (di_set_size dnd (Z_to_bv 32 szd')))
         sb i (di_create ty maj min))
      a
      (fs_splice (P a) (16 * (k mod 64)) 16
         (fun j => dirent_bytes (de_of_name (Z_to_bv 16 i) name) !!! j)).

  Lemma eff_create_entry_wf (d : Z) (k : nat) (name : fname) (i : Z)
      (ty maj min : bv 16) :
    0 <= d < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
    fs_reachable P sb d ->
    0 < i < sb_ninodes sb -> i < 65536 ->
    bv_unsigned (di_type (fs_dinode P sb i)) = 0 ->
    (bv_unsigned ty = T_FILE_z \/ bv_unsigned ty = T_DEVICE_z) ->
    (length name <= 14)%nat -> nonul name ->
    dir_first (fs_file_data P sb d)
      (dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))) name = None ->
    ((k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat
       /\ ~ dir_live (fs_file_data P sb d) k
     \/ k = dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))
       /\ 16 * (Z.of_nat k + 1)
          <= fs_nblk (bv_unsigned (di_size (fs_dinode P sb d))) * BSIZE_z) ->
    fs_durable_wf_view (eff_create_entry d k name i ty maj min).
  Proof.
    intros Hd Hdty Hdre Hi Hi16 Hifree Hty Hlen Hnn Hnone Harm.
    assert (Hm32 : bv_modulus 32 = 4294967296) by reflexivity.
    set (dn := fs_dinode P sb d) in *.
    set (dni := fs_dinode P sb i) in *.
    unfold fs_file_data in Hnone, Harm. fold dn in Hnone, Harm.
    set (szd := bv_unsigned (di_size dn)) in *.
    set (nrec := dir_nrec szd) in *.
    set (data := fs_data_of P dn) in *.
    set (szd' := Z.max szd (16 * (Z.of_nat k + 1))).
    set (dnd' := di_set_size dn (Z_to_bv 32 szd')).
    set (dni' := di_create ty maj min).
    set (w := Z_to_bv 16 i).
    set (P' := eff_create_entry d k name i ty maj min).
    assert (Hdlive : bv_unsigned (di_type dn) <> 0)
      by (rewrite Hdty; unfold T_DIR_z; discriminate).
    assert (Htyi' : bv_unsigned (di_type dni') = bv_unsigned ty)
      by reflexivity.
    assert (Hinotdir' : bv_unsigned (di_type dni') <> T_DIR_z)
      by (rewrite Htyi'; unfold T_FILE_z, T_DEVICE_z, T_DIR_z in *; lia).
    assert (Hilive' : bv_unsigned (di_type dni') <> 0)
      by (rewrite Htyi'; unfold T_FILE_z, T_DEVICE_z in *; lia).
    assert (Hdi_ne : d <> i).
    { intros Hc.
      assert (Hc2 : bv_unsigned (di_type dn) = 0).
      { unfold dn. rewrite Hc. exact Hifree. }
      rewrite Hdty in Hc2. unfold T_DIR_z in Hc2. lia. }
    assert (Hd_rd : d ∈ rd)
      by (apply (Hrd d); split; [lia | split; [exact Hdty | exact Hdre]]).
    pose proof (Hdok d Hd_rd) as Hddok. fold dn in Hddok.
    pose proof (dok_at d Hd Hdlive) as Hdok_d. fold dn in Hdok_d.
    pose proof (fdi_size _ _ _ Hdok_d) as Hcapd. fold dn in Hcapd.
    pose proof (proj1 (bv_unsigned_in_range _ (di_size dn))) as Hsz0.
    destruct (dots_flat d Hd Hdty) as
      (Hnrec2 & Hlv0 & Hin0 & Hbn0 & Hlv1 & Hbn1).
    fold dn data in Hnrec2, Hlv0, Hin0, Hbn0, Hlv1, Hbn1.
    fold szd nrec in Hnrec2.
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
    assert (Hwfd' : dinode_wf dnd')
      by (apply di_set_size_wf, fs_dinode_wf).
    assert (Hwfi' : dinode_wf dni') by (apply di_create_wf).
    assert (Hwu : bv_unsigned w = i).
    { unfold w. apply Z_to_bv_small.
      assert (Hm16 : bv_modulus 16 = 65536) by reflexivity. lia. }
    assert (Hwnz : w <> bv_0 16).
    { intros Hc.
      assert (Hc' : bv_unsigned w = 0) by (rewrite Hc; reflexivity).
      lia. }
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
    assert (Ha_in : fs_blk_addr P dn (k / 64) ∈ fs_inode_ents P dn).
    { rewrite <- (fs_slot_blk dn (k / 64)%nat HkbM).
      apply (fs_inode_ents_slot P dn); [lia |].
      rewrite (fs_slot_blk dn (k / 64)%nat HkbM). exact Ha0. }
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
    { intros b Hb1 Hb2 Hb3. unfold P', eff_create_entry. cbv zeta.
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
    { unfold P', eff_create_entry. cbv zeta. fold dn. apply fs_upd_at. }
    assert (Hdec : forall z : Z, 0 <= z < 16 * (sb_ninodes sb / 16 + 1) ->
              fs_dinode P' sb z
              = if decide (z = i) then dni'
                else if decide (z = d) then dnd' else fs_dinode P sb z).
    { intros z Hz.
      transitivity (fs_dinode
                      (eff_dinode
                         (eff_dinode P sb d dnd') sb i dni') sb z).
      - apply fs_dinode_ext. unfold P', eff_create_entry. cbv zeta.
        fold dn. fold dnd'.
        apply fs_upd_ne.
        destruct (iblock_bounds sb Hok z Hz) as (Hz1 & Hz2 & Hz3).
        unfold fs_data_start in Ha_rng. lia.
      - rewrite (eff_dinode_dec sb Hok _ i dni' z Hwfi' HiN Hz).
        destruct (decide (z = i)) as [-> | Hzi]; [reflexivity |].
        exact (eff_dinode_dec sb Hok P d dnd' z Hwfd' HdN Hz). }
    assert (Hslotinj : fs_slot_inj P dn) by (apply (slot_inj_at d Hd Hdlive)).
    assert (Hother : forall k' : nat, k' <> (k / 64)%nat ->
              fs_blk_addr P dn k' <> 0 ->
              P' (fs_blk_addr P dn k') = P (fs_blk_addr P dn k')).
    { intros k' Hne Hnz.
      destruct (Nat.lt_ge_cases k' FS_MAXFILE) as [Hk' | Hk'].
      - assert (Hrng : fs_data_start sb <= fs_blk_addr P dn k' < sb_size sb).
        { (* the ENTRY clauses: a nonzero address is a data block,
             whatever the size says (durable-disk F3.1) *)
          exact (fs_blk_addr_range P sb dn k' Hdok_d Hk' Hnz). }
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
                     ∈ fs_inode_ents P dn).
      { rewrite <- (fs_slot_max P dn).
        apply (fs_inode_ents_slot P dn); [lia |].
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
              /\ fs_inode_ents P' (fs_dinode P sb z)
                 = fs_inode_ents P (fs_dinode P sb z)
              /\ fs_inode_dwf P' sb (fs_dinode P sb z)
                 = fs_inode_dwf P sb (fs_dinode P sb z)).
    { intros z Hz Hnd' Hni' Hnz. apply inode_untouched; try assumption.
      intros b Hb. apply HaE.
      - intros ->. exact (blocks_cross z d _ Hz Hd Hnd' Hnz Hdlive Hb Ha_in).
      - pose proof (blocks_range z b Hz Hnz Hb) as Hbr.
        unfold fs_data_start in Hbr. clear -Hbr Hibd3 Hibi3. lia.
      - pose proof (blocks_range z b Hz Hnz Hb) as Hbr.
        unfold fs_data_start in Hbr. clear -Hbr Hibd3 Hibi3. lia. }
    (* the fresh record's readers: everything is zero *)
    assert (Hsizei' : di_size dni' = bv_0 32) by reflexivity.
    assert (Haddri' : di_addrs dni' = replicate 13 (bv_0 32)) by reflexivity.
    assert (Hdwfi : fs_inode_dwf P' sb dni' = true).
    { apply (zeroed_dwf P' dni' Hsizei' Haddri').
      rewrite Htyi'. unfold T_FILE_z, T_DEVICE_z in Hty. tauto. }
    assert (Hblki : fs_inode_ents P' dni' = []).
    { exact (zeroed_blocks_nil P' dni' Haddri'). }
    (* the written record, at the view *)
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
    (* --- the tree ------------------------------------------------------ *)
    assert (Htyp : forall z : Z, 0 <= z < sb_ninodes sb -> z <> i ->
              bv_unsigned (di_type (fs_dinode P' sb z))
              = bv_unsigned (di_type (fs_dinode P sb z))).
    { intros z Hz Hzi. rewrite (Hdec z ltac:(irng)).
      rewrite decide_False by exact Hzi.
      destruct (decide (z = d)) as [-> | Hzd];
        [rewrite Htyd'; reflexivity | reflexivity]. }
    assert (Hentd : forall f : fname,
              tree_ent (tree_of_disk P' sb) d f
              = <[name := i]> (dir_view data nrec) !! f).
    { intros f.
      rewrite (tree_ent_dir_eq P' d Hd)
        by (rewrite (Htyp d Hd ltac:(intros Hc; exact (Hdi_ne Hc)));
            exact Hdty).
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
          unfold dni in Hifree. rewrite Hifree. unfold T_DIR_z. lia.
        + rewrite (Hdec i HiN), decide_True by reflexivity.
          exact Hinotdir'.
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
        exact Hinotdir'. }
    (* --- the supply gains one ticket ----------------------------------- *)
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
          by (intros Hc; rewrite Hc in Hxty; unfold dni in Hifree;
              rewrite Hifree in Hxty; unfold T_DIR_z in Hxty; lia).
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
    assert (Hcnt0 : fs_rtick P sb rd i = 0%nat)
      by (exact (rtick_free i ltac:(lia) ltac:(exact Hifree))).
    (* --- the remaining sweeps ------------------------------------------ *)
    assert (Hdwfd : fs_inode_dwf P' sb dnd' = true).
    { pose proof (dwf_bool_at d Hd Hdlive) as Hold. fold dn in Hold.
      unfold fs_inode_dwf in Hold |- *. cbv zeta in Hold |- *.
      rewrite HindD, Haddrd', Htyd', Hszd'u, Hnb'.
      fold szd in Hold.
      rewrite !andb_true_iff in Hold |- *.
      destruct Hold as [[[[Ho1 Ho2] Ho3] Ho4] Ho5].
      repeat split; try assumption.
      apply Z.leb_le. lia. }
    assert (Hblkd : fs_inode_ents P' dnd' = fs_inode_ents P dn).
    { (* the entry list does not read the size (durable-disk F3.1) *)
      apply fs_inode_ents_det; assumption. }
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
      + assert (Hused : fs_ent_blocks P' sb = fs_ent_blocks P sb).
        { unfold fs_ent_blocks. f_equal. apply list_fmap_ext.
          intros idx x Hx. apply lookup_seq in Hx as [-> Hidx].
          cbv beta zeta.
          rewrite (Hdec (Z.of_nat (0 + idx))
                     (iblk_ix_range sb (0 + idx) Hidx)).
          destruct (decide (Z.of_nat (0 + idx) = i)) as [Heq | Hzi].
          { rewrite Heq. fold dni.
            rewrite (proj2 (Z.eqb_neq _ _) Hilive').
            rewrite (proj2 (Z.eqb_eq _ _) Hifree).
            rewrite Hblki. reflexivity. }
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
        unfold fs_ent_set. rewrite Hused. exact Hu.
      + unfold fs_bitmap_wf in Hbm |- *. cbv zeta in Hbm |- *.
        rewrite HbmU. exact Hbm.
    - (* the root *)
      assert (Hri : ROOTINO <> i).
      { intros Hc.
        pose proof (fs_root_wf_type P sb HW7) as Hr.
        rewrite Hc in Hr. unfold dni in Hifree. rewrite Hifree in Hr.
        unfold T_DIR_z in Hr. lia. }
      destruct (decide (d = ROOTINO)) as [-> | Hdroot].
      + apply root_wf_intro.
        * rewrite (Htyp ROOTINO Hd ltac:(intros Hc; exact (Hdi_ne Hc))).
          exact Hdty.
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
      { exfalso. exact (Hinotdir' Hdty'). }
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
    - exists nib. split; [exact Hnibz |].
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
        { exfalso. exact (Hilive' Hfree). }
        destruct (decide (z = d)) as [-> | Hzd].
        { exfalso. rewrite Htyd' in Hfree. exact (Hdlive Hfree). }
        apply (fs_region_nlink_free P sb nib z
                 (fs_region_wf_nlink P sb nib Hreg)); [lia | exact Hfree].
      + intros z Hz.
        rewrite (Hdec z ltac:(irng)).
        destruct (decide (z = i)) as [-> | Hzi].
        * unfold dni'. unfold di_create. cbn [di_nlink].
          change (bv_unsigned (Z_to_bv 16 1)) with 1. lia.
        * destruct (decide (z = d)) as [-> | Hzd].
          -- rewrite Hnlkd'.
             apply (fs_region_nlink_short P sb nib d
                      (fs_region_wf_nlink P sb nib Hreg)). lia.
          -- apply (fs_region_nlink_short P sb nib z
                      (fs_region_wf_nlink P sb nib Hreg)). lia.
    - exists rd.
      split; [| split; [| split]].
      + intros z. rewrite (Hrd z).
        destruct (decide (z = i)) as [-> | Hzi].
        { split.
          - intros (_ & Hc & _). exfalso.
            unfold dni in Hifree. rewrite Hifree in Hc.
            unfold T_DIR_z in Hc. lia.
          - intros (_ & Hc & _). exfalso.
            rewrite (Hdec i HiN), decide_True in Hc by reflexivity.
            exact (Hinotdir' Hc). }
        destruct (decide (0 <= z < sb_ninodes sb)) as [Hzr | Hzr].
        * rewrite (Htyp z Hzr Hzi).
          split; intros (A & B & C); (split; [exact A |]);
            (split; [exact B |]).
          -- exact (Hfwd z C).
          -- destruct (Hbwd z C) as [Hre | Heq]; [exact Hre |].
             exfalso. exact (Hzi Heq).
        * split; intros (A & _); [lia | lia].
      + intros z Hz.
        destruct (proj1 (Hrd z) Hz) as (Hzr & Hzty & _).
        assert (Hzi : z <> i)
          by (intros Hc; rewrite Hc in Hzty; unfold dni in Hifree;
              rewrite Hifree in Hzty; unfold T_DIR_z in Hzty; lia).
        destruct (decide (z = d)) as [-> | Hzd].
        * assert (Hdecd : fs_dinode P' sb d = dnd').
          { rewrite (Hdec d ltac:(irng)).
            rewrite decide_False
              by (intros Hc; exact (Hdi_ne Hc)).
            rewrite decide_True by reflexivity. reflexivity. }
          rewrite Hdecd.
          constructor.
          -- rewrite Hszd'u. unfold szd'.
             destruct (Z.max_spec szd (16 * (Z.of_nat k + 1)))
               as [[_ ->] | [_ ->]].
             ++ exists (Z.of_nat k + 1). lia.
             ++ exists qd. exact Hqd.
          -- intros k0 Hk0 Hlive'.
             rewrite Hszd'u in Hk0. fold nrec' in Hk0.
             destruct (decide (k0 = k)) as [-> | Hk0k].
             ++ rewrite Hwz, Hwu.
                split; [lia |].
                rewrite (Hdec i HiN), decide_True by reflexivity.
                exact Hilive'.
             ++ destruct (dir_written_class data (fs_data_of P' dnd')
                            nrec nrec' k name w k0 Hwrit Hdead Hk0
                            Hlive' Hk0k) as (Hk0n & Hlv).
                rewrite (dir_inum_agree _ _ k0 (Hwagree k0 Hk0k)).
                destruct (fdo_ent _ _ _ _ Hddok k0 Hk0n Hlv)
                  as (Hran & Hty0).
                fold data in Hran, Hty0.
                split; [exact Hran |].
                assert (Hti : bv_unsigned (dir_inum data k0) <> i).
                { intros Hc. rewrite Hc in Hty0.
                  unfold dni in Hifree. exact (Hty0 Hifree). }
                rewrite (Htyp (bv_unsigned (dir_inum data k0))
                           ltac:(lia) Hti).
                exact Hty0.
          -- rewrite Hszd'u. fold nrec'.
             apply (dir_names_unique_write data _ nrec nrec' k name w);
               [| exact Hnrecle | exact Hknrec' | exact Hdead
                | exact Hnone | exact Hwrit].
             exact (fdo_unique _ _ _ _ Hddok).
          -- rewrite Hszd'u. fold nrec'. rewrite Hview.
             rewrite lookup_insert_ne
               by (intros Hc; exact (Hnamedot Hc)).
             exact (fdo_dot _ _ _ _ Hddok).
          -- rewrite Hszd'u. fold nrec'. rewrite Hview.
             rewrite lookup_insert_ne
               by (intros Hc; exact (Hnamedd Hc)).
             exact (fdo_dotdot _ _ _ _ Hddok).
        * assert (Hzl : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
            by (rewrite Hzty; unfold T_DIR_z; discriminate).
          destruct (Hunt z Hzr Hzd Hzi Hzl) as (_ & Hdata & _ & _).
          apply dir_ok_untouched; [exact Hz | | |].
          -- rewrite (Hdec z (iblk_z_range sb z Hzr)).
             rewrite decide_False by exact Hzi.
             rewrite decide_False by exact Hzd. reflexivity.
          -- intros k0 Hk0. exact (Hdata k0).
          -- intros w0 Hw0 Hwl Hw0'.
             destruct (decide (w0 = i)) as [-> | Hwne].
             ++ exfalso.
                rewrite (Hdec i HiN), decide_True in Hw0'
                  by reflexivity.
                exact (Hilive' Hw0').
             ++ exfalso. apply Hwl.
                rewrite <- (Htyp w0 Hw0 Hwne). exact Hw0'.
      + intros z Hz. cbv zeta.
        rewrite (Hdec z ltac:(irng)).
        destruct (decide (z = i)) as [-> | Hzi].
        * intros _.
          unfold dni'. unfold di_create. cbn [di_nlink di_type].
          change (bv_unsigned (Z_to_bv 16 1)) with 1.
          pose proof (Hcount i) as Hc. unfold otick in Hc.
          rewrite bool_decide_eq_true_2 in Hc by reflexivity.
          rewrite Hcnt0 in Hc.
          rewrite (bool_decide_eq_false_2 (bv_unsigned ty = T_DIR_z))
            by (unfold T_FILE_z, T_DEVICE_z, T_DIR_z in *; lia).
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
      + intros z Hz Hty' Hnin.
        rewrite (Hdec z ltac:(irng)) in Hty' |- *.
        destruct (decide (z = i)) as [-> | Hzi].
        { exfalso. exact (Hinotdir' Hty'). }
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

  (* the used set after one inode GAINS the block list [fb] (create-dir's
     dots block; alloc's shape is the same with a longer segment) *)
  Local Lemma used_add (P' : Z -> list (bv 8)) (i : Z) (nb : list Z) :
    0 <= i < sb_ninodes sb ->
    ((if bv_unsigned (di_type (fs_dinode P sb i)) =? 0 then []
      else fs_inode_ents P (fs_dinode P sb i)) = []) ->
    ((if bv_unsigned (di_type (fs_dinode P' sb i)) =? 0 then []
      else fs_inode_ents P' (fs_dinode P' sb i)) = nb) ->
    NoDup nb ->
    (forall b : Z, b ∈ nb -> b ∉ u) ->
    (forall z : Z, 0 <= z < sb_ninodes sb -> z <> i ->
       (if bv_unsigned (di_type (fs_dinode P' sb z)) =? 0 then []
        else fs_inode_ents P' (fs_dinode P' sb z))
       = (if bv_unsigned (di_type (fs_dinode P sb z)) =? 0 then []
          else fs_inode_ents P (fs_dinode P sb z))) ->
    exists u'' : gset Z,
      fs_ent_set P' sb = Some u''
      /\ (forall b : Z, b ∈ u'' <-> (b ∈ u \/ b ∈ nb)).
  Proof.
    intros Hi Hoi Hni Hnd0 Hfresh Hsame.
    set (n := Z.to_nat (sb_ninodes sb)).
    set (F := fun x : nat =>
                let dn0 := fs_dinode P sb (Z.of_nat x) in
                if bv_unsigned (di_type dn0) =? 0 then []
                else fs_inode_ents P dn0).
    set (G := fun x : nat =>
                let dn0 := fs_dinode P' sb (Z.of_nat x) in
                if bv_unsigned (di_type dn0) =? 0 then []
                else fs_inode_ents P' dn0).
    assert (HFold : fs_ent_blocks P sb = mjoin (F <$> seq 0 n))
      by reflexivity.
    assert (HGold : fs_ent_blocks P' sb = mjoin (G <$> seq 0 n))
      by reflexivity.
    assert (HFi : F (Z.to_nat i) = []).
    { unfold F. cbv zeta. rewrite Z2Nat.id by lia. exact Hoi. }
    assert (HGi : G (Z.to_nat i) = nb).
    { unfold G. cbv zeta. rewrite Z2Nat.id by lia. exact Hni. }
    assert (Hext : forall x : nat, x <> Z.to_nat i -> (x < n)%nat ->
              G x = F x).
    { intros x Hx Hxn. unfold G, F. cbv zeta.
      apply Hsame; [unfold n in Hxn; lia | lia]. }
    assert (HsplF : mjoin (F <$> seq 0 n)
                    = (mjoin (F <$> seq 0 (Z.to_nat i)) ++ F (Z.to_nat i)
                       ++ mjoin (F <$> seq (S (Z.to_nat i))
                                   (n - S (Z.to_nat i))))%list)
      by (apply mjoin_seq_split; unfold n; lia).
    assert (HsplG : mjoin (G <$> seq 0 n)
                    = (mjoin (F <$> seq 0 (Z.to_nat i)) ++ nb
                       ++ mjoin (F <$> seq (S (Z.to_nat i))
                                   (n - S (Z.to_nat i))))%list).
    { rewrite (mjoin_seq_split G n (Z.to_nat i)) by (unfold n; lia).
      rewrite HGi.
      rewrite (tick_mjoin_ext F G 0 (Z.to_nat i))
        by (intros x Hx; apply Hext; lia).
      rewrite (tick_mjoin_ext F G (S (Z.to_nat i)) (n - S (Z.to_nat i)))
        by (intros x Hx; apply Hext; lia).
      reflexivity. }
    assert (Hold_mem : forall b : Z,
              b ∈ (mjoin (F <$> seq 0 (Z.to_nat i))
                   ++ mjoin (F <$> seq (S (Z.to_nat i))
                               (n - S (Z.to_nat i))))%list
              <-> b ∈ u).
    { intros b.
      rewrite (fs_ent_set_elem P sb u b Hu).
      rewrite HFold, HsplF, HFi.
      rewrite app_nil_l.
      reflexivity. }
    assert (Hnd_old : NoDup (mjoin (F <$> seq 0 (Z.to_nat i))
                             ++ mjoin (F <$> seq (S (Z.to_nat i))
                                         (n - S (Z.to_nat i))))%list).
    { pose proof Hnd as Hnd1. rewrite HFold, HsplF, HFi in Hnd1.
      rewrite app_nil_l in Hnd1. exact Hnd1. }
    apply stdpp.list_relations.NoDup_app in Hnd_old.
    destruct Hnd_old as (Hnd1 & Hdisj12 & Hnd2).
    assert (Hnd' : NoDup (fs_ent_blocks P' sb)).
    { rewrite HGold, HsplG.
      apply stdpp.list_relations.NoDup_app.
      split; [exact Hnd1 |]. split.
      - intros b Hb1 Hb2.
        apply elem_of_app in Hb2 as [Hb2 | Hb2].
        + apply (Hfresh b Hb2). apply Hold_mem.
          apply elem_of_app. left. exact Hb1.
        + exact (Hdisj12 b Hb1 Hb2).
      - apply stdpp.list_relations.NoDup_app.
        split; [exact Hnd0 |]. split; [| exact Hnd2].
        intros b Hb1 Hb2.
        apply (Hfresh b Hb1). apply Hold_mem.
        apply elem_of_app. right. exact Hb2. }
    destruct (gset_nodup_of_NoDup (fs_ent_blocks P' sb) Hnd')
      as (u'' & Hu'').
    exists u''. split; [exact Hu'' |].
    intros b.
    rewrite (gset_nodup_set _ _ Hu'' b).
    rewrite HGold, HsplG.
    rewrite !elem_of_app.
    rewrite <- (Hold_mem b). rewrite elem_of_app.
    tauto.
  Qed.

  (* ---- the freshly created directory's two records --------------------- *)

  Local Lemma dot_name_len : (length dot_name <= 14)%nat.
  Proof. cbn. lia. Qed.

  Local Lemma dotdot_name_len : (length dotdot_name <= 14)%nat.
  Proof. cbn. lia. Qed.

  Local Lemma dot_name_nonul : nonul dot_name.
  Proof.
    unfold nonul, dot_name. apply Forall_cons_2; [| apply Forall_nil_2].
    intros Hc.
    assert (Hcu : bv_unsigned (Z_to_bv 8 0x2e) = bv_unsigned NUL)
      by (rewrite Hc; reflexivity).
    change (bv_unsigned (Z_to_bv 8 0x2e)) with 46 in Hcu.
    change (bv_unsigned NUL) with 0 in Hcu. lia.
  Qed.

  Local Lemma dotdot_name_nonul : nonul dotdot_name.
  Proof.
    unfold nonul, dotdot_name.
    apply Forall_cons_2; [| apply Forall_cons_2; [| apply Forall_nil_2]];
      intros Hc;
      (assert (Hcu : bv_unsigned (Z_to_bv 8 0x2e) = bv_unsigned NUL)
        by (rewrite Hc; reflexivity));
      change (bv_unsigned (Z_to_bv 8 0x2e)) with 46 in Hcu;
      change (bv_unsigned NUL) with 0 in Hcu; lia.
  Qed.

  Local Lemma dot_ne_dotdot : dot_name <> dotdot_name.
  Proof. intros Hc. inversion Hc. Qed.

  Local Lemma child_facts (P' : Z -> list (bv 8)) (i d fb : Z) :
    0 < i -> i < 65536 -> 0 < d -> d < 65536 ->
    0 < fb -> fb < 4294967296 ->
    P' fb = dirblk_bytes
              ([de_of_name (Z_to_bv 16 i) dot_name;
                de_of_name (Z_to_bv 16 d) dotdot_name]
               ++ replicate 62 dirent_zero) ->
    dir_inum (fs_data_of P' (di_create_dir fb)) 0 = Z_to_bv 16 i
    /\ dir_bname (fs_data_of P' (di_create_dir fb)) 0 = dot_name
    /\ dir_inum (fs_data_of P' (di_create_dir fb)) 1 = Z_to_bv 16 d
    /\ dir_bname (fs_data_of P' (di_create_dir fb)) 1 = dotdot_name.
  Proof.
    intros Hi0 Hi16 Hd0 Hd16 Hfb0 Hfb32 Hfb.
    set (dsc := ([de_of_name (Z_to_bv 16 i) dot_name;
                  de_of_name (Z_to_bv 16 d) dotdot_name]
                 ++ replicate 62 dirent_zero)%list).
    assert (Hwfc : Forall dirent_wf dsc).
    { unfold dsc. apply Forall_app. split.
      - apply Forall_cons_2; [apply de_of_name_wf |].
        apply Forall_cons_2; [apply de_of_name_wf | apply Forall_nil_2].
      - apply Forall_replicate. apply dirent_zero_wf. }
    assert (Hlenc : length dsc = 64%nat).
    { unfold dsc. rewrite length_app, length_replicate. reflexivity. }
    assert (Haddr0 : fs_blk_addr P' (di_create_dir fb) 0 = fb).
    { unfold fs_blk_addr. cbn [Nat.ltb Nat.leb].
      unfold di_create_dir. cbn [di_addrs].
      rewrite list_lookup_total_insert
        by (rewrite length_replicate; lia).
      apply Z_to_bv_small. unfold bv_modulus.
      change (2 ^ Z.of_N 32) with 4294967296. lia. }
    assert (Hbyte : forall x : nat, (x < 1024)%nat ->
              file_byte (fs_data_of P' (di_create_dir fb)) x
              = dirblk_bytes dsc !!! x).
    { intros x Hx. unfold file_byte.
      destruct (nat_block_split 0 x Hx) as (Hd' & Hm').
      cbn [Nat.mul Nat.add] in Hd', Hm'. rewrite Hd', Hm'.
      rewrite fs_data_of_addr, Haddr0.
      rewrite (proj2 (Z.eqb_neq fb 0) ltac:(lia)).
      rewrite Hfb. reflexivity. }
    assert (Hwin : forall (k0 : nat) (de0 : dirent), (k0 < 64)%nat ->
              dsc !! k0 = Some de0 ->
              forall j : nat, (j < 16)%nat ->
                file_byte (fs_data_of P' (di_create_dir fb))
                  (16 * k0 + j)%nat
                = dirent_bytes de0 !!! j).
    { intros k0 de0 Hk0 Hlk j Hj.
      rewrite (Hbyte (16 * k0 + j)%nat) by lia.
      rewrite (dirblk_bytes_lookup_t dsc k0 j Hwfc
                 ltac:(rewrite Hlenc; exact Hk0) Hj).
      rewrite (list_lookup_total_correct _ _ _ Hlk). reflexivity. }
    destruct (dir_record_of_name (fs_data_of P' (di_create_dir fb)) 0
                (Z_to_bv 16 i) dot_name dot_name_len dot_name_nonul)
      as (Hi1 & Hb1).
    { intros j Hj. apply (Hwin 0%nat _ ltac:(lia)); [reflexivity | lia]. }
    destruct (dir_record_of_name (fs_data_of P' (di_create_dir fb)) 1
                (Z_to_bv 16 d) dotdot_name dotdot_name_len
                dotdot_name_nonul)
      as (Hi2 & Hb2).
    { intros j Hj. apply (Hwin 1%nat _ ltac:(lia)); [reflexivity | lia]. }
    tauto.
  Qed.


  (* ==================================================================== *)
  (*  21.  EFFECT 3b -- CREATING A DIRECTORY ENTRY (mkdir)                 *)
  (*                                                                       *)
  (*  The dirent, a fresh dinode of type T_DIR with ONE data block         *)
  (*  holding the two dot records, that block's bitmap bit, and the        *)
  (*  parent's extra link (paid for by the child's "..").                  *)
  (* ==================================================================== *)

  Definition eff_create_dir_entry (d : Z) (k : nat) (name : fname)
      (i fb : Z) : Z -> list (bv 8) :=
    let dnd := fs_dinode P sb d in
    let szd' := Z.max (bv_unsigned (di_size dnd)) (16 * (Z.of_nat k + 1)) in
    let a := fs_blk_addr P dnd (k / 64)%nat in
    fs_upd
      (fs_upd
         (fs_upd
            (eff_dinode
               (eff_dinode P sb d
                  (di_nlink_inc (di_set_size dnd (Z_to_bv 32 szd'))))
               sb i (di_create_dir fb))
            (sb_bmapstart sb)
            (bm_bytes BSIZE
               (fs_bmap_set BSIZE (P (sb_bmapstart sb)) ∪ {[fb]})))
         fb
         (dirblk_bytes
            ([de_of_name (Z_to_bv 16 i) dot_name;
              de_of_name (Z_to_bv 16 d) dotdot_name]
             ++ replicate 62 dirent_zero)))
      a
      (fs_splice (P a) (16 * (k mod 64)) 16
         (fun j => dirent_bytes (de_of_name (Z_to_bv 16 i) name) !!! j)).

  Lemma eff_create_dir_entry_wf (d : Z) (k : nat) (name : fname)
      (i fb : Z) :
    0 < d < sb_ninodes sb -> d < 65536 ->
    bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
    fs_reachable P sb d ->
    bv_unsigned (di_nlink (fs_dinode P sb d)) < 32767 ->
    0 < i < sb_ninodes sb -> i < 65536 ->
    bv_unsigned (di_type (fs_dinode P sb i)) = 0 ->
    fs_data_start sb <= fb < sb_size sb -> fb ∉ u ->
    (length name <= 14)%nat -> nonul name ->
    dir_first (fs_file_data P sb d)
      (dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))) name = None ->
    ((k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat
       /\ ~ dir_live (fs_file_data P sb d) k
     \/ k = dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))
       /\ 16 * (Z.of_nat k + 1)
          <= fs_nblk (bv_unsigned (di_size (fs_dinode P sb d))) * BSIZE_z) ->
    fs_durable_wf_view (eff_create_dir_entry d k name i fb).
  Proof.
    intros Hd Hd16 Hdty Hdre Hnlcap Hi Hi16 Hifree Hfbr Hfbu Hlen Hnn
      Hnone Harm.
    assert (Hm32 : bv_modulus 32 = 4294967296) by reflexivity.
    destruct (fs_sb_ok_meta sb Hok) as (Hm1 & Hm2 & Hm3).
    pose proof (sbo_one_bitmap sb Hok) as Hone.
    set (dn := fs_dinode P sb d) in *.
    set (dni := fs_dinode P sb i) in *.
    unfold fs_file_data in Hnone, Harm. fold dn in Hnone, Harm.
    set (szd := bv_unsigned (di_size dn)) in *.
    set (nrec := dir_nrec szd) in *.
    set (data := fs_data_of P dn) in *.
    set (szd' := Z.max szd (16 * (Z.of_nat k + 1))).
    set (dnd' := di_nlink_inc (di_set_size dn (Z_to_bv 32 szd'))).
    set (dnc := di_create_dir fb).
    set (w := Z_to_bv 16 i).
    set (P' := eff_create_dir_entry d k name i fb).
    assert (Hfb0 : 0 < fb)
      by (unfold fs_data_start in Hfbr, Hm2; lia).
    assert (Hfb32 : fb < 4294967296)
      by (unfold BSIZE_z in Hone; lia).
    assert (Hdlive : bv_unsigned (di_type dn) <> 0)
      by (rewrite Hdty; unfold T_DIR_z; discriminate).
    assert (Htyc : bv_unsigned (di_type dnc) = T_DIR_z) by reflexivity.
    assert (Hilive' : bv_unsigned (di_type dnc) <> 0)
      by (rewrite Htyc; unfold T_DIR_z; discriminate).
    assert (Hszc : bv_unsigned (di_size dnc) = 32) by reflexivity.
    assert (Hnlc : bv_unsigned (di_nlink dnc) = 1) by reflexivity.
    assert (Hdi_ne : d <> i).
    { intros Hc.
      assert (Hc2 : bv_unsigned (di_type dn) = 0).
      { unfold dn. rewrite Hc. exact Hifree. }
      rewrite Hdty in Hc2. unfold T_DIR_z in Hc2. lia. }
    assert (Hd_rd : d ∈ rd)
      by (apply (Hrd d); split; [lia | split; [exact Hdty | exact Hdre]]).
    pose proof (Hdok d ltac:(exact Hd_rd)) as Hddok. fold dn in Hddok.
    pose proof (dok_at d ltac:(lia) Hdlive) as Hdok_d. fold dn in Hdok_d.
    pose proof (fdi_size _ _ _ Hdok_d) as Hcapd. fold dn in Hcapd.
    pose proof (proj1 (bv_unsigned_in_range _ (di_size dn))) as Hsz0.
    destruct (dots_flat d ltac:(lia) Hdty) as
      (Hnrec2 & Hlv0 & Hin0 & Hbn0 & Hlv1 & Hbn1).
    fold dn data in Hnrec2, Hlv0, Hin0, Hbn0, Hlv1, Hbn1.
    fold szd nrec in Hnrec2.
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
    { unfold dnd'. cbn [di_size di_set_size di_nlink_inc di_set_nlink].
      apply Z_to_bv_small.
      unfold FS_MAXFILE, BSIZE_z in Hszd'cap. lia. }
    assert (Htyd' : di_type dnd' = di_type dn) by reflexivity.
    assert (Haddrd' : di_addrs dnd' = di_addrs dn) by reflexivity.
    assert (Hnlkd'u : bv_unsigned (di_nlink dnd')
                      = bv_unsigned (di_nlink dn) + 1).
    { unfold dnd'. cbn [di_nlink di_nlink_inc di_set_nlink di_set_size].
      apply Z_to_bv_small.
      assert (Hm16 : bv_modulus 16 = 65536) by reflexivity.
      pose proof (proj1 (bv_unsigned_in_range _ (di_nlink dn))). lia. }
    assert (Hwfd' : dinode_wf dnd')
      by (apply di_set_nlink_wf, di_set_size_wf, fs_dinode_wf).
    assert (Hwfc : dinode_wf dnc) by (apply di_create_dir_wf).
    assert (Hwu : bv_unsigned w = i).
    { unfold w. apply Z_to_bv_small.
      assert (Hm16 : bv_modulus 16 = 65536) by reflexivity. lia. }
    assert (Hwnz : w <> bv_0 16).
    { intros Hc.
      assert (Hc' : bv_unsigned w = 0) by (rewrite Hc; reflexivity).
      lia. }
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
      by (apply (blk_addr_covered d (k / 64)%nat ltac:(lia) Hdlive HkbM
                   Hkbnb)).
    assert (Ha0 : fs_blk_addr P dn (k / 64) <> 0)
      by (unfold fs_data_start in *; lia).
    assert (Ha_in : fs_blk_addr P dn (k / 64) ∈ fs_inode_ents P dn).
    { rewrite <- (fs_slot_blk dn (k / 64)%nat HkbM).
      apply (fs_inode_ents_slot P dn); [lia |].
      rewrite (fs_slot_blk dn (k / 64)%nat HkbM). exact Ha0. }
    assert (Hafb : fs_blk_addr P dn (k / 64) <> fb).
    { intros Hc. apply Hfbu.
      rewrite <- Hc.
      exact (used_elem d _ ltac:(lia) Hdlive Ha_in). }
    pose proof Hnin_le as HninN.
    assert (HdN : 0 <= d < 16 * (sb_ninodes sb / 16 + 1)) by lia.
    assert (HiN : 0 <= i < 16 * (sb_ninodes sb / 16 + 1)) by lia.
    destruct (iblock_bounds sb Hok d HdN) as (Hibd1 & Hibd2 & Hibd3).
    destruct (iblock_bounds sb Hok i HiN) as (Hibi1 & Hibi2 & Hibi3).
    assert (HaE : forall b : Z,
              b <> fs_blk_addr P dn (k / 64) ->
              b <> fb ->
              b <> sb_bmapstart sb ->
              b <> IBLOCK (fs_inum_bv d) (sb_inodestart sb) ->
              b <> IBLOCK (fs_inum_bv i) (sb_inodestart sb) ->
              P' b = P b).
    { intros b Hb1 Hb2 Hb3 Hb4 Hb5. unfold P', eff_create_dir_entry.
      cbv zeta. fold dn.
      rewrite fs_upd_ne by exact Hb1.
      rewrite fs_upd_ne by exact Hb2.
      rewrite fs_upd_ne by exact Hb3.
      rewrite (eff_dinode_out sb) by exact Hb5.
      exact (eff_dinode_out sb _ _ _ _ Hb4). }
    assert (HsbU : P' SB_BNO = P SB_BNO).
    { apply HaE; unfold SB_BNO, fs_data_start in *; lia. }
    assert (HbmB : P' (sb_bmapstart sb)
                   = bm_bytes BSIZE
                       (fs_bmap_set BSIZE (P (sb_bmapstart sb)) ∪ {[fb]})).
    { unfold P', eff_create_dir_entry. cbv zeta. fold dn.
      rewrite fs_upd_ne by (unfold fs_data_start in *; lia).
      rewrite fs_upd_ne by (unfold fs_data_start in *; lia).
      apply fs_upd_at. }
    assert (HfbB : P' fb
                   = dirblk_bytes
                       ([de_of_name (Z_to_bv 16 i) dot_name;
                         de_of_name (Z_to_bv 16 d) dotdot_name]
                        ++ replicate 62 dirent_zero)).
    { unfold P', eff_create_dir_entry. cbv zeta. fold dn.
      rewrite fs_upd_ne by (intros Hc; exact (Hafb (eq_sym Hc))).
      apply fs_upd_at. }
    assert (HaB : P' (fs_blk_addr P dn (k / 64))
                  = fs_splice (P (fs_blk_addr P dn (k / 64)))
                      (16 * (k mod 64)) 16
                      (fun j => dirent_bytes (de_of_name w name) !!! j)).
    { unfold P', eff_create_dir_entry. cbv zeta. fold dn. apply fs_upd_at. }
    assert (Hdec : forall z : Z, 0 <= z < 16 * (sb_ninodes sb / 16 + 1) ->
              fs_dinode P' sb z
              = if decide (z = i) then dnc
                else if decide (z = d) then dnd' else fs_dinode P sb z).
    { intros z Hz.
      destruct (iblock_bounds sb Hok z Hz) as (Hz1 & Hz2 & Hz3).
      transitivity (fs_dinode
                      (eff_dinode
                         (eff_dinode P sb d dnd') sb i dnc) sb z).
      - apply fs_dinode_ext. unfold P', eff_create_dir_entry. cbv zeta.
        fold dn. fold dnd'. fold dnc.
        rewrite fs_upd_ne by (unfold fs_data_start in Ha_rng; lia).
        rewrite fs_upd_ne by (unfold fs_data_start in Hfbr; lia).
        rewrite fs_upd_ne by lia.
        reflexivity.
      - rewrite (eff_dinode_dec sb Hok _ i dnc z Hwfc HiN Hz).
        destruct (decide (z = i)) as [-> | Hzi]; [reflexivity |].
        exact (eff_dinode_dec sb Hok P d dnd' z Hwfd' HdN Hz). }
    assert (Hslotinj : fs_slot_inj P dn)
      by (apply (slot_inj_at d ltac:(lia) Hdlive)).
    assert (Hother : forall k' : nat, k' <> (k / 64)%nat ->
              fs_blk_addr P dn k' <> 0 ->
              P' (fs_blk_addr P dn k') = P (fs_blk_addr P dn k')).
    { intros k' Hne Hnz.
      destruct (Nat.lt_ge_cases k' FS_MAXFILE) as [Hk' | Hk'].
      - assert (Hrng : fs_data_start sb <= fs_blk_addr P dn k' < sb_size sb).
        { (* the ENTRY clauses: a nonzero address is a data block,
             whatever the size says (durable-disk F3.1) *)
          exact (fs_blk_addr_range P sb dn k' Hdok_d Hk' Hnz). }
        assert (Hinb : fs_blk_addr P dn k' ∈ fs_inode_ents P dn).
        { rewrite <- (fs_slot_blk dn k' Hk').
          apply (fs_inode_ents_slot P dn); [lia |].
          rewrite (fs_slot_blk dn k' Hk'). exact Hnz. }
        apply HaE; [| | unfold fs_data_start in *; blk_ne Hibd3 Hibi3
                    | unfold fs_data_start in *; blk_ne Hibd3 Hibi3
                    | unfold fs_data_start in *; blk_ne Hibd3 Hibi3].
        + intros Hc.
          apply Hne.
          apply (Hslotinj k' (k / 64)%nat ltac:(lia) ltac:(lia)).
          * rewrite (fs_slot_blk dn k' Hk'). exact Hnz.
          * rewrite (fs_slot_blk dn k' Hk'),
              (fs_slot_blk dn (k / 64)%nat HkbM).
            exact Hc.
        + intros Hc. apply Hfbu. rewrite <- Hc.
          exact (used_elem d _ ltac:(lia) Hdlive Hinb).
      - rewrite (fs_blk_addr_high P dn k' Hk'). exact HsbU. }
    assert (HindD : fs_ind_ents P' dnd' = fs_ind_ents P dn).
    { transitivity (fs_ind_ents P' dn);
        [exact (fs_ind_ents_meta P' dn dnd' Haddrd') |].
      apply fs_ind_ents_ext. intros Hnz12.
      assert (Hin' : bv_unsigned (di_addrs dn !!! 12%nat)
                     ∈ fs_inode_ents P dn).
      { rewrite <- (fs_slot_max P dn).
        apply (fs_inode_ents_slot P dn); [lia |].
        rewrite fs_slot_max. exact Hnz12. }
      pose proof (blocks_range d _ ltac:(lia) Hdlive Hin') as Hbr.
      apply HaE; [| | unfold fs_data_start in *; blk_ne Hibd3 Hibi3
                  | unfold fs_data_start in *; blk_ne Hibd3 Hibi3
                  | unfold fs_data_start in *; blk_ne Hibd3 Hibi3].
      - intros Hc.
        assert (Hfe : fs_slot P dn FS_MAXFILE = fs_slot P dn (k / 64)).
        { rewrite fs_slot_max, (fs_slot_blk dn (k / 64)%nat HkbM). exact Hc. }
        assert (Hnz' : fs_slot P dn FS_MAXFILE <> 0)
          by (rewrite fs_slot_max; exact Hnz12).
        pose proof (Hslotinj FS_MAXFILE (k / 64)%nat ltac:(lia) ltac:(lia)
                      Hnz' Hfe) as Hcc.
        lia.
      - intros Hc. apply Hfbu. rewrite <- Hc.
        exact (used_elem d _ ltac:(lia) Hdlive Hin'). }
    assert (Hunt : forall z : Z, 0 <= z < sb_ninodes sb ->
              z <> d -> z <> i ->
              bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
              fs_ind_ents P' (fs_dinode P sb z)
              = fs_ind_ents P (fs_dinode P sb z)
              /\ (forall k0 : nat,
                    fs_data_of P' (fs_dinode P sb z) k0
                    = fs_data_of P (fs_dinode P sb z) k0)
              /\ fs_inode_ents P' (fs_dinode P sb z)
                 = fs_inode_ents P (fs_dinode P sb z)
              /\ fs_inode_dwf P' sb (fs_dinode P sb z)
                 = fs_inode_dwf P sb (fs_dinode P sb z)).
    { intros z Hz Hnd' Hni' Hnz. apply inode_untouched; try assumption.
      intros b Hb. apply HaE.
      - intros ->.
        exact (blocks_cross z d _ Hz ltac:(lia) Hnd' Hnz Hdlive Hb Ha_in).
      - intros ->. apply Hfbu. exact (used_elem z _ Hz Hnz Hb).
      - pose proof (blocks_range z b Hz Hnz Hb) as Hbr.
        unfold fs_data_start in Hbr. clear -Hbr Hibd3 Hibi3. lia.
      - pose proof (blocks_range z b Hz Hnz Hb) as Hbr.
        unfold fs_data_start in Hbr. clear -Hbr Hibd3 Hibi3. lia.
      - pose proof (blocks_range z b Hz Hnz Hb) as Hbr.
        unfold fs_data_start in Hbr. clear -Hbr Hibd3 Hibi3. lia. }
    (* --- the child's readers ------------------------------------------- *)
    assert (Haddrc12 : forall j : nat, (1 <= j < 13)%nat ->
              di_addrs dnc !!! j = bv_0 32).
    { intros j Hj. unfold dnc, di_create_dir. cbn [di_addrs].
      rewrite list_lookup_total_insert_ne by lia.
      apply lookup_total_replicate_2. lia. }
    assert (Haddrc0 : bv_unsigned (di_addrs dnc !!! 0%nat) = fb).
    { unfold dnc, di_create_dir. cbn [di_addrs].
      rewrite list_lookup_total_insert
        by (rewrite length_replicate; lia).
      apply Z_to_bv_small. lia. }
    assert (Hindc : fs_ind_ents P' dnc = replicate FS_NINDIRECT 0).
    { unfold fs_ind_ents.
      rewrite (Haddrc12 12%nat ltac:(lia)).
      change (bv_unsigned (bv_0 32)) with 0.
      reflexivity. }
    assert (Hblkaddrc0 : fs_blk_addr P' dnc 0 = fb).
    { unfold fs_blk_addr. cbn [Nat.ltb Nat.leb]. exact Haddrc0. }
    assert (Hblkc : fs_inode_ents P' dnc = [fb]).
    { (* ialloc+mkdir's record names ONE block: [addrs[0]] *)
      rewrite fs_inode_ents_alt.
      rewrite (Haddrc12 12%nat ltac:(lia)).
      change (bv_unsigned (bv_0 32)) with 0. cbn [Z.eqb app].
      rewrite Hindc.
      rewrite (filter_all_false (fun a : Z => negb (a =? 0))
                 (replicate FS_NINDIRECT 0)).
      2:{ intros x Hx. apply elem_of_replicate in Hx as [-> _]. reflexivity. }
      rewrite List.app_nil_r.
      rewrite (filter_nz_prefix
                 (fun k => bv_unsigned (di_addrs dnc !!! k)) FS_NDIRECT 1%nat).
      - cbn [seq fmap list_fmap]. rewrite Haddrc0. reflexivity.
      - unfold FS_NDIRECT. lia.
      - intros q Hq. replace q with 0%nat by lia.
        rewrite Haddrc0. lia.
      - intros q Hlo Hhi.
        rewrite (Haddrc12 q ltac:(unfold FS_NDIRECT in *; lia)).
        reflexivity. }
    destruct (child_facts P' i d fb ltac:(lia) Hi16 ltac:(lia) Hd16
                Hfb0 Hfb32 HfbB) as (Hci0 & Hcb0 & Hci1 & Hcb1).
    fold dnc in Hci0, Hcb0, Hci1, Hcb1.
    set (datac := fs_data_of P' dnc) in *.
    assert (Hclv0 : dir_live datac 0).
    { unfold dir_live. rewrite Hci0.
      intros Hc.
      assert (Hc' : bv_unsigned (Z_to_bv 16 i) = 0)
        by (rewrite Hc; reflexivity).
      fold w in Hc'. lia. }
    assert (Hclv1 : dir_live datac 1).
    { unfold dir_live. rewrite Hci1.
      intros Hc.
      assert (Hc' : bv_unsigned (Z_to_bv 16 d) = 0)
        by (rewrite Hc; reflexivity).
      assert (Hdu : bv_unsigned (Z_to_bv 16 d) = d).
      { apply Z_to_bv_small.
        assert (Hm16 : bv_modulus 16 = 65536) by reflexivity. lia. }
      lia. }
    assert (Hdu : bv_unsigned (Z_to_bv 16 d) = d).
    { apply Z_to_bv_small.
      assert (Hm16 : bv_modulus 16 = 65536) by reflexivity. lia. }
    assert (Hnrecc : dir_nrec (bv_unsigned (di_size dnc)) = 2%nat)
      by (rewrite Hszc; reflexivity).
    (* the child's view: DOT -> i, DOTDOT -> d, nothing else *)
    assert (Hcdot : dir_view datac 2 !! DOT = Some i).
    { rewrite dir_view_lookup.
      assert (Hf : dir_first datac 2 DOT = Some 0%nat).
      { apply dfirst_Some_2; [lia | |].
        - apply dir_matchb_true. split; [exact Hclv0 |].
          replace (bname 14 (dir_name datac 0)) with (dir_bname datac 0)
            by reflexivity.
          rewrite Hcb0. reflexivity.
        - intros j Hj. lia. }
      rewrite Hf. cbn [fmap option_fmap option_map].
      rewrite Hci0. fold w. rewrite Hwu. reflexivity. }
    assert (Hcdd : dir_view datac 2 !! DOTDOT = Some d).
    { rewrite dir_view_lookup.
      assert (Hf : dir_first datac 2 DOTDOT = Some 1%nat).
      { apply dfirst_Some_2; [lia | |].
        - apply dir_matchb_true. split; [exact Hclv1 |].
          replace (bname 14 (dir_name datac 1)) with (dir_bname datac 1)
            by reflexivity.
          rewrite Hcb1. reflexivity.
        - intros j Hj.
          replace j with 0%nat by lia.
          apply dir_matchb_false. intros [_ Hnm].
          replace (bname 14 (dir_name datac 0)) with (dir_bname datac 0)
            in Hnm by reflexivity.
          rewrite Hcb0 in Hnm. exact (dot_ne_dotdot Hnm). }
      rewrite Hf. cbn [fmap option_fmap option_map].
      rewrite Hci1. rewrite Hdu. reflexivity. }
    assert (Hcout : forall (f : fname) (w0 : Z),
              dir_view datac 2 !! f = Some w0 -> w0 = i \/ w0 = d).
    { intros f w0 Hv.
      apply dir_view_lookup_rec in Hv.
      destruct Hv as (k1 & Hk1 & _ & _ & Hin1).
      destruct k1 as [| [| k1']]; [| | lia].
      - left. rewrite <- Hin1. rewrite Hci0. fold w. exact Hwu.
      - right. rewrite <- Hin1. rewrite Hci1. exact Hdu. }
    (* the child's boolean sweeps *)
    assert (Hdwfc : fs_inode_dwf P' sb dnc = true).
    { unfold fs_inode_dwf. cbv zeta.
      rewrite Hindc, Hszc.
      change (fs_nblk 32) with 1.
      apply andb_true_iff. split; [| apply forallb_seq_intro].
      2:{ intros x Hx.
          cbv beta zeta.
          rewrite lookup_total_replicate_2 by lia.
          destruct (Z.ltb_spec (Z.of_nat x) (1 - Z.of_nat FS_NDIRECT))
            as [Hlt | Hge];
            [unfold FS_NDIRECT in Hlt; lia | reflexivity]. }
      apply andb_true_iff. split.
      2:{ change (1 <=? Z.of_nat FS_NDIRECT) with true. cbn [andb].
          rewrite (Haddrc12 12%nat ltac:(lia)). reflexivity. }
      apply andb_true_iff. split; [| apply forallb_seq_intro].
      2:{ intros x Hx.
          cbv beta zeta.
          destruct x as [| x'].
          - change (Z.of_nat 0 <? 1) with true.
            unfold fs_addr_ok.
            apply andb_true_iff. rewrite Haddrc0.
            split; [apply Z.leb_le; lia | apply Z.ltb_lt; lia].
          - destruct (Z.ltb_spec (Z.of_nat (S x')) 1) as [Hlt | Hge];
              [lia |].
            rewrite (Haddrc12 (S x')
                       ltac:(unfold FS_NDIRECT in Hx; lia)).
            reflexivity. }
      apply andb_true_iff. split.
      - rewrite Htyc. reflexivity.
      - reflexivity. }
    (* the parent's sweeps, as in the link effect *)
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
    assert (Hdwfd : fs_inode_dwf P' sb dnd' = true).
    { pose proof (dwf_bool_at d ltac:(lia) Hdlive) as Hold.
      fold dn in Hold.
      unfold fs_inode_dwf in Hold |- *. cbv zeta in Hold |- *.
      rewrite HindD, Haddrd', Htyd', Hszd'u, Hnb'.
      fold szd in Hold.
      rewrite !andb_true_iff in Hold |- *.
      destruct Hold as [[[[Ho1 Ho2] Ho3] Ho4] Ho5].
      repeat split; try assumption.
      apply Z.leb_le. lia. }
    assert (Hblkd : fs_inode_ents P' dnd' = fs_inode_ents P dn).
    { (* the entry list does not read the size (durable-disk F3.1) *)
      apply fs_inode_ents_det; assumption. }
    (* --- the tree ------------------------------------------------------ *)
    assert (Htyp : forall z : Z, 0 <= z < sb_ninodes sb -> z <> i ->
              bv_unsigned (di_type (fs_dinode P' sb z))
              = bv_unsigned (di_type (fs_dinode P sb z))).
    { intros z Hz Hzi. rewrite (Hdec z ltac:(irng)).
      rewrite decide_False by exact Hzi.
      destruct (decide (z = d)) as [-> | Hzd];
        [rewrite Htyd'; reflexivity | reflexivity]. }
    assert (Hentd : forall f : fname,
              tree_ent (tree_of_disk P' sb) d f
              = <[name := i]> (dir_view data nrec) !! f).
    { intros f.
      rewrite (tree_ent_dir_eq P' d ltac:(lia))
        by (rewrite (Htyp d ltac:(lia)
                       ltac:(intros Hc; exact (Hdi_ne Hc)));
            exact Hdty).
      unfold fs_file_data.
      rewrite (Hdec d ltac:(irng)).
      rewrite decide_False by (intros Hc; exact (Hdi_ne Hc)).
      rewrite decide_True by reflexivity.
      rewrite Hszd'u. fold nrec'. rewrite Hview. reflexivity. }
    assert (Henti : forall f : fname,
              tree_ent (tree_of_disk P' sb) i f
              = dir_view datac 2 !! f).
    { intros f.
      rewrite (tree_ent_dir_eq P' i ltac:(lia)).
      2:{ rewrite (Hdec i HiN), decide_True by reflexivity. exact Htyc. }
      unfold fs_file_data.
      rewrite (Hdec i HiN), decide_True by reflexivity.
      rewrite Hnrecc. reflexivity. }
    assert (Hentt : forall f : fname,
              tree_ent t d f = dir_view data nrec !! f).
    { intros f. unfold t.
      rewrite (tree_ent_dir_eq P d ltac:(lia) Hdty).
      unfold fs_file_data. fold dn. fold szd nrec data. reflexivity. }
    assert (Hentother : forall (j : Z) (f : fname), j <> d -> j <> i ->
              tree_ent (tree_of_disk P' sb) j f = tree_ent t j f).
    { intros j f Hjd Hji.
      apply tree_ent_untouched. intros Hjr.
      apply node_at_untouched; [exact Hjr | |].
      - rewrite (Hdec j ltac:(irng)).
        rewrite decide_False by exact Hji.
        rewrite decide_False by exact Hjd. reflexivity.
      - intros Hjl k0 Hk0.
        destruct (Hunt j Hjr Hjd Hji Hjl) as (_ & Hdata & _ & _).
        exact (Hdata k0). }
    assert (Hentti : forall f : fname, tree_ent t i f = None).
    { intros f. unfold t. apply (tree_ent_nondir P i f).
      unfold dni in Hifree. rewrite Hifree. unfold T_DIR_z. lia. }
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
      - destruct (decide (j = i)) as [-> | Hji].
        + rewrite Hentti in He. discriminate.
        + rewrite (Hentother j f Hjd Hji). exact He. }
    assert (Hire' : fs_reachable P' sb i).
    { unfold fs_reachable.
      apply (rch_snoc (tree_of_disk P' sb) ROOTINO d name);
        [exact (Hfwd d Hdre) |].
      rewrite Hentd. apply lookup_insert. }
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
        + left. rewrite <- (Hentother j f Hjd Hji). exact He.
      - intros f w0 He.
        rewrite Henti in He. exact (Hcout f w0 He). }
    (* --- the supply gains the dirent's ticket and the child's ".." ----- *)
    set (rd' := rd ∪ ({[i]} : gset Z)).
    assert (Hird : i ∉ rd).
    { intros Hc. destruct (proj1 (Hrd i) Hc) as (_ & Hc2 & _).
      unfold dni in Hifree. rewrite Hifree in Hc2.
      unfold T_DIR_z in Hc2. lia. }
    assert (Hi_rd' : i ∈ rd')
      by (apply elem_of_union; right; apply elem_of_singleton; reflexivity).
    assert (Hd_rd' : d ∈ rd')
      by (apply elem_of_union; left; exact Hd_rd).
    assert (Hrd'mem : forall z : Z, z <> i -> (z ∈ rd' <-> z ∈ rd)).
    { intros z Hzi. unfold rd'.
      rewrite elem_of_union, elem_of_singleton. tauto. }
    assert (Hsegc : forall z : Z,
              Z.of_nat (fs_tick_count (fs_dir_tickets P' i dnc) z)
              = Z.of_nat (otick (Some d) z)).
    { intros z. unfold fs_dir_tickets.
      rewrite Hnrecc.
      set (f0 := fs_rec_ticket P' i dnc).
      assert (Hf00 : f0 0%nat = None).
      { unfold f0, fs_rec_ticket. cbv zeta. fold datac.
        rewrite (proj2 (dir_liveb_true _ _) Hclv0). cbn [andb].
        rewrite Hci0.
        rewrite bool_decide_eq_true_2 by (exact Hwu).
        reflexivity. }
      assert (Hf01 : f0 1%nat = Some d).
      { unfold f0, fs_rec_ticket. cbv zeta. fold datac.
        rewrite (proj2 (dir_liveb_true _ _) Hclv1). cbn [andb].
        rewrite Hci1.
        rewrite bool_decide_eq_false_2
          by (rewrite Hdu; intros Hc; exact (Hdi_ne Hc)).
        cbn [negb]. rewrite Hdu. reflexivity. }
      change 2%nat with (S (S 0)).
      rewrite (tick_omap_snoc f0 1%nat z).
      rewrite (tick_omap_snoc f0 0%nat z).
      rewrite Hf00, Hf01. cbn [otick].
      unfold fs_tick_count. cbn [omap list_omap seq List.filter length].
      lia. }
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
              Z.of_nat (fs_rtick P' sb rd' z)
              = Z.of_nat (fs_rtick P sb rd z)
                + Z.of_nat (otick (Some i) z) + Z.of_nat (otick (Some d) z)).
    { intros z. unfold fs_rtick, fs_rtickets.
      rewrite (tick_mjoin_upd2
                 (fun x : nat =>
                    if bool_decide (Z.of_nat x ∈ rd)
                    then fs_dir_tickets_at P sb (Z.of_nat x) else [])
                 (fun x : nat =>
                    if bool_decide (Z.of_nat x ∈ rd')
                    then fs_dir_tickets_at P' sb (Z.of_nat x) else [])
                 (Z.to_nat (sb_ninodes sb)) (Z.to_nat d) (Z.to_nat i) z
                 ltac:(clear -Hd; lia) ltac:(clear -Hi; lia)
                 ltac:(clear -Hd Hi Hdi_ne; lia)).
      - rewrite Z2Nat.id by lia.
        rewrite bool_decide_eq_true_2 by exact Hd_rd'.
        rewrite bool_decide_eq_true_2 by exact Hd_rd.
        unfold fs_dir_tickets_at. cbv zeta.
        rewrite (Hdec d ltac:(irng)).
        rewrite decide_False by (intros Hc; exact (Hdi_ne Hc)).
        rewrite decide_True by reflexivity.
        rewrite Htyd'. fold dn.
        rewrite (proj2 (Z.eqb_eq _ _) Hdty).
        rewrite (Hsegd z). fold dn.
        rewrite Z2Nat.id by lia.
        rewrite bool_decide_eq_true_2 by exact Hi_rd'.
        rewrite (bool_decide_eq_false_2 (i ∈ rd) Hird).
        unfold fs_dir_tickets_at. cbv zeta.
        rewrite (Hdec i HiN), decide_True by reflexivity.
        rewrite (proj2 (Z.eqb_eq _ _) Htyc).
        rewrite fs_tick_count_nil.
        rewrite (Hsegc z). lia.
      - intros x Hx Hxd Hxi. cbv beta.
        assert (Hxdz : Z.of_nat x <> d)
          by (intros Hc; apply Hxd; clear -Hc; lia).
        assert (Hxiz : Z.of_nat x <> i)
          by (intros Hc; apply Hxi; clear -Hc; lia).
        rewrite (bool_decide_ext (Z.of_nat x ∈ rd') (Z.of_nat x ∈ rd)
                   (Hrd'mem (Z.of_nat x) Hxiz)).
        destruct (bool_decide (Z.of_nat x ∈ rd)) eqn:Hg; [| reflexivity].
        apply bool_decide_eq_true_1 in Hg.
        destruct (proj1 (Hrd _) Hg) as (Hxr & Hxty & _).
        assert (Hxl : bv_unsigned (di_type (fs_dinode P sb (Z.of_nat x)))
                      <> 0)
          by (rewrite Hxty; unfold T_DIR_z; discriminate).
        apply tickets_at_untouched; [exact Hxr | |].
        + rewrite (Hdec (Z.of_nat x) (iblk_ix_range sb x Hx)).
          rewrite decide_False by exact Hxiz.
          rewrite decide_False by exact Hxdz. reflexivity.
        + intros _ k0 Hk0.
          destruct (Hunt _ Hxr Hxdz Hxiz Hxl) as (_ & Hdata & _ & _).
          exact (Hdata k0). }
    assert (Hcnt0 : fs_rtick P sb rd i = 0%nat)
      by (exact (rtick_free i ltac:(lia) ltac:(exact Hifree))).
    assert (Hiroot : i <> ROOTINO).
    { intros Hc.
      pose proof (fs_root_wf_type P sb HW7) as Hr.
      rewrite <- Hc in Hr. unfold dni in Hifree. rewrite Hifree in Hr.
      unfold T_DIR_z in Hr. lia. }
    (* --- the used set and the bitmap ----------------------------------- *)
    destruct (used_add P' i [fb] ltac:(lia)) as (u'' & Hu'' & Hu''mem).
    { fold dni. rewrite (proj2 (Z.eqb_eq _ _) ltac:(exact Hifree)).
      reflexivity. }
    { rewrite (Hdec i HiN), decide_True by reflexivity.
      rewrite (proj2 (Z.eqb_neq _ _) Hilive').
      exact Hblkc. }
    { apply NoDup_cons_2; [| apply NoDup_nil_2].
      intros Hc. exact (proj1 (elem_of_nil fb) Hc). }
    { intros b Hb. apply elem_of_cons in Hb as [-> | Hb];
        [exact Hfbu | exfalso; exact (proj1 (elem_of_nil b) Hb)]. }
    { intros z Hz Hne.
      rewrite (Hdec z ltac:(irng)), decide_False by exact Hne.
      destruct (decide (z = d)) as [-> | Hzd].
      { fold dn. rewrite Htyd'.
        destruct (bv_unsigned (di_type dn) =? 0); [reflexivity |].
        exact Hblkd. }
      destruct (bv_unsigned (di_type (fs_dinode P sb z)) =? 0) eqn:Ez;
        [reflexivity |].
      destruct (Hunt z Hz Hzd Hne (proj1 (Z.eqb_neq _ _) Ez))
        as (_ & _ & Hbl & _).
      exact Hbl. }
    (* --- assemble ------------------------------------------------------ *)
    exists sb. split.
    { rewrite (fs_parse_sb_ext P P' HsbU). exact Hp. }
    constructor.
    - exact Hsb.
    - apply fs_inodes_dwf_intro. intros z Hz Hnz'.
      rewrite (Hdec z ltac:(irng)) in Hnz' |- *.
      destruct (decide (z = i)) as [-> | Hzi]; [exact Hdwfc |].
      destruct (decide (z = d)) as [-> | Hzd]; [exact Hdwfd |].
      destruct (Hunt z Hz Hzd Hzi Hnz') as (_ & _ & _ & Hdwf).
      rewrite Hdwf. exact (dwf_bool_at z Hz Hnz').
    - exists u''. split; [exact Hu'' |].
      apply (bitmap_wf_of_set P' u''
               (fs_bmap_set BSIZE (P (sb_bmapstart sb)) ∪ {[fb]}));
        [exact HbmB |].
      intros b Hb.
      rewrite elem_of_union, elem_of_singleton.
      rewrite (old_bit_iff b Hb), (Hu''mem b).
      rewrite elem_of_list_singleton.
      unfold fs_data_start in Hfbr. unfold fs_data_start.
      tauto.
    - (* the root *)
      destruct (decide (d = ROOTINO)) as [-> | Hdroot].
      + apply root_wf_intro.
        * rewrite (Htyp ROOTINO ltac:(lia)
                     ltac:(intros Hc; exact (Hdi_ne Hc))).
          exact Hdty.
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
        apply root_wf_untouched.
        * rewrite (Hdec ROOTINO (iblk_root_range sb Hnin1)).
          rewrite decide_False by (intros Hc; exact (Hiroot (eq_sym Hc))).
          rewrite decide_False by (intros Hc; exact (Hdroot (eq_sym Hc))).
          reflexivity.
        * intros k0 Hk0.
          destruct (Hunt ROOTINO
                      ltac:(pose proof Hnin1; unfold ROOTINO; lia)
                      ltac:(intros Hc; exact (Hdroot (eq_sym Hc)))
                      ltac:(intros Hc; exact (Hiroot (eq_sym Hc))) Hrl)
            as (_ & Hdata & _ & _).
          exact (Hdata k0).
    - (* the dots *)
      apply fs_dots_all_intro. intros z Hz Hdty'.
      rewrite (Hdec z ltac:(irng)) in Hdty' |- *.
      destruct (decide (z = i)) as [-> | Hzi].
      + (* the child's dots, by construction *)
        unfold fs_dots_wf. cbv zeta.
        rewrite Hnrecc.
        apply andb_true_iff. split.
        2:{ apply bool_decide_eq_true_2. fold datac. exact Hcb1. }
        apply andb_true_iff. split.
        2:{ fold datac. exact (proj2 (dir_liveb_true _ _) Hclv1). }
        apply andb_true_iff. split.
        2:{ apply bool_decide_eq_true_2. fold datac. exact Hcb0. }
        apply andb_true_iff. split.
        2:{ apply Z.eqb_eq. fold datac. rewrite Hci0. exact Hwu. }
        apply andb_true_iff. split.
        2:{ fold datac. exact (proj2 (dir_liveb_true _ _) Hclv0). }
        reflexivity.
      + destruct (decide (z = d)) as [-> | Hzd].
        * apply (fs_dots_wf_win P P' d dn dnd').
          -- fold szd. rewrite Hszd'u. exact Hszd'le.
          -- intros j Hj. exact (Hwagree 0%nat ltac:(lia) j Hj).
          -- intros j Hj. exact (Hwagree 1%nat ltac:(lia) j Hj).
          -- exact (dots_bool_at d ltac:(lia) Hdty).
        * assert (Hzl : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
            by (rewrite Hdty'; unfold T_DIR_z; discriminate).
          destruct (Hunt z Hz Hzd Hzi Hzl) as (_ & Hdata & _ & _).
          apply (fs_dots_wf_win P P' z (fs_dinode P sb z)
                   (fs_dinode P sb z)).
          -- lia.
          -- apply (dir_win_agree_blocks _ _ FS_MAXFILE);
               [intros k0 Hk0; exact (Hdata k0)
               | unfold FS_MAXFILE, BSIZE; lia].
          -- apply (dir_win_agree_blocks _ _ FS_MAXFILE);
               [intros k0 Hk0; exact (Hdata k0)
               | unfold FS_MAXFILE, BSIZE; lia].
          -- exact (dots_bool_at z Hz Hdty').
    - exists nib. split; [exact Hnibz |].
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
        { exfalso. exact (Hilive' Hfree). }
        destruct (decide (z = d)) as [-> | Hzd].
        { exfalso. rewrite Htyd' in Hfree. exact (Hdlive Hfree). }
        apply (fs_region_nlink_free P sb nib z
                 (fs_region_wf_nlink P sb nib Hreg)); [lia | exact Hfree].
      + intros z Hz.
        rewrite (Hdec z ltac:(irng)).
        destruct (decide (z = i)) as [-> | Hzi].
        * rewrite Hnlc. lia.
        * destruct (decide (z = d)) as [-> | Hzd].
          -- rewrite Hnlkd'u. lia.
          -- apply (fs_region_nlink_short P sb nib z
                      (fs_region_wf_nlink P sb nib Hreg)). lia.
    - exists rd'.
      split; [| split; [| split]].
      + intros z.
        destruct (decide (z = i)) as [-> | Hzi].
        { split.
          - intros _. split; [lia |]. split.
            + rewrite (Hdec i HiN), decide_True by reflexivity.
              exact Htyc.
            + exact Hire'.
          - intros _. exact Hi_rd'. }
        rewrite (Hrd'mem z Hzi). rewrite (Hrd z).
        destruct (decide (0 <= z < sb_ninodes sb)) as [Hzr | Hzr].
        * rewrite (Htyp z Hzr Hzi).
          split; intros (A & B & C); (split; [exact A |]);
            (split; [exact B |]).
          -- exact (Hfwd z C).
          -- destruct (Hbwd z C) as [Hre | Heq]; [exact Hre |].
             exfalso. exact (Hzi Heq).
        * split; intros (A & _); [lia | lia].
      + intros z Hz.
        destruct (decide (z = i)) as [-> | Hzi].
        * (* the child's bundle *)
          assert (Hdeci : fs_dinode P' sb i = dnc).
          { rewrite (Hdec i HiN), decide_True by reflexivity.
            reflexivity. }
          rewrite Hdeci.
          constructor.
          -- rewrite Hszc. exists 2. reflexivity.
          -- intros k0 Hk0 Hlive'.
             rewrite Hnrecc in Hk0.
             fold datac in Hlive' |- *.
             destruct k0 as [| [| k0']]; [| | lia].
             ++ rewrite Hci0. fold w. rewrite Hwu.
                split; [lia |].
                rewrite (Hdec i HiN), decide_True by reflexivity.
                exact Hilive'.
             ++ rewrite Hci1, Hdu.
                split; [lia |].
                rewrite (Htyp d ltac:(lia)
                           ltac:(intros Hc; exact (Hdi_ne Hc))).
                fold dn. rewrite Hdty. unfold T_DIR_z. lia.
          -- rewrite Hnrecc.
             intros j k0 Hj Hk0 Hlj Hlk Heq.
             fold datac in Hlj, Hlk, Heq.
             destruct j as [| [| j']]; [| | lia];
               destruct k0 as [| [| k0']]; try lia.
             ++ exfalso.
                rewrite Hcb0, Hcb1 in Heq.
                exact (dot_ne_dotdot Heq).
             ++ exfalso.
                rewrite Hcb0, Hcb1 in Heq.
                exact (dot_ne_dotdot (eq_sym Heq)).
          -- rewrite Hnrecc. fold datac. exact Hcdot.
          -- rewrite Hnrecc. fold datac.
             rewrite Hcdd. exact (ex_intro _ d eq_refl).
        * assert (Hzrd : z ∈ rd) by (apply (Hrd'mem z Hzi); exact Hz).
          destruct (proj1 (Hrd z) Hzrd) as (Hzr & Hzty & _).
          destruct (decide (z = d)) as [-> | Hzd].
          -- (* the parent's bundle, as in the link effect *)
             assert (Hdecd : fs_dinode P' sb d = dnd').
             { rewrite (Hdec d ltac:(irng)).
               rewrite decide_False
                 by (intros Hc; exact (Hdi_ne Hc)).
               rewrite decide_True by reflexivity. reflexivity. }
             rewrite Hdecd.
             constructor.
             ++ rewrite Hszd'u. unfold szd'.
                destruct (Z.max_spec szd (16 * (Z.of_nat k + 1)))
                  as [[_ ->] | [_ ->]].
                ** exists (Z.of_nat k + 1). lia.
                ** exists qd. exact Hqd.
             ++ intros k0 Hk0 Hlive'.
                rewrite Hszd'u in Hk0. fold nrec' in Hk0.
                destruct (decide (k0 = k)) as [-> | Hk0k].
                ** rewrite Hwz, Hwu.
                   split; [lia |].
                   rewrite (Hdec i HiN), decide_True by reflexivity.
                   exact Hilive'.
                ** destruct (dir_written_class data (fs_data_of P' dnd')
                               nrec nrec' k name w k0 Hwrit Hdead Hk0
                               Hlive' Hk0k) as (Hk0n & Hlv).
                   rewrite (dir_inum_agree _ _ k0 (Hwagree k0 Hk0k)).
                   destruct (fdo_ent _ _ _ _ Hddok k0 Hk0n Hlv)
                     as (Hran & Hty0).
                   fold data in Hran, Hty0.
                   split; [exact Hran |].
                   assert (Hti : bv_unsigned (dir_inum data k0) <> i).
                   { intros Hc. rewrite Hc in Hty0.
                     unfold dni in Hifree. exact (Hty0 Hifree). }
                   rewrite (Htyp (bv_unsigned (dir_inum data k0))
                              ltac:(lia) Hti).
                   exact Hty0.
             ++ rewrite Hszd'u. fold nrec'.
                apply (dir_names_unique_write data _ nrec nrec' k name w);
                  [| exact Hnrecle | exact Hknrec' | exact Hdead
                   | exact Hnone | exact Hwrit].
                exact (fdo_unique _ _ _ _ Hddok).
             ++ rewrite Hszd'u. fold nrec'. rewrite Hview.
                rewrite lookup_insert_ne
                  by (intros Hc; exact (Hnamedot Hc)).
                exact (fdo_dot _ _ _ _ Hddok).
             ++ rewrite Hszd'u. fold nrec'. rewrite Hview.
                rewrite lookup_insert_ne
                  by (intros Hc; exact (Hnamedd Hc)).
                exact (fdo_dotdot _ _ _ _ Hddok).
          -- assert (Hzl : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
               by (rewrite Hzty; unfold T_DIR_z; discriminate).
             destruct (Hunt z Hzr Hzd Hzi Hzl) as (_ & Hdata & _ & _).
             apply dir_ok_untouched; [exact Hzrd | | |].
             ++ rewrite (Hdec z (iblk_z_range sb z Hzr)).
                rewrite decide_False by exact Hzi.
                rewrite decide_False by exact Hzd. reflexivity.
             ++ intros k0 Hk0. exact (Hdata k0).
             ++ intros w0 Hw0 Hwl Hw0'.
                destruct (decide (w0 = i)) as [-> | Hwne].
                ** exfalso.
                   rewrite (Hdec i HiN), decide_True in Hw0'
                     by reflexivity.
                   exact (Hilive' Hw0').
                ** exfalso. apply Hwl.
                   rewrite <- (Htyp w0 Hw0 Hwne). exact Hw0'.
      + intros z Hz. cbv zeta.
        rewrite (Hdec z ltac:(irng)).
        destruct (decide (z = i)) as [-> | Hzi].
        * intros _.
          rewrite Hnlc.
          pose proof (Hcount i) as Hc. unfold otick in Hc.
          rewrite bool_decide_eq_true_2 in Hc by reflexivity.
          rewrite (bool_decide_eq_false_2 (d = i)
                     ltac:(intros Hcc; exact (Hdi_ne Hcc))) in Hc.
          rewrite Hcnt0 in Hc.
          rewrite (bool_decide_eq_true_2
                     (bv_unsigned (di_type dnc) = T_DIR_z) Htyc).
          rewrite (bool_decide_eq_false_2 (i = ROOTINO) Hiroot).
          lia.
        * destruct (decide (z = d)) as [-> | Hzd].
          -- rewrite Htyd'. intros Hnz.
             rewrite Hnlkd'u.
             pose proof (Hcount d) as Hc. unfold otick in Hc.
             rewrite (bool_decide_eq_false_2 (i = d)
                        ltac:(intros Hcc; exact (Hdi_ne (eq_sym Hcc))))
               in Hc.
             rewrite bool_decide_eq_true_2 in Hc by reflexivity.
             pose proof (Hlkg d ltac:(lia) Hnz) as Hold. cbv zeta in Hold.
             fold dn in Hold.
             destruct (bool_decide (bv_unsigned (di_type dn) = T_DIR_z));
               destruct (bool_decide (d = ROOTINO)); (clear -Hc Hold; lia).
          -- intros Hnz.
             pose proof (Hcount z) as Hc. unfold otick in Hc.
             rewrite (bool_decide_eq_false_2 (i = z)
                        ltac:(intros Hcc; exact (Hzi (eq_sym Hcc)))) in Hc.
             rewrite (bool_decide_eq_false_2 (d = z)
                        ltac:(intros Hcc; exact (Hzd (eq_sym Hcc)))) in Hc.
             pose proof (Hlkg z Hz Hnz) as Hold. cbv zeta in Hold.
             destruct (bool_decide
                         (bv_unsigned (di_type (fs_dinode P sb z))
                          = T_DIR_z));
               destruct (bool_decide (z = ROOTINO)); (clear -Hc Hold; lia).
      + intros z Hz Hty' Hnin.
        rewrite (Hdec z ltac:(irng)) in Hty' |- *.
        destruct (decide (z = i)) as [-> | Hzi].
        { exfalso. exact (Hnin Hi_rd'). }
        destruct (decide (z = d)) as [-> | Hzd].
        { exfalso. exact (Hnin Hd_rd'). }
        assert (Hznrd : z ∉ rd).
        { intros Hc. apply Hnin. apply (Hrd'mem z Hzi). exact Hc. }
        assert (Hzl : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
          by (rewrite Hty'; unfold T_DIR_z; discriminate).
        destruct (Hunt z Hz Hzd Hzi Hzl) as (_ & Hdata & _ & _).
        apply (dots_only_untouched P' (fs_dinode P sb z)).
        * exact (fdi_size _ _ _ (dok_at z Hz Hzl)).
        * intros k0 Hk0. exact (Hdata k0).
        * exact (Horph z Hz Hty' Hznrd).
  Qed.

End EffCreateEntry.

(* the [fs_durable_wf_view]-level wrappers -- the shape stage G2
   consumes: the invariant of the OLD view, the decode-level
   preconditions, the invariant of the updated view. *)

Lemma eff_create_entry_wfv (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (name : fname) (i : Z)
      (ty maj min : bv 16) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 <= d < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
  fs_reachable P sb d ->
  0 < i < sb_ninodes sb -> i < 65536 ->
  bv_unsigned (di_type (fs_dinode P sb i)) = 0 ->
  (bv_unsigned ty = T_FILE_z \/ bv_unsigned ty = T_DEVICE_z) ->
  (length name <= 14)%nat -> nonul name ->
  dir_first (fs_file_data P sb d)
    (dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))) name = None ->
  ((k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat
     /\ ~ dir_live (fs_file_data P sb d) k
   \/ k = dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))
     /\ 16 * (Z.of_nat k + 1)
        <= fs_nblk (bv_unsigned (di_size (fs_dinode P sb d))) * BSIZE_z) ->
  fs_durable_wf_view (eff_create_entry P sb d k name i ty maj min).
Proof.
  intros Hv Hp. intros.
  destruct Hv as (sb0 & Hp0 & Hsw).
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
  destruct HW45 as (u & Hu & Hbm).
  destruct Hregx as (nib & Hnibz & Hreg).
  destruct HW9 as (rd & Hrd & Hdok & Hlkg & Horph).
  apply (eff_create_entry_wf P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph); assumption.
Qed.

Lemma eff_create_dir_entry_wfv (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (name : fname)
      (i fb : Z) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 < d < sb_ninodes sb -> d < 65536 ->
  bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
  fs_reachable P sb d ->
  bv_unsigned (di_nlink (fs_dinode P sb d)) < 32767 ->
  0 < i < sb_ninodes sb -> i < 65536 ->
  bv_unsigned (di_type (fs_dinode P sb i)) = 0 ->
  fs_data_start sb <= fb < sb_size sb ->
  fs_bit (P (sb_bmapstart sb)) fb = false ->
  (length name <= 14)%nat -> nonul name ->
  dir_first (fs_file_data P sb d)
    (dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))) name = None ->
  ((k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat
     /\ ~ dir_live (fs_file_data P sb d) k
   \/ k = dir_nrec (bv_unsigned (di_size (fs_dinode P sb d)))
     /\ 16 * (Z.of_nat k + 1)
        <= fs_nblk (bv_unsigned (di_size (fs_dinode P sb d))) * BSIZE_z) ->
  fs_durable_wf_view (eff_create_dir_entry P sb d k name i fb).
Proof.
  intros Hv Hp Hd Hd16 Hdty Hdre Hnl Hi Hi16 Hifree Hfb Hbit Hlen Hnn
    Hnone Harm.
  destruct Hv as (sb0 & Hp0 & Hsw).
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
  destruct HW45 as (u & Hu & Hbm).
  destruct Hregx as (nib & Hnibz & Hreg).
  destruct HW9 as (rd & Hrd & Hdok & Hlkg & Horph).
  assert (Hfbu : fb ∉ u).
  { destruct (fs_sb_ok_meta sb (fs_sb_wf_ok sb Hsb)) as (Hg1 & Hg2 & Hg3).
    destruct (fs_bitmap_wf_free P sb u fb Hbm
                ltac:(unfold fs_data_start in *; lia) Hbit) as (_ & Hn).
    exact Hn. }
  apply (eff_create_dir_entry_wf P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph); assumption.
Qed.
