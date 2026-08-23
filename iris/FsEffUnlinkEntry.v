(* FsEffUnlinkEntry.v -- durable-disk stage F2, effect 5: unlinking a
   directory entry; the dir arm orphans exactly the dots-only child. *)
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

Section EffUnlinkEntry.
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

  (* ---- counting bounds and the target-kept reach transfer -------------- *)

  Local Lemma mjoin_seq_split_a (F : nat -> list Z) (a n m : nat) :
    (a <= m < a + n)%nat ->
    mjoin (F <$> seq a n)
    = (mjoin (F <$> seq a (m - a)) ++ F m
       ++ mjoin (F <$> seq (S m) (a + n - S m)))%list.
  Proof.
    intros Hm.
    replace n with ((m - a) + (n - (m - a)))%nat at 1 by lia.
    rewrite seq_app, fmap_app, mjoin_app.
    replace (n - (m - a))%nat with (S (a + n - S m))%nat by lia.
    replace (a + (m - a))%nat with m by lia.
    cbn [seq fmap list_fmap]. rewrite mjoin_cons. reflexivity.
  Qed.

  Local Lemma tick_mjoin_le (F : nat -> list Z) (n m : nat) (z : Z) :
    (m < n)%nat ->
    (fs_tick_count (F m) z
     <= fs_tick_count (mjoin (F <$> seq 0 n)) z)%nat.
  Proof.
    intros Hm.
    rewrite (mjoin_seq_split F n m Hm).
    rewrite !fs_tick_count_app. lia.
  Qed.

  Local Lemma tick_mjoin_two (F : nat -> list Z) (n m1 m2 : nat) (z : Z) :
    (m1 < m2 < n)%nat ->
    (fs_tick_count (F m1) z + fs_tick_count (F m2) z
     <= fs_tick_count (mjoin (F <$> seq 0 n)) z)%nat.
  Proof.
    intros Hm.
    rewrite (mjoin_seq_split F n m1 ltac:(lia)).
    rewrite !fs_tick_count_app.
    pose proof (mjoin_seq_split_a F (S m1) (n - S m1) m2 ltac:(lia)) as Hs.
    rewrite Hs, !fs_tick_count_app. lia.
  Qed.

  Local Lemma tick_omap_le (f : nat -> option Z) (n m : nat) (z : Z) :
    (m < n)%nat ->
    (otick (f m) z <= fs_tick_count (omap f (seq 0 n)) z)%nat.
  Proof.
    intros Hm.
    replace n with (m + S (n - S m))%nat by lia.
    rewrite seq_app, omap_app, fs_tick_count_app.
    replace (0 + m)%nat with m by lia.
    cbn [seq omap list_omap].
    destruct (f m) as [tk |] eqn:E.
    - change (tk :: omap f (seq (S m) (n - S m)))
        with ([tk] ++ omap f (seq (S m) (n - S m)))%list.
      rewrite fs_tick_count_app. rewrite fs_tick_count_singleton. lia.
    - cbn [otick]. lia.
  Qed.

  Local Lemma tick_omap_two (f : nat -> option Z) (n m1 m2 : nat) (z : Z) :
    (m1 < m2 < n)%nat ->
    (otick (f m1) z + otick (f m2) z
     <= fs_tick_count (omap f (seq 0 n)) z)%nat.
  Proof.
    intros Hm.
    replace n with (m1 + S (n - S m1))%nat by lia.
    rewrite seq_app, omap_app, fs_tick_count_app.
    replace (0 + m1)%nat with m1 by lia.
    cbn [seq omap list_omap].
    assert (Htail : (otick (f m2) z
                     <= fs_tick_count (omap f (seq (S m1) (n - S m1))) z)%nat).
    { replace (n - S m1)%nat
        with ((m2 - S m1) + S (n - S m2))%nat by lia.
      rewrite seq_app, omap_app, fs_tick_count_app.
      replace (S m1 + (m2 - S m1))%nat with m2 by lia.
      cbn [seq omap list_omap].
      destruct (f m2) as [tk |] eqn:E.
      - change (tk :: omap f (seq (S m2) (n - S m2)))
          with ([tk] ++ omap f (seq (S m2) (n - S m2)))%list.
        rewrite fs_tick_count_app. rewrite fs_tick_count_singleton. lia.
      - cbn [otick]. lia. }
    destruct (f m1) as [tk |] eqn:E.
    - change (tk :: omap f (seq (S m1) (n - S m1)))
        with ([tk] ++ omap f (seq (S m1) (n - S m1)))%list.
      rewrite fs_tick_count_app. rewrite fs_tick_count_singleton. lia.
    - cbn [otick]. lia.
  Qed.

  (* an edge-preserving move that only loses edges INTO a sink [i] keeps
     everything but [i] reachable *)
  Local Lemma rch_keep_target (t' : fstree) (i : Z) :
    (forall (f : fname) (w : Z), tree_ent t i f = Some w -> False) ->
    (forall (j : Z) (f : fname) (w : Z),
       rch t ROOTINO j -> w <> i -> tree_ent t j f = Some w ->
       tree_ent t' j f = Some w) ->
    forall z : Z, rch t ROOTINO z -> z <> i -> rch t' ROOTINO z.
  Proof.
    intros Hsink Hkeep z (p & Hpz) Hzi.
    assert (Hgen : forall (q : list fname) (s : Z),
              path_at t s q = Some z -> rch t ROOTINO s ->
              rch t' ROOTINO s -> s <> i -> rch t' ROOTINO z).
    { induction q as [| f q IH]; intros s Hq Hs Hs' Hsi.
      - rewrite path_at_nil in Hq. injection Hq as <-. exact Hs'.
      - rewrite path_at_cons in Hq.
        destruct (tree_ent t s f) as [j |] eqn:He; [| discriminate].
        destruct (decide (j = i)) as [-> | Hji].
        + destruct q as [| g q'].
          * rewrite path_at_nil in Hq. injection Hq as Hq.
            exfalso. exact (Hzi (eq_sym Hq)).
          * rewrite path_at_cons in Hq.
            destruct (tree_ent t i g) as [w0 |] eqn:Hw; [| discriminate].
            exfalso. exact (Hsink g w0 Hw).
        + pose proof (Hkeep s f j Hs Hji He) as He'.
          apply (IH j Hq).
          * exact (rch_snoc t ROOTINO s f j Hs He).
          * exact (rch_snoc t' ROOTINO s f j Hs' He').
          * exact Hji. }
    assert (Hri : ROOTINO <> i).
    { intros Hc. apply Hzi.
      (* if the root were the sink, nothing would be reachable but it *)
      destruct p as [| f p'].
      - rewrite path_at_nil in Hpz. injection Hpz as Hpz.
        exact (eq_trans (eq_sym Hpz) Hc).
      - rewrite path_at_cons in Hpz.
        destruct (tree_ent t ROOTINO f) as [j |] eqn:He; [| discriminate].
        exfalso. rewrite Hc in He. exact (Hsink f j He). }
    apply (Hgen p ROOTINO Hpz (rch_refl t ROOTINO) (rch_refl t' ROOTINO)
             Hri).
  Qed.

  (* ==================================================================== *)
  (*  19.  EFFECT 5 -- UNLINKING AN ENTRY                                  *)
  (*                                                                       *)
  (*  Record [k] of [d] is zeroed and the target loses a link; a           *)
  (*  directory target additionally costs the parent the link its ".."     *)
  (*  paid for, and leaves [rd] (it was dots-only, so it orphans exactly   *)
  (*  itself).  The two arms are separate lemmas over ONE definition.      *)
  (* ==================================================================== *)

  Definition eff_unlink_entry (d : Z) (k : nat) (i : Z) : Z -> list (bv 8) :=
    let dnd := fs_dinode P sb d in
    let dni := fs_dinode P sb i in
    let base :=
      if decide (bv_unsigned (di_type dni) = T_DIR_z)
      then eff_dinode P sb d (di_nlink_dec dnd)
      else P in
    let a := fs_blk_addr P dnd (k / 64)%nat in
    fs_upd (eff_dinode base sb i (di_nlink_dec dni)) a
      (fs_splice (P a) (16 * (k mod 64)) 16
         (fun j => dirent_bytes dirent_zero !!! j)).

  Lemma eff_unlink_entry_file_wf (d : Z) (k : nat) (i : Z) :
    0 <= d < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
    fs_reachable P sb d ->
    (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat ->
    (2 <= k)%nat ->
    dir_live (fs_file_data P sb d) k ->
    bv_unsigned (dir_inum (fs_file_data P sb d) k) = i ->
    (bv_unsigned (di_type (fs_dinode P sb i)) = T_FILE_z
     \/ bv_unsigned (di_type (fs_dinode P sb i)) = T_DEVICE_z) ->
    fs_durable_wf_view (eff_unlink_entry d k i).
  Proof.
    intros Hd Hdty Hdre Hk Hk2 Hlvk Hieq Hity.
    set (dn := fs_dinode P sb d) in *.
    set (dni := fs_dinode P sb i) in *.
    unfold fs_file_data in Hlvk, Hieq. fold dn in Hlvk, Hieq.
    set (szd := bv_unsigned (di_size dn)) in *.
    set (nrec := dir_nrec szd) in *.
    set (data := fs_data_of P dn) in *.
    set (dni' := di_nlink_dec dni).
    set (P' := eff_unlink_entry d k i).
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
    pose proof (fdi_size _ _ _ Hdok_d) as Hcapd. fold dn in Hcapd.
    pose proof (proj1 (bv_unsigned_in_range _ (di_size dn))) as Hsz0.
    destruct (fdo_ent _ _ _ _ Hddok k Hk Hlvk) as (Hirange & _).
    fold data in Hirange. rewrite Hieq in Hirange.
    assert (Htyi' : di_type dni' = di_type dni) by reflexivity.
    assert (Haddri' : di_addrs dni' = di_addrs dni) by reflexivity.
    assert (Hszi' : di_size dni' = di_size dni) by reflexivity.
    assert (Hwfi' : dinode_wf dni')
      by (apply di_set_nlink_wf, fs_dinode_wf).
    pose proof (dok_at i ltac:(lia) Hilive) as Hdok_i. fold dni in Hdok_i.
    (* the record's block, as in the link effect *)
    destruct (dots_flat d Hd Hdty) as
      (Hnrec2 & Hlv0 & Hin0 & Hbn0 & Hlv1 & Hbn1).
    fold dn data in Hnrec2, Hlv0, Hin0, Hbn0, Hlv1, Hbn1.
    fold szd nrec in Hnrec2.
    destruct (fdo_gran _ _ _ _ Hddok) as (qd & Hqd). fold szd in Hqd.
    assert (Hsz16 : szd = 16 * Z.of_nat nrec).
    { unfold nrec, dir_nrec. rewrite Z2Nat.id by (apply Z.div_pos; lia).
      rewrite Hqd. rewrite Z.div_mul by lia. lia. }
    assert (Hkwin : 16 * (Z.of_nat k + 1) <= fs_nblk szd * BSIZE_z).
    { pose proof (fs_nblk_cover szd ltac:(lia)) as Hcov.
      unfold BSIZE_z in *. lia. }
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
    destruct (fs_sb_ok_meta sb Hok) as (Hm1 & Hm2 & Hm3).
    pose proof Hnin_le as HninN.
    assert (HdN : 0 <= d < 16 * (sb_ninodes sb / 16 + 1)) by lia.
    assert (HiN : 0 <= i < 16 * (sb_ninodes sb / 16 + 1)) by lia.
    destruct (iblock_bounds sb Hok d HdN) as (Hibd1 & Hibd2 & Hibd3).
    destruct (iblock_bounds sb Hok i HiN) as (Hibi1 & Hibi2 & Hibi3).
    (* the FILE arm's base is [P] itself *)
    assert (HPdef : P' = fs_upd (eff_dinode P sb i dni')
                          (fs_blk_addr P dn (k / 64))
                          (fs_splice (P (fs_blk_addr P dn (k / 64)))
                             (16 * (k mod 64)) 16
                             (fun j => dirent_bytes dirent_zero !!! j))).
    { unfold P', eff_unlink_entry. cbv zeta. fold dn dni.
      rewrite decide_False by exact Hinotdir. reflexivity. }
    assert (HaE : forall b : Z,
              b <> fs_blk_addr P dn (k / 64) ->
              b <> IBLOCK (fs_inum_bv i) (sb_inodestart sb) ->
              P' b = P b).
    { intros b Hb1 Hb2. rewrite HPdef.
      rewrite fs_upd_ne by exact Hb1.
      exact (eff_dinode_out sb _ _ _ _ Hb2). }
    assert (HsbU : P' SB_BNO = P SB_BNO).
    { apply HaE; unfold SB_BNO, fs_data_start in *; lia. }
    assert (HbmU : P' (sb_bmapstart sb) = P (sb_bmapstart sb)).
    { apply HaE; unfold fs_data_start in *; lia. }
    assert (HaB : P' (fs_blk_addr P dn (k / 64))
                  = fs_splice (P (fs_blk_addr P dn (k / 64)))
                      (16 * (k mod 64)) 16
                      (fun j => dirent_bytes dirent_zero !!! j)).
    { rewrite HPdef. apply fs_upd_at. }
    assert (Hdec : forall z : Z, 0 <= z < 16 * (sb_ninodes sb / 16 + 1) ->
              fs_dinode P' sb z
              = if decide (z = i) then dni' else fs_dinode P sb z).
    { intros z Hz.
      transitivity (fs_dinode (eff_dinode P sb i dni') sb z).
      - apply fs_dinode_ext. rewrite HPdef.
        apply fs_upd_ne.
        destruct (iblock_bounds sb Hok z Hz) as (Hz1 & Hz2 & Hz3).
        unfold fs_data_start in Ha_rng. lia.
      - exact (eff_dinode_dec sb Hok P i dni' z Hwfi' HiN Hz). }
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
        apply HaE; [| unfold fs_data_start in *; blk_ne Hibd3 Hibi3].
        intros Hc.
        apply Hne.
        apply (Hslotinj k' (k / 64)%nat ltac:(lia) ltac:(lia)).
        + rewrite (fs_slot_blk dn k' Hk'). exact Hnz.
        + rewrite (fs_slot_blk dn k' Hk'),
            (fs_slot_blk dn (k / 64)%nat HkbM).
          exact Hc.
      - rewrite (fs_blk_addr_high P dn k' Hk'). exact HsbU. }
    assert (HindD : fs_ind_ents P' dn = fs_ind_ents P dn).
    { apply fs_ind_ents_ext. intros Hnz12.
      assert (Hin' : bv_unsigned (di_addrs dn !!! 12%nat)
                     ∈ fs_inode_blocks P dn).
      { rewrite <- (fs_slot_max P dn).
        apply (fs_slot_elem_dok P sb dn); [exact Hdok_d | lia |].
        rewrite fs_slot_max. exact Hnz12. }
      pose proof (blocks_range d _ Hd Hdlive Hin') as Hbr.
      apply HaE; [| unfold fs_data_start in *; blk_ne Hibd3 Hibi3].
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
        unfold fs_data_start in Hbr. clear -Hbr Hibd3 Hibi3. lia. }
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
      apply HaE; [| unfold fs_data_start in *; blk_ne Hibd3 Hibi3].
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
        apply HaE; [| unfold fs_data_start in *; blk_ne Hibd3 Hibi3].
        intros Hc.
        refine (blocks_cross i d (fs_blk_addr P dn (k / 64)%nat)
                  ltac:(lia) Hd
                  ltac:(intros Hcc; exact (Hdi_ne (eq_sym Hcc)))
                  Hilive Hdlive _ Ha_in).
        rewrite <- Hc. exact Hin'.
      - rewrite (fs_blk_addr_high P dni k0 Hk0). exact HsbU. }
    (* the zeroed record, at the view *)
    destruct (dirent_zeroed P' dn dn k eq_refl HindD Ha0 HaB Hother)
      as (Hzero & Hwagree).
    pose proof Hzero as (Hz0 & Hzinum & Hzname).
    assert (Hview : dir_view (fs_data_of P' dn) nrec
                    = delete (dir_bname data k) (dir_view data nrec)).
    { apply (dir_view_zero data _ nrec k (fdo_unique _ _ _ _ Hddok)
               Hk Hlvk Hzero). }
    assert (Htyp : forall z : Z, 0 <= z < sb_ninodes sb ->
              bv_unsigned (di_type (fs_dinode P' sb z))
              = bv_unsigned (di_type (fs_dinode P sb z))).
    { intros z Hz. rewrite (Hdec z ltac:(irng)).
      destruct (decide (z = i)) as [-> | Hzi];
        [rewrite Htyi'; reflexivity | reflexivity]. }
    assert (Hentd : forall f : fname,
              tree_ent (tree_of_disk P' sb) d f
              = delete (dir_bname data k) (dir_view data nrec) !! f).
    { intros f.
      rewrite (tree_ent_dir_eq P' d Hd)
        by (rewrite (Htyp d Hd); exact Hdty).
      unfold fs_file_data.
      rewrite (Hdec d ltac:(irng)).
      rewrite decide_False by (intros Hc; exact (Hdi_ne Hc)).
      fold dn szd nrec. rewrite Hview. reflexivity. }
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
        + rewrite (Hdec j ltac:(irng)), decide_False by exact Hji.
          reflexivity.
        + intros Hjl k0 Hk0.
          destruct (Hunt j Hjr Hjd Hji Hjl) as (_ & Hdata & _ & _).
          exact (Hdata k0). }
    (* the view names [i] only at record [k]'s name *)
    assert (Hviewk : dir_view data nrec !! dir_bname data k = Some i).
    { rewrite <- Hieq. unfold data.
      apply dir_view_live; [exact (fdo_unique _ _ _ _ Hddok) | exact Hk
                            | exact Hlvk]. }
    assert (Hfwd : forall z : Z, fs_reachable P' sb z ->
              fs_reachable P sb z).
    { intros z Hz. unfold fs_reachable in *.
      apply (rch_mono t (tree_of_disk P' sb) ROOTINO); [| exact Hz].
      intros j f w0 Hj' Hj He.
      destruct (decide (j = d)) as [-> | Hjd].
      - rewrite Hentd in He. rewrite Hentt.
        destruct (decide (f = dir_bname data k)) as [-> | Hfn].
        + rewrite lookup_delete in He. discriminate.
        + rewrite lookup_delete_ne in He
            by (intros Hc; exact (Hfn (eq_sym Hc))).
          exact He.
      - rewrite (Hentother j f Hjd) in He. exact He. }
    assert (Hbwd : forall z : Z, fs_reachable P sb z -> z <> i ->
              fs_reachable P' sb z).
    { intros z Hz Hzi. unfold fs_reachable in *.
      apply (rch_keep_target (tree_of_disk P' sb) i); [| | exact Hz
                                                       | exact Hzi].
      - intros f w0 Hw. unfold t in Hw.
        rewrite (tree_ent_nondir P i f) in Hw; [discriminate | ].
        exact Hinotdir.
      - intros j f w0 Hj Hwi He.
        destruct (decide (j = d)) as [-> | Hjd].
        + rewrite Hentt in He. rewrite Hentd.
          destruct (decide (f = dir_bname data k)) as [-> | Hfn].
          * exfalso. rewrite Hviewk in He. injection He as He.
            exact (Hwi (eq_sym He)).
          * rewrite lookup_delete_ne
              by (intros Hc; exact (Hfn (eq_sym Hc))).
            exact He.
        + rewrite (Hentother j f Hjd). exact He. }
    (* the segment loses record [k]'s ticket *)
    assert (Hsegd : forall z : Z,
              Z.of_nat (fs_tick_count (fs_dir_tickets P' d dn) z)
              = Z.of_nat (fs_tick_count (fs_dir_tickets P d dn) z)
                - Z.of_nat (otick (Some i) z)).
    { intros z. unfold fs_dir_tickets. fold szd nrec.
      rewrite (tick_omap_upd (fs_rec_ticket P d dn)
                 (fs_rec_ticket P' d dn) nrec k z Hk).
      - assert (Hgk : fs_rec_ticket P' d dn k = None).
        { unfold fs_rec_ticket. cbv zeta.
          rewrite (proj2 (dir_liveb_false _ _) Hz0). reflexivity. }
        assert (Hfk : fs_rec_ticket P d dn k = Some i).
        { unfold fs_rec_ticket. cbv zeta. fold data.
          rewrite (proj2 (dir_liveb_true _ _) Hlvk). cbn [andb].
          rewrite Hieq.
          rewrite bool_decide_eq_false_2
            by (intros Hc; exact (Hdi_ne (eq_sym Hc))).
          cbn [negb]. reflexivity. }
        rewrite Hgk, Hfk. cbn [otick]. lia.
      - intros q Hq Hqk.
        unfold fs_rec_ticket. cbv zeta.
        rewrite (dir_liveb_agree _ _ q (Hwagree q Hqk)).
        rewrite (dir_inum_agree _ _ q (Hwagree q Hqk)).
        reflexivity. }
    assert (Hcount : forall z : Z,
              Z.of_nat (fs_rtick P' sb rd z)
              = Z.of_nat (fs_rtick P sb rd z) - Z.of_nat (otick (Some i) z)).
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
        fold dn.
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
          rewrite decide_False by exact Hxi. reflexivity.
        + intros _ k0 Hk0.
          destruct (Hunt _ Hxr Hxd Hxi Hxl) as (_ & Hdata & _ & _).
          exact (Hdata k0). }
    (* the target's old link count is at least one *)
    assert (Hnl1 : 1 <= bv_unsigned (di_nlink dni)).
    { pose proof (Hlkg i ltac:(lia) Hilive) as Hold. cbv zeta in Hold.
      fold dni in Hold.
      assert (Hrt : (1 <= fs_rtick P sb rd i)%nat).
      { rewrite <- Hieq.
        apply (rtick_of_record d k Hd_rd Hk).
        - unfold fs_file_data. fold dn data. exact Hlvk.
        - unfold fs_file_data. fold dn data. rewrite Hieq.
          intros Hc. exact (Hdi_ne (eq_sym Hc)). }
      rewrite (bool_decide_eq_false_2
                 (bv_unsigned (di_type dni) = T_DIR_z) Hinotdir) in Hold.
      lia. }
    assert (Hnli'u : bv_unsigned (di_nlink dni')
                     = bv_unsigned (di_nlink dni) - 1).
    { unfold dni'. unfold di_nlink_dec. cbn [di_nlink di_set_nlink].
      apply Z_to_bv_small.
      assert (Hm16 : bv_modulus 16 = 65536) by reflexivity.
      pose proof (proj2 (bv_unsigned_in_range _ (di_nlink dni))) as Hup.
      unfold bv_modulus in Hup.
      change (2 ^ Z.of_N 16) with 65536 in Hup. lia. }
    assert (Hdwfi : fs_inode_dwf P' sb dni' = true).
    { pose proof (dwf_bool_at i ltac:(lia) Hilive) as Hold.
      fold dni in Hold.
      unfold fs_inode_dwf in Hold |- *. cbv zeta in Hold |- *.
      rewrite HindI, Haddri', Htyi', Hszi'. exact Hold. }
    assert (Hblki : fs_inode_blocks P' dni' = fs_inode_blocks P dni).
    { unfold fs_inode_blocks. cbv zeta.
      rewrite HindI, Haddri', Hszi'. reflexivity. }
    assert (Hbnk_dot' : dir_bname data k <> dot_name).
    { intros Hc.
      pose proof (fdo_unique _ _ _ _ Hddok) as Huq.
      assert (Hkeq : k = 0%nat).
      { apply (Huq k 0%nat Hk ltac:(fold szd nrec; lia) Hlvk Hlv0).
        fold data. rewrite Hc. rewrite Hbn0. reflexivity. }
      lia. }
    assert (Hbnk_dd' : dir_bname data k <> dotdot_name).
    { intros Hc.
      pose proof (fdo_unique _ _ _ _ Hddok) as Huq.
      assert (Hkeq : k = 1%nat).
      { apply (Huq k 1%nat Hk ltac:(fold szd nrec; lia) Hlvk Hlv1).
        fold data. rewrite Hc. rewrite Hbn1. reflexivity. }
      lia. }
    (* [d]'s own readers: the dinode is untouched, its data moved at [k] *)
    assert (HdataD : forall k0 : nat, k0 <> (k / 64)%nat ->
              fs_data_of P' dn k0 = fs_data_of P dn k0).
    { intros k0 Hk0. apply (fs_data_of_same P P' dn k0 HindD).
      intros Hnz. apply Hother; [exact Hk0 | exact Hnz]. }
    assert (Hdwfd : fs_inode_dwf P' sb dn = true).
    { pose proof (dwf_bool_at d Hd Hdlive) as Hold. fold dn in Hold.
      rewrite (fs_inode_dwf_same P P' sb dn HindD). exact Hold. }
    assert (Hblkd : fs_inode_blocks P' dn = fs_inode_blocks P dn)
      by (exact (fs_inode_blocks_same P P' dn HindD)).
    (* -------- assemble ------------------------------------------------- *)
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
          { rewrite Heq. fold dn.
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
          rewrite decide_False by (intros Hc; exact (Hdi_ne Hc)).
          fold dn szd nrec. rewrite Hview.
          rewrite lookup_delete_ne
            by (intros Hc; exact (Hbnk_dd' Hc)).
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
      + apply (fs_dots_wf_win P P' d dn dn).
        * lia.
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
        apply (fs_region_free_spec P sb nib z
                 (fs_region_wf_free P sb nib Hreg)); lia.
      + intros z Hz Hfree.
        rewrite (Hdec z ltac:(irng)) in Hfree |- *.
        destruct (decide (z = i)) as [-> | Hzi].
        { exfalso. rewrite Htyi' in Hfree. exact (Hilive Hfree). }
        apply (fs_region_nlink_free P sb nib z
                 (fs_region_wf_nlink P sb nib Hreg)); [lia | exact Hfree].
      + intros z Hz.
        rewrite (Hdec z ltac:(irng)).
        destruct (decide (z = i)) as [-> | Hzi].
        * rewrite Hnli'u.
          pose proof (fs_region_nlink_short P sb nib i
                        (fs_region_wf_nlink P sb nib Hreg) ltac:(lia))
            as Hsh.
          fold dni in Hsh. lia.
        * apply (fs_region_nlink_short P sb nib z
                   (fs_region_wf_nlink P sb nib Hreg)). lia.
    - exists rd.
      split; [| split; [| split]].
      + intros z. rewrite (Hrd z).
        destruct (decide (0 <= z < sb_ninodes sb)) as [Hzr | Hzr].
        * rewrite (Htyp z Hzr).
          assert (Hzi_dir : bv_unsigned (di_type (fs_dinode P sb z))
                            = T_DIR_z -> z <> i).
          { intros Hty Hc. rewrite Hc in Hty. exact (Hinotdir Hty). }
          split; intros (A & B & C); (split; [exact A |]);
            (split; [exact B |]).
          -- exact (Hbwd z C (Hzi_dir B)).
          -- exact (Hfwd z C).
        * split; intros (A & _); [lia | lia].
      + intros z Hz.
        destruct (proj1 (Hrd z) Hz) as (Hzr & Hzty & _).
        destruct (decide (z = d)) as [-> | Hzd].
        * assert (Hdecd : fs_dinode P' sb d = dn).
          { rewrite (Hdec d ltac:(irng)).
            rewrite decide_False by (intros Hc; exact (Hdi_ne Hc)).
            reflexivity. }
          rewrite Hdecd.
          destruct Hddok as [Hgr Hent Huq Hdot Hdd].
          constructor.
          -- exact Hgr.
          -- intros k0 Hk0 Hlive'. fold szd nrec in Hk0.
             destruct (decide (k0 = k)) as [-> | Hk0k].
             { exfalso. exact (dir_zeroed_dead _ _ _ Hzero Hlive'). }
             assert (Hlv : dir_live data k0).
             { unfold dir_live in *. rewrite Hzinum in Hlive';
                 [exact Hlive' | exact Hk0k]. }
             destruct (Hent k0 Hk0 Hlv) as (Hran & Hty0).
             fold data in Hran, Hty0.
             rewrite (Hzinum k0 Hk0k).
             fold data. split; [exact Hran |].
             rewrite (Htyp (bv_unsigned (dir_inum data k0)) ltac:(lia)).
             exact Hty0.
          -- fold szd nrec.
             exact (dir_names_unique_zero _ _ nrec k Hzero Huq).
          -- fold szd nrec. rewrite Hview.
             rewrite lookup_delete_ne
               by (intros Hc; exact (Hbnk_dot' Hc)).
             exact Hdot.
          -- fold szd nrec. rewrite Hview.
             rewrite lookup_delete_ne
               by (intros Hc; exact (Hbnk_dd' Hc)).
             exact Hdd.
        * assert (Hzi : z <> i)
            by (intros Hc; rewrite Hc in Hzty; exact (Hinotdir Hzty)).
          assert (Hzl : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
            by (rewrite Hzty; unfold T_DIR_z; discriminate).
          destruct (Hunt z Hzr Hzd Hzi Hzl) as (_ & Hdata & _ & _).
          apply dir_ok_untouched; [exact Hz | | |].
          -- rewrite (Hdec z ltac:(irng)).
             rewrite decide_False by exact Hzi. reflexivity.
          -- intros k0 Hk0. exact (Hdata k0).
          -- intros w0 Hw0 Hwl Hw0'. exfalso. apply Hwl.
             rewrite <- (Htyp w0 Hw0). exact Hw0'.
      + intros z Hz. cbv zeta.
        rewrite (Hdec z ltac:(irng)).
        destruct (decide (z = i)) as [-> | Hzi].
        * rewrite Htyi'. intros Hnz.
          rewrite Hnli'u.
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
        * intros Hnz.
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


  Local Lemma tick_mjoin_two' (F : nat -> list Z) (n m1 m2 : nat) (z : Z) :
    (m1 < n)%nat -> (m2 < n)%nat -> m1 <> m2 ->
    (fs_tick_count (F m1) z + fs_tick_count (F m2) z
     <= fs_tick_count (mjoin (F <$> seq 0 n)) z)%nat.
  Proof.
    intros H1 H2 Hne.
    destruct (Nat.lt_ge_cases m1 m2) as [Hlt | Hge].
    - apply tick_mjoin_two. lia.
    - pose proof (tick_mjoin_two F n m2 m1 z ltac:(lia)). lia.
  Qed.

  Local Lemma node_of_meta (dn1 dn2 : dinode) (dat : nat -> list (bv 8)) :
    di_type dn2 = di_type dn1 -> di_size dn2 = di_size dn1 ->
    node_of dn2 dat = node_of dn1 dat.
  Proof. intros Ht Hs. unfold node_of. rewrite Ht, Hs. reflexivity. Qed.

  Lemma eff_unlink_entry_dir_wf (d : Z) (k : nat) (i : Z) :
    0 <= d < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
    fs_reachable P sb d ->
    (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat ->
    (2 <= k)%nat ->
    dir_live (fs_file_data P sb d) k ->
    bv_unsigned (dir_inum (fs_file_data P sb d) k) = i ->
    i <> d ->
    bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z ->
    bv_unsigned (di_nlink (fs_dinode P sb i)) = 1 ->
    fs_dir_dots_only P (fs_dinode P sb i) ->
    bv_unsigned (dir_inum (fs_data_of P (fs_dinode P sb i)) 1) = d ->
    fs_durable_wf_view (eff_unlink_entry d k i).
  Proof.
    intros Hd Hdty Hdre Hk Hk2 Hlvk Hieq Hid_ne Hity Hnl1 Honly Hddi.
    set (dn := fs_dinode P sb d) in *.
    set (dni := fs_dinode P sb i) in *.
    unfold fs_file_data in Hlvk, Hieq. fold dn in Hlvk, Hieq.
    set (szd := bv_unsigned (di_size dn)) in *.
    set (nrec := dir_nrec szd) in *.
    set (data := fs_data_of P dn) in *.
    set (datai := fs_data_of P dni) in *.
    set (dnd' := di_nlink_dec dn).
    set (dni' := di_nlink_dec dni).
    set (P' := eff_unlink_entry d k i).
    assert (Hdi_ne : d <> i) by (intros Hc; exact (Hid_ne (eq_sym Hc))).
    assert (Hdlive : bv_unsigned (di_type dn) <> 0)
      by (rewrite Hdty; unfold T_DIR_z; discriminate).
    assert (Hilive : bv_unsigned (di_type dni) <> 0)
      by (rewrite Hity; unfold T_DIR_z; discriminate).
    assert (Hd_rd : d ∈ rd)
      by (apply (Hrd d); split; [lia | split; [exact Hdty | exact Hdre]]).
    pose proof (Hdok d Hd_rd) as Hddok. fold dn in Hddok.
    pose proof (dok_at d Hd Hdlive) as Hdok_d. fold dn in Hdok_d.
    pose proof (fdi_size _ _ _ Hdok_d) as Hcapd. fold dn in Hcapd.
    pose proof (proj1 (bv_unsigned_in_range _ (di_size dn))) as Hsz0.
    destruct (fdo_ent _ _ _ _ Hddok k Hk Hlvk) as (Hirange & _).
    fold data in Hirange. rewrite Hieq in Hirange.
    pose proof (dok_at i ltac:(lia) Hilive) as Hdok_i. fold dni in Hdok_i.
    assert (Htyd' : di_type dnd' = di_type dn) by reflexivity.
    assert (Haddrd' : di_addrs dnd' = di_addrs dn) by reflexivity.
    assert (Hszd'e : di_size dnd' = di_size dn) by reflexivity.
    assert (Htyi' : di_type dni' = di_type dni) by reflexivity.
    assert (Haddri' : di_addrs dni' = di_addrs dni) by reflexivity.
    assert (Hszi' : di_size dni' = di_size dni) by reflexivity.
    assert (Hwfd' : dinode_wf dnd')
      by (apply di_set_nlink_wf, fs_dinode_wf).
    assert (Hwfi' : dinode_wf dni')
      by (apply di_set_nlink_wf, fs_dinode_wf).
    destruct (dots_flat d Hd Hdty) as
      (Hnrec2 & Hlv0 & Hin0 & Hbn0 & Hlv1 & Hbn1).
    fold dn data in Hnrec2, Hlv0, Hin0, Hbn0, Hlv1, Hbn1.
    fold szd nrec in Hnrec2.
    destruct (dots_flat i ltac:(lia) Hity) as
      (Hnrec2i & Hlv0i & Hin0i & Hbn0i & Hlv1i & Hbn1i).
    fold dni datai in Hnrec2i, Hlv0i, Hin0i, Hbn0i, Hlv1i, Hbn1i.
    fold datai in Hddi. fold dni in Honly.
    (* --- the reachable child and its exactly-one ticket ---------------- *)
    assert (Hentt : forall f : fname,
              tree_ent t d f = dir_view data nrec !! f).
    { intros f. unfold t.
      rewrite (tree_ent_dir_eq P d Hd Hdty).
      unfold fs_file_data. fold dn. fold szd nrec data. reflexivity. }
    assert (Hviewk : dir_view data nrec !! dir_bname data k = Some i).
    { rewrite <- Hieq. unfold data.
      apply dir_view_live; [exact (fdo_unique _ _ _ _ Hddok) | exact Hk
                            | exact Hlvk]. }
    assert (Hire : fs_reachable P sb i).
    { apply (rch_snoc t ROOTINO d (dir_bname data k)); [exact Hdre |].
      rewrite Hentt. exact Hviewk. }
    assert (Hi_rd : i ∈ rd)
      by (apply (Hrd i); split; [lia | split; [exact Hity | exact Hire]]).
    assert (Hbonus0 : (if bool_decide (bv_unsigned (di_type dni) = T_DIR_z)
                       then (if bool_decide (i = ROOTINO) then 1 else 0)
                       else 0)
                      = (if bool_decide (i = ROOTINO) then 1 else 0))
      by (rewrite (bool_decide_eq_true_2 _ Hity); reflexivity).
    assert (Hrt1 : (1 <= fs_rtick P sb rd i)%nat).
    { rewrite <- Hieq.
      apply (rtick_of_record d k Hd_rd Hk).
      - unfold fs_file_data. fold dn data. exact Hlvk.
      - unfold fs_file_data. fold dn data. rewrite Hieq.
        intros Hc. exact (Hid_ne Hc). }
    assert (Hiroot : i <> ROOTINO).
    { intros Hc.
      pose proof (Hlkg i ltac:(lia) Hilive) as Hold. cbv zeta in Hold.
      fold dni in Hold. rewrite Hbonus0 in Hold.
      rewrite (bool_decide_eq_true_2 (i = ROOTINO) Hc) in Hold.
      lia. }
    assert (Hcnt1 : Z.of_nat (fs_rtick P sb rd i) = 1).
    { pose proof (Hlkg i ltac:(lia) Hilive) as Hold. cbv zeta in Hold.
      fold dni in Hold. rewrite Hbonus0 in Hold.
      rewrite (bool_decide_eq_false_2 (i = ROOTINO) Hiroot) in Hold.
      lia. }
    (* one live record in one reachable directory names the child *)
    assert (Hticket : forall (j : Z) (k1 : nat),
              j ∈ rd -> j <> i ->
              (k1 < dir_nrec
                      (bv_unsigned (di_size (fs_dinode P sb j))))%nat ->
              dir_live (fs_data_of P (fs_dinode P sb j)) k1 ->
              bv_unsigned (dir_inum (fs_data_of P (fs_dinode P sb j)) k1)
              = i ->
              fs_rec_ticket P j (fs_dinode P sb j) k1 = Some i).
    { intros j k1 Hj Hji Hk1 Hlv' Hin'.
      unfold fs_rec_ticket. cbv zeta.
      rewrite (proj2 (dir_liveb_true _ _) Hlv'). cbn [andb].
      rewrite Hin'.
      rewrite bool_decide_eq_false_2
        by (intros Hc; exact (Hji (eq_sym Hc))).
      cbn [negb]. reflexivity. }
    assert (Hsegof : forall (j : Z) (k1 : nat),
              j ∈ rd -> j <> i ->
              (k1 < dir_nrec
                      (bv_unsigned (di_size (fs_dinode P sb j))))%nat ->
              dir_live (fs_data_of P (fs_dinode P sb j)) k1 ->
              bv_unsigned (dir_inum (fs_data_of P (fs_dinode P sb j)) k1)
              = i ->
              (1 <= fs_tick_count (fs_dir_tickets_at P sb j) i)%nat).
    { intros j k1 Hj Hji Hk1 Hlv' Hin'.
      destruct (proj1 (Hrd j) Hj) as (Hjr & Hjty & _).
      unfold fs_dir_tickets_at. cbv zeta.
      rewrite (proj2 (Z.eqb_eq _ _) Hjty).
      apply fs_tick_count_elem.
      unfold fs_dir_tickets.
      apply elem_of_list_omap. exists k1.
      split; [apply elem_of_seq; lia |].
      exact (Hticket j k1 Hj Hji Hk1 Hlv' Hin'). }
    assert (Huniqrec : forall (j : Z) (k1 : nat),
              j ∈ rd -> j <> i ->
              (k1 < dir_nrec
                      (bv_unsigned (di_size (fs_dinode P sb j))))%nat ->
              dir_live (fs_data_of P (fs_dinode P sb j)) k1 ->
              bv_unsigned (dir_inum (fs_data_of P (fs_dinode P sb j)) k1)
              = i ->
              j = d /\ k1 = k).
    { intros j k1 Hj Hji Hk1 Hlv' Hin'.
      destruct (proj1 (Hrd j) Hj) as (Hjr & Hjty & _).
      set (F := fun x : nat =>
                  if bool_decide (Z.of_nat x ∈ rd)
                  then fs_dir_tickets_at P sb (Z.of_nat x) else []).
      assert (HFd : F (Z.to_nat d) = fs_dir_tickets_at P sb d).
      { unfold F. rewrite Z2Nat.id by lia.
        rewrite bool_decide_eq_true_2 by exact Hd_rd. reflexivity. }
      assert (HFj : F (Z.to_nat j) = fs_dir_tickets_at P sb j).
      { unfold F. rewrite Z2Nat.id by lia.
        rewrite bool_decide_eq_true_2 by exact Hj. reflexivity. }
      destruct (decide (j = d)) as [-> | Hjd].
      - split; [reflexivity |].
        destruct (decide (k1 = k)) as [-> | Hk1k]; [reflexivity |].
        exfalso.
        (* two live records of [d] name [i]: the count passes one *)
        assert (Hseg2 : (2 <= fs_tick_count (fs_dir_tickets_at P sb d)
                               i)%nat).
        { unfold fs_dir_tickets_at. cbv zeta. fold dn.
          rewrite (proj2 (Z.eqb_eq _ _) Hdty).
          unfold fs_dir_tickets.
          assert (Hf1 : fs_rec_ticket P d (fs_dinode P sb d) k1 = Some i)
            by (exact (Hticket d k1 Hd_rd
                         ltac:(intros Hc; exact (Hdi_ne Hc))
                         Hk1 Hlv' Hin')).
          assert (Hf2 : fs_rec_ticket P d (fs_dinode P sb d) k = Some i).
          { apply (Hticket d k Hd_rd
                     ltac:(intros Hc; exact (Hdi_ne Hc))).
            - fold dn. fold szd nrec. exact Hk.
            - fold dn data. exact Hlvk.
            - fold dn data. exact Hieq. }
          destruct (Nat.lt_ge_cases k1 k) as [Hlt | Hge].
          - pose proof (tick_omap_two
                          (fs_rec_ticket P d (fs_dinode P sb d))
                          (dir_nrec (bv_unsigned
                                       (di_size (fs_dinode P sb d))))
                          k1 k i
                          ltac:(split; [exact Hlt |
                                        fold dn; fold szd nrec; exact Hk]))
              as Htwo.
            rewrite Hf1, Hf2 in Htwo. cbn [otick] in Htwo.
            rewrite bool_decide_eq_true_2 in Htwo by reflexivity.
            fold dn in Htwo. lia.
          - pose proof (tick_omap_two
                          (fs_rec_ticket P d (fs_dinode P sb d))
                          (dir_nrec (bv_unsigned
                                       (di_size (fs_dinode P sb d))))
                          k k1 i ltac:(lia))
              as Htwo.
            rewrite Hf1, Hf2 in Htwo. cbn [otick] in Htwo.
            rewrite bool_decide_eq_true_2 in Htwo by reflexivity.
            fold dn in Htwo. lia. }
        assert (Hcnt2 : (2 <= fs_rtick P sb rd i)%nat); [| lia].
        unfold fs_rtick, fs_rtickets.
        pose proof (tick_mjoin_le F (Z.to_nat (sb_ninodes sb))
                      (Z.to_nat d) i ltac:(lia)) as Hle.
        rewrite HFd in Hle. unfold F in Hle. lia.
      - exfalso.
        assert (Hseg1 : (1 <= fs_tick_count (fs_dir_tickets_at P sb j)
                               i)%nat)
          by (exact (Hsegof j k1 Hj Hji Hk1 Hlv' Hin')).
        assert (Hsegd1 : (1 <= fs_tick_count (fs_dir_tickets_at P sb d)
                                i)%nat).
        { apply (Hsegof d k Hd_rd
                   ltac:(intros Hc; exact (Hdi_ne Hc))).
          - fold dn. fold szd nrec. exact Hk.
          - fold dn data. exact Hlvk.
          - fold dn data. exact Hieq. }
        assert (Hcnt2 : (2 <= fs_rtick P sb rd i)%nat); [| lia].
        unfold fs_rtick, fs_rtickets.
        pose proof (tick_mjoin_two' F (Z.to_nat (sb_ninodes sb))
                      (Z.to_nat j) (Z.to_nat d) i
                      ltac:(lia) ltac:(lia)
                      ltac:(intros Hc; apply Hjd; lia)) as Hle.
        rewrite HFd, HFj in Hle. unfold F in Hle. lia. }
    (* --- geometry of the record's block, as before --------------------- *)
    destruct (fdo_gran _ _ _ _ Hddok) as (qd & Hqd). fold szd in Hqd.
    assert (Hsz16 : szd = 16 * Z.of_nat nrec).
    { unfold nrec, dir_nrec. rewrite Z2Nat.id by (apply Z.div_pos; lia).
      rewrite Hqd. rewrite Z.div_mul by lia. lia. }
    assert (Hkwin : 16 * (Z.of_nat k + 1) <= fs_nblk szd * BSIZE_z).
    { pose proof (fs_nblk_cover szd ltac:(lia)) as Hcov.
      unfold BSIZE_z in *. lia. }
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
    destruct (fs_sb_ok_meta sb Hok) as (Hm1 & Hm2 & Hm3).
    pose proof Hnin_le as HninN.
    assert (HdN : 0 <= d < 16 * (sb_ninodes sb / 16 + 1)) by lia.
    assert (HiN : 0 <= i < 16 * (sb_ninodes sb / 16 + 1)) by lia.
    destruct (iblock_bounds sb Hok d HdN) as (Hibd1 & Hibd2 & Hibd3).
    destruct (iblock_bounds sb Hok i HiN) as (Hibi1 & Hibi2 & Hibi3).
    (* --- the effect's blocks ------------------------------------------- *)
    assert (HPdef : P' = fs_upd
                          (eff_dinode (eff_dinode P sb d dnd') sb i dni')
                          (fs_blk_addr P dn (k / 64))
                          (fs_splice (P (fs_blk_addr P dn (k / 64)))
                             (16 * (k mod 64)) 16
                             (fun j => dirent_bytes dirent_zero !!! j))).
    { unfold P', eff_unlink_entry. cbv zeta. fold dn dni.
      rewrite decide_True by exact Hity. reflexivity. }
    assert (HaE : forall b : Z,
              b <> fs_blk_addr P dn (k / 64) ->
              b <> IBLOCK (fs_inum_bv d) (sb_inodestart sb) ->
              b <> IBLOCK (fs_inum_bv i) (sb_inodestart sb) ->
              P' b = P b).
    { intros b Hb1 Hb2 Hb3. rewrite HPdef.
      rewrite fs_upd_ne by exact Hb1.
      rewrite (eff_dinode_out sb) by exact Hb3.
      exact (eff_dinode_out sb _ _ _ _ Hb2). }
    assert (HsbU : P' SB_BNO = P SB_BNO).
    { apply HaE; unfold SB_BNO, fs_data_start in *; lia. }
    assert (HbmU : P' (sb_bmapstart sb) = P (sb_bmapstart sb)).
    { apply HaE; unfold fs_data_start in *; lia. }
    assert (HaB : P' (fs_blk_addr P dn (k / 64))
                  = fs_splice (P (fs_blk_addr P dn (k / 64)))
                      (16 * (k mod 64)) 16
                      (fun j => dirent_bytes dirent_zero !!! j)).
    { rewrite HPdef. apply fs_upd_at. }
    assert (Hdec : forall z : Z, 0 <= z < 16 * (sb_ninodes sb / 16 + 1) ->
              fs_dinode P' sb z
              = if decide (z = i) then dni'
                else if decide (z = d) then dnd' else fs_dinode P sb z).
    { intros z Hz.
      transitivity (fs_dinode
                      (eff_dinode (eff_dinode P sb d dnd') sb i dni') sb z).
      - apply fs_dinode_ext. rewrite HPdef.
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
                  ltac:(lia) Hd
                  ltac:(intros Hcc; exact (Hdi_ne (eq_sym Hcc)))
                  Hilive Hdlive _ Ha_in).
        rewrite <- Hc. exact Hin'.
      - rewrite (fs_blk_addr_high P dni k0 Hk0). exact HsbU. }
    (* the zeroed record, at the parent's view *)
    destruct (dirent_zeroed P' dn dnd' k Haddrd' HindD Ha0 HaB Hother)
      as (Hzero & Hwagree).
    pose proof Hzero as (Hz0 & Hzinum & Hzname).
    assert (Hview : dir_view (fs_data_of P' dnd') nrec
                    = delete (dir_bname data k) (dir_view data nrec)).
    { apply (dir_view_zero data _ nrec k (fdo_unique _ _ _ _ Hddok)
               Hk Hlvk Hzero). }
    assert (Htyp : forall z : Z, 0 <= z < sb_ninodes sb ->
              bv_unsigned (di_type (fs_dinode P' sb z))
              = bv_unsigned (di_type (fs_dinode P sb z))).
    { intros z Hz. rewrite (Hdec z ltac:(irng)).
      destruct (decide (z = i)) as [-> | Hzi];
        [rewrite Htyi'; reflexivity |].
      destruct (decide (z = d)) as [-> | Hzd];
        [rewrite Htyd'; reflexivity | reflexivity]. }
    assert (Hbnk_dot' : dir_bname data k <> dot_name).
    { intros Hc.
      pose proof (fdo_unique _ _ _ _ Hddok) as Huq.
      assert (Hkeq : k = 0%nat).
      { apply (Huq k 0%nat Hk ltac:(fold szd nrec; lia) Hlvk Hlv0).
        fold data. rewrite Hc. rewrite Hbn0. reflexivity. }
      lia. }
    assert (Hbnk_dd' : dir_bname data k <> dotdot_name).
    { intros Hc.
      pose proof (fdo_unique _ _ _ _ Hddok) as Huq.
      assert (Hkeq : k = 1%nat).
      { apply (Huq k 1%nat Hk ltac:(fold szd nrec; lia) Hlvk Hlv1).
        fold data. rewrite Hc. rewrite Hbn1. reflexivity. }
      lia. }
    (* --- the tree ------------------------------------------------------ *)
    assert (Hentd : forall f : fname,
              tree_ent (tree_of_disk P' sb) d f
              = delete (dir_bname data k) (dir_view data nrec) !! f).
    { intros f.
      rewrite (tree_ent_dir_eq P' d Hd)
        by (rewrite (Htyp d Hd); exact Hdty).
      unfold fs_file_data.
      rewrite (Hdec d ltac:(irng)).
      rewrite decide_False by (intros Hc; exact (Hdi_ne Hc)).
      rewrite decide_True by reflexivity.
      rewrite Hszd'e. fold szd nrec. rewrite Hview. reflexivity. }
    assert (Hnodei : node_at P' sb i = node_at P sb i).
    { rewrite (node_at_live P sb i Hilive).
      rewrite (node_at_live P' sb i)
        by (rewrite (Hdec i HiN), decide_True by reflexivity;
            rewrite Htyi'; exact Hilive).
      unfold fs_file_data.
      rewrite (Hdec i HiN), decide_True by reflexivity.
      rewrite (node_of_meta dni dni' _ Htyi' Hszi').
      pose proof (fdi_size _ _ _ Hdok_i) as Hszbi. fold dni in Hszbi.
      pose proof (proj1 (bv_unsigned_in_range _ (di_size dni))) as Hsz0i.
      destruct (dir_nrec_bound (bv_unsigned (di_size dni)) Hsz0i Hszbi)
        as [Hnri Hbbi].
      f_equal.
      apply (node_of_agree _ _ _ FS_MAXFILE); [| exact Hnri | exact Hbbi].
      intros k0 Hk0. fold dni. exact (HdataI k0). }
    assert (Hentother : forall (j : Z) (f : fname), j <> d ->
              tree_ent (tree_of_disk P' sb) j f = tree_ent t j f).
    { intros j f Hjd.
      destruct (decide (j = i)) as [-> | Hji].
      - apply tree_ent_untouched. intros _. exact Hnodei.
      - apply tree_ent_untouched. intros Hjr.
        apply node_at_untouched; [exact Hjr | |].
        + rewrite (Hdec j ltac:(irng)).
          rewrite decide_False by exact Hji.
          rewrite decide_False by exact Hjd. reflexivity.
        + intros Hjl k0 Hk0.
          destruct (Hunt j Hjr Hjd Hji Hjl) as (_ & Hdata & _ & _).
          exact (Hdata k0). }
    assert (Hfwd : forall z : Z, fs_reachable P' sb z ->
              fs_reachable P sb z).
    { intros z Hz. unfold fs_reachable in *.
      apply (rch_mono t (tree_of_disk P' sb) ROOTINO); [| exact Hz].
      intros j f w0 Hj' Hj He.
      destruct (decide (j = d)) as [-> | Hjd].
      - rewrite Hentd in He. rewrite Hentt.
        destruct (decide (f = dir_bname data k)) as [-> | Hfn].
        + rewrite lookup_delete in He. discriminate.
        + rewrite lookup_delete_ne in He
            by (intros Hc; exact (Hfn (eq_sym Hc))).
          exact He.
      - rewrite (Hentother j f Hjd) in He. exact He. }
    (* the tree-level in-edge fact, from the ticket-level one *)
    assert (Hinedge : forall (j : Z) (f : fname),
              rch t ROOTINO j -> j <> i ->
              tree_ent t j f = Some i -> j = d /\ f = dir_bname data k).
    { intros j f Hj Hji He.
      apply (tree_ent_char P j f i) in He.
      destruct He as (Hjr & Hjty & Hv).
      assert (Hjrd : j ∈ rd)
        by (apply (Hrd j); split; [exact Hjr | split; [exact Hjty | exact Hj]]).
      apply dir_view_lookup_rec in Hv.
      destruct Hv as (k1 & Hk1 & Hlv1' & Hbn1' & Hin1').
      unfold fs_file_data in Hk1, Hlv1', Hbn1', Hin1'.
      destruct (Huniqrec j k1 Hjrd Hji Hk1 Hlv1' Hin1') as (-> & ->).
      split; [reflexivity |].
      rewrite <- Hbn1'. unfold data. reflexivity. }
    assert (Hout_i : forall (f : fname) (w0 : Z),
              tree_ent t i f = Some w0 -> w0 = i \/ w0 = d).
    { intros f w0 He.
      apply (tree_ent_char P i f w0) in He.
      destruct He as (_ & _ & Hv).
      apply dir_view_lookup_rec in Hv.
      destruct Hv as (k1 & Hk1 & Hlv1' & _ & Hin1').
      unfold fs_file_data in Hk1, Hlv1', Hin1'.
      fold dni datai in Hk1, Hlv1', Hin1'.
      destruct k1 as [| [| k1']].
      - left. rewrite <- Hin1'. rewrite Hin0i. reflexivity.
      - right. rewrite <- Hin1'. rewrite Hddi. reflexivity.
      - exfalso. apply (Honly (S (S k1')) ltac:(lia) Hk1).
        fold datai. exact Hlv1'. }
    assert (Hkeep : forall z : Z, fs_reachable P sb z -> z <> i ->
              fs_reachable P' sb z).
    { intros z Hz Hzi. unfold fs_reachable in *.
      apply (rch_delete_keep t (tree_of_disk P' sb) ROOTINO d i
               (dir_bname data k));
        [exact Hiroot | exact Hid_ne | | exact Hinedge | exact Hout_i
         | | exact Hz | exact Hzi].
      - rewrite Hentt. exact Hviewk.
      - intros j f w0 Hj Hji Hnotdel He.
        destruct (decide (j = d)) as [-> | Hjd].
        + rewrite Hentd.
          rewrite Hentt in He.
          destruct (decide (f = dir_bname data k)) as [-> | Hfn].
          * exfalso. apply Hnotdel. split; reflexivity.
          * rewrite lookup_delete_ne
              by (intros Hc; exact (Hfn (eq_sym Hc))).
            exact He.
        + rewrite (Hentother j f Hjd). exact He. }
    assert (Hnoin : ~ fs_reachable P' sb i).
    { unfold fs_reachable.
      apply (rch_no_in (tree_of_disk P' sb) ROOTINO i).
      - intros Hc. exact (Hiroot Hc).
      - intros j f Hj' Hji He.
        assert (Hj : rch t ROOTINO j) by (exact (Hfwd j Hj')).
        destruct (decide (j = d)) as [-> | Hjd].
        + rewrite Hentd in He.
          destruct (decide (f = dir_bname data k)) as [-> | Hfn].
          * rewrite lookup_delete in He. discriminate.
          * rewrite lookup_delete_ne in He
              by (intros Hc; exact (Hfn (eq_sym Hc))).
            assert (He' : tree_ent t d f = Some i)
              by (rewrite Hentt; exact He).
            destruct (Hinedge d f Hj
                        ltac:(intros Hc; exact (Hdi_ne Hc)) He')
              as (_ & Hf).
            exact (Hfn Hf).
        + rewrite (Hentother j f Hjd) in He.
          destruct (Hinedge j f Hj Hji He) as (Hc & _).
          exact (Hjd Hc). }
    (* --- the supply loses two tickets ---------------------------------- *)
    set (rd' := rd ∖ ({[i]} : gset Z)).
    assert (Hird' : i ∉ rd') by (apply not_elem_of_difference; right;
                                  apply elem_of_singleton; reflexivity).
    assert (Hrd'mem : forall z : Z, z <> i -> (z ∈ rd' <-> z ∈ rd)).
    { intros z Hzi. unfold rd'.
      rewrite elem_of_difference, elem_of_singleton. tauto. }
    assert (Hd_rd' : d ∈ rd')
      by (apply (Hrd'mem d ltac:(intros Hc; exact (Hdi_ne Hc))); exact Hd_rd).
    assert (Hsegi : forall z : Z,
              Z.of_nat (fs_tick_count (fs_dir_tickets P i dni) z)
              = Z.of_nat (otick (Some d) z)).
    { intros z. unfold fs_dir_tickets.
      set (f0 := fs_rec_ticket P i dni).
      assert (Hf00 : f0 0%nat = None).
      { unfold f0, fs_rec_ticket. cbv zeta. fold datai.
        rewrite (proj2 (dir_liveb_true _ _) Hlv0i). cbn [andb].
        rewrite Hin0i.
        rewrite bool_decide_eq_true_2 by reflexivity.
        reflexivity. }
      assert (Hf01 : f0 1%nat = Some d).
      { unfold f0, fs_rec_ticket. cbv zeta. fold datai.
        rewrite (proj2 (dir_liveb_true _ _) Hlv1i). cbn [andb].
        rewrite Hddi.
        rewrite bool_decide_eq_false_2
          by (intros Hc; exact (Hdi_ne Hc)).
        cbn [negb]. reflexivity. }
      assert (Hfq : forall q : nat, (2 <= q)%nat ->
                (q < dir_nrec (bv_unsigned (di_size dni)))%nat ->
                f0 q = None).
      { intros q Hq2 Hqn.
        unfold f0, fs_rec_ticket. cbv zeta. fold datai.
        assert (Hz0' : dir_inum datai q = bv_0 16).
        { destruct (decide (dir_inum datai q = bv_0 16))
            as [He | Hne']; [exact He |].
          exfalso. apply (Honly q Hq2 Hqn). fold datai. exact Hne'. }
        rewrite (proj2 (dir_liveb_false _ _) Hz0'). reflexivity. }
      replace (dir_nrec (bv_unsigned (di_size dni)))
        with (2 + (dir_nrec (bv_unsigned (di_size dni)) - 2))%nat
        by lia.
      rewrite (tick_omap_pad f0 2 _ z)
        by (intros q Hq; apply Hfq; lia).
      rewrite (tick_omap_snoc f0 1%nat z).
      rewrite (tick_omap_snoc f0 0%nat z).
      rewrite Hf00, Hf01. cbn [otick].
      unfold fs_tick_count. cbn [omap list_omap seq List.filter length].
      lia. }
    assert (Hsegd : forall z : Z,
              Z.of_nat (fs_tick_count (fs_dir_tickets P' d dnd') z)
              = Z.of_nat (fs_tick_count (fs_dir_tickets P d dn) z)
                - Z.of_nat (otick (Some i) z)).
    { intros z. unfold fs_dir_tickets.
      rewrite Hszd'e. fold szd nrec.
      rewrite (tick_omap_upd (fs_rec_ticket P d dn)
                 (fs_rec_ticket P' d dnd') nrec k z Hk).
      - assert (Hgk : fs_rec_ticket P' d dnd' k = None).
        { unfold fs_rec_ticket. cbv zeta.
          rewrite (proj2 (dir_liveb_false _ _) Hz0). reflexivity. }
        assert (Hfk : fs_rec_ticket P d dn k = Some i).
        { unfold fs_rec_ticket. cbv zeta. fold data.
          rewrite (proj2 (dir_liveb_true _ _) Hlvk). cbn [andb].
          rewrite Hieq.
          rewrite bool_decide_eq_false_2
            by (intros Hc; exact (Hdi_ne (eq_sym Hc))).
          cbn [negb]. reflexivity. }
        rewrite Hgk, Hfk. cbn [otick]. lia.
      - intros q Hq Hqk.
        unfold fs_rec_ticket. cbv zeta.
        rewrite (dir_liveb_agree _ _ q (Hwagree q Hqk)).
        rewrite (dir_inum_agree _ _ q (Hwagree q Hqk)).
        reflexivity. }
    assert (Hcount : forall z : Z,
              Z.of_nat (fs_rtick P' sb rd' z)
              = Z.of_nat (fs_rtick P sb rd z)
                - Z.of_nat (otick (Some i) z) - Z.of_nat (otick (Some d) z)).
    { intros z. unfold fs_rtick, fs_rtickets.
      rewrite (tick_mjoin_upd2
                 (fun x : nat =>
                    if bool_decide (Z.of_nat x ∈ rd)
                    then fs_dir_tickets_at P sb (Z.of_nat x) else [])
                 (fun x : nat =>
                    if bool_decide (Z.of_nat x ∈ rd')
                    then fs_dir_tickets_at P' sb (Z.of_nat x) else [])
                 (Z.to_nat (sb_ninodes sb)) (Z.to_nat d) (Z.to_nat i) z
                 ltac:(clear -Hd; lia) ltac:(clear -Hirange; lia)
                 ltac:(clear -Hd Hirange Hid_ne; lia)).
      - (* segment [d] *)
        rewrite Z2Nat.id by lia.
        rewrite bool_decide_eq_true_2 by exact Hd_rd'.
        rewrite bool_decide_eq_true_2 by exact Hd_rd.
        unfold fs_dir_tickets_at. cbv zeta.
        rewrite (Hdec d ltac:(irng)).
        rewrite decide_False by (intros Hc; exact (Hdi_ne Hc)).
        rewrite decide_True by reflexivity.
        rewrite Htyd'. fold dn.
        rewrite (proj2 (Z.eqb_eq _ _) Hdty).
        rewrite (Hsegd z). fold dn.
        (* segment [i] *)
        rewrite Z2Nat.id by lia.
        rewrite (bool_decide_eq_false_2 (i ∈ rd') Hird').
        rewrite bool_decide_eq_true_2 by exact Hi_rd.
        unfold fs_dir_tickets_at. cbv zeta. fold dni.
        rewrite (proj2 (Z.eqb_eq _ _) Hity).
        rewrite fs_tick_count_nil.
        rewrite (Hsegi z). lia.
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
    (* --- the two link counts move down by one -------------------------- *)
    assert (Hnld1 : 1 <= bv_unsigned (di_nlink dn)).
    { pose proof (Hlkg d Hd Hdlive) as Hold. cbv zeta in Hold.
      fold dn in Hold.
      assert (Hrt : (1 <= fs_rtick P sb rd d)%nat).
      { rewrite <- Hddi.
        apply (rtick_of_record i 1%nat Hi_rd).
        - fold dni. lia.
        - unfold fs_file_data. fold dni datai. exact Hlv1i.
        - unfold fs_file_data. fold dni datai. rewrite Hddi.
          intros Hc. exact (Hid_ne (eq_sym Hc)). }
      destruct (bool_decide (bv_unsigned (di_type dn) = T_DIR_z));
        destruct (bool_decide (d = ROOTINO)); lia. }
    assert (Hnld'u : bv_unsigned (di_nlink dnd')
                     = bv_unsigned (di_nlink dn) - 1).
    { unfold dnd'. unfold di_nlink_dec. cbn [di_nlink di_set_nlink].
      apply Z_to_bv_small.
      assert (Hm16 : bv_modulus 16 = 65536) by reflexivity.
      pose proof (proj2 (bv_unsigned_in_range _ (di_nlink dn))) as Hup.
      unfold bv_modulus in Hup.
      change (2 ^ Z.of_N 16) with 65536 in Hup. lia. }
    assert (Hnli'u : bv_unsigned (di_nlink dni') = 0).
    { unfold dni'. unfold di_nlink_dec. cbn [di_nlink di_set_nlink].
      rewrite Hnl1.
      change (Z_to_bv 16 (1 - 1)) with (Z_to_bv 16 0).
      apply Z_to_bv_small.
      assert (Hm16 : bv_modulus 16 = 65536) by reflexivity. lia. }
    (* --- the local sweeps ---------------------------------------------- *)
    assert (Hdwfi : fs_inode_dwf P' sb dni' = true).
    { pose proof (dwf_bool_at i ltac:(lia) Hilive) as Hold.
      fold dni in Hold.
      unfold fs_inode_dwf in Hold |- *. cbv zeta in Hold |- *.
      rewrite HindI, Haddri', Htyi', Hszi'. exact Hold. }
    assert (Hblki : fs_inode_blocks P' dni' = fs_inode_blocks P dni).
    { unfold fs_inode_blocks. cbv zeta.
      rewrite HindI, Haddri', Hszi'. reflexivity. }
    assert (Hdwfd : fs_inode_dwf P' sb dnd' = true).
    { pose proof (dwf_bool_at d Hd Hdlive) as Hold. fold dn in Hold.
      unfold fs_inode_dwf in Hold |- *. cbv zeta in Hold |- *.
      rewrite HindD, Haddrd', Htyd', Hszd'e. exact Hold. }
    assert (Hblkd : fs_inode_blocks P' dnd' = fs_inode_blocks P dn).
    { unfold fs_inode_blocks. cbv zeta.
      rewrite HindD, Haddrd', Hszd'e. reflexivity. }
    (* --- assemble ------------------------------------------------------ *)
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
          rewrite decide_False by (intros Hc; exact (Hdi_ne Hc)).
          rewrite decide_True by reflexivity.
          rewrite Hszd'e. fold szd nrec. rewrite Hview.
          rewrite lookup_delete_ne
            by (intros Hc; exact (Hbnk_dd' Hc)).
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
      + apply (fs_dots_wf_win P P' i dni dni').
        * rewrite Hszi'. lia.
        * apply (dir_win_agree_blocks _ _ FS_MAXFILE);
            [intros k0 Hk0; exact (HdataI k0)
            | unfold FS_MAXFILE, BSIZE; lia].
        * apply (dir_win_agree_blocks _ _ FS_MAXFILE);
            [intros k0 Hk0; exact (HdataI k0)
            | unfold FS_MAXFILE, BSIZE; lia].
        * exact (dots_bool_at i ltac:(lia) Hity).
      + destruct (decide (z = d)) as [-> | Hzd].
        * apply (fs_dots_wf_win P P' d dn dnd').
          -- rewrite Hszd'e. lia.
          -- intros j Hj. exact (Hwagree 0%nat ltac:(lia) j Hj).
          -- intros j Hj. exact (Hwagree 1%nat ltac:(lia) j Hj).
          -- exact (dots_bool_at d Hd Hdty).
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
        { exfalso. rewrite Htyi' in Hfree. exact (Hilive Hfree). }
        destruct (decide (z = d)) as [-> | Hzd].
        { exfalso. rewrite Htyd' in Hfree. exact (Hdlive Hfree). }
        apply (fs_region_nlink_free P sb nib z
                 (fs_region_wf_nlink P sb nib Hreg)); [lia | exact Hfree].
      + intros z Hz.
        rewrite (Hdec z ltac:(irng)).
        destruct (decide (z = i)) as [-> | Hzi].
        { rewrite Hnli'u. lia. }
        destruct (decide (z = d)) as [-> | Hzd].
        * rewrite Hnld'u.
          pose proof (fs_region_nlink_short P sb nib d
                        (fs_region_wf_nlink P sb nib Hreg) ltac:(lia))
            as Hsh.
          fold dn in Hsh. lia.
        * apply (fs_region_nlink_short P sb nib z
                   (fs_region_wf_nlink P sb nib Hreg)). lia.
    - exists rd'.
      split; [| split; [| split]].
      + intros z.
        destruct (decide (z = i)) as [-> | Hzi].
        { split.
          - intros Hc. exfalso. exact (Hird' Hc).
          - intros (_ & _ & Hre). exfalso. exact (Hnoin Hre). }
        rewrite (Hrd'mem z Hzi). rewrite (Hrd z).
        destruct (decide (0 <= z < sb_ninodes sb)) as [Hzr | Hzr].
        * rewrite (Htyp z Hzr).
          split; intros (A & B & C); (split; [exact A |]);
            (split; [exact B |]).
          -- exact (Hkeep z C Hzi).
          -- exact (Hfwd z C).
        * split; intros (A & _); [lia | lia].
      + intros z Hz.
        assert (Hzi : z <> i)
          by (intros ->; exact (Hird' Hz)).
        assert (Hzrd : z ∈ rd) by (apply (Hrd'mem z Hzi); exact Hz).
        destruct (proj1 (Hrd z) Hzrd) as (Hzr & Hzty & _).
        destruct (decide (z = d)) as [-> | Hzd].
        * assert (Hdecd : fs_dinode P' sb d = dnd').
          { rewrite (Hdec d ltac:(irng)).
            rewrite decide_False by (intros Hc; exact (Hdi_ne Hc)).
            rewrite decide_True by reflexivity. reflexivity. }
          rewrite Hdecd.
          destruct Hddok as [Hgr Hent Huq Hdot Hdd].
          constructor.
          -- rewrite Hszd'e. exact Hgr.
          -- intros k0 Hk0 Hlive'.
             rewrite Hszd'e in Hk0. fold szd nrec in Hk0.
             destruct (decide (k0 = k)) as [-> | Hk0k].
             { exfalso. exact (dir_zeroed_dead _ _ _ Hzero Hlive'). }
             assert (Hlv : dir_live data k0).
             { unfold dir_live in *. rewrite Hzinum in Hlive';
                 [exact Hlive' | exact Hk0k]. }
             destruct (Hent k0 Hk0 Hlv) as (Hran & Hty0).
             fold data in Hran, Hty0.
             rewrite (Hzinum k0 Hk0k).
             fold data. split; [exact Hran |].
             rewrite (Htyp (bv_unsigned (dir_inum data k0)) ltac:(lia)).
             exact Hty0.
          -- rewrite Hszd'e. fold szd nrec.
             exact (dir_names_unique_zero _ _ nrec k Hzero Huq).
          -- rewrite Hszd'e. fold szd nrec. rewrite Hview.
             rewrite lookup_delete_ne
               by (intros Hc; exact (Hbnk_dot' Hc)).
             exact Hdot.
          -- rewrite Hszd'e. fold szd nrec. rewrite Hview.
             rewrite lookup_delete_ne
               by (intros Hc; exact (Hbnk_dd' Hc)).
             exact Hdd.
        * assert (Hzl : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
            by (rewrite Hzty; unfold T_DIR_z; discriminate).
          destruct (Hunt z Hzr Hzd Hzi Hzl) as (_ & Hdata & _ & _).
          apply dir_ok_untouched; [exact Hzrd | | |].
          -- rewrite (Hdec z ltac:(irng)).
             rewrite decide_False by exact Hzi.
             rewrite decide_False by exact Hzd. reflexivity.
          -- intros k0 Hk0. exact (Hdata k0).
          -- intros w0 Hw0 Hwl Hw0'. exfalso. apply Hwl.
             rewrite <- (Htyp w0 Hw0). exact Hw0'.
      + intros z Hz. cbv zeta.
        rewrite (Hdec z ltac:(irng)).
        destruct (decide (z = i)) as [-> | Hzi].
        * intros Hnz.
          rewrite Hnli'u.
          pose proof (Hcount i) as Hc. unfold otick in Hc.
          rewrite bool_decide_eq_true_2 in Hc by reflexivity.
          rewrite (bool_decide_eq_false_2 (d = i)
                     ltac:(intros Hcc; exact (Hdi_ne Hcc))) in Hc.
          rewrite (bool_decide_eq_true_2
                     (bv_unsigned (di_type dni') = T_DIR_z))
            by (rewrite Htyi'; exact Hity).
          rewrite (bool_decide_eq_false_2 (i = ROOTINO) Hiroot).
          lia.
        * destruct (decide (z = d)) as [-> | Hzd].
          -- intros Hnz.
             rewrite Hnld'u.
             pose proof (Hcount d) as Hc. unfold otick in Hc.
             rewrite (bool_decide_eq_false_2 (i = d)
                        ltac:(intros Hcc; exact (Hid_ne Hcc))) in Hc.
             rewrite bool_decide_eq_true_2 in Hc by reflexivity.
             pose proof (Hlkg d Hz ltac:(exact Hdlive)) as Hold.
             cbv zeta in Hold. fold dn in Hold.
             rewrite (bool_decide_eq_true_2
                        (bv_unsigned (di_type dnd') = T_DIR_z))
               by (rewrite Htyd'; exact Hdty).
             rewrite (bool_decide_eq_true_2
                        (bv_unsigned (di_type dn) = T_DIR_z) Hdty) in Hold.
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
        { (* the new orphan is dots-only, and its data is untouched *)
          intros k0 Hk02 Hk0n Hlive'.
          rewrite Hszi' in Hk0n.
          apply (Honly k0 Hk02 Hk0n).
          unfold dir_live in *. fold datai.
          pose proof (fdi_size _ _ _ Hdok_i) as Hszbi. fold dni in Hszbi.
          pose proof (proj1 (bv_unsigned_in_range _ (di_size dni)))
            as Hsz0i.
          destruct (dir_nrec_bound (bv_unsigned (di_size dni)) Hsz0i Hszbi)
            as [Hnri _].
          assert (Hwin : dir_win_agree datai (fs_data_of P' dni') k0).
          { apply (dir_win_agree_blocks _ _ FS_MAXFILE);
              [intros k1 Hk1; exact (HdataI k1) | lia]. }
          rewrite (dir_inum_agree _ _ k0 Hwin) in Hlive'. exact Hlive'. }
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

End EffUnlinkEntry.

(* the [fs_durable_wf_view]-level wrappers -- the shape stage G2
   consumes: the invariant of the OLD view, the decode-level
   preconditions, the invariant of the updated view. *)

Lemma eff_unlink_entry_file_wfv (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (i : Z) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 <= d < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
  fs_reachable P sb d ->
  (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat ->
  (2 <= k)%nat ->
  dir_live (fs_file_data P sb d) k ->
  bv_unsigned (dir_inum (fs_file_data P sb d) k) = i ->
  (bv_unsigned (di_type (fs_dinode P sb i)) = T_FILE_z
   \/ bv_unsigned (di_type (fs_dinode P sb i)) = T_DEVICE_z) ->
  fs_durable_wf_view (eff_unlink_entry P sb d k i).
Proof.
  intros Hv Hp. intros.
  destruct Hv as (sb0 & Hp0 & Hsw).
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
  destruct HW45 as (u & Hu & Hbm).
  destruct Hregx as (nib & Hnibz & Hreg).
  destruct HW9 as (rd & Hrd & Hdok & Hlkg & Horph).
  apply (eff_unlink_entry_file_wf P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph); assumption.
Qed.

Lemma eff_unlink_entry_dir_wfv (P : Z -> list (bv 8)) (sb : fs_sb)
    (d : Z) (k : nat) (i : Z) :
  fs_durable_wf_view P ->
  fs_parse_sb P = Some sb ->
  0 <= d < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb d)) = T_DIR_z ->
  fs_reachable P sb d ->
  (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb d))))%nat ->
  (2 <= k)%nat ->
  dir_live (fs_file_data P sb d) k ->
  bv_unsigned (dir_inum (fs_file_data P sb d) k) = i ->
  i <> d ->
  bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z ->
  bv_unsigned (di_nlink (fs_dinode P sb i)) = 1 ->
  fs_dir_dots_only P (fs_dinode P sb i) ->
  bv_unsigned (dir_inum (fs_data_of P (fs_dinode P sb i)) 1) = d ->
  fs_durable_wf_view (eff_unlink_entry P sb d k i).
Proof.
  intros Hv Hp. intros.
  destruct Hv as (sb0 & Hp0 & Hsw).
  assert (Hse : sb0 = sb) by congruence. subst sb0.
  destruct Hsw as [Hsb HW3 HW45 HW7 HW8 Hregx HW9].
  destruct HW45 as (u & Hu & Hbm).
  destruct Hregx as (nib & Hnibz & Hreg).
  destruct HW9 as (rd & Hrd & Hdok & Hlkg & Horph).
  apply (eff_unlink_entry_dir_wf P sb Hp Hsb HW3 u Hu Hbm HW7 HW8 nib Hnibz Hreg rd Hrd Hdok Hlkg Horph); assumption.
Qed.
