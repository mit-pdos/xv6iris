(* ====================================================================== *)
(* FsObjEff.v -- durable-disk flip-A: THE PER-EFFECT OBJECT FOOTPRINTS.    *)
(*                                                                         *)
(* For each F3-final effect of the [FsEff*] band this file names the set    *)
(* of objects it moves and proves the two facts an ending op's arm needs    *)
(* beside its G2 [_wfv] lemma:                                             *)
(*                                                                         *)
(*   FRAME  -- outside the footprint the effect decodes exactly as the      *)
(*             old view did ([obj_agree (eff .. A) A]); and                 *)
(*   FOLD   -- given the block equations the op's own [log_write]s          *)
(*             establish, agreement holds again with the footprint REMOVED  *)
(*             from the pending set ([FsObj.views_agree_fold]).             *)
(*                                                                         *)
(* The arm therefore invokes a PAIR: [eff_X_wfv] (the invariant of the new  *)
(* committed view) and [eff_X_fold] (the bookkeeping of row (a)).           *)
(*                                                                         *)
(* SHAPE.  Every effect is a composition of [fs_upd]s of four kinds, so     *)
(* every frame proof below is [frame_compose] over the four LAYER lemmas    *)
(* of section 1 and nothing else.  The layers are where the geometry side   *)
(* conditions live; an effect's own lemma only has to say which layer it    *)
(* is at and hand over the premises.                                       *)
(*                                                                         *)
(* THREE THINGS WORTH KNOWING at the call site:                            *)
(*                                                                         *)
(* - A dirent write's object is the RECORD [ORec a (k mod 64)] of the       *)
(*   dir's content block [a = fs_blk_addr A dn (k / 64)]; the block is      *)
(*   read off the OLD view [A], which is where the op's own [bmap] read     *)
(*   it too.                                                               *)
(* - A 4-byte indirect-entry write ([eff_alloc_file_block] above NDIRECT)   *)
(*   claims the whole 16-byte RECORD it sits in, i.e. four entries at       *)
(*   once.  That over-approximation is sound because an indirect block      *)
(*   belongs to one inode and the writer holds that inode's lock, so no     *)
(*   second op can own a neighbouring entry.                               *)
(* - [eff_trunc]/[eff_free_inode] claim one [OBit] per freed block and      *)
(*   NOT the freed blocks themselves: the effect does not touch their       *)
(*   bytes.                                                                *)
(* ====================================================================== *)
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
Require Import FsObj.
Require Import FsEffBase.
Require Import FsEffWriteData.
Require Import FsEffTrunc.
Require Import FsEffFreeInode.
Require Import FsEffLinkEntry.
Require Import FsEffUnlinkEntry.
Require Import FsEffCreateEntry.
Require Import FsEffAllocBlock.
Require Import FsEffAllocIndBlock.

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE FOUR LAYERS                                                    *)
(* ====================================================================== *)

(* the inode-region width, in the two spellings the two files use *)
Lemma iblk_width (sb : fs_sb) :
  fs_sb_ok sb ->
  16 * (sb_bmapstart sb - sb_inodestart sb) = 16 * (sb_ninodes sb / 16 + 1).
Proof. intros Hok. rewrite (sbo_bmapstart sb Hok). lia. Qed.

(* ---- layer 1: the dinode re-encode ----------------------------------- *)
Lemma frame_dinode (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z)
    (dn' : dinode) :
  fs_sb_ok sb -> dinode_wf dn' ->
  0 <= z < 16 * (sb_bmapstart sb - sb_inodestart sb) ->
  forall o : fsobj, obj_leaf sb o -> ~ obj_masked {[OSlot z]} sb o ->
    obj_agree (eff_dinode P sb z dn') P sb o.
Proof.
  intros Hok Hwf Hz o Ho Hm.
  assert (Hzn : 0 <= z < 16 * (sb_ninodes sb / 16 + 1))
    by (rewrite <- (iblk_width sb Hok); exact Hz).
  destruct o as [b k | x | y | b]; cbn [obj_leaf obj_blk obj_agree] in *.
  - (* a record of a rec-kind block: the inode block is not one *)
    rewrite (eff_dinode_out sb P z dn' b); [reflexivity |].
    apply not_eq_sym.
    exact (obj_slot_blk_ne_rec sb _ b Hok (obj_slot_blk_of sb z Hok Hz)
             (proj1 Ho)).
  - (* the bitmap block is not an inode block *)
    rewrite (eff_dinode_out sb P z dn' (sb_bmapstart sb)); [reflexivity |].
    apply not_eq_sym.
    exact (obj_slot_blk_ne_bmap sb _ (obj_slot_blk_of sb z Hok Hz)).
  - (* another slot: the decode-level frame *)
    assert (Hne : y <> z).
    { intros ->. apply Hm. left. by apply elem_of_singleton. }
    assert (Hyn : 0 <= y < 16 * (sb_ninodes sb / 16 + 1))
      by (rewrite <- (iblk_width sb Hok); exact Ho).
    rewrite (eff_dinode_dec sb Hok P z dn' y Hwf Hzn Hyn).
    by rewrite decide_False.
  - destruct Ho.
Qed.

(* ---- layer 2: a splice inside ONE record ----------------------------- *)
Lemma frame_splice (P : Z -> list (bv 8)) (sb : fs_sb) (a : Z)
    (base : list (bv 8)) (r o0 len : nat) (g : nat -> bv 8) :
  fs_sb_ok sb -> off_meta sb a -> view_sized P sb -> base = P a ->
  (16 * r <= o0)%nat -> (o0 + len <= 16 * r + 16)%nat ->
  forall o : fsobj, obj_leaf sb o -> ~ obj_masked {[ORec a r]} sb o ->
    obj_agree (fs_upd P a (fs_splice base o0 len g)) P sb o.
Proof.
  intros Hok Ha Hsz -> Hlo Hhi o Ho Hm.
  destruct o as [b k | x | y | b]; cbn [obj_leaf obj_blk obj_agree] in *.
  - destruct Ho as [Hab Hk].
    destruct (decide (b = a)) as [-> | Hne]; [| by rewrite (fs_upd_ne P a b)].
    assert (Hkr : k <> r).
    { intros ->. apply Hm. left. by apply elem_of_singleton. }
    rewrite fs_upd_at.
    assert (HlA : length (P a) = BSIZE)
      by (apply Hsz, (obj_rec_blk_home sb a Hok), Hab).
    unfold FS_NREC, BSIZE in *.
    apply rec_bytes_intro_total;
      [ apply fs_splice_len | exact HlA | exact Hk |].
    intros t Ht. rewrite fs_splice_lookup by (unfold BSIZE; lia).
    by rewrite decide_False by lia.
  - by rewrite (fs_upd_ne P a (sb_bmapstart sb))
      by exact (off_meta_ne_bmap sb a Hok Ha).
  - apply fs_dinode_ext, (fs_upd_ne P a).
    exact (off_meta_ne_slot sb a _ Hok Ha (obj_slot_blk_of sb y Hok Ho)).
  - destruct Ho.
Qed.

(* ---- layer 3: the bitmap re-lay -------------------------------------- *)
Lemma frame_bmap (P : Z -> list (bv 8)) (sb : fs_sb) (u' : gset Z)
    (FB : gset fsobj) :
  fs_sb_ok sb ->
  (forall x : Z, 0 <= x < 8 * BSIZE_z -> OBit x ∉ FB ->
     (x ∈ u' <-> fs_bit (P (sb_bmapstart sb)) x = true)) ->
  forall o : fsobj, obj_leaf sb o -> ~ obj_masked FB sb o ->
    obj_agree (fs_upd P (sb_bmapstart sb) (bm_bytes BSIZE u')) P sb o.
Proof.
  intros Hok Hcond o Ho Hm.
  destruct o as [b k | x | y | b]; cbn [obj_leaf obj_blk obj_agree] in *.
  - by rewrite (fs_upd_ne P (sb_bmapstart sb) b)
      by exact (obj_rec_blk_ne_bmap sb b Hok (proj1 Ho)).
  - rewrite fs_upd_at.
    assert (Hx : OBit x ∉ FB) by (intros Hc; apply Hm; by left).
    rewrite (fs_bit_bm_bytes BSIZE u' x)
      by (rewrite BSIZE_z_nat; exact Ho).
    destruct (fs_bit (P (sb_bmapstart sb)) x) eqn:Hb.
    + apply bool_decide_eq_true_2, (Hcond x Ho Hx). exact Hb.
    + apply bool_decide_eq_false_2. intros Hc.
      rewrite ((proj1 (Hcond x Ho Hx)) Hc) in Hb. discriminate.
  - apply fs_dinode_ext, (fs_upd_ne P (sb_bmapstart sb)).
    exact (obj_slot_blk_ne_bmap sb _ (obj_slot_blk_of sb y Hok Ho)).
  - destruct Ho.
Qed.

(* ---- layer 4: a whole data block ------------------------------------- *)
Lemma frame_whole (P : Z -> list (bv 8)) (sb : fs_sb) (c : Z)
    (bs : list (bv 8)) :
  fs_sb_ok sb -> off_meta sb c ->
  forall o : fsobj, obj_leaf sb o -> ~ obj_masked {[OBlk c]} sb o ->
    obj_agree (fs_upd P c bs) P sb o.
Proof.
  intros Hok Hc o Ho Hm.
  destruct o as [b k | x | y | b]; cbn [obj_leaf obj_blk obj_agree] in *.
  - assert (Hne : b <> c).
    { intros ->. apply Hm. right. by apply elem_of_singleton. }
    by rewrite (fs_upd_ne P c b).
  - by rewrite (fs_upd_ne P c (sb_bmapstart sb))
      by exact (off_meta_ne_bmap sb c Hok Hc).
  - apply fs_dinode_ext, (fs_upd_ne P c).
    exact (off_meta_ne_slot sb c _ Hok Hc (obj_slot_blk_of sb y Hok Ho)).
  - destruct Ho.
Qed.

(* ---- the four LAYER STEPS -------------------------------------------
   The frame of a composite effect is built OUTERMOST FIRST: each step's
   conclusion names the layer's own shape ([eff_dinode Q ..], [fs_upd Q
   ..]), so [apply] reads the intermediate view [Q] straight off the goal
   -- which a bare [frame_compose] cannot do (its [Q] occurs only in the
   premises).  Footprints therefore come out left-associated,
   [F_inner ∪ F_this]. *)

Lemma step_dinode (P Q : Z -> list (bv 8)) (sb : fs_sb) (F : gset fsobj)
    (z : Z) (dn' : dinode) :
  fs_sb_ok sb -> dinode_wf dn' ->
  0 <= z < 16 * (sb_bmapstart sb - sb_inodestart sb) ->
  (forall o, obj_leaf sb o -> ~ obj_masked F sb o -> obj_agree Q P sb o) ->
  forall o : fsobj, obj_leaf sb o ->
    ~ obj_masked (F ∪ {[OSlot z]}) sb o -> obj_agree (eff_dinode Q sb z dn') P sb o.
Proof.
  intros Hok Hwf Hz Hin.
  apply (frame_compose P Q _ sb F {[OSlot z]}); [exact Hin |].
  exact (frame_dinode Q sb z dn' Hok Hwf Hz).
Qed.

Lemma step_splice (P Q : Z -> list (bv 8)) (sb : fs_sb) (F : gset fsobj)
    (a : Z) (base : list (bv 8)) (r o0 len : nat) (g : nat -> bv 8) :
  fs_sb_ok sb -> off_meta sb a -> view_sized Q sb -> base = Q a ->
  (16 * r <= o0)%nat -> (o0 + len <= 16 * r + 16)%nat ->
  (forall o, obj_leaf sb o -> ~ obj_masked F sb o -> obj_agree Q P sb o) ->
  forall o : fsobj, obj_leaf sb o ->
    ~ obj_masked (F ∪ {[ORec a r]}) sb o ->
    obj_agree (fs_upd Q a (fs_splice base o0 len g)) P sb o.
Proof.
  intros Hok Ha Hsz Hb Hlo Hhi Hin.
  apply (frame_compose P Q _ sb F {[ORec a r]}); [exact Hin |].
  exact (frame_splice Q sb a base r o0 len g Hok Ha Hsz Hb Hlo Hhi).
Qed.

Lemma step_bmap (P Q : Z -> list (bv 8)) (sb : fs_sb) (F FB : gset fsobj)
    (u' : gset Z) :
  fs_sb_ok sb ->
  (forall x : Z, 0 <= x < 8 * BSIZE_z -> OBit x ∉ FB ->
     (x ∈ u' <-> fs_bit (Q (sb_bmapstart sb)) x = true)) ->
  (forall o, obj_leaf sb o -> ~ obj_masked F sb o -> obj_agree Q P sb o) ->
  forall o : fsobj, obj_leaf sb o ->
    ~ obj_masked (F ∪ FB) sb o ->
    obj_agree (fs_upd Q (sb_bmapstart sb) (bm_bytes BSIZE u')) P sb o.
Proof.
  intros Hok Hcond Hin.
  apply (frame_compose P Q _ sb F FB); [exact Hin |].
  exact (frame_bmap Q sb u' FB Hok Hcond).
Qed.

Lemma step_whole (P Q : Z -> list (bv 8)) (sb : fs_sb) (F : gset fsobj)
    (c : Z) (bs : list (bv 8)) :
  fs_sb_ok sb -> off_meta sb c ->
  (forall o, obj_leaf sb o -> ~ obj_masked F sb o -> obj_agree Q P sb o) ->
  forall o : fsobj, obj_leaf sb o ->
    ~ obj_masked (F ∪ {[OBlk c]}) sb o -> obj_agree (fs_upd Q c bs) P sb o.
Proof.
  intros Hok Hc Hin.
  apply (frame_compose P Q _ sb F {[OBlk c]}); [exact Hin |].
  exact (frame_whole Q sb c bs Hok Hc).
Qed.

(* ---- the two bitmap conditions the effects need ---------------------- *)
Lemma bmap_cond_add (P : Z -> list (bv 8)) (sb : fs_sb) (S : gset Z)
    (FB : gset fsobj) :
  (forall x : Z, OBit x ∉ FB -> x ∉ S) ->
  forall x : Z, 0 <= x < 8 * BSIZE_z -> OBit x ∉ FB ->
    (x ∈ fs_bmap_set BSIZE (P (sb_bmapstart sb)) ∪ S
     <-> fs_bit (P (sb_bmapstart sb)) x = true).
Proof.
  intros HS x Hx Hnb. rewrite elem_of_union, fs_bmap_set_elem, BSIZE_z_nat.
  split.
  - intros [[_ Hb] | Hc]; [exact Hb | by destruct (HS x Hnb Hc)].
  - intros Hb. left. split; [exact Hx | exact Hb].
Qed.

Lemma bmap_cond_del (P : Z -> list (bv 8)) (sb : fs_sb) (S : gset Z)
    (FB : gset fsobj) :
  (forall x : Z, OBit x ∉ FB -> x ∉ S) ->
  forall x : Z, 0 <= x < 8 * BSIZE_z -> OBit x ∉ FB ->
    (x ∈ fs_bmap_set BSIZE (P (sb_bmapstart sb)) ∖ S
     <-> fs_bit (P (sb_bmapstart sb)) x = true).
Proof.
  intros HS x Hx Hnb. rewrite elem_of_difference, fs_bmap_set_elem, BSIZE_z_nat.
  split.
  - intros [[_ Hb] _]. exact Hb.
  - intros Hb. split; [split; [exact Hx | exact Hb] | exact (HS x Hnb)].
Qed.

(* ---- sizes ----------------------------------------------------------- *)
Lemma view_sized_upd (P : Z -> list (bv 8)) (sb : fs_sb) (b : Z)
    (bs : list (bv 8)) :
  view_sized P sb -> length bs = BSIZE -> view_sized (fs_upd P b bs) sb.
Proof.
  intros Hsz Hlen c Hc. unfold fs_upd.
  destruct (decide (c = b)) as [-> | Hne]; [exact Hlen | exact (Hsz c Hc)].
Qed.

Lemma view_sized_dinode (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (dn' : dinode) :
  view_sized P sb -> dinode_wf dn' -> view_sized (eff_dinode P sb i dn') sb.
Proof.
  intros Hsz Hwf. unfold eff_dinode. apply view_sized_upd; [exact Hsz |].
  apply diblk_bytes_length_16, diblk_wf_insert; [apply fs_iblk_wf | exact Hwf].
Qed.

(* mkdir's dots block is a well-formed dir block, hence [BSIZE] bytes *)
Lemma mkdir_blk_wf (i d : Z) :
  dirblk_wf ([de_of_name (Z_to_bv 16 i) dot_name;
              de_of_name (Z_to_bv 16 d) dotdot_name]
             ++ replicate 62 dirent_zero).
Proof.
  split.
  - rewrite length_app, length_replicate. reflexivity.
  - apply Forall_app. split.
    + constructor; [apply de_of_name_wf |].
      constructor; [apply de_of_name_wf | constructor].
    + apply Forall_replicate_de, dirent_zero_wf.
Qed.

(* ---- the block a dirent write lands in is not metadata --------------- *)
Lemma blk_addr_off_meta (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode)
    (k : nat) :
  fs_sb_ok sb -> fs_inode_dok P sb dn -> (k < FS_MAXFILE)%nat ->
  off_meta sb (fs_blk_addr P dn k).
Proof.
  intros Hok Hdok Hk. unfold off_meta.
  destruct (decide (fs_blk_addr P dn k = 0)) as [-> | Hnz].
  - left. destruct (obj_geom sb Hok) as (H1 & _). lia.
  - right. exact (proj1 (fs_blk_addr_range P sb dn k Hdok Hk Hnz)).
Qed.

Lemma dok_of_wfv (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_durable_wf_view P -> fs_parse_sb P = Some sb ->
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  fs_inode_dok P sb (fs_dinode P sb i).
Proof.
  intros (sb' & Hp' & Hsw) Hp Hi Hty.
  assert (Hse : sb' = sb) by congruence. subst sb'.
  exact (fs_inodes_dwf_spec P sb i (fdw_inodes _ _ Hsw) Hi Hty).
Qed.

(* the inum range the object layer wants, from the one an op carries *)
Lemma inum_obj_range (sb : fs_sb) (i : Z) :
  fs_sb_ok sb -> 0 <= i < sb_ninodes sb ->
  0 <= i < 16 * (sb_bmapstart sb - sb_inodestart sb).
Proof.
  intros Hok Hi. rewrite (iblk_width sb Hok).
  pose proof (iblk_z_range sb i Hi). lia.
Qed.

(* ====================================================================== *)
(*  2.  THE DIRENT EFFECTS (link / create / create-dir / unlink)           *)
(* ====================================================================== *)

(* the dir record a dirent effect writes, as an object *)
Definition dirent_obj (P : Z -> list (bv 8)) (sb : fs_sb) (d : Z) (k : nat)
  : fsobj :=
  ORec (fs_blk_addr P (fs_dinode P sb d) (k / 64)%nat) (k `mod` 64)%nat.

Definition foot_link_entry (P : Z -> list (bv 8)) (sb : fs_sb) (d : Z)
    (k : nat) (i : Z) : gset fsobj :=
  {[OSlot d]} ∪ {[OSlot i]} ∪ {[dirent_obj P sb d k]}.

Lemma eff_link_entry_frame (P : Z -> list (bv 8)) (sb : fs_sb) (d : Z)
    (k : nat) (name : fname) (i : Z) :
  fs_sb_ok sb -> view_sized P sb ->
  0 <= d < sb_ninodes sb -> 0 <= i < sb_ninodes sb ->
  off_meta sb (fs_blk_addr P (fs_dinode P sb d) (k / 64)%nat) ->
  forall o : fsobj, obj_leaf sb o ->
    ~ obj_masked (foot_link_entry P sb d k i) sb o ->
    obj_agree (eff_link_entry P sb d k name i) P sb o.
Proof.
  intros Hok Hsz Hd Hi Ha.
  assert (Hdb := obj_slot_blk_of sb d Hok (inum_obj_range sb d Hok Hd)).
  assert (Hib := obj_slot_blk_of sb i Hok (inum_obj_range sb i Hok Hi)).
  unfold eff_link_entry, foot_link_entry, dirent_obj.
  apply (step_splice _ _ sb _ _ _ (k `mod` 64)%nat (16 * (k `mod` 64))%nat
           16%nat);
    [exact Hok | exact Ha | | | lia | lia |].
  - apply view_sized_dinode; [apply view_sized_dinode; [exact Hsz |] |];
      [apply di_set_size_wf, fs_dinode_wf | apply di_set_nlink_wf, fs_dinode_wf].
  - rewrite (eff_dinode_out sb _ i _ _), (eff_dinode_out sb P d _ _);
      [reflexivity | |].
    + exact (not_eq_sym (off_meta_ne_slot sb _ _ Hok Ha Hdb)).
    + exact (not_eq_sym (off_meta_ne_slot sb _ _ Hok Ha Hib)).
  - apply (step_dinode P _ sb {[OSlot d]});
      [exact Hok | apply di_set_nlink_wf, fs_dinode_wf
       | exact (inum_obj_range sb i Hok Hi) |].
    apply frame_dinode;
      [exact Hok | apply di_set_size_wf, fs_dinode_wf
       | exact (inum_obj_range sb d Hok Hd)].
Qed.

Lemma eff_link_entry_sized (P : Z -> list (bv 8)) (sb : fs_sb) (d : Z)
    (k : nat) (name : fname) (i : Z) :
  view_sized P sb -> view_sized (eff_link_entry P sb d k name i) sb.
Proof.
  intros Hsz. unfold eff_link_entry.
  apply view_sized_upd; [| apply fs_splice_len].
  apply view_sized_dinode; [apply view_sized_dinode; [exact Hsz |] |];
    [apply di_set_size_wf, fs_dinode_wf | apply di_set_nlink_wf, fs_dinode_wf].
Qed.

(* the fold: the three blocks the op logged are the three the effect
   wrote -- the dir's record block and the two inode blocks. *)
Lemma eff_link_entry_fold (A L : Z -> list (bv 8)) (sb : fs_sb)
    (pend : gset fsobj) (d : Z) (k : nat) (name : fname) (i : Z) :
  fs_sb_ok sb -> views_agree_off A L sb pend ->
  0 <= d < sb_ninodes sb -> 0 <= i < sb_ninodes sb ->
  off_meta sb (fs_blk_addr A (fs_dinode A sb d) (k / 64)%nat) ->
  eff_link_entry A sb d k name i (IBLOCK (fs_inum_bv d) (sb_inodestart sb))
    = L (IBLOCK (fs_inum_bv d) (sb_inodestart sb)) ->
  eff_link_entry A sb d k name i (IBLOCK (fs_inum_bv i) (sb_inodestart sb))
    = L (IBLOCK (fs_inum_bv i) (sb_inodestart sb)) ->
  eff_link_entry A sb d k name i (fs_blk_addr A (fs_dinode A sb d) (k / 64)%nat)
    = L (fs_blk_addr A (fs_dinode A sb d) (k / 64)%nat) ->
  views_agree_off (eff_link_entry A sb d k name i) L sb
    (pend ∖ foot_link_entry A sb d k i).
Proof.
  intros Hok Hag Hd Hi Ha HbD HbI HbA.
  apply (views_agree_fold A _ L sb pend (foot_link_entry A sb d k i)).
  - exact Hag.
  - exact (eff_link_entry_frame A sb d k name i Hok
             (vao_szA _ _ _ _ Hag) Hd Hi Ha).
  - exact (eff_link_entry_sized A sb d k name i (vao_szA _ _ _ _ Hag)).
  - intros b Hb. apply elem_of_map in Hb as (o & -> & Ho).
    unfold foot_link_entry, dirent_obj in Ho.
    apply elem_of_union in Ho as [Ho | Ho];
      [apply elem_of_union in Ho as [Ho | Ho] |];
      apply elem_of_singleton in Ho as ->; cbn [obj_blk].
    + exact HbD.
    + exact HbI.
    + exact HbA.
Qed.

(* ---- create (mknod's net) -------------------------------------------- *)
Definition foot_create_entry (P : Z -> list (bv 8)) (sb : fs_sb) (d : Z)
    (k : nat) (i : Z) : gset fsobj :=
  {[OSlot d]} ∪ {[OSlot i]} ∪ {[dirent_obj P sb d k]}.

Lemma eff_create_entry_frame (P : Z -> list (bv 8)) (sb : fs_sb) (d : Z)
    (k : nat) (name : fname) (i : Z) (ty maj min : bv 16) :
  fs_sb_ok sb -> view_sized P sb ->
  0 <= d < sb_ninodes sb -> 0 <= i < sb_ninodes sb ->
  off_meta sb (fs_blk_addr P (fs_dinode P sb d) (k / 64)%nat) ->
  forall o : fsobj, obj_leaf sb o ->
    ~ obj_masked (foot_create_entry P sb d k i) sb o ->
    obj_agree (eff_create_entry P sb d k name i ty maj min) P sb o.
Proof.
  intros Hok Hsz Hd Hi Ha.
  assert (Hdb := obj_slot_blk_of sb d Hok (inum_obj_range sb d Hok Hd)).
  assert (Hib := obj_slot_blk_of sb i Hok (inum_obj_range sb i Hok Hi)).
  unfold eff_create_entry, foot_create_entry, dirent_obj.
  apply (step_splice _ _ sb _ _ _ (k `mod` 64)%nat (16 * (k `mod` 64))%nat
           16%nat);
    [exact Hok | exact Ha | | | lia | lia |].
  - apply view_sized_dinode; [apply view_sized_dinode; [exact Hsz |] |];
      [apply di_set_size_wf, fs_dinode_wf | apply di_create_wf].
  - rewrite (eff_dinode_out sb _ i _ _), (eff_dinode_out sb P d _ _);
      [reflexivity | |].
    + exact (not_eq_sym (off_meta_ne_slot sb _ _ Hok Ha Hdb)).
    + exact (not_eq_sym (off_meta_ne_slot sb _ _ Hok Ha Hib)).
  - apply (step_dinode P _ sb {[OSlot d]});
      [exact Hok | apply di_create_wf
       | exact (inum_obj_range sb i Hok Hi) |].
    apply frame_dinode;
      [exact Hok | apply di_set_size_wf, fs_dinode_wf
       | exact (inum_obj_range sb d Hok Hd)].
Qed.

Lemma eff_create_entry_sized (P : Z -> list (bv 8)) (sb : fs_sb) (d : Z)
    (k : nat) (name : fname) (i : Z) (ty maj min : bv 16) :
  view_sized P sb -> view_sized (eff_create_entry P sb d k name i ty maj min) sb.
Proof.
  intros Hsz. unfold eff_create_entry.
  apply view_sized_upd; [| apply fs_splice_len].
  apply view_sized_dinode; [apply view_sized_dinode; [exact Hsz |] |];
    [apply di_set_size_wf, fs_dinode_wf | apply di_create_wf].
Qed.

Lemma eff_create_entry_fold (A L : Z -> list (bv 8)) (sb : fs_sb)
    (pend : gset fsobj) (d : Z) (k : nat) (name : fname) (i : Z)
    (ty maj min : bv 16) :
  fs_sb_ok sb -> views_agree_off A L sb pend ->
  0 <= d < sb_ninodes sb -> 0 <= i < sb_ninodes sb ->
  off_meta sb (fs_blk_addr A (fs_dinode A sb d) (k / 64)%nat) ->
  eff_create_entry A sb d k name i ty maj min
    (IBLOCK (fs_inum_bv d) (sb_inodestart sb))
    = L (IBLOCK (fs_inum_bv d) (sb_inodestart sb)) ->
  eff_create_entry A sb d k name i ty maj min
    (IBLOCK (fs_inum_bv i) (sb_inodestart sb))
    = L (IBLOCK (fs_inum_bv i) (sb_inodestart sb)) ->
  eff_create_entry A sb d k name i ty maj min
    (fs_blk_addr A (fs_dinode A sb d) (k / 64)%nat)
    = L (fs_blk_addr A (fs_dinode A sb d) (k / 64)%nat) ->
  views_agree_off (eff_create_entry A sb d k name i ty maj min) L sb
    (pend ∖ foot_create_entry A sb d k i).
Proof.
  intros Hok Hag Hd Hi Ha HbD HbI HbA.
  apply (views_agree_fold A _ L sb pend (foot_create_entry A sb d k i)).
  - exact Hag.
  - exact (eff_create_entry_frame A sb d k name i ty maj min Hok
             (vao_szA _ _ _ _ Hag) Hd Hi Ha).
  - exact (eff_create_entry_sized A sb d k name i ty maj min
             (vao_szA _ _ _ _ Hag)).
  - intros b Hb. apply elem_of_map in Hb as (o & -> & Ho).
    unfold foot_create_entry, dirent_obj in Ho.
    apply elem_of_union in Ho as [Ho | Ho];
      [apply elem_of_union in Ho as [Ho | Ho] |];
      apply elem_of_singleton in Ho as ->; cbn [obj_blk].
    + exact HbD.
    + exact HbI.
    + exact HbA.
Qed.

(* ---- mkdir's fused effect -------------------------------------------- *)
Definition foot_create_dir_entry (P : Z -> list (bv 8)) (sb : fs_sb) (d : Z)
    (k : nat) (i fb : Z) : gset fsobj :=
  {[OSlot d]} ∪ {[OSlot i]} ∪ {[OBit fb]} ∪ {[OBlk fb]}
  ∪ {[dirent_obj P sb d k]}.

Lemma eff_create_dir_entry_frame (P : Z -> list (bv 8)) (sb : fs_sb) (d : Z)
    (k : nat) (name : fname) (i fb : Z) :
  fs_sb_ok sb -> view_sized P sb ->
  0 <= d < sb_ninodes sb -> 0 <= i < sb_ninodes sb ->
  fs_data_start sb <= fb < sb_size sb ->
  off_meta sb (fs_blk_addr P (fs_dinode P sb d) (k / 64)%nat) ->
  fs_blk_addr P (fs_dinode P sb d) (k / 64)%nat <> fb ->
  forall o : fsobj, obj_leaf sb o ->
    ~ obj_masked (foot_create_dir_entry P sb d k i fb) sb o ->
    obj_agree (eff_create_dir_entry P sb d k name i fb) P sb o.
Proof.
  intros Hok Hsz Hd Hi Hfb Ha Hafb.
  assert (Hfbm : off_meta sb fb) by (unfold off_meta; lia).
  assert (Hdb := obj_slot_blk_of sb d Hok (inum_obj_range sb d Hok Hd)).
  assert (Hib := obj_slot_blk_of sb i Hok (inum_obj_range sb i Hok Hi)).
  unfold eff_create_dir_entry, foot_create_dir_entry, dirent_obj.
  apply (step_splice _ _ sb _ _ _ (k `mod` 64)%nat (16 * (k `mod` 64))%nat
           16%nat);
    [exact Hok | exact Ha | | | lia | lia |].
  - apply view_sized_upd; [| apply dirblk_bytes_length_64, mkdir_blk_wf].
    apply view_sized_upd; [| apply bm_bytes_length].
    apply view_sized_dinode; [apply view_sized_dinode; [exact Hsz |] |];
      [apply di_set_nlink_wf, di_set_size_wf, fs_dinode_wf
       | apply di_create_dir_wf].
  - rewrite (fs_upd_ne _ fb _), (fs_upd_ne _ (sb_bmapstart sb) _),
      (eff_dinode_out sb _ i _ _), (eff_dinode_out sb P d _ _);
      [reflexivity | | | |].
    + exact (not_eq_sym (off_meta_ne_slot sb _ _ Hok Ha Hdb)).
    + exact (not_eq_sym (off_meta_ne_slot sb _ _ Hok Ha Hib)).
    + exact (not_eq_sym (off_meta_ne_bmap sb _ Hok Ha)).
    + exact Hafb.
  - apply (step_whole P _ sb _ fb); [exact Hok | exact Hfbm |].
    apply (step_bmap P _ sb _ {[OBit fb]}); [exact Hok | | ].
    + rewrite (eff_dinode_out sb _ i _ _), (eff_dinode_out sb P d _ _);
        [| exact (not_eq_sym (obj_slot_blk_ne_bmap sb _ Hdb))
         | exact (not_eq_sym (obj_slot_blk_ne_bmap sb _ Hib))].
      apply bmap_cond_add. intros x Hx Hc.
      apply elem_of_singleton in Hc as ->. apply Hx, elem_of_singleton.
      reflexivity.
    + apply (step_dinode P _ sb {[OSlot d]});
        [exact Hok | apply di_create_dir_wf
         | exact (inum_obj_range sb i Hok Hi) |].
      apply frame_dinode;
        [exact Hok | apply di_set_nlink_wf, di_set_size_wf, fs_dinode_wf
         | exact (inum_obj_range sb d Hok Hd)].
Qed.

Lemma eff_create_dir_entry_sized (P : Z -> list (bv 8)) (sb : fs_sb) (d : Z)
    (k : nat) (name : fname) (i fb : Z) :
  view_sized P sb -> view_sized (eff_create_dir_entry P sb d k name i fb) sb.
Proof.
  intros Hsz. unfold eff_create_dir_entry.
  apply view_sized_upd; [| apply fs_splice_len].
  apply view_sized_upd; [| apply dirblk_bytes_length_64, mkdir_blk_wf].
  apply view_sized_upd; [| apply bm_bytes_length].
  apply view_sized_dinode; [apply view_sized_dinode; [exact Hsz |] |];
    [apply di_set_nlink_wf, di_set_size_wf, fs_dinode_wf
     | apply di_create_dir_wf].
Qed.

Lemma eff_create_dir_entry_fold (A L : Z -> list (bv 8)) (sb : fs_sb)
    (pend : gset fsobj) (d : Z) (k : nat) (name : fname) (i fb : Z) :
  fs_sb_ok sb -> views_agree_off A L sb pend ->
  0 <= d < sb_ninodes sb -> 0 <= i < sb_ninodes sb ->
  fs_data_start sb <= fb < sb_size sb ->
  off_meta sb (fs_blk_addr A (fs_dinode A sb d) (k / 64)%nat) ->
  fs_blk_addr A (fs_dinode A sb d) (k / 64)%nat <> fb ->
  (forall b : Z,
     b = IBLOCK (fs_inum_bv d) (sb_inodestart sb)
     \/ b = IBLOCK (fs_inum_bv i) (sb_inodestart sb)
     \/ b = sb_bmapstart sb \/ b = fb
     \/ b = fs_blk_addr A (fs_dinode A sb d) (k / 64)%nat ->
     eff_create_dir_entry A sb d k name i fb b = L b) ->
  views_agree_off (eff_create_dir_entry A sb d k name i fb) L sb
    (pend ∖ foot_create_dir_entry A sb d k i fb).
Proof.
  intros Hok Hag Hd Hi Hfb Ha Hafb Hbl.
  apply (views_agree_fold A _ L sb pend (foot_create_dir_entry A sb d k i fb)).
  - exact Hag.
  - exact (eff_create_dir_entry_frame A sb d k name i fb Hok
             (vao_szA _ _ _ _ Hag) Hd Hi Hfb Ha Hafb).
  - exact (eff_create_dir_entry_sized A sb d k name i fb
             (vao_szA _ _ _ _ Hag)).
  - intros b Hb. apply elem_of_map in Hb as (o & -> & Ho).
    unfold foot_create_dir_entry, dirent_obj in Ho.
    apply elem_of_union in Ho as [Ho | Ho];
      [apply elem_of_union in Ho as [Ho | Ho] | ];
      [apply elem_of_union in Ho as [Ho | Ho] | | ];
      [apply elem_of_union in Ho as [Ho | Ho] | | | ];
      apply elem_of_singleton in Ho as ->; cbn [obj_blk]; apply Hbl; tauto.
Qed.

(* ---- unlink ---------------------------------------------------------- *)
Definition foot_unlink_entry (P : Z -> list (bv 8)) (sb : fs_sb) (d : Z)
    (k : nat) (i : Z) : gset fsobj :=
  {[OSlot d]} ∪ {[OSlot i]} ∪ {[dirent_obj P sb d k]}.

Lemma eff_unlink_entry_frame (P : Z -> list (bv 8)) (sb : fs_sb) (d : Z)
    (k : nat) (i : Z) :
  fs_sb_ok sb -> view_sized P sb ->
  0 <= d < sb_ninodes sb -> 0 <= i < sb_ninodes sb ->
  off_meta sb (fs_blk_addr P (fs_dinode P sb d) (k / 64)%nat) ->
  forall o : fsobj, obj_leaf sb o ->
    ~ obj_masked (foot_unlink_entry P sb d k i) sb o ->
    obj_agree (eff_unlink_entry P sb d k i) P sb o.
Proof.
  intros Hok Hsz Hd Hi Ha.
  assert (Hdb := obj_slot_blk_of sb d Hok (inum_obj_range sb d Hok Hd)).
  assert (Hib := obj_slot_blk_of sb i Hok (inum_obj_range sb i Hok Hi)).
  unfold eff_unlink_entry, foot_unlink_entry, dirent_obj.
  (* the parent's record moves only on the directory arm; the [decide] is
     framed uniformly by taking [OSlot d] into the footprint either way *)
  apply (step_splice _ _ sb _ _ _ (k `mod` 64)%nat (16 * (k `mod` 64))%nat
           16%nat);
    [exact Hok | exact Ha | | | lia | lia |].
  - apply view_sized_dinode;
      [destruct (decide (bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z));
        [apply view_sized_dinode; [exact Hsz |] | exact Hsz] |];
      [apply di_set_nlink_wf, fs_dinode_wf | apply di_set_nlink_wf, fs_dinode_wf].
  - rewrite (eff_dinode_out sb _ i _ _);
      [| exact (not_eq_sym (off_meta_ne_slot sb _ _ Hok Ha Hib))].
    destruct (decide (bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z));
      [| reflexivity].
    rewrite (eff_dinode_out sb P d _ _); [reflexivity |].
    exact (not_eq_sym (off_meta_ne_slot sb _ _ Hok Ha Hdb)).
  - apply (step_dinode P _ sb {[OSlot d]});
      [exact Hok | apply di_set_nlink_wf, fs_dinode_wf
       | exact (inum_obj_range sb i Hok Hi) |].
    destruct (decide (bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z)).
    + apply frame_dinode;
        [exact Hok | apply di_set_nlink_wf, fs_dinode_wf
         | exact (inum_obj_range sb d Hok Hd)].
    + intros o Ho Hm. apply obj_agree_refl.
Qed.

Lemma eff_unlink_entry_sized (P : Z -> list (bv 8)) (sb : fs_sb) (d : Z)
    (k : nat) (i : Z) :
  view_sized P sb -> view_sized (eff_unlink_entry P sb d k i) sb.
Proof.
  intros Hsz. unfold eff_unlink_entry.
  apply view_sized_upd; [| apply fs_splice_len].
  apply view_sized_dinode;
    [destruct (decide (bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z));
      [apply view_sized_dinode; [exact Hsz |] | exact Hsz] |];
    [apply di_set_nlink_wf, fs_dinode_wf | apply di_set_nlink_wf, fs_dinode_wf].
Qed.

Lemma eff_unlink_entry_fold (A L : Z -> list (bv 8)) (sb : fs_sb)
    (pend : gset fsobj) (d : Z) (k : nat) (i : Z) :
  fs_sb_ok sb -> views_agree_off A L sb pend ->
  0 <= d < sb_ninodes sb -> 0 <= i < sb_ninodes sb ->
  off_meta sb (fs_blk_addr A (fs_dinode A sb d) (k / 64)%nat) ->
  eff_unlink_entry A sb d k i (IBLOCK (fs_inum_bv d) (sb_inodestart sb))
    = L (IBLOCK (fs_inum_bv d) (sb_inodestart sb)) ->
  eff_unlink_entry A sb d k i (IBLOCK (fs_inum_bv i) (sb_inodestart sb))
    = L (IBLOCK (fs_inum_bv i) (sb_inodestart sb)) ->
  eff_unlink_entry A sb d k i (fs_blk_addr A (fs_dinode A sb d) (k / 64)%nat)
    = L (fs_blk_addr A (fs_dinode A sb d) (k / 64)%nat) ->
  views_agree_off (eff_unlink_entry A sb d k i) L sb
    (pend ∖ foot_unlink_entry A sb d k i).
Proof.
  intros Hok Hag Hd Hi Ha HbD HbI HbA.
  apply (views_agree_fold A _ L sb pend (foot_unlink_entry A sb d k i)).
  - exact Hag.
  - exact (eff_unlink_entry_frame A sb d k i Hok
             (vao_szA _ _ _ _ Hag) Hd Hi Ha).
  - exact (eff_unlink_entry_sized A sb d k i (vao_szA _ _ _ _ Hag)).
  - intros b Hb. apply elem_of_map in Hb as (o & -> & Ho).
    unfold foot_unlink_entry, dirent_obj in Ho.
    apply elem_of_union in Ho as [Ho | Ho];
      [apply elem_of_union in Ho as [Ho | Ho] |];
      apply elem_of_singleton in Ho as ->; cbn [obj_blk].
    + exact HbD.
    + exact HbI.
    + exact HbA.
Qed.

(* ====================================================================== *)
(*  3.  THE FILE EFFECTS (write / alloc / alloc-ind)                       *)
(* ====================================================================== *)

Definition foot_write_file_data (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (fbn : nat) : gset fsobj :=
  {[OSlot i]} ∪ {[OBlk (fs_blk_addr P (fs_dinode P sb i) fbn)]}.

Lemma eff_write_file_data_frame (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (fbn : nat) (bs : list (bv 8)) (sz' : Z) :
  fs_sb_ok sb -> 0 <= i < sb_ninodes sb ->
  off_meta sb (fs_blk_addr P (fs_dinode P sb i) fbn) ->
  forall o : fsobj, obj_leaf sb o ->
    ~ obj_masked (foot_write_file_data P sb i fbn) sb o ->
    obj_agree (eff_write_file_data P sb i fbn bs sz') P sb o.
Proof.
  intros Hok Hi Ha.
  unfold eff_write_file_data, foot_write_file_data.
  apply (step_whole P _ sb {[OSlot i]}); [exact Hok | exact Ha |].
  apply frame_dinode;
    [exact Hok | apply di_set_size_wf, fs_dinode_wf
     | exact (inum_obj_range sb i Hok Hi)].
Qed.

Lemma eff_write_file_data_sized (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (fbn : nat) (bs : list (bv 8)) (sz' : Z) :
  view_sized P sb -> length bs = BSIZE ->
  view_sized (eff_write_file_data P sb i fbn bs sz') sb.
Proof.
  intros Hsz Hbs. unfold eff_write_file_data.
  apply view_sized_upd; [| exact Hbs].
  apply view_sized_dinode; [exact Hsz | apply di_set_size_wf, fs_dinode_wf].
Qed.

Lemma eff_write_file_data_fold (A L : Z -> list (bv 8)) (sb : fs_sb)
    (pend : gset fsobj) (i : Z) (fbn : nat) (bs : list (bv 8)) (sz' : Z) :
  fs_sb_ok sb -> views_agree_off A L sb pend -> 0 <= i < sb_ninodes sb ->
  length bs = BSIZE ->
  off_meta sb (fs_blk_addr A (fs_dinode A sb i) fbn) ->
  eff_write_file_data A sb i fbn bs sz'
    (IBLOCK (fs_inum_bv i) (sb_inodestart sb))
    = L (IBLOCK (fs_inum_bv i) (sb_inodestart sb)) ->
  eff_write_file_data A sb i fbn bs sz'
    (fs_blk_addr A (fs_dinode A sb i) fbn)
    = L (fs_blk_addr A (fs_dinode A sb i) fbn) ->
  views_agree_off (eff_write_file_data A sb i fbn bs sz') L sb
    (pend ∖ foot_write_file_data A sb i fbn).
Proof.
  intros Hok Hag Hi Hbs Ha HbI HbA.
  apply (views_agree_fold A _ L sb pend (foot_write_file_data A sb i fbn)).
  - exact Hag.
  - exact (eff_write_file_data_frame A sb i fbn bs sz' Hok Hi Ha).
  - exact (eff_write_file_data_sized A sb i fbn bs sz'
             (vao_szA _ _ _ _ Hag) Hbs).
  - intros b Hb. apply elem_of_map in Hb as (o & -> & Ho).
    unfold foot_write_file_data in Ho.
    apply elem_of_union in Ho as [Ho | Ho];
      apply elem_of_singleton in Ho as ->; cbn [obj_blk].
    + exact HbI.
    + exact HbA.
Qed.

(* ---- balloc's install ------------------------------------------------ *)

(* the indirect entry's record, when the slot is an indirect one *)
Definition foot_alloc_file_block (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (fbn : nat) (fresh : Z) : gset fsobj :=
  ({[OSlot i]}
   ∪ (if (fbn <? 12)%nat then ∅
      else {[ORec (bv_unsigned (di_addrs (fs_dinode P sb i) !!! 12%nat))
               ((fbn - 12) / 4)%nat]}))
  ∪ {[OBit fresh]} ∪ {[OBlk fresh]}.

Lemma eff_alloc_file_block_frame (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (fbn : nat) (fresh : Z) :
  fs_sb_ok sb -> view_sized P sb -> 0 <= i < sb_ninodes sb ->
  (fbn < FS_MAXFILE)%nat ->
  fs_data_start sb <= fresh < sb_size sb ->
  off_meta sb (bv_unsigned (di_addrs (fs_dinode P sb i) !!! 12%nat)) ->
  forall o : fsobj, obj_leaf sb o ->
    ~ obj_masked (foot_alloc_file_block P sb i fbn fresh) sb o ->
    obj_agree (eff_alloc_file_block P sb i fbn fresh) P sb o.
Proof.
  intros Hok Hsz Hi Hfbn Hfr Hind.
  assert (Hfrm : off_meta sb fresh) by (unfold off_meta; lia).
  assert (Hib := obj_slot_blk_of sb i Hok (inum_obj_range sb i Hok Hi)).
  pose proof (Nat.div_mod_eq (fbn - 12) 4) as Hdm.
  pose proof (Nat.mod_upper_bound (fbn - 12) 4 ltac:(lia)) as Hmb.
  unfold eff_alloc_file_block, foot_alloc_file_block.
  apply (step_whole P _ sb _ fresh); [exact Hok | exact Hfrm |].
  apply (step_bmap P _ sb _ {[OBit fresh]}); [exact Hok | | ].
  - (* the base does not touch the bitmap block *)
    destruct (Nat.ltb_spec fbn 12) as [Hlt | Hge].
    + rewrite (eff_dinode_out sb P i _ _);
        [| exact (not_eq_sym (obj_slot_blk_ne_bmap sb _ Hib))].
      apply bmap_cond_add. intros x Hx Hc.
      apply elem_of_singleton in Hc as ->. apply Hx, elem_of_singleton.
      reflexivity.
    + rewrite (fs_upd_ne _ _ (sb_bmapstart sb)),
        (eff_dinode_out sb P i _ _);
        [| exact (not_eq_sym (obj_slot_blk_ne_bmap sb _ Hib))
         | exact (off_meta_ne_bmap sb _ Hok Hind)].
      apply bmap_cond_add. intros x Hx Hc.
      apply elem_of_singleton in Hc as ->. apply Hx, elem_of_singleton.
      reflexivity.
  - (* the base: either the record alone, or the record plus the entry *)
    destruct (Nat.ltb_spec fbn 12) as [Hlt | Hge].
    + rewrite union_empty_r_L.
      apply frame_dinode;
        [exact Hok | apply di_set_size_addr_wf, fs_dinode_wf
         | exact (inum_obj_range sb i Hok Hi)].
    + apply (step_splice P _ sb {[OSlot i]} _ _ ((fbn - 12) / 4)%nat
               (4 * (fbn - 12))%nat 4%nat);
        [exact Hok | exact Hind | | | lia | lia |].
      * apply view_sized_dinode; [exact Hsz | apply fs_dinode_wf].
      * exact (eq_sym (eff_dinode_out sb P i _ _
                 (not_eq_sym (off_meta_ne_slot sb _ _ Hok Hind Hib)))).
      * apply frame_dinode;
          [exact Hok | apply fs_dinode_wf
           | exact (inum_obj_range sb i Hok Hi)].
Qed.

Lemma eff_alloc_file_block_sized (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (fbn : nat) (fresh : Z) :
  view_sized P sb -> view_sized (eff_alloc_file_block P sb i fbn fresh) sb.
Proof.
  intros Hsz. unfold eff_alloc_file_block.
  apply view_sized_upd; [| apply length_replicate].
  apply view_sized_upd; [| apply bm_bytes_length].
  destruct (Nat.ltb_spec fbn 12) as [Hlt | Hge].
  - apply view_sized_dinode;
      [exact Hsz | apply di_set_size_addr_wf, fs_dinode_wf].
  - apply view_sized_upd; [| apply fs_splice_len].
    apply view_sized_dinode; [exact Hsz | apply fs_dinode_wf].
Qed.

Lemma eff_alloc_file_block_fold (A L : Z -> list (bv 8)) (sb : fs_sb)
    (pend : gset fsobj) (i : Z) (fbn : nat) (fresh : Z) :
  fs_sb_ok sb -> views_agree_off A L sb pend -> 0 <= i < sb_ninodes sb ->
  (fbn < FS_MAXFILE)%nat ->
  fs_data_start sb <= fresh < sb_size sb ->
  off_meta sb (bv_unsigned (di_addrs (fs_dinode A sb i) !!! 12%nat)) ->
  (forall b : Z,
     b = IBLOCK (fs_inum_bv i) (sb_inodestart sb)
     \/ b = bv_unsigned (di_addrs (fs_dinode A sb i) !!! 12%nat)
     \/ b = sb_bmapstart sb \/ b = fresh ->
     eff_alloc_file_block A sb i fbn fresh b = L b) ->
  views_agree_off (eff_alloc_file_block A sb i fbn fresh) L sb
    (pend ∖ foot_alloc_file_block A sb i fbn fresh).
Proof.
  intros Hok Hag Hi Hfbn Hfr Hind Hbl.
  apply (views_agree_fold A _ L sb pend
           (foot_alloc_file_block A sb i fbn fresh)).
  - exact Hag.
  - exact (eff_alloc_file_block_frame A sb i fbn fresh Hok
             (vao_szA _ _ _ _ Hag) Hi Hfbn Hfr Hind).
  - exact (eff_alloc_file_block_sized A sb i fbn fresh (vao_szA _ _ _ _ Hag)).
  - intros b Hb. apply elem_of_map in Hb as (o & -> & Ho).
    unfold foot_alloc_file_block in Ho.
    apply elem_of_union in Ho as [Ho | Ho];
      [apply elem_of_union in Ho as [Ho | Ho] | ];
      [| apply elem_of_singleton in Ho as ->; cbn [obj_blk]; apply Hbl; tauto
       | apply elem_of_singleton in Ho as ->; cbn [obj_blk]; apply Hbl; tauto].
    apply elem_of_union in Ho as [Ho | Ho].
    + apply elem_of_singleton in Ho as ->. cbn [obj_blk]. apply Hbl. tauto.
    + destruct (fbn <? 12)%nat;
        [ by apply (not_elem_of_empty (C := gset fsobj)) in Ho |].
      apply elem_of_singleton in Ho as ->. cbn [obj_blk]. apply Hbl. tauto.
Qed.

(* ---- the NDIRECT crossing -------------------------------------------- *)
Definition foot_alloc_ind_block (i : Z) (fresh_ind : Z) : gset fsobj :=
  {[OSlot i]} ∪ {[OBit fresh_ind]} ∪ {[OBlk fresh_ind]}.

Lemma eff_alloc_ind_block_frame (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (fresh_ind : Z) :
  fs_sb_ok sb -> 0 <= i < sb_ninodes sb ->
  fs_data_start sb <= fresh_ind < sb_size sb ->
  forall o : fsobj, obj_leaf sb o ->
    ~ obj_masked (foot_alloc_ind_block i fresh_ind) sb o ->
    obj_agree (eff_alloc_ind_block P sb i fresh_ind) P sb o.
Proof.
  intros Hok Hi Hfr.
  assert (Hfrm : off_meta sb fresh_ind) by (unfold off_meta; lia).
  assert (Hib := obj_slot_blk_of sb i Hok (inum_obj_range sb i Hok Hi)).
  unfold eff_alloc_ind_block, foot_alloc_ind_block.
  apply (step_whole P _ sb _ fresh_ind); [exact Hok | exact Hfrm |].
  apply (step_bmap P _ sb {[OSlot i]} {[OBit fresh_ind]}); [exact Hok | |].
  - rewrite (eff_dinode_out sb P i _ _);
      [| exact (not_eq_sym (obj_slot_blk_ne_bmap sb _ Hib))].
    apply bmap_cond_add. intros x Hx Hc.
    apply elem_of_singleton in Hc as ->. apply Hx, elem_of_singleton.
    reflexivity.
  - apply frame_dinode;
      [exact Hok | apply di_set_size_addr_wf, fs_dinode_wf
       | exact (inum_obj_range sb i Hok Hi)].
Qed.

Lemma eff_alloc_ind_block_sized (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (fresh_ind : Z) :
  view_sized P sb -> view_sized (eff_alloc_ind_block P sb i fresh_ind) sb.
Proof.
  intros Hsz. unfold eff_alloc_ind_block.
  apply view_sized_upd;
    [| apply ind_bytes_length_256, length_replicate].
  apply view_sized_upd; [| apply bm_bytes_length].
  apply view_sized_dinode;
    [exact Hsz | apply di_set_size_addr_wf, fs_dinode_wf].
Qed.

Lemma eff_alloc_ind_block_fold (A L : Z -> list (bv 8)) (sb : fs_sb)
    (pend : gset fsobj) (i : Z) (fresh_ind : Z) :
  fs_sb_ok sb -> views_agree_off A L sb pend -> 0 <= i < sb_ninodes sb ->
  fs_data_start sb <= fresh_ind < sb_size sb ->
  (forall b : Z,
     b = IBLOCK (fs_inum_bv i) (sb_inodestart sb)
     \/ b = sb_bmapstart sb \/ b = fresh_ind ->
     eff_alloc_ind_block A sb i fresh_ind b = L b) ->
  views_agree_off (eff_alloc_ind_block A sb i fresh_ind) L sb
    (pend ∖ foot_alloc_ind_block i fresh_ind).
Proof.
  intros Hok Hag Hi Hfr Hbl.
  apply (views_agree_fold A _ L sb pend (foot_alloc_ind_block i fresh_ind)).
  - exact Hag.
  - exact (eff_alloc_ind_block_frame A sb i fresh_ind Hok Hi Hfr).
  - exact (eff_alloc_ind_block_sized A sb i fresh_ind (vao_szA _ _ _ _ Hag)).
  - intros b Hb. apply elem_of_map in Hb as (o & -> & Ho).
    unfold foot_alloc_ind_block in Ho.
    apply elem_of_union in Ho as [Ho | Ho];
      [apply elem_of_union in Ho as [Ho | Ho] |];
      apply elem_of_singleton in Ho as ->; cbn [obj_blk]; apply Hbl; tauto.
Qed.

(* ====================================================================== *)
(*  4.  THE FREEING EFFECTS (trunc / free-inode / free-slot)               *)
(* ====================================================================== *)

(* one bit object per freed block *)
Definition bit_objs (l : list Z) : gset fsobj := list_to_set (OBit <$> l).

Lemma bit_objs_not_in (l : list Z) (x : Z) :
  OBit x ∉ bit_objs l -> x ∉ list_to_set (C := gset Z) l.
Proof.
  intros H Hc. apply H. unfold bit_objs.
  apply elem_of_list_to_set, elem_of_list_fmap.
  exists x. split; [reflexivity |].
  by apply elem_of_list_to_set in Hc.
Qed.

Definition foot_trunc (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
  : gset fsobj :=
  {[OSlot i]} ∪ bit_objs (fs_inode_ents P (fs_dinode P sb i)).

Lemma eff_trunc_frame (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_sb_ok sb -> 0 <= i < sb_ninodes sb ->
  forall o : fsobj, obj_leaf sb o -> ~ obj_masked (foot_trunc P sb i) sb o ->
    obj_agree (eff_trunc P sb i) P sb o.
Proof.
  intros Hok Hi.
  assert (Hib := obj_slot_blk_of sb i Hok (inum_obj_range sb i Hok Hi)).
  unfold eff_trunc, foot_trunc.
  apply (step_bmap P _ sb {[OSlot i]} (bit_objs _)); [exact Hok | |].
  - rewrite (eff_dinode_out sb P i _ _);
      [| exact (not_eq_sym (obj_slot_blk_ne_bmap sb _ Hib))].
    apply bmap_cond_del. intros x Hx. exact (bit_objs_not_in _ x Hx).
  - apply frame_dinode;
      [exact Hok | apply di_trunc_v_wf | exact (inum_obj_range sb i Hok Hi)].
Qed.

Lemma eff_trunc_sized (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  view_sized P sb -> view_sized (eff_trunc P sb i) sb.
Proof.
  intros Hsz. unfold eff_trunc.
  apply view_sized_upd; [| apply bm_bytes_length].
  apply view_sized_dinode; [exact Hsz | apply di_trunc_v_wf].
Qed.

Lemma eff_trunc_fold (A L : Z -> list (bv 8)) (sb : fs_sb)
    (pend : gset fsobj) (i : Z) :
  fs_sb_ok sb -> views_agree_off A L sb pend -> 0 <= i < sb_ninodes sb ->
  eff_trunc A sb i (IBLOCK (fs_inum_bv i) (sb_inodestart sb))
    = L (IBLOCK (fs_inum_bv i) (sb_inodestart sb)) ->
  eff_trunc A sb i (sb_bmapstart sb) = L (sb_bmapstart sb) ->
  views_agree_off (eff_trunc A sb i) L sb (pend ∖ foot_trunc A sb i).
Proof.
  intros Hok Hag Hi HbI Hbm.
  apply (views_agree_fold A _ L sb pend (foot_trunc A sb i)).
  - exact Hag.
  - exact (eff_trunc_frame A sb i Hok Hi).
  - exact (eff_trunc_sized A sb i (vao_szA _ _ _ _ Hag)).
  - intros b Hb. apply elem_of_map in Hb as (o & -> & Ho).
    unfold foot_trunc, bit_objs in Ho.
    apply elem_of_union in Ho as [Ho | Ho].
    + apply elem_of_singleton in Ho as ->. cbn [obj_blk]. exact HbI.
    + apply elem_of_list_to_set, elem_of_list_fmap in Ho as (x & -> & _).
      cbn [obj_blk]. exact Hbm.
Qed.

Definition foot_free_inode (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
  : gset fsobj :=
  {[OSlot i]} ∪ bit_objs (fs_inode_ents P (fs_dinode P sb i)).

Lemma eff_free_inode_frame (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_sb_ok sb -> 0 <= i < sb_ninodes sb ->
  forall o : fsobj, obj_leaf sb o ->
    ~ obj_masked (foot_free_inode P sb i) sb o ->
    obj_agree (eff_free_inode P sb i) P sb o.
Proof.
  intros Hok Hi.
  assert (Hib := obj_slot_blk_of sb i Hok (inum_obj_range sb i Hok Hi)).
  unfold eff_free_inode, foot_free_inode.
  apply (step_bmap P _ sb {[OSlot i]} (bit_objs _)); [exact Hok | |].
  - rewrite (eff_dinode_out sb P i _ _);
      [| exact (not_eq_sym (obj_slot_blk_ne_bmap sb _ Hib))].
    apply bmap_cond_del. intros x Hx. exact (bit_objs_not_in _ x Hx).
  - apply frame_dinode;
      [exact Hok | apply di_free_v_wf | exact (inum_obj_range sb i Hok Hi)].
Qed.

Lemma eff_free_inode_sized (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  view_sized P sb -> view_sized (eff_free_inode P sb i) sb.
Proof.
  intros Hsz. unfold eff_free_inode.
  apply view_sized_upd; [| apply bm_bytes_length].
  apply view_sized_dinode; [exact Hsz | apply di_free_v_wf].
Qed.

Lemma eff_free_inode_fold (A L : Z -> list (bv 8)) (sb : fs_sb)
    (pend : gset fsobj) (i : Z) :
  fs_sb_ok sb -> views_agree_off A L sb pend -> 0 <= i < sb_ninodes sb ->
  eff_free_inode A sb i (IBLOCK (fs_inum_bv i) (sb_inodestart sb))
    = L (IBLOCK (fs_inum_bv i) (sb_inodestart sb)) ->
  eff_free_inode A sb i (sb_bmapstart sb) = L (sb_bmapstart sb) ->
  views_agree_off (eff_free_inode A sb i) L sb
    (pend ∖ foot_free_inode A sb i).
Proof.
  intros Hok Hag Hi HbI Hbm.
  apply (views_agree_fold A _ L sb pend (foot_free_inode A sb i)).
  - exact Hag.
  - exact (eff_free_inode_frame A sb i Hok Hi).
  - exact (eff_free_inode_sized A sb i (vao_szA _ _ _ _ Hag)).
  - intros b Hb. apply elem_of_map in Hb as (o & -> & Ho).
    unfold foot_free_inode, bit_objs in Ho.
    apply elem_of_union in Ho as [Ho | Ho].
    + apply elem_of_singleton in Ho as ->. cbn [obj_blk]. exact HbI.
    + apply elem_of_list_to_set, elem_of_list_fmap in Ho as (x & -> & _).
      cbn [obj_blk]. exact Hbm.
Qed.

(* the record-only free (ireclaim's second half) *)
Definition foot_free_slot (i : Z) : gset fsobj := {[OSlot i]}.

Lemma eff_free_slot_frame (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_sb_ok sb -> 0 <= i < sb_ninodes sb ->
  forall o : fsobj, obj_leaf sb o -> ~ obj_masked (foot_free_slot i) sb o ->
    obj_agree (eff_free_slot P sb i) P sb o.
Proof.
  intros Hok Hi. unfold eff_free_slot, foot_free_slot.
  apply frame_dinode;
    [exact Hok | apply di_free_v_wf | exact (inum_obj_range sb i Hok Hi)].
Qed.

Lemma eff_free_slot_sized (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  view_sized P sb -> view_sized (eff_free_slot P sb i) sb.
Proof.
  intros Hsz. unfold eff_free_slot.
  apply view_sized_dinode; [exact Hsz | apply di_free_v_wf].
Qed.

Lemma eff_free_slot_fold (A L : Z -> list (bv 8)) (sb : fs_sb)
    (pend : gset fsobj) (i : Z) :
  fs_sb_ok sb -> views_agree_off A L sb pend -> 0 <= i < sb_ninodes sb ->
  eff_free_slot A sb i (IBLOCK (fs_inum_bv i) (sb_inodestart sb))
    = L (IBLOCK (fs_inum_bv i) (sb_inodestart sb)) ->
  views_agree_off (eff_free_slot A sb i) L sb (pend ∖ foot_free_slot i).
Proof.
  intros Hok Hag Hi HbI.
  apply (views_agree_fold A _ L sb pend (foot_free_slot i)).
  - exact Hag.
  - exact (eff_free_slot_frame A sb i Hok Hi).
  - exact (eff_free_slot_sized A sb i (vao_szA _ _ _ _ Hag)).
  - intros b Hb. apply elem_of_map in Hb as (o & -> & Ho).
    unfold foot_free_slot in Ho.
    apply elem_of_singleton in Ho as ->. cbn [obj_blk]. exact HbI.
Qed.
