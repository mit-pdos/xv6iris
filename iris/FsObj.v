(* ====================================================================== *)
(* FsObj.v -- durable-disk, THE FLIP'S OBJECT LAYER (stage flip-A, pure).  *)
(*                                                                         *)
(* Row (a) of the log invariant is restated OBJECT-WISE: between begin_op   *)
(* and end_op the committed view [A] and the logged view [L] may differ     *)
(* only at the OBJECTS some open transaction has claimed.  This file is     *)
(* the pure half: the object type, the agreement relation, its tiling       *)
(* completeness theorem, and the generic FOLD an ending op's arm invokes.   *)
(* No Iris; it sits on [FsWf] only.  The per-effect object footprints are   *)
(* [FsObjEff.v] (they need the [FsEff*] band).                              *)
(*                                                                         *)
(* ---------------------------------------------------------------------- *)
(* THE FOUR ADDRESSING DECISIONS (and why), since every consumer inherits   *)
(* them:                                                                   *)
(*                                                                         *)
(* (1) [ORec b k] IS ADDRESSED BY BLOCK, NOT BY (dir inum, record index).   *)
(*     The design-of-record left the choice open; the block spelling wins   *)
(*     on all three counts.  (a) TILING: a record is then the byte window   *)
(*     [16k, 16k+16) of block [b] and the tiling lemma is arithmetic --     *)
(*     no premise about who owns [b], no uniqueness-of-owner obligation.    *)
(*     (b) STABILITY: an inum-addressed record's home block is derived      *)
(*     through the owner's block map, which MOVES inside a transaction      *)
(*     group (itrunc frees a dir's blocks; balloc can hand the same block   *)
(*     to another inode in the same group), so [ORec d k] would silently    *)
(*     rename itself to a window of somebody else's file.  A block-         *)
(*     addressed object never moves.  (c) THE OP ALREADY HOLDS IT: what an  *)
(*     op logs is a BLOCK ([log_write]'s footprint), and the arm's ledger   *)
(*     entry is a set of blocks; the record index inside the block is       *)
(*     [k mod 64], which the effect definitions already compute.            *)
(*     COST: the dir-view ghost [dv] is indexed by (dir, record), so        *)
(*     flip-C's wiring owes the dv-to-block bridge -- the `dv-to-decode     *)
(*     bridge lemma` the design already budgets.                            *)
(*                                                                         *)
(* (2) THE BLOCK'S DECOMPOSITION IS GEOMETRIC, NOT ROLE-DEPENDENT.  The     *)
(*     design worried about `a data block's role as dir-content depends on  *)
(*     the OWNING inode's type -- does the role come from [A] or [L]?`.     *)
(*     That question is DISSOLVED here: [sb_inodestart, sb_bmapstart) is    *)
(*     tiled by dinode SLOTS, [sb_bmapstart] by BITS, and EVERY other home  *)
(*     block (the superblock and the whole data region alike) by 16-byte    *)
(*     RECORDS.  A file data block is record-tiled too -- the records are   *)
(*     just byte windows, and 64 of them tile the block exactly, so         *)
(*     nothing is lost and no role has to agree between the views.  A       *)
(*     whole-block write is not a fifth scheme: it is [OBlk b], which       *)
(*     MASKS every leaf of [b] (see (4)).                                   *)
(*                                                                         *)
(* (3) EACH LEAF'S AGREEMENT IS AT THE GRANULARITY ITS WRITERS USE, and     *)
(*     the three differ on purpose: a RECORD agrees BYTE-WISE (the dirent   *)
(*     decode is lossy -- the bytes past a name's NUL are junk -- and a     *)
(*     file data block is arbitrary bytes, so a decode-level record clause  *)
(*     could never tile); a SLOT agrees at the DECODE ([fs_dinode]),        *)
(*     because [eff_dinode] rewrites the whole inode block by re-encoding   *)
(*     its sixteen decoded records, so its frame is decode-level and        *)
(*     byte-level framing would carry a canonicity premise at every site;   *)
(*     a BIT agrees at [fs_bit], since eight of them share a byte.  The     *)
(*     RESIDUE that makes this byte-complete is the size clause: every      *)
(*     home block of either view is [BSIZE] bytes (true of every disk       *)
(*     block, preserved by every effect), which is what turns 64 windows /  *)
(*     16 decodes / 8192 bits back into list equality.  With it the         *)
(*     decompositions need no trailing-junk clause at all.                  *)
(*                                                                         *)
(* (4) [OBlk b] IS A COARSE OBJECT, NOT A LEAF.  It carries no agreement    *)
(*     clause of its own ([obj_leaf] is false at it); what it does is MASK  *)
(*     the leaves of [b] while it is pending, so a whole-block write        *)
(*     claims ONE object instead of sixty-four.  Its agreement spelling     *)
(*     [obj_agree A L sb (OBlk b) = (A b = L b)] is still what an arm       *)
(*     proves at the fold.                                                  *)
(* ====================================================================== *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import RiscvModelBytes.  (* [nth_byte_assemble_len] *)
Require Import BioDefs.          (* [BSIZE] *)
Require Import BlockWords.       (* [ind_bytes] and its lookups *)
Require Import DirentEnc.
Require Import DinodeEnc.
Require Import BitmapEnc.
Require Import InodeDefs.        (* [file_byte] *)
Require Import DirView.
Require Import FsTree.
Require Import FsImg.
Require Import FsWf.
Require Export FsObjType.  (* [fsobj] + its [Countable]; see the note below *)

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE OBJECT                                                         *)
(* ====================================================================== *)

(* [fsobj] itself, its [EqDecision] and its [Countable] instance live in
   [FsObjType.v] -- a two-import file below [Xv6Cameras], because the log's
   ledger entry stores a [gset fsobj] and the camera class that holds the
   ledger cannot see this band.  Re-exported above, so importing [FsObj]
   still puts the constructors in scope. *)

(* ====================================================================== *)
(*  2.  GEOMETRY: WHICH BLOCKS EXIST, AND WHICH SCHEME TILES THEM          *)
(* ====================================================================== *)

(* records per block *)
Definition FS_NREC : nat := 64%nat.

(* THE HOME EXTENT, in [FsWf]'s own spelling: exactly the footprint
   [fs_durable_wf_view_ext] reads (block 1 and [inodestart, size)), which
   for the geometry [fs_sb_wf] pins is [fs_home_set cov logstart] whenever
   [cov] covers [1, size). *)
Definition fs_obj_home (sb : fs_sb) (b : Z) : Prop :=
  b = SB_BNO \/ sb_inodestart sb <= b < sb_size sb.

(* the three tiling schemes, by block *)
Definition obj_rec_blk (sb : fs_sb) (b : Z) : Prop :=
  b = SB_BNO \/ fs_data_start sb <= b < sb_size sb.
Definition obj_slot_blk (sb : fs_sb) (b : Z) : Prop :=
  sb_inodestart sb <= b < sb_bmapstart sb.

(* the block an object lives in *)
Definition obj_blk (sb : fs_sb) (o : fsobj) : Z :=
  match o with
  | ORec b _ => b
  | OBit _ => sb_bmapstart sb
  | OSlot i => IBLOCK (fs_inum_bv i) (sb_inodestart sb)
  | OBlk b => b
  end.

(* THE LEAVES: the objects that tile the home extent.  [OBlk] is not one
   (header, decision (4)). *)
Definition obj_leaf (sb : fs_sb) (o : fsobj) : Prop :=
  match o with
  | ORec b k => obj_rec_blk sb b /\ (k < FS_NREC)%nat
  | OBit b => 0 <= b < 8 * BSIZE_z
  | OSlot i => 0 <= i < 16 * (sb_bmapstart sb - sb_inodestart sb)
  | OBlk _ => False
  end.

(* `this block is neither an inode block nor the bitmap block` -- the side
   condition a write to a DATA block owes, since a data-block address is
   read out of a decoded record and only the invariant bounds it. *)
Definition off_meta (sb : fs_sb) (a : Z) : Prop :=
  a < sb_inodestart sb \/ fs_data_start sb <= a.

(* THE GEOMETRY BUNDLE this file runs on, once: the inode region is a
   nonempty range strictly above the superblock, the bitmap is the one
   block below the data region, and the region's inum range fits a
   [bv 32] (so [fs_inum_bv] is exact on it). *)
Lemma obj_geom (sb : fs_sb) :
  fs_sb_ok sb ->
  2 < sb_inodestart sb
  /\ sb_inodestart sb < sb_bmapstart sb
  /\ fs_data_start sb = sb_bmapstart sb + 1
  /\ fs_data_start sb <= sb_size sb
  /\ 16 * (sb_bmapstart sb - sb_inodestart sb) < bv_modulus 32.
Proof.
  intros Hok.
  destruct (fs_sb_ok_meta sb Hok) as (Hm1 & Hm2 & Hm3).
  destruct (fs_sb_ok_geom sb Hok) as (_ & _ & _ & _ & _ & H6).
  pose proof (sbo_bmapstart sb Hok) as Hbm.
  pose proof (sbo_ninodes sb Hok) as Hn. unfold ROOTINO in Hn.
  assert (Hd : 0 <= sb_ninodes sb / 16) by (apply Z.div_pos; lia).
  unfold fs_data_start in *. lia.
Qed.

Ltac obj_geom_of Hok :=
  let H1 := fresh "Hg1" in let H2 := fresh "Hg2" in
  let H3 := fresh "Hg3" in let H4 := fresh "Hg4" in
  let H5 := fresh "Hg5" in
  destruct (obj_geom _ Hok) as (H1 & H2 & H3 & H4 & H5).

(* nat division facts, the way [lia] can use them (zify does not do
   [Nat.div] on its own) *)
Ltac dmf x y :=
  let H1 := fresh "Hdm" in let H2 := fresh "Hmb" in
  pose proof (Nat.div_mod_eq x y) as H1;
  pose proof (Nat.mod_upper_bound x y ltac:(lia)) as H2.

Lemma inum_bv_unsigned (sb : fs_sb) (i : Z) :
  fs_sb_ok sb -> 0 <= i < 16 * (sb_bmapstart sb - sb_inodestart sb) ->
  bv_unsigned (fs_inum_bv i) = i.
Proof.
  intros Hok Hi. obj_geom_of Hok.
  unfold fs_inum_bv. apply Z_to_bv_small. lia.
Qed.

(* an inode-slot object sits in an inode block *)
Lemma obj_slot_blk_of (sb : fs_sb) (i : Z) :
  fs_sb_ok sb -> 0 <= i < 16 * (sb_bmapstart sb - sb_inodestart sb) ->
  obj_slot_blk sb (IBLOCK (fs_inum_bv i) (sb_inodestart sb)).
Proof.
  intros Hok Hi. unfold obj_slot_blk, IBLOCK.
  rewrite (inum_bv_unsigned sb i Hok Hi).
  assert (H0 : 0 <= i / 16) by (apply Z.div_pos; lia).
  assert (H1 : i / 16 < sb_bmapstart sb - sb_inodestart sb)
    by (apply Z.div_lt_upper_bound; lia).
  lia.
Qed.

Lemma obj_slot_blk_home (sb : fs_sb) (b : Z) :
  fs_sb_ok sb -> obj_slot_blk sb b -> fs_obj_home sb b.
Proof.
  intros Hok Hb. obj_geom_of Hok.
  unfold obj_slot_blk in Hb. unfold fs_obj_home. lia.
Qed.

Lemma obj_rec_blk_home (sb : fs_sb) (b : Z) :
  fs_sb_ok sb -> obj_rec_blk sb b -> fs_obj_home sb b.
Proof.
  intros Hok [-> | Hb]; [by left | right]. obj_geom_of Hok. lia.
Qed.

Lemma bmap_home (sb : fs_sb) :
  fs_sb_ok sb -> fs_obj_home sb (sb_bmapstart sb).
Proof. intros Hok. right. obj_geom_of Hok. lia. Qed.

Lemma obj_leaf_home (sb : fs_sb) (o : fsobj) :
  fs_sb_ok sb -> obj_leaf sb o -> fs_obj_home sb (obj_blk sb o).
Proof.
  intros Hok. destruct o as [b k | b | i | b]; cbn [obj_leaf obj_blk].
  - intros [Hb _]. exact (obj_rec_blk_home sb b Hok Hb).
  - intros _. exact (bmap_home sb Hok).
  - intros Hi.
    exact (obj_slot_blk_home sb _ Hok (obj_slot_blk_of sb i Hok Hi)).
  - intros [].
Qed.

(* the three schemes partition the home extent *)
Lemma fs_obj_home_cases (sb : fs_sb) (b : Z) :
  fs_sb_ok sb -> fs_obj_home sb b ->
  obj_rec_blk sb b \/ obj_slot_blk sb b \/ b = sb_bmapstart sb.
Proof.
  intros Hok [-> | Hb]; [left; by left |]. obj_geom_of Hok.
  unfold obj_rec_blk, obj_slot_blk. lia.
Qed.

(* an inode block is neither the superblock, nor the bitmap, nor data *)
Lemma obj_slot_blk_ne_rec (sb : fs_sb) (b c : Z) :
  fs_sb_ok sb -> obj_slot_blk sb b -> obj_rec_blk sb c -> b <> c.
Proof.
  intros Hok Hb [-> | Hc]; obj_geom_of Hok;
    unfold obj_slot_blk, SB_BNO in *; lia.
Qed.

Lemma obj_slot_blk_ne_bmap (sb : fs_sb) (b : Z) :
  obj_slot_blk sb b -> b <> sb_bmapstart sb.
Proof. unfold obj_slot_blk. lia. Qed.

Lemma obj_rec_blk_ne_bmap (sb : fs_sb) (b : Z) :
  fs_sb_ok sb -> obj_rec_blk sb b -> b <> sb_bmapstart sb.
Proof.
  intros Hok [-> | Hb]; obj_geom_of Hok; unfold SB_BNO in *; lia.
Qed.

(* what [off_meta] buys: the written block is no inode block and not the
   bitmap block *)
Lemma off_meta_ne_slot (sb : fs_sb) (a b : Z) :
  fs_sb_ok sb -> off_meta sb a -> obj_slot_blk sb b -> b <> a.
Proof.
  intros Hok Ha Hb. obj_geom_of Hok.
  unfold off_meta, obj_slot_blk in *. lia.
Qed.

Lemma off_meta_ne_bmap (sb : fs_sb) (a : Z) :
  fs_sb_ok sb -> off_meta sb a -> sb_bmapstart sb <> a.
Proof. intros Hok Ha. obj_geom_of Hok. unfold off_meta in *. lia. Qed.

(* the frame side condition, packaged by object kind: a write to a data
   block moves no inode-region and no bitmap object. *)
Lemma obj_blk_off_meta_ne (sb : fs_sb) (o : fsobj) (a : Z) :
  fs_sb_ok sb -> obj_leaf sb o -> off_meta sb a ->
  obj_blk sb o <> a \/ obj_rec_blk sb (obj_blk sb o).
Proof.
  intros Hok Ho Ha.
  destruct o as [b k | b | i | b]; cbn [obj_leaf obj_blk] in *.
  - right. tauto.
  - left. exact (off_meta_ne_bmap sb a Hok Ha).
  - left. exact (off_meta_ne_slot sb a _ Hok Ha (obj_slot_blk_of sb i Hok Ho)).
  - destruct Ho.
Qed.

(* ====================================================================== *)
(*  3.  AGREEMENT AT ONE OBJECT                                            *)
(* ====================================================================== *)

(* record [k]'s bytes of a block *)
Definition rec_bytes (bs : list (bv 8)) (k : nat) : list (bv 8) :=
  take 16 (drop (16 * k) bs).

Definition obj_agree (A L : Z -> list (bv 8)) (sb : fs_sb) (o : fsobj)
  : Prop :=
  match o with
  | ORec b k => rec_bytes (A b) k = rec_bytes (L b) k
  | OBit b => fs_bit (A (sb_bmapstart sb)) b = fs_bit (L (sb_bmapstart sb)) b
  | OSlot i => fs_dinode A sb i = fs_dinode L sb i
  | OBlk b => A b = L b
  end.

Lemma obj_agree_refl (A : Z -> list (bv 8)) (sb : fs_sb) (o : fsobj) :
  obj_agree A A sb o.
Proof. destruct o; reflexivity. Qed.

Lemma obj_agree_sym (A L : Z -> list (bv 8)) (sb : fs_sb) (o : fsobj) :
  obj_agree A L sb o -> obj_agree L A sb o.
Proof. destruct o; cbn; intros H; by symmetry. Qed.

Lemma obj_agree_trans (A B L : Z -> list (bv 8)) (sb : fs_sb) (o : fsobj) :
  obj_agree A B sb o -> obj_agree B L sb o -> obj_agree A L sb o.
Proof. destruct o; cbn; intros H1 H2; by rewrite H1. Qed.

(* THE WORKHORSE: block equality gives agreement at every object of that
   block -- what an arm's [log_write] postcondition hands the fold. *)
Lemma obj_agree_of_blk_eq (A L : Z -> list (bv 8)) (sb : fs_sb) (o : fsobj) :
  A (obj_blk sb o) = L (obj_blk sb o) -> obj_agree A L sb o.
Proof.
  destruct o as [b k | b | i | b]; cbn [obj_blk obj_agree]; intros H.
  - by rewrite H.
  - by rewrite H.
  - by apply fs_dinode_ext.
  - exact H.
Qed.

(* ====================================================================== *)
(*  4.  THE RELATION [A ~[pend] L]                                         *)
(* ====================================================================== *)

(* THE RESIDUE CLAUSE (header, decision (3)): every home block is a full
   block.  Unconditional -- not masked by [pend] -- because it is true of
   the disk and every effect re-lays a [BSIZE]-sized block. *)
Definition view_sized (P : Z -> list (bv 8)) (sb : fs_sb) : Prop :=
  forall b : Z, fs_obj_home sb b -> length (P b) = BSIZE.

(* [o] is covered by the pending set: either claimed outright, or its
   whole block is (header, decision (4)). *)
Definition obj_masked (pend : gset fsobj) (sb : fs_sb) (o : fsobj) : Prop :=
  o ∈ pend \/ OBlk (obj_blk sb o) ∈ pend.

Record views_agree_off (A L : Z -> list (bv 8)) (sb : fs_sb)
    (pend : gset fsobj) : Prop := {
  vao_szA : view_sized A sb;
  vao_szL : view_sized L sb;
  vao_at : forall o : fsobj,
      obj_leaf sb o -> ~ obj_masked pend sb o -> obj_agree A L sb o;
}.

Lemma obj_masked_mono (pend pend' : gset fsobj) (sb : fs_sb) (o : fsobj) :
  pend ⊆ pend' -> obj_masked pend sb o -> obj_masked pend' sb o.
Proof. intros Hsub [H | H]; [left | right]; by apply Hsub. Qed.

(* GROWTH is free -- [log_state_pend_mono]'s content at the object level. *)
Lemma views_agree_off_mono (A L : Z -> list (bv 8)) (sb : fs_sb)
    (pend pend' : gset fsobj) :
  pend ⊆ pend' ->
  views_agree_off A L sb pend -> views_agree_off A L sb pend'.
Proof.
  intros Hsub [HA HL Hat]. constructor; [exact HA | exact HL |].
  intros o Ho Hm. apply Hat; [exact Ho |].
  intros Hc. apply Hm. exact (obj_masked_mono pend pend' sb o Hsub Hc).
Qed.

Lemma views_agree_off_sym (A L : Z -> list (bv 8)) (sb : fs_sb)
    (pend : gset fsobj) :
  views_agree_off A L sb pend -> views_agree_off L A sb pend.
Proof.
  intros [HA HL Hat]. constructor; [exact HL | exact HA |].
  intros o Ho Hm. exact (obj_agree_sym _ _ _ _ (Hat o Ho Hm)).
Qed.

(* the [pend = ∅] reading, used by the tiling proofs below *)
Lemma vao_at_empty (A L : Z -> list (bv 8)) (sb : fs_sb) :
  views_agree_off A L sb ∅ ->
  forall o : fsobj, obj_leaf sb o -> obj_agree A L sb o.
Proof.
  intros Hag o Ho. apply (vao_at _ _ _ _ Hag o Ho).
  intros [Hc | Hc]; by apply (not_elem_of_empty (C := gset fsobj)) in Hc.
Qed.

(* ====================================================================== *)
(*  5.  BYTE PLUMBING FOR THE TILING                                       *)
(* ====================================================================== *)

Lemma list_eq_total {A : Type} `{Inh : Inhabited A} (x y : list A) (n : nat) :
  length x = n -> length y = n ->
  (forall j : nat, (j < n)%nat -> x !!! j = y !!! j) -> x = y.
Proof.
  intros Hx Hy H. apply list_eq. intros j.
  destruct (Nat.lt_ge_cases j n) as [Hj | Hj].
  - rewrite (list_lookup_lookup_total_lt x j) by lia.
    rewrite (list_lookup_lookup_total_lt y j) by lia.
    by rewrite (H j Hj).
  - rewrite (lookup_ge_None_2 x j) by lia.
    rewrite (lookup_ge_None_2 y j) by lia. reflexivity.
Qed.

Lemma rec_bytes_lookup (bs : list (bv 8)) (k j : nat) :
  (j < 16)%nat -> rec_bytes bs k !! j = bs !! (16 * k + j)%nat.
Proof.
  intros Hj. unfold rec_bytes.
  rewrite lookup_take by exact Hj. by rewrite lookup_drop.
Qed.

(* the ELIMINATION an agreeing record gives, in [!!!] form *)
Lemma rec_bytes_elim (x y : list (bv 8)) (k j : nat) :
  rec_bytes x k = rec_bytes y k -> (j < 16)%nat ->
  x !!! (16 * k + j)%nat = y !!! (16 * k + j)%nat.
Proof.
  intros H Hj.
  rewrite !list_lookup_total_alt, <- !(rec_bytes_lookup _ k j Hj), H.
  reflexivity.
Qed.

(* ...and the INTRODUCTION a frame proof owes *)
Lemma rec_bytes_intro (x y : list (bv 8)) (k : nat) :
  (forall j : nat, (j < 16)%nat ->
     x !! (16 * k + j)%nat = y !! (16 * k + j)%nat) ->
  rec_bytes x k = rec_bytes y k.
Proof.
  intros H. apply list_eq. intros j.
  destruct (Nat.lt_ge_cases j 16) as [Hj | Hj].
  - rewrite !(rec_bytes_lookup _ k j Hj). exact (H j Hj).
  - rewrite (lookup_ge_None_2 (rec_bytes x k) j)
      by (unfold rec_bytes; rewrite length_take; lia).
    rewrite (lookup_ge_None_2 (rec_bytes y k) j)
      by (unfold rec_bytes; rewrite length_take; lia).
    reflexivity.
Qed.

Lemma rec_bytes_intro_total (x y : list (bv 8)) (k : nat) :
  length x = BSIZE -> length y = BSIZE -> (k < FS_NREC)%nat ->
  (forall j : nat, (j < 16)%nat ->
     x !!! (16 * k + j)%nat = y !!! (16 * k + j)%nat) ->
  rec_bytes x k = rec_bytes y k.
Proof.
  intros Hx Hy Hk H. apply rec_bytes_intro. intros j Hj.
  unfold FS_NREC, BSIZE in *.
  rewrite (list_lookup_lookup_total_lt x) by lia.
  rewrite (list_lookup_lookup_total_lt y) by lia.
  by rewrite (H j Hj).
Qed.

(* the little-endian field readers invert the encoders, byte by byte *)
Lemma nth_byte_fs_le_at (m : N) (bs : list (bv 8)) (o n j : nat) :
  (8 * Z.of_nat n <= Z.of_N m) -> (j < n)%nat ->
  nth_byte (Z_to_bv m (fs_le_at bs o n) : bv m) j = bs !!! (o + j)%nat.
Proof.
  intros Hm Hj. unfold fs_le_at.
  rewrite (nth_byte_assemble_len m _ j);
    [| rewrite length_fmap, length_seq; lia
     | rewrite length_fmap, length_seq; lia].
  rewrite list_lookup_total_alt, list_lookup_fmap,
    (lookup_seq_lt 0 n j Hj).
  cbn [fmap option_fmap option_map default from_option]. f_equal; lia.
Qed.

(* an [ind_bytes] of a FUNCTION's image, at one word's byte -- the shape
   [fs_dinode]'s address list has *)
Lemma ind_bytes_fmap_lookup (f : nat -> bv 32) (n q t : nat) :
  (q < n)%nat -> (t < 4)%nat ->
  ind_bytes (f <$> seq 0 n) !!! (4 * q + t)%nat = nth_byte (f q) t.
Proof.
  intros Hq Ht. rewrite list_lookup_total_alt.
  rewrite (ind_bytes_lookup (f <$> seq 0 n) q t
             ltac:(rewrite length_fmap, length_seq; lia) Ht).
  cbn [default from_option]. f_equal.
  rewrite list_lookup_total_alt, list_lookup_fmap,
    (lookup_seq_lt 0 n q Hq).
  cbn [fmap option_fmap option_map default from_option]. f_equal; lia.
Qed.

(* THE INODE ROUND TRIP, byte by byte: re-encoding a decoded record gives
   the window's own bytes back.  Total lookups on both sides, so no length
   premise is needed here. *)
Lemma dinode_bytes_fs_dinode (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (r : nat) :
  (r < 64)%nat ->
  dinode_bytes (fs_dinode P sb i) !!! r = fs_dinode_bytes P sb i !!! r.
Proof.
  intros Hr.
  unfold fs_dinode. cbv zeta.
  destruct (Nat.lt_ge_cases r 2) as [H2 | H2].
  { rewrite (dinode_bytes_type_t _ r H2). cbn [di_type].
    rewrite (nth_byte_fs_le_at 16 (fs_dinode_bytes P sb i) 0 2 r
               ltac:(cbn; lia) H2).
    f_equal; lia. }
  destruct (Nat.lt_ge_cases r 4) as [H4 | H4].
  { assert (Hq : r = (2 + (r - 2))%nat) by lia. rewrite Hq at 1.
    rewrite (dinode_bytes_major_t _ (r - 2)%nat ltac:(lia)).
    cbn [di_major].
    rewrite (nth_byte_fs_le_at 16 (fs_dinode_bytes P sb i) 2 2 (r - 2)%nat
               ltac:(cbn; lia) ltac:(lia)).
    f_equal; lia. }
  destruct (Nat.lt_ge_cases r 6) as [H6 | H6].
  { assert (Hq : r = (4 + (r - 4))%nat) by lia. rewrite Hq at 1.
    rewrite (dinode_bytes_minor_t _ (r - 4)%nat ltac:(lia)).
    cbn [di_minor].
    rewrite (nth_byte_fs_le_at 16 (fs_dinode_bytes P sb i) 4 2 (r - 4)%nat
               ltac:(cbn; lia) ltac:(lia)).
    f_equal; lia. }
  destruct (Nat.lt_ge_cases r 8) as [H8 | H8].
  { assert (Hq : r = (6 + (r - 6))%nat) by lia. rewrite Hq at 1.
    rewrite (dinode_bytes_nlink_t _ (r - 6)%nat ltac:(lia)).
    cbn [di_nlink].
    rewrite (nth_byte_fs_le_at 16 (fs_dinode_bytes P sb i) 6 2 (r - 6)%nat
               ltac:(cbn; lia) ltac:(lia)).
    f_equal; lia. }
  destruct (Nat.lt_ge_cases r 12) as [H12 | H12].
  { assert (Hq : r = (8 + (r - 8))%nat) by lia. rewrite Hq at 1.
    rewrite (dinode_bytes_size_t _ (r - 8)%nat ltac:(lia)).
    cbn [di_size].
    rewrite (nth_byte_fs_le_at 32 (fs_dinode_bytes P sb i) 8 4 (r - 8)%nat
               ltac:(cbn; lia) ltac:(lia)).
    f_equal; lia. }
  (* the thirteen address words *)
  assert (Hq : r = (12 + (r - 12))%nat) by lia. rewrite Hq at 1.
  rewrite (dinode_bytes_addrs_t _ (r - 12)%nat).
  cbn [di_addrs].
  dmf (r - 12)%nat 4%nat.
  assert (Hqq : ((r - 12) / 4 < 13)%nat) by lia.
  assert (Htt : ((r - 12) `mod` 4 < 4)%nat) by lia.
  assert (Hrt : (r - 12)%nat = (4 * ((r - 12) / 4) + (r - 12) `mod` 4)%nat)
    by lia.
  rewrite Hrt, (ind_bytes_fmap_lookup _ 13%nat _ _ Hqq Htt).
  rewrite (nth_byte_fs_le_at 32 (fs_dinode_bytes P sb i)
             (12 + 4 * ((r - 12) / 4))%nat 4
             ((r - 12) `mod` 4)%nat ltac:(cbn; lia) Htt).
  f_equal; lia.
Qed.

(* ---- the inode block, whole ------------------------------------------ *)

(* the first inum of inode block [b] *)
Definition iblk_base (sb : fs_sb) (b : Z) : Z := 16 * (b - sb_inodestart sb).

Lemma iblk_base_range (sb : fs_sb) (b : Z) (s : nat) :
  obj_slot_blk sb b -> (s < 16)%nat ->
  0 <= iblk_base sb b + Z.of_nat s
       < 16 * (sb_bmapstart sb - sb_inodestart sb).
Proof. unfold obj_slot_blk, iblk_base. lia. Qed.

Lemma iblk_inum_blk (sb : fs_sb) (b : Z) (s : nat) :
  fs_sb_ok sb -> obj_slot_blk sb b -> (s < 16)%nat ->
  IBLOCK (fs_inum_bv (iblk_base sb b + Z.of_nat s)) (sb_inodestart sb) = b.
Proof.
  intros Hok Hb Hs. unfold IBLOCK.
  rewrite (inum_bv_unsigned sb _ Hok (iblk_base_range sb b s Hb Hs)).
  unfold iblk_base.
  assert (Hre : 16 * (b - sb_inodestart sb) + Z.of_nat s
                = Z.of_nat s + (b - sb_inodestart sb) * 16) by lia.
  rewrite Hre, Z.div_add by lia.
  rewrite (Z.div_small (Z.of_nat s) 16) by lia. lia.
Qed.

Lemma iblk_inum_slot (sb : fs_sb) (b : Z) (s : nat) :
  fs_sb_ok sb -> obj_slot_blk sb b -> (s < 16)%nat ->
  islot (fs_inum_bv (iblk_base sb b + Z.of_nat s)) = s.
Proof.
  intros Hok Hb Hs. unfold islot.
  rewrite (inum_bv_unsigned sb _ Hok (iblk_base_range sb b s Hb Hs)).
  unfold iblk_base.
  assert (Hre : 16 * (b - sb_inodestart sb) + Z.of_nat s
                = Z.of_nat s + (b - sb_inodestart sb) * 16) by lia.
  rewrite Hre, Z_mod_plus_full.
  rewrite (Z.mod_small (Z.of_nat s) 16) by lia. lia.
Qed.

(* the sixteen records of inode block [b] (a local spelling of
   [FsEffBase.fs_iblk], which this file may not depend on) *)
Definition fs_iblk_at (P : Z -> list (bv 8)) (sb : fs_sb) (b : Z)
  : list dinode :=
  (fun s => fs_dinode P sb (iblk_base sb b + Z.of_nat s)) <$> seq 0 16.

Lemma fs_iblk_at_wf (P : Z -> list (bv 8)) (sb : fs_sb) (b : Z) :
  diblk_wf (fs_iblk_at P sb b).
Proof.
  split.
  - unfold fs_iblk_at. by rewrite length_fmap, length_seq.
  - apply Forall_forall. intros dn Hdn.
    apply elem_of_list_In, elem_of_list_fmap in Hdn as (s & -> & _).
    apply fs_dinode_wf.
Qed.

Lemma fs_iblk_at_lookup (P : Z -> list (bv 8)) (sb : fs_sb) (b : Z)
    (s : nat) :
  (s < 16)%nat ->
  fs_iblk_at P sb b !!! s = fs_dinode P sb (iblk_base sb b + Z.of_nat s).
Proof.
  intros Hs. unfold fs_iblk_at.
  rewrite list_lookup_total_alt, list_lookup_fmap,
    (lookup_seq_lt 0 16 s Hs).
  cbn [fmap option_fmap option_map default from_option]. f_equal; lia.
Qed.

(* THE BLOCK-LEVEL ROUND TRIP: a full inode block IS the encoding of its
   own sixteen decodes.  This is what turns slot-level (decode) agreement
   into block equality. *)
Lemma diblk_bytes_fs_iblk_at (P : Z -> list (bv 8)) (sb : fs_sb) (b : Z) :
  fs_sb_ok sb -> obj_slot_blk sb b -> length (P b) = BSIZE ->
  diblk_bytes (fs_iblk_at P sb b) = P b.
Proof.
  intros Hok Hb Hlen.
  destruct (fs_iblk_at_wf P sb b) as [Hlen16 Hall].
  apply (list_eq_total _ _ 1024%nat).
  - exact (diblk_bytes_length_16 _ (fs_iblk_at_wf P sb b)).
  - unfold BSIZE in Hlen. exact Hlen.
  - intros j Hj.
    dmf j 64%nat.
    assert (Hs : (j / 64 < 16)%nat) by lia.
    assert (Hr : (j `mod` 64 < 64)%nat) by lia.
    assert (Hjsr : j = (64 * (j / 64) + j `mod` 64)%nat) by lia.
    rewrite Hjsr.
    rewrite (diblk_bytes_lookup_t _ (j / 64)%nat (j `mod` 64)%nat Hall
               ltac:(lia) Hr).
    rewrite (fs_iblk_at_lookup P sb b (j / 64)%nat Hs).
    rewrite (dinode_bytes_fs_dinode P sb _ (j `mod` 64)%nat Hr).
    unfold fs_dinode_bytes.
    rewrite (iblk_inum_blk sb b (j / 64)%nat Hok Hb Hs).
    rewrite list_lookup_total_alt, lookup_drop, <- list_lookup_total_alt.
    rewrite (iblk_inum_slot sb b (j / 64)%nat Hok Hb Hs). reflexivity.
Qed.

(* ====================================================================== *)
(*  6.  TILING COMPLETENESS                                                *)
(* ====================================================================== *)

Lemma blk_agree_rec (A L : Z -> list (bv 8)) (sb : fs_sb) (b : Z) :
  fs_sb_ok sb -> views_agree_off A L sb ∅ -> obj_rec_blk sb b -> A b = L b.
Proof.
  intros Hok Hag Hb.
  assert (Hhome : fs_obj_home sb b) by exact (obj_rec_blk_home sb b Hok Hb).
  apply (list_eq_total _ _ BSIZE).
  - exact (vao_szA _ _ _ _ Hag b Hhome).
  - exact (vao_szL _ _ _ _ Hag b Hhome).
  - intros j Hj.
    unfold FS_NREC, BSIZE in *. dmf j 16%nat.
    assert (Hk : (j / 16 < 64)%nat) by lia.
    assert (Ht : (j `mod` 16 < 16)%nat) by lia.
    assert (Hjkt : j = (16 * (j / 16) + j `mod` 16)%nat) by lia.
    rewrite Hjkt.
    exact (rec_bytes_elim _ _ (j / 16)%nat (j `mod` 16)%nat
             (vao_at_empty A L sb Hag (ORec b (j / 16)%nat) (conj Hb Hk)) Ht).
Qed.

Lemma blk_agree_slot (A L : Z -> list (bv 8)) (sb : fs_sb) (b : Z) :
  fs_sb_ok sb -> views_agree_off A L sb ∅ -> obj_slot_blk sb b -> A b = L b.
Proof.
  intros Hok Hag Hb.
  assert (Hhome : fs_obj_home sb b) by exact (obj_slot_blk_home sb b Hok Hb).
  rewrite <- (diblk_bytes_fs_iblk_at A sb b Hok Hb
                (vao_szA _ _ _ _ Hag b Hhome)).
  rewrite <- (diblk_bytes_fs_iblk_at L sb b Hok Hb
                (vao_szL _ _ _ _ Hag b Hhome)).
  f_equal. unfold fs_iblk_at. apply list_eq. intros s.
  rewrite !list_lookup_fmap.
  destruct (seq 0 16 !! s) as [x |] eqn:E; [| reflexivity].
  apply lookup_seq in E as [-> Hlt].
  cbn [fmap option_fmap option_map]. f_equal.
  exact (vao_at_empty A L sb Hag (OSlot (iblk_base sb b + Z.of_nat (0 + s)))
           (iblk_base_range sb b (0 + s)%nat Hb ltac:(lia))).
Qed.

Lemma blk_agree_bit (A L : Z -> list (bv 8)) (sb : fs_sb) :
  fs_sb_ok sb -> views_agree_off A L sb ∅ ->
  A (sb_bmapstart sb) = L (sb_bmapstart sb).
Proof.
  intros Hok Hag.
  pose proof (bmap_home sb Hok) as Hhome.
  pose proof (vao_szA _ _ _ _ Hag _ Hhome) as HlA.
  pose proof (vao_szL _ _ _ _ Hag _ Hhome) as HlL.
  transitivity (bm_bytes BSIZE (fs_bmap_set BSIZE (A (sb_bmapstart sb)))).
  { symmetry. exact (bm_bytes_fs_bmap_set BSIZE _ HlA). }
  transitivity (bm_bytes BSIZE (fs_bmap_set BSIZE (L (sb_bmapstart sb)))).
  { f_equal. apply set_eq. intros x.
    rewrite !fs_bmap_set_elem, BSIZE_z_nat.
    split; intros [Hx Hbit]; (split; [exact Hx |]).
    - rewrite <- (vao_at_empty A L sb Hag (OBit x) Hx). exact Hbit.
    - rewrite (vao_at_empty A L sb Hag (OBit x) Hx). exact Hbit. }
  exact (bm_bytes_fs_bmap_set BSIZE _ HlL).
Qed.

(* THE THEOREM: with nothing pending the two views ARE the same disk on the
   home extent -- [FsWf]'s own footprint, so [fs_durable_wf_view] transfers
   by [fs_durable_wf_view_ext] (corollary below). *)
Theorem views_agree_tiling (A L : Z -> list (bv 8)) (sb : fs_sb) (b : Z) :
  fs_sb_ok sb -> views_agree_off A L sb ∅ -> fs_obj_home sb b -> A b = L b.
Proof.
  intros Hok Hag Hb.
  destruct (fs_obj_home_cases sb b Hok Hb) as [Hr | [Hs | ->]].
  - exact (blk_agree_rec A L sb b Hok Hag Hr).
  - exact (blk_agree_slot A L sb b Hok Hag Hs).
  - exact (blk_agree_bit A L sb Hok Hag).
Qed.

(* the superblock is a home block, so the two views parse alike *)
Corollary views_agree_tiling_sb (A L : Z -> list (bv 8)) (sb : fs_sb) :
  fs_sb_ok sb -> views_agree_off A L sb ∅ -> fs_parse_sb L = fs_parse_sb A.
Proof.
  intros Hok Hag. apply fs_parse_sb_ext. symmetry.
  apply (views_agree_tiling A L sb SB_BNO Hok Hag). by left.
Qed.

(* ...and the durable invariant transfers *)
Corollary views_agree_tiling_wf (A L : Z -> list (bv 8)) (sb : fs_sb) :
  fs_parse_sb A = Some sb -> views_agree_off A L sb ∅ ->
  fs_durable_wf_view A -> fs_durable_wf_view L.
Proof.
  intros Hp Hag Hwf.
  assert (Hok : fs_sb_ok sb).
  { destruct Hwf as (sb' & Hp' & Hsw).
    assert (Hse : sb' = sb) by congruence. subst sb'.
    exact (fs_sb_wf_ok sb (fdw_sb _ _ Hsw)). }
  apply (fs_durable_wf_view_ext A L sb Hp); [| exact Hwf].
  intros b Hb. symmetry. exact (views_agree_tiling A L sb b Hok Hag Hb).
Qed.

(* THE [gmap] FORM, in [FsWf]'s [dv_of_D] spelling: at [pend = ∅] the
   committed map and the logged map are EQUAL when both are the home set --
   what the flip's finalize consumes. *)
Corollary views_agree_tiling_gmap (DA DL : gmap Z (list (bv 8)))
    (sb : fs_sb) :
  fs_sb_ok sb ->
  (forall b : Z, b ∈ dom DA -> fs_obj_home sb b) ->
  dom DA = dom DL ->
  views_agree_off (dv_of_D DA) (dv_of_D DL) sb ∅ ->
  DA = DL.
Proof.
  intros Hok Hdom Hdd Hag. apply map_eq. intros b.
  destruct (decide (b ∈ dom DA)) as [Hin | Hout].
  - pose proof Hin as Hin0. apply elem_of_dom in Hin as [v Hv].
    assert (Hin' : b ∈ dom DL) by (rewrite <- Hdd; exact Hin0).
    apply elem_of_dom in Hin' as [w Hw].
    pose proof (views_agree_tiling _ _ sb b Hok Hag (Hdom b Hin0)) as Heq.
    unfold dv_of_D in Heq. rewrite Hv, Hw in Heq. cbn in Heq.
    rewrite Hv, Hw. by rewrite Heq.
  - assert (Hout' : b ∉ dom DL) by (rewrite <- Hdd; exact Hout).
    apply not_elem_of_dom in Hout. apply not_elem_of_dom in Hout'.
    by rewrite Hout, Hout'.
Qed.

(* ====================================================================== *)
(*  7.  THE FOLD                                                           *)
(* ====================================================================== *)

Lemma obj_masked_union (F1 F2 : gset fsobj) (sb : fs_sb) (o : fsobj) :
  ~ obj_masked (F1 ∪ F2) sb o ->
  ~ obj_masked F1 sb o /\ ~ obj_masked F2 sb o.
Proof.
  intros H. split; intros [Hc | Hc]; apply H;
    [left | right | left | right]; set_solver.
Qed.

(* composing two layers of one effect: their footprints union *)
Lemma frame_compose (P1 P2 P3 : Z -> list (bv 8)) (sb : fs_sb)
    (F1 F2 : gset fsobj) :
  (forall o, obj_leaf sb o -> ~ obj_masked F1 sb o -> obj_agree P2 P1 sb o) ->
  (forall o, obj_leaf sb o -> ~ obj_masked F2 sb o -> obj_agree P3 P2 sb o) ->
  forall o, obj_leaf sb o -> ~ obj_masked (F1 ∪ F2) sb o ->
    obj_agree P3 P1 sb o.
Proof.
  intros H1 H2 o Ho Hm.
  destruct (obj_masked_union F1 F2 sb o Hm) as [Hm1 Hm2].
  exact (obj_agree_trans _ _ _ _ _ (H2 o Ho Hm2) (H1 o Ho Hm1)).
Qed.

(* every masked object lives in one of the footprint's blocks -- so the
   MATCH side of the fold is discharged from BLOCK equations, which is what
   an op's [log_write] postconditions are. *)
Lemma obj_masked_blk (F : gset fsobj) (sb : fs_sb) (o : fsobj) :
  obj_masked F sb o -> obj_blk sb o ∈ (set_map (obj_blk sb) F : gset Z).
Proof.
  intros [H | H]; apply elem_of_map.
  - by exists o.
  - by exists (OBlk (obj_blk sb o)).
Qed.

(* THE FOLD (the shape an ending op's arm invokes, beside its G2 lemma):
   the effect frames outside its footprint, keeps the blocks full, and
   agrees with the logged view ON THE BLOCKS IT WROTE; the footprint then
   leaves the pending set.

   NOTE the premise that is NOT there: [F ⊆ pend].  The ledger does give
   it, but the fold does not need it -- an object of [F] is discharged by
   the block equation whether or not it was pending. *)
Theorem views_agree_fold (A A' L : Z -> list (bv 8)) (sb : fs_sb)
    (pend F : gset fsobj) :
  views_agree_off A L sb pend ->
  (forall o, obj_leaf sb o -> ~ obj_masked F sb o -> obj_agree A' A sb o) ->
  view_sized A' sb ->
  (forall b : Z, b ∈ (set_map (obj_blk sb) F : gset Z) -> A' b = L b) ->
  views_agree_off A' L sb (pend ∖ F).
Proof.
  intros Hag Hframe Hsz Hmatch. constructor.
  - exact Hsz.
  - exact (vao_szL _ _ _ _ Hag).
  - intros o Ho Hm.
    destruct (decide (obj_masked F sb o)) as [Hmf | Hmf].
    + apply obj_agree_of_blk_eq. exact (Hmatch _ (obj_masked_blk F sb o Hmf)).
    + (* framed: the effect did not move it, and it was not pending *)
      apply (obj_agree_trans A' A L sb o (Hframe o Ho Hmf)).
      apply (vao_at _ _ _ _ Hag o Ho).
      intros Hcm. apply Hm. destruct Hcm as [Hc | Hc].
      * left. apply elem_of_difference. split; [exact Hc |].
        intros Hc2. apply Hmf. by left.
      * right. apply elem_of_difference. split; [exact Hc |].
        intros Hc2. apply Hmf. by right.
Qed.

(* ====================================================================== *)
(*  8.  DECODE BRIDGES FOR CONSUMERS                                       *)
(* ====================================================================== *)

(* A record object's byte agreement IS [DirView.dir_win_agree] at the
   corresponding file-record index, so every DirView reader
   ([dir_inum]/[bname]/[dir_live]/[dir_first]/...) agrees at it.  Stated
   over the two content blocks so that the caller supplies the block-map
   readings ([fs_data_of_addr]) it already has. *)
Lemma dir_win_agree_of_rec (dataA dataL : nat -> list (bv 8))
    (x y : list (bv 8)) (k : nat) :
  dataA (k / 64)%nat = x -> dataL (k / 64)%nat = y ->
  rec_bytes x (k `mod` 64)%nat = rec_bytes y (k `mod` 64)%nat ->
  dir_win_agree dataA dataL k.
Proof.
  intros HA HL Hrec j Hj. unfold file_byte. dmf k 64%nat.
  assert (Hk : (16 * k + j)%nat
               = ((16 * (k `mod` 64) + j) + (k / 64) * 1024)%nat) by lia.
  assert (Hsm : (16 * (k `mod` 64) + j < 1024)%nat) by lia.
  assert (Hdiv : ((16 * k + j) `div` BSIZE)%nat = (k / 64)%nat).
  { unfold BSIZE. rewrite Hk, Nat.div_add by lia.
    rewrite (Nat.div_small _ 1024 Hsm). lia. }
  assert (Hmod : ((16 * k + j) `mod` BSIZE)%nat
                 = (16 * (k `mod` 64) + j)%nat).
  { unfold BSIZE. rewrite Hk, Nat.Div0.mod_add.
    exact (Nat.mod_small _ 1024 Hsm). }
  rewrite Hdiv, Hmod, HA, HL. symmetry.
  exact (rec_bytes_elim x y (k `mod` 64)%nat j Hrec Hj).
Qed.
