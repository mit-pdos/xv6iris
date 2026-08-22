(* ====================================================================== *)
(* FsEffects.v -- stage F2: the semantic-effect update lemmas for          *)
(* [FsWf.fs_durable_wf_view] (claude-notes/projects/durable-disk.md §5).   *)
(*                                                                         *)
(* THE VOCABULARY: each of xv6's twelve FS transactions nets out to a      *)
(* composition of a handful of SEMANTIC EFFECTS, each a multi-block        *)
(* update of the committed view that PRESERVES the durable invariant       *)
(* under decode-level preconditions.  Per-block lemmas cannot do this      *)
(* job: a bitmap bit set before the inode points at the block IS the      *)
(* mid-transaction inconsistency, so the update unit is the effect, not    *)
(* the block (worklist F2, corrected 2026-08-22).                          *)
(*                                                                         *)
(* Every effect is a composition of single-block updates                   *)
(* [fs_upd P b bs] whose contents come from the EXISTING encoders          *)
(* ([DinodeEnc.diblk_bytes], [BitmapEnc.bm_bytes], [DirentEnc.             *)
(* dirent_bytes]/[de_of_name], the [fs_splice] byte window -- the pure     *)
(* body of [ProofWriteiParts.wi_splice]), so that stage G2 can match op    *)
(* postconditions to the effect functions.                                 *)
(*                                                                         *)
(* This file is PURE (no Iris) and sits as a leaf over [FsWf].             *)
(* ====================================================================== *)
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

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  1.  THE SINGLE-BLOCK UPDATE                                            *)
(* ====================================================================== *)

Definition fs_upd (P : Z -> list (bv 8)) (b : Z) (bs : list (bv 8))
  : Z -> list (bv 8) :=
  fun c => if decide (c = b) then bs else P c.

Lemma fs_upd_at (P : Z -> list (bv 8)) (b : Z) (bs : list (bv 8)) :
  fs_upd P b bs b = bs.
Proof. unfold fs_upd. rewrite decide_True by reflexivity. reflexivity. Qed.

Lemma fs_upd_ne (P : Z -> list (bv 8)) (b c : Z) (bs : list (bv 8)) :
  c <> b -> fs_upd P b bs c = P c.
Proof. intros H. unfold fs_upd. rewrite decide_False by exact H. reflexivity. Qed.

(* ====================================================================== *)
(*  2.  THE BYTE-WINDOW SPLICE                                             *)
(*                                                                         *)
(*  [ProofWriteiParts.wi_splice]'s body, verbatim -- restated here          *)
(*  because that file is iris-heavy and this one is pure.  The two are      *)
(*  DEFINITIONALLY equal, so a G2 consumer bridges by [reflexivity].        *)
(* ====================================================================== *)

Definition fs_splice (bs : list (bv 8)) (o len : nat) (g : nat -> bv 8)
  : list (bv 8) :=
  (fun i => if decide ((o <= i)%nat /\ (i < o + len)%nat)
            then g (i - o)%nat else bs !!! i) <$> seq 0 BSIZE.

Lemma fs_splice_len (bs : list (bv 8)) (o len : nat) (g : nat -> bv 8) :
  length (fs_splice bs o len g) = BSIZE.
Proof. unfold fs_splice. rewrite length_fmap, length_seq. reflexivity. Qed.

Lemma fs_splice_lookup (bs : list (bv 8)) (o len i : nat) (g : nat -> bv 8) :
  (i < BSIZE)%nat ->
  fs_splice bs o len g !!! i
  = if decide ((o <= i)%nat /\ (i < o + len)%nat)
    then g (i - o)%nat else bs !!! i.
Proof.
  intros Hi.
  assert (Hlk : seq 0 BSIZE !! i = Some i) by (apply lookup_seq; lia).
  unfold fs_splice.
  rewrite list_lookup_total_alt, list_lookup_fmap, Hlk. reflexivity.
Qed.

Lemma fs_splice_lookup_hi (bs : list (bv 8)) (o len i : nat)
    (g : nat -> bv 8) :
  (BSIZE <= i)%nat -> fs_splice bs o len g !!! i = bv_0 8.
Proof.
  intros Hi. rewrite list_lookup_total_alt.
  rewrite lookup_ge_None_2; [reflexivity |].
  rewrite fs_splice_len. exact Hi.
Qed.

(* ====================================================================== *)
(*  3.  DINODE FIELD UPDATES (the values the effects write)                 *)
(* ====================================================================== *)

Definition di_set_nlink (dn : dinode) (w : bv 16) : dinode :=
  MkDinode (di_type dn) (di_major dn) (di_minor dn) w
           (di_size dn) (di_addrs dn).

Definition di_set_size (dn : dinode) (sz : bv 32) : dinode :=
  MkDinode (di_type dn) (di_major dn) (di_minor dn) (di_nlink dn)
           sz (di_addrs dn).

Definition di_set_size_addr (dn : dinode) (sz : bv 32) (j : nat) (a : bv 32)
  : dinode :=
  MkDinode (di_type dn) (di_major dn) (di_minor dn) (di_nlink dn)
           sz (<[j := a]> (di_addrs dn)).

(* the one-step nlink moves, at the bv 16 the record stores *)
Definition di_nlink_inc (dn : dinode) : dinode :=
  di_set_nlink dn (Z_to_bv 16 (bv_unsigned (di_nlink dn) + 1)).
Definition di_nlink_dec (dn : dinode) : dinode :=
  di_set_nlink dn (Z_to_bv 16 (bv_unsigned (di_nlink dn) - 1)).

(* a freshly created non-directory inode: create/mknod's net record
   ([SpecIalloc.ialloc_fresh ty] with [nlink := 1] and the device pair
   filled in, which is what the transaction writes home) *)
Definition di_create (ty maj min : bv 16) : dinode :=
  MkDinode ty maj min (Z_to_bv 16 1) (bv_0 32) (replicate 13 (bv_0 32)).

(* a freshly created directory: type T_DIR, one link, one data block
   holding the two dot records (size 32) *)
Definition di_create_dir (fb : Z) : dinode :=
  MkDinode (Z_to_bv 16 T_DIR_z) (bv_0 16) (bv_0 16) (Z_to_bv 16 1)
           (Z_to_bv 32 32) (<[0%nat := Z_to_bv 32 fb]> (replicate 13 (bv_0 32))).

(* itrunc's record ([SpecItrunc.di_trunc], whose addrs spelling
   [bm_cells bm_empty] is definitionally [replicate 13 (bv_0 32)]) *)
Definition di_trunc_v (dn : dinode) : dinode :=
  MkDinode (di_type dn) (di_major dn) (di_minor dn) (di_nlink dn)
           (bv_0 32) (replicate 13 (bv_0 32)).

(* iput's freed record: the truncated record with the type zeroed *)
Definition di_free_v (dn : dinode) : dinode :=
  MkDinode (bv_0 16) (di_major dn) (di_minor dn) (di_nlink dn)
           (bv_0 32) (replicate 13 (bv_0 32)).

Lemma di_set_nlink_wf (dn : dinode) (w : bv 16) :
  dinode_wf dn -> dinode_wf (di_set_nlink dn w).
Proof. exact (fun H => H). Qed.

Lemma di_set_size_wf (dn : dinode) (sz : bv 32) :
  dinode_wf dn -> dinode_wf (di_set_size dn sz).
Proof. exact (fun H => H). Qed.

Lemma di_set_size_addr_wf (dn : dinode) (sz : bv 32) (j : nat) (a : bv 32) :
  dinode_wf dn -> dinode_wf (di_set_size_addr dn sz j a).
Proof.
  intros H. unfold dinode_wf, di_set_size_addr in *. cbn [di_addrs].
  rewrite length_insert. exact H.
Qed.

Lemma di_create_wf (ty maj min : bv 16) : dinode_wf (di_create ty maj min).
Proof. unfold dinode_wf. cbn [di_addrs]. apply length_replicate. Qed.

Lemma di_create_dir_wf (fb : Z) : dinode_wf (di_create_dir fb).
Proof.
  unfold dinode_wf, di_create_dir. cbn [di_addrs].
  rewrite length_insert. apply length_replicate.
Qed.

Lemma di_trunc_v_wf (dn : dinode) : dinode_wf (di_trunc_v dn).
Proof. unfold dinode_wf. cbn [di_addrs]. apply length_replicate. Qed.

Lemma di_free_v_wf (dn : dinode) : dinode_wf (di_free_v dn).
Proof. unfold dinode_wf. cbn [di_addrs]. apply length_replicate. Qed.

(* ====================================================================== *)
(*  4.  THE INODE-RECORD EFFECT                                            *)
(*                                                                         *)
(*  One inode record is rewritten by RE-ENCODING its whole block: the       *)
(*  block's sixteen records are decoded ([fs_iblk]), the slot is            *)
(*  replaced, and [DinodeEnc.diblk_bytes] lays the block back down.  On     *)
(*  a block that already IS [diblk_bytes ds] (every block the FS proofs     *)
(*  produce), [FsImg.fs_dinode_of_diblk] collapses [fs_iblk] to [ds], so    *)
(*  the written bytes are [diblk_bytes (<[islot i := dn']> ds)] --          *)
(*  exactly the op postconditions' shape.                                   *)
(* ====================================================================== *)

Definition fs_iblk (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
  : list dinode :=
  (fun s => fs_dinode P sb (16 * (i / 16) + Z.of_nat s)) <$> seq 0 16.

Definition eff_dinode (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (dn' : dinode) : Z -> list (bv 8) :=
  fs_upd P (IBLOCK (fs_inum_bv i) (sb_inodestart sb))
    (diblk_bytes (<[islot (fs_inum_bv i) := dn']> (fs_iblk P sb i))).

Lemma fs_iblk_wf (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  diblk_wf (fs_iblk P sb i).
Proof.
  split.
  - unfold fs_iblk. rewrite length_fmap, length_seq. reflexivity.
  - apply Forall_forall. intros dn Hdn.
    apply elem_of_list_In in Hdn.
    apply elem_of_list_fmap in Hdn as (s & -> & _).
    apply fs_dinode_wf.
Qed.

(* the region-wide arithmetic the decode lemmas below run on *)
Section IblkGeom.
  Context (sb : fs_sb) (Hok : fs_sb_ok sb).

  Let N : Z := 16 * (sb_ninodes sb / 16 + 1).

  Lemma fs_inum_bv_unsigned (i : Z) :
    0 <= i < N -> bv_unsigned (fs_inum_bv i) = i.
  Proof.
    intros Hi. unfold fs_inum_bv. apply Z_to_bv_small.
    destruct (fs_sb_ok_geom sb Hok) as (_ & _ & _ & _ & _ & Hm).
    unfold N in *. lia.
  Qed.

  Lemma iblock_of (i : Z) :
    0 <= i < N ->
    IBLOCK (fs_inum_bv i) (sb_inodestart sb) = i / 16 + sb_inodestart sb.
  Proof.
    intros Hi. unfold IBLOCK. rewrite fs_inum_bv_unsigned by exact Hi.
    reflexivity.
  Qed.

  Lemma islot_of (i : Z) :
    0 <= i < N -> islot (fs_inum_bv i) = Z.to_nat (i `mod` 16).
  Proof.
    intros Hi. unfold islot. rewrite fs_inum_bv_unsigned by exact Hi.
    reflexivity.
  Qed.

  (* the inode blocks sit strictly between the superblock and the bitmap *)
  Lemma iblock_bounds (i : Z) :
    0 <= i < N ->
    SB_BNO < IBLOCK (fs_inum_bv i) (sb_inodestart sb)
    /\ sb_inodestart sb <= IBLOCK (fs_inum_bv i) (sb_inodestart sb)
    /\ IBLOCK (fs_inum_bv i) (sb_inodestart sb) < sb_bmapstart sb.
  Proof.
    intros Hi. rewrite (iblock_of i Hi).
    destruct (fs_sb_ok_meta sb Hok) as (H2 & _).
    pose proof (sbo_bmapstart sb Hok) as Hbm.
    assert (Hd : 0 <= i / 16 < sb_ninodes sb / 16 + 1).
    { split; [apply Z.div_pos; lia |].
      apply Z.div_lt_upper_bound; unfold N in Hi; lia. }
    unfold SB_BNO. lia.
  Qed.

  Lemma iblock_eq_iff (i j : Z) :
    0 <= i < N -> 0 <= j < N ->
    (IBLOCK (fs_inum_bv j) (sb_inodestart sb)
     = IBLOCK (fs_inum_bv i) (sb_inodestart sb)
     <-> j / 16 = i / 16).
  Proof.
    intros Hi Hj. rewrite (iblock_of i Hi), (iblock_of j Hj). lia.
  Qed.

  Lemma fs_iblk_slot (P : Z -> list (bv 8)) (i j : Z) :
    0 <= i < N -> 0 <= j < N -> j / 16 = i / 16 ->
    fs_iblk P sb i !!! islot (fs_inum_bv j) = fs_dinode P sb j.
  Proof.
    intros Hi Hj Hdiv. rewrite (islot_of j Hj).
    unfold fs_iblk.
    pose proof (Z.mod_pos_bound j 16 ltac:(lia)) as Hm.
    rewrite list_lookup_total_alt, list_lookup_fmap.
    rewrite (lookup_seq_lt 0 16 (Z.to_nat (j `mod` 16))) by lia.
    cbn [fmap option_fmap option_map default from_option id].
    f_equal. rewrite <- Hdiv.
    pose proof (Z.div_mod j 16 ltac:(lia)). lia.
  Qed.

  (* the slots of one block are the inums that share [i / 16] *)
  Lemma islot_inj (i j : Z) :
    0 <= i < N -> 0 <= j < N -> j / 16 = i / 16 ->
    islot (fs_inum_bv j) = islot (fs_inum_bv i) -> j = i.
  Proof.
    intros Hi Hj Hdiv Hslot.
    rewrite (islot_of i Hi), (islot_of j Hj) in Hslot.
    pose proof (Z.mod_pos_bound i 16 ltac:(lia)).
    pose proof (Z.mod_pos_bound j 16 ltac:(lia)).
    pose proof (Z.div_mod i 16 ltac:(lia)).
    pose proof (Z.div_mod j 16 ltac:(lia)).
    lia.
  Qed.

  (* THE DECODE: the effect rewrites record [i] and nothing else *)
  Lemma eff_dinode_dec (P : Z -> list (bv 8)) (i : Z) (dn' : dinode)
      (j : Z) :
    dinode_wf dn' -> 0 <= i < N -> 0 <= j < N ->
    fs_dinode (eff_dinode P sb i dn') sb j
    = if decide (j = i) then dn' else fs_dinode P sb j.
  Proof.
    intros Hwf Hi Hj.
    destruct (decide (j / 16 = i / 16)) as [Hdiv | Hdiv].
    - (* same block: through the encoder's round trip *)
      assert (Hds : diblk_wf (<[islot (fs_inum_bv i) := dn']>
                                (fs_iblk P sb i))).
      { apply diblk_wf_insert; [apply fs_iblk_wf | exact Hwf]. }
      assert (Hblk : eff_dinode P sb i dn'
                       (IBLOCK (fs_inum_bv j) (sb_inodestart sb))
                     = diblk_bytes (<[islot (fs_inum_bv i) := dn']>
                                      (fs_iblk P sb i))).
      { unfold eff_dinode.
        rewrite (proj2 (iblock_eq_iff i j Hi Hj) Hdiv).
        apply fs_upd_at. }
      rewrite (fs_dinode_of_diblk _ sb j _ Hds Hblk).
      destruct (decide (j = i)) as [-> | Hne].
      + rewrite list_lookup_total_insert; [reflexivity |].
        destruct (fs_iblk_wf P sb i) as [Hlen _]. rewrite Hlen.
        apply islot_lt.
      + rewrite list_lookup_total_insert_ne.
        * exact (fs_iblk_slot P i j Hi Hj Hdiv).
        * intros Hc. exact (Hne (islot_inj i j Hi Hj Hdiv (eq_sym Hc))).
    - (* different block: untouched *)
      rewrite decide_False by (intros ->; exact (Hdiv eq_refl)).
      apply fs_dinode_ext. unfold eff_dinode. apply fs_upd_ne.
      intros Hc. exact (Hdiv (proj1 (iblock_eq_iff i j Hi Hj) Hc)).
  Qed.

  Lemma eff_dinode_out (P : Z -> list (bv 8)) (i : Z) (dn' : dinode)
      (b : Z) :
    b <> IBLOCK (fs_inum_bv i) (sb_inodestart sb) ->
    eff_dinode P sb i dn' b = P b.
  Proof. intros H. unfold eff_dinode. apply fs_upd_ne. exact H. Qed.

  (* the effect leaves the superblock, the bitmap block and the whole
     data region alone *)
  Lemma eff_dinode_out_data (P : Z -> list (bv 8)) (i : Z) (dn' : dinode)
      (b : Z) :
    0 <= i < N -> fs_data_start sb <= b \/ b = SB_BNO \/ b = sb_bmapstart sb ->
    eff_dinode P sb i dn' b = P b.
  Proof.
    intros Hi Hb. apply eff_dinode_out.
    destruct (iblock_bounds i Hi) as (H1 & H2 & H3).
    unfold fs_data_start in Hb. lia.
  Qed.

End IblkGeom.

(* ====================================================================== *)
(*  5.  THE BITMAP EFFECT                                                  *)
(* ====================================================================== *)

Definition eff_bmap (P : Z -> list (bv 8)) (sb : fs_sb) (u' : gset Z)
  : Z -> list (bv 8) :=
  fs_upd P (sb_bmapstart sb) (bm_bytes BSIZE u').

Lemma eff_bmap_out (P : Z -> list (bv 8)) (sb : fs_sb) (u' : gset Z)
    (b : Z) :
  b <> sb_bmapstart sb -> eff_bmap P sb u' b = P b.
Proof. intros H. unfold eff_bmap. apply fs_upd_ne. exact H. Qed.

Lemma eff_bmap_bit (P : Z -> list (bv 8)) (sb : fs_sb) (u' : gset Z)
    (b : Z) :
  0 <= b < 8 * BSIZE_z ->
  fs_bit (eff_bmap P sb u' (sb_bmapstart sb)) b = bool_decide (b ∈ u').
Proof.
  intros Hb. unfold eff_bmap. rewrite fs_upd_at.
  apply fs_bit_bm_bytes. rewrite BSIZE_z_nat. exact Hb.
Qed.

(* the introduction rule for W5 at a rewritten block *)
Lemma fs_bitmap_wf_intro (P' : Z -> list (bv 8)) (sb : fs_sb)
    (u'' : gset Z) :
  (forall b : Z, 0 <= b < sb_size sb ->
     (fs_bit (P' (sb_bmapstart sb)) b = true
      <-> (b < fs_data_start sb \/ b ∈ u''))) ->
  fs_bitmap_wf P' sb u'' = true.
Proof.
  intros H. unfold fs_bitmap_wf.
  rewrite List.forallb_forall. intros x Hin.
  apply elem_of_list_In, elem_of_seq in Hin.
  cbv beta zeta. apply bool_decide_eq_true_2.
  pose proof (H (Z.of_nat x) ltac:(lia)) as Hx.
  destruct (fs_bit (P' (sb_bmapstart sb)) (Z.of_nat x)) eqn:Hbit.
  - symmetry. apply orb_true_iff.
    destruct (proj1 Hx eq_refl) as [Hlt | Hin'].
    + left. apply Z.ltb_lt. exact Hlt.
    + right. apply bool_decide_eq_true_2. exact Hin'.
  - symmetry. apply orb_false_iff.
    assert (Hnot : ~ (Z.of_nat x < fs_data_start sb \/ Z.of_nat x ∈ u'')).
    { intros Hc. pose proof (proj2 Hx Hc) as He. congruence. }
    split.
    + apply Z.ltb_ge. lia.
    + apply bool_decide_eq_false_2. tauto.
Qed.

(* ====================================================================== *)
(*  6.  LOCALITY: A DECODE ONLY READS ITS OWN BLOCKS                       *)
(*                                                                         *)
(*  [FsWf] §5-7 gives agreement under FULL-region agreement; the effects    *)
(*  change blocks INSIDE the region, so these are the finer per-inode       *)
(*  forms: a reader is unmoved as long as the blocks IT reads are.          *)
(* ====================================================================== *)

Lemma fs_data_of_same (P P' : Z -> list (bv 8)) (dn : dinode) (k : nat) :
  fs_ind_ents P' dn = fs_ind_ents P dn ->
  (fs_blk_addr P dn k <> 0 ->
   P' (fs_blk_addr P dn k) = P (fs_blk_addr P dn k)) ->
  fs_data_of P' dn k = fs_data_of P dn k.
Proof.
  intros Hind Hblk.
  assert (Haddr : fs_blk_addr P' dn k = fs_blk_addr P dn k).
  { unfold fs_blk_addr. rewrite Hind. reflexivity. }
  rewrite !fs_data_of_addr, Haddr.
  destruct (fs_blk_addr P dn k =? 0) eqn:E; [reflexivity |].
  apply Hblk. apply Z.eqb_neq. exact E.
Qed.

Lemma fs_inode_blocks_same (P P' : Z -> list (bv 8)) (dn : dinode) :
  fs_ind_ents P' dn = fs_ind_ents P dn ->
  fs_inode_blocks P' dn = fs_inode_blocks P dn.
Proof. intros Hind. unfold fs_inode_blocks. rewrite Hind. reflexivity. Qed.

Lemma fs_inode_dwf_same (P P' : Z -> list (bv 8)) (sb : fs_sb)
    (dn : dinode) :
  fs_ind_ents P' dn = fs_ind_ents P dn ->
  fs_inode_dwf P' sb dn = fs_inode_dwf P sb dn.
Proof. intros Hind. unfold fs_inode_dwf. rewrite Hind. reflexivity. Qed.

(* the readers that ignore everything but type/size/addrs *)
Lemma fs_ind_ents_meta (P : Z -> list (bv 8)) (dn dn' : dinode) :
  di_addrs dn' = di_addrs dn -> fs_ind_ents P dn' = fs_ind_ents P dn.
Proof. intros H. unfold fs_ind_ents. rewrite H. reflexivity. Qed.

Lemma fs_blk_addr_meta (P : Z -> list (bv 8)) (dn dn' : dinode) (k : nat) :
  di_addrs dn' = di_addrs dn -> fs_blk_addr P dn' k = fs_blk_addr P dn k.
Proof.
  intros H. unfold fs_blk_addr. rewrite (fs_ind_ents_meta P dn dn' H), H.
  reflexivity.
Qed.

Lemma fs_data_of_meta (P : Z -> list (bv 8)) (dn dn' : dinode) (k : nat) :
  di_addrs dn' = di_addrs dn -> fs_data_of P dn' k = fs_data_of P dn k.
Proof.
  intros H. rewrite !fs_data_of_addr, (fs_blk_addr_meta P dn dn' k H).
  reflexivity.
Qed.

Lemma fs_inode_blocks_meta (P : Z -> list (bv 8)) (dn dn' : dinode) :
  di_addrs dn' = di_addrs dn -> di_size dn' = di_size dn ->
  fs_inode_blocks P dn' = fs_inode_blocks P dn.
Proof.
  intros Ha Hs. unfold fs_inode_blocks.
  rewrite (fs_ind_ents_meta P dn dn' Ha), Ha, Hs. reflexivity.
Qed.

Lemma fs_inode_dwf_meta (P : Z -> list (bv 8)) (sb : fs_sb)
    (dn dn' : dinode) :
  di_type dn' = di_type dn -> di_addrs dn' = di_addrs dn ->
  di_size dn' = di_size dn ->
  fs_inode_dwf P sb dn' = fs_inode_dwf P sb dn.
Proof.
  intros Ht Ha Hs. unfold fs_inode_dwf.
  rewrite (fs_ind_ents_meta P dn dn' Ha), Ht, Ha, Hs. reflexivity.
Qed.

(* ====================================================================== *)
(*  7.  TICKET-COUNT ARITHMETIC                                            *)
(*                                                                         *)
(*  [FsWf.fs_rtickets] is one [mjoin] segment per directory, and a          *)
(*  directory's segment is one [omap] slot per record -- so every effect's  *)
(*  count delta is local: one segment moves, and inside it one slot.        *)
(* ====================================================================== *)

Lemma fs_tick_count_nil (z : Z) : fs_tick_count [] z = 0%nat.
Proof. reflexivity. Qed.

Lemma fs_tick_count_app (l1 l2 : list Z) (z : Z) :
  fs_tick_count (l1 ++ l2) z
  = (fs_tick_count l1 z + fs_tick_count l2 z)%nat.
Proof.
  unfold fs_tick_count. rewrite List.filter_app, length_app. reflexivity.
Qed.

Lemma fs_tick_count_elem (l : list Z) (z : Z) :
  z ∈ l -> (1 <= fs_tick_count l z)%nat.
Proof.
  induction l as [| a l IH]; intros Hz.
  - exfalso. exact (proj1 (elem_of_nil z) Hz).
  - unfold fs_tick_count. cbn [List.filter].
    apply elem_of_cons in Hz as [Heq | Hz].
    + rewrite (bool_decide_eq_true_2 (a = z) (eq_sym Heq)). cbn [length]. lia.
    + destruct (bool_decide (a = z)); cbn [length];
        pose proof (IH Hz); unfold fs_tick_count in *; lia.
Qed.

(* one option slot's contribution *)
Definition otick (o : option Z) (z : Z) : nat :=
  match o with
  | Some t => if bool_decide (t = z) then 1%nat else 0%nat
  | None => 0%nat
  end.

Lemma fs_tick_count_singleton (t z : Z) :
  fs_tick_count [t] z = otick (Some t) z.
Proof.
  unfold fs_tick_count, otick. cbn [List.filter].
  destruct (bool_decide (t = z)); reflexivity.
Qed.

Lemma fs_tick_count_opt (o : option Z) (z : Z) :
  fs_tick_count (omap id [o]) z = otick o z.
Proof.
  destruct o as [t |]; unfold otick, fs_tick_count;
    cbn [omap list_omap id List.filter].
  - destruct (bool_decide (t = z)); reflexivity.
  - reflexivity.
Qed.

(* ---- [omap] over [seq]: the per-directory segment ---------------------- *)

Lemma omap_seq_snoc {A : Type} (f : nat -> option A) (n : nat) :
  omap f (seq 0 (S n)) = (omap f (seq 0 n) ++ omap f [n])%list.
Proof. rewrite seq_S, omap_app. reflexivity. Qed.

Lemma tick_omap_snoc (f : nat -> option Z) (n : nat) (z : Z) :
  fs_tick_count (omap f (seq 0 (S n))) z
  = (fs_tick_count (omap f (seq 0 n)) z + otick (f n) z)%nat.
Proof.
  rewrite omap_seq_snoc, fs_tick_count_app. f_equal.
  destruct (f n) as [t |] eqn:E; cbn [omap list_omap].
  - rewrite E. unfold fs_tick_count, otick. cbn [List.filter].
    destruct (bool_decide (t = z)); reflexivity.
  - rewrite E. reflexivity.
Qed.

Lemma tick_omap_ext (f g : nat -> option Z) (n : nat) (z : Z) :
  (forall q : nat, (q < n)%nat -> g q = f q) ->
  fs_tick_count (omap g (seq 0 n)) z = fs_tick_count (omap f (seq 0 n)) z.
Proof.
  intros H.
  assert (He : omap g (seq 0 n) = omap f (seq 0 n)).
  { apply omap_ext_in. intros q Hq. apply elem_of_seq in Hq. apply H. lia. }
  rewrite He. reflexivity.
Qed.

(* padding a segment with dead slots does not move its count *)
Lemma tick_omap_pad (f : nat -> option Z) (n d : nat) (z : Z) :
  (forall q : nat, (n <= q < n + d)%nat -> f q = None) ->
  fs_tick_count (omap f (seq 0 (n + d))) z
  = fs_tick_count (omap f (seq 0 n)) z.
Proof.
  induction d as [| d IH]; intros H.
  - rewrite Nat.add_0_r. reflexivity.
  - rewrite Nat.add_succ_r, tick_omap_snoc.
    rewrite (H (n + d)%nat ltac:(lia)). cbn [otick].
    rewrite IH by (intros q Hq; apply H; lia). lia.
Qed.

(* the reuse arm: one slot of an unchanged-width segment moves *)
Lemma tick_omap_upd (f g : nat -> option Z) (n k : nat) (z : Z) :
  (k < n)%nat ->
  (forall q : nat, (q < n)%nat -> q <> k -> g q = f q) ->
  Z.of_nat (fs_tick_count (omap g (seq 0 n)) z)
  = Z.of_nat (fs_tick_count (omap f (seq 0 n)) z)
    + Z.of_nat (otick (g k) z) - Z.of_nat (otick (f k) z).
Proof.
  intros Hk Hext.
  (* split at [k], then once more for the head slot of the tail *)
  assert (Hsplit : forall h : nat -> option Z,
            fs_tick_count (omap h (seq 0 n)) z
            = (fs_tick_count (omap h (seq 0 k)) z + otick (h k) z
               + fs_tick_count (omap h (seq (S k) (n - S k))) z)%nat).
  { intros h.
    replace n with (k + (n - k))%nat at 1 by lia.
    rewrite seq_app, omap_app, fs_tick_count_app.
    replace (n - k)%nat with (S (n - S k))%nat by lia.
    replace (0 + k)%nat with k by lia.
    cbn [seq omap list_omap].
    destruct (h k) as [t |] eqn:E.
    - change (t :: omap h (seq (S k) (n - S k)))
        with ([t] ++ omap h (seq (S k) (n - S k)))%list.
      rewrite fs_tick_count_app, fs_tick_count_singleton. lia.
    - cbn [otick]. lia. }
  rewrite (Hsplit g), (Hsplit f).
  assert (H1 : omap g (seq 0 k) = omap f (seq 0 k)).
  { apply omap_ext_in. intros q Hq. apply elem_of_seq in Hq.
    apply Hext; lia. }
  assert (H2 : omap g (seq (S k) (n - S k)) = omap f (seq (S k) (n - S k))).
  { apply omap_ext_in. intros q Hq. apply elem_of_seq in Hq.
    apply Hext; lia. }
  rewrite H1, H2. lia.
Qed.

(* ---- [mjoin] over [fmap seq]: the whole supply ------------------------- *)

Lemma mjoin_app {A : Type} (l1 l2 : list (list A)) :
  mjoin (l1 ++ l2) = (mjoin l1 ++ mjoin l2)%list.
Proof.
  induction l1 as [| x l1 IH]; [reflexivity |].
  rewrite <- app_comm_cons. rewrite !mjoin_cons, IH, app_assoc. reflexivity.
Qed.

Lemma tick_mjoin_ext (F G : nat -> list Z) (a n : nat) :
  (forall x : nat, (a <= x < a + n)%nat -> G x = F x) ->
  mjoin (G <$> seq a n) = mjoin (F <$> seq a n).
Proof.
  intros H. f_equal. apply list_fmap_ext.
  intros idx x Hx. apply lookup_seq in Hx as [-> Hidx]. apply H. lia.
Qed.

(* one segment of the join moves *)
Lemma tick_mjoin_upd (F G : nat -> list Z) (n m : nat) (z : Z) :
  (m < n)%nat ->
  (forall x : nat, (x < n)%nat -> x <> m -> G x = F x) ->
  Z.of_nat (fs_tick_count (mjoin (G <$> seq 0 n)) z)
  = Z.of_nat (fs_tick_count (mjoin (F <$> seq 0 n)) z)
    + Z.of_nat (fs_tick_count (G m) z) - Z.of_nat (fs_tick_count (F m) z).
Proof.
  intros Hm Hext.
  assert (Hsplit : forall H : nat -> list Z,
            fs_tick_count (mjoin (H <$> seq 0 n)) z
            = (fs_tick_count (mjoin (H <$> seq 0 m)) z
               + fs_tick_count (H m) z
               + fs_tick_count (mjoin (H <$> seq (S m) (n - S m))) z)%nat).
  { intros H.
    replace n with (m + (n - m))%nat at 1 by lia.
    rewrite seq_app, fmap_app, mjoin_app, fs_tick_count_app.
    replace (n - m)%nat with (S (n - S m))%nat by lia.
    replace (0 + m)%nat with m by lia.
    cbn [seq fmap list_fmap]. rewrite mjoin_cons, fs_tick_count_app. lia. }
  rewrite (Hsplit G), (Hsplit F).
  rewrite (tick_mjoin_ext F G 0 m)
    by (intros x Hx; apply Hext; lia).
  rewrite (tick_mjoin_ext F G (S m) (n - S m))
    by (intros x Hx; apply Hext; lia).
  lia.
Qed.

(* two segments move (a dirent effect moves the parent's segment and the
   child's) *)
Lemma tick_mjoin_upd2 (F G : nat -> list Z) (n m1 m2 : nat) (z : Z) :
  (m1 < n)%nat -> (m2 < n)%nat -> m1 <> m2 ->
  (forall x : nat, (x < n)%nat -> x <> m1 -> x <> m2 -> G x = F x) ->
  Z.of_nat (fs_tick_count (mjoin (G <$> seq 0 n)) z)
  = Z.of_nat (fs_tick_count (mjoin (F <$> seq 0 n)) z)
    + (Z.of_nat (fs_tick_count (G m1) z) - Z.of_nat (fs_tick_count (F m1) z))
    + (Z.of_nat (fs_tick_count (G m2) z) - Z.of_nat (fs_tick_count (F m2) z)).
Proof.
  intros Hm1 Hm2 Hne Hext.
  set (H := fun x : nat => if decide (x = m1) then G m1 else F x).
  assert (HH1 : Z.of_nat (fs_tick_count (mjoin (H <$> seq 0 n)) z)
                = Z.of_nat (fs_tick_count (mjoin (F <$> seq 0 n)) z)
                  + Z.of_nat (fs_tick_count (G m1) z)
                  - Z.of_nat (fs_tick_count (F m1) z)).
  { rewrite (tick_mjoin_upd F H n m1 z Hm1)
      by (intros x Hx Hxm; unfold H; rewrite decide_False by exact Hxm;
          reflexivity).
    unfold H. rewrite decide_True by reflexivity. reflexivity. }
  assert (HH2 : Z.of_nat (fs_tick_count (mjoin (G <$> seq 0 n)) z)
                = Z.of_nat (fs_tick_count (mjoin (H <$> seq 0 n)) z)
                  + Z.of_nat (fs_tick_count (G m2) z)
                  - Z.of_nat (fs_tick_count (H m2) z)).
  { rewrite (tick_mjoin_upd H G n m2 z Hm2); [reflexivity |].
    intros x Hx Hxm. unfold H.
    destruct (decide (x = m1)) as [-> | Hx1]; [reflexivity |].
    apply Hext; assumption. }
  assert (HHm2 : H m2 = F m2)
    by (unfold H; rewrite decide_False by (intros ->; exact (Hne eq_refl));
        reflexivity).
  rewrite HH2, HHm2, HH1. lia.
Qed.

(* ====================================================================== *)
(*  8.  REACHABILITY UNDER ONE EDGE MOVE                                   *)
(*                                                                         *)
(*  [FsWf.fs_reachable] is [path_at] from the root; every effect moves at   *)
(*  most one directory ENTRY (an edge), so these are the graph lemmas the   *)
(*  [rd]-delta proofs run on: monotonicity under kept edges, the            *)
(*  insert/delete transfers, and "no in-edges means unreachable".           *)
(* ====================================================================== *)

Definition rch (t : fstree) (r z : Z) : Prop :=
  exists p : list fname, path_at t r p = Some z.

Lemma rch_refl (t : fstree) (r : Z) : rch t r r.
Proof. exists []. apply path_at_nil. Qed.

Lemma rch_snoc (t : fstree) (r j : Z) (f : fname) (z : Z) :
  rch t r j -> tree_ent t j f = Some z -> rch t r z.
Proof.
  intros (p & Hp) He. exists (p ++ [f]).
  rewrite path_at_app, Hp, path_at_singleton. exact He.
Qed.

(* kept edges keep reachability: every [t']-path replays in [t] *)
Lemma rch_mono (t t' : fstree) (r : Z) :
  (forall (j : Z) (f : fname) (w : Z),
     rch t' r j -> rch t r j ->
     tree_ent t' j f = Some w -> tree_ent t j f = Some w) ->
  forall z : Z, rch t' r z -> rch t r z.
Proof.
  intros Hkeep z (p & Hp).
  assert (Hgen : forall (q : list fname) (s : Z),
            path_at t' s q = Some z -> rch t' r s -> rch t r s ->
            rch t r z).
  { induction q as [| f q IH]; intros s Hq Hs' Hs.
    - rewrite path_at_nil in Hq. injection Hq as <-. exact Hs.
    - rewrite path_at_cons in Hq.
      destruct (tree_ent t' s f) as [j |] eqn:He; [| discriminate].
      apply (IH j Hq).
      + exact (rch_snoc t' r s f j Hs' He).
      + exact (rch_snoc t r s f j Hs (Hkeep s f j Hs' Hs He)). }
  exact (Hgen p r Hp (rch_refl t' r) (rch_refl t r)).
Qed.

(* an inserted edge [d -f-> i], with [i]'s own out-edges confined to
   [{i, d}]: everything newly reachable is old or IS [i] *)
Lemma rch_insert_back (t t' : fstree) (r d i : Z) :
  rch t r d ->
  (forall (j : Z) (f : fname) (w : Z),
     rch t r j -> j <> i -> tree_ent t' j f = Some w ->
     tree_ent t j f = Some w \/ w = i) ->
  (forall (f : fname) (w : Z),
     tree_ent t' i f = Some w -> w = i \/ w = d) ->
  forall z : Z, rch t' r z -> rch t r z \/ z = i.
Proof.
  intros Hd Hkeep Hout z (p & Hp).
  assert (Hgen : forall (q : list fname) (s : Z),
            path_at t' s q = Some z -> rch t r s \/ s = i ->
            rch t r z \/ z = i).
  { induction q as [| f q IH]; intros s Hq Hs.
    - rewrite path_at_nil in Hq. injection Hq as <-. exact Hs.
    - rewrite path_at_cons in Hq.
      destruct (tree_ent t' s f) as [j |] eqn:He; [| discriminate].
      apply (IH j Hq).
      destruct (decide (s = i)) as [-> | Hsi].
      + destruct (Hout f j He) as [-> | ->]; [right; reflexivity |].
        left. exact Hd.
      + destruct Hs as [Hs | Hc]; [| exfalso; exact (Hsi Hc)].
        destruct (Hkeep s f j Hs Hsi He) as [Hkept | ->].
        * left. exact (rch_snoc t r s f j Hs Hkept).
        * right. reflexivity. }
  exact (Hgen p r Hp (or_introl (rch_refl t r))).
Qed.

(* a node with no in-edge from any OTHER reachable node is unreachable *)
Lemma rch_no_in (t : fstree) (r i : Z) :
  i <> r ->
  (forall (j : Z) (f : fname),
     rch t r j -> j <> i -> tree_ent t j f <> Some i) ->
  ~ rch t r i.
Proof.
  intros Hr Hno (p & Hp).
  assert (Hgen : forall (n : nat) (q : list fname),
            (length q <= n)%nat -> path_at t r q <> Some i).
  { induction n as [| n IH]; intros q Hlen Hq.
    - destruct q as [| f q]; [| cbn in Hlen; lia].
      rewrite path_at_nil in Hq. injection Hq as Hq. exact (Hr (eq_sym Hq)).
    - destruct q as [| f0 q0] using rev_ind.
      + rewrite path_at_nil in Hq. injection Hq as Hq. exact (Hr (eq_sym Hq)).
      + rewrite path_at_app in Hq.
        destruct (path_at t r q0) as [j |] eqn:Hj; [| discriminate].
        rewrite path_at_singleton in Hq.
        destruct (decide (j = i)) as [-> | Hji].
        * apply (IH q0); [| exact Hj].
          rewrite length_app in Hlen. cbn in Hlen. lia.
        * exact (Hno j f0 (ex_intro _ q0 Hj) Hji Hq). }
  exact (Hgen (length p) p (Nat.le_refl _) Hp).
Qed.

(* deleting the ONLY in-edge of a dots-only directory [i] strands exactly
   [i]: every other reachable node keeps a path that avoids [i] *)
Lemma rch_delete_keep (t t' : fstree) (r d i : Z) (nm : fname) :
  i <> r -> i <> d ->
  tree_ent t d nm = Some i ->
  (forall (j : Z) (f : fname),
     rch t r j -> j <> i -> tree_ent t j f = Some i -> j = d /\ f = nm) ->
  (forall (f : fname) (w : Z),
     tree_ent t i f = Some w -> w = i \/ w = d) ->
  (forall (j : Z) (f : fname) (w : Z),
     rch t r j -> j <> i -> ~ (j = d /\ f = nm) ->
     tree_ent t j f = Some w -> tree_ent t' j f = Some w) ->
  forall z : Z, rch t r z -> z <> i -> rch t' r z.
Proof.
  intros Hr Hdne Hde Hin Hout Hkeep z (p & Hp) Hzi.
  assert (Hgen : forall (n : nat) (q : list fname) (s : Z),
            (length q <= n)%nat -> path_at t s q = Some z ->
            rch t r s -> rch t' r s -> s <> i ->
            rch t' r z).
  { induction n as [| n IH]; intros q s Hlen Hq Hs Hs' Hsi.
    - destruct q as [| f q]; [| cbn in Hlen; lia].
      rewrite path_at_nil in Hq. injection Hq as <-. exact Hs'.
    - destruct q as [| f q'].
      + rewrite path_at_nil in Hq. injection Hq as <-. exact Hs'.
      + rewrite path_at_cons in Hq.
        destruct (tree_ent t s f) as [j |] eqn:He; [| discriminate].
        cbn in Hlen.
        destruct (decide (j = i)) as [-> | Hji].
        * (* the walk stepped onto [i]; it must leave through [i] or [d] *)
          destruct (Hin s f Hs Hsi He) as [-> Hf].
          destruct q' as [| g q''].
          { rewrite path_at_nil in Hq. injection Hq as Hq.
            exfalso. exact (Hzi (eq_sym Hq)). }
          rewrite path_at_cons in Hq.
          destruct (tree_ent t i g) as [w |] eqn:Hw; [| discriminate].
          destruct (Hout g w Hw) as [-> | ->].
          -- (* i -> i: shorten the loop *)
             apply (IH (f :: q'') d); [cbn in Hlen |- *; lia | | exact Hs
                                       | exact Hs' | exact Hsi].
             rewrite path_at_cons, He. exact Hq.
          -- (* i -> d: restart from d *)
             apply (IH q'' d); [cbn in Hlen; lia | exact Hq | exact Hs
                                 | exact Hs' |].
             intros Hc. exact (Hdne (eq_sym Hc)).
        * (* an ordinary kept edge *)
          assert (Hnotdel : ~ (s = d /\ f = nm)).
          { intros [-> ->]. rewrite Hde in He. injection He as He.
            exact (Hji (eq_sym He)). }
          pose proof (Hkeep s f j Hs Hsi Hnotdel He) as He'.
          apply (IH q' j); [lia | exact Hq | | | exact Hji].
          -- exact (rch_snoc t r s f j Hs He).
          -- exact (rch_snoc t' r s f j Hs' He'). }
  exact (Hgen (length p) p r (Nat.le_refl _) Hp (rch_refl t r)
           (rch_refl t' r) (fun Hc => Hr (eq_sym Hc))).
Qed.

(* ====================================================================== *)
(*  9.  [dir_view] AND [dir_first] UNDER THE RECORD MOVES                  *)
(* ====================================================================== *)

(* scanning dead padding finds nothing new *)
Lemma dfirst_pad (p : nat -> bool) (n n' : nat) :
  (n <= n')%nat ->
  (forall q : nat, (n <= q < n')%nat -> p q = false) ->
  dfirst p n' = dfirst p n.
Proof.
  intros Hle Hdead.
  induction n' as [| n' IH].
  - replace n with 0%nat by lia. reflexivity.
  - destruct (decide (n = S n')) as [-> | Hne]; [reflexivity |].
    rewrite dfirst_S, IH by (try lia; intros q Hq; apply Hdead; lia).
    destruct (dfirst p n) as [k |] eqn:E; [reflexivity |].
    rewrite (Hdead n') by lia. reflexivity.
Qed.

Lemma dir_view_dead_ext (data : nat -> list (bv 8)) (n n' : nat) :
  (n <= n')%nat ->
  (forall q : nat, (n <= q < n')%nat -> ~ dir_live data q) ->
  dir_view data n' = dir_view data n.
Proof.
  intros Hle Hdead.
  induction n' as [| n' IH].
  - replace n with 0%nat by lia. reflexivity.
  - destruct (decide (n = S n')) as [-> | Hne]; [reflexivity |].
    rewrite dir_view_S.
    assert (Hnl : dir_wins data n' = false).
    { destruct (dir_wins data n') eqn:Hw; [| reflexivity].
      exfalso. apply (Hdead n'); [lia |].
      exact (dir_wins_live data n' Hw). }
    rewrite Hnl, (right_id ∅ union).
    apply IH; [lia |]. intros q Hq. apply Hdead. lia.
Qed.

(* THE VIEW OF A DIRENT WRITE: writing name [s] at a free (or fresh) slot
   [k] inserts exactly [s ↦ w] -- dirlink's tree delta, the companion of
   [FsTree.dir_view_zero]. *)
Lemma dir_view_write (data data' : nat -> list (bv 8)) (n n' k : nat)
    (s : fname) (w : bv 16) :
  (n <= n')%nat -> (k < n')%nat ->
  dir_written_at data data' k s w ->
  (forall q : nat, (n <= q < n')%nat -> q <> k -> ~ dir_live data' q) ->
  ((k < n)%nat -> ~ dir_live data k) ->
  dir_first data n s = None ->
  w <> bv_0 16 ->
  dir_view data' n' = <[s := bv_unsigned w]> (dir_view data n).
Proof.
  intros Hle Hk Hw Hdead Hfree Hnone Hnz.
  pose proof Hw as (Hz & Hname & Hagree).
  assert (Hmiss : forall q : nat, (q < n)%nat -> q <> k ->
            dir_matchb data' q s = false).
  { intros q Hq Hqk.
    rewrite (dir_matchb_agree data data' q s (Hagree q Hqk)).
    apply dir_matchb_false.
    exact (proj1 (dir_first_None data n s) Hnone q Hq). }
  assert (Hmissq : forall (q : nat) (s0 : fname), (n <= q < n')%nat ->
            q <> k -> dir_matchb data' q s0 = false).
  { intros q s0 Hq Hqk. apply dir_matchb_false.
    intros [Hlv _]. exact (Hdead q Hq Hqk Hlv). }
  apply map_eq. intros s0.
  destruct (decide (s0 = s)) as [-> | Hne].
  - rewrite lookup_insert.
    rewrite dir_view_lookup.
    assert (Hfirst : dir_first data' n' s = Some k).
    { apply dfirst_Some_2; [exact Hk | |].
      - apply dir_matchb_true. split.
        + unfold dir_live. rewrite Hz. exact Hnz.
        + replace (bname 14 (dir_name data' k)) with (dir_bname data' k)
            by reflexivity.
          exact Hname.
      - intros j Hj.
        destruct (Nat.lt_ge_cases j n) as [Hjn | Hjn].
        + exact (Hmiss j Hjn ltac:(lia)).
        + exact (Hmissq j s ltac:(lia) ltac:(lia)). }
    rewrite Hfirst. cbn [fmap option_fmap option_map].
    rewrite Hz. reflexivity.
  - rewrite lookup_insert_ne by congruence.
    rewrite !dir_view_lookup.
    assert (Hmatchk : dir_matchb data' k s0 = false).
    { apply dir_matchb_false. intros [_ Hnm]. apply Hne.
      rewrite <- Hnm.
      replace (bname 14 (dir_name data' k)) with (dir_bname data' k)
        by reflexivity.
      rewrite Hname. reflexivity. }
    assert (Hpad : dir_first data' n' s0 = dir_first data' n s0).
    { unfold dir_first. apply dfirst_pad; [exact Hle |].
      intros q Hq.
      destruct (decide (q = k)) as [-> | Hqk]; [exact Hmatchk |].
      exact (Hmissq q s0 Hq Hqk). }
    assert (Hext : dir_first data' n s0 = dir_first data n s0).
    { unfold dir_first. apply dfirst_ext. intros j Hj.
      destruct (decide (j = k)) as [-> | Hjk].
      - rewrite Hmatchk. symmetry. apply dir_matchb_false.
        intros [Hlv _]. exact (Hfree Hj Hlv).
      - exact (dir_matchb_agree data data' j s0 (Hagree j Hjk)). }
    rewrite Hpad, Hext.
    destruct (dir_first data n s0) as [k0 |] eqn:Hf; [| reflexivity].
    cbn [fmap option_fmap option_map].
    assert (Hk0k : k0 <> k).
    { intros ->. pose proof (dir_first_live _ _ _ _ Hf) as Hlv.
      exact (Hfree (dir_first_lt _ _ _ _ Hf) Hlv). }
    rewrite (dir_inum_agree data data' k0 (Hagree k0 Hk0k)). reflexivity.
Qed.

(* W8's transfer onto a changed directory: the two dot windows are
   untouched and the record count can only have grown *)
Lemma fs_dots_wf_win (P P' : Z -> list (bv 8)) (self : Z)
    (dn dn' : dinode) :
  bv_unsigned (di_size dn) <= bv_unsigned (di_size dn') ->
  dir_win_agree (fs_data_of P dn) (fs_data_of P' dn') 0 ->
  dir_win_agree (fs_data_of P dn) (fs_data_of P' dn') 1 ->
  fs_dots_wf P self dn = true -> fs_dots_wf P' self dn' = true.
Proof.
  intros Hsz H0 H1 H. unfold fs_dots_wf in *. cbv zeta in *.
  rewrite !andb_true_iff in H.
  destruct H as [[[[[Hn Hl0] Hi0] Hb0] Hl1] Hb1].
  rewrite (dir_liveb_agree _ _ 0%nat H0).
  rewrite (dir_liveb_agree _ _ 1%nat H1).
  rewrite (dir_inum_agree _ _ 0%nat H0).
  rewrite (dir_bname_agree' _ _ 0%nat H0).
  rewrite (dir_bname_agree' _ _ 1%nat H1).
  rewrite !andb_true_iff.
  apply Z.leb_le in Hn.
  pose proof (dir_nrec_mono _ _ Hsz).
  repeat split; try assumption.
  apply Z.leb_le. lia.
Qed.

(* ====================================================================== *)
(*  10.  THE DIRENT SPLICE, AT THE FILE-BYTE LEVEL                         *)
(* ====================================================================== *)

(* past the entry list every slot reads the [list Z] inhabitant -- which
   is 1, i.e. [SB_BNO]: a block NO effect ever touches, which is what
   makes the all-[k] agreement premises dischargeable *)
Lemma fs_blk_addr_high (P : Z -> list (bv 8)) (dn : dinode) (k : nat) :
  (FS_MAXFILE <= k)%nat -> fs_blk_addr P dn k = 1.
Proof.
  intros Hk. unfold fs_blk_addr.
  rewrite (proj2 (Nat.ltb_ge k FS_NDIRECT))
    by (unfold FS_NDIRECT, FS_MAXFILE in *; lia).
  rewrite list_lookup_total_alt, lookup_ge_None_2; [reflexivity |].
  rewrite fs_ind_ents_length.
  unfold FS_NDIRECT, FS_MAXFILE, FS_NINDIRECT in *. lia.
Qed.

(* the pointwise block map is unmoved by a metadata-only dinode change
   under an unmoved entry list *)
Lemma fs_blk_addr_same_all (P P' : Z -> list (bv 8)) (dn dn' : dinode) :
  di_addrs dn' = di_addrs dn ->
  fs_ind_ents P' dn' = fs_ind_ents P dn ->
  forall k : nat, fs_blk_addr P' dn' k = fs_blk_addr P dn k.
Proof.
  intros Hmeta Hind k. unfold fs_blk_addr. rewrite Hind, Hmeta. reflexivity.
Qed.

(* THE CHARACTERIZATION: a 16-byte record splice into content block [kb]
   moves exactly record [k]'s window of the directory's byte view.  This
   is the shape [FsTree.dir_zeroed_of_bytes] consumes directly, and the
   written arm feeds [DirView.dir_record_of_name]. *)
Lemma file_byte_splice (P P' : Z -> list (bv 8)) (dn dn' : dinode)
    (k : nat) (de : dirent) :
  di_addrs dn' = di_addrs dn ->
  fs_ind_ents P' dn' = fs_ind_ents P dn ->
  fs_blk_addr P dn (k / 64) <> 0 ->
  P' (fs_blk_addr P dn (k / 64))
  = fs_splice (P (fs_blk_addr P dn (k / 64))) (16 * (k mod 64)) 16
      (fun j => dirent_bytes de !!! j) ->
  (forall k' : nat, k' <> (k / 64)%nat -> fs_blk_addr P dn k' <> 0 ->
     P' (fs_blk_addr P dn k') = P (fs_blk_addr P dn k')) ->
  forall x : nat,
    file_byte (fs_data_of P' dn') x
    = if decide ((16 * k <= x)%nat /\ (x < 16 * k + 16)%nat)
      then dirent_bytes de !!! (x - 16 * k)%nat
      else file_byte (fs_data_of P dn) x.
Proof.
  intros Hmeta Hind Ha Hsp Hother x.
  pose proof (fs_blk_addr_same_all P P' dn dn' Hmeta Hind) as Haddr.
  pose proof (Nat.div_mod_eq x BSIZE) as Hx.
  pose proof (Nat.mod_upper_bound x BSIZE ltac:(unfold BSIZE; lia)) as Hxo.
  pose proof (Nat.div_mod_eq k 64) as Hk.
  pose proof (Nat.mod_upper_bound k 64 ltac:(lia)) as Hko.
  unfold file_byte.
  rewrite !fs_data_of_addr, Haddr.
  destruct (decide ((x / BSIZE)%nat = (k / 64)%nat)) as [Hxb | Hxb].
  - (* the spliced block *)
    rewrite Hxb.
    rewrite (proj2 (Z.eqb_neq _ _) Ha), Hsp.
    rewrite fs_splice_lookup by exact Hxo.
    assert (Hwin : ((16 * (k mod 64) <= x mod BSIZE)%nat
                    /\ (x mod BSIZE < 16 * (k mod 64) + 16)%nat)
                   <-> ((16 * k <= x)%nat /\ (x < 16 * k + 16)%nat)).
    { unfold BSIZE in *. lia. }
    destruct (decide ((16 * (k mod 64) <= x mod BSIZE)%nat
                      /\ (x mod BSIZE < 16 * (k mod 64) + 16)%nat))
      as [Hin | Hout].
    + rewrite decide_True by (apply Hwin; exact Hin).
      f_equal. unfold BSIZE in *. lia.
    + rewrite decide_False by (intros Hc; exact (Hout (proj2 Hwin Hc))).
      reflexivity.
  - (* an untouched block *)
    rewrite decide_False.
    2:{ intros [H1 H2]. apply Hxb.
        assert (Hxeq : x = ((k / 64) * BSIZE
                            + (16 * (k mod 64) + (x - 16 * k)))%nat)
          by (unfold BSIZE in *; lia).
        assert (Hjlt : (16 * (k mod 64) + (x - 16 * k) < BSIZE)%nat)
          by (unfold BSIZE in *; lia).
        rewrite Hxeq. exact (proj1 (nat_block_split _ _ Hjlt)). }
    destruct (fs_blk_addr P dn (x / BSIZE) =? 0) eqn:E; [reflexivity |].
    rewrite Hother; [reflexivity | exact Hxb |].
    apply Z.eqb_neq. exact E.
Qed.

(* ====================================================================== *)
(*  11.  INTRO RULES FOR THE BOOLEAN SWEEPS, AND THE [dok] TRANSFERS       *)
(* ====================================================================== *)

Lemma fs_inodes_dwf_intro (P' : Z -> list (bv 8)) (sb : fs_sb) :
  (forall z : Z, 0 <= z < sb_ninodes sb ->
     bv_unsigned (di_type (fs_dinode P' sb z)) <> 0 ->
     fs_inode_dwf P' sb (fs_dinode P' sb z) = true) ->
  fs_inodes_dwf P' sb = true.
Proof.
  intros H. unfold fs_inodes_dwf.
  rewrite List.forallb_forall. intros x Hin.
  apply elem_of_list_In, elem_of_seq in Hin. cbv beta zeta.
  destruct (bv_unsigned (di_type (fs_dinode P' sb (Z.of_nat x))) =? 0)
    eqn:E; [reflexivity |].
  apply H; [lia | apply Z.eqb_neq; exact E].
Qed.

Lemma fs_dots_all_intro (P' : Z -> list (bv 8)) (sb : fs_sb) :
  (forall z : Z, 0 <= z < sb_ninodes sb ->
     bv_unsigned (di_type (fs_dinode P' sb z)) = T_DIR_z ->
     fs_dots_wf P' z (fs_dinode P' sb z) = true) ->
  fs_dots_all P' sb = true.
Proof.
  intros H. unfold fs_dots_all.
  rewrite List.forallb_forall. intros x Hin.
  apply elem_of_list_In, elem_of_seq in Hin. cbv beta zeta.
  destruct (bv_unsigned (di_type (fs_dinode P' sb (Z.of_nat x)))
            =? T_DIR_z) eqn:E; [| reflexivity].
  apply H; [lia | apply Z.eqb_eq; exact E].
Qed.

Lemma fs_region_wf_intro (P' : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) :
  (forall z : Z, 0 <= z < 16 * Z.of_nat nib -> sb_ninodes sb <= z ->
     bv_unsigned (di_type (fs_dinode P' sb z)) = 0) ->
  (forall z : Z, 0 <= z < 16 * Z.of_nat nib ->
     bv_unsigned (di_type (fs_dinode P' sb z)) = 0 ->
     bv_unsigned (di_nlink (fs_dinode P' sb z)) = 0) ->
  (forall z : Z, 0 <= z < 16 * Z.of_nat nib ->
     bv_unsigned (di_nlink (fs_dinode P' sb z)) <= 32767) ->
  fs_region_wf P' sb nib = true.
Proof.
  intros Hfree Hl3 Hl4. unfold fs_region_wf. apply andb_true_iff. split.
  - unfold fs_region_free.
    rewrite List.forallb_forall. intros x Hin.
    apply elem_of_list_In, elem_of_seq in Hin. cbv beta zeta.
    destruct (Z.ltb_spec (Z.of_nat x) (sb_ninodes sb)) as [Hlt | Hge];
      [reflexivity |].
    apply Z.eqb_eq. apply Hfree; lia.
  - unfold fs_region_nlink.
    rewrite List.forallb_forall. intros x Hin.
    apply elem_of_list_In, elem_of_seq in Hin. cbv beta zeta.
    apply andb_true_iff. split.
    + destruct (bv_unsigned (di_type (fs_dinode P' sb (Z.of_nat x))) =? 0)
        eqn:E; [| reflexivity].
      apply Z.eqb_eq, Hl3; [lia | apply Z.eqb_eq; exact E].
    + apply Z.leb_le, Hl4. lia.
Qed.

Lemma gset_nodup_of_NoDup {A : Type} `{Countable A} (l : list A) :
  NoDup l -> exists s : gset A, gset_nodup l = Some s.
Proof.
  induction l as [| x r IH]; intros Hnd.
  - exists ∅. reflexivity.
  - destruct (IH (NoDup_cons_1_2 x r Hnd)) as (s & Hs).
    exists ({[x]} ∪ s). cbn. rewrite Hs.
    rewrite bool_decide_eq_false_2; [reflexivity |].
    intros Hin. apply (NoDup_cons_1_1 x r Hnd).
    apply (gset_nodup_set r s Hs). exact Hin.
Qed.

(* [fs_inode_dok] reaches the [fio]-based slot machinery through a
   one-link bump: every reader involved ignores [di_nlink] *)
Lemma fs_inode_dok_ok1 (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode) :
  fs_inode_dok P sb dn ->
  fs_inode_ok P sb (di_set_nlink dn (Z_to_bv 16 1)).
Proof.
  intros Hd.
  assert (Hind : fs_ind_ents P (di_set_nlink dn (Z_to_bv 16 1))
                 = fs_ind_ents P dn)
    by (apply fs_ind_ents_meta; reflexivity).
  constructor; cbn [di_type di_size di_addrs di_nlink di_set_nlink].
  - exact (fdi_type P sb dn Hd).
  - change (bv_unsigned (Z_to_bv 16 1)) with 1. lia.
  - exact (fdi_size P sb dn Hd).
  - exact (fdi_direct P sb dn Hd).
  - exact (fdi_direct_zero P sb dn Hd).
  - exact (fdi_ind_zero P sb dn Hd).
  - exact (fdi_ind P sb dn Hd).
  - intros j Hj Hlt. rewrite Hind. exact (fdi_ent P sb dn Hd j Hj Hlt).
  - intros j Hj Hge. rewrite Hind. exact (fdi_ent_zero P sb dn Hd j Hj Hge).
Qed.

Lemma fs_slot_meta (P : Z -> list (bv 8)) (dn dn' : dinode) (k : nat) :
  di_addrs dn' = di_addrs dn -> fs_slot P dn' k = fs_slot P dn k.
Proof.
  intros Ha. unfold fs_slot. rewrite Ha.
  rewrite (fs_blk_addr_meta P dn dn' k Ha). reflexivity.
Qed.

Lemma fs_slot_inj_dok (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode) :
  fs_inode_dok P sb dn -> NoDup (fs_inode_blocks P dn) ->
  fs_slot_inj P dn.
Proof.
  intros Hd Hnd.
  assert (Hmeta : di_addrs (di_set_nlink dn (Z_to_bv 16 1)) = di_addrs dn)
    by reflexivity.
  assert (Hinj : fs_slot_inj P (di_set_nlink dn (Z_to_bv 16 1))).
  { apply (fs_slot_inj_of_nodup P sb).
    - exact (fs_inode_dok_ok1 P sb dn Hd).
    - rewrite (fs_inode_blocks_meta P dn (di_set_nlink dn (Z_to_bv 16 1))
                 Hmeta eq_refl).
      exact Hnd. }
  intros i j Hi Hj Hnz Heq.
  apply (Hinj i j Hi Hj);
    rewrite !(fs_slot_meta P dn _ _ Hmeta); assumption.
Qed.

Lemma fs_inode_blocks_range_dok (P : Z -> list (bv 8)) (sb : fs_sb)
    (dn : dinode) (b : Z) :
  fs_inode_dok P sb dn -> b ∈ fs_inode_blocks P dn ->
  fs_data_start sb <= b < sb_size sb.
Proof.
  intros Hd Hb.
  apply (fs_inode_blocks_range P sb (di_set_nlink dn (Z_to_bv 16 1)) b).
  - exact (fs_inode_dok_ok1 P sb dn Hd).
  - rewrite (fs_inode_blocks_meta P dn (di_set_nlink dn (Z_to_bv 16 1))
               eq_refl eq_refl).
    exact Hb.
Qed.

(* a nonzero slot is a member of the block list -- [fs_inode_blocks_lookup]
   read at membership altitude, transferred to [dok] *)
Lemma fs_slot_elem_dok (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode)
    (k : nat) :
  fs_inode_dok P sb dn -> (k <= FS_MAXFILE)%nat -> fs_slot P dn k <> 0 ->
  fs_slot P dn k ∈ fs_inode_blocks P dn.
Proof.
  intros Hd Hk Hnz.
  assert (Hmeta : di_addrs (di_set_nlink dn (Z_to_bv 16 1)) = di_addrs dn)
    by reflexivity.
  pose proof (fs_inode_blocks_lookup P sb (di_set_nlink dn (Z_to_bv 16 1)) k
                (fs_inode_dok_ok1 P sb dn Hd)) as Hlk.
  rewrite (fs_slot_meta P dn _ k Hmeta) in Hlk.
  rewrite (fs_inode_blocks_meta P dn (di_set_nlink dn (Z_to_bv 16 1))
             eq_refl eq_refl) in Hlk.
  cbn [di_size di_set_nlink] in Hlk.
  apply elem_of_list_lookup. eexists. exact (Hlk Hk Hnz).
Qed.

Lemma forallb_seq_intro (f : nat -> bool) (n : nat) :
    (forall x : nat, (x < n)%nat -> f x = true) ->
    List.forallb f (seq 0 n) = true.
  Proof.
    intros H. rewrite List.forallb_forall. intros x Hin.
    apply elem_of_list_In, elem_of_seq in Hin. apply H. lia.
  Qed.

(* ====================================================================== *)
(*  12.  THE COMMON GROUND OF THE PER-EFFECT PRESERVATION PROOFS           *)
(*                                                                         *)
(*  One section holds the destructed invariant of the OLD view and the     *)
(*  derived facts every effect proof reads.  [Set Default Proof Using      *)
(*  "All"] makes every lemma close over the WHOLE context, so the seven    *)
(*  per-effect files rebind them uniformly (their local notation blocks    *)
(*  apply the seventeen context arguments in declaration order).           *)
(* ====================================================================== *)

Section EffectsWf.
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

  (* the region width, as both spellings *)
  Lemma Hnib16 : 16 * Z.of_nat nib = 16 * (sb_ninodes sb / 16 + 1).
  Proof. rewrite Hnibz. reflexivity. Qed.

  Lemma Hnin_le : sb_ninodes sb <= 16 * (sb_ninodes sb / 16 + 1).
  Proof.
    destruct (fs_sb_ok_geom sb Hok) as (_ & _ & _ & _ & Hle & _). exact Hle.
  Qed.

  Lemma Hnin1 : 1 < sb_ninodes sb.
  Proof.
    destruct (fs_sb_ok_geom sb Hok) as (_ & _ & _ & H1 & _). exact H1.
  Qed.

  Lemma Hnd : NoDup (fs_used_blocks P sb).
  Proof. exact (fs_used_set_nodup P sb u Hu). Qed.

  Lemma dok_at (z : Z) :
    0 <= z < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
    fs_inode_dok P sb (fs_dinode P sb z).
  Proof. intros Hz Hnz. exact (fs_inodes_dwf_spec P sb z HW3 Hz Hnz). Qed.

  Lemma used_elem (z b : Z) :
    0 <= z < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
    b ∈ fs_inode_blocks P (fs_dinode P sb z) -> b ∈ u.
  Proof.
    intros Hz Hnz Hb. apply (fs_used_set_elem P sb u b Hu).
    exact (fs_used_blocks_inode P sb z b Hz Hnz Hb).
  Qed.

  Lemma blocks_range (z b : Z) :
    0 <= z < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
    b ∈ fs_inode_blocks P (fs_dinode P sb z) ->
    fs_data_start sb <= b < sb_size sb.
  Proof.
    intros Hz Hnz Hb.
    exact (fs_inode_blocks_range_dok P sb _ b (dok_at z Hz Hnz) Hb).
  Qed.

  Lemma blocks_cross (z z' b : Z) :
    0 <= z < sb_ninodes sb -> 0 <= z' < sb_ninodes sb -> z <> z' ->
    bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
    bv_unsigned (di_type (fs_dinode P sb z')) <> 0 ->
    b ∈ fs_inode_blocks P (fs_dinode P sb z) ->
    b ∈ fs_inode_blocks P (fs_dinode P sb z') -> False.
  Proof.
    intros Hz Hz' Hne Hnz Hnz' Hb Hb'.
    pose proof (fs_inode_blocks_disjoint P sb z z' Hnd Hz Hz' Hne Hnz Hnz')
      as Hdisj.
    apply (proj1 (elem_of_disjoint _ _) Hdisj b);
      unfold fs_inode_blocks_set; apply elem_of_list_to_set; assumption.
  Qed.

  Lemma slot_inj_at (z : Z) :
    0 <= z < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
    fs_slot_inj P (fs_dinode P sb z).
  Proof.
    intros Hz Hnz.
    apply (fs_slot_inj_dok P sb _ (dok_at z Hz Hnz)).
    exact (fs_used_blocks_nodup_inode P sb z Hnd Hz Hnz).
  Qed.

  Lemma fs_slot_blk (dn : dinode) (k : nat) :
    (k < FS_MAXFILE)%nat -> fs_slot P dn k = fs_blk_addr P dn k.
  Proof.
    intros Hk. unfold fs_slot. rewrite decide_False by lia. reflexivity.
  Qed.

  (* ---- the untouched-inode workhorse --------------------------------- *)

  Lemma inode_untouched (P' : Z -> list (bv 8)) (z : Z) :
    0 <= z < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
    (forall b : Z, b ∈ fs_inode_blocks P (fs_dinode P sb z) -> P' b = P b) ->
    P' SB_BNO = P SB_BNO ->
    fs_ind_ents P' (fs_dinode P sb z) = fs_ind_ents P (fs_dinode P sb z)
    /\ (forall k : nat,
          fs_data_of P' (fs_dinode P sb z) k
          = fs_data_of P (fs_dinode P sb z) k)
    /\ fs_inode_blocks P' (fs_dinode P sb z)
       = fs_inode_blocks P (fs_dinode P sb z)
    /\ fs_inode_dwf P' sb (fs_dinode P sb z)
       = fs_inode_dwf P sb (fs_dinode P sb z).
  Proof.
    intros Hz Hnz Hblk Hsb1.
    set (dn := fs_dinode P sb z).
    assert (Hdok' : fs_inode_dok P sb dn) by (exact (dok_at z Hz Hnz)).
    assert (Hind : fs_ind_ents P' dn = fs_ind_ents P dn).
    { apply fs_ind_ents_ext. intros Hnz12. apply Hblk.
      rewrite <- (fs_slot_max P dn). apply (fs_slot_elem_dok P sb dn);
        [exact Hdok' | lia | rewrite fs_slot_max; exact Hnz12]. }
    split; [exact Hind |].
    split; [| split].
    - intros k. apply (fs_data_of_same P P' dn k Hind).
      intros Hknz.
      destruct (Nat.lt_ge_cases k FS_MAXFILE) as [Hk | Hk].
      + apply Hblk. rewrite <- (fs_slot_blk dn k Hk).
        apply (fs_slot_elem_dok P sb dn);
          [exact Hdok' | lia | rewrite (fs_slot_blk dn k Hk); exact Hknz].
      + rewrite (fs_blk_addr_high P dn k Hk). exact Hsb1.
    - exact (fs_inode_blocks_same P P' dn Hind).
    - exact (fs_inode_dwf_same P P' sb dn Hind).
  Qed.

  (* ...and its consequences at the tree and ticket layers *)

  Lemma node_at_untouched (P' : Z -> list (bv 8)) (z : Z) :
    0 <= z < sb_ninodes sb ->
    fs_dinode P' sb z = fs_dinode P sb z ->
    (bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
     forall k : nat, (k < FS_MAXFILE)%nat ->
       fs_data_of P' (fs_dinode P sb z) k
       = fs_data_of P (fs_dinode P sb z) k) ->
    node_at P' sb z = node_at P sb z.
  Proof.
    intros Hz Hdin Hdata.
    destruct (decide (bv_unsigned (di_type (fs_dinode P sb z)) = 0))
      as [Hfree | Hlive].
    - rewrite node_at_free by (rewrite Hdin; exact Hfree).
      rewrite node_at_free by exact Hfree. reflexivity.
    - rewrite node_at_live by (rewrite Hdin; exact Hlive).
      rewrite node_at_live by exact Hlive.
      unfold fs_file_data. rewrite Hdin. f_equal.
      pose proof (dok_at z Hz Hlive) as Hdz.
      pose proof (fdi_size _ _ _ Hdz) as Hszb.
      pose proof (proj1 (bv_unsigned_in_range _
                    (di_size (fs_dinode P sb z)))) as Hsz0.
      destruct (dir_nrec_bound (bv_unsigned (di_size (fs_dinode P sb z)))
                  Hsz0 Hszb) as [Hnr Hbb].
      apply (node_of_agree _ _ _ FS_MAXFILE);
        [exact (Hdata Hlive) | exact Hnr | exact Hbb].
  Qed.

  Lemma tickets_at_untouched (P' : Z -> list (bv 8)) (z : Z) :
    0 <= z < sb_ninodes sb ->
    fs_dinode P' sb z = fs_dinode P sb z ->
    (bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
     forall k : nat, (k < FS_MAXFILE)%nat ->
       fs_data_of P' (fs_dinode P sb z) k
       = fs_data_of P (fs_dinode P sb z) k) ->
    fs_dir_tickets_at P' sb z = fs_dir_tickets_at P sb z.
  Proof.
    intros Hz Hdin Hdata.
    unfold fs_dir_tickets_at. cbv zeta. rewrite Hdin.
    destruct (bv_unsigned (di_type (fs_dinode P sb z)) =? T_DIR_z)
      eqn:Ety; [| reflexivity].
    assert (Hlive : bv_unsigned (di_type (fs_dinode P sb z)) <> 0).
    { rewrite (proj1 (Z.eqb_eq _ _) Ety). unfold T_DIR_z. lia. }
    pose proof (dok_at z Hz Hlive) as Hdz.
    pose proof (fdi_size _ _ _ Hdz) as Hszb.
    pose proof (proj1 (bv_unsigned_in_range _
                  (di_size (fs_dinode P sb z)))) as Hsz0.
    destruct (dir_nrec_bound (bv_unsigned (di_size (fs_dinode P sb z)))
                Hsz0 Hszb) as [Hnr _].
    unfold fs_dir_tickets. apply omap_ext_in.
    intros k Hk. apply elem_of_seq in Hk.
    assert (Hwin : dir_win_agree (fs_data_of P (fs_dinode P sb z))
                     (fs_data_of P' (fs_dinode P sb z)) k).
    { apply (dir_win_agree_blocks _ _ FS_MAXFILE);
        [exact (Hdata Hlive) | lia]. }
    unfold fs_rec_ticket. cbv zeta.
    rewrite (dir_liveb_agree _ _ k Hwin).
    rewrite (dir_inum_agree _ _ k Hwin).
    reflexivity.
  Qed.

  (* ---- the tree bridge ------------------------------------------------ *)

  Lemma tree_ent_char (Q : Z -> list (bv 8)) (j : Z) (f : fname)
      (w : Z) :
    tree_ent (tree_of_disk Q sb) j f = Some w
    <-> (0 <= j < sb_ninodes sb
         /\ bv_unsigned (di_type (fs_dinode Q sb j)) = T_DIR_z
         /\ dir_view (fs_file_data Q sb j)
              (dir_nrec (bv_unsigned (di_size (fs_dinode Q sb j)))) !! f
            = Some w).
  Proof.
    unfold tree_ent.
    destruct (decide (0 <= j < sb_ninodes sb)) as [Hj | Hj].
    - rewrite (tree_of_disk_lookup Q sb j Hj).
      destruct (decide (bv_unsigned (di_type (fs_dinode Q sb j)) = 0))
        as [Hfree | Hlive].
      + rewrite (node_at_free Q sb j Hfree).
        split; [intros Hc; discriminate | intros (_ & Hty & _)].
        rewrite Hfree in Hty. unfold T_DIR_z in Hty. lia.
      + rewrite (node_at_live Q sb j Hlive). unfold node_of.
        destruct (decide (bv_unsigned (di_type (fs_dinode Q sb j))
                          = T_DIR_z)) as [Hd | Hnd'].
        * cbv beta iota.
          split; [intros Hv | intros (_ & _ & Hv)]; [| exact Hv].
          split; [exact Hj | split; [exact Hd | exact Hv]].
        * cbv beta iota.
          split; [intros Hc; discriminate | intros (_ & Hty & _)].
          exfalso. exact (Hnd' Hty).
    - rewrite (tree_of_disk_lookup_out Q sb j) by lia.
      split; [intros Hc; discriminate | intros (Hc & _); lia].
  Qed.

  (* a live record of a REACHABLE directory steps the tree (uniqueness
     makes the any-match reading exact) *)
  Lemma rd_record_step (j : Z) (k : nat) :
    j ∈ rd ->
    (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb j))))%nat ->
    dir_live (fs_file_data P sb j) k ->
    tree_ent t j (dir_bname (fs_file_data P sb j) k)
    = Some (bv_unsigned (dir_inum (fs_file_data P sb j) k)).
  Proof.
    intros Hj Hk Hlv.
    destruct (proj1 (Hrd j) Hj) as (Hjr & Hjty & _).
    apply (tree_ent_char P j _ _).
    split; [exact Hjr |]. split; [exact Hjty |].
    unfold fs_file_data.
    apply dir_view_live; [| exact Hk | exact Hlv].
    exact (fdo_unique _ _ _ _ (Hdok j Hj)).
  Qed.

  (* the reachable-set membership, unfolded to [rch] *)
  Lemma rd_iff (z : Z) :
    z ∈ rd <-> 0 <= z < sb_ninodes sb
               /\ bv_unsigned (di_type (fs_dinode P sb z)) = T_DIR_z
               /\ rch t ROOTINO z.
  Proof. exact (Hrd z). Qed.

  Lemma root_in_rd : ROOTINO ∈ rd.
  Proof.
    apply rd_iff. split; [pose proof Hnin1; unfold ROOTINO; lia |].
    split; [exact (fs_root_wf_type P sb HW7) |].
    exact (rch_refl t ROOTINO).
  Qed.

  (* a ticket in the reachable supply, from its record *)
  Lemma rtick_of_record (j : Z) (k : nat) :
    j ∈ rd ->
    (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb j))))%nat ->
    dir_live (fs_file_data P sb j) k ->
    bv_unsigned (dir_inum (fs_file_data P sb j) k) <> j ->
    (1 <= fs_rtick P sb rd
            (bv_unsigned (dir_inum (fs_file_data P sb j) k)))%nat.
  Proof.
    intros Hj Hk Hlv Hself.
    destruct (proj1 (Hrd j) Hj) as (Hjr & Hjty & _).
    apply fs_tick_count_elem.
    unfold fs_rtickets.
    apply elem_of_list_join.
    exists (fs_dir_tickets_at P sb j).
    split.
    - unfold fs_dir_tickets_at. cbv zeta.
      rewrite (proj2 (Z.eqb_eq _ _) Hjty).
      unfold fs_dir_tickets.
      apply elem_of_list_omap. exists k.
      split; [apply elem_of_seq; lia |].
      unfold fs_rec_ticket. cbv zeta.
      unfold fs_file_data in Hlv, Hself.
      rewrite (proj2 (dir_liveb_true _ _) Hlv). cbn [andb].
      rewrite bool_decide_eq_false_2 by exact Hself.
      reflexivity.
    - apply elem_of_list_fmap. exists (Z.to_nat j).
      split.
      + cbv beta. rewrite Z2Nat.id by lia.
        rewrite bool_decide_eq_true_2 by exact Hj.
        reflexivity.
      + apply elem_of_seq. lia.
  Qed.


  (* ---- boolean readings of the OLD sweeps, per inum ------------------- *)

  Lemma dwf_bool_at (z : Z) :
    0 <= z < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
    fs_inode_dwf P sb (fs_dinode P sb z) = true.
  Proof.
    intros Hz Hnz.
    pose proof (forallb_seq _ (Z.to_nat (sb_ninodes sb)) (Z.to_nat z) HW3
                  ltac:(lia)) as Hk.
    cbv beta zeta in Hk. rewrite Z2Nat.id in Hk by lia.
    rewrite (proj2 (Z.eqb_neq _ _) Hnz) in Hk. exact Hk.
  Qed.

  Lemma dots_bool_at (z : Z) :
    0 <= z < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb z)) = T_DIR_z ->
    fs_dots_wf P z (fs_dinode P sb z) = true.
  Proof.
    intros Hz Hty.
    pose proof (forallb_seq _ (Z.to_nat (sb_ninodes sb)) (Z.to_nat z) HW8
                  ltac:(lia)) as Hk.
    cbv beta zeta in Hk. rewrite Z2Nat.id in Hk by lia.
    rewrite (proj2 (Z.eqb_eq _ _) Hty) in Hk. exact Hk.
  Qed.

  (* ---- a covered content block is a real data block ------------------- *)

  Lemma fs_nblk_gt (sz : Z) (k : nat) :
    0 <= sz -> Z.of_nat k < fs_nblk sz -> Z.of_nat k * BSIZE_z < sz.
  Proof.
    intros Hsz Hk. unfold fs_nblk in Hk.
    destruct (Z.le_gt_cases sz (Z.of_nat k * BSIZE_z)) as [Hle | Hgt];
      [| exact Hgt].
    exfalso.
    assert (Hd : (sz + (BSIZE_z - 1)) / BSIZE_z < Z.of_nat k + 1).
    { apply Z.div_lt_upper_bound; [unfold BSIZE_z; lia |].
      unfold BSIZE_z in *. lia. }
    unfold fs_nblk in *. lia.
  Qed.

  Lemma blk_addr_covered (z : Z) (k : nat) :
    0 <= z < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
    (k < FS_MAXFILE)%nat ->
    Z.of_nat k < fs_nblk (bv_unsigned (di_size (fs_dinode P sb z))) ->
    fs_data_start sb <= fs_blk_addr P (fs_dinode P sb z) k < sb_size sb.
  Proof.
    intros Hz Hnz Hk Hnb.
    set (dn := fs_dinode P sb z).
    pose proof (fs_inode_dok_ok1 P sb dn (dok_at z Hz Hnz)) as Hok1.
    pose proof (fs_inode_ok_blk P sb (di_set_nlink dn (Z_to_bv 16 1)) k Hok1)
      as Hblk.
    cbn [di_size di_set_nlink] in Hblk.
    rewrite (fs_blk_addr_meta P dn (di_set_nlink dn (Z_to_bv 16 1)) k
               eq_refl) in Hblk.
    apply Hblk; [exact Hk |].
    apply fs_nblk_gt; [| exact Hnb].
    exact (proj1 (bv_unsigned_in_range _ _)).
  Qed.

  (* ---- tree entries under an untouched decode ------------------------- *)

  Lemma tree_ent_nondir (Q : Z -> list (bv 8)) (j : Z) (f : fname) :
    bv_unsigned (di_type (fs_dinode Q sb j)) <> T_DIR_z ->
    tree_ent (tree_of_disk Q sb) j f = None.
  Proof.
    intros Hnd'.
    destruct (tree_ent (tree_of_disk Q sb) j f) as [w |] eqn:He;
      [| reflexivity].
    apply (tree_ent_char Q j f w) in He.
    destruct He as (_ & Hty & _). exfalso. exact (Hnd' Hty).
  Qed.

  Lemma tree_ent_untouched (P' : Z -> list (bv 8)) (j : Z)
      (f : fname) :
    (0 <= j < sb_ninodes sb -> node_at P' sb j = node_at P sb j) ->
    tree_ent (tree_of_disk P' sb) j f = tree_ent t j f.
  Proof.
    intros Hnode.
    destruct (decide (0 <= j < sb_ninodes sb)) as [Hj | Hj].
    - unfold t. rewrite !(tree_ent_of_disk _ sb j f Hj), (Hnode Hj).
      reflexivity.
    - unfold tree_ent, t.
      rewrite !(tree_of_disk_lookup_out _ sb j) by lia. reflexivity.
  Qed.

  (* ---- the fdo bundle survives an untouched decode -------------------- *)

  Lemma dir_ok_untouched (P' : Z -> list (bv 8)) (z : Z) :
    z ∈ rd ->
    fs_dinode P' sb z = fs_dinode P sb z ->
    (forall k : nat, (k < FS_MAXFILE)%nat ->
       fs_data_of P' (fs_dinode P sb z) k
       = fs_data_of P (fs_dinode P sb z) k) ->
    (* a KILLED inode (live before, free after) must have been
       unreachable -- vacuous for the type-preserving effects, the
       whole point for [eff_free_inode] *)
    (forall w : Z, 0 <= w < sb_ninodes sb ->
       bv_unsigned (di_type (fs_dinode P sb w)) <> 0 ->
       bv_unsigned (di_type (fs_dinode P' sb w)) = 0 ->
       ~ rch t ROOTINO w) ->
    fs_dir_ok P' sb z (fs_dinode P' sb z).
  Proof.
    intros Hz Hdin Hdata Htys.
    destruct (proj1 (Hrd z) Hz) as (Hzr & Hzty & _).
    assert (Hlive : bv_unsigned (di_type (fs_dinode P sb z)) <> 0)
      by (rewrite Hzty; unfold T_DIR_z; lia).
    pose proof (dok_at z Hzr Hlive) as Hdz.
    pose proof (fdi_size _ _ _ Hdz) as Hszb.
    pose proof (proj1 (bv_unsigned_in_range _
                  (di_size (fs_dinode P sb z)))) as Hsz0.
    destruct (dir_nrec_bound (bv_unsigned (di_size (fs_dinode P sb z)))
                Hsz0 Hszb) as [Hnr _].
    assert (Hwin : forall r : nat,
              (r < dir_nrec (bv_unsigned (di_size (fs_dinode P sb z))))%nat ->
              dir_win_agree (fs_data_of P (fs_dinode P sb z))
                (fs_data_of P' (fs_dinode P sb z)) r).
    { intros r Hr.
      apply (dir_win_agree_blocks _ _ FS_MAXFILE); [exact Hdata | lia]. }
    rewrite Hdin.
    destruct (Hdok z Hz) as [Hgr Hent Huq Hdot Hdd].
    constructor.
    - exact Hgr.
    - intros k Hk Hlive'.
      assert (Hlv : dir_live (fs_data_of P (fs_dinode P sb z)) k).
      { unfold dir_live in *.
        rewrite (dir_inum_agree _ _ k (Hwin k Hk)) in Hlive'. exact Hlive'. }
      destruct (Hent k Hk Hlv) as [Hran Hty].
      rewrite (dir_inum_agree _ _ k (Hwin k Hk)).
      split; [exact Hran |].
      intros Hkill.
      assert (Hwr : 0 <= bv_unsigned
                           (dir_inum (fs_data_of P (fs_dinode P sb z)) k)
                    < sb_ninodes sb) by lia.
      apply (Htys _ Hwr Hty Hkill).
      apply (rch_snoc t ROOTINO z
               (dir_bname (fs_data_of P (fs_dinode P sb z)) k)).
      { destruct (proj1 (Hrd z) Hz) as (_ & _ & Hre). exact Hre. }
      exact (rd_record_step z k Hz Hk Hlv).
    - exact (dir_names_unique_agree _ _ _ Hwin Huq).
    - rewrite (dir_view_agree _ _ _ Hwin). exact Hdot.
    - rewrite (dir_view_agree _ _ _ Hwin). exact Hdd.
  Qed.

  Lemma dots_only_untouched (P' : Z -> list (bv 8)) (dn : dinode) :
    bv_unsigned (di_size dn) <= Z.of_nat FS_MAXFILE * BSIZE_z ->
    (forall k : nat, (k < FS_MAXFILE)%nat ->
       fs_data_of P' dn k = fs_data_of P dn k) ->
    fs_dir_dots_only P dn -> fs_dir_dots_only P' dn.
  Proof.
    intros Hcap Hdata Honly k Hk2 Hkn Hlive.
    apply (Honly k Hk2 Hkn).
    unfold dir_live in *.
    pose proof (proj1 (bv_unsigned_in_range _ (di_size dn))) as Hsz0.
    destruct (dir_nrec_bound _ Hsz0 Hcap) as [Hnr _].
    assert (Hwin : dir_win_agree (fs_data_of P dn) (fs_data_of P' dn) k).
    { apply (dir_win_agree_blocks _ _ FS_MAXFILE); [exact Hdata | lia]. }
    rewrite (dir_inum_agree _ _ k Hwin) in Hlive. exact Hlive.
  Qed.

  Lemma root_wf_untouched (P' : Z -> list (bv 8)) :
    fs_dinode P' sb ROOTINO = fs_dinode P sb ROOTINO ->
    (forall k : nat, (k < FS_MAXFILE)%nat ->
       fs_data_of P' (fs_dinode P sb ROOTINO) k
       = fs_data_of P (fs_dinode P sb ROOTINO) k) ->
    fs_root_wf P' sb = true.
  Proof.
    intros Hdin Hdata.
    pose proof (fs_root_wf_type P sb HW7) as Hty.
    assert (Hlive : bv_unsigned (di_type (fs_dinode P sb ROOTINO)) <> 0)
      by (rewrite Hty; unfold T_DIR_z; lia).
    pose proof Hnin1 as Hn1.
    pose proof (dok_at ROOTINO ltac:(unfold ROOTINO; lia) Hlive) as Hdr.
    pose proof (fdi_size _ _ _ Hdr) as Hszb.
    pose proof (proj1 (bv_unsigned_in_range _
                  (di_size (fs_dinode P sb ROOTINO)))) as Hsz0.
    destruct (dir_nrec_bound (bv_unsigned (di_size (fs_dinode P sb ROOTINO)))
                Hsz0 Hszb) as [Hnr _].
    assert (Hwin : forall r : nat,
              (r < dir_nrec
                     (bv_unsigned (di_size (fs_dinode P sb ROOTINO))))%nat ->
              dir_win_agree (fs_data_of P (fs_dinode P sb ROOTINO))
                (fs_data_of P' (fs_dinode P sb ROOTINO)) r).
    { intros r Hr.
      apply (dir_win_agree_blocks _ _ FS_MAXFILE); [exact Hdata | lia]. }
    unfold fs_root_wf in *. cbv zeta in *. rewrite Hdin.
    apply andb_true_iff in HW7. destruct HW7 as [Hty' Hdd].
    apply andb_true_iff. split; [exact Hty' |].
    rewrite (dir_first_agree _ _ _ DOTDOT Hwin).
    destruct (dir_first (fs_data_of P (fs_dinode P sb ROOTINO))
                (dir_nrec (bv_unsigned (di_size (fs_dinode P sb ROOTINO))))
                DOTDOT) as [k |] eqn:Hf; [| exact Hdd].
    rewrite (dir_inum_agree _ _ k (Hwin k (dir_first_lt _ _ _ _ Hf))).
    exact Hdd.
  Qed.

  (* ---- reachability transfer under unchanged edges -------------------- *)

  Lemma reach_iff_of_ent (P' : Z -> list (bv 8)) :
    (forall (j : Z) (f : fname),
       tree_ent (tree_of_disk P' sb) j f = tree_ent t j f) ->
    forall z : Z, fs_reachable P' sb z <-> fs_reachable P sb z.
  Proof.
    intros He z. unfold fs_reachable. split.
    - intros H.
      apply (rch_mono t (tree_of_disk P' sb) ROOTINO); [| exact H].
      intros j f w _ _ Hw. rewrite (He j f) in Hw. exact Hw.
    - intros H.
      apply (rch_mono (tree_of_disk P' sb) t ROOTINO); [| exact H].
      intros j f w _ _ Hw. rewrite (He j f). exact Hw.
  Qed.


  (* ==================================================================== *)
  (*  14.  SHARED MACHINERY: THE USED SET AND THE BITMAP UNDER A MOVE      *)
  (* ==================================================================== *)

  Lemma elem_mjoin_seq (F : nat -> list Z) (a n : nat) (b : Z) :
    b ∈ mjoin (F <$> seq a n)
    <-> exists x : nat, (a <= x < a + n)%nat /\ b ∈ F x.
  Proof.
    rewrite elem_of_list_join. split.
    - intros (l & Hb & Hl).
      apply elem_of_list_fmap in Hl as (x & -> & Hx).
      apply elem_of_seq in Hx. exists x. split; [lia | exact Hb].
    - intros (x & Hx & Hb). exists (F x). split; [exact Hb |].
      apply elem_of_list_fmap. exists x.
      split; [reflexivity | apply elem_of_seq; lia].
  Qed.

  Lemma NoDup_mjoin_sub (F G : nat -> list Z) :
    forall (n a : nat),
    (forall x : nat, (a <= x < a + n)%nat -> G x = F x \/ G x = []) ->
    NoDup (mjoin (F <$> seq a n)) -> NoDup (mjoin (G <$> seq a n)).
  Proof.
    induction n as [| n IH]; intros a Hsub Hnd'.
    - cbn. apply NoDup_nil_2.
    - cbn [seq fmap list_fmap] in Hnd' |- *.
      rewrite mjoin_cons in Hnd' |- *.
      apply stdpp.list_relations.NoDup_app in Hnd'.
      destruct Hnd' as (Ha & Hdisj & Hrest).
      apply stdpp.list_relations.NoDup_app.
      assert (Hsub' : forall b : Z,
                b ∈ mjoin (G <$> seq (S a) n) ->
                b ∈ mjoin (F <$> seq (S a) n)).
      { intros b Hb. apply elem_mjoin_seq in Hb as (x & Hx & Hbx).
        apply elem_mjoin_seq. exists x. split; [lia |].
        destruct (Hsub x ltac:(lia)) as [He | He]; rewrite He in Hbx.
        - exact Hbx.
        - exfalso. exact (proj1 (elem_of_nil b) Hbx). }
      destruct (Hsub a ltac:(lia)) as [He | He]; rewrite He.
      + split; [exact Ha |]. split.
        * intros b Hb Hb'. exact (Hdisj b Hb (Hsub' b Hb')).
        * apply (IH (S a)); [| exact Hrest].
          intros x Hx. apply Hsub. lia.
      + split; [apply NoDup_nil_2 |]. split.
        * intros b Hb. exfalso. exact (proj1 (elem_of_nil b) Hb).
        * apply (IH (S a)); [| exact Hrest].
          intros x Hx. apply Hsub. lia.
  Qed.

  Lemma mjoin_seq_split (F : nat -> list Z) (n m : nat) :
    (m < n)%nat ->
    mjoin (F <$> seq 0 n)
    = (mjoin (F <$> seq 0 m) ++ F m
       ++ mjoin (F <$> seq (S m) (n - S m)))%list.
  Proof.
    intros Hm.
    replace n with (m + (n - m))%nat at 1 by lia.
    rewrite seq_app, fmap_app, mjoin_app.
    replace (n - m)%nat with (S (n - S m))%nat by lia.
    replace (0 + m)%nat with m by lia.
    cbn [seq fmap list_fmap]. rewrite mjoin_cons. reflexivity.
  Qed.

  (* the old bitmap block's own bit set, read against W5 *)
  Lemma old_bit_iff (b : Z) :
    0 <= b < sb_size sb ->
    (b ∈ fs_bmap_set BSIZE (P (sb_bmapstart sb))
     <-> (b < fs_data_start sb \/ b ∈ u)).
  Proof.
    intros Hb.
    pose proof (sbo_one_bitmap sb Hok) as Hone.
    rewrite fs_bmap_set_elem.
    rewrite <- (fs_bitmap_wf_spec P sb u b Hbm Hb).
    rewrite BSIZE_z_nat.
    intuition lia.
  Qed.

  Lemma bitmap_wf_of_set (P' : Z -> list (bv 8)) (u'' S' : gset Z) :
    P' (sb_bmapstart sb) = bm_bytes BSIZE S' ->
    (forall b : Z, 0 <= b < sb_size sb ->
       (b ∈ S' <-> (b < fs_data_start sb \/ b ∈ u''))) ->
    fs_bitmap_wf P' sb u'' = true.
  Proof.
    intros Hbk Hiff. apply fs_bitmap_wf_intro. intros b Hb.
    pose proof (sbo_one_bitmap sb Hok) as Hone.
    rewrite Hbk.
    rewrite fs_bit_bm_bytes by (rewrite BSIZE_z_nat; lia).
    rewrite bool_decide_eq_true. exact (Hiff b Hb).
  Qed.

  (* the used set after DROPPING one inode's blocks (trunc / free) *)
  Lemma used_drop (P' : Z -> list (bv 8)) (i : Z) :
    0 <= i < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
    (forall z : Z, 0 <= z < sb_ninodes sb -> z <> i ->
       (if bv_unsigned (di_type (fs_dinode P' sb z)) =? 0 then []
        else fs_inode_blocks P' (fs_dinode P' sb z))
       = (if bv_unsigned (di_type (fs_dinode P sb z)) =? 0 then []
          else fs_inode_blocks P (fs_dinode P sb z))) ->
    (if bv_unsigned (di_type (fs_dinode P' sb i)) =? 0 then []
     else fs_inode_blocks P' (fs_dinode P' sb i)) = [] ->
    exists u'' : gset Z,
      fs_used_set P' sb = Some u''
      /\ (forall b : Z,
            b ∈ u'' <-> b ∈ u
                        /\ ~ b ∈ fs_inode_blocks P (fs_dinode P sb i)).
  Proof.
    intros Hi Hlive Hsame Hnil.
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
    assert (HGF : forall x : nat, (0 <= x < 0 + n)%nat ->
              G x = F x \/ G x = []).
    { intros x Hx.
      destruct (decide (Z.of_nat x = i)) as [Heq | Hne].
      - right. unfold G. cbv zeta. rewrite Heq. exact Hnil.
      - left. unfold G, F. cbv zeta.
        apply Hsame; [unfold n in Hx; lia | exact Hne]. }
    assert (Hnd' : NoDup (fs_used_blocks P' sb)).
    { rewrite HGold. apply (NoDup_mjoin_sub F G n 0%nat HGF).
      rewrite <- HFold. exact Hnd. }
    destruct (gset_nodup_of_NoDup (fs_used_blocks P' sb) Hnd')
      as (u'' & Hu'').
    exists u''. split; [exact Hu'' |].
    intros b.
    rewrite (gset_nodup_set _ _ Hu'' b).
    rewrite HGold, (elem_mjoin_seq G 0 n b).
    split.
    - intros (x & Hx & Hbx).
      destruct (decide (Z.of_nat x = i)) as [Heq | Hne].
      { exfalso. unfold G in Hbx. cbv zeta in Hbx.
        rewrite Heq, Hnil in Hbx.
        exact (proj1 (elem_of_nil b) Hbx). }
      destruct (HGF x Hx) as [He | He]; rewrite He in Hbx.
      2:{ exfalso. exact (proj1 (elem_of_nil b) Hbx). }
      assert (Hbu : b ∈ fs_used_blocks P sb).
      { rewrite HFold. apply (elem_mjoin_seq F 0 n b).
        exists x. split; [exact Hx | exact Hbx]. }
      split.
      + apply (fs_used_set_elem P sb u b Hu). exact Hbu.
      + intros Hbi.
        unfold F in Hbx. cbv zeta in Hbx.
        destruct (bv_unsigned (di_type (fs_dinode P sb (Z.of_nat x))) =? 0)
          eqn:Ez.
        { exact (proj1 (elem_of_nil b) Hbx). }
        exact (blocks_cross (Z.of_nat x) i b
                 ltac:(unfold n in Hx; lia) Hi Hne
                 (proj1 (Z.eqb_neq _ _) Ez) Hlive Hbx Hbi).
    - intros (Hbu & Hbni).
      apply (fs_used_set_elem P sb u b Hu) in Hbu.
      rewrite HFold in Hbu. apply (elem_mjoin_seq F 0 n b) in Hbu.
      destruct Hbu as (x & Hx & Hbx).
      assert (Hne : Z.of_nat x <> i).
      { intros Heq. apply Hbni.
        unfold F in Hbx. cbv zeta in Hbx. rewrite Heq in Hbx.
        rewrite (proj2 (Z.eqb_neq _ _) Hlive) in Hbx. exact Hbx. }
      exists x. split; [exact Hx |].
      destruct (HGF x Hx) as [He | He].
      + rewrite He. exact Hbx.
      + exfalso. unfold G in He. cbv zeta in He.
        pose proof (Hsame (Z.of_nat x) ltac:(unfold n in Hx; lia) Hne)
          as Hs'.
        rewrite He in Hs'. unfold F in Hbx. cbv zeta in Hbx.
        rewrite <- Hs' in Hbx.
        exact (proj1 (elem_of_nil b) Hbx).
  Qed.

  (* every ticket comes from a live record of a reachable directory *)
  Lemma rtick_inv (tk : Z) :
    tk ∈ fs_rtickets P sb rd ->
    exists (j : Z) (k : nat),
      j ∈ rd
      /\ (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb j))))%nat
      /\ dir_live (fs_file_data P sb j) k
      /\ bv_unsigned (dir_inum (fs_file_data P sb j) k) = tk
      /\ tk <> j.
  Proof.
    intros Htk. unfold fs_rtickets in Htk.
    apply elem_of_list_join in Htk as (l & Hl & Hls).
    apply elem_of_list_fmap in Hls as (x & -> & _).
    revert Hl. cbv beta.
    destruct (bool_decide (Z.of_nat x ∈ rd)) eqn:Hg;
      [| intros Hl; exfalso; exact (proj1 (elem_of_nil tk) Hl)].
    apply bool_decide_eq_true_1 in Hg.
    unfold fs_dir_tickets_at. cbv zeta.
    destruct (bv_unsigned (di_type (fs_dinode P sb (Z.of_nat x)))
              =? T_DIR_z) eqn:Ety;
      [| intros Hl; exfalso; exact (proj1 (elem_of_nil tk) Hl)].
    intros Hl.
    apply elem_of_list_omap in Hl as (k & Hk & Hkt).
    apply elem_of_seq in Hk.
    unfold fs_rec_ticket in Hkt. cbv zeta in Hkt.
    destruct (dir_liveb (fs_data_of P (fs_dinode P sb (Z.of_nat x))) k
              && negb (bool_decide
                         (bv_unsigned
                            (dir_inum
                               (fs_data_of P (fs_dinode P sb (Z.of_nat x)))
                               k)
                          = Z.of_nat x))) eqn:Hgd; [| discriminate].
    injection Hkt as <-.
    apply andb_true_iff in Hgd as [Hlv Hnself].
    apply negb_true_iff, bool_decide_eq_false in Hnself.
    exists (Z.of_nat x), k.
    split; [exact Hg |]. split; [lia |].
    split; [exact (proj1 (dir_liveb_true _ _) Hlv) |].
    split; [reflexivity | exact Hnself].
  Qed.

  (* an unreachable inum bears no ticket *)
  Lemma rtick_unreachable (w : Z) :
    ~ fs_reachable P sb w -> fs_rtick P sb rd w = 0%nat.
  Proof.
    intros Hun. apply fs_tick_count_zero.
    intros tk Htk Heq. subst tk.
    destruct (rtick_inv w Htk) as (j & k & Hj & Hk & Hlv & Hin & Hne).
    apply Hun.
    destruct (proj1 (Hrd j) Hj) as (_ & _ & Hre).
    rewrite <- Hin.
    apply (rch_snoc t ROOTINO j
             (dir_bname (fs_data_of P (fs_dinode P sb j)) k)); [exact Hre |].
    exact (rd_record_step j k Hj Hk Hlv).
  Qed.

  (* a FREE inum bears no ticket (reachable dirs name only live inodes) *)
  Lemma rtick_free (w : Z) :
    0 <= w < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb w)) = 0 ->
    fs_rtick P sb rd w = 0%nat.
  Proof.
    intros Hw Hfree. apply fs_tick_count_zero.
    intros tk Htk Heq. subst tk.
    destruct (rtick_inv w Htk) as (j & k & Hj & Hk & Hlv & Hin & Hne).
    destruct (proj1 (Hrd j) Hj) as (Hjr & _ & _).
    destruct (fdo_ent _ _ _ _ (Hdok j Hj) k Hk Hlv) as (_ & Hty).
    unfold fs_file_data in Hin. rewrite Hin in Hty. exact (Hty Hfree).
  Qed.

  (* ---- the zeroed record's readers ------------------------------------ *)

  Lemma zeroed_ind_ents (Q : Z -> list (bv 8)) (dn0 : dinode) :
    di_addrs dn0 = replicate 13 (bv_0 32) ->
    fs_ind_ents Q dn0 = replicate FS_NINDIRECT 0.
  Proof.
    intros Ha. unfold fs_ind_ents. rewrite Ha.
    rewrite lookup_total_replicate_2 by lia.
    reflexivity.
  Qed.

  Lemma zeroed_blocks_nil (Q : Z -> list (bv 8)) (dn0 : dinode) :
    di_size dn0 = bv_0 32 ->
    fs_inode_blocks Q dn0 = [].
  Proof.
    intros Hs. unfold fs_inode_blocks. cbv zeta. rewrite Hs. reflexivity.
  Qed.

  Lemma zeroed_dwf (Q : Z -> list (bv 8)) (dn0 : dinode) :
    di_size dn0 = bv_0 32 ->
    di_addrs dn0 = replicate 13 (bv_0 32) ->
    (bv_unsigned (di_type dn0) = T_DIR_z
     \/ bv_unsigned (di_type dn0) = T_FILE_z
     \/ bv_unsigned (di_type dn0) = T_DEVICE_z) ->
    fs_inode_dwf Q sb dn0 = true.
  Proof.
    intros Hs Ha Hty.
    unfold fs_inode_dwf. cbv zeta.
    rewrite (zeroed_ind_ents Q dn0 Ha), Hs, Ha.
    destruct Hty as [Hty | [Hty | Hty]]; rewrite Hty; reflexivity.
  Qed.


  (* ==================================================================== *)
  (*  17.  SHARED MACHINERY: THE DIRENT RECORD MOVES                       *)
  (* ==================================================================== *)

  Lemma fs_nblk_between (sz sz' : Z) :
    0 < sz -> sz <= sz' -> sz' <= fs_nblk sz * BSIZE_z ->
    fs_nblk sz' = fs_nblk sz.
  Proof.
    intros H0 Hle Hup.
    assert (Hmono : fs_nblk sz <= fs_nblk sz').
    { unfold fs_nblk. apply Z.div_le_mono; unfold BSIZE_z; lia. }
    assert (Hcap : fs_nblk sz' <= fs_nblk sz); [| lia].
    unfold fs_nblk at 1.
    assert (Hlt : (sz' + (BSIZE_z - 1)) / BSIZE_z < fs_nblk sz + 1);
      [| lia].
    apply Z.div_lt_upper_bound; unfold BSIZE_z in *; lia.
  Qed.

  (* the record window inside the splice, read back as [dir_written_at] *)
  Lemma dirent_written (P' : Z -> list (bv 8)) (dnd dnd' : dinode)
      (k : nat) (w : bv 16) (name : fname) :
    (length name <= 14)%nat -> nonul name ->
    di_addrs dnd' = di_addrs dnd ->
    fs_ind_ents P' dnd' = fs_ind_ents P dnd ->
    fs_blk_addr P dnd (k / 64) <> 0 ->
    P' (fs_blk_addr P dnd (k / 64))
    = fs_splice (P (fs_blk_addr P dnd (k / 64))) (16 * (k mod 64)) 16
        (fun j => dirent_bytes (de_of_name w name) !!! j) ->
    (forall k' : nat, k' <> (k / 64)%nat -> fs_blk_addr P dnd k' <> 0 ->
       P' (fs_blk_addr P dnd k') = P (fs_blk_addr P dnd k')) ->
    dir_written_at (fs_data_of P dnd) (fs_data_of P' dnd') k name w.
  Proof.
    intros Hlen Hnn Hmeta Hind Ha Hsp Hother.
    pose proof (file_byte_splice P P' dnd dnd' k (de_of_name w name)
                  Hmeta Hind Ha Hsp Hother) as Hbytes.
    assert (Hwinb : forall j : nat, (j < 16)%nat ->
              file_byte (fs_data_of P' dnd') (16 * k + j)%nat
              = dirent_bytes (de_of_name w name) !!! j).
    { intros j Hj. rewrite (Hbytes (16 * k + j)%nat).
      rewrite decide_True by lia.
      f_equal. lia. }
    destruct (dir_record_of_name (fs_data_of P' dnd') k w name Hlen Hnn
                Hwinb) as (Hinum & Hbn).
    split; [exact Hinum |]. split; [exact Hbn |].
    intros q Hq j Hj.
    rewrite (Hbytes (16 * q + j)%nat).
    rewrite decide_False; [reflexivity |].
    intros [H1 H2]. apply Hq. lia.
  Qed.

  Lemma dirent_zeroed (P' : Z -> list (bv 8)) (dnd dnd' : dinode)
      (k : nat) :
    di_addrs dnd' = di_addrs dnd ->
    fs_ind_ents P' dnd' = fs_ind_ents P dnd ->
    fs_blk_addr P dnd (k / 64) <> 0 ->
    P' (fs_blk_addr P dnd (k / 64))
    = fs_splice (P (fs_blk_addr P dnd (k / 64))) (16 * (k mod 64)) 16
        (fun j => dirent_bytes dirent_zero !!! j) ->
    (forall k' : nat, k' <> (k / 64)%nat -> fs_blk_addr P dnd k' <> 0 ->
       P' (fs_blk_addr P dnd k') = P (fs_blk_addr P dnd k')) ->
    dir_zeroed_at (fs_data_of P dnd) (fs_data_of P' dnd') k
    /\ (forall q : nat, q <> k ->
          dir_win_agree (fs_data_of P dnd) (fs_data_of P' dnd') q).
  Proof.
    intros Hmeta Hind Ha Hsp Hother.
    pose proof (file_byte_splice P P' dnd dnd' k dirent_zero
                  Hmeta Hind Ha Hsp Hother) as Hbytes.
    split.
    - apply (dir_zeroed_of_bytes _ _ k 16 dirent_zero); [lia | lia | |].
      + exact dirent_zero_free.
      + exact Hbytes.
    - intros q Hq j Hj.
      rewrite (Hbytes (16 * q + j)%nat).
      rewrite decide_False; [reflexivity |].
      intros [H1 H2]. apply Hq. lia.
  Qed.

  (* one written slot's ticket-count move, both arms in one statement *)
  Lemma tick_omap_write (f g : nat -> option Z) (n n' k : nat)
      (z : Z) :
    (n <= n')%nat -> (k < n')%nat ->
    (forall q : nat, (q < n)%nat -> q <> k -> g q = f q) ->
    (forall q : nat, (n <= q < n')%nat -> q <> k -> g q = None) ->
    ((k < n)%nat -> f k = None) ->
    Z.of_nat (fs_tick_count (omap g (seq 0 n')) z)
    = Z.of_nat (fs_tick_count (omap f (seq 0 n)) z)
      + Z.of_nat (otick (g k) z).
  Proof.
    intros Hle Hk Hext Hdead Hfree.
    set (f' := fun q : nat => if (q <? n)%nat then f q else None).
    assert (Hf'n : fs_tick_count (omap f' (seq 0 n')) z
                   = fs_tick_count (omap f (seq 0 n)) z).
    { replace n' with (n + (n' - n))%nat by lia.
      rewrite (tick_omap_pad f' n (n' - n)%nat z)
        by (intros q Hq; unfold f';
            rewrite (proj2 (Nat.ltb_ge q n)) by lia; reflexivity).
      apply tick_omap_ext. intros q Hq. unfold f'.
      rewrite (proj2 (Nat.ltb_lt q n)) by lia. reflexivity. }
    assert (Hupd : Z.of_nat (fs_tick_count (omap g (seq 0 n')) z)
                   = Z.of_nat (fs_tick_count (omap f' (seq 0 n')) z)
                     + Z.of_nat (otick (g k) z)
                     - Z.of_nat (otick (f' k) z)).
    { apply (tick_omap_upd f' g n' k z Hk).
      intros q Hq Hqk. unfold f'.
      destruct (Nat.ltb_spec q n) as [Hqn | Hqn].
      - exact (Hext q Hqn Hqk).
      - apply Hdead; [lia | exact Hqk]. }
    assert (Hf'k : otick (f' k) z = 0%nat).
    { unfold f'. destruct (Nat.ltb_spec k n) as [Hkn | Hkn].
      - rewrite (Hfree Hkn). reflexivity.
      - reflexivity. }
    rewrite Hupd, Hf'n, Hf'k. lia.
  Qed.

  (* a directory's tree entries, spelled at its view *)
  Lemma tree_ent_dir_eq (Q : Z -> list (bv 8)) (j : Z) :
    0 <= j < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode Q sb j)) = T_DIR_z ->
    forall f : fname,
      tree_ent (tree_of_disk Q sb) j f
      = dir_view (fs_file_data Q sb j)
          (dir_nrec (bv_unsigned (di_size (fs_dinode Q sb j)))) !! f.
  Proof.
    intros Hj Hty f.
    rewrite (tree_ent_of_disk Q sb j f Hj).
    rewrite (node_at_live Q sb j)
      by (rewrite Hty; unfold T_DIR_z; lia).
    unfold node_of. rewrite decide_True by exact Hty.
    reflexivity.
  Qed.

  Lemma root_wf_intro (P' : Z -> list (bv 8)) :
    bv_unsigned (di_type (fs_dinode P' sb ROOTINO)) = T_DIR_z ->
    dir_view (fs_file_data P' sb ROOTINO)
      (dir_nrec (bv_unsigned (di_size (fs_dinode P' sb ROOTINO)))) !! DOTDOT
    = Some ROOTINO ->
    fs_root_wf P' sb = true.
  Proof.
    intros Hty Hdd. unfold fs_root_wf. cbv zeta.
    apply andb_true_iff. split.
    { apply Z.eqb_eq. exact Hty. }
    unfold fs_file_data in Hdd.
    rewrite dir_view_lookup in Hdd.
    destruct (dir_first (fs_data_of P' (fs_dinode P' sb ROOTINO))
                (dir_nrec (bv_unsigned (di_size (fs_dinode P' sb ROOTINO))))
                DOTDOT) as [k0 |] eqn:Hf; [| discriminate].
    cbn [fmap option_fmap option_map] in Hdd.
    injection Hdd as Hdd. apply Z.eqb_eq. exact Hdd.
  Qed.

  Lemma dots_flat (z : Z) :
    0 <= z < sb_ninodes sb ->
    bv_unsigned (di_type (fs_dinode P sb z)) = T_DIR_z ->
    (2 <= dir_nrec (bv_unsigned (di_size (fs_dinode P sb z))))%nat
    /\ dir_live (fs_data_of P (fs_dinode P sb z)) 0
    /\ bv_unsigned (dir_inum (fs_data_of P (fs_dinode P sb z)) 0) = z
    /\ dir_bname (fs_data_of P (fs_dinode P sb z)) 0 = dot_name
    /\ dir_live (fs_data_of P (fs_dinode P sb z)) 1
    /\ dir_bname (fs_data_of P (fs_dinode P sb z)) 1 = dotdot_name.
  Proof.
    intros Hz Hty.
    pose proof (dots_bool_at z Hz Hty) as Hb.
    unfold fs_dots_wf in Hb. cbv zeta in Hb.
    rewrite !andb_true_iff in Hb.
    destruct Hb as [[[[[Hn Hl0] Hi0] Hb0] Hl1] Hb1].
    apply Z.leb_le in Hn. apply Z.eqb_eq in Hi0.
    apply bool_decide_eq_true in Hb0. apply bool_decide_eq_true in Hb1.
    split; [lia |].
    split; [exact (proj1 (dir_liveb_true _ _) Hl0) |].
    split; [exact Hi0 |].
    split; [exact Hb0 |].
    split; [exact (proj1 (dir_liveb_true _ _) Hl1) | exact Hb1].
  Qed.


End EffectsWf.
