(* FsStateInode.v -- one inode, as nested separation-logic predicates.

   Design of record: claude-notes/design/fs-state.md section 2.  Stage 2a of
   claude-notes/projects/durable-disk.md.

   THE INODE NODE.  [fs_node] is the abstract value of one inode:

       n = { rec ; ent ; blk }

   [rec] is the 64-byte on-disk record, [ent] the indirect block's entry
   array, and [blk] maps a SLOT INDEX to that slot's block contents.  [blk]
   ranges over EVERY nonzero [addrs] entry -- direct and, through the owned
   indirect block, indirect -- REGARDLESS of [rec.size].  That is the F3
   ruling, built into the representation: an inode may own blocks beyond its
   size ([itrunc] frees them all; [writei]'s partial-failure commit leaves
   one), and nothing above has to reason about the discrepancy.

   The abstract byte-sequence is a READING, not the ownership:
   [fn_file_bytes n] and [dir_entries n] are functions of [n].  The one local
   clause the reading needs to be total is [inl_covers] (every slot below the
   size is allocated).  Distinctness of an inode's own blocks is the [∗]
   ([FsStateDefs.blk_owned_ne]); no clause states it.

   LOCAL REASONING (fs-state.md section 0).  Every clause of [inode_local]
   mentions ONE inode.  The only clause that mentions an inum at all is the
   "." entry, and it names the inode's OWN inum.  Links to other inodes are
   carried as [link_tok]s, never as an equation. *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap numbers.
From iris.base_logic.lib Require Import iprop own.
Require Import BioDefs.
Require Import RiscvModelBytes.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import DirView.
Require Import InodeDefs.
Require Import FsTree.
Require Import FsImg.
Require Export FsNode.        (* [fs_node] -- the record; see its header *)
Require Export FsStateLink.

Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  1.  The node, and its readings                                     *)
(* ------------------------------------------------------------------ *)

(* [fs_node] and its [Inhabited] instance are FsNode.v's, re-exported above:
   the top map's capacity class is an [Xv6G.xv6G] member since durable-disk
   2b-inode-3, so the TYPE its camera is over had to move below
   [Xv6Cameras.v].  Everything else about the node is here. *)

Definition fn_type (n : fs_node) : Z := bv_unsigned (di_type (fn_rec n)).
Definition fn_size (n : fs_node) : Z := bv_unsigned (di_size (fn_rec n)).
Definition fn_nlink (n : fs_node) : nat :=
  Z.to_nat (bv_unsigned (di_nlink (fn_rec n))).

(* the block number of slot [k]: direct out of the record, indirect out of
   the entry array *)
Definition fn_naddr (n : fs_node) (k : nat) : Z :=
  if decide (k < FS_NDIRECT)%nat
  then bv_unsigned (di_addrs (fn_rec n) !!! k)
  else bv_unsigned (fn_ent n !!! (k - FS_NDIRECT)%nat).

(* the indirect block itself; 0 = none *)
Definition fn_indb (n : fs_node) : Z :=
  bv_unsigned (di_addrs (fn_rec n) !!! FS_NDIRECT).

(* the [data] function the tree's readings are stated over.  Slots the node
   does not own read as zeroes -- which is only ever consulted below the
   size, where [inl_covers] says the slot IS owned. *)
Definition fn_data (n : fs_node) : nat -> list (bv 8) :=
  fun k => default (replicate BSIZE (bv_0 8)) (fn_blk n !! k).

Definition fn_nrec (n : fs_node) : nat := dir_nrec (fn_size n).

Definition fn_file_bytes (n : fs_node) : list (bv 8) :=
  file_bytes (fn_data n) (Z.to_nat (fn_size n)).

Definition fn_is_dir (n : fs_node) : bool := bool_decide (fn_type n = T_DIR_z).

Definition dir_entries (n : fs_node) : gmap fname Z :=
  if fn_is_dir n then dir_view (fn_data n) (fn_nrec n) else ∅.

(* an ORPHAN directory is one at [nlink = 0]: its ".." entry is TOKENLESS,
   the parent having taken that token back at the unlink (fs-state.md
   section 2).  This kernel's "grey" record. *)
Definition fn_orphan (n : fs_node) : bool := bool_decide (fn_nlink n = 0%nat).

(* ------------------------------------------------------------------ *)
(*  2.  The local clauses                                              *)
(* ------------------------------------------------------------------ *)

Record inode_local (i : Z) (n : fs_node) : Prop := MkInodeLocal {
  (* representation *)
  inl_rec_wf     : dinode_wf (fn_rec n);
  inl_ent_len    : length (fn_ent n) = FS_NINDIRECT;
  inl_ind_zero   : fn_indb n = 0 -> fn_ent n = replicate FS_NINDIRECT (bv_0 32);
  inl_blk_dom    : forall k, (k < FS_MAXFILE)%nat ->
                     (is_Some (fn_blk n !! k) <-> fn_naddr n k <> 0);
  inl_blk_top    : forall k, (FS_MAXFILE <= k)%nat -> fn_blk n !! k = None;
  inl_blk_len    : forall k bs, fn_blk n !! k = Some bs -> length bs = BSIZE;
  (* the record's own fields *)
  inl_type       : fn_type n = 0 \/ fn_type n = T_DIR_z
                   \/ fn_type n = T_FILE_z \/ fn_type n = T_DEVICE_z;
  inl_size       : 0 <= fn_size n <= Z.of_nat FS_MAXFILE * BSIZE_z;
  inl_covers     : forall k, (k < FS_MAXFILE)%nat ->
                     Z.of_nat k * BSIZE_z < fn_size n -> fn_naddr n k <> 0;
  inl_free       : fn_type n = 0 -> fn_nlink n = 0%nat;
  inl_nlink      : bv_unsigned (di_nlink (fn_rec n)) <= 32767;
  (* directory-local; vacuous for anything else.  [inode_owned] is the one
     iterated predicate, so a directory's clauses live here rather than in a
     sibling of it -- see [dir_owned] below, which is the reading. *)
  inl_dir_size   : fn_is_dir n = true -> (16 | fn_size n);
  inl_dir_uniq   : fn_is_dir n = true -> dir_names_unique (fn_data n) (fn_nrec n);
  (* THE DOTS ARE GUARDED BY [nlink <> 0] (B2 of the 2026-08-23 survey).
     A [T_DIR] record at size 0 holds no records at all, hence no "." and no
     "..", and this kernel really does produce two of them: the CLAIM BOX
     [ialloc] installs (type [T_DIR], size 0, nlink 0 -- before [mkdir]'s two
     [dirlink]s run) and the CORPSE [itrunc] leaves (every block freed, size
     0, nlink 0, still typed until [iput] clears it).  Both sit at
     [nlink = 0], which is the tree's own guard ([DirView.dir_dots_ix] is
     stated the same way) and is what the C guarantees: a directory some name
     reaches has had [mkdir] run on it.  [inl_dir_uniq] and [inl_dir_size]
     hold at size 0 and stay UNGUARDED.  An ORPHAN owes no dots clause and
     needs none: its ".." is TOKENLESS whatever the entry says (section 8). *)
  inl_dir_dot    : fn_is_dir n = true -> fn_nlink n <> 0%nat ->
                     dir_entries n !! DOT = Some i;
  inl_dir_dotdot : fn_is_dir n = true -> fn_nlink n <> 0%nat ->
                     is_Some (dir_entries n !! DOTDOT);
}.

Global Arguments inl_rec_wf {_ _} _.
Global Arguments inl_ent_len {_ _} _.
Global Arguments inl_ind_zero {_ _} _.
Global Arguments inl_blk_dom {_ _} _.
Global Arguments inl_blk_top {_ _} _.
Global Arguments inl_blk_len {_ _} _.
Global Arguments inl_type {_ _} _.
Global Arguments inl_size {_ _} _.
Global Arguments inl_covers {_ _} _.
Global Arguments inl_free {_ _} _.
Global Arguments inl_nlink {_ _} _.
Global Arguments inl_dir_size {_ _} _.
Global Arguments inl_dir_uniq {_ _} _.
Global Arguments inl_dir_dot {_ _} _.
Global Arguments inl_dir_dotdot {_ _} _.

(* the reading is total below the size: [inl_covers] plus [inl_blk_dom] *)
Lemma inode_local_data_owned i n k :
  inode_local i n -> (k < FS_MAXFILE)%nat ->
  Z.of_nat k * BSIZE_z < fn_size n ->
  exists bs, fn_blk n !! k = Some bs /\ fn_data n k = bs /\ length bs = BSIZE.
Proof.
  intros Hl Hk Hlt.
  destruct (proj2 (inl_blk_dom Hl k Hk) (inl_covers Hl k Hk Hlt)) as [bs Hbs].
  exists bs. rewrite /fn_data Hbs /=. split; [done | split; [done |]].
  by eapply inl_blk_len.
Qed.

(* the F3 reading, spelled out: a slot the node OWNS need not be below the
   size.  [inl_blk_dom] is an iff with the ADDRESS, never with the size. *)
Lemma inode_local_beyond_size i n k bs :
  inode_local i n -> fn_blk n !! k = Some bs ->
  (k < FS_MAXFILE)%nat /\ fn_naddr n k <> 0 /\ length bs = BSIZE.
Proof.
  intros Hl Hbs.
  assert (Hk : (k < FS_MAXFILE)%nat).
  { destruct (decide (k < FS_MAXFILE)%nat) as [| Hge]; [done |].
    rewrite (inl_blk_top Hl k) // in Hbs. lia. }
  split; [done |]. split; [| by eapply inl_blk_len].
  apply (inl_blk_dom Hl k Hk). by exists bs.
Qed.

(* ------------------------------------------------------------------ *)
(*  2a. THE BARE NODE, and [inode_local] of it                         *)
(*                                                                     *)
(*  A node with no blocks, no indirect block, size 0 and nlink 0.       *)
(*  THREE of this kernel's records are bare, and they are the same      *)
(*  shape, so this is ONE definition and not three:                     *)
(*                                                                      *)
(*    - the FREE record ([di_type = 0]) the mkfs image is full of;       *)
(*    - the CLAIM BOX [ialloc] installs ([SpecIalloc.ialloc_fresh ty]:   *)
(*      the zero record with the type halfword set);                     *)
(*    - the CORPSE [itrunc] then [iput] leave ([ProofIput.set_ditype0]   *)
(*      of a record whose blocks and size [itrunc] already cleared).      *)
(*                                                                      *)
(*  [inode_local] holds of a bare node AT ANY TYPE, which is exactly     *)
(*  what B2's guard above buys: without it a bare [T_DIR] node would     *)
(*  owe a "." entry that it cannot have.  The mover is                   *)
(*  [inode_owned_bare_move] in section 7.                                *)
(* ------------------------------------------------------------------ *)

Lemma dir_nrec_zero : dir_nrec 0 = 0%nat.
Proof. reflexivity. Qed.

Definition fn_bare (n : fs_node) : Prop :=
  (* [13] is [FS_NDIRECT + 1], spelled as [dinode_wf] spells it *)
  di_addrs (fn_rec n) = replicate 13 (bv_0 32)
  /\ fn_ent n = replicate FS_NINDIRECT (bv_0 32)
  /\ fn_blk n = ∅
  /\ fn_size n = 0
  /\ fn_nlink n = 0%nat.

Lemma fn_bare_wf n : fn_bare n -> dinode_wf (fn_rec n).
Proof. intros (Ha & _). rewrite /dinode_wf Ha length_replicate //. Qed.

Lemma fn_bare_indb n : fn_bare n -> fn_indb n = 0.
Proof.
  intros (Ha & _). rewrite /fn_indb Ha.
  rewrite lookup_total_replicate_2; [| rewrite /FS_NDIRECT; lia].
  by change (bv_unsigned (bv_0 32)) with 0.
Qed.

Lemma fn_bare_naddr n k : fn_bare n -> (k < FS_MAXFILE)%nat -> fn_naddr n k = 0.
Proof.
  intros (Ha & He & _) Hk. rewrite /fn_naddr.
  case_decide as Hd.
  - rewrite Ha lookup_total_replicate_2; [| rewrite /FS_NDIRECT in Hd; lia].
    by change (bv_unsigned (bv_0 32)) with 0.
  - rewrite He lookup_total_replicate_2;
      [| rewrite /FS_NINDIRECT /FS_NDIRECT; rewrite /FS_MAXFILE in Hk;
         rewrite /FS_NDIRECT in Hd; lia].
    by change (bv_unsigned (bv_0 32)) with 0.
Qed.

Lemma fn_bare_nrec n : fn_bare n -> fn_nrec n = 0%nat.
Proof. intros (_ & _ & _ & Hsz & _). rewrite /fn_nrec Hsz //. Qed.

(* a bare node's entry map is EMPTY at either type: [dir_nrec 0 = 0] and
   [dir_view _ 0 = ∅] ([FsTree.dir_view_nil]). *)
Lemma dir_entries_bare n : fn_bare n -> dir_entries n = ∅.
Proof.
  intros Hb. rewrite /dir_entries.
  destruct (fn_is_dir n); [| done].
  rewrite (fn_bare_nrec n Hb). apply dir_view_nil.
Qed.

Lemma fn_bare_orphan n : fn_bare n -> fn_orphan n = true.
Proof.
  intros (_ & _ & _ & _ & Hnl). rewrite /fn_orphan bool_decide_eq_true_2 //.
Qed.

(* the all-zero record: the mkfs image's free inode, and the node the boot
   allocation starts every inum at (2b-A's [fs_boot_alloc]). *)
Definition fn_zero : fs_node :=
  MkNode (MkDinode (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 16) (bv_0 32)
                   (replicate 13 (bv_0 32)))
         (replicate FS_NINDIRECT (bv_0 32)) ∅.

Lemma fn_bare_zero : fn_bare fn_zero.
Proof.
  rewrite /fn_bare /fn_zero /fn_size /fn_nlink /=.
  split_and!; try reflexivity; by change (bv_unsigned (bv_0 32)) with 0.
Qed.

Lemma inode_local_bare i n :
  fn_bare n ->
  (fn_type n = 0 \/ fn_type n = T_DIR_z
   \/ fn_type n = T_FILE_z \/ fn_type n = T_DEVICE_z) ->
  inode_local i n.
Proof.
  intros Hb Hty.
  pose proof Hb as (Ha & He & Hblk & Hsz & Hnl).
  assert (Hnl0 : bv_unsigned (di_nlink (fn_rec n)) = 0).
  { pose proof (bv_unsigned_in_range _ (di_nlink (fn_rec n))) as [Hlo _].
    rewrite /fn_nlink in Hnl. lia. }
  split.
  - exact (fn_bare_wf n Hb).
  - rewrite He length_replicate //.
  - intros _. exact He.
  - intros k Hk. rewrite Hblk lookup_empty (fn_bare_naddr n k Hb Hk).
    split; [by intros [? ?] | done].
  - intros k _. by rewrite Hblk lookup_empty.
  - intros k bs Hbs. rewrite Hblk lookup_empty in Hbs. done.
  - exact Hty.
  - rewrite Hsz. rewrite /BSIZE_z /FS_MAXFILE. lia.
  - intros k _ Hlt. exfalso. rewrite Hsz in Hlt.
    assert (0 <= Z.of_nat k * BSIZE_z); [rewrite /BSIZE_z; nia | lia].
  - intros _. exact Hnl.
  - rewrite Hnl0. lia.
  - intros _. rewrite Hsz. by exists 0.
  - intros _. rewrite (fn_bare_nrec n Hb). intros j k Hj. exfalso. lia.
  - intros _ Hne. exfalso. exact (Hne Hnl).
  - intros _ Hne. exfalso. exact (Hne Hnl).
Qed.

(* ------------------------------------------------------------------ *)
(*  2b. The PURE bridge from the tree's dirent vocabulary              *)
(*                                                                     *)
(*  [FsTree] states an unlink as [dir_zeroed_at] and a dirlink as      *)
(*  [dir_insert_at], and proves BOTH view deltas outright              *)
(*  ([dir_view_zero], [dir_view_insert]).  These read them at          *)
(*  [fs_node]; section 8's token moves take the record delta as their  *)
(*  premise and go through them, so nothing below assumes an           *)
(*  entry-map delta.                                                   *)
(* ------------------------------------------------------------------ *)

Lemma dir_entries_zero (n n' : fs_node) (k0 : nat) :
  fn_is_dir n = true -> fn_is_dir n' = true ->
  fn_size n' = fn_size n ->
  dir_names_unique (fn_data n) (fn_nrec n) ->
  (k0 < fn_nrec n)%nat ->
  dir_live (fn_data n) k0 ->
  dir_zeroed_at (fn_data n) (fn_data n') k0 ->
  dir_entries n' = delete (dir_bname (fn_data n) k0) (dir_entries n).
Proof.
  intros Hd Hd' Hsz Hu Hk Hlive Hz.
  rewrite /dir_entries Hd Hd' /fn_nrec Hsz.
  by apply (dir_view_zero (fn_data n) (fn_data n') (dir_nrec (fn_size n)) k0).
Qed.

(* the dirlink twin.  [dir_insert_at] carries the record-count arithmetic
   (both arms of the free-slot scan) and the free-slot and grown-range
   liveness side conditions; the ONE guard left over is dirlink's own,
   [s] not already a live name. *)
Lemma dir_entries_write (n n' : fs_node) (k0 : nat) (s : fname) (z : bv 16) :
  fn_is_dir n = true -> fn_is_dir n' = true ->
  dir_first (fn_data n) (fn_nrec n) s = None ->
  dir_insert_at (fn_data n) (fn_data n') (fn_nrec n) (fn_nrec n') k0 s z ->
  dir_entries n' = <[s := bv_unsigned z]> (dir_entries n).
Proof.
  intros Hd Hd' Hnone Hins. rewrite /dir_entries Hd Hd'.
  exact (dir_view_insert (fn_data n) (fn_data n') (fn_nrec n) (fn_nrec n')
           k0 s z Hnone Hins).
Qed.

(* ...and the freshness the [big_sepM_insert] needs, off the same guard *)
Lemma dir_entries_fresh (n : fs_node) (s : fname) :
  dir_first (fn_data n) (fn_nrec n) s = None -> dir_entries n !! s = None.
Proof.
  intros Hnone. rewrite /dir_entries. destruct (fn_is_dir n).
  - by apply dir_view_lookup_None.
  - apply lookup_empty.
Qed.

(* ------------------------------------------------------------------ *)
(*  3.  The node's byte ownership                                      *)
(* ------------------------------------------------------------------ *)

(* THE RECORD-ONLY HALF IS RA-FREE, AND THAT IS LOAD-BEARING
   (durable-disk 2b-inode-1).  [rec_owned]/[rec_owned_at] and the sixteen-
   fold split are about BYTES alone; stating them inside the link RA's
   section would discharge every one of them over [fsLinkG Σ], and a
   consumer without that class in context -- [InodeRegion], whose
   [ireg_inv] arity is fixed by 30-odd fs contracts -- would then leave an
   unresolvable instance goal SHELVED and fail at [Qed] with "Attempt to
   save an incomplete proof" (durable-notes, the capacity-class trap).  So
   they live in their own section over a bare [Σ]. *)
Section RecOwned.
  Context {Σ : gFunctors}.
  Implicit Types Γ : fs_view_names Σ.

  (* inum [i]'s 64-byte slot of its inode block *)
  Definition rec_owned Γ (sb : fs_sb) (i : Z) (dn : dinode) : iProp Σ :=
    byte_range Γ (IBLOCK (fs_inum_bv i) (sb_inodestart sb))
                 (Z.of_nat (64 * islot (fs_inum_bv i))) (dinode_bytes dn).

  (* ---------------------------------------------------------------- *)
  (*  3b. B5: the GEOMETRY-FREE reading, and sixteen records per block  *)
  (*                                                                    *)
  (*  [rec_owned] takes an [fs_sb]; the inode REGION has no superblock,  *)
  (*  only [icfg_ist] and an inum as a plain [Z].  So the record's       *)
  (*  ownership is stated once over the two numbers it actually uses --  *)
  (*  the [FsStateBitmap.free_bitmap_at] pattern -- and [rec_owned] is   *)
  (*  its superblock reading.                                            *)
  (* ---------------------------------------------------------------- *)

  (* inum [z]'s 64 bytes: offset [64 * (z mod 16)] of block [istart + z/16].
     [InodeRegion.iblk_of_IBLOCK] is the same numbering equality one level
     up, and holds there by [reflexivity] for the same reason. *)
  Definition rec_owned_at Γ (istart z : Z) (dn : dinode) : iProp Σ :=
    byte_range Γ (istart + z `div` 16) (64 * (z `mod` 16)) (dinode_bytes dn).

  Global Instance rec_owned_at_timeless `{!GTimeless Γ} istart z dn :
    Timeless (rec_owned_at Γ istart z dn).
  Proof. rewrite /rec_owned_at. apply _. Qed.

  (* THE RANGE PREMISE IS REAL, not slack: [rec_owned] goes through
     [FsImg.fs_inum_bv i = Z_to_bv 32 i], which WRAPS.  Every caller has it
     ([sb_ninodes] is far below 2^32); it is the premise
     [FsEffBase.fs_inum_bv_unsigned] takes for the same reason. *)
  Lemma rec_owned_sb Γ sb i dn :
    0 <= i < 2 ^ 32 ->
    rec_owned Γ sb i dn ⊣⊢ rec_owned_at Γ (sb_inodestart sb) i dn.
  Proof.
    intros Hi.
    assert (H32 : bv_modulus 32 = (2 ^ 32)%Z) by (vm_compute; reflexivity).
    assert (Hbv : bv_unsigned (fs_inum_bv i) = i).
    { rewrite /fs_inum_bv. apply Z_to_bv_small. rewrite H32. lia. }
    pose proof (Z.mod_pos_bound i 16 ltac:(lia)) as [Hm0 Hm1].
    assert (Hblk : IBLOCK (fs_inum_bv i) (sb_inodestart sb)
                   = sb_inodestart sb + i `div` 16)
      by (rewrite /IBLOCK Hbv; lia).
    assert (Hoff : Z.of_nat (64 * islot (fs_inum_bv i)) = 64 * (i `mod` 16)).
    { rewrite /islot Hbv Nat2Z.inj_mul Z2Nat.id; [reflexivity | lia]. }
    rewrite /rec_owned /rec_owned_at Hblk Hoff //.
  Qed.

  (* ---- the 16-fold split/gather ------------------------------------ *)

  (* two generic big-op readings, both about the INDEX only *)
  Lemma big_sepL_seq0 (Ψ : nat -> iProp Σ) (n : nat) :
    ([∗ list] j ∈ seq 0 n, Ψ j) ⊣⊢ ([∗ list] k ↦ _ ∈ seq 0 n, Ψ k).
  Proof.
    apply big_sepL_proper. intros k j Hk.
    apply lookup_seq in Hk as [-> _]. done.
  Qed.

  Lemma big_sepL_len_irrel {A B : Type} (l : list A) (l' : list B)
      (Ψ : nat -> iProp Σ) :
    length l = length l' ->
    ([∗ list] k ↦ _ ∈ l, Ψ k) ⊣⊢ ([∗ list] k ↦ _ ∈ l', Ψ k).
  Proof.
    revert l' Ψ. induction l as [| x l IH]; intros l' Ψ Hlen.
    - destruct l' as [| y l']; [done | simpl in Hlen; lia].
    - destruct l' as [| y l']; [simpl in Hlen; lia |].
      rewrite !big_sepL_cons. apply bi.sep_proper; [done |].
      apply (IH l' (fun k => Ψ (S k))). simpl in Hlen. lia.
  Qed.

  (* a run of records is the concatenation of their byte runs -- one
     [byte_range_app] per record, off [dinode_bytes_length] *)
  Lemma byte_range_diblk Γ (b off : Z) (ds : list dinode) :
    Forall dinode_wf ds ->
    byte_range Γ b off (diblk_bytes ds)
    ⊣⊢ [∗ list] k ↦ d ∈ ds,
         byte_range Γ b (off + 64 * Z.of_nat k) (dinode_bytes d).
  Proof.
    revert off. induction ds as [| d ds IH]; intros off Hall.
    { rewrite diblk_bytes_nil byte_range_nil big_sepL_nil //. }
    inversion Hall as [| xd xds Hd Hds]; subst.
    rewrite diblk_bytes_cons byte_range_app (dinode_bytes_length d Hd).
    rewrite big_sepL_cons.
    apply bi.sep_proper.
    - assert (Hz : off + 64 * Z.of_nat 0%nat = off) by lia. rewrite Hz //.
    - rewrite (IH (off + Z.of_nat 64%nat) Hds).
      apply big_sepL_proper. intros k y _.
      assert (Hz : off + Z.of_nat 64%nat + 64 * Z.of_nat k
                   = off + 64 * Z.of_nat (S k)) by lia.
      rewrite Hz //.
  Qed.

  (* slot [k] of block [bi] IS inum [16*bi + k] *)
  Lemma rec_owned_at_slot Γ (istart bi : Z) (k : nat) dn :
    (k < 16)%nat ->
    rec_owned_at Γ istart (16 * bi + Z.of_nat k) dn
    ⊣⊢ byte_range Γ (istart + bi) (64 * Z.of_nat k) (dinode_bytes dn).
  Proof.
    intros Hk. rewrite /rec_owned_at.
    assert (Hk0 : Z.of_nat k `div` 16 = 0) by (apply Z.div_small; lia).
    assert (Hd : (16 * bi + Z.of_nat k) `div` 16 = bi).
    { rewrite (Z.mul_comm 16 bi) Z.div_add_l; [| lia]. rewrite Hk0. lia. }
    assert (Hm : (16 * bi + Z.of_nat k) `mod` 16 = Z.of_nat k).
    { rewrite (Z.mul_comm 16 bi) Z.add_comm Z_mod_plus_full.
      apply Z.mod_small. lia. }
    rewrite Hd Hm //.
  Qed.

  (* THE SPLIT/GATHER.  One inode block's byte run IS its sixteen records,
     at the region's own numbering ([16*bi + k], which is what
     [InodeRegion.ireg_blk]'s slot big-op is indexed by). *)
  Lemma rec_owned_at_diblk Γ (istart bi : Z) (ds : list dinode) :
    diblk_wf ds ->
    byte_range Γ (istart + bi) 0 (diblk_bytes ds)
    ⊣⊢ [∗ list] k ∈ seq 0 16,
         rec_owned_at Γ istart (16 * bi + Z.of_nat k) (ds !!! k).
  Proof.
    intros [Hlen Hall].
    rewrite (byte_range_diblk Γ (istart + bi) 0 ds Hall).
    rewrite (big_sepL_seq0
               (fun k => rec_owned_at Γ istart (16 * bi + Z.of_nat k)
                                      (ds !!! k)) 16).
    rewrite (big_sepL_proper
               (fun k d => byte_range Γ (istart + bi) (0 + 64 * Z.of_nat k)
                                      (dinode_bytes d))
               (fun k (_ : dinode) =>
                  byte_range Γ (istart + bi) (64 * Z.of_nat k)
                             (dinode_bytes (ds !!! k))) ds); last first.
    { intros k d Hkd. rewrite (list_lookup_total_correct ds k d Hkd).
      assert (Hz : 0 + 64 * Z.of_nat k = 64 * Z.of_nat k) by lia.
      rewrite Hz //. }
    rewrite (big_sepL_len_irrel ds (seq 0 16)
               (fun k => byte_range Γ (istart + bi) (64 * Z.of_nat k)
                                    (dinode_bytes (ds !!! k))));
      [| rewrite Hlen length_seq //].
    apply big_sepL_proper. intros k j Hk.
    apply lookup_seq in Hk as [_ Hlt].
    rewrite (rec_owned_at_slot Γ istart bi k (ds !!! k) Hlt) //.
  Qed.

End RecOwned.

(* ------------------------------------------------------------------ *)
(*  3c. ...and the rest of the inode, which DOES read the link RA      *)
(* ------------------------------------------------------------------ *)

Section InodeOwned.
  Context `{!fsLinkG Σ}.
  Implicit Types Γ : fs_view_names Σ.

  Definition ind_owned Γ (n : fs_node) : iProp Σ :=
    (if decide (fn_indb n = 0) then emp
     else blk_owned Γ (fn_indb n) (ind_bytes (fn_ent n)))%I.

  (* the Φ-only part of an inode: exactly its footprint *)
  Definition inode_phi Γ (sb : fs_sb) (i : Z) (n : fs_node) : iProp Σ :=
    (rec_owned Γ sb i (fn_rec n)
     ∗ ([∗ map] k ↦ bs ∈ fn_blk n, blk_owned Γ (fn_naddr n k) bs)
     ∗ ind_owned Γ n)%I.

  (* ---------------------------------------------------------------- *)
  (*  4.  The link tokens an inode's directory entries carry           *)
  (* ---------------------------------------------------------------- *)

  (* THREE EXEMPTIONS, and each of them is the kernel's own arithmetic.

     - ".": xv6 deliberately does not bump [nlink] for it ("No ip->nlink++
       for '.': avoid cyclic ref count"), so there is nothing to pay for it.
     - ".." of an ORPHAN: the parent took that token back when it removed
       the directory's name, and the record it left behind is exactly this
       kernel's grey ".." (fs-icache.md section 20).
     - ".." OF A SELF-PARENT, i.e. the ROOT, whose [".."] names the root.
       That record is a SELF record and pays for nothing, exactly as "."
       does -- it is the image's own counting rule
       ([FsImg.fs_rec_ticket]'s [negb (dir_inum = self)] guard, and W9's
       "a live directory has zero incoming tickets").  What the exemption
       buys is the ROOT KEEP-ALIVE TOKEN: with root's [".."] tokenless the
       image's [nlink = 1] is unaccounted for, so the inode region can park
       one [link_tok] at [ireg_root] that nothing ever spends, and
       "the root is allocated" becomes a reading of the RA's own law rather
       than a maintained clause. *)
  Definition ent_tokenless (self : Z) (orph : bool) (s : fname) (t : Z)
    : bool :=
    bool_decide (s = DOT)
    || (bool_decide (s = DOTDOT) && (orph || bool_decide (t = self))).

  Definition ent_tok Γ (self : Z) (orph : bool) (s : fname) (t : Z)
    : iProp Σ :=
    (if ent_tokenless self orph s t then emp else link_tok Γ t)%I.

  Definition ent_toks Γ (i : Z) (n : fs_node) : iProp Σ :=
    ([∗ map] s ↦ t ∈ dir_entries n, ent_tok Γ i (fn_orphan n) s t)%I.

  (* the same thing as ONE resource-algebra element -- what the mint
     allocates (fs-state.md section 1, "Functoriality") *)
  Definition ent_elem (self : Z) (orph : bool) (s : fname) (t : Z)
    : fsLinkUR :=
    if ent_tokenless self orph s t then ε else link_tok_elem t 1.

  Definition link_elem_node (i : Z) (n : fs_node) : fsLinkUR :=
    link_auth_elem i (fn_nlink n)
    ⋅ ([^op map] s ↦ t ∈ dir_entries n, ent_elem i (fn_orphan n) s t).

  (* the Φ-FREE part of an inode: the link ghosts and the local clauses *)
  Definition inode_ghost Γ (i : Z) (n : fs_node) : iProp Σ :=
    (link_auth Γ i (fn_nlink n) ∗ ent_toks Γ i n ∗ ⌜inode_local i n⌝)%I.

  Definition inode_owned Γ (sb : fs_sb) (i : Z) (n : fs_node) : iProp Σ :=
    (inode_phi Γ sb i n ∗ inode_ghost Γ i n)%I.

  (* the reading a directory's clients use *)
  Definition dir_owned Γ (sb : fs_sb) (d : Z) (n : fs_node) : iProp Σ :=
    (inode_owned Γ sb d n ∗ ⌜fn_is_dir n = true⌝)%I.

  Lemma inode_owned_split Γ sb i n :
    inode_owned Γ sb i n ⊣⊢ inode_phi Γ sb i n ∗ inode_ghost Γ i n.
  Proof. done. Qed.

  Lemma inode_owned_local Γ sb i n :
    inode_owned Γ sb i n -∗ ⌜inode_local i n⌝.
  Proof. iIntros "[_ (_ & _ & $)]". Qed.

  Lemma dir_owned_of Γ sb d n :
    fn_is_dir n = true -> inode_owned Γ sb d n ⊢ dir_owned Γ sb d n.
  Proof. iIntros (H) "H". by iFrame. Qed.

  (* ---------------------------------------------------------------- *)
  (*  5.  Timelessness                                                 *)
  (* ---------------------------------------------------------------- *)

  Global Instance rec_owned_timeless `{!GTimeless Γ} sb i dn :
    Timeless (rec_owned Γ sb i dn).
  Proof. rewrite /rec_owned. apply _. Qed.

  Global Instance ind_owned_timeless `{!GTimeless Γ} n :
    Timeless (ind_owned Γ n).
  Proof. rewrite /ind_owned. case_decide; apply _. Qed.

  Global Instance inode_phi_timeless `{!GTimeless Γ} sb i n :
    Timeless (inode_phi Γ sb i n).
  Proof. rewrite /inode_phi. apply _. Qed.

  Global Instance ent_tok_timeless Γ self orph s t :
    Timeless (ent_tok Γ self orph s t).
  Proof. rewrite /ent_tok. destruct (ent_tokenless self orph s t); apply _. Qed.

  Global Instance ent_toks_timeless Γ i n : Timeless (ent_toks Γ i n).
  Proof. rewrite /ent_toks. apply _. Qed.

  Global Instance inode_ghost_timeless Γ i n : Timeless (inode_ghost Γ i n).
  Proof. rewrite /inode_ghost. apply _. Qed.

  Global Instance inode_owned_timeless `{!GTimeless Γ} sb i n :
    Timeless (inode_owned Γ sb i n).
  Proof. rewrite /inode_owned. apply _. Qed.

  Global Instance dir_owned_timeless `{!GTimeless Γ} sb d n :
    Timeless (dir_owned Γ sb d n).
  Proof. rewrite /dir_owned. apply _. Qed.

  (* ---------------------------------------------------------------- *)
  (*  6.  Gathering and scattering the link ghosts                     *)
  (*                                                                   *)
  (*  These are the two halves of the mint's transport (FsState.v):     *)
  (*  gathering reads the family's VALIDITY off the durable instance's  *)
  (*  own [own]; scattering hands the freshly allocated one back out.   *)
  (* ---------------------------------------------------------------- *)

  Lemma inode_link_gather Γ i n (x : fsLinkUR) :
    own (γlink Γ) x -∗ link_auth Γ i (fn_nlink n) -∗ ent_toks Γ i n -∗
    own (γlink Γ) (x ⋅ link_elem_node i n).
  Proof.
    iIntros "Hx Ha Ht".
    iDestruct (own_op with "[$Hx $Ha]") as "Hxa".
    iDestruct (own_gather_map_opt (γlink Γ)
                 (fun (_ : fname) (t : Z) => link_tok_elem t 1)
                 (fun (s : fname) (t : Z) => ent_tokenless i (fn_orphan n) s t)
                 (dir_entries n) (x ⋅ link_auth_elem i (fn_nlink n))
                with "Hxa [Ht]") as "H".
    { iApply (big_sepM_mono with "Ht"). intros s t _; simpl.
      rewrite /ent_tok /link_tok /link_toks. done. }
    rewrite /link_elem_node /ent_elem -assoc //.
  Qed.

  (* the same, with no accumulator: the auth IS the accumulator *)
  Lemma inode_link_pack Γ i n :
    link_auth Γ i (fn_nlink n) -∗ ent_toks Γ i n -∗
    own (γlink Γ) (link_elem_node i n).
  Proof.
    iIntros "Ha Ht".
    iDestruct (own_gather_map_opt (γlink Γ)
                 (fun (_ : fname) (t : Z) => link_tok_elem t 1)
                 (fun (s : fname) (t : Z) => ent_tokenless i (fn_orphan n) s t)
                 (dir_entries n) (link_auth_elem i (fn_nlink n))
                with "Ha [Ht]") as "H".
    { iApply (big_sepM_mono with "Ht"). intros s t _; simpl.
      rewrite /ent_tok /link_tok /link_toks. done. }
    rewrite /link_elem_node /ent_elem //.
  Qed.

  Lemma inode_link_scatter Γ i n :
    own (γlink Γ) (link_elem_node i n) ⊢
    link_auth Γ i (fn_nlink n) ∗ ent_toks Γ i n.
  Proof.
    rewrite /link_elem_node own_op. iIntros "[$ Ht]".
    iDestruct (own_scatter_map_opt (γlink Γ)
                 (fun (_ : fname) (t : Z) => link_tok_elem t 1)
                 (fun (s : fname) (t : Z) => ent_tokenless i (fn_orphan n) s t)
                 (dir_entries n) with "[Ht]") as "H".
    { rewrite /ent_elem //. }
    iApply (big_sepM_mono with "H"). intros s t _; simpl.
    rewrite /ent_tok /link_tok /link_toks. done.
  Qed.

  Lemma inode_link_iff Γ i n :
    link_auth Γ i (fn_nlink n) ∗ ent_toks Γ i n
    ⊣⊢ own (γlink Γ) (link_elem_node i n).
  Proof.
    iSplit.
    - iIntros "[Ha Ht]". iApply (inode_link_pack with "Ha Ht").
    - iApply inode_link_scatter.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  7.  ENCODE LEMMAS -- what a writer uses at its AU                *)
  (*                                                                   *)
  (*  Every one of them is an ACCESSOR: it hands the writer the byte    *)
  (*  range the log is about to move, and takes it back at the new      *)
  (*  bytes.  None of them updates anything itself -- at an abstract    *)
  (*  [fsΦ] there is no update to make; the log's [byte_range_update]   *)
  (*  is what moves the bytes, and these lemmas are the repackaging     *)
  (*  either side of it.                                               *)
  (* ---------------------------------------------------------------- *)

  Lemma rec_owned_length dn : dinode_wf dn -> length (dinode_bytes dn) = 64%nat.
  Proof. apply dinode_bytes_length. Qed.

  (* (a) the record's bytes move -- iupdate, ialloc, ifree *)
  Lemma rec_owned_acc Γ sb i dn dn' :
    rec_owned Γ sb i dn ⊢
      byte_range Γ (IBLOCK (fs_inum_bv i) (sb_inodestart sb))
                   (Z.of_nat (64 * islot (fs_inum_bv i))) (dinode_bytes dn)
      ∗ (byte_range Γ (IBLOCK (fs_inum_bv i) (sb_inodestart sb))
                      (Z.of_nat (64 * islot (fs_inum_bv i))) (dinode_bytes dn')
         -∗ rec_owned Γ sb i dn').
  Proof. iIntros "H". iFrame "H". by iIntros "H". Qed.

  (* (a') THE BARE MOVE -- the ONE mover the claim box and the corpse both
     use.  Section 2a's [fn_bare] covers three records of the same shape, so
     this is one lemma and not a family: at [ialloc] the old node is the FREE
     record and the new one is [SpecIalloc.ialloc_fresh ty] (the type
     halfword set, everything else zero); at [iput]'s free the old node is
     what [itrunc] left (blocks gone, size 0, nlink 0) and the new one is
     [ProofIput.set_ditype0] of it.  Only the RECORD's bytes move -- a bare
     node owns nothing else -- and [inode_local] of the target is
     RE-ESTABLISHED here rather than taken as a premise, which is exactly
     what B2's guard makes possible: a bare [T_DIR] node owes no "." entry.
     [nlink] is 0 on both sides, so the auth passes through untouched. *)
  Lemma inode_owned_bare_move Γ sb i n n' :
    fn_bare n -> fn_bare n' ->
    (fn_type n' = 0 \/ fn_type n' = T_DIR_z
     \/ fn_type n' = T_FILE_z \/ fn_type n' = T_DEVICE_z) ->
    inode_owned Γ sb i n ⊢
      rec_owned Γ sb i (fn_rec n)
      ∗ (rec_owned Γ sb i (fn_rec n') -∗ inode_owned Γ sb i n').
  Proof.
    intros Hb Hb' Hty.
    pose proof Hb' as (Ha' & He' & Hblk' & Hsz' & Hnl').
    assert (Hnn : fn_nlink n' = fn_nlink n).
    { destruct Hb as (_ & _ & _ & _ & Hnl). rewrite Hnl Hnl' //. }
    pose proof (fn_bare_indb n' Hb') as Hind'.
    pose proof (dir_entries_bare n' Hb') as Hent'.
    pose proof (inode_local_bare i n' Hb' Hty) as Hloc'.
    rewrite /inode_owned /inode_phi /inode_ghost.
    iIntros "[(Hr & _ & _) (Ha & _ & _)]". iFrame "Hr". iIntros "Hr".
    iSplitL "Hr".
    { rewrite Hblk' big_sepM_empty /ind_owned (decide_True _ _ Hind').
      iFrame "Hr". auto. }
    rewrite /ent_toks Hent' big_sepM_empty Hnn.
    iSplitL "Ha"; [iExact "Ha" |].
    iSplitR; [auto |]. iPureIntro. exact Hloc'.
  Qed.

  (* the record write inside a whole inode.  The addresses may move (this is
     also the "attach a freshly allocated direct block" step), as long as no
     slot the node ALREADY owns changes address. *)
  Definition fn_addrs_kept (n n' : fs_node) : Prop :=
    forall k, is_Some (fn_blk n !! k) -> fn_naddr n' k = fn_naddr n k.

  Lemma inode_phi_rec_move Γ sb i n n' :
    fn_blk n' = fn_blk n ->
    fn_ent n' = fn_ent n ->
    fn_indb n' = fn_indb n ->
    fn_addrs_kept n n' ->
    inode_phi Γ sb i n ⊢
      rec_owned Γ sb i (fn_rec n)
      ∗ (rec_owned Γ sb i (fn_rec n') -∗ inode_phi Γ sb i n').
  Proof.
    intros Hblk Hent Hind Hkept.
    iIntros "(Hr & Hb & Hi)". iFrame "Hr". iIntros "Hr".
    rewrite /inode_phi. iFrame "Hr".
    iSplitL "Hb".
    - rewrite Hblk. iApply (big_sepM_mono with "Hb").
      intros k bs Hk; simpl.
      assert (Hs : is_Some (fn_blk n !! k)) by (by exists bs).
      rewrite (Hkept k Hs) //.
    - rewrite /ind_owned Hind Hent //.
  Qed.

  (* (b) one data block's bytes move -- writei, and the readings follow *)
  Definition fn_set_blk (n : fs_node) (k : nat) (bs : list (bv 8)) : fs_node :=
    MkNode (fn_rec n) (fn_ent n) (<[k := bs]> (fn_blk n)).

  Lemma fn_naddr_set_blk n k bs : fn_naddr (fn_set_blk n k bs) = fn_naddr n.
  Proof. done. Qed.
  Lemma fn_indb_set_blk n k bs : fn_indb (fn_set_blk n k bs) = fn_indb n.
  Proof. done. Qed.

  Lemma inode_phi_blk_move Γ sb i n k bs bs' :
    fn_blk n !! k = Some bs ->
    inode_phi Γ sb i n ⊢
      blk_owned Γ (fn_naddr n k) bs
      ∗ (blk_owned Γ (fn_naddr n k) bs'
         -∗ inode_phi Γ sb i (fn_set_blk n k bs')).
  Proof.
    intros Hk. iIntros "(Hr & Hb & Hi)".
    iDestruct (big_sepM_insert_acc _ _ k bs Hk with "Hb") as "[$ Hb]".
    iIntros "Hnew". iDestruct ("Hb" with "Hnew") as "Hb".
    rewrite /inode_phi /fn_set_blk /=. by iFrame.
  Qed.

  (* (c) ATTACH a block the node did not own -- balloc's block arriving at a
     slot whose address the record (or the indirect block) already names.
     Together with (a)/(d) this is bmap's growth step; used alone with the
     size unchanged it is [writei]'s PARTIAL FAILURE, which commits the block
     without committing the size. *)
  Lemma inode_phi_blk_add Γ sb i n k bs :
    fn_blk n !! k = None ->
    inode_phi Γ sb i n ∗ blk_owned Γ (fn_naddr n k) bs
    ⊢ inode_phi Γ sb i (fn_set_blk n k bs).
  Proof.
    intros Hk. iIntros "((Hr & Hb & Hi) & Hnew)".
    rewrite /inode_phi /fn_set_blk /=. iFrame "Hr Hi".
    rewrite big_sepM_insert //. iFrame.
  Qed.

  (* (d) the indirect block's bytes move -- bmap writing one entry *)
  Lemma inode_phi_ind_move Γ sb i n n' :
    fn_rec n' = fn_rec n ->
    fn_blk n' = fn_blk n ->
    fn_addrs_kept n n' ->
    fn_indb n <> 0 ->
    inode_phi Γ sb i n ⊢
      blk_owned Γ (fn_indb n) (ind_bytes (fn_ent n))
      ∗ (blk_owned Γ (fn_indb n) (ind_bytes (fn_ent n')) -∗ inode_phi Γ sb i n').
  Proof.
    intros Hrec Hblk Hkept Hnz.
    iIntros "(Hr & Hb & Hi)".
    rewrite {1}/ind_owned decide_False //.
    iFrame "Hi". iIntros "Hi".
    rewrite /inode_phi /rec_owned Hrec. iFrame "Hr".
    iSplitL "Hb".
    - rewrite Hblk. iApply (big_sepM_mono with "Hb").
      intros k bs Hk; simpl.
      assert (Hs : is_Some (fn_blk n !! k)) by (by exists bs).
      rewrite (Hkept k Hs) //.
    - rewrite /ind_owned /fn_indb Hrec decide_False //.
  Qed.

  (* (e) the indirect block is CREATED -- the record gains addrs[12] and the
     new block arrives *)
  Lemma inode_phi_ind_create Γ sb i n n' :
    fn_blk n' = fn_blk n ->
    fn_addrs_kept n n' ->
    fn_indb n = 0 ->
    fn_indb n' <> 0 ->
    inode_phi Γ sb i n ⊢
      rec_owned Γ sb i (fn_rec n)
      ∗ (rec_owned Γ sb i (fn_rec n')
         -∗ blk_owned Γ (fn_indb n') (ind_bytes (fn_ent n'))
         -∗ inode_phi Γ sb i n').
  Proof.
    intros Hblk Hkept Hz Hnz.
    iIntros "(Hr & Hb & _)". iFrame "Hr". iIntros "Hr Hnew".
    rewrite /inode_phi. iFrame "Hr".
    iSplitL "Hb".
    - rewrite Hblk. iApply (big_sepM_mono with "Hb").
      intros k bs Hk; simpl.
      assert (Hs : is_Some (fn_blk n !! k)) by (by exists bs).
      rewrite (Hkept k Hs) //.
    - rewrite /ind_owned decide_False //.
  Qed.

  (* (f) ITRUNC frees EVERY owned block -- the direct and indirect data
     blocks and the indirect block itself, whether or not they are below the
     size.  What comes back is the truncated record; the blocks go to
     [free_bitmap] (FsStateBitmap.bitmap_free). *)
  Lemma inode_phi_trunc Γ sb i n n' :
    fn_blk n' = ∅ ->
    fn_indb n' = 0 ->
    inode_phi Γ sb i n ⊢
      ([∗ map] k ↦ bs ∈ fn_blk n, blk_owned Γ (fn_naddr n k) bs)
      ∗ ind_owned Γ n
      ∗ rec_owned Γ sb i (fn_rec n)
      ∗ (rec_owned Γ sb i (fn_rec n') -∗ inode_phi Γ sb i n').
  Proof.
    intros Hblk Hind.
    iIntros "(Hr & Hb & Hi)".
    iSplitL "Hb"; [iExact "Hb" |].
    iSplitL "Hi"; [iExact "Hi" |].
    iSplitL "Hr"; [iExact "Hr" |].
    iIntros "Hr".
    rewrite /inode_phi Hblk big_sepM_empty /ind_owned (decide_True _ _ Hind).
    iFrame "Hr". auto.
  Qed.

  (* the indirect block, handed back as an anonymous block when it exists *)
  Lemma ind_owned_block Γ n :
    fn_indb n <> 0 ->
    ind_owned Γ n ⊢ blk_owned Γ (fn_indb n) (ind_bytes (fn_ent n)).
  Proof. intros Hnz. rewrite /ind_owned (decide_False _ _ Hnz) //. Qed.

  Lemma ind_owned_none Γ n : fn_indb n = 0 -> ind_owned Γ n ⊣⊢ emp.
  Proof. intros Hz. rewrite /ind_owned (decide_True _ _ Hz) //. Qed.

  (* ---------------------------------------------------------------- *)
  (*  8.  ENCODE LEMMAS -- the dirent moves, at the token layer         *)
  (*                                                                   *)
  (*  The BYTES of a dirent write move by (b) above; what is left is    *)
  (*  the token that rides with the entry.  The DELETE is stated at the *)
  (*  entry-map delta (the caller holds [dir_entries_zero]'s conclusion  *)
  (*  in that shape anyway); the INSERT is stated at the RECORD delta    *)
  (*  [dir_insert_at] and goes through section 2b's                      *)
  (*  [dir_entries_write], so it assumes no view equation.               *)
  (* ---------------------------------------------------------------- *)

  Lemma ent_toks_delete Γ i n n' s t :
    fn_orphan n' = fn_orphan n ->
    dir_entries n !! s = Some t ->
    dir_entries n' = delete s (dir_entries n) ->
    ent_toks Γ i n -∗ ent_tok Γ i (fn_orphan n) s t ∗ ent_toks Γ i n'.
  Proof.
    intros Horph Hs Hdel.
    rewrite /ent_toks (big_sepM_delete _ (dir_entries n) s t) //.
    iIntros "[$ H]". rewrite Hdel Horph //.
  Qed.

  (* THE INSERT TAKES THE RECORD DELTA, NOT THE ENTRY-MAP DELTA.  Its
     entry-map delta is [FsTree.dir_view_insert], read at [fs_node] by
     [dir_entries_write] above -- so a caller supplies what a dirlink
     postcondition actually says (which slot moved, and dirlink's guard)
     rather than an equation about the view. *)
  Lemma ent_toks_insert Γ i n n' k0 s z :
    fn_orphan n' = fn_orphan n ->
    fn_is_dir n = true -> fn_is_dir n' = true ->
    dir_first (fn_data n) (fn_nrec n) s = None ->
    dir_insert_at (fn_data n) (fn_data n') (fn_nrec n) (fn_nrec n') k0 s z ->
    ent_toks Γ i n -∗ ent_tok Γ i (fn_orphan n) s (bv_unsigned z) -∗
    ent_toks Γ i n'.
  Proof.
    intros Horph Hd Hd' Hnone Hins.
    rewrite /ent_toks (dir_entries_write n n' k0 s z Hd Hd' Hnone Hins) Horph.
    rewrite big_sepM_insert; [| exact (dir_entries_fresh n s Hnone)].
    iIntros "H Ht". iFrame.
  Qed.

  (* the ORPHAN step: the directory's own [nlink] reaches 0, the parent takes
     its ".." token back, and the entry becomes tokenless.  Everything else
     keeps its token, because [ent_tokenless] differs at ".." only. *)
  Lemma dot_ne_dotdot : DOT <> DOTDOT.
  Proof. rewrite /DOT /DOTDOT. intros H. inversion H. Qed.

  Lemma ent_tokenless_orphan_ne self orph orph' s t :
    s <> DOTDOT -> ent_tokenless self orph' s t = ent_tokenless self orph s t.
  Proof.
    intros Hne. rewrite /ent_tokenless (bool_decide_eq_false_2 _ Hne).
    by rewrite !andb_false_l.
  Qed.

  Lemma ent_tokenless_dotdot self orph t :
    ent_tokenless self orph DOTDOT t = (orph || bool_decide (t = self)).
  Proof.
    rewrite /ent_tokenless.
    rewrite (bool_decide_eq_false_2 (DOTDOT = DOT));
      [| intros H; by apply dot_ne_dotdot].
    by rewrite bool_decide_eq_true_2 // andb_true_l orb_false_l.
  Qed.

  Lemma ent_tok_dotdot Γ self orph t :
    ent_tok Γ self orph DOTDOT t
    ⊣⊢ (if orph || bool_decide (t = self) then emp else link_tok Γ t).
  Proof. rewrite /ent_tok ent_tokenless_dotdot //. Qed.

  (* [t <> i] is the SELF-PARENT exclusion: a directory whose [".."] names
     ITSELF is the root, whose record already carries no token (see
     [ent_tokenless]) -- there is nothing to hand back, and no kernel path
     orphans the root anyway. *)
  Lemma ent_toks_orphan Γ i n n' t :
    dir_entries n' = dir_entries n ->
    fn_orphan n = false ->
    fn_orphan n' = true ->
    dir_entries n !! DOTDOT = Some t ->
    t <> i ->
    ent_toks Γ i n -∗ link_tok Γ t ∗ ent_toks Γ i n'.
  Proof.
    intros Hents Ho Ho' Hdd Hne.
    rewrite /ent_toks Hents Ho Ho'.
    rewrite (big_sepM_delete (fun s t => ent_tok Γ i false s t)
               (dir_entries n) DOTDOT t) //.
    rewrite (big_sepM_delete (fun s t => ent_tok Γ i true s t)
               (dir_entries n) DOTDOT t) //.
    rewrite !ent_tok_dotdot.
    rewrite (bool_decide_eq_false_2 (t = i) Hne).
    cbn [orb].
    iIntros "[Hd H]". iFrame "Hd". iSplitR; [done |].
    iApply (big_sepM_mono with "H"). intros s v Hs; simpl.
    rewrite /ent_tok (ent_tokenless_orphan_ne i false true s v) //.
    intros ->. rewrite lookup_delete in Hs. done.
  Qed.

  (* ---------------------------------------------------------------- *)
  (*  9.  The readings, after a write                                  *)
  (* ---------------------------------------------------------------- *)

  Lemma fn_data_set_blk n k bs j :
    fn_data (fn_set_blk n k bs) j =
      if decide (j = k) then bs else fn_data n j.
  Proof.
    rewrite /fn_data /fn_set_blk /=.
    destruct (decide (j = k)) as [-> |].
    - by rewrite lookup_insert.
    - by rewrite lookup_insert_ne.
  Qed.

  (* what a [dir_written_at]/[dir_zeroed_at] hypothesis is stated over *)
  Lemma fn_file_byte_set_blk n k bs j :
    file_byte (fn_data (fn_set_blk n k bs)) j =
      if decide ((j `div` BSIZE)%nat = k)
      then bs !!! (j `mod` BSIZE)%nat
      else file_byte (fn_data n) j.
  Proof.
    rewrite /file_byte fn_data_set_blk.
    by destruct (decide ((j `div` BSIZE)%nat = k)).
  Qed.

  Lemma fn_size_set_blk n k bs : fn_size (fn_set_blk n k bs) = fn_size n.
  Proof. done. Qed.
  Lemma fn_is_dir_set_blk n k bs : fn_is_dir (fn_set_blk n k bs) = fn_is_dir n.
  Proof. done. Qed.
  Lemma fn_nlink_set_blk n k bs : fn_nlink (fn_set_blk n k bs) = fn_nlink n.
  Proof. done. Qed.
  Lemma fn_orphan_set_blk n k bs : fn_orphan (fn_set_blk n k bs) = fn_orphan n.
  Proof. done. Qed.

  (* ---------------------------------------------------------------- *)
  (*  10. The DIRENT moves at [dir_owned], and the link reading        *)
  (*                                                                   *)
  (*  Each hands the writer the Φ-part (whose bytes the log moves, by  *)
  (*  [inode_phi_blk_move]) and does the token move beside it.  The    *)
  (*  premise is a pure fact about ONE directory's own bytes: the      *)
  (*  removal's entry-map delta, which [dir_entries_zero] proves       *)
  (*  outright, and the link's RECORD delta, which                     *)
  (*  [dir_entries_write] turns into the view's.                       *)
  (* ---------------------------------------------------------------- *)

  (* the direction safety uses: at [nlink = 0] no entry points here *)
  Lemma inode_link_tok_nz Γ sb i n :
    inode_owned Γ sb i n -∗ link_tok Γ i -∗ ⌜fn_nlink n <> 0%nat⌝.
  Proof.
    iIntros "[_ (Ha & _ & _)] Ht".
    destruct (decide (fn_nlink n = 0%nat)) as [Hz | Hnz]; [| done].
    rewrite Hz. iDestruct (link_auth_zero_no_tok with "Ha Ht") as "[]".
  Qed.

  Lemma dir_owned_unlink Γ sb d n n' s t :
    fn_orphan n' = fn_orphan n ->
    fn_nlink n' = fn_nlink n ->
    dir_entries n !! s = Some t ->
    dir_entries n' = delete s (dir_entries n) ->
    inode_local d n' -> fn_is_dir n' = true ->
    dir_owned Γ sb d n ⊢
      inode_phi Γ sb d n
      ∗ ent_tok Γ d (fn_orphan n) s t
      ∗ (inode_phi Γ sb d n' -∗ dir_owned Γ sb d n').
  Proof.
    intros Horph Hnl Hs Hdel Hloc Hdir.
    iIntros "[[$ (Ha & Ht & _)] _]".
    iDestruct (ent_toks_delete Γ d n n' s t Horph Hs Hdel with "Ht") as "[$ Ht]".
    iIntros "Hphi".
    rewrite /dir_owned /inode_owned /inode_ghost Hnl. by iFrame.
  Qed.

  Lemma dir_owned_link Γ sb d n n' k0 s z :
    fn_orphan n' = fn_orphan n ->
    fn_nlink n' = fn_nlink n ->
    fn_is_dir n = true ->
    dir_first (fn_data n) (fn_nrec n) s = None ->
    dir_insert_at (fn_data n) (fn_data n') (fn_nrec n) (fn_nrec n') k0 s z ->
    inode_local d n' -> fn_is_dir n' = true ->
    dir_owned Γ sb d n ⊢
      inode_phi Γ sb d n
      ∗ (inode_phi Γ sb d n' -∗ ent_tok Γ d (fn_orphan n) s (bv_unsigned z)
         -∗ dir_owned Γ sb d n').
  Proof.
    intros Horph Hnl Hd Hnone Hins Hloc Hdir.
    iIntros "[[$ (Ha & Ht & _)] _]".
    iIntros "Hphi Htok".
    iDestruct (ent_toks_insert Γ d n n' k0 s z Horph Hd Hdir Hnone Hins
                 with "Ht Htok") as "Ht".
    rewrite /dir_owned /inode_owned /inode_ghost Hnl. by iFrame.
  Qed.

  (* the child's side of "unlink a directory": its [nlink] reaches 0, its
     ".." entry becomes TOKENLESS, and the token it held goes back to the
     parent.  The caller supplies the new [link_auth] because the RA move
     ([link_return] at the parent's own auth) is its to make. *)
  Lemma dir_owned_orphan Γ sb d n n' t :
    dir_entries n' = dir_entries n ->
    fn_orphan n = false -> fn_orphan n' = true ->
    dir_entries n !! DOTDOT = Some t ->
    t <> d ->
    inode_local d n' -> fn_is_dir n' = true ->
    dir_owned Γ sb d n ⊢
      inode_phi Γ sb d n ∗ link_auth Γ d (fn_nlink n) ∗ link_tok Γ t
      ∗ (inode_phi Γ sb d n' -∗ link_auth Γ d (fn_nlink n')
         -∗ dir_owned Γ sb d n').
  Proof.
    intros Hents Ho Ho' Hdd Hne Hloc Hdir.
    iIntros "[[$ (Ha & Ht & _)] _]". iFrame "Ha".
    iDestruct (ent_toks_orphan Γ d n n' t Hents Ho Ho' Hdd Hne with "Ht")
      as "[$ Ht]".
    iIntros "Hphi Ha".
    rewrite /dir_owned /inode_owned /inode_ghost. by iFrame.
  Qed.

End InodeOwned.
