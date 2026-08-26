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
From iris.algebra Require Import auth gmap gmultiset numbers dfrac.
From iris.base_logic.lib Require Import iprop own.
Require Import BioDefs.
Require Import RiscvModelBytes.
Require Import BlockWords.
Require Import DinodeEnc.
Require Import DirentEnc.
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

(* A node with no blocks, no indirect block, size 0 and nlink 0 -- the
   shape of every FREE record, of [ialloc]'s claim box and of the corpse
   [itrunc]/[iput] leave.  It is defined HERE, before [inode_local], because
   that record's last clause [inl_bare_free] names it; section 2a below is
   where its readings live. *)
Definition fn_bare (n : fs_node) : Prop :=
  (* [13] is [FS_NDIRECT + 1], spelled as [dinode_wf] spells it *)
  di_addrs (fn_rec n) = replicate 13 (bv_0 32)
  /\ fn_ent n = replicate FS_NINDIRECT (bv_0 32)
  /\ fn_blk n = ∅
  /\ fn_size n = 0
  /\ fn_nlink n = 0%nat.

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
  (* ---- A FREE NODE IS BARE (durable-disk lane E-boot, plan section 5's
     second missing clause).  [inl_free] already says a type-0 record has no
     links; this says it names no block and has size zero, which is what
     makes a free inum's abstract value the CANONICAL [free_node] of its own
     record -- the form the inode region parks
     ([InodeRegion.ireg_top_park]) and the form a boot mint from the durable
     snapshot has to re-found the region at.  It is PER-OBJECT, it is true
     of every free record this kernel writes ([iput] clears the blocks and
     the size in [itrunc] BEFORE it clears the type) and of every mkfs
     image ([FsImg.fs_region_bare]), and it costs nothing at the two
     producers: [inode_local_bare] has it outright and [inode_local_of_ok]
     is vacuous at it, because [FsStateEra.inode_ok] carries [di_type <> 0].
     LAST, so no destructuring pattern above moves (durable-notes.md). *)
  inl_bare_free  : fn_type n = 0 -> fn_bare n;
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
Global Arguments inl_bare_free {_ _} _.

(* ------------------------------------------------------------------ *)
(*  2a'. THE THREE DIRECTORY CLAUSES THE ESCROW PAYLOADS CARRY, AT A    *)
(*       NODE (durable-disk lane E-clauses)                            *)
(*                                                                     *)
(*  [IcacheEscrow.ic_loaded] and [ipool_alloc] each carry three pure    *)
(*  directory facts beside [inode_local]'s, stated over the payload's   *)
(*  own record and total [data]:                                       *)
(*                                                                     *)
(*    [DirView.dir_ok]           every live entry's inum is inside the  *)
(*                               inode region ([< 16 * nib]);          *)
(*    [DirView.dir_dots_ix]      a LIVE directory's records 0 and 1     *)
(*                               POSITIONALLY are ["."] and [".."] --   *)
(*                               strictly stronger than [inl_dir_dot] / *)
(*                               [inl_dir_dotdot], which are about the  *)
(*                               name -> inum VIEW and blind to which   *)
(*                               record carries a name;                 *)
(*    [DirView.dir_orphan_clean] an ORPHAN directory ([nlink = 0])      *)
(*                               holds only dot records.                *)
(*                                                                     *)
(*  A BOOT MINT HAS TO RE-FOUND THOSE PAYLOADS, so the durable snapshot *)
(*  must carry them ([FsDurSnap.sk_dirloc]); this is the NODE-shaped    *)
(*  spelling both sides meet, with [FsStateEra.node_dir_local_of_ok]    *)
(*  the transport from a payload's [(dn, bm, data)] triple.             *)
(*                                                                     *)
(*  THEY ARE NOT CLAUSES OF [inode_local], AND ONE OF THEM CANNOT BE.   *)
(*  [inode_local i n] takes an inum and a node and nothing else, while  *)
(*  [dir_ok] needs the region's WIDTH -- a superblock number.  So the   *)
(*  three travel together here, are carried by the snapshot's byte half *)
(*  (which knows [S]'s superblock, exactly as [sk_regdom] does), and    *)
(*  reach the commit off the escrow payloads that already re-prove them *)
(*  at every [iunlock].                                                 *)
(* ------------------------------------------------------------------ *)
Definition node_dir_local (i : Z) (nib : nat) (n : fs_node) : Prop :=
  dir_ok nib (fn_rec n) (fn_data n)
  /\ dir_dots_ix i (fn_rec n) (fn_data n)
  /\ dir_orphan_clean (fn_rec n) (fn_data n).

(* the free-record discharge: a type-0 record is no directory, so all
   three are vacuous.  This is what the region's parked free node and the
   corpse ledger's markers use. *)
Lemma node_dir_local_free (i : Z) (nib : nat) (n : fs_node) :
  bv_unsigned (di_type (fn_rec n)) = 0 -> node_dir_local i nib n.
Proof.
  intros H0. rewrite /node_dir_local. split_and!.
  - exact (dir_ok_free nib (fn_rec n) (fn_data n) H0).
  - apply dir_dots_ix_not_dir. rewrite H0 /T_DIR_z. lia.
  - exact (dir_orphan_clean_free (fn_rec n) (fn_data n) H0).
Qed.

Definition node_dir_local_ok {i nib n} (H : node_dir_local i nib n) :
  dir_ok nib (fn_rec n) (fn_data n) := proj1 H.
Definition node_dir_local_ix {i nib n} (H : node_dir_local i nib n) :
  dir_dots_ix i (fn_rec n) (fn_data n) := proj1 (proj2 H).
Definition node_dir_local_orph {i nib n} (H : node_dir_local i nib n) :
  dir_orphan_clean (fn_rec n) (fn_data n) := proj2 (proj2 H).

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

(* [fn_bare] itself is defined ABOVE, immediately before [inode_local],
   because that record's last clause [inl_bare_free] names it. *)

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
  - intros _. exact Hb.
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

  (* THE INDIRECT BLOCK, at a share (durable-fs-plan.md sections 4 and 6).
     [ind_owned] is the [DfracOwn 1] reading and its text has not moved, so
     every existing [rewrite /ind_owned] still sees the [decide]. *)
  Definition ind_owned_q Γ (dq : dfrac) (n : fs_node) : iProp Σ :=
    (if decide (fn_indb n = 0) then emp
     else blk_owned_q Γ dq (fn_indb n) (ind_bytes (fn_ent n)))%I.

  Definition ind_owned Γ (n : fs_node) : iProp Σ :=
    (if decide (fn_indb n = 0) then emp
     else blk_owned Γ (fn_indb n) (ind_bytes (fn_ent n)))%I.

  Lemma ind_owned_1 Γ n : ind_owned Γ n = ind_owned_q Γ (DfracOwn 1) n.
  Proof. reflexivity. Qed.

  Global Instance ind_owned_q_timeless `{!GTimeless Γ} dq n :
    Timeless (ind_owned_q Γ dq n).
  Proof. rewrite /ind_owned_q. case_decide; apply _. Qed.

  Lemma ind_owned_q_split Γ (Hfr : phi_frac Γ) (q1 q2 : Qp) n :
    ind_owned_q Γ (DfracOwn (q1 + q2)) n
    ⊣⊢ ind_owned_q Γ (DfracOwn q1) n ∗ ind_owned_q Γ (DfracOwn q2) n.
  Proof.
    rewrite /ind_owned_q. case_decide.
    - iSplit; [iIntros "_"; iSplitR; done | iIntros "_"; done].
    - apply (blk_owned_q_split Γ Hfr).
  Qed.

  Lemma ind_owned_split_34 Γ (Hfr : phi_frac Γ) n :
    ind_owned Γ n
    ⊣⊢ ind_owned_q Γ (DfracOwn (3/4)) n ∗ ind_owned_q Γ (DfracOwn (1/4)) n.
  Proof.
    rewrite ind_owned_1 -(ind_owned_q_split Γ Hfr (3/4) (1/4)).
    rewrite Qp.three_quarter_quarter //.
  Qed.

  (* the Φ-only part of an inode: exactly its footprint *)
  Definition inode_phi Γ (sb : fs_sb) (i : Z) (n : fs_node) : iProp Σ :=
    (rec_owned Γ sb i (fn_rec n)
     ∗ ([∗ map] k ↦ bs ∈ fn_blk n, blk_owned Γ (fn_naddr n k) bs)
     ∗ ind_owned Γ n)%I.

  (* ---------------------------------------------------------------- *)
  (*  4.  The TYPE REGISTER's fragments an inode's entries carry       *)
  (*      (fs-state.md section 6.5 -- lane G5's ruling)                *)
  (* ---------------------------------------------------------------- *)

  (* a directory's up-pointing target: the inum its [".."] names.
     [inl_dir_dotdot] makes the [default] unreachable where it is read. *)
  Definition fn_dotdot (n : fs_node) : Z :=
    default 0 (dir_entries n !! DOTDOT).

  (* THE NODE'S REGISTER VALUE IS NOT A FUNCTION OF THE NODE, and create's
     mkdir arm is why.  The value is FIXED at the FILL -- the flush that
     takes the multiplicity from zero, where a retype is free -- and xv6
     writes the child's [".."] only AFTER it ([dirlink(ip, "..", dp)] runs
     two instructions later).  A value read off the [".."] ENTRY would
     therefore have to MOVE at that write, at a multiplicity of two, which
     is not a frame-preserving update.

     So the bundle binds the value existentially, tied to the node only
     through its TYPE ([fn_ity_ok]), and the ["."] fragment carries the
     PARENT -- under a guard: "if my [".."] entry exists, it names the [p]
     my value carries".  The guard is vacuous exactly across create's
     window and is discharged everywhere rmdir's (D1) reads it, because a
     LIVE directory has a [".."] ([inode_local]'s [inl_dir_dotdot]). *)
  Definition fn_ity_ok (n : fs_node) (v : ity) : Prop :=
    match v with
    | TFile => fn_is_dir n = false
    | TDir _ => fn_is_dir n = true
    end.

  Lemma fn_ity_ok_ex n : exists v, fn_ity_ok n v.
  Proof.
    destruct (fn_is_dir n) eqn:E; [exists (TDir 0) | exists TFile]; exact E.
  Qed.

  (* ...AND ITS MULTIPLICITY: one unit per COUNTED dirent, plus the ["."]
     a LIVE directory holds in its own bundle -- the [+1] xv6 deliberately
     does not count ("No ip->nlink++ for '.'").  An ORPHAN directory's
     dots are tokenless, so its multiplicity is its count, namely zero,
     and the free path's type write needs no fragment. *)
  Definition fn_mult (n : fs_node) : nat :=
    (fn_nlink n + if fn_is_dir n && negb (fn_orphan n) then 1%nat else 0%nat)%nat.

  (* at [nlink = 0] there is no bonus WHATEVER the type is, so an orphan's
     -- and a free record's -- register is empty and the type write is not
     an update at all *)
  Lemma fn_mult_zero n : fn_nlink n = 0%nat -> fn_mult n = 0%nat.
  Proof.
    intros Hz. rewrite /fn_mult Hz /fn_orphan
      (bool_decide_eq_true_2 (fn_nlink n = 0%nat) Hz) andb_false_r //.
  Qed.

  Lemma fn_mult_ge n : (fn_nlink n <= fn_mult n)%nat.
  Proof. rewrite /fn_mult. destruct (_ && _)%bool; lia. Qed.

  (* TWO EXEMPTIONS, and each is the kernel's own arithmetic.

     - EITHER DOT NAME AT AN ORPHAN.  [".."] is the parent's: it took that
       unit back when it removed the directory's name, and the record it
       left behind is exactly this kernel's grey ".." (fs-icache.md
       section 20).  ["."] is the home's OWN and it is the [+1] above,
       which an orphan does not have -- so it goes at the same step, and
       [ip->nlink--] at a directory returns TWO units (the name's and the
       ["."]'s), which is rmdir's own arithmetic.
     - THE ROOT'S [".."], which names the ROOT.  With it tokenless the
       image's [nlink = 1] at the root is unaccounted for by any entry,
       and the inode region can park one unspendable fragment there
       ([InodeRegion.ireg_keep]) -- which is the ONLY source
       [IgetLic]'s licence (f) has, since namei's [iget(ROOTINO)] holds
       nothing at all and every other fragment at the root lives in the
       root's own checked-out payload.

     THERE IS NO GENERAL SELF EXEMPTION any more (lane G5): ["."] at a
     LIVE directory carries a fragment, and it is that fragment that ties
     the region's existential parent to the [".."] entry. *)
  Definition ent_tokenless (self : Z) (orph : bool) (s : fname) (t : Z)
    : bool :=
    ((bool_decide (s = DOT) || bool_decide (s = DOTDOT)) && orph)
    || (bool_decide (s = DOTDOT) && bool_decide (t = self)).

  (* WHAT THE HOLDER ASSERTS ABOUT THE FRAGMENT'S VALUE, per flavour:

     - a NAME record (neither dot) in [self]: "if my target is a
       directory, its parent is ME".  It needs nothing about the target's
       type -- the fragment reveals it.
     - ["."]: the home's OWN value [sty].  At a directory that is
       [TDir (fn_dotdot n)], so this fragment is the TIE between the
       region's authority and the [".."] entry: rmdir's (D1).
     - [".."]: nothing.  The parent's own value is about the
       grandparent. *)
  Definition ent_ty_ok (self : Z) (dd : option Z) (s : fname) (ty : ity)
    : Prop :=
    if bool_decide (s = DOT)
    then forall p q, ty = TDir p -> dd = Some q -> q = p
    else if bool_decide (s = DOTDOT) then True
    else forall p, ty = TDir p -> p = self.

  (* the fragment at a KNOWN value -- the shape the pack/scatter and the
     boot's routing walk *)
  Definition ent_tok_at Γ (self : Z) (orph : bool) (s : fname) (t : Z)
      (ty : ity) : iProp Σ :=
    (if ent_tokenless self orph s t then emp else link_tok Γ t ty)%I.

  Definition ent_tok Γ (self : Z) (dd : option Z) (orph : bool) (s : fname)
      (t : Z) : iProp Σ :=
    (if ent_tokenless self orph s t then emp
     else ∃ ty, link_tok Γ t ty ∗ ⌜ent_ty_ok self dd s ty⌝)%I.

  Definition fn_dd (n : fs_node) : option Z := dir_entries n !! DOTDOT.

  Definition ent_toks Γ (i : Z) (n : fs_node) : iProp Σ :=
    ([∗ map] s ↦ t ∈ dir_entries n,
       ent_tok Γ i (fn_dd n) (fn_orphan n) s t)%I.

  (* the same thing as ONE resource-algebra element -- what the mint
     allocates (fs-state.md section 1, "Functoriality") *)
  Definition ent_elem (self : Z) (orph : bool) (s : fname) (t : Z)
      (ty : ity) : fsLinkUR :=
    if ent_tokenless self orph s t then ε else link_tok_elem t ty.

  (* THE PER-INODE ELEMENT.  [tyf] is the node's own choice of value for
     each of its entries; the CLAUSE on it is [node_ent_ok] below, and at
     the value level (FsState) it is read off the TARGET's node -- the one
     cross-inode reading in the whole design. *)
  Definition link_elem_node (i : Z) (n : fs_node) (v : ity)
      (tyf : fname -> ity) : fsLinkUR :=
    link_auth_elem i (fn_mult n) v
    ⋅ ([^op map] s ↦ t ∈ dir_entries n,
         ent_elem i (fn_orphan n) s t (tyf s)).

  Definition node_ent_ok (i : Z) (n : fs_node) (v : ity)
      (tyf : fname -> ity) : Prop :=
    fn_ity_ok n v
    /\ forall s t, dir_entries n !! s = Some t ->
         ent_tokenless i (fn_orphan n) s t = false ->
         ent_ty_ok i (fn_dd n) s (tyf s).

  (* the Φ-FREE part of an inode: the link ghosts and the local clauses. *)
  Definition inode_ghost Γ (i : Z) (n : fs_node) : iProp Σ :=
    (∃ v : ity, ⌜fn_ity_ok n v⌝ ∗ link_auth Γ i (fn_mult n) v
     ∗ ent_toks Γ i n ∗ ⌜inode_local i n⌝)%I.

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
  Proof. iIntros "[_ (%v & _ & _ & _ & $)]". Qed.

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

  Global Instance ent_tok_at_timeless Γ self orph s t ty :
    Timeless (ent_tok_at Γ self orph s t ty).
  Proof. rewrite /ent_tok_at. destruct (ent_tokenless self orph s t); apply _. Qed.

  Global Instance ent_tok_timeless Γ self dd orph s t :
    Timeless (ent_tok Γ self dd orph s t).
  Proof. rewrite /ent_tok. destruct (ent_tokenless self orph s t); apply _. Qed.

  (* the congruence at the READINGS: two nodes whose entry maps, orphan
     flags and register values agree carry the same fragments, whatever
     their records are *)
  Lemma ent_toks_cong_ent Γ i n n' :
    fn_orphan n' = fn_orphan n -> dir_entries n' = dir_entries n ->
    ent_toks Γ i n ⊣⊢ ent_toks Γ i n'.
  Proof. intros Ho He. rewrite /ent_toks /fn_dd He Ho //. Qed.

  (* a NON-directory owns no entries and therefore no fragments *)
  Lemma ent_toks_not_dir Γ i n : fn_is_dir n = false -> ⊢ ent_toks Γ i n.
  Proof.
    intros H. rewrite /ent_toks /dir_entries H big_sepM_empty. done.
  Qed.

  (* ...and neither does a directory whose record count is zero (a claim
     box, a truncated corpse) *)
  Lemma ent_toks_nrec0 Γ i n : fn_nrec n = 0%nat -> ⊢ ent_toks Γ i n.
  Proof.
    intros H. rewrite /ent_toks /dir_entries.
    destruct (fn_is_dir n); [| rewrite big_sepM_empty; done].
    rewrite H dir_view_nil big_sepM_empty. done.
  Qed.

  Global Instance ent_toks_timeless Γ i n : Timeless (ent_toks Γ i n).
  Proof. rewrite /ent_toks. apply _. Qed.

  (* the up-pointing target under a delete that is not the up-pointing
     record itself *)
  Lemma fn_dotdot_delete n n' s :
    s <> DOTDOT -> dir_entries n' = delete s (dir_entries n) ->
    fn_dotdot n' = fn_dotdot n.
  Proof.
    intros Hne Hdel. rewrite /fn_dotdot Hdel lookup_delete_ne //.
  Qed.

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
  (*                                                                    *)
  (*  The per-entry value is EXISTENTIAL in [ent_toks] and a FUNCTION in *)
  (*  [link_elem_node], so the gather has to CHOOSE it -- one function   *)
  (*  per node, built by induction over the entry map.                  *)
  (* ---------------------------------------------------------------- *)

  Lemma ent_toks_choose Γ (self : Z) (dd : option Z) (orph : bool)
      (m : gmap fname Z) :
    ([∗ map] s ↦ t ∈ m, ent_tok Γ self dd orph s t) -∗
    ∃ tyf : fname -> ity,
      ⌜forall s t, m !! s = Some t ->
         ent_tokenless self orph s t = false -> ent_ty_ok self dd s (tyf s)⌝
      ∗ ([∗ map] s ↦ t ∈ m, ent_tok_at Γ self orph s t (tyf s)).
  Proof.
    induction m as [| s t m Hs IH] using map_ind.
    - iIntros "_". iExists (fun _ => TFile). iSplitR.
      { iPureIntro. intros s' t' Hlk. rewrite lookup_empty in Hlk. done. }
      rewrite big_sepM_empty. done.
    - rewrite big_sepM_insert //. iIntros "[Ht Hm]".
      iDestruct (IH with "Hm") as (tyf) "[%Hok Hm]".
      rewrite /ent_tok.
      destruct (ent_tokenless self orph s t) eqn:Etl.
      + iExists tyf. iSplitR.
        { iPureIntro. intros s' t' Hlk Hnt.
          destruct (decide (s' = s)) as [-> | Hne].
          - rewrite lookup_insert in Hlk. inversion Hlk; subst t'.
            rewrite Etl in Hnt. done.
          - rewrite lookup_insert_ne // in Hlk. exact (Hok s' t' Hlk Hnt). }
        rewrite big_sepM_insert //. rewrite /ent_tok_at Etl. iFrame.
      + iDestruct "Ht" as (ty) "[Ht %Hty]".
        iExists (fun s' => if decide (s' = s) then ty else tyf s').
        iSplitR.
        { iPureIntro. intros s' t' Hlk Hnt.
          destruct (decide (s' = s)) as [-> | Hne].
          - exact Hty.
          - rewrite lookup_insert_ne // in Hlk. exact (Hok s' t' Hlk Hnt). }
        rewrite big_sepM_insert //.
        iSplitL "Ht".
        { rewrite /ent_tok_at Etl decide_True //. }
        iApply (big_sepM_mono with "Hm"). intros s' t' Hlk; simpl.
        assert (Hne : s' <> s) by (intros ->; rewrite Hs in Hlk; done).
        rewrite decide_False //.
  Qed.

  Lemma ent_toks_of_at Γ (self : Z) (dd : option Z) (orph : bool)
      (m : gmap fname Z) (tyf : fname -> ity) :
    (forall s t, m !! s = Some t ->
       ent_tokenless self orph s t = false -> ent_ty_ok self dd s (tyf s)) ->
    ([∗ map] s ↦ t ∈ m, ent_tok_at Γ self orph s t (tyf s)) -∗
    ([∗ map] s ↦ t ∈ m, ent_tok Γ self dd orph s t).
  Proof.
    intros Hok. iIntros "H".
    iApply (big_sepM_mono with "H"). intros s t Hlk; simpl.
    rewrite /ent_tok_at /ent_tok.
    destruct (ent_tokenless self orph s t) eqn:Etl; [done |].
    iIntros "Ht". iExists (tyf s). iFrame. iPureIntro.
    exact (Hok s t Hlk Etl).
  Qed.

  Lemma inode_link_pack Γ i n v tyf :
    link_auth Γ i (fn_mult n) v -∗
    ([∗ map] s ↦ t ∈ dir_entries n, ent_tok_at Γ i (fn_orphan n) s t (tyf s)) -∗
    own (γlink Γ) (link_elem_node i n v tyf).
  Proof.
    iIntros "Ha Ht".
    iDestruct (own_gather_map_opt (γlink Γ)
                 (fun (s : fname) (t : Z) => link_tok_elem t (tyf s))
                 (fun (s : fname) (t : Z) => ent_tokenless i (fn_orphan n) s t)
                 (dir_entries n)
                 (link_auth_elem i (fn_mult n) v)
                with "Ha [Ht]") as "H".
    { iApply (big_sepM_mono with "Ht"). intros s t _; simpl.
      rewrite /ent_tok_at /link_tok /link_toks /link_tok_elem.
      destruct (ent_tokenless i (fn_orphan n) s t); done. }
    rewrite /link_elem_node /ent_elem //.
  Qed.

  Lemma inode_link_gather Γ i n v tyf (x : fsLinkUR) :
    own (γlink Γ) x -∗ link_auth Γ i (fn_mult n) v -∗
    ([∗ map] s ↦ t ∈ dir_entries n, ent_tok_at Γ i (fn_orphan n) s t (tyf s)) -∗
    own (γlink Γ) (x ⋅ link_elem_node i n v tyf).
  Proof.
    iIntros "Hx Ha Ht".
    iDestruct (own_op with "[$Hx $Ha]") as "Hxa".
    iDestruct (own_gather_map_opt (γlink Γ)
                 (fun (s : fname) (t : Z) => link_tok_elem t (tyf s))
                 (fun (s : fname) (t : Z) => ent_tokenless i (fn_orphan n) s t)
                 (dir_entries n)
                 (x ⋅ link_auth_elem i (fn_mult n) v)
                with "Hxa [Ht]") as "H".
    { iApply (big_sepM_mono with "Ht"). intros s t _; simpl.
      rewrite /ent_tok_at /link_tok /link_toks /link_tok_elem.
      destruct (ent_tokenless i (fn_orphan n) s t); done. }
    rewrite /link_elem_node /ent_elem -assoc //.
  Qed.

  Lemma inode_link_scatter Γ i n v tyf :
    own (γlink Γ) (link_elem_node i n v tyf) ⊢
    link_auth Γ i (fn_mult n) v
    ∗ ([∗ map] s ↦ t ∈ dir_entries n, ent_tok_at Γ i (fn_orphan n) s t (tyf s)).
  Proof.
    rewrite /link_elem_node own_op. iIntros "[$ Ht]".
    iDestruct (own_scatter_map_opt (γlink Γ)
                 (fun (s : fname) (t : Z) => link_tok_elem t (tyf s))
                 (fun (s : fname) (t : Z) => ent_tokenless i (fn_orphan n) s t)
                 (dir_entries n) with "[Ht]") as "H".
    { rewrite /ent_elem //. }
    iApply (big_sepM_mono with "H"). intros s t _; simpl.
    rewrite /ent_tok_at /link_tok /link_toks /link_tok_elem.
    destruct (ent_tokenless i (fn_orphan n) s t); done.
  Qed.

  Lemma inode_link_iff Γ i n :
    (∃ v, ⌜fn_ity_ok n v⌝ ∗ link_auth Γ i (fn_mult n) v) ∗ ent_toks Γ i n
    ⊣⊢ ∃ v tyf, ⌜node_ent_ok i n v tyf⌝
                ∗ own (γlink Γ) (link_elem_node i n v tyf).
  Proof.
    iSplit.
    - iIntros "[(%v & %Hv & Ha) Ht]".
      iDestruct (ent_toks_choose with "Ht") as (tyf) "[%Hok Ht]".
      iExists v, tyf. iSplitR; [iPureIntro; split; [exact Hv | exact Hok] |].
      iApply (inode_link_pack with "Ha Ht").
    - iIntros "(%v & %tyf & %Hok & Hown)".
      iDestruct (inode_link_scatter with "Hown") as "[Ha Ht]".
      iSplitL "Ha"; [iExists v; iSplitR; [iPureIntro; exact (proj1 Hok) | iExact "Ha"] |].
      iApply (ent_toks_of_at Γ i (fn_dd n) (fn_orphan n) (dir_entries n) tyf
                (proj2 Hok) with "Ht").
  Qed.

  (* the per-inode shape [FsState.fs_links] iterates: the whole register
     contribution as ONE [own] under the existential its choice function
     is bound by. *)
  Lemma inode_ghost_iff Γ i n :
    inode_ghost Γ i n
    ⊣⊢ (∃ v tyf, ⌜node_ent_ok i n v tyf⌝
                 ∗ own (γlink Γ) (link_elem_node i n v tyf))
       ∗ ⌜inode_local i n⌝.
  Proof.
    rewrite /inode_ghost -inode_link_iff.
    iSplit.
    - iIntros "(%v & %Hv & Ha & Ht & %Hl)".
      iFrame "Ht". iSplitL "Ha"; [| by iPureIntro].
      iExists v. by iFrame.
    - iIntros "[[(%v & %Hv & Ha) Ht] %Hl]".
      iExists v. by iFrame.
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
    assert (Hnl0 : fn_nlink n = 0%nat)
      by (destruct Hb as (_ & _ & _ & _ & Hnl); exact Hnl).
    rewrite /inode_owned /inode_phi /inode_ghost.
    iIntros "[(Hr & _ & _) (%v & _ & Ha & _ & _)]". iFrame "Hr". iIntros "Hr".
    iSplitL "Hr".
    { rewrite Hblk' big_sepM_empty /ind_owned (decide_True _ _ Hind').
      iFrame "Hr". auto. }
    destruct (fn_ity_ok_ex n') as [v' Hv'].
    assert (Hmz : fn_mult n = 0%nat) by exact (fn_mult_zero n Hnl0).
    assert (Hmz' : fn_mult n' = 0%nat) by exact (fn_mult_zero n' Hnl').
    iEval (rewrite Hmz) in "Ha".
    iEval (rewrite (link_auth_zero_retype Γ i v v')) in "Ha".
    assert (Hnr' : fn_nrec n' = 0%nat)
      by (rewrite /fn_nrec Hsz' dir_nrec_zero //).
    rewrite Hmz'.
    iExists v'. iSplitR; [by iPureIntro |].
    iSplitL "Ha"; [iExact "Ha" |].
    iSplitR; [iApply (ent_toks_nrec0 Γ i n' Hnr') |].
    iPureIntro. exact Hloc'.
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
    fn_dd n' = fn_dd n ->
    dir_entries n !! s = Some t ->
    dir_entries n' = delete s (dir_entries n) ->
    ent_toks Γ i n -∗
    ent_tok Γ i (fn_dd n) (fn_orphan n) s t ∗ ent_toks Γ i n'.
  Proof.
    intros Horph Hdd Hs Hdel.
    rewrite /ent_toks (big_sepM_delete _ (dir_entries n) s t) //.
    iIntros "[$ H]". rewrite Hdel Horph Hdd //.
  Qed.

  (* THE INSERT TAKES THE RECORD DELTA, NOT THE ENTRY-MAP DELTA.  Its
     entry-map delta is [FsTree.dir_view_insert], read at [fs_node] by
     [dir_entries_write] above -- so a caller supplies what a dirlink
     postcondition actually says (which slot moved, and dirlink's guard)
     rather than an equation about the view. *)
  Lemma ent_toks_insert Γ i n n' k0 s z :
    fn_orphan n' = fn_orphan n ->
    fn_dd n' = fn_dd n ->
    fn_is_dir n = true -> fn_is_dir n' = true ->
    dir_first (fn_data n) (fn_nrec n) s = None ->
    dir_insert_at (fn_data n) (fn_data n') (fn_nrec n) (fn_nrec n') k0 s z ->
    ent_toks Γ i n -∗
    ent_tok Γ i (fn_dd n) (fn_orphan n) s (bv_unsigned z) -∗
    ent_toks Γ i n'.
  Proof.
    intros Horph Hdd Hd Hd' Hnone Hins.
    rewrite /ent_toks (dir_entries_write n n' k0 s z Hd Hd' Hnone Hins)
      Horph Hdd.
    rewrite big_sepM_insert; [| exact (dir_entries_fresh n s Hnone)].
    iIntros "H Ht". iFrame.
  Qed.

  (* ...AND THE ONE THAT WRITES [".."] ITSELF, where the guard on the
     ["."] clause is DISCHARGED (create's mkdir arm).  Every other entry's
     clause is blind to [fn_dd], so only the ["."] record has to be
     re-proved -- and the fragment it holds is the one the FILL chose,
     which is exactly [TDir] of the [".."] target now being written. *)
  Lemma ent_toks_insert_dd Γ i n n' k0 z :
    fn_orphan n' = fn_orphan n ->
    fn_dd n = None ->
    fn_is_dir n = true -> fn_is_dir n' = true ->
    dir_first (fn_data n) (fn_nrec n) DOTDOT = None ->
    dir_insert_at (fn_data n) (fn_data n') (fn_nrec n) (fn_nrec n') k0
      DOTDOT z ->
    (forall ty, ent_ty_ok i (fn_dd n) DOT ty ->
       ent_ty_ok i (fn_dd n') DOT ty) ->
    ent_toks Γ i n -∗
    ent_tok Γ i (fn_dd n') (fn_orphan n) DOTDOT (bv_unsigned z) -∗
    ent_toks Γ i n'.
  Proof.
    intros Horph Hnone0 Hd Hd' Hnone Hins Hup.
    rewrite /ent_toks (dir_entries_write n n' k0 DOTDOT z Hd Hd' Hnone Hins)
      Horph.
    rewrite big_sepM_insert; [| exact (dir_entries_fresh n DOTDOT Hnone)].
    iIntros "H Ht". iFrame "Ht".
    iApply (big_sepM_mono with "H"). intros s v Hs; simpl.
    rewrite /ent_tok. destruct (ent_tokenless i (fn_orphan n) s v); [done |].
    iIntros "(%ty & Ht & %Hok)". iExists ty. iFrame "Ht". iPureIntro.
    destruct (decide (s = DOT)) as [-> | Hne]; [exact (Hup ty Hok) |].
    rewrite /ent_ty_ok (bool_decide_eq_false_2 (s = DOT) Hne) in Hok |- *.
    exact Hok.
  Qed.

  (* ---- the exemption's own arithmetic ------------------------------ *)

  Lemma dot_ne_dotdot : DOT <> DOTDOT.
  Proof. rewrite /DOT /DOTDOT. intros H. inversion H. Qed.

  (* a NAME record (neither dot) is never exempt, at any orphan flag *)
  Lemma ent_tokenless_name self orph s t :
    s <> DOT -> s <> DOTDOT -> ent_tokenless self orph s t = false.
  Proof.
    intros Hnd Hne. rewrite /ent_tokenless
      (bool_decide_eq_false_2 (s = DOT) Hnd)
      (bool_decide_eq_false_2 (s = DOTDOT) Hne).
    by destruct orph, (bool_decide (t = self)).
  Qed.

  Lemma ent_tokenless_orphan_ne self orph orph' s t :
    s <> DOT -> s <> DOTDOT ->
    ent_tokenless self orph' s t = ent_tokenless self orph s t.
  Proof.
    intros Hnd Hne.
    rewrite (ent_tokenless_name self orph' s t Hnd Hne)
            (ent_tokenless_name self orph s t Hnd Hne) //.
  Qed.

  (* ...and the ORPHANING step is MONOTONE at every entry: going orphan
     only ever REMOVES a demand, so an entry's unit is simply dropped
     rather than transported. *)
  Lemma ent_tokenless_orph_up self s t :
    ent_tokenless self false s t = true -> ent_tokenless self true s t = true.
  Proof.
    rewrite /ent_tokenless.
    destruct (bool_decide (s = DOT)), (bool_decide (s = DOTDOT)),
             (bool_decide (t = self)); simpl; auto.
  Qed.

  Lemma ent_tokenless_dotdot self orph t :
    ent_tokenless self orph DOTDOT t = (orph || bool_decide (t = self)).
  Proof.
    rewrite /ent_tokenless
      (bool_decide_eq_true_2 (DOTDOT = DOTDOT) eq_refl).
    destruct (bool_decide (DOTDOT = DOT)), orph, (bool_decide (t = self));
      reflexivity.
  Qed.

  (* the ["."] twin, and it is NOT the same statement any more: a live
     directory's ["."] carries a fragment -- the [+1] of [fn_mult] and the
     tie rmdir's (D1) reads. *)
  Lemma ent_tokenless_dot self orph t :
    ent_tokenless self orph DOT t = orph.
  Proof.
    rewrite /ent_tokenless (bool_decide_eq_true_2 (DOT = DOT) eq_refl)
      (bool_decide_eq_false_2 (DOT = DOTDOT) dot_ne_dotdot).
    by destruct orph, (bool_decide (t = self)).
  Qed.

  Lemma ent_ty_ok_dot self dd ty :
    (forall p q, ty = TDir p -> dd = Some q -> q = p) ->
    ent_ty_ok self dd DOT ty.
  Proof.
    intros H. rewrite /ent_ty_ok
      (bool_decide_eq_true_2 (DOT = DOT) eq_refl). exact H.
  Qed.

  Lemma ent_ty_ok_dot_none self ty : ent_ty_ok self None DOT ty.
  Proof. apply ent_ty_ok_dot. intros p q _ Hc. discriminate. Qed.

  (* THE (D1) READING, at the payload: a LIVE directory's ["."] fragment
     is [TDir] of its own [".."] target. *)
  Lemma ent_ty_ok_dot_read self dd p ty :
    ent_ty_ok self dd DOT ty -> ty = TDir p ->
    forall q, dd = Some q -> q = p.
  Proof.
    rewrite /ent_ty_ok (bool_decide_eq_true_2 (DOT = DOT) eq_refl).
    intros H Hty q Hq. exact (H p q Hty Hq).
  Qed.

  Lemma ent_ty_ok_dotdot self dd ty : ent_ty_ok self dd DOTDOT ty.
  Proof.
    rewrite /ent_ty_ok (bool_decide_eq_false_2 (DOTDOT = DOT)
                          (fun H => dot_ne_dotdot (eq_sym H)))
      (bool_decide_eq_true_2 (DOTDOT = DOTDOT) eq_refl) //.
  Qed.

  Lemma ent_ty_ok_name self dd s ty :
    s <> DOT -> s <> DOTDOT -> (forall p, ty = TDir p -> p = self) ->
    ent_ty_ok self dd s ty.
  Proof.
    intros Hd Hdd Hp. rewrite /ent_ty_ok
      (bool_decide_eq_false_2 (s = DOT) Hd)
      (bool_decide_eq_false_2 (s = DOTDOT) Hdd) //.
  Qed.

  (* THE FORM A WALK HANDS IN.  A [dirlink] holds the register fragment
     for the inum it is about to name; whether the entry it creates PAYS
     for it is the exemption's business, and at an exempt record the unit
     is simply dropped (the logic is affine). *)
  Lemma ent_tok_of_link Γ self dd orph s t ty :
    ent_ty_ok self dd s ty ->
    link_tok Γ t ty -∗ ent_tok Γ self dd orph s t.
  Proof.
    intros Hok. rewrite /ent_tok.
    destruct (ent_tokenless self orph s t); [iIntros "_"; done |].
    iIntros "Ht". iExists ty. by iFrame.
  Qed.

  (* the ORPHANING WEAKENING, at the resource: see [ent_tokenless_orph_up] *)
  Lemma ent_tok_orph_up Γ self dd s t :
    ent_tok Γ self dd false s t -∗ ent_tok Γ self dd true s t.
  Proof.
    rewrite /ent_tok. destruct (ent_tokenless self false s t) eqn:H0.
    - rewrite (ent_tokenless_orph_up self s t H0). iIntros "$".
    - destruct (ent_tokenless self true s t); iIntros "H"; done.
  Qed.

  Lemma ent_tok_open Γ self dd orph s t :
    ent_tokenless self orph s t = false ->
    ent_tok Γ self dd orph s t
    ⊣⊢ ∃ ty, link_tok Γ t ty ∗ ⌜ent_ty_ok self dd s ty⌝.
  Proof. intros H. rewrite /ent_tok H //. Qed.

  Lemma ent_tok_ne Γ self dd orph s t :
    s <> DOT -> s <> DOTDOT ->
    ent_tok Γ self dd orph s t
    ⊣⊢ ∃ ty, link_tok Γ t ty ∗ ⌜forall p, ty = TDir p -> p = self⌝.
  Proof.
    intros Hd Hdd.
    rewrite (ent_tok_open Γ self dd orph s t
               (ent_tokenless_name self orph s t Hd Hdd)).
    rewrite /ent_ty_ok (bool_decide_eq_false_2 (s = DOT) Hd)
      (bool_decide_eq_false_2 (s = DOTDOT) Hdd) //.
  Qed.

  Lemma ent_tok_dotdot Γ self dd orph t :
    ent_tok Γ self dd orph DOTDOT t
    ⊣⊢ (if orph || bool_decide (t = self) then emp else ∃ ty, link_tok Γ t ty).
  Proof.
    rewrite /ent_tok ent_tokenless_dotdot.
    destruct (orph || bool_decide (t = self)); [done |].
    iSplit.
    - iIntros "(%ty & Ht & _)". iExists ty. iFrame.
    - iIntros "(%ty & Ht)". iExists ty. iFrame.
      iPureIntro. exact (ent_ty_ok_dotdot self dd ty).
  Qed.

  Lemma ent_tok_dot Γ self dd orph t :
    ent_tok Γ self dd orph DOT t
    ⊣⊢ (if orph then emp
        else ∃ ty, link_tok Γ t ty ∗ ⌜ent_ty_ok self dd DOT ty⌝).
  Proof. rewrite /ent_tok ent_tokenless_dot. by destruct orph. Qed.

  (* THE ORPHAN STEP: the directory's own count reaches zero, BOTH its dot
     records become exempt, and the two fragments come out -- the [".."]'s,
     which is what pays for the parent's own [dp->nlink--], and the ["."]'s,
     which is the [+1] a live directory holds and which pays for the child's
     own second decrement.  The ["."]'s comes out WITH its clause, which is
     rmdir's (D1): its value is [TDir] of this directory's [".."] target.

     [t <> i] is the SELF-PARENT exclusion: a directory whose [".."] names
     ITSELF is the root, which carries no [".."] unit to hand back and which
     no kernel path orphans anyway. *)
  Lemma ent_toks_orphan Γ i n n' t :
    dir_entries n' = dir_entries n ->
    fn_orphan n = false ->
    fn_orphan n' = true ->
    dir_entries n !! DOTDOT = Some t ->
    dir_entries n !! DOT = Some i ->
    t <> i ->
    ent_toks Γ i n -∗
    (∃ ty, link_tok Γ t ty)
    ∗ (∃ ty, link_tok Γ i ty ∗ ⌜ent_ty_ok i (fn_dd n) DOT ty⌝)
    ∗ ent_toks Γ i n'.
  Proof.
    intros Hents Ho Ho' Hdd Hdt Hne.
    assert (Hdd' : fn_dd n' = fn_dd n) by (rewrite /fn_dd Hents //).
    rewrite /ent_toks Hents Ho Ho' Hdd'.
    rewrite (big_sepM_delete (fun s t => ent_tok Γ i (fn_dd n) false s t)
               (dir_entries n) DOTDOT t) //.
    rewrite (big_sepM_delete (fun s t => ent_tok Γ i (fn_dd n) true s t)
               (dir_entries n) DOTDOT t) //.
    assert (Hdt' : delete DOTDOT (dir_entries n) !! DOT = Some i)
      by (rewrite lookup_delete_ne;
          [exact Hdt | exact (fun H => dot_ne_dotdot (eq_sym H))]).
    rewrite (big_sepM_delete (fun s t => ent_tok Γ i (fn_dd n) false s t)
               (delete DOTDOT (dir_entries n)) DOT i) //.
    rewrite (big_sepM_delete (fun s t => ent_tok Γ i (fn_dd n) true s t)
               (delete DOTDOT (dir_entries n)) DOT i) //.
    rewrite !ent_tok_dotdot !ent_tok_dot.
    rewrite (bool_decide_eq_false_2 (t = i) Hne).
    cbn [orb].
    iIntros "[Hdd [Hdt H]]". iFrame "Hdd Hdt".
    iSplitR; [done |]. iSplitR; [done |].
    iApply (big_sepM_mono with "H"). intros s v Hs; simpl.
    iApply ent_tok_orph_up.
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
  (* ---------------------------------------------------------------- *)

  (* the direction safety uses: at [nlink = 0] no entry points here *)
  Lemma inode_link_tok_nz Γ sb i n ty :
    inode_owned Γ sb i n -∗ link_tok Γ i ty -∗ ⌜fn_nlink n <> 0%nat⌝.
  Proof.
    iIntros "[_ (%v & _ & Ha & _ & _)] Ht".
    destruct (decide (fn_nlink n = 0%nat)) as [Hz | Hnz]; [| done].
    rewrite (fn_mult_zero n Hz).
    iDestruct (link_auth_zero_no_tok with "Ha Ht") as "[]".
  Qed.

  Lemma dir_owned_unlink Γ sb d n n' s t :
    fn_orphan n' = fn_orphan n ->
    fn_nlink n' = fn_nlink n ->
    fn_dd n' = fn_dd n ->
    fn_is_dir n' = fn_is_dir n ->
    s <> DOTDOT ->
    dir_entries n !! s = Some t ->
    dir_entries n' = delete s (dir_entries n) ->
    inode_local d n' -> fn_is_dir n' = true ->
    dir_owned Γ sb d n ⊢
      inode_phi Γ sb d n
      ∗ ent_tok Γ d (fn_dd n) (fn_orphan n) s t
      ∗ (inode_phi Γ sb d n' -∗ dir_owned Γ sb d n').
  Proof.
    intros Horph Hnl Hdd Hdir0 Hne Hs Hdel Hloc Hdir.
    iIntros "[[$ (%v & %Hv & Ha & Ht & _)] %Hdir1]".
    iDestruct (ent_toks_delete Γ d n n' s t Horph Hdd Hs Hdel with "Ht")
      as "[$ Ht]".
    iIntros "Hphi".
    rewrite /dir_owned /inode_owned /inode_ghost /fn_mult Hnl Horph Hdir0.
    iFrame "Hphi". iSplitL; [| by iPureIntro].
    iExists v. iSplitR.
    { iPureIntro. rewrite /fn_ity_ok in Hv |- *.
      destruct v; rewrite Hdir0; exact Hv. }
    iFrame "Ha Ht". by iPureIntro.
  Qed.

  Lemma dir_owned_link Γ sb d n n' k0 s z :
    fn_orphan n' = fn_orphan n ->
    fn_nlink n' = fn_nlink n ->
    fn_dd n' = fn_dd n ->
    fn_is_dir n = true ->
    dir_first (fn_data n) (fn_nrec n) s = None ->
    dir_insert_at (fn_data n) (fn_data n') (fn_nrec n) (fn_nrec n') k0 s z ->
    inode_local d n' -> fn_is_dir n' = true ->
    dir_owned Γ sb d n ⊢
      inode_phi Γ sb d n
      ∗ (inode_phi Γ sb d n' -∗
         ent_tok Γ d (fn_dd n) (fn_orphan n) s (bv_unsigned z)
         -∗ dir_owned Γ sb d n').
  Proof.
    intros Horph Hnl Hdd Hd Hnone Hins Hloc Hdir.
    iIntros "[[$ (%v & %Hv & Ha & Ht & _)] _]".
    iIntros "Hphi Htok".
    iDestruct (ent_toks_insert Γ d n n' k0 s z Horph Hdd Hd Hdir Hnone Hins
                 with "Ht Htok") as "Ht".
    rewrite /dir_owned /inode_owned /inode_ghost /fn_mult Hnl Horph Hd Hdir.
    iFrame "Hphi". iSplitL; [| by iPureIntro].
    iExists v. iSplitR.
    { iPureIntro. rewrite /fn_ity_ok in Hv |- *.
      destruct v; rewrite Hdir; rewrite Hd in Hv; exact Hv. }
    iFrame "Ha Ht". by iPureIntro.
  Qed.

  (* the child's side of "unlink a directory": its [nlink] reaches 0, BOTH
     its dot records become exempt, and the two fragments they held go
     out.  The caller supplies the new [link_auth] because the RA move is
     its to make. *)
  Lemma dir_owned_orphan Γ sb d n n' t :
    dir_entries n' = dir_entries n ->
    fn_orphan n = false -> fn_orphan n' = true ->
    fn_is_dir n' = fn_is_dir n ->
    dir_entries n !! DOTDOT = Some t ->
    dir_entries n !! DOT = Some d ->
    t <> d ->
    inode_local d n' -> fn_is_dir n' = true ->
    dir_owned Γ sb d n ⊢
      inode_phi Γ sb d n
      ∗ ∃ v, ⌜fn_ity_ok n v /\ ent_ty_ok d (fn_dd n) DOT v⌝
             ∗ link_auth Γ d (fn_mult n) v
             ∗ (∃ ty, link_tok Γ t ty) ∗ link_tok Γ d v
             ∗ (inode_phi Γ sb d n' -∗ link_auth Γ d (fn_mult n') v
                -∗ dir_owned Γ sb d n').
  Proof.
    intros Hents Ho Ho' Hdir0 Hdd Hdt Hne Hloc Hdir.
    iIntros "[[$ (%v & %Hv & Ha & Ht & _)] _]".
    iDestruct (ent_toks_orphan Γ d n n' t Hents Ho Ho' Hdd Hdt Hne
                 with "Ht") as "[Hup [(%ty & Hdotv & %Hok) Ht]]".
    iDestruct (link_auth_tok_agree with "Ha Hdotv") as %[-> _].
    iExists v. iFrame "Ha Hup Hdotv".
    iSplitR; [iPureIntro; split; [exact Hv | exact Hok] |].
    iIntros "Hphi Ha".
    rewrite /dir_owned /inode_owned /inode_ghost.
    iFrame "Hphi". iSplitL; [| by iPureIntro].
    iExists v. iSplitR.
    { iPureIntro. rewrite /fn_ity_ok in Hv |- *.
      destruct v; rewrite Hdir0; exact Hv. }
    iFrame "Ha Ht". by iPureIntro.
  Qed.

End InodeOwned.
