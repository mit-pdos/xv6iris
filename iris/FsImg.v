(* ======================================================================= *)
(*  FsImg.v -- THE PURE ON-DISK FILE-SYSTEM SEMANTICS: what a block image   *)
(*  MEANS, and what makes it a well-formed mkfs / durable state.            *)
(*  design: claude-notes/design/elf.md (the vm_compute rules this file      *)
(*  obeys), fs-icache.md, fs-inode.md, fs-bitmap.md (the consumers)         *)
(* ======================================================================= *)

(*  WHAT THIS FILE IS.

    [ElfFile.v] says what an ELF FILE means -- the memory image a loader
    must establish from a byte sequence.  This is the same move one layer
    out: what a DISK IMAGE means -- the file-system tree a kernel would
    read out of it -- said over the abstract block view

        P : Z -> list (bv 8)

    which is exactly the type [FsCrash.fs_blocks] produces and
    [FsCrash.fs_recovery] consumes.  So the image-check file above can
    instantiate [P := fs_blocks fsimg_dk] with zero glue, and this file
    never mentions an [iProp].

    ---- ONE READING, NOT A SECOND ONE -----------------------------------

    Everything the tree already knows how to say is REUSED and nothing is
    restated:

      the byte assembler   [RiscvModelBytes.assemble_bytes] -- the only one
                           in the tree; [fs_le_at] below is [ElfEnc.le_at]'s
                           body with the naming function replaced by a
                           list's [!!!], exactly as [ElfFile.elf_le_at] is;
      the dinode           [DinodeEnc.dinode] + its ENCODER [dinode_bytes].
                           [fs_dinode] is the decoder that file does not
                           have, and [fs_dinode_of_diblk] is the theorem
                           that it INVERTS the encoder -- which is what
                           makes it a reading of the tree's records rather
                           than a second, possibly disagreeing, one;
      the dirent view      [DirView.dir_inum] / [dir_name] / [dir_live] /
                           [dir_first] / [dir_nrec] / [dir_inums_ok] --
                           no second name decoder, no second record scan;
      the tree             [FsTree.node_of] / [dir_view] / [file_bytes] /
                           [path_at] / [dir_names_unique] / [DOT]/[DOTDOT];
      the bitmap           [BitmapEnc.bm_byte] -- [fs_bit] is the READ side
                           of that encoder, tied to it by [fs_bit_bm_bytes].

    Three names are restated as literals because their home files are not
    iris-free and this one must be: NDIRECT = 12, NINDIRECT = 256 and
    MAXFILE = 268 live in [InodeInv.v] (which imports [RiscvPtsto]), and
    LOGBLOCKS = 30 lives in [LogDefs.v].  [DinodeEnc.v]'s own rule -- state
    the geometry with literals, never with a folded constant -- applies.

    ---- EXECUTABILITY IS A DESIGN CONSTRAINT, NOT A BONUS ---------------

    Every definition here is meant to be run by [vm_compute] on a 2 MB
    image's block view, so (design/elf.md's measured rules): [Z]
    arithmetic, [nat] only as structural fuel, no [List.rev] anywhere,
    lists built in final order with the fuel counting DOWN.

    TWO PLACES WOULD OTHERWISE BE QUADRATIC, and each has a REDUCTION
    LEMMA that a consumer rewrites with BEFORE computing:

    - **the whole tree**.  [tree_of_disk] folds [node_at] over every inum,
      which forces every file's contents (~1 MB).  A per-file theorem must
      never do that, so [tree_of_disk_lookup] takes a lookup down to ONE
      [node_at], and [path_at_disk_dir] takes a one-step path walk down to
      ONE [DirView.dir_first] scan -- one dirlookup, no tree.

    - **a file's bytes**.  [FsTree.file_bytes data n] is [file_byte data
      <$> seq 0 n] with [n] the file's size IN BYTES: at [n = 58312] that
      is a unary [seq], and [file_byte] divides by [BSIZE] at every byte
      (unary [Nat.div] is linear in its dividend), so the cost is
      quadratic in the file size and the block is rebuilt once PER BYTE.
      [file_bytes_take_blocks] rewrites it to [take n (fs_take_blocks data
      0 nb)] -- one pass over [nb] blocks -- and [node_at_file] is that
      lemma delivered at [node_at].  A consumer that computes [node_at] on
      a 35 kB file WITHOUT rewriting first has not made a slow proof, it
      has made a non-terminating one.

    ---- [fsimg_wf] ------------------------------------------------------

    The mkfs / durable-state check, W1-W7 below, each with a one-line WHY
    naming its consumer and each with a bool -> Prop spec lemma stating
    the reused vocabulary's own predicate wherever one exists.  It reads
    the superblock, the log header, the 13 inode blocks, the bitmap block,
    the directories' contents and the indirect blocks -- tens of kB.  It
    does NOT force a single file's contents, and it must not: a conjunct
    that needed to would be a design error, not a slow check.

    iris-FREE (no proofmode, no ssreflect), like [ElfFile.v], [FsTree.v]
    and [RiscvModelBytes.v], so vanilla [rewrite ... by ...] stays
    available.                                                             *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
Require Import RiscvModelBytes.
Require Import BioDefs.  (* [BSIZE]: [InodeDefs.file_byte] indexes with it,
                            and [Require Import] does not propagate *)
Require Import BlockWords.
Require Import BitmapEnc.
Require Import DinodeEnc.
Require Import DirentEnc.
Require Import InodeDefs.
Require Import DirView.
Require Import FsTree.

Local Open Scope Z_scope.

(* ====================================================================== *)
(*  0.  GEOMETRY CONSTANTS AND THE LITTLE-ENDIAN READER                    *)
(* ====================================================================== *)

(* [InodeInv.NDIRECT] / [NINDIRECT] / [MAXFILE], restated: that file is not
   iris-free.  [DinodeEnc.v]'s rule -- the laws are stated with the
   literals the instruction stream produces -- applies to these too. *)
Definition FS_NDIRECT : nat := 12%nat.
Definition FS_NINDIRECT : nat := 256%nat.
Definition FS_MAXFILE : nat := 268%nat.

Definition FSMAGIC : Z := 0x10203040.
Definition ROOTINO : Z := 1.
Definition T_FILE_z : Z := 2.
Definition T_DEVICE_z : Z := 3.

(* [BioDefs.BSIZE] at [Z].  [InodeDefs.file_byte] indexes at [nat], the
   geometry arithmetic is at [Z]; this is the one bridge. *)
Definition BSIZE_z : Z := 1024.

Lemma BSIZE_z_nat : Z.of_nat BSIZE = BSIZE_z.
Proof. vm_compute. reflexivity. Qed.

(* [ElfEnc.le_at]'s body with the buffer's naming function replaced by the
   list's total lookup -- the same move [ElfFile.elf_le_at] makes, and
   bottoming out in the tree's ONE assembler.  There is no second
   little-endian assembler anywhere below this. *)
Definition fs_le_at (bs : list (bv 8)) (o n : nat) : Z :=
  assemble_bytes ((fun j => bs !!! (o + j)%nat) <$> seq 0 n).

Lemma fs_le_at_2 (bs : list (bv 8)) (o : nat) :
  fs_le_at bs o 2 = assemble_bytes [bs !!! (o + 0)%nat; bs !!! (o + 1)%nat].
Proof. reflexivity. Qed.

Lemma fs_le_at_4 (bs : list (bv 8)) (o : nat) :
  fs_le_at bs o 4
  = assemble_bytes [bs !!! (o + 0)%nat; bs !!! (o + 1)%nat;
                    bs !!! (o + 2)%nat; bs !!! (o + 3)%nat].
Proof. reflexivity. Qed.

(* the two round trips: assembling a field's own bytes gives the field
   back.  [DinodeEnc.half_bytes] / [BlockWords.word_bytes] are the
   encoders, so these say [fs_le_at] INVERTS them. *)
Lemma half_bytes_dec (w : bv 16) :
  Z_to_bv 16 (assemble_bytes (half_bytes w)) = w.
Proof.
  apply (bv_eq_of_bytes (n := 2)). intros j Hj.
  transitivity (half_bytes w !!! j).
  - apply (nth_byte_assemble_len 16 (half_bytes w) j);
      [rewrite half_bytes_length; cbn; lia | rewrite half_bytes_length; lia].
  - destruct j as [|[|j]]; [reflexivity | reflexivity | exfalso; lia].
Qed.

Lemma word_bytes_dec (w : bv 32) :
  Z_to_bv 32 (assemble_bytes (word_bytes w)) = w.
Proof.
  apply (bv_eq_of_bytes (n := 4)). intros j Hj.
  transitivity (word_bytes w !!! j).
  - apply (nth_byte_assemble_len 32 (word_bytes w) j);
      [rewrite word_bytes_length; cbn; lia | rewrite word_bytes_length; lia].
  - destruct j as [|[|[|[|j]]]];
      [reflexivity | reflexivity | reflexivity | reflexivity | exfalso; lia].
Qed.

Lemma fs_le_half_at (bs : list (bv 8)) (o : nat) (w : bv 16) :
  (forall j : nat, (j < 2)%nat -> bs !!! (o + j)%nat = nth_byte w j) ->
  Z_to_bv 16 (fs_le_at bs o 2) = w.
Proof.
  intros H. rewrite fs_le_at_2, (H 0%nat ltac:(lia)), (H 1%nat ltac:(lia)).
  exact (half_bytes_dec w).
Qed.

Lemma fs_le_word_at (bs : list (bv 8)) (o : nat) (w : bv 32) :
  (forall j : nat, (j < 4)%nat -> bs !!! (o + j)%nat = nth_byte w j) ->
  Z_to_bv 32 (fs_le_at bs o 4) = w.
Proof.
  intros H.
  rewrite fs_le_at_4, (H 0%nat ltac:(lia)), (H 1%nat ltac:(lia)),
    (H 2%nat ltac:(lia)), (H 3%nat ltac:(lia)).
  exact (word_bytes_dec w).
Qed.

(* a byte of an all-zero little-endian value is zero -- W2's byte reading *)
Lemma assemble_bytes_zero_byte (bs : list (bv 8)) (j : nat) :
  assemble_bytes bs = 0 -> (j < length bs)%nat -> bs !!! j = bv_0 8.
Proof.
  intros Hz Hj. pose proof (assemble_bytes_byte bs j Hj) as Hb.
  rewrite Hz in Hb. rewrite Z.shiftr_0_l, Zmod_0_l in Hb.
  apply bv_eq. rewrite <- Hb. reflexivity.
Qed.

(* the seq/forallb bridge every conjunct's spec lemma peels with *)
Lemma forallb_seq (f : nat -> bool) (n k : nat) :
  List.forallb f (seq 0 n) = true -> (k < n)%nat -> f k = true.
Proof.
  intros H Hk. rewrite List.forallb_forall in H. apply H.
  apply elem_of_list_In, elem_of_seq. lia.
Qed.

(* ====================================================================== *)
(*  1.  THE SUPERBLOCK                                                     *)
(* ====================================================================== *)

(* [struct superblock] (kernel/fs.h), eight little-endian [uint]s in block
   1.  The offsets are the ones the code's own loads use:
   [BitmapInv.sb_size] at +4 and [sb_bmapstart] at +28 (design/fs-bitmap.md
   reads both off balloc's instruction stream), SpecInitlog at +20,
   InodeInv at +24. *)
Record fs_sb := MkFsSb {
  sb_magic : Z;
  sb_size : Z;
  sb_nblocks : Z;
  sb_ninodes : Z;
  sb_nlog : Z;
  sb_logstart : Z;
  sb_inodestart : Z;
  sb_bmapstart : Z;
}.

Global Instance fs_sb_eq_dec : EqDecision fs_sb.
Proof. solve_decision. Defined.

Definition SB_BNO : Z := 1.

Definition fs_parse_sb (P : Z -> list (bv 8)) : option fs_sb :=
  let bs := P SB_BNO in
  if (32 <=? length bs)%nat
  then Some (MkFsSb (fs_le_at bs 0 4) (fs_le_at bs 4 4) (fs_le_at bs 8 4)
                    (fs_le_at bs 12 4) (fs_le_at bs 16 4) (fs_le_at bs 20 4)
                    (fs_le_at bs 24 4) (fs_le_at bs 28 4))
  else None.

(* [ boot | super | log | inode blocks | bitmap | DATA ] *)
Definition fs_data_start (sb : fs_sb) : Z := sb_bmapstart sb + 1.

(* ====================================================================== *)
(*  2.  THE INODE RECORDS -- AND THAT THIS IS DinodeEnc'S INVERSE          *)
(* ====================================================================== *)

(* the [bv 32] coercion of an inum, [FsRep.inum_of] verbatim (that file is
   iris-heavy, so the one line lands here too) *)
Definition fs_inum_bv (i : Z) : bv 32 := Z_to_bv 32 i.

(* record [i]'s 64 bytes: [DinodeEnc.IBLOCK]'s block, [DinodeEnc.islot]'s
   slot.  A [drop] rather than a per-field index into the whole block --
   under [vm_compute] the difference is one 1024-cons walk against
   nineteen of them. *)
Definition fs_dinode_bytes (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
  : list (bv 8) :=
  drop (64 * islot (fs_inum_bv i))
       (P (IBLOCK (fs_inum_bv i) (sb_inodestart sb))).

(* THE DECODER.  Field offsets are [DinodeEnc]'s own (type@0 major@2
   minor@4 nlink@6 size@8 addrs@12, thirteen words). *)
Definition fs_dinode (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) : dinode :=
  let bs := fs_dinode_bytes P sb i in
  MkDinode (Z_to_bv 16 (fs_le_at bs 0 2))
           (Z_to_bv 16 (fs_le_at bs 2 2))
           (Z_to_bv 16 (fs_le_at bs 4 2))
           (Z_to_bv 16 (fs_le_at bs 6 2))
           (Z_to_bv 32 (fs_le_at bs 8 4))
           ((fun j => Z_to_bv 32 (fs_le_at bs (12 + 4 * j)%nat 4))
              <$> seq 0 13).

Lemma fs_dinode_wf (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  dinode_wf (fs_dinode P sb i).
Proof.
  unfold dinode_wf, fs_dinode. cbn [di_addrs].
  rewrite length_fmap, length_seq. reflexivity.
Qed.

(* **THE REUSE OBLIGATION, DISCHARGED.**  [DinodeEnc.v] carries the
   ENCODER; this says [fs_dinode] is its INVERSE, so the records this file
   reasons about are the very records [IcacheBoot.image_dinode] mints out
   of the same block.  Without it [fs_dinode] would be a second dinode
   reader with nothing tying it to the first. *)
Lemma fs_dinode_of_diblk (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (ds : list dinode) :
  diblk_wf ds ->
  P (IBLOCK (fs_inum_bv i) (sb_inodestart sb)) = diblk_bytes ds ->
  fs_dinode P sb i = ds !!! islot (fs_inum_bv i).
Proof.
  intros [Hlen Hall] Hblk.
  pose proof (islot_lt (fs_inum_bv i)) as Hk.
  assert (Hk' : (islot (fs_inum_bv i) < length ds)%nat) by lia.
  pose proof (diblk_wf_slot ds _ Hall Hk') as Hd.
  (* every byte of the window is the slot record's own byte *)
  assert (Hget : forall j : nat, (j < 64)%nat ->
            fs_dinode_bytes P sb i !!! j
            = dinode_bytes (ds !!! islot (fs_inum_bv i)) !!! j).
  { intros j Hj. unfold fs_dinode_bytes. rewrite Hblk.
    rewrite list_lookup_total_alt, lookup_drop, <- list_lookup_total_alt.
    apply (diblk_bytes_lookup_t ds _ j Hall Hk' Hj). }
  unfold fs_dinode. cbv zeta.
  unfold dinode_wf in Hd.
  destruct (ds !!! islot (fs_inum_bv i)) as [ty mj mn nl sz ad] eqn:Hdd.
  cbn [di_addrs] in Hd. f_equal.
  - apply fs_le_half_at. intros j Hj. rewrite (Hget (0 + j)%nat ltac:(lia)).
    rewrite Nat.add_0_l. exact (dinode_bytes_type_t _ j Hj).
  - apply fs_le_half_at. intros j Hj. rewrite (Hget (2 + j)%nat ltac:(lia)).
    exact (dinode_bytes_major_t _ j Hj).
  - apply fs_le_half_at. intros j Hj. rewrite (Hget (4 + j)%nat ltac:(lia)).
    exact (dinode_bytes_minor_t _ j Hj).
  - apply fs_le_half_at. intros j Hj. rewrite (Hget (6 + j)%nat ltac:(lia)).
    exact (dinode_bytes_nlink_t _ j Hj).
  - apply fs_le_word_at. intros j Hj. rewrite (Hget (8 + j)%nat ltac:(lia)).
    exact (dinode_bytes_size_t _ j Hj).
  - apply list_eq. intros q.
    rewrite list_lookup_fmap.
    destruct (Nat.lt_ge_cases q 13) as [Hq|Hq].
    + rewrite lookup_seq_lt by exact Hq. cbn [fmap option_fmap option_map].
      rewrite Nat.add_0_l.
      rewrite (list_lookup_lookup_total_lt ad q) by lia.
      f_equal. apply fs_le_word_at. intros j Hj.
      replace (12 + 4 * q + j)%nat with (12 + (4 * q + j))%nat by lia.
      rewrite (Hget (12 + (4 * q + j))%nat ltac:(lia)).
      rewrite (dinode_bytes_addrs_t _ (4 * q + j)%nat).
      cbn [di_addrs].
      rewrite list_lookup_total_alt.
      rewrite (ind_bytes_lookup ad q j ltac:(lia) Hj).
      cbn [default from_option]. reflexivity.
    + rewrite (lookup_ge_None_2 (seq 0 13) q) by (rewrite length_seq; lia).
      cbn [fmap option_fmap option_map].
      symmetry. apply lookup_ge_None_2. lia.
Qed.

(* ====================================================================== *)
(*  3.  A FILE'S CONTENTS, BLOCK-INDEXED                                   *)
(* ====================================================================== *)

(* the indirect block's 256 entries, ALWAYS 256 of them: no indirect block
   is 256 zeroes, which is [InodeInv.blkmap_wf]'s "no indirect block => no
   entries" clause read on the bytes.  The block is bound by a [let] so
   [vm_compute] reads it ONCE for all 256 entries. *)
Definition fs_ind_ents (P : Z -> list (bv 8)) (dn : dinode) : list Z :=
  let ib := bv_unsigned (di_addrs dn !!! 12%nat) in
  if ib =? 0 then replicate FS_NINDIRECT 0
  else let ibs := P ib in
       (fun j => fs_le_at ibs (4 * j)%nat 4) <$> seq 0 FS_NINDIRECT.

Lemma fs_ind_ents_length (P : Z -> list (bv 8)) (dn : dinode) :
  length (fs_ind_ents P dn) = FS_NINDIRECT.
Proof.
  unfold fs_ind_ents. destruct (_ =? 0).
  - apply length_replicate.
  - rewrite length_fmap, length_seq. reflexivity.
Qed.

(* file block [k]'s disk block number: [bmap]'s answer, with no allocation *)
Definition fs_blk_addr (P : Z -> list (bv 8)) (dn : dinode) (k : nat) : Z :=
  if (k <? FS_NDIRECT)%nat
  then bv_unsigned (di_addrs dn !!! k)
  else fs_ind_ents P dn !!! (k - FS_NDIRECT)%nat.

(* **THE [data] ARGUMENT [FsTree.node_of] WANTS**: block [k] of the file's
   content.  A HOLE reads as a block of zeroes, which is exactly
   [InodeInv.blk_holes_zero] -- so this function satisfies that clause by
   construction ([fs_data_of_holes] below) rather than by hypothesis.  Both
   the indirect block and the entry list are [let]-bound, so a walk over
   the file's blocks decodes them once. *)
Definition fs_data_of (P : Z -> list (bv 8)) (dn : dinode)
  : nat -> list (bv 8) :=
  let es := fs_ind_ents P dn in
  fun k => let a := if (k <? FS_NDIRECT)%nat
                    then bv_unsigned (di_addrs dn !!! k)
                    else es !!! (k - FS_NDIRECT)%nat in
           if a =? 0 then replicate BSIZE (bv_0 8) else P a.

Definition fs_file_data (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
  : nat -> list (bv 8) := fs_data_of P (fs_dinode P sb i).

Lemma fs_data_of_addr (P : Z -> list (bv 8)) (dn : dinode) (k : nat) :
  fs_data_of P dn k
  = if fs_blk_addr P dn k =? 0 then replicate BSIZE (bv_0 8)
    else P (fs_blk_addr P dn k).
Proof. unfold fs_data_of, fs_blk_addr. reflexivity. Qed.

Lemma fs_data_of_holes (P : Z -> list (bv 8)) (dn : dinode) (k : nat) :
  fs_blk_addr P dn k = 0 -> fs_data_of P dn k = replicate BSIZE (bv_0 8).
Proof. intros H. rewrite fs_data_of_addr, H. reflexivity. Qed.

(* every block a whole image hands back is BSIZE bytes -- [FsCrash]'s
   [fs_blocks_length] in one line, and [InodeInv.inode_sized]'s premise *)
Definition fs_blocks_full (P : Z -> list (bv 8)) : Prop :=
  forall b : Z, length (P b) = BSIZE.

Lemma fs_data_of_sized (P : Z -> list (bv 8)) (dn : dinode) :
  fs_blocks_full P -> forall k : nat, length (fs_data_of P dn k) = BSIZE.
Proof.
  intros HP k. rewrite fs_data_of_addr.
  destruct (fs_blk_addr P dn k =? 0); [apply length_replicate | apply HP].
Qed.

(* ====================================================================== *)
(*  4.  NODES, THE TREE, AND THE TWO REDUCTION LEMMAS                      *)
(* ====================================================================== *)

(* A free record ([type = 0]) represents no node at all -- [FsTree]'s
   [node_rep] demands a nonzero type, so the tree never contains one. *)
Definition node_at (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
  : option fsnode :=
  let dn := fs_dinode P sb i in
  if bv_unsigned (di_type dn) =? 0 then None
  else Some (node_of dn (fs_data_of P dn)).

Lemma node_at_live (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  node_at P sb i = Some (node_of (fs_dinode P sb i) (fs_file_data P sb i)).
Proof.
  intros H. unfold node_at, fs_file_data.
  destruct (bv_unsigned (di_type (fs_dinode P sb i)) =? 0) eqn:E;
    [| reflexivity].
  exfalso. apply H. apply Z.eqb_eq. exact E.
Qed.

Lemma node_at_free (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  bv_unsigned (di_type (fs_dinode P sb i)) = 0 -> node_at P sb i = None.
Proof.
  intros H. unfold node_at. rewrite H. reflexivity.
Qed.

(* the node store: fuel counts DOWN, entries are inserted as they are met,
   nothing is reversed *)
Fixpoint fs_nodes_upto (P : Z -> list (bv 8)) (sb : fs_sb) (n : nat)
  : gmap Z fsnode :=
  match n with
  | O => ∅
  | S m => match node_at P sb (Z.of_nat m) with
           | Some nd => <[Z.of_nat m := nd]> (fs_nodes_upto P sb m)
           | None => fs_nodes_upto P sb m
           end
  end.

Definition tree_of_disk (P : Z -> list (bv 8)) (sb : fs_sb) : fstree :=
  MkTree (fs_nodes_upto P sb (Z.to_nat (sb_ninodes sb))) ROOTINO.

Lemma fs_nodes_upto_lookup_out (P : Z -> list (bv 8)) (sb : fs_sb)
    (n : nat) (i : Z) :
  i < 0 \/ Z.of_nat n <= i -> fs_nodes_upto P sb n !! i = None.
Proof.
  induction n as [|m IH]; intros Hi; [reflexivity |].
  cbn [fs_nodes_upto]. rewrite Nat2Z.inj_succ in Hi.
  destruct (node_at P sb (Z.of_nat m)) as [nd|].
  - rewrite lookup_insert_ne by lia. apply IH. lia.
  - apply IH. lia.
Qed.

(* **THE LOOKUP LEMMA, AND IT IS LOAD-BEARING FOR PERFORMANCE.**  A
   consumer's per-file theorem computes ONE [node_at] -- one inode, one
   file -- never the whole store, which holds every file's contents. *)
Lemma fs_nodes_upto_lookup (P : Z -> list (bv 8)) (sb : fs_sb)
    (n : nat) (i : Z) :
  0 <= i < Z.of_nat n -> fs_nodes_upto P sb n !! i = node_at P sb i.
Proof.
  induction n as [|m IH]; intros Hi; [exfalso; lia |].
  rewrite Nat2Z.inj_succ in Hi. cbn [fs_nodes_upto].
  destruct (decide (i = Z.of_nat m)) as [->|Hne].
  - destruct (node_at P sb (Z.of_nat m)) as [nd|] eqn:Hn.
    + rewrite lookup_insert. reflexivity.
    + apply fs_nodes_upto_lookup_out. right. lia.
  - destruct (node_at P sb (Z.of_nat m)) as [nd|] eqn:Hn.
    + rewrite lookup_insert_ne by congruence. apply IH. lia.
    + apply IH. lia.
Qed.

Lemma tree_of_disk_lookup (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  0 <= i < sb_ninodes sb ->
  fs_nodes (tree_of_disk P sb) !! i = node_at P sb i.
Proof.
  intros Hi. cbn [fs_nodes tree_of_disk].
  apply fs_nodes_upto_lookup. rewrite Z2Nat.id by lia. exact Hi.
Qed.

Lemma tree_of_disk_lookup_out (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  i < 0 \/ sb_ninodes sb <= i ->
  fs_nodes (tree_of_disk P sb) !! i = None.
Proof.
  intros Hi. cbn [fs_nodes tree_of_disk].
  apply fs_nodes_upto_lookup_out.
  destruct (Z.lt_ge_cases i 0) as [Hneg|Hpos]; [left; exact Hneg |].
  right. lia.
Qed.

Lemma tree_of_disk_root (P : Z -> list (bv 8)) (sb : fs_sb) :
  fs_root (tree_of_disk P sb) = ROOTINO.
Proof. reflexivity. Qed.

(* ---- the path reduction ---------------------------------------------- *)

Lemma tree_ent_of_disk (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (f : fname) :
  0 <= i < sb_ninodes sb ->
  tree_ent (tree_of_disk P sb) i f
  = match node_at P sb i with
    | Some (NDir ents) => ents !! f
    | _ => None
    end.
Proof. intros Hi. unfold tree_ent. rewrite tree_of_disk_lookup by exact Hi.
  reflexivity. Qed.

Lemma path_at_disk_cons (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (f : fname) (p : list fname) :
  0 <= i < sb_ninodes sb ->
  path_at (tree_of_disk P sb) i (f :: p)
  = match match node_at P sb i with
          | Some (NDir ents) => ents !! f
          | _ => None
          end with
    | Some j => path_at (tree_of_disk P sb) j p
    | None => None
    end.
Proof.
  intros Hi. rewrite path_at_cons, (tree_ent_of_disk P sb i f Hi). reflexivity.
Qed.

(* the contract's form: one step out of a directory IS a [dir_view] lookup
   of that ONE inode's node *)
Lemma path_at_disk_singleton (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (f : fname) :
  0 <= i < sb_ninodes sb ->
  path_at (tree_of_disk P sb) i [f]
  = match node_at P sb i with
    | Some (NDir ents) => ents !! f
    | _ => None
    end.
Proof.
  intros Hi. rewrite path_at_singleton. apply tree_ent_of_disk. exact Hi.
Qed.

(* ...AND THE FORM TO ACTUALLY COMPUTE WITH.  [dir_view] is
   [O(nrec^2)] -- every record's [dir_wins] rescans the records before it
   -- and building it is pure waste when one name is wanted.
   [DirView.dir_first] is the single scan [dirlookup] itself performs, and
   [FsTree.dir_view_lookup] says the view's answer IS that scan's.  The
   type premise costs one dinode decode. *)
Lemma path_at_disk_dir (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (f : fname) :
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z ->
  path_at (tree_of_disk P sb) i [f]
  = (fun k => bv_unsigned (dir_inum (fs_file_data P sb i) k))
      <$> dir_first (fs_file_data P sb i)
            (dir_nrec (bv_unsigned (di_size (fs_dinode P sb i)))) f.
Proof.
  intros Hi Hty.
  rewrite (path_at_disk_singleton P sb i f Hi).
  rewrite (node_at_live P sb i) by (rewrite Hty; unfold T_DIR_z; lia).
  unfold node_of. rewrite decide_True by exact Hty.
  apply dir_view_lookup.
Qed.

(* ---- the file-bytes reduction ---------------------------------------- *)

(* the first [n] blocks of a file, concatenated: ONE pass, fuel counting
   down, nothing reversed *)
Fixpoint fs_take_blocks (data : nat -> list (bv 8)) (i n : nat)
  : list (bv 8) :=
  match n with
  | O => []
  | S m => (data i ++ fs_take_blocks data (S i) m)%list
  end.

(* the block/offset split, proved off [Nat.div_mod_eq] so no [Nat.Div0]
   lemma name is depended on *)
Lemma nat_block_split (i j : nat) :
  (j < BSIZE)%nat ->
  ((i * BSIZE + j) `div` BSIZE)%nat = i /\ ((i * BSIZE + j) `mod` BSIZE)%nat = j.
Proof.
  intros Hj.
  pose proof (Nat.div_mod_eq (i * BSIZE + j)%nat BSIZE) as He.
  pose proof (Nat.mod_upper_bound (i * BSIZE + j)%nat BSIZE
                ltac:(unfold BSIZE; lia)) as Hm.
  unfold BSIZE in *. lia.
Qed.

Lemma fs_take_blocks_lookup (data : nat -> list (bv 8)) (i n j : nat) :
  (forall q : nat, length (data q) = BSIZE) ->
  (j < n * BSIZE)%nat ->
  fs_take_blocks data i n !! j = Some (file_byte data (i * BSIZE + j)%nat).
Proof.
  intros Hlen. revert i j. induction n as [|m IH]; intros i j Hj;
    [exfalso; cbn in Hj; lia |].
  cbn [fs_take_blocks].
  destruct (Nat.lt_ge_cases j BSIZE) as [Hlt|Hge].
  - rewrite lookup_app_l by (rewrite Hlen; exact Hlt).
    unfold file_byte.
    destruct (nat_block_split i j Hlt) as [Hd Hr].
    rewrite Hd, Hr.
    apply list_lookup_lookup_total_lt. rewrite Hlen. exact Hlt.
  - rewrite lookup_app_r by (rewrite Hlen; exact Hge).
    rewrite Hlen.
    rewrite (IH (S i) (j - BSIZE)%nat) by (unfold BSIZE in *; lia).
    do 2 f_equal. unfold BSIZE in *. lia.
Qed.

(* **THE REDUCTION.**  [FsTree.file_bytes] is a per-BYTE walk that divides
   by BSIZE at every step and re-reads the block at every step; this is
   the same list as ONE pass over the file's blocks.  Rewrite with it
   before any [vm_compute] on a real file. *)
Lemma file_bytes_take_blocks (data : nat -> list (bv 8)) (n nb : nat) :
  (forall q : nat, length (data q) = BSIZE) ->
  (n <= nb * BSIZE)%nat ->
  file_bytes data n = take n (fs_take_blocks data 0 nb).
Proof.
  intros Hlen Hn. apply list_eq. intros j.
  unfold file_bytes. rewrite list_lookup_fmap.
  destruct (Nat.lt_ge_cases j n) as [Hj|Hj].
  - rewrite lookup_seq_lt by exact Hj. cbn [fmap option_fmap option_map].
    rewrite lookup_take by exact Hj.
    rewrite (fs_take_blocks_lookup data 0 nb j Hlen) by lia.
    rewrite Nat.mul_0_l, Nat.add_0_l. reflexivity.
  - rewrite (lookup_ge_None_2 (seq 0 n) j) by (rewrite length_seq; lia).
    cbn [fmap option_fmap option_map].
    symmetry. apply lookup_ge_None_2. rewrite length_take. lia.
Qed.

(* ceil(sz / BSIZE): the number of content blocks a file of size [sz] has *)
Definition fs_nblk (sz : Z) : Z := (sz + (BSIZE_z - 1)) / BSIZE_z.
Definition fs_nblocks (sz : Z) : nat := Z.to_nat (fs_nblk sz).

Lemma fs_nblk_cover (sz : Z) : 0 <= sz -> sz <= fs_nblk sz * BSIZE_z.
Proof.
  intros H. unfold fs_nblk. change (BSIZE_z - 1) with 1023.
  change BSIZE_z with 1024 in *.
  pose proof (Z.div_mod (sz + 1023) 1024 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (sz + 1023) 1024 ltac:(lia)) as Hm. lia.
Qed.

(* a block index whose byte range starts inside the file is below the count *)
Lemma fs_nblk_lt (sz k : Z) : 0 <= k -> k * BSIZE_z < sz -> k < fs_nblk sz.
Proof.
  intros Hk Hlt. unfold fs_nblk. change (BSIZE_z - 1) with 1023.
  change BSIZE_z with 1024 in *.
  pose proof (Z.div_mod (sz + 1023) 1024 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (sz + 1023) 1024 ltac:(lia)) as Hm. lia.
Qed.

(* the FILE arm of [node_at], delivered in the computable shape *)
Lemma node_at_file (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_blocks_full P ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> T_DIR_z ->
  node_at P sb i
  = Some (NFile
            (take (Z.to_nat (bv_unsigned (di_size (fs_dinode P sb i))))
                  (fs_take_blocks (fs_file_data P sb i) 0
                     (fs_nblocks (bv_unsigned (di_size (fs_dinode P sb i))))))).
Proof.
  intros HP Hnz Hnd.
  rewrite (node_at_live P sb i Hnz).
  unfold node_of. rewrite decide_False by exact Hnd. f_equal. f_equal.
  set (sz := bv_unsigned (di_size (fs_dinode P sb i))).
  assert (Hsz : 0 <= sz) by exact (proj1 (bv_unsigned_in_range _ _)).
  apply file_bytes_take_blocks.
  - intros q. apply fs_data_of_sized. exact HP.
  - unfold fs_nblocks.
    assert (Hnn : 0 <= fs_nblk sz)
      by (unfold fs_nblk, BSIZE_z; apply Z.div_pos; lia).
    apply Nat2Z.inj_le. rewrite Nat2Z.inj_mul.
    rewrite (Z2Nat.id sz Hsz), (Z2Nat.id (fs_nblk sz) Hnn), BSIZE_z_nat.
    exact (fs_nblk_cover sz Hsz).
Qed.

(* [FsTree.fsnode] carries no decidable equality of its own; a consumer's
   [bool_decide (node_at ... = Some (NFile bs))] needs one. *)
Global Instance fsnode_eq_dec : EqDecision fsnode.
Proof. solve_decision. Defined.

(* ====================================================================== *)
(*  5.  DUPLICATE-FREE COLLECTION (the W4/W6 workhorse)                    *)
(* ====================================================================== *)

(* [O(n log n)]: one gset built as the list is walked, refusing an element
   already in it.  Returning the set is what lets W5 read W4's answer
   instead of recomputing it. *)
Fixpoint gset_nodup {A : Type} `{Countable A} (l : list A)
  : option (gset A) :=
  match l with
  | [] => Some ∅
  | x :: r => match gset_nodup r with
              | None => None
              | Some s => if bool_decide (x ∈ s) then None else Some ({[x]} ∪ s)
              end
  end.

Lemma gset_nodup_set {A : Type} `{Countable A} (l : list A) (s : gset A) :
  gset_nodup l = Some s -> forall x : A, x ∈ s <-> x ∈ l.
Proof.
  revert s. induction l as [|y r IH]; intros s Hs x; cbn in Hs.
  - injection Hs as <-. rewrite elem_of_empty, elem_of_nil. tauto.
  - destruct (gset_nodup r) as [s0|] eqn:Hr; [| discriminate].
    destruct (bool_decide (y ∈ s0)) eqn:Hy; [discriminate |].
    injection Hs as <-. rewrite elem_of_union, elem_of_singleton.
    rewrite (IH s0 eq_refl x), elem_of_cons. tauto.
Qed.

Lemma gset_nodup_NoDup {A : Type} `{Countable A} (l : list A) (s : gset A) :
  gset_nodup l = Some s -> NoDup l.
Proof.
  revert s. induction l as [|y r IH]; intros s Hs; cbn in Hs.
  - apply NoDup_nil_2.
  - destruct (gset_nodup r) as [s0|] eqn:Hr; [| discriminate].
    destruct (bool_decide (y ∈ s0)) eqn:Hy; [discriminate |].
    apply NoDup_cons_2; [| exact (IH s0 eq_refl)].
    intros Hin. apply (proj1 (bool_decide_eq_false _) Hy).
    apply (gset_nodup_set r s0 Hr). exact Hin.
Qed.

(* ====================================================================== *)
(*  6.  W1 -- THE SUPERBLOCK'S OWN ARITHMETIC                              *)
(* ====================================================================== *)

(* WHY: every consumer's block geometry is read off these fields --
   [DinodeEnc.IBLOCK] off [inodestart], [BitmapInv.BBLOCK_single] off
   [bmapstart] and [size], [LogDefs.log_region_set] off [logstart].
   The equations are mkfs.c's own (mkfs/mkfs.c, main):
     nlog = LOGBLOCKS + 1;  logstart = 2;  inodestart = 2 + nlog;
     bmapstart = 2 + nlog + (NINODES / IPB + 1);
     size = FSSIZE = nmeta + nblocks.
   [ninodes / 16 + 1] is mkfs's own inode-block count, NOT ceil: they
   coincide except when 16 divides ninodes, where mkfs leaves one spare
   block.  [fs_sb_ok_inodes_fit] below is the weaker fact consumers want
   (the region covers every inum).
   [size <= 8 * BSIZE] is the single-bitmap-block simplification the whole
   tree stands on (design/fs-bitmap.md: FSSIZE = 2000 < BPB = 8192, so
   BBLOCK collapses and balloc's outer loop runs once).
   [ROOTINO < ninodes] is what lets W7 speak at all -- the root's record
   has to be INSIDE the region the tree covers -- and [0 < nblocks] is what
   makes the data region nonempty ([fs_sb_ok_meta]). *)
Definition fs_sb_wf (sb : fs_sb) : bool :=
  (sb_magic sb =? FSMAGIC) &&
  (sb_logstart sb =? 2) &&
  (sb_nlog sb =? 31) &&
  (sb_inodestart sb =? sb_logstart sb + sb_nlog sb) &&
  (sb_bmapstart sb =? sb_inodestart sb + (sb_ninodes sb / 16 + 1)) &&
  (sb_size sb =? fs_data_start sb + sb_nblocks sb) &&
  (ROOTINO <? sb_ninodes sb) &&
  (0 <? sb_nblocks sb) &&
  (sb_size sb <=? 8 * BSIZE_z).

Record fs_sb_ok (sb : fs_sb) : Prop := {
  sbo_magic : sb_magic sb = FSMAGIC;
  sbo_logstart : sb_logstart sb = 2;
  sbo_nlog : sb_nlog sb = 31;
  sbo_inodestart : sb_inodestart sb = sb_logstart sb + sb_nlog sb;
  sbo_bmapstart : sb_bmapstart sb = sb_inodestart sb + (sb_ninodes sb / 16 + 1);
  sbo_size : sb_size sb = fs_data_start sb + sb_nblocks sb;
  sbo_ninodes : ROOTINO < sb_ninodes sb;
  sbo_nblocks : 0 < sb_nblocks sb;
  sbo_one_bitmap : sb_size sb <= 8 * BSIZE_z;
}.

Lemma fs_sb_wf_ok (sb : fs_sb) : fs_sb_wf sb = true -> fs_sb_ok sb.
Proof.
  unfold fs_sb_wf. intros H. rewrite !andb_true_iff in H.
  destruct H as [[[[[[[[H1 H2] H3] H4] H5] H6] H7] H8] H9].
  apply Z.eqb_eq in H1, H2, H3, H4, H5, H6.
  apply Z.ltb_lt in H7, H8. apply Z.leb_le in H9.
  constructor; assumption.
Qed.

(* what a consumer actually wants out of W1: the inode region covers every
   inum and stops below the bitmap, and the data region is what is left *)
Lemma fs_sb_ok_inodes_fit (sb : fs_sb) :
  fs_sb_ok sb ->
  sb_inodestart sb + (sb_ninodes sb + 15) / 16 <= sb_bmapstart sb.
Proof.
  intros Hok. rewrite (sbo_bmapstart sb Hok).
  pose proof (sbo_ninodes sb Hok) as Hn. unfold ROOTINO in Hn.
  pose proof (Z.div_mod (sb_ninodes sb) 16 ltac:(lia)) as Hd.
  pose proof (Z.mod_pos_bound (sb_ninodes sb) 16 ltac:(lia)) as Hm.
  pose proof (Z.div_mod (sb_ninodes sb + 15) 16 ltac:(lia)) as Hd'.
  pose proof (Z.mod_pos_bound (sb_ninodes sb + 15) 16 ltac:(lia)) as Hm'.
  lia.
Qed.

Lemma fs_sb_ok_meta (sb : fs_sb) :
  fs_sb_ok sb ->
  2 < sb_inodestart sb /\ sb_inodestart sb < fs_data_start sb
  /\ fs_data_start sb <= sb_size sb.
Proof.
  intros Hok. pose proof (sbo_ninodes sb Hok) as Hn. unfold ROOTINO in Hn.
  assert (Hdi : 0 <= sb_ninodes sb / 16) by (apply Z.div_pos; lia).
  pose proof (sbo_logstart sb Hok). pose proof (sbo_nlog sb Hok).
  pose proof (sbo_inodestart sb Hok). pose proof (sbo_bmapstart sb Hok).
  pose proof (sbo_size sb Hok). pose proof (sbo_nblocks sb Hok).
  unfold fs_data_start in *. lia.
Qed.

(* ====================================================================== *)
(*  7.  W2 -- THE LOG IS CLEAN                                             *)
(* ====================================================================== *)

(* WHY: [FsCrash.fs_recovery_clean] says that at [hdr_n = 0] recovery IS
   [fs_restrict] of the home set, i.e. the durable state is the image
   itself -- the adequacy client's whole crash story.  [LogDefs.hdr_n bs]
   is [assemble_bytes (take 4 bs)] and [log_hdr_bno logstart] is
   [logstart], so the term below is that one UNFOLDED: the check file
   bridges with [rewrite /hdr_n /log_hdr_bno].  It is spelled out rather
   than imported because [LogDefs.v] is iris-heavy. *)
Definition fs_log_clean (P : Z -> list (bv 8)) (sb : fs_sb) : bool :=
  assemble_bytes (take 4 (P (sb_logstart sb))) =? 0.

Lemma fs_log_clean_spec (P : Z -> list (bv 8)) (sb : fs_sb) :
  fs_log_clean P sb = true
  <-> assemble_bytes (take 4 (P (sb_logstart sb))) = 0.
Proof. unfold fs_log_clean. apply Z.eqb_eq. Qed.

(* ...and the same fact at the BYTES, which is what "the header says zero"
   means on a disk *)
Lemma fs_log_clean_bytes (P : Z -> list (bv 8)) (sb : fs_sb) (j : nat) :
  fs_log_clean P sb = true -> (4 <= length (P (sb_logstart sb)))%nat ->
  (j < 4)%nat -> P (sb_logstart sb) !!! j = bv_0 8.
Proof.
  intros Hc Hlen Hj.
  apply fs_log_clean_spec in Hc.
  assert (Hb : take 4 (P (sb_logstart sb)) !!! j = bv_0 8).
  { apply (assemble_bytes_zero_byte _ j Hc). rewrite length_take. lia. }
  rewrite <- Hb, !list_lookup_total_alt, lookup_take by exact Hj.
  reflexivity.
Qed.

(* ====================================================================== *)
(*  8.  W3 -- EVERY LIVE INODE'S RECORD                                    *)
(* ====================================================================== *)

(* WHY, AND WHAT IT IS AIMED AT.  [InodeLock.inode_ok] is the pure bundle
   ilock mints and every parked icache entry holds; its clauses are
   [InodeInv.blkmap_wf] (the named blocks are covered home blocks, and no
   indirect block means no entries), [bm_covers] (every block index below
   the size is allocated), the SIZE CAP [size <= MAXFILE * BSIZE]
   (fs-icache.md §13.5 -- NOT derivable from [bm_covers]), and
   [blk_holes_zero].  The boot stocking of the inode pool owes exactly
   that bundle for every allocated inum, and it cannot decode it:
   [IcacheBoot.v]'s header says so in as many words ("no amount of
   decoding will produce them ... that is an image-well-formedness layer"),
   and [ipool_alloc] therefore takes the allocated inums' bundles as a
   THREADED PREMISE (projects/fs-icache.md, C7).  THIS IS THAT LAYER's
   pure half: [fs_inode_ok_blk] below is [bm_covers]' shape, and
   [fs_data_of_holes] above is [blk_holes_zero]'s, both said over the
   image's own bytes.  The composition -- an [ipool] built from an image
   satisfying [fsimg_wf] -- does not exist yet; W3 is aimed at it.
   (design/fs-icache.md C7; design/fs-inode.md for [blkmap_wf].) *)

Definition fs_addr_ok (sb : fs_sb) (a : Z) : bool :=
  (fs_data_start sb <=? a) && (a <? sb_size sb).

Definition fs_inode_wf (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode)
  : bool :=
  let sz := bv_unsigned (di_size dn) in
  let nb := fs_nblk sz in
  let ib := bv_unsigned (di_addrs dn !!! 12%nat) in
  let es := fs_ind_ents P dn in
  ((bv_unsigned (di_type dn) =? T_DIR_z)
     || (bv_unsigned (di_type dn) =? T_FILE_z)
     || (bv_unsigned (di_type dn) =? T_DEVICE_z)) &&
  (1 <=? bv_unsigned (di_nlink dn)) &&
  (sz <=? Z.of_nat FS_MAXFILE * BSIZE_z) &&
  List.forallb
    (fun k => let a := bv_unsigned (di_addrs dn !!! k) in
              if Z.of_nat k <? nb then fs_addr_ok sb a else a =? 0)
    (seq 0 FS_NDIRECT) &&
  (if nb <=? Z.of_nat FS_NDIRECT then ib =? 0 else fs_addr_ok sb ib) &&
  List.forallb
    (fun j => let e := es !!! j in
              if Z.of_nat j <? nb - Z.of_nat FS_NDIRECT
              then fs_addr_ok sb e else e =? 0)
    (seq 0 FS_NINDIRECT).

Record fs_inode_ok (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode)
  : Prop := {
  fio_type : bv_unsigned (di_type dn) = T_DIR_z
             \/ bv_unsigned (di_type dn) = T_FILE_z
             \/ bv_unsigned (di_type dn) = T_DEVICE_z;
  fio_nlink : 1 <= bv_unsigned (di_nlink dn);
  fio_size : bv_unsigned (di_size dn) <= Z.of_nat FS_MAXFILE * BSIZE_z;
  fio_direct : forall k : nat, (k < FS_NDIRECT)%nat ->
      Z.of_nat k < fs_nblk (bv_unsigned (di_size dn)) ->
      fs_data_start sb <= bv_unsigned (di_addrs dn !!! k) < sb_size sb;
  fio_direct_zero : forall k : nat, (k < FS_NDIRECT)%nat ->
      fs_nblk (bv_unsigned (di_size dn)) <= Z.of_nat k ->
      bv_unsigned (di_addrs dn !!! k) = 0;
  fio_ind_zero : fs_nblk (bv_unsigned (di_size dn)) <= Z.of_nat FS_NDIRECT ->
      bv_unsigned (di_addrs dn !!! 12%nat) = 0;
  fio_ind : Z.of_nat FS_NDIRECT < fs_nblk (bv_unsigned (di_size dn)) ->
      fs_data_start sb <= bv_unsigned (di_addrs dn !!! 12%nat) < sb_size sb;
  fio_ent : forall j : nat, (j < FS_NINDIRECT)%nat ->
      Z.of_nat j < fs_nblk (bv_unsigned (di_size dn)) - Z.of_nat FS_NDIRECT ->
      fs_data_start sb <= fs_ind_ents P dn !!! j < sb_size sb;
  fio_ent_zero : forall j : nat, (j < FS_NINDIRECT)%nat ->
      fs_nblk (bv_unsigned (di_size dn)) - Z.of_nat FS_NDIRECT <= Z.of_nat j ->
      fs_ind_ents P dn !!! j = 0;
}.

Lemma fs_addr_ok_spec (sb : fs_sb) (a : Z) :
  fs_addr_ok sb a = true <-> fs_data_start sb <= a < sb_size sb.
Proof.
  unfold fs_addr_ok. rewrite andb_true_iff, Z.leb_le, Z.ltb_lt. reflexivity.
Qed.

Lemma fs_inode_wf_ok (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode) :
  fs_inode_wf P sb dn = true -> fs_inode_ok P sb dn.
Proof.
  unfold fs_inode_wf. intros H. rewrite !andb_true_iff in H.
  destruct H as [[[[[Hty Hnl] Hsz] Hdir] Hind] Hent].
  constructor.
  - rewrite !orb_true_iff, !Z.eqb_eq in Hty. tauto.
  - apply Z.leb_le. exact Hnl.
  - apply Z.leb_le. exact Hsz.
  - intros k Hk Hlt. apply fs_addr_ok_spec.
    pose proof (forallb_seq _ FS_NDIRECT k Hdir Hk) as Hk'.
    cbv beta zeta in Hk'. rewrite (proj2 (Z.ltb_lt _ _) Hlt) in Hk'. exact Hk'.
  - intros k Hk Hge. apply Z.eqb_eq.
    pose proof (forallb_seq _ FS_NDIRECT k Hdir Hk) as Hk'.
    cbv beta zeta in Hk'. rewrite (proj2 (Z.ltb_ge _ _) Hge) in Hk'. exact Hk'.
  - intros Hle. apply Z.eqb_eq.
    rewrite (proj2 (Z.leb_le _ _) Hle) in Hind. exact Hind.
  - intros Hgt. apply fs_addr_ok_spec.
    rewrite (proj2 (Z.leb_gt _ _) Hgt) in Hind. exact Hind.
  - intros j Hj Hlt. apply fs_addr_ok_spec.
    pose proof (forallb_seq _ FS_NINDIRECT j Hent Hj) as Hj'.
    cbv beta zeta in Hj'. rewrite (proj2 (Z.ltb_lt _ _) Hlt) in Hj'. exact Hj'.
  - intros j Hj Hge. apply Z.eqb_eq.
    pose proof (forallb_seq _ FS_NINDIRECT j Hent Hj) as Hj'.
    cbv beta zeta in Hj'. rewrite (proj2 (Z.ltb_ge _ _) Hge) in Hj'. exact Hj'.
Qed.

(* **[InodeInv.bm_covers]' SHAPE, over the image's bytes.**  That predicate
   is [forall i < MAXFILE, i * BSIZE < sz -> blkmap_get bm i <> 0]; this is
   the same statement about [fs_blk_addr], sharpened to say WHERE the block
   is (in the data region).  It is what a future boot composition converts
   into [bm_covers] once the blkmap resource exists. *)
Lemma fs_inode_ok_blk (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode)
    (k : nat) :
  fs_inode_ok P sb dn -> (k < FS_MAXFILE)%nat ->
  Z.of_nat k * BSIZE_z < bv_unsigned (di_size dn) ->
  fs_data_start sb <= fs_blk_addr P dn k < sb_size sb.
Proof.
  intros Hok Hk Hlt.
  assert (Hnb : Z.of_nat k < fs_nblk (bv_unsigned (di_size dn)))
    by (apply fs_nblk_lt; lia).
  unfold fs_blk_addr.
  destruct (Nat.ltb_spec k FS_NDIRECT) as [Hd|Hd].
  - exact (fio_direct P sb dn Hok k Hd Hnb).
  - apply (fio_ent P sb dn Hok (k - FS_NDIRECT)%nat).
    + unfold FS_MAXFILE, FS_NDIRECT, FS_NINDIRECT in *. lia.
    + rewrite Nat2Z.inj_sub by exact Hd. lia.
Qed.

Definition fs_inodes_wf (P : Z -> list (bv 8)) (sb : fs_sb) : bool :=
  List.forallb
    (fun i => let dn := fs_dinode P sb (Z.of_nat i) in
              if bv_unsigned (di_type dn) =? 0 then true
              else fs_inode_wf P sb dn)
    (seq 0 (Z.to_nat (sb_ninodes sb))).

Lemma fs_inodes_wf_spec (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_inodes_wf P sb = true -> 0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  fs_inode_ok P sb (fs_dinode P sb i).
Proof.
  intros H Hi Hnz. apply fs_inode_wf_ok.
  pose proof (forallb_seq _ (Z.to_nat (sb_ninodes sb)) (Z.to_nat i) H
                ltac:(lia)) as Hk.
  cbv beta zeta in Hk. rewrite Z2Nat.id in Hk by lia.
  destruct (bv_unsigned (di_type (fs_dinode P sb i)) =? 0) eqn:E;
    [| exact Hk].
  exfalso. apply Hnz, Z.eqb_eq, E.
Qed.

(* ====================================================================== *)
(*  9.  W4/W5 -- THE USED BLOCKS AND THE BITMAP                            *)
(* ====================================================================== *)

(* one inode's disk blocks: its content blocks and, when it has one, its
   indirect block.  Built in final order; the indirect-entry slice is
   taken from the [let]-bound entry list so the block is read once. *)
Definition fs_inode_blocks (P : Z -> list (bv 8)) (dn : dinode) : list Z :=
  let nb := fs_nblk (bv_unsigned (di_size dn)) in
  let es := fs_ind_ents P dn in
  ((if Z.of_nat FS_NDIRECT <? nb
    then [bv_unsigned (di_addrs dn !!! 12%nat)] else [])
   ++ ((fun k => bv_unsigned (di_addrs dn !!! k))
         <$> seq 0 (Z.to_nat (Z.min nb (Z.of_nat FS_NDIRECT))))
   ++ ((fun j => es !!! j)
         <$> seq 0 (Z.to_nat (nb - Z.of_nat FS_NDIRECT))))%list.

Definition fs_used_blocks (P : Z -> list (bv 8)) (sb : fs_sb) : list Z :=
  mjoin ((fun i => let dn := fs_dinode P sb (Z.of_nat i) in
                    if bv_unsigned (di_type dn) =? 0 then []
                    else fs_inode_blocks P dn)
            <$> seq 0 (Z.to_nat (sb_ninodes sb))).

(* WHY (W4): two inodes naming one disk block would make
   [InodeInv.blkmap_wf]'s injectivity clause unprovable across the region
   and the [fsblock]/[blk_own] halves of two inodes claim one key.  The
   check is [O(n log n)] -- one gset -- and its answer is the used set W5
   then reads. *)
Definition fs_used_set (P : Z -> list (bv 8)) (sb : fs_sb) : option (gset Z) :=
  gset_nodup (fs_used_blocks P sb).

Lemma fs_used_set_nodup (P : Z -> list (bv 8)) (sb : fs_sb) (u : gset Z) :
  fs_used_set P sb = Some u -> NoDup (fs_used_blocks P sb).
Proof. apply gset_nodup_NoDup. Qed.

Lemma fs_used_set_elem (P : Z -> list (bv 8)) (sb : fs_sb) (u : gset Z)
    (b : Z) :
  fs_used_set P sb = Some u -> (b ∈ u <-> b ∈ fs_used_blocks P sb).
Proof. intros H. exact (gset_nodup_set _ u H b). Qed.

(* every live inode's blocks really are in the collected list *)
Lemma fs_used_blocks_inode (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (b : Z) :
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  b ∈ fs_inode_blocks P (fs_dinode P sb i) ->
  b ∈ fs_used_blocks P sb.
Proof.
  intros Hi Hnz Hb. unfold fs_used_blocks.
  apply elem_of_list_join. eexists. split; [exact Hb |].
  apply elem_of_list_fmap. exists (Z.to_nat i). split.
  - rewrite Z2Nat.id by lia.
    destruct (bv_unsigned (di_type (fs_dinode P sb i)) =? 0) eqn:E;
      [| reflexivity].
    exfalso. apply Hnz, Z.eqb_eq, E.
  - apply elem_of_seq. lia.
Qed.

(* ---- W5 -------------------------------------------------------------- *)

(* the READ side of [BitmapEnc]'s encoder: bit [b] of a bitmap block.  In
   xv6 a SET bit means IN USE. *)
Definition fs_bit (bmb : list (bv 8)) (b : Z) : bool :=
  Z.testbit (bv_unsigned (bmb !!! Z.to_nat (b `div` 8))) (b `mod` 8).

(* ...tied to that encoder: on a block that IS [BitmapEnc.bm_bytes n u],
   [fs_bit] is membership in [u].  No second bitmap vocabulary. *)
Lemma fs_bit_bm_bytes (n : nat) (u : gset Z) (b : Z) :
  0 <= b < 8 * Z.of_nat n -> fs_bit (bm_bytes n u) b = bool_decide (b ∈ u).
Proof.
  intros Hb. unfold fs_bit.
  rewrite (list_lookup_total_alt (bm_bytes n u)).
  rewrite (bm_bytes_lookup n u (Z.to_nat (b `div` 8)))
    by (apply bit_byte_lt; lia).
  cbn [default from_option id].
  rewrite Z2Nat.id by (apply Z.div_pos; lia).
  rewrite bm_byte_testbit by (apply bit_off_range; lia).
  rewrite (bit_split b). reflexivity.
Qed.

(* WHY: the FREE POOL.  [BitmapInv.free_pool] holds a [free_blk] for every
   block of [free_set size used = list_to_set (seqZ 0 size) ∖ used], and
   [bitmap_res] holds the bitmap block AT [bm_bytes BSIZE used].  So the
   image's bitmap must say "in use" exactly of the metadata blocks and the
   blocks the inodes name; every other block below [size] is what boot can
   hand to the pool (design/fs-bitmap.md, "BitmapInv.v -- the resource and
   the free pool"). *)
Definition fs_bitmap_wf (P : Z -> list (bv 8)) (sb : fs_sb) (u : gset Z)
  : bool :=
  let bmb := P (sb_bmapstart sb) in
  List.forallb
    (fun i => let b := Z.of_nat i in
              bool_decide (fs_bit bmb b
                           = ((b <? fs_data_start sb) || bool_decide (b ∈ u))))
    (seq 0 (Z.to_nat (sb_size sb))).

Lemma fs_bitmap_wf_spec (P : Z -> list (bv 8)) (sb : fs_sb) (u : gset Z)
    (b : Z) :
  fs_bitmap_wf P sb u = true -> 0 <= b < sb_size sb ->
  (fs_bit (P (sb_bmapstart sb)) b = true <-> (b < fs_data_start sb \/ b ∈ u)).
Proof.
  intros H Hb.
  pose proof (forallb_seq _ (Z.to_nat (sb_size sb)) (Z.to_nat b) H
                ltac:(lia)) as Hk.
  cbv beta zeta in Hk. rewrite Z2Nat.id in Hk by lia.
  apply bool_decide_eq_true_1 in Hk. rewrite Hk.
  rewrite orb_true_iff, Z.ltb_lt, bool_decide_eq_true. reflexivity.
Qed.

(* the free-pool reading: a CLEAR bit below [size] is a data block no
   inode names -- exactly what boot may put in the pool *)
Lemma fs_bitmap_wf_free (P : Z -> list (bv 8)) (sb : fs_sb) (u : gset Z)
    (b : Z) :
  fs_bitmap_wf P sb u = true -> 0 <= b < sb_size sb ->
  fs_bit (P (sb_bmapstart sb)) b = false ->
  fs_data_start sb <= b /\ b ∉ u.
Proof.
  intros H Hb Hfree.
  destruct (Z.lt_ge_cases b (fs_data_start sb)) as [Hlt|Hge].
  { exfalso. rewrite (proj2 (fs_bitmap_wf_spec P sb u b H Hb)) in Hfree;
      [discriminate | left; exact Hlt]. }
  split; [exact Hge |]. intros Hin.
  rewrite (proj2 (fs_bitmap_wf_spec P sb u b H Hb)) in Hfree;
    [discriminate | right; exact Hin].
Qed.

(* ====================================================================== *)
(*  10.  W6 -- THE DIRECTORIES                                             *)
(* ====================================================================== *)

(* the name-uniqueness check, [O(n log n)] rather than the [O(n^2)] the
   predicate's own shape suggests: one gset of the LIVE records' canonical
   names.  Free records are deliberately unconstrained -- xv6 zeroes only
   the inum halfword, so a dead record's NAME bytes survive its deletion
   (FsTree.v §4). *)
(* one record's contribution to the name set.  Split out so that every
   case analysis below happens on a GOAL rather than on a hypothesis. *)
Definition uniq_step (data : nat -> list (bv 8)) (m : nat) (s : gset fname)
  : option (gset fname) :=
  if dir_liveb data m
  then (if bool_decide (dir_bname data m ∈ s) then None
        else Some ({[dir_bname data m]} ∪ s))
  else Some s.

Lemma uniq_step_Some (data : nat -> list (bv 8)) (m : nat) (s s' : gset fname) :
  uniq_step data m s = Some s' ->
  (dir_live data m /\ dir_bname data m ∉ s
   /\ s' = {[dir_bname data m]} ∪ s)
  \/ (~ dir_live data m /\ s' = s).
Proof.
  unfold uniq_step. destruct (dir_liveb data m) eqn:Hl.
  - destruct (bool_decide (dir_bname data m ∈ s)) eqn:Hb.
    + intros HC. discriminate.
    + intros HC. injection HC as <-. left.
      split; [apply dir_liveb_true; exact Hl |].
      split; [apply (proj1 (bool_decide_eq_false _) Hb) | reflexivity].
  - intros HC. injection HC as <-. right. split; [| reflexivity].
    intros Hlv. rewrite (proj2 (dir_liveb_true data m) Hlv) in Hl.
    discriminate.
Qed.

Fixpoint dir_uniqb (data : nat -> list (bv 8)) (n : nat)
  : option (gset fname) :=
  match n with
  | O => Some ∅
  | S m => match dir_uniqb data m with
           | None => None
           | Some s => uniq_step data m s
           end
  end.

Lemma dir_uniqb_set (data : nat -> list (bv 8)) (n : nat) (s : gset fname)
    (f : fname) :
  dir_uniqb data n = Some s ->
  (f ∈ s <-> exists k : nat, (k < n)%nat /\ dir_live data k
                             /\ dir_bname data k = f).
Proof.
  revert s. induction n as [|m IH]; intros s Hs; cbn in Hs.
  - injection Hs as <-. split.
    + intros Hf. exfalso. exact (proj1 (elem_of_empty f) Hf).
    + intros (k & Hk & _). exfalso. lia.
  - destruct (dir_uniqb data m) as [s0|] eqn:Hm; [| discriminate].
    assert (Hrec : f ∈ s0 <-> exists k : nat, (k < m)%nat /\ dir_live data k
                                              /\ dir_bname data k = f)
      by (apply IH; first [reflexivity | exact Hm]).
    destruct (uniq_step_Some data m s0 s Hs)
      as [(Hlv & Hnin & ->) | (Hnl & ->)].
    + rewrite elem_of_union, elem_of_singleton, Hrec. split.
      * intros [Heq | (k & Hk & Hlk & Hnk)].
        { exists m. split; [lia | split; [exact Hlv | symmetry; exact Heq]]. }
        { exists k. split; [lia | split; assumption]. }
      * intros (k & Hk & Hlk & Hnk).
        destruct (decide (k = m)) as [->|Hne];
          [left; symmetry; exact Hnk |].
        right. exists k. split; [lia | split; assumption].
    + rewrite Hrec. split.
      * intros (k & Hk & Hlk & Hnk). exists k. split; [lia | tauto].
      * intros (k & Hk & Hlk & Hnk).
        destruct (decide (k = m)) as [->|Hne]; [exfalso; exact (Hnl Hlk) |].
        exists k. split; [lia | tauto].
Qed.

(* **THE SPEC: it IS [FsTree.dir_names_unique].**  The invariant R2 carries
   (and which makes [dir_view] the exact any-match map), read off a
   linear-time check. *)
Lemma dir_uniqb_unique (data : nat -> list (bv 8)) (n : nat) (s : gset fname) :
  dir_uniqb data n = Some s -> dir_names_unique data n.
Proof.
  revert s. induction n as [|m IH]; intros s Hs.
  { intros j k Hj. exfalso. lia. }
  cbn in Hs.
  destruct (dir_uniqb data m) as [s0|] eqn:Hm; [| discriminate].
  assert (Hu0 : dir_names_unique data m)
    by (apply (IH s0); first [reflexivity | exact Hm]).
  destruct (uniq_step_Some data m s0 s Hs)
    as [(Hlv & Hnin & ->) | (Hnl & ->)].
  - assert (Hno : forall k : nat, (k < m)%nat -> dir_live data k ->
                    dir_bname data k <> dir_bname data m).
    { intros k Hk Hlk Heq. apply Hnin.
      apply (dir_uniqb_set data m s0 (dir_bname data m) Hm).
      exists k. split; [exact Hk | split; [exact Hlk | exact Heq]]. }
    intros j k Hj Hk Hlj Hlk Heq.
    destruct (decide (j = m)) as [->|Hjm];
      destruct (decide (k = m)) as [->|Hkm].
    + reflexivity.
    + exfalso. apply (Hno k ltac:(lia) Hlk). symmetry. exact Heq.
    + exfalso. apply (Hno j ltac:(lia) Hlj). exact Heq.
    + apply (Hu0 j k ltac:(lia) ltac:(lia) Hlj Hlk Heq).
  - intros j k Hj Hk Hlj Hlk Heq.
    destruct (decide (j = m)) as [->|Hjm]; [exfalso; exact (Hnl Hlj) |].
    destruct (decide (k = m)) as [->|Hkm]; [exfalso; exact (Hnl Hlk) |].
    apply (Hu0 j k ltac:(lia) ltac:(lia) Hlj Hlk Heq).
Qed.

(* WHY: [DirView.dir_ok] / [dir_inums_ok] ride in BOTH icache escrow
   payloads ([IcacheEscrow.ic_loaded] and [ipool_shape]'s allocated arm,
   fs-icache.md §15(a)) and no decoding produces them -- IcacheBoot threads
   them.  [FsTree.dir_names_unique] is R2's invariant, which is what makes
   an unlink's tree delta a [delete] rather than an unmasking.  The dot
   records are [DirView.dir_dots_ix]'s content.
   [dir_first] rather than [dir_view] for the two dot lookups: one scan,
   not the view's quadratic build. *)
Definition fs_dir_wf (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (dn : dinode) : bool :=
  let data := fs_data_of P dn in
  let sz := bv_unsigned (di_size dn) in
  let nrec := dir_nrec sz in
  (sz `mod` 16 =? 0) &&
  List.forallb
    (fun k => negb (dir_liveb data k)
              || (let inum := bv_unsigned (dir_inum data k) in
                  (0 <? inum) && (inum <? sb_ninodes sb) &&
                  negb (bv_unsigned (di_type (fs_dinode P sb inum)) =? 0)))
    (seq 0 nrec) &&
  (match dir_uniqb data nrec with Some _ => true | None => false end) &&
  (match dir_first data nrec DOT with
   | Some k => bv_unsigned (dir_inum data k) =? i
   | None => false
   end) &&
  (match dir_first data nrec DOTDOT with Some _ => true | None => false end).

Record fs_dir_ok (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) (dn : dinode)
  : Prop := {
  fdo_gran : (16 | bv_unsigned (di_size dn));
  fdo_ent : forall k : nat,
      (k < dir_nrec (bv_unsigned (di_size dn)))%nat ->
      dir_live (fs_data_of P dn) k ->
      0 < bv_unsigned (dir_inum (fs_data_of P dn) k) < sb_ninodes sb
      /\ bv_unsigned
           (di_type (fs_dinode P sb
                       (bv_unsigned (dir_inum (fs_data_of P dn) k)))) <> 0;
  fdo_unique : dir_names_unique (fs_data_of P dn)
                 (dir_nrec (bv_unsigned (di_size dn)));
  fdo_dot : dir_view (fs_data_of P dn)
              (dir_nrec (bv_unsigned (di_size dn))) !! DOT = Some i;
  fdo_dotdot : is_Some (dir_view (fs_data_of P dn)
                          (dir_nrec (bv_unsigned (di_size dn))) !! DOTDOT);
}.

Lemma fs_dir_wf_ok (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (dn : dinode) :
  fs_dir_wf P sb i dn = true -> fs_dir_ok P sb i dn.
Proof.
  unfold fs_dir_wf. intros H. rewrite !andb_true_iff in H.
  destruct H as [[[[Hgr Hent] Huq] Hdot] Hdd].
  constructor.
  - apply Z.eqb_eq in Hgr. apply Z.mod_divide; [lia | exact Hgr].
  - intros k Hk Hlive.
    pose proof (forallb_seq _ _ k Hent Hk) as Hk'.
    cbv beta zeta in Hk'. rewrite orb_true_iff in Hk'. destruct Hk' as [Hn|Hk'].
    { exfalso. apply negb_true_iff in Hn.
      rewrite (proj2 (dir_liveb_true _ _) Hlive) in Hn. discriminate. }
    rewrite !andb_true_iff in Hk'. destruct Hk' as [[Hlo Hhi] Hty].
    apply Z.ltb_lt in Hlo, Hhi. apply negb_true_iff in Hty.
    split; [lia |]. intros Hc. rewrite Hc in Hty. discriminate.
  - destruct (dir_uniqb (fs_data_of P dn)
                (dir_nrec (bv_unsigned (di_size dn)))) as [s|] eqn:Hs;
      [| discriminate].
    exact (dir_uniqb_unique _ _ s Hs).
  - destruct (dir_first (fs_data_of P dn)
                (dir_nrec (bv_unsigned (di_size dn))) DOT) as [k|] eqn:Hf;
      [| discriminate].
    rewrite dir_view_lookup, Hf. cbn [fmap option_fmap option_map].
    f_equal. apply Z.eqb_eq. exact Hdot.
  - destruct (dir_first (fs_data_of P dn)
                (dir_nrec (bv_unsigned (di_size dn))) DOTDOT) as [k|] eqn:Hf;
      [| discriminate].
    rewrite dir_view_lookup, Hf. cbn [fmap option_fmap option_map].
    exists (bv_unsigned (dir_inum (fs_data_of P dn) k)). reflexivity.
Qed.

(* **[DirView.dir_inums_ok] ITSELF**, the escrow payloads' own conjunct:
   every live record names an inum the inode region covers. *)
Lemma fs_dir_ok_inums (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (dn : dinode) (nib : nat) :
  fs_dir_ok P sb i dn -> sb_ninodes sb <= 16 * Z.of_nat nib ->
  dir_inums_ok (fs_data_of P dn)
    (dir_nrec (bv_unsigned (di_size dn))) nib.
Proof.
  intros Hok Hnib k Hk Hlive.
  destruct (fdo_ent P sb i dn Hok k Hk Hlive) as [[_ Hlt] _]. lia.
Qed.

(* ...and [FsTree.node_rep] for a directory node, which is what a boot
   composition has to exhibit *)
Lemma fs_dir_ok_node (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (dn : dinode) :
  fs_dir_ok P sb i dn -> bv_unsigned (di_type dn) = T_DIR_z ->
  node_rep (node_of dn (fs_data_of P dn)) dn (fs_data_of P dn).
Proof.
  intros Hok Hty. apply node_rep_of.
  - rewrite Hty. unfold T_DIR_z. lia.
  - exact (fdo_unique P sb i dn Hok).
Qed.

Definition fs_dirs_wf (P : Z -> list (bv 8)) (sb : fs_sb) : bool :=
  List.forallb
    (fun i => let dn := fs_dinode P sb (Z.of_nat i) in
              if bv_unsigned (di_type dn) =? T_DIR_z
              then fs_dir_wf P sb (Z.of_nat i) dn
              else true)
    (seq 0 (Z.to_nat (sb_ninodes sb))).

Lemma fs_dirs_wf_spec (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_dirs_wf P sb = true -> 0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z ->
  fs_dir_ok P sb i (fs_dinode P sb i).
Proof.
  intros H Hi Hty. apply fs_dir_wf_ok.
  pose proof (forallb_seq _ (Z.to_nat (sb_ninodes sb)) (Z.to_nat i) H
                ltac:(lia)) as Hk.
  cbv beta zeta in Hk. rewrite Z2Nat.id in Hk by lia.
  rewrite (proj2 (Z.eqb_eq _ _) Hty) in Hk. exact Hk.
Qed.

(* ====================================================================== *)
(*  11.  W7 -- THE ROOT                                                    *)
(* ====================================================================== *)

(* WHY: [FsTree.fs_root_dir] -- the tree's root must BE a directory -- and
   namei's absolute-path start ([ROOTINO] is where every [/...] walk
   begins).  [".." = 1] is the root's own fixed point, [dir_dots_ix]'s
   content at the one inode that has no parent. *)
Definition fs_root_wf (P : Z -> list (bv 8)) (sb : fs_sb) : bool :=
  let dn := fs_dinode P sb ROOTINO in
  let data := fs_data_of P dn in
  (bv_unsigned (di_type dn) =? T_DIR_z) &&
  (match dir_first data (dir_nrec (bv_unsigned (di_size dn))) DOTDOT with
   | Some k => bv_unsigned (dir_inum data k) =? ROOTINO
   | None => false
   end).

Lemma fs_root_wf_type (P : Z -> list (bv 8)) (sb : fs_sb) :
  fs_root_wf P sb = true ->
  bv_unsigned (di_type (fs_dinode P sb ROOTINO)) = T_DIR_z.
Proof.
  unfold fs_root_wf. intros H. apply andb_true_iff in H as [H _].
  apply Z.eqb_eq. exact H.
Qed.

Lemma fs_root_wf_node (P : Z -> list (bv 8)) (sb : fs_sb) :
  fs_root_wf P sb = true ->
  node_at P sb ROOTINO
  = Some (NDir (dir_view (fs_file_data P sb ROOTINO)
                  (dir_nrec (bv_unsigned (di_size (fs_dinode P sb ROOTINO)))))).
Proof.
  intros H. pose proof (fs_root_wf_type P sb H) as Hty.
  rewrite (node_at_live P sb ROOTINO) by (rewrite Hty; unfold T_DIR_z; lia).
  unfold node_of. rewrite decide_True by exact Hty. reflexivity.
Qed.

Lemma fs_root_wf_dotdot (P : Z -> list (bv 8)) (sb : fs_sb) :
  fs_root_wf P sb = true ->
  dir_view (fs_file_data P sb ROOTINO)
    (dir_nrec (bv_unsigned (di_size (fs_dinode P sb ROOTINO)))) !! DOTDOT
  = Some ROOTINO.
Proof.
  unfold fs_root_wf. intros H. apply andb_true_iff in H as [_ H].
  unfold fs_file_data.
  destruct (dir_first (fs_data_of P (fs_dinode P sb ROOTINO))
              (dir_nrec (bv_unsigned (di_size (fs_dinode P sb ROOTINO))))
              DOTDOT) as [k|] eqn:Hf; [| discriminate].
  rewrite dir_view_lookup, Hf. cbn [fmap option_fmap option_map].
  f_equal. apply Z.eqb_eq. exact H.
Qed.

(* [FsTree.fs_root_dir] outright *)
Lemma fs_root_wf_tree (P : Z -> list (bv 8)) (sb : fs_sb) :
  fs_root_wf P sb = true -> ROOTINO < sb_ninodes sb ->
  fs_root_dir (tree_of_disk P sb).
Proof.
  (* the [ROOTINO < ninodes] premise is what makes the store's lookup at
     the root speak; W1 carries it *)
  intros H Hn. unfold fs_root_dir. rewrite tree_of_disk_root.
  rewrite tree_of_disk_lookup by (unfold ROOTINO in *; lia).
  eexists. apply fs_root_wf_node. exact H.
Qed.

(* ====================================================================== *)
(*  12.  THE CHECK                                                         *)
(* ====================================================================== *)

Definition fsimg_wf (P : Z -> list (bv 8)) (sb : fs_sb) : bool :=
  fs_sb_wf sb &&                                          (* W1 *)
  fs_log_clean P sb &&                                    (* W2 *)
  fs_inodes_wf P sb &&                                    (* W3 *)
  (match fs_used_set P sb with                            (* W4 + W5 *)
   | None => false
   | Some u => fs_bitmap_wf P sb u
   end) &&
  fs_dirs_wf P sb &&                                      (* W6 *)
  fs_root_wf P sb.                                        (* W7 *)

Lemma fsimg_wf_sb (P : Z -> list (bv 8)) (sb : fs_sb) :
  fsimg_wf P sb = true -> fs_sb_ok sb.
Proof.
  unfold fsimg_wf. rewrite !andb_true_iff. intros H.
  apply fs_sb_wf_ok. tauto.
Qed.

Lemma fsimg_wf_log (P : Z -> list (bv 8)) (sb : fs_sb) :
  fsimg_wf P sb = true ->
  assemble_bytes (take 4 (P (sb_logstart sb))) = 0.
Proof.
  unfold fsimg_wf. rewrite !andb_true_iff. intros H.
  apply fs_log_clean_spec. tauto.
Qed.

Lemma fsimg_wf_inode (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fsimg_wf P sb = true -> 0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  fs_inode_ok P sb (fs_dinode P sb i).
Proof.
  unfold fsimg_wf. rewrite !andb_true_iff. intros H Hi Hnz.
  apply (fs_inodes_wf_spec P sb i); [tauto | exact Hi | exact Hnz].
Qed.

Lemma fsimg_wf_used (P : Z -> list (bv 8)) (sb : fs_sb) :
  fsimg_wf P sb = true ->
  exists u : gset Z, fs_used_set P sb = Some u
                     /\ NoDup (fs_used_blocks P sb)
                     /\ fs_bitmap_wf P sb u = true.
Proof.
  unfold fsimg_wf. rewrite !andb_true_iff. intros H.
  destruct H as [[[[[_ _] _] Hu] _] _].
  destruct (fs_used_set P sb) as [u|] eqn:Hus; [| discriminate].
  exists u. split; [reflexivity |].
  split; [exact (fs_used_set_nodup P sb u Hus) | exact Hu].
Qed.

Lemma fsimg_wf_dir (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fsimg_wf P sb = true -> 0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z ->
  fs_dir_ok P sb i (fs_dinode P sb i).
Proof.
  unfold fsimg_wf. rewrite !andb_true_iff. intros H Hi Hty.
  apply (fs_dirs_wf_spec P sb i); [tauto | exact Hi | exact Hty].
Qed.

Lemma fsimg_wf_root (P : Z -> list (bv 8)) (sb : fs_sb) :
  fsimg_wf P sb = true -> fs_root_wf P sb = true.
Proof.
  unfold fsimg_wf. rewrite !andb_true_iff. intros H. tauto.
Qed.

(* THE HEADLINE READING: a well-formed image's tree has a root directory,
   every node in it is a live record's reading, and the root's [".."] is
   the root. *)
Lemma fsimg_wf_tree_root (P : Z -> list (bv 8)) (sb : fs_sb) :
  fsimg_wf P sb = true -> fs_root_dir (tree_of_disk P sb).
Proof.
  intros H. apply fs_root_wf_tree.
  - exact (fsimg_wf_root P sb H).
  - exact (sbo_ninodes sb (fsimg_wf_sb P sb H)).
Qed.
