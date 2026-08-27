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

    The mkfs / durable-state check, W1-W8 below, each with a one-line WHY
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

(* **[InodeInv.ind_res]'s CONTENT HALF, and it is the direction the tree
   did not have.**  The icache's indirect-block resource holds the block AT
   [BlockWords.ind_bytes e] for a [bv 32] entry list [e]; the image side has
   [fs_ind_ents], the [Z]s DECODED out of that same block.  This says the
   two are the same 1024 bytes, so the [fs_chalf] half the boot fupd holds
   for the home block IS the resource the pool's allocated arm asks for.
   [fs_le_word_at] above is the per-field converse (bytes -> value); this is
   value -> bytes, 256 entries at once, and it bottoms out in the tree's one
   assembler through [RiscvModelBytes.nth_byte_assemble_len].
   The fmap is spelled exactly as the blkmap's [bm_ent] is built. *)
Lemma fs_ind_bytes_round_trip (P : Z -> list (bv 8)) (dn : dinode) :
  fs_blocks_full P ->
  bv_unsigned (di_addrs dn !!! 12%nat) <> 0 ->
  ind_bytes ((fun z => Z_to_bv 32 z) <$> fs_ind_ents P dn)
  = P (bv_unsigned (di_addrs dn !!! 12%nat)).
Proof.
  intros Hfull Hnz.
  remember (bv_unsigned (di_addrs dn !!! 12%nat)) as ib eqn:Hib.
  assert (Hents : fs_ind_ents P dn
                  = (fun q => fs_le_at (P ib) (4 * q)%nat 4)
                      <$> seq 0 FS_NINDIRECT).
  { unfold fs_ind_ents. cbv zeta. rewrite <- Hib.
    rewrite (proj2 (Z.eqb_neq ib 0) Hnz). reflexivity. }
  (* one entry's four bytes ARE the block's own four bytes: this is
     [nth_byte_assemble_len], the assembler's converse *)
  assert (Hbyte : forall q r : nat, (r < 4)%nat ->
            nth_byte (Z_to_bv 32 (fs_le_at (P ib) (4 * q)%nat 4)) r
            = P ib !!! (4 * q + r)%nat).
  { intros q r Hr. unfold fs_le_at.
    rewrite (nth_byte_assemble_len 32 _ r)
      by (rewrite length_fmap, length_seq; lia).
    rewrite list_lookup_total_alt, list_lookup_fmap,
      (lookup_seq_lt 0 4 r Hr).
    cbn [fmap option_fmap option_map default from_option].
    rewrite Nat.add_0_l. reflexivity. }
  assert (Hent : forall q : nat, (q < FS_NINDIRECT)%nat ->
            ((fun z => Z_to_bv 32 z) <$> fs_ind_ents P dn) !!! q
            = Z_to_bv 32 (fs_le_at (P ib) (4 * q)%nat 4)).
  { intros q Hq. rewrite Hents.
    rewrite list_lookup_total_alt, !list_lookup_fmap,
      (lookup_seq_lt 0 FS_NINDIRECT q Hq).
    cbn [fmap option_fmap option_map default from_option].
    rewrite Nat.add_0_l. reflexivity. }
  pose proof (Hfull ib) as Hlen.
  assert (Hle : length ((fun z => Z_to_bv 32 z) <$> fs_ind_ents P dn)
                = FS_NINDIRECT)
    by (rewrite length_fmap; apply fs_ind_ents_length).
  apply list_eq. intros k.
  destruct (Nat.lt_ge_cases k 1024) as [Hk|Hk].
  - (* k = 4 * (k / 4) + k mod 4 *)
    pose proof (Nat.div_mod_eq k 4) as Hdm.
    pose proof (Nat.mod_upper_bound k 4 ltac:(lia)) as Hmb.
    set (i := (k / 4)%nat) in *. set (j := (k `mod` 4)%nat) in *.
    assert (Hi : (i < FS_NINDIRECT)%nat) by (unfold FS_NINDIRECT; lia).
    assert (Hj : (j < 4)%nat) by lia.
    replace k with (4 * i + j)%nat by lia.
    rewrite (ind_bytes_lookup _ i j)
      by (first [rewrite Hle; exact Hi | exact Hj]).
    rewrite (Hent i Hi), (Hbyte i j Hj).
    symmetry. apply list_lookup_lookup_total_lt. rewrite Hlen.
    unfold BSIZE. lia.
  - rewrite ind_bytes_lookup_None
      by (rewrite Hle; unfold FS_NINDIRECT; lia).
    symmetry. apply lookup_ge_None_2. rewrite Hlen. unfold BSIZE. lia.
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

(* ...AND THE SAME COVER AT [nat], which is the shape
   [file_bytes_take_blocks]' second premise wants.  IT IS PROVED
   SYMBOLICALLY, THROUGH [Nat2Z.inj_le], AND THAT IS THE WHOLE POINT.  The
   goal is [Z.to_nat sz <= Z.to_nat (fs_nblk sz) * BSIZE] at [nat], and for
   a REAL file [sz] is tens of thousands: a [vm_compute] on it normalises
   both sides to unary successor chains that deep and overflows an 8 MB
   stack outright and deterministically -- it does not look like memory
   pressure, it looks like a broken proof in a file nobody touched.  (That
   is durable-notes' "a [nat] equality whose RHS is a large literal needs
   [Z], not a bigger stack", one inequality over.)  Through [Nat2Z.inj_le]
   the whole thing is [fs_nblk_cover] and costs nothing at all, at any
   size.  Every caller with a concrete image wants THIS, never the
   [vm_compute]. *)
Lemma fs_nblocks_cover_nat (sz : Z) :
  0 <= sz -> (Z.to_nat sz <= fs_nblocks sz * BSIZE)%nat.
Proof.
  intros Hsz. unfold fs_nblocks.
  assert (Hnn : 0 <= fs_nblk sz)
    by (unfold fs_nblk, BSIZE_z; apply Z.div_pos; lia).
  apply Nat2Z.inj_le. rewrite Nat2Z.inj_mul.
  rewrite (Z2Nat.id sz Hsz), (Z2Nat.id (fs_nblk sz) Hnn), BSIZE_z_nat.
  exact (fs_nblk_cover sz Hsz).
Qed.

(* ...and the SIZE CAP read as a block-count cap: a file no bigger than
   MAXFILE blocks has at most MAXFILE of them.  This is what bounds the
   indirect-entry INDEX in [fs_inode_blocks] (an entry list is only 256
   long, so a bigger [nb] would make the list's tail read the [Inhabited]
   default rather than a block number). *)
Lemma fs_nblk_max (sz : Z) :
  0 <= sz -> sz <= Z.of_nat FS_MAXFILE * BSIZE_z ->
  fs_nblk sz <= Z.of_nat FS_MAXFILE.
Proof.
  assert (HM : Z.of_nat FS_MAXFILE = 268) by (vm_compute; reflexivity).
  rewrite HM. intros H0 H. unfold fs_nblk.
  change (BSIZE_z - 1) with 1023. change BSIZE_z with 1024 in *.
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
  - exact (fs_nblocks_cover_nat sz Hsz).
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
  (sb_size sb <=? 8 * BSIZE_z) &&
  (* AN INUM IS A [ushort] ON THE DISK (durable-disk lane E-himg).  A
     directory entry's [inum] field is sixteen bits (kernel/fs.h's
     [struct dirent]), so a superblock that declared more inode slots than
     [2^16] would name inodes no directory entry can reach.  The region is
     [ninodes / 16 + 1] blocks of sixteen records, so the bound is on the
     REGION's inum space and not on [ninodes] itself -- that is the number
     [FsReady.fgo_ushort] is stated at and the one the boot mint carries.
     It is here rather than as a separate era premise because it is a fact
     about the superblock alone, and every era's superblock has to have it:
     nothing else in this record bounds the region above by anything
     tighter than the one-bitmap-block limit ([size <= 8 * BSIZE] leaves
     [16 * nib] up at [2^17]).  LAST, so no destructuring moves. *)
  (16 * (sb_ninodes sb / 16 + 1) <=? 2 ^ 16).

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
  (* the region's inum space fits a [ushort] -- see [fs_sb_wf]'s last
     conjunct.  LAST, so no destructuring moves. *)
  sbo_ushort : 16 * (sb_ninodes sb / 16 + 1) <= 2 ^ 16;
}.

Lemma fs_sb_wf_ok (sb : fs_sb) : fs_sb_wf sb = true -> fs_sb_ok sb.
Proof.
  unfold fs_sb_wf. intros H. rewrite !andb_true_iff in H.
  destruct H as [[[[[[[[[H1 H2] H3] H4] H5] H6] H7] H8] H9] H10].
  apply Z.eqb_eq in H1, H2, H3, H4, H5, H6.
  apply Z.ltb_lt in H7, H8. apply Z.leb_le in H9, H10.
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

(* ---- WHICH INUMS ARE LIVE, AND WHAT IS PAST THE END ------------------ *)

(* **THE TAIL NO W-CLAUSE COVERS.**  Every W conjunct above sweeps
   [seq 0 ninodes], but the INODE REGION the icache addresses is
   [16 * nib] records wide ([DinodeEnc.IBLOCK]'s geometry: 16 records to a
   block), and mkfs rounds up -- at the literal image [ninodes = 200] while
   [16 * 13 = 208], so eight records live in the region and outside every
   sweep.  [IcacheBoot.ipool_alloc]'s FREE arm needs them typed 0, and
   nothing above says so.  This is that check: [O(nib)], no file contents,
   and it reads the same inode blocks W3 already reads. *)
Definition fs_region_free (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
  : bool :=
  List.forallb
    (fun i => let z := Z.of_nat i in
              if z <? sb_ninodes sb then true
              else bv_unsigned (di_type (fs_dinode P sb z)) =? 0)
    (seq 0 (16 * nib)%nat).

Lemma fs_region_free_spec (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (z : Z) :
  fs_region_free P sb nib = true ->
  0 <= z -> sb_ninodes sb <= z -> z < 16 * Z.of_nat nib ->
  bv_unsigned (di_type (fs_dinode P sb z)) = 0.
Proof.
  intros H H0 Hlo Hhi. apply Z.eqb_eq.
  pose proof (forallb_seq _ (16 * nib)%nat (Z.to_nat z) H ltac:(lia)) as Hk.
  cbv beta zeta in Hk. rewrite Z2Nat.id in Hk by lia.
  rewrite (proj2 (Z.ltb_ge _ _) Hlo) in Hk. exact Hk.
Qed.

(* **THE TWO CLAUSES W3 CANNOT CARRY (fs-cfg-boot.md (d1) debt B).**
   [IcacheBoot.ireg_alloc]'s stage-A image premises are
   [image_free_nlink] (L3: a type-0 record has [nlink = 0]) and
   [image_nlink_short] (L4: every [nlink] is a non-negative short), and
   NEITHER is a reading of any W conjunct: W3 ([fs_inodes_wf]) skips a
   type-0 record entirely, so it says nothing about the free records'
   link counts, and no clause anywhere bounds [nlink] above.

   THEY RUN OVER THE WHOLE REGION, NOT OVER [seq 0 ninodes], and that is
   forced rather than chosen.  [ireg_alloc] states both at every
   [z ∈ region_inums nib], i.e. over [16 * nib] records; the tail
   [[ninodes, 16*nib)] is covered for the TYPE by [fs_region_free] above,
   but a type-0 tail record's [nlink] is exactly what L3 is about, so
   deriving L3 in the tail from [fs_region_free] is circular, and L4 is
   about arbitrary bytes.  Hence: one sweep of the region, in
   [fs_region_free]'s own idiom and reading the same thirteen inode
   blocks.  It cannot be an [fsimg_wf] conjunct because [fsimg_wf] does
   not take [nib].
   Both clauses ride in ONE sweep so the region's records are decoded
   once (measured: [fs_region_free] alone is 0.44 s at the literal
   image). *)
Definition fs_region_nlink (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
  : bool :=
  List.forallb
    (fun i => let z := Z.of_nat i in
              let dn := fs_dinode P sb z in
              (if bv_unsigned (di_type dn) =? 0
               then bv_unsigned (di_nlink dn) =? 0
               else true) &&
              (bv_unsigned (di_nlink dn) <=? 32767))
    (seq 0 (16 * nib)%nat).

Local Lemma fs_region_nlink_at (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (z : Z) :
  fs_region_nlink P sb nib = true -> 0 <= z < 16 * Z.of_nat nib ->
  (if bv_unsigned (di_type (fs_dinode P sb z)) =? 0
   then bv_unsigned (di_nlink (fs_dinode P sb z)) =? 0
   else true) = true
  /\ (bv_unsigned (di_nlink (fs_dinode P sb z)) <=? 32767) = true.
Proof.
  intros H Hz.
  pose proof (forallb_seq _ (16 * nib)%nat (Z.to_nat z) H ltac:(lia)) as Hk.
  cbv beta zeta in Hk. rewrite Z2Nat.id in Hk by lia.
  apply andb_true_iff. exact Hk.
Qed.

(* L3, at the region's width *)
Lemma fs_region_nlink_free (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (z : Z) :
  fs_region_nlink P sb nib = true -> 0 <= z < 16 * Z.of_nat nib ->
  bv_unsigned (di_type (fs_dinode P sb z)) = 0 ->
  bv_unsigned (di_nlink (fs_dinode P sb z)) = 0.
Proof.
  intros H Hz Hty.
  destruct (fs_region_nlink_at P sb nib z H Hz) as [H1 _].
  rewrite (proj2 (Z.eqb_eq _ _) Hty) in H1. apply Z.eqb_eq. exact H1.
Qed.

(* L4, at the region's width *)
Lemma fs_region_nlink_short (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (z : Z) :
  fs_region_nlink P sb nib = true -> 0 <= z < 16 * Z.of_nat nib ->
  bv_unsigned (di_nlink (fs_dinode P sb z)) <= 32767.
Proof.
  intros H Hz.
  destruct (fs_region_nlink_at P sb nib z H Hz) as [_ H2].
  apply Z.leb_le. exact H2.
Qed.

(* **CONJUNCT (14): A FREE RECORD IS BARE.**  [FsState.fs_inodes] iterates
   [FsStateInode.inode_owned] over the WHOLE inode map and that predicate
   carries [FsStateInode.inode_local], whose [inl_size] and [inl_covers]
   clauses are claims about a record's SIZE and ADDRESSES.  At a live inum
   W3 supplies them; at a type-0 one NOTHING above does -- W3 skips a
   type-0 record entirely and [fs_region_nlink] speaks only of [nlink] --
   so a garbage free record would refute both.  This is the missing sweep:
   zero size and thirteen zero addresses at every type-0 record of the
   REGION.  With L3 ([fs_region_nlink_free]) beside it it is exactly
   [FsStateInode.fn_bare] of the node the image decodes
   ([FsDurImg.img_node_bare]), hence [inode_local_bare].
   Region-wide and in [fs_region_free]'s own idiom, reading the same
   thirteen inode blocks, for that definition's reason: the tail
   [[ninodes, 16*nib)] is inside the icache's region and outside every W
   sweep.  It is NOT a conjunct of [fs_region_wf] -- that bundle's
   consumers destructure it -- but a separate premise, as [fs_links_eq] is
   beside [fsimg_wf]. *)

(* one type-0 record's shape: zero size and thirteen zero addresses.
   IT TAKES THE DECODED RECORD, not an inum: a record decode is ~21 ms at
   the literal image, and a [P]/[z] form would make the sweep below decode
   every free record TWICE (measured 8.5 s against 4.5 s). *)
Definition fs_rec_bare (dn : dinode) : bool :=
  (bv_unsigned (di_size dn) =? 0)
  && List.forallb (fun a : bv 32 => bv_unsigned a =? 0) (di_addrs dn).

Definition fs_region_bare (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
  : bool :=
  List.forallb
    (fun i => let dn := fs_dinode P sb (Z.of_nat i) in
              if bv_unsigned (di_type dn) =? 0 then fs_rec_bare dn else true)
    (seq 0 (16 * nib)%nat).

Lemma fs_region_bare_size (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (z : Z) :
  fs_region_bare P sb nib = true -> 0 <= z < 16 * Z.of_nat nib ->
  bv_unsigned (di_type (fs_dinode P sb z)) = 0 ->
  bv_unsigned (di_size (fs_dinode P sb z)) = 0.
Proof.
  intros H Hz Hty.
  assert (Hzid : Z.of_nat (Z.to_nat z) = z) by lia.
  pose proof (forallb_seq _ (16 * nib)%nat (Z.to_nat z) H ltac:(lia)) as Hk.
  cbv beta zeta in Hk. rewrite Hzid in Hk.
  rewrite (proj2 (Z.eqb_eq _ _) Hty) in Hk.
  unfold fs_rec_bare in Hk.
  apply andb_true_iff in Hk as [Hs _]. apply Z.eqb_eq. exact Hs.
Qed.

Lemma fs_region_bare_addr (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
    (z : Z) (k : nat) :
  fs_region_bare P sb nib = true -> 0 <= z < 16 * Z.of_nat nib ->
  bv_unsigned (di_type (fs_dinode P sb z)) = 0 -> (k < 13)%nat ->
  bv_unsigned (di_addrs (fs_dinode P sb z) !!! k) = 0.
Proof.
  intros H Hz Hty Hk.
  assert (Hzid : Z.of_nat (Z.to_nat z) = z) by lia.
  pose proof (forallb_seq _ (16 * nib)%nat (Z.to_nat z) H ltac:(lia)) as Hq.
  cbv beta zeta in Hq. rewrite Hzid in Hq.
  rewrite (proj2 (Z.eqb_eq _ _) Hty) in Hq.
  unfold fs_rec_bare in Hq.
  apply andb_true_iff in Hq as [_ Ha].
  rewrite List.forallb_forall in Ha.
  assert (Hlen : length (di_addrs (fs_dinode P sb z)) = 13%nat)
    by exact (fs_dinode_wf P sb z).
  destruct (lookup_lt_is_Some_2 (di_addrs (fs_dinode P sb z)) k
              ltac:(lia)) as [a Ha'].
  rewrite (list_lookup_total_correct _ _ _ Ha').
  apply Z.eqb_eq. apply Ha.
  apply elem_of_list_In, elem_of_list_lookup_2 with k. exact Ha'.
Qed.

(* **THE ONE REGION-WIDE HYPOTHESIS.**  [fsimg_wf] cannot see [nib], so the
   region's three claims (the tail's type, and L3/L4 everywhere) cannot be
   conjuncts of it; they are collected here instead so that
   [FsCfgBoot.fs_cfg_alloc] takes exactly TWO image hypotheses --
   [fsimg_wf P sb = true] and [fs_region_wf P sb nib = true] -- rather than
   three.  [fs_region_free] keeps its own name and spec: it is already
   [FsCfgBoot.ipool_alloc_of_image]'s premise. *)
Definition fs_region_wf (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat)
  : bool := fs_region_free P sb nib && fs_region_nlink P sb nib.

Lemma fs_region_wf_free (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) :
  fs_region_wf P sb nib = true -> fs_region_free P sb nib = true.
Proof. unfold fs_region_wf. rewrite andb_true_iff. tauto. Qed.

Lemma fs_region_wf_nlink (P : Z -> list (bv 8)) (sb : fs_sb) (nib : nat) :
  fs_region_wf P sb nib = true -> fs_region_nlink P sb nib = true.
Proof. unfold fs_region_wf. rewrite andb_true_iff. tauto. Qed.

(* **THE LIVE SET, AS AN OBJECT.**  The stocking of the inode pool splits
   the region as [R = A ⊎ (R ∖ A)] with [A] the ALLOCATED inums; the split
   needs [A] as one [gset] with a membership law, not 208 separate
   decisions (a per-inum [vm_compute] sweep is ~2 s x 208).  At the literal
   image [A] is [{[1 .. 24]}], computed once. *)
Definition fs_live_set (P : Z -> list (bv 8)) (sb : fs_sb) : gset Z :=
  list_to_set
    (List.filter
       (fun z => negb (bv_unsigned (di_type (fs_dinode P sb z)) =? 0))
       (Z.of_nat <$> seq 0 (Z.to_nat (sb_ninodes sb)))).

Lemma fs_live_set_elem_of (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  z ∈ fs_live_set P sb
  <-> 0 <= z < sb_ninodes sb
      /\ bv_unsigned (di_type (fs_dinode P sb z)) <> 0.
Proof.
  unfold fs_live_set. rewrite elem_of_list_to_set.
  rewrite elem_of_list_In, filter_In, <- elem_of_list_In, elem_of_list_fmap.
  split.
  - intros [(k & -> & Hk) Hnz].
    apply elem_of_seq in Hk. apply negb_true_iff in Hnz.
    apply Z.eqb_neq in Hnz. split; [lia | exact Hnz].
  - intros [Hz Hnz]. split.
    + exists (Z.to_nat z).
      split; [rewrite Z2Nat.id by lia; reflexivity |].
      apply elem_of_seq. lia.
    + apply negb_true_iff, Z.eqb_neq. exact Hnz.
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
   and two inodes would own one block's bytes.  The
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

(* ---- W4 REINDEXED: ONE INODE'S SLOTS ARE INJECTIVE ------------------- *)

(* **THE MISSING BRIDGE, AND WHY IT IS HERE RATHER THAN AT THE RESOURCE
   LAYER.**  [InodeInv.blkmap_wf]'s last clause is INJECTIVITY: two slots
   of one inode never name one block.  W3 does not say it -- [fs_inode_ok]
   places every named block in the data region and zeroes every unnamed
   slot, which is silent about collisions -- and W5 (the bitmap) is the
   free pool's fact, not this one.  The image layer DOES have it, globally,
   as W4's [NoDup (fs_used_blocks P sb)]; what was missing is the
   reindexing from that ONE list onto [InodeInv.bm_slot]'s 269 indices.
   That is what this block is.

   The route is: [NoDup] of the [mjoin] gives [NoDup] of one inode's own
   [fs_inode_blocks] (a member of the joined list), and
   [fs_inode_blocks_lookup] below is the index bijection -- slot [i] sits
   at position [fs_slot_pos nb i] of that list.  NOTHING here re-decodes
   [fs_ind_ents]: the entry list is read through [fs_slot], whose indirect
   arm is [fs_blk_addr]'s, exactly as [fs_inode_blocks] itself does.  (A
   per-index re-decode was MEASURED at 636 s on the literal image; this
   route costs no [vm_compute] at all.)

   [fs_slot] is [InodeInv.bm_slot]'s image reading: the MAXFILE file
   indices, plus the indirect block itself at index MAXFILE.  A bridge file
   that can name [InodeInv] should take its [img_slot] to BE [fs_slot]
   ([FS_MAXFILE] and [InodeInv.MAXFILE] are the same literal, so the two
   are convertible). *)
Definition fs_slot (P : Z -> list (bv 8)) (dn : dinode) (i : nat) : Z :=
  if decide (i = FS_MAXFILE) then bv_unsigned (di_addrs dn !!! 12%nat)
  else fs_blk_addr P dn i.

Definition fs_slot_inj (P : Z -> list (bv 8)) (dn : dinode) : Prop :=
  forall i j : nat, (i <= FS_MAXFILE)%nat -> (j <= FS_MAXFILE)%nat ->
    fs_slot P dn i <> 0 -> fs_slot P dn i = fs_slot P dn j -> i = j.

Lemma fs_slot_max (P : Z -> list (bv 8)) (dn : dinode) :
  fs_slot P dn FS_MAXFILE = bv_unsigned (di_addrs dn !!! 12%nat).
Proof.
  unfold fs_slot. destruct (decide (FS_MAXFILE = FS_MAXFILE)) as [_|Hc];
    [reflexivity | exfalso; exact (Hc eq_refl)].
Qed.

Lemma fs_slot_direct (P : Z -> list (bv 8)) (dn : dinode) (i : nat) :
  (i < FS_NDIRECT)%nat -> fs_slot P dn i = bv_unsigned (di_addrs dn !!! i).
Proof.
  intros Hi. unfold fs_slot.
  rewrite decide_False by (unfold FS_NDIRECT, FS_MAXFILE in *; lia).
  unfold fs_blk_addr. rewrite (proj2 (Nat.ltb_lt _ _) Hi). reflexivity.
Qed.

Lemma fs_slot_ent (P : Z -> list (bv 8)) (dn : dinode) (i : nat) :
  (FS_NDIRECT <= i)%nat -> (i < FS_MAXFILE)%nat ->
  fs_slot P dn i = fs_ind_ents P dn !!! (i - FS_NDIRECT)%nat.
Proof.
  intros H1 H2. unfold fs_slot. rewrite decide_False by lia.
  unfold fs_blk_addr. rewrite (proj2 (Nat.ltb_ge _ _) H1). reflexivity.
Qed.

(* a nonzero indirect block means the file HAS indirect blocks -- W3's
   [fio_ind_zero] read backwards, and the fact that pins [fs_slot_pos]'s
   branch at the one index that lands in the first chunk *)
Lemma fs_slot_ind_nb (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode) :
  fs_inode_ok P sb dn -> bv_unsigned (di_addrs dn !!! 12%nat) <> 0 ->
  Z.of_nat FS_NDIRECT < fs_nblk (bv_unsigned (di_size dn)).
Proof.
  intros Hok Hnz.
  destruct (Z_le_gt_dec (fs_nblk (bv_unsigned (di_size dn)))
              (Z.of_nat FS_NDIRECT)) as [Hle|Hgt]; [| lia].
  exfalso. apply Hnz. exact (fio_ind_zero P sb dn Hok Hle).
Qed.

(* WHERE slot [i] sits in [fs_inode_blocks]: the indirect block heads the
   list, then the direct entries, then the indirect entries -- so every
   non-MAXFILE slot is at [S i] when there is an indirect block (the direct
   chunk is then full, 12 long) and at [i] when there is not. *)
Definition fs_slot_pos (nb : Z) (i : nat) : nat :=
  if decide (i = FS_MAXFILE) then 0%nat
  else if Z.of_nat FS_NDIRECT <? nb then S i else i.

Lemma fs_inode_blocks_lookup (P : Z -> list (bv 8)) (sb : fs_sb)
    (dn : dinode) (i : nat) :
  fs_inode_ok P sb dn -> (i <= FS_MAXFILE)%nat -> fs_slot P dn i <> 0 ->
  fs_inode_blocks P dn
    !! fs_slot_pos (fs_nblk (bv_unsigned (di_size dn))) i
  = Some (fs_slot P dn i).
Proof.
  intros Hok Hi Hnz. unfold fs_slot_pos, fs_inode_blocks. cbv zeta.
  destruct (decide (i = FS_MAXFILE)) as [->|Hne].
  - (* the indirect block: it heads the list *)
    rewrite fs_slot_max in Hnz |- *.
    rewrite (proj2 (Z.ltb_lt _ _) (fs_slot_ind_nb P sb dn Hok Hnz)).
    reflexivity.
  - (* [decide]'s else arm: [destruct] already took it *)
    destruct (Nat.lt_ge_cases i FS_NDIRECT) as [Hd|Hd].
    + (* a direct entry: it is at [i] past the first chunk *)
      rewrite (fs_slot_direct P dn i Hd) in Hnz |- *.
      assert (Hnbi : Z.of_nat i < fs_nblk (bv_unsigned (di_size dn))).
      { destruct (Z_lt_ge_dec (Z.of_nat i)
                    (fs_nblk (bv_unsigned (di_size dn)))) as [H|H];
          [exact H |].
        exfalso. apply Hnz.
        exact (fio_direct_zero P sb dn Hok i Hd ltac:(lia)). }
      assert (HB : ((fun k => bv_unsigned (di_addrs dn !!! k))
                      <$> seq 0 (Z.to_nat
                                   (Z.min (fs_nblk (bv_unsigned (di_size dn)))
                                      (Z.of_nat FS_NDIRECT))))
                     !! i = Some (bv_unsigned (di_addrs dn !!! i))).
      { rewrite list_lookup_fmap, (lookup_seq_lt 0 _ i)
          by (unfold FS_NDIRECT in *; lia).
        rewrite Nat.add_0_l. reflexivity. }
      destruct (Z.ltb_spec (Z.of_nat FS_NDIRECT)
                  (fs_nblk (bv_unsigned (di_size dn)))) as [Hgt|Hle].
      * rewrite lookup_app_r by (cbn [length]; lia).
        cbn [length]. replace (S i - 1)%nat with i by lia.
        rewrite lookup_app_l
          by (rewrite length_fmap, length_seq; unfold FS_NDIRECT in *; lia).
        exact HB.
      * rewrite app_nil_l, lookup_app_l
          by (rewrite length_fmap, length_seq; unfold FS_NDIRECT in *; lia).
        exact HB.
    + (* an indirect entry: past both earlier chunks *)
      assert (Hlt : (i < FS_MAXFILE)%nat) by lia.
      assert (Hie : (i - FS_NDIRECT < FS_NINDIRECT)%nat)
        by (unfold FS_MAXFILE, FS_NDIRECT, FS_NINDIRECT in *; lia).
      rewrite (fs_slot_ent P dn i Hd Hlt) in Hnz |- *.
      assert (Hnbi : Z.of_nat (i - FS_NDIRECT)%nat
                     < fs_nblk (bv_unsigned (di_size dn))
                       - Z.of_nat FS_NDIRECT).
      { destruct (Z_lt_ge_dec (Z.of_nat (i - FS_NDIRECT)%nat)
                    (fs_nblk (bv_unsigned (di_size dn))
                     - Z.of_nat FS_NDIRECT)) as [H|H]; [exact H |].
        exfalso. apply Hnz.
        exact (fio_ent_zero P sb dn Hok (i - FS_NDIRECT)%nat Hie ltac:(lia)). }
      assert (Hgt : Z.of_nat FS_NDIRECT < fs_nblk (bv_unsigned (di_size dn)))
        by (rewrite Nat2Z.inj_sub in Hnbi by exact Hd; lia).
      destruct (Z.ltb_spec (Z.of_nat FS_NDIRECT)
                  (fs_nblk (bv_unsigned (di_size dn)))) as [_|Hle];
        [| exfalso; lia].
      rewrite lookup_app_r by (cbn [length]; lia).
      cbn [length]. replace (S i - 1)%nat with i by lia.
      rewrite lookup_app_r
        by (rewrite length_fmap, length_seq; unfold FS_NDIRECT in *; lia).
      rewrite length_fmap, length_seq.
      replace (i - Z.to_nat (Z.min (fs_nblk (bv_unsigned (di_size dn)))
                               (Z.of_nat FS_NDIRECT)))%nat
        with (i - FS_NDIRECT)%nat by (unfold FS_NDIRECT in *; lia).
      rewrite list_lookup_fmap, (lookup_seq_lt 0 _ (i - FS_NDIRECT)%nat)
        by lia.
      rewrite Nat.add_0_l. reflexivity.
Qed.

Lemma fs_slot_inj_of_nodup (P : Z -> list (bv 8)) (sb : fs_sb)
    (dn : dinode) :
  fs_inode_ok P sb dn -> NoDup (fs_inode_blocks P dn) -> fs_slot_inj P dn.
Proof.
  intros Hok Hnd i j Hi Hj Hnz Heq.
  assert (Hnzj : fs_slot P dn j <> 0) by (rewrite <- Heq; exact Hnz).
  assert (Hpos : fs_slot_pos (fs_nblk (bv_unsigned (di_size dn))) i
                 = fs_slot_pos (fs_nblk (bv_unsigned (di_size dn))) j).
  { apply (proj1 (NoDup_alt _) Hnd _ _ (fs_slot P dn i)).
    - exact (fs_inode_blocks_lookup P sb dn i Hok Hi Hnz).
    - rewrite Heq. exact (fs_inode_blocks_lookup P sb dn j Hok Hj Hnzj). }
  unfold fs_slot_pos in Hpos.
  destruct (decide (i = FS_MAXFILE)) as [Hi'|Hi'];
    destruct (decide (j = FS_MAXFILE)) as [Hj'|Hj'].
  - congruence.
  - (* the indirect block heads the list; no other slot is at position 0 *)
    exfalso.
    rewrite Hi', fs_slot_max in Hnz.
    rewrite (proj2 (Z.ltb_lt _ _) (fs_slot_ind_nb P sb dn Hok Hnz)) in Hpos.
    cbn in Hpos. discriminate.
  - exfalso.
    rewrite Hj', fs_slot_max in Hnzj.
    rewrite (proj2 (Z.ltb_lt _ _) (fs_slot_ind_nb P sb dn Hok Hnzj)) in Hpos.
    cbn in Hpos. discriminate.
  - (* both are file indices: the position is [i] or [S i], either way
       injective *)
    destruct (Z_le_gt_dec (fs_nblk (bv_unsigned (di_size dn)))
                (Z.of_nat FS_NDIRECT)) as [Hle|Hgt].
    + rewrite (proj2 (Z.ltb_ge _ _) Hle) in Hpos. cbn in Hpos. lia.
    + assert (Hgt' : Z.of_nat FS_NDIRECT < fs_nblk (bv_unsigned (di_size dn)))
        by lia.
      rewrite (proj2 (Z.ltb_lt _ _) Hgt') in Hpos. cbn in Hpos. lia.
Qed.

(* the join's [NoDup] restricted to one member list -- W4 is a [NoDup] of
   the CONCATENATION, and one inode's slots need only its own chunk *)
Lemma mjoin_cons {A : Type} (l : list A) (ls : list (list A)) :
  mjoin (l :: ls) = (l ++ mjoin ls)%list.
Proof. reflexivity. Qed.

(* stated by hand rather than through [NoDup_app]: that name is Stdlib's
   [List.NoDup_app] here (the [Stdlib.Lists.List] import wins), whose shape
   is the introduction rule, not the elimination one *)
Lemma NoDup_app_split {A : Type} (l k : list A) :
  NoDup (l ++ k) -> NoDup l /\ NoDup k.
Proof.
  induction l as [|x l IH]; intros H.
  - split; [apply NoDup_nil_2 | exact H].
  - destruct (IH (NoDup_cons_1_2 x (l ++ k) H)) as (Hl & Hk).
    split; [| exact Hk].
    apply NoDup_cons_2; [| exact Hl].
    intros Hin. apply (NoDup_cons_1_1 x (l ++ k) H), elem_of_app.
    left. exact Hin.
Qed.

Lemma NoDup_mjoin_elem {A : Type} (ls : list (list A)) (l : list A) :
  NoDup (mjoin ls) -> l ∈ ls -> NoDup l.
Proof.
  induction ls as [|x r IH]; intros Hnd Hl.
  - exfalso. exact (proj1 (elem_of_nil l) Hl).
  - rewrite mjoin_cons in Hnd.
    destruct (NoDup_app_split x (mjoin r) Hnd) as (Hx & Hr).
    apply elem_of_cons in Hl as [-> | Hl]; [exact Hx | exact (IH Hr Hl)].
Qed.

Lemma fs_used_blocks_nodup_inode (P : Z -> list (bv 8)) (sb : fs_sb)
    (i : Z) :
  NoDup (fs_used_blocks P sb) -> 0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  NoDup (fs_inode_blocks P (fs_dinode P sb i)).
Proof.
  intros Hnd Hi Hnz. unfold fs_used_blocks in Hnd.
  apply (NoDup_mjoin_elem _ _ Hnd).
  apply elem_of_list_fmap. exists (Z.to_nat i). split.
  - rewrite Z2Nat.id by lia.
    destruct (bv_unsigned (di_type (fs_dinode P sb i)) =? 0) eqn:E;
      [| reflexivity].
    exfalso. apply Hnz, Z.eqb_eq, E.
  - apply elem_of_seq. lia.
Qed.

(* **THE LEMMA THE STOCKING NEEDS**: W4 + W3, per live inum, in
   [InodeInv.blkmap_wf]'s own injectivity shape.  No new computation. *)
Lemma fs_used_nodup_slot_inj (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  NoDup (fs_used_blocks P sb) -> fs_inodes_wf P sb = true ->
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  fs_slot_inj P (fs_dinode P sb i).
Proof.
  intros Hnd Hw Hi Hnz.
  apply (fs_slot_inj_of_nodup P sb).
  - exact (fs_inodes_wf_spec P sb i Hw Hi Hnz).
  - exact (fs_used_blocks_nodup_inode P sb i Hnd Hi Hnz).
Qed.

(* ---- W4 READ THE OTHER WAY: THE INODES' BLOCK SETS ARE DISJOINT ------ *)

(* **WHY THIS READING TOO.**  The stocking of the inode pool hands each
   live inode the byte run of every block it names, carved
   out of the ONE big-op the era fupd holds over [cov]
   ([FsBoot.big_sepS_carve]).  A carve needs its pieces PAIRWISE DISJOINT
   -- two inodes naming one block would have the carve claim one key twice
   -- and needs each piece INSIDE [cov].  Both are readings of W4 plus W3
   and neither costs a new computation: disjointness is the [NoDup] of the
   concatenation restricted to two DIFFERENT members (the companion of
   [fs_used_blocks_nodup_inode], which restricts it to one), and the range
   is [fs_inode_ok]'s own three clauses. *)

(* every block a live inode names is in the DATA REGION.  The converse of
   [fs_slot]'s [fs_inode_blocks] membership ([FsImgBridge.
   img_slot_in_inode_blocks]): there, a nonzero slot is in the list; here,
   every list member is a real data block. *)
Lemma fs_inode_blocks_range (P : Z -> list (bv 8)) (sb : fs_sb)
    (dn : dinode) (b : Z) :
  fs_inode_ok P sb dn -> b ∈ fs_inode_blocks P dn ->
  fs_data_start sb <= b < sb_size sb.
Proof.
  intros Hok Hb.
  (* the entry INDEX bound, from the size cap *)
  assert (Hnb : fs_nblk (bv_unsigned (di_size dn)) <= Z.of_nat FS_MAXFILE).
  { apply fs_nblk_max;
      [exact (proj1 (bv_unsigned_in_range _ _)) | exact (fio_size P sb dn Hok)]. }
  unfold fs_inode_blocks in Hb. cbv zeta in Hb.
  apply elem_of_app in Hb as [Hb | Hb].
  - (* the indirect block, which heads the list exactly when there is one *)
    destruct (Z.ltb_spec (Z.of_nat FS_NDIRECT)
                (fs_nblk (bv_unsigned (di_size dn)))) as [Hgt|Hle].
    + apply elem_of_list_singleton in Hb as ->.
      exact (fio_ind P sb dn Hok Hgt).
    + exfalso. exact (proj1 (elem_of_nil b) Hb).
  - apply elem_of_app in Hb as [Hb | Hb].
    + (* a direct entry, below both [nb] and NDIRECT *)
      apply elem_of_list_fmap in Hb as (k & -> & Hk).
      apply elem_of_seq in Hk.
      apply (fio_direct P sb dn Hok k); unfold FS_NDIRECT in *; lia.
    + (* an indirect entry: [nb - NDIRECT] of them, and [nb <= MAXFILE] *)
      apply elem_of_list_fmap in Hb as (j & -> & Hj).
      apply elem_of_seq in Hj.
      apply (fio_ent P sb dn Hok j);
        unfold FS_MAXFILE, FS_NDIRECT, FS_NINDIRECT in *; lia.
Qed.

Definition fs_inode_blocks_set (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
  : gset Z := list_to_set (fs_inode_blocks P (fs_dinode P sb i)).

Lemma fs_inode_blocks_set_sub (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
    (X : gset Z) :
  fs_inode_ok P sb (fs_dinode P sb i) ->
  (forall b : Z, fs_data_start sb <= b < sb_size sb -> b ∈ X) ->
  fs_inode_blocks_set P sb i ⊆ X.
Proof.
  intros Hok HX. apply elem_of_subseteq. intros b Hb.
  unfold fs_inode_blocks_set in Hb. rewrite elem_of_list_to_set in Hb.
  exact (HX b (fs_inode_blocks_range P sb (fs_dinode P sb i) b Hok Hb)).
Qed.

(* one element of two DIFFERENT members of a duplicate-free concatenation
   -- stated by hand for [NoDup_app_split]'s reason (Stdlib's
   [List.NoDup_app] wins the name and is the introduction rule) *)
Lemma NoDup_app_cross {A : Type} (l k : list A) (x : A) :
  NoDup (l ++ k) -> x ∈ l -> x ∈ k -> False.
Proof.
  induction l as [|a l IH]; intros H Hx Hk.
  - exact (proj1 (elem_of_nil x) Hx).
  - apply elem_of_cons in Hx as [-> | Hx].
    + apply (NoDup_cons_1_1 a (l ++ k) H), elem_of_app. right. exact Hk.
    + exact (IH (NoDup_cons_1_2 a (l ++ k) H) Hx Hk).
Qed.

Lemma NoDup_mjoin_cross {A : Type} (ls : list (list A)) (n1 n2 : nat)
    (l1 l2 : list A) (x : A) :
  NoDup (mjoin ls) -> ls !! n1 = Some l1 -> ls !! n2 = Some l2 ->
  n1 <> n2 -> x ∈ l1 -> x ∈ l2 -> False.
Proof.
  revert n1 n2.
  induction ls as [|y ls IH]; intros n1 n2 Hnd H1 H2 Hne Hx1 Hx2.
  { destruct n1; discriminate. }
  rewrite mjoin_cons in Hnd.
  destruct n1 as [|m1]; destruct n2 as [|m2]; cbn in H1, H2.
  - exact (Hne eq_refl).
  - injection H1 as Hl1. subst l1.
    apply (NoDup_app_cross y (mjoin ls) x Hnd Hx1).
    apply elem_of_list_join. exists l2.
    split; [exact Hx2 | exact (elem_of_list_lookup_2 ls m2 l2 H2)].
  - injection H2 as Hl2. subst l2.
    apply (NoDup_app_cross y (mjoin ls) x Hnd Hx2).
    apply elem_of_list_join. exists l1.
    split; [exact Hx1 | exact (elem_of_list_lookup_2 ls m1 l1 H1)].
  - destruct (NoDup_app_split y (mjoin ls) Hnd) as (_ & Hr).
    exact (IH m1 m2 Hr H1 H2 ltac:(lia) Hx1 Hx2).
Qed.

(* **THE CARVE'S OTHER PREMISE**: W4, per PAIR of live inums, in
   [FsBoot.big_sepS_carve]'s own shape.  No new computation. *)
Lemma fs_inode_blocks_disjoint (P : Z -> list (bv 8)) (sb : fs_sb)
    (i j : Z) :
  NoDup (fs_used_blocks P sb) ->
  0 <= i < sb_ninodes sb -> 0 <= j < sb_ninodes sb -> i <> j ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  bv_unsigned (di_type (fs_dinode P sb j)) <> 0 ->
  fs_inode_blocks_set P sb i ## fs_inode_blocks_set P sb j.
Proof.
  intros Hnd Hi Hj Hne Hti Htj.
  apply elem_of_disjoint. intros b Hb1 Hb2.
  unfold fs_inode_blocks_set in Hb1, Hb2.
  rewrite elem_of_list_to_set in Hb1. rewrite elem_of_list_to_set in Hb2.
  unfold fs_used_blocks in Hnd.
  apply (NoDup_mjoin_cross _ (Z.to_nat i) (Z.to_nat j)
           (fs_inode_blocks P (fs_dinode P sb i))
           (fs_inode_blocks P (fs_dinode P sb j)) b Hnd);
    [ | | lia | exact Hb1 | exact Hb2].
  - rewrite list_lookup_fmap, (lookup_seq_lt 0 _ (Z.to_nat i)) by lia.
    cbn [fmap option_fmap option_map].
    rewrite Nat.add_0_l, Z2Nat.id by lia.
    rewrite (proj2 (Z.eqb_neq _ _) Hti). reflexivity.
  - rewrite list_lookup_fmap, (lookup_seq_lt 0 _ (Z.to_nat j)) by lia.
    cbn [fmap option_fmap option_map].
    rewrite Nat.add_0_l, Z2Nat.id by lia.
    rewrite (proj2 (Z.eqb_neq _ _) Htj). reflexivity.
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

(* ---- W5 READ BACKWARDS: THE BLOCK'S OWN BIT SET ---------------------- *)

(*  [BitmapInv.bitmap_res] holds the bitmap block AT [bm_bytes BSIZE used]
    -- an EQUATION between the image's bytes and the encoder's image of a
    pure set -- and boot has to produce it.  The set that satisfies it is
    not a derived quantity to be swept for: it is the block's OWN bits,
    read back.  Then the equation is a THEOREM about any block-sized byte
    list ([bm_bytes_fs_bmap_set]) rather than a new image check.

    WHY THIS AND NOT "the used set ∪ the metadata blocks".  That set agrees
    with the block below [sb_size] -- which is exactly what W5 says -- and
    says NOTHING about the bits above it, so the equation would additionally
    need the tail swept clear: 6192 [fs_bit]s at the literal image, on the
    build's longest leaf.  Nothing needs the tail clear:
    [BitmapInv.bitmap_ok] quantifies over [x < size] and
    [BitmapInv.free_set] intersects [seqZ 0 size], so a [used] carrying bits
    above [size] is indistinguishable from one that does not.  W5 is still
    what makes the set USABLE -- [fs_bmap_set_free] below is the reading
    that says a clear bit is a free data block.                            *)
Definition fs_bmap_set (n : nat) (bmb : list (bv 8)) : gset Z :=
  list_to_set (List.filter (fs_bit bmb) (seqZ 0 (8 * Z.of_nat n))).

Lemma fs_bmap_set_elem (n : nat) (bmb : list (bv 8)) (b : Z) :
  b ∈ fs_bmap_set n bmb
  <-> (0 <= b < 8 * Z.of_nat n /\ fs_bit bmb b = true).
Proof.
  unfold fs_bmap_set. rewrite elem_of_list_to_set.
  rewrite elem_of_list_In, filter_In, <- elem_of_list_In, elem_of_seqZ.
  split; intros [H1 H2]; (split; [lia | exact H2]).
Qed.

(* a byte is determined by its low eight bits: everything above is zero.
   [BitmapEnc.bm_byte_testbit_high] is the same fact on the encoder's side;
   this is the one on an ARBITRARY image byte, which is what an equation
   between the two needs. *)
Lemma bv8_testbit_high (w : bv 8) (k : Z) :
  8 <= k -> Z.testbit (bv_unsigned w) k = false.
Proof.
  intros Hk. pose proof (bv_unsigned_in_range _ w) as [Hlo Hhi].
  unfold bv_modulus in Hhi. change (2 ^ Z.of_N 8) with 256 in Hhi.
  apply Z.testbit_false; [lia |].
  rewrite Z.div_small; [reflexivity |].
  split; [lia |]. apply (Z.lt_le_trans _ 256); [lia |].
  change 256 with (2 ^ 8). apply Z.pow_le_mono_r; lia.
Qed.

(* THE EQUATION.  A block-sized byte list IS the encoder's image of its own
   bit set -- no image hypothesis, no computation. *)
Lemma bm_bytes_fs_bmap_set (n : nat) (bmb : list (bv 8)) :
  length bmb = n -> bm_bytes n (fs_bmap_set n bmb) = bmb.
Proof.
  intros Hlen. apply list_eq. intros j.
  destruct (Nat.lt_ge_cases j n) as [Hj|Hj].
  - rewrite (bm_bytes_lookup n _ j Hj).
    assert (Hjl : (j < length bmb)%nat) by lia.
    destruct (lookup_lt_is_Some_2 bmb j Hjl) as [w Hw].
    rewrite Hw. f_equal.
    assert (Hwt : bmb !!! j = w).
    { rewrite (list_lookup_total_alt bmb). rewrite Hw. reflexivity. }
    apply bv_eq. apply Z.bits_inj_iff'. intros k Hk.
    destruct (Z.lt_ge_cases k 8) as [Hk8|Hk8].
    + rewrite bm_byte_testbit by lia.
      assert (Hdiv : (8 * Z.of_nat j + k) `div` 8 = Z.of_nat j)
        by (apply bit_byte_of; lia).
      assert (Hmod : (8 * Z.of_nat j + k) `mod` 8 = k).
      { pose proof (bit_split (8 * Z.of_nat j + k)) as Hs.
        rewrite Hdiv in Hs. lia. }
      assert (Hbit : fs_bit bmb (8 * Z.of_nat j + k)
                     = Z.testbit (bv_unsigned w) k).
      { unfold fs_bit. rewrite Hdiv. rewrite Hmod. rewrite Nat2Z.id.
        rewrite Hwt. reflexivity. }
      rewrite <- Hbit.
      destruct (fs_bit bmb (8 * Z.of_nat j + k)) eqn:Hfb.
      * apply bool_decide_eq_true_2. apply fs_bmap_set_elem.
        split; [lia | exact Hfb].
      * apply bool_decide_eq_false_2. rewrite fs_bmap_set_elem.
        intros [_ Hc]. congruence.
    + rewrite bm_byte_testbit_high by lia.
      symmetry. apply bv8_testbit_high. lia.
  - rewrite (bm_bytes_lookup_None n _ j Hj).
    symmetry. apply lookup_ge_None_2. lia.
Qed.

(* THE READING THAT MAKES THE SET USABLE: a block below [size] whose bit is
   CLEAR is a data block no inode names -- [BitmapInv.free_pool]'s member,
   stated at [fs_bmap_set] instead of at [fs_bit]. *)
Lemma fs_bmap_set_free (P : Z -> list (bv 8)) (sb : fs_sb) (u : gset Z)
    (b : Z) :
  fs_sb_ok sb -> fs_bitmap_wf P sb u = true ->
  0 <= b < sb_size sb ->
  b ∉ fs_bmap_set BSIZE (P (sb_bmapstart sb)) ->
  fs_data_start sb <= b /\ b ∉ u.
Proof.
  intros Hsb Hw Hb Hnin.
  assert (Hclear : fs_bit (P (sb_bmapstart sb)) b = false).
  { destruct (fs_bit (P (sb_bmapstart sb)) b) eqn:Hbit; [| reflexivity].
    exfalso. apply Hnin, fs_bmap_set_elem.
    pose proof (sbo_one_bitmap sb Hsb) as Hone.
    rewrite BSIZE_z_nat. split; [lia | exact Hbit]. }
  exact (fs_bitmap_wf_free P sb u b Hw Hb Hclear).
Qed.

(*  SEALED, AND THE SEAL IS LOAD-BEARING.  At [n = BSIZE] the body is
    [list_to_set (filter _ (seqZ 0 (8 * Z.of_nat 1024%nat)))]: a 1024-deep
    unary literal under [Z.of_nat], then an 8192-element list, then 8192
    nested [gset] unions over a STUCK filter.  Nothing ever needs to
    compute it -- every consumer goes through the three lemmas above -- but
    the tactic unifier will happily start, and then a one-delta-step
    conversion between two spellings of the same set becomes a fifteen-
    minute non-answer with no error (durable-notes' "a compile that never
    finishes").  Do not make it transparent again. *)
Global Opaque fs_bmap_set.

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
(*  10b.  W8 -- THE DOT RECORDS, BY INDEX                                  *)
(* ====================================================================== *)

(* WHY THIS IS A SEPARATE CONJUNCT AND NOT A CLAUSE OF W6.  Every escrow
   payload and [IcacheBoot.ipool_shape]'s allocated arm carries
   [DirView.dir_dots_ix], which pins ["."] at record 0 and [".."] at
   record 1 -- BY INDEX.  W6's [fs_dir_wf] and W7's [fs_root_wf] check the
   dots through [DirView.dir_first], the scan [dirlookup] performs: they say
   the FIRST live ["."] names [i] and that a [".."] exists SOMEWHERE, and
   NEITHER pins an index.  [FsTree.dir_names_unique] does not recover it
   either (uniqueness of names says nothing about their positions).  So
   [dir_dots_ix] is NOT derivable from W1-W7, and this is the check that
   supplies it -- additive, one more [O(nrec)] pass per directory over
   records the W6 sweep already reads.
   It rides beside [fs_dirs_wf] rather than inside [fs_dir_wf] so that the
   two readings of a directory stay separable: W6 is what [dirlookup]
   sees, W8 is what the icache's payload demands. *)
Definition fs_dots_wf (P : Z -> list (bv 8)) (self : Z) (dn : dinode)
  : bool :=
  let data := fs_data_of P dn in
  let nrec := dir_nrec (bv_unsigned (di_size dn)) in
  (2 <=? Z.of_nat nrec) &&
  dir_liveb data 0 &&
  (bv_unsigned (dir_inum data 0) =? self) &&
  bool_decide (dir_bname data 0 = dot_name) &&
  dir_liveb data 1 &&
  bool_decide (dir_bname data 1 = dotdot_name).

(* **THE SPEC: it IS [DirView.dir_dots_ix].**  ([dir_bname] is
   [DirentEnc.bname 14] of the record's name function, which is the
   spelling [dir_dots_ix] uses.) *)
Lemma fs_dots_wf_ok (P : Z -> list (bv 8)) (self : Z) (dn : dinode) :
  fs_dots_wf P self dn = true -> dir_dots_ix self dn (fs_data_of P dn).
Proof.
  unfold fs_dots_wf. cbv zeta. intros H. rewrite !andb_true_iff in H.
  destruct H as [[[[[Hn Hl0] Hi0] Hb0] Hl1] Hb1].
  intros _ _.
  apply Z.leb_le in Hn. apply Z.eqb_eq in Hi0.
  apply bool_decide_eq_true in Hb0, Hb1.
  split; [lia |].
  split; [exact (proj1 (dir_liveb_true _ 0) Hl0) |].
  split; [exact Hi0 |].
  split; [exact Hb0 |].
  split; [exact (proj1 (dir_liveb_true _ 1) Hl1) | exact Hb1].
Qed.

Definition fs_dots_all (P : Z -> list (bv 8)) (sb : fs_sb) : bool :=
  List.forallb
    (fun i => let dn := fs_dinode P sb (Z.of_nat i) in
              if bv_unsigned (di_type dn) =? T_DIR_z
              then fs_dots_wf P (Z.of_nat i) dn
              else true)
    (seq 0 (Z.to_nat (sb_ninodes sb))).

Lemma fs_dots_all_spec (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_dots_all P sb = true -> 0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z ->
  dir_dots_ix i (fs_dinode P sb i) (fs_data_of P (fs_dinode P sb i)).
Proof.
  intros H Hi Hty. apply fs_dots_wf_ok.
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
(*  11b.  W9 -- THE PER-INUM COUNT OF LINK FRAGMENTS THE IMAGE DEMANDS     *)
(* ====================================================================== *)

(*  WHY THIS CONJUNCT EXISTS.  A directory's payload holds ONE fragment of
    its TARGET's link register per ticket-bearing record it contains
    ([IcacheEscrow.dlinks], i.e. [FsStateInode.ent_toks_x]; fs-state.md
    §6½), and every such fragment is drawn out of that target's region-side
    authority ([InodeRegion.ireg_lnk]), which is tied to the target's own
    [di_nlink].  So before boot can mint the fragments it has to KNOW, per
    inum, how many the image demands -- and that number is a fact about the
    image's directory CONTENTS which no decoding lemma supplies.  This
    section computes it and W9 checks the inequalities the region invariant
    and the boot's mint need.

    THE TICKET DISCIPLINE.  A record bears a ticket exactly when it is LIVE
    and does NOT name its own home; [fs_rec_ticket] below is that guard.
    The SELF EXEMPTION covers both dot records of any directory (["."]
    names the home by W8, and [".."] names it too at the root), and a FREE
    record (inum 0) carries nothing at all.  It is the image-level cousin
    of [FsStateInode.ent_tokenless] and NOT the same guard -- conjunct (15)
    below is exactly that difference, and why it has to be checked too.

    WHAT W9 CHECKS, per inum [z] of [0 .. ninodes):

      (a) the count is at most [z]'s own [di_nlink] -- [z]'s own authority
          has to cover every fragment the image hands out at it;
      (b) if [z] is a DIRECTORY then the count is ZERO, its [di_nlink] is
          exactly ONE, and [z] IS the root.  All three are true of every
          mkfs image, which lays down exactly ONE directory: nothing in the
          image names it but its own two dot records, both self-exempt, so
          no payload owes a fragment at it, and mkfs writes its [di_nlink]
          as one.

    COST: one pass over the [ninodes] records to find the directories (the
    same read W3/W6/W8 already do) plus one [O(nrec)] pass over each
    directory's records, and then a [length (filter ...)] over the ~25-entry
    ticket list per inum.  The ticket list is [let]-bound so it is built
    ONCE for the whole sweep.                                              *)

(* ONE RECORD'S TICKET: LIVE, and not naming its own home *)
Definition fs_rec_ticket (P : Z -> list (bv 8)) (self : Z) (dn : dinode)
    (k : nat) : option Z :=
  let data := fs_data_of P dn in
  if dir_liveb data k
     && negb (bool_decide (bv_unsigned (dir_inum data k) = self))
  then Some (bv_unsigned (dir_inum data k)) else None.

(* ...one DIRECTORY's tickets, in record order.  [omap] rather than a
   [filter]+[map] so that the list a resource-side [big_sepL] walks and the
   record indices the entry fragments are stated at line up by ONE induction
   ([FsCfgBoot.big_sepL_omap_mono]). *)
Definition fs_dir_tickets (P : Z -> list (bv 8)) (self : Z) (dn : dinode)
  : list Z :=
  omap (fs_rec_ticket P self dn)
       (seq 0 (dir_nrec (bv_unsigned (di_size dn)))).

(* ...at an inum, [] unless the record is a directory *)
Definition fs_dir_tickets_at (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z)
  : list Z :=
  let dn := fs_dinode P sb z in
  if bv_unsigned (di_type dn) =? T_DIR_z then fs_dir_tickets P z dn else [].

(* ...and the whole image's, in inum order.  [fs_used_blocks]' shape, at
   the records instead of the blocks. *)
Definition fs_all_tickets (P : Z -> list (bv 8)) (sb : fs_sb) : list Z :=
  mjoin ((fun i => fs_dir_tickets_at P sb (Z.of_nat i))
           <$> seq 0 (Z.to_nat (sb_ninodes sb))).

(* how many of a ticket list name [z].  Named separately from
   [fs_link_count] because the resource-side routing lemma
   ([FsCfgBoot.big_sepS_tick_route]) is generic in the list. *)
Definition fs_tick_count (L : list Z) (z : Z) : nat :=
  length (List.filter (fun t => bool_decide (t = z)) L).

(* **THE COUNT**: how many ticket-bearing records of the image name [z].
   This is how many fragments of [z]'s register the boot hands out. *)
Definition fs_link_count (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) : nat :=
  fs_tick_count (fs_all_tickets P sb) z.

(* EVERY TICKET NAMES A LIVE INUM INSIDE [ninodes] -- W6's [fdo_ent],
   lifted over the join.  This is what puts the whole ticket supply inside
   the inode region (so the routing lemma's [t ∈ P] premise is free) and
   what makes the count VANISH off the sweep's range. *)
Lemma fs_all_tickets_range (P : Z -> list (bv 8)) (sb : fs_sb) (t : Z) :
  fs_dirs_wf P sb = true -> t ∈ fs_all_tickets P sb ->
  0 < t < sb_ninodes sb.
Proof.
  intros Hw Ht. unfold fs_all_tickets in Ht.
  apply elem_of_list_join in Ht as (l & Hl & Hls).
  apply elem_of_list_fmap in Hls as (i & -> & Hi).
  apply elem_of_seq in Hi as [_ Hi].
  unfold fs_dir_tickets_at in Hl. cbv zeta in Hl.
  destruct (bv_unsigned (di_type (fs_dinode P sb (Z.of_nat i))) =? T_DIR_z)
    eqn:Hty; [| by apply elem_of_nil in Hl].
  apply elem_of_list_omap in Hl as (k & Hk & Hkt).
  apply elem_of_seq in Hk as [_ Hk].
  unfold fs_rec_ticket in Hkt. cbv zeta in Hkt.
  destruct (dir_liveb (fs_data_of P (fs_dinode P sb (Z.of_nat i))) k
            && negb (bool_decide
                       (bv_unsigned
                          (dir_inum
                             (fs_data_of P (fs_dinode P sb (Z.of_nat i))) k)
                        = Z.of_nat i))) eqn:Hg; [| discriminate].
  injection Hkt as <-.
  apply andb_true_iff in Hg as [Hlv _].
  pose proof (fs_dirs_wf_spec P sb (Z.of_nat i) Hw ltac:(lia)
                (proj1 (Z.eqb_eq _ _) Hty)) as Hdok.
  destruct (fdo_ent P sb (Z.of_nat i) (fs_dinode P sb (Z.of_nat i)) Hdok k
              Hk (proj1 (dir_liveb_true _ k) Hlv)) as [Hran _].
  exact Hran.
Qed.

Lemma fs_tick_count_zero (L : list Z) (z : Z) :
  (forall t : Z, t ∈ L -> t <> z) -> fs_tick_count L z = 0%nat.
Proof.
  intros H. unfold fs_tick_count.
  assert (Hnil : List.filter (fun t => bool_decide (t = z)) L = []).
  { induction L as [| a L IH]; [reflexivity |].
    cbn [List.filter].
    rewrite (bool_decide_eq_false_2 (a = z) (H a (elem_of_list_here a L))).
    apply IH. intros t Ht. apply H. apply elem_of_list_further. exact Ht. }
  rewrite Hnil. reflexivity.
Qed.

(* OFF the sweep's range the count is zero, by the tickets' own range *)
Lemma fs_link_count_out (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  fs_dirs_wf P sb = true -> ~ (0 < z < sb_ninodes sb) ->
  fs_link_count P sb z = 0%nat.
Proof.
  intros Hw Hz. unfold fs_link_count. apply fs_tick_count_zero.
  intros t Ht Heq. rewrite Heq in Ht.
  exact (Hz (fs_all_tickets_range P sb z Hw Ht)).
Qed.

(* THE SWEEP *)
Definition fs_links_wf (P : Z -> list (bv 8)) (sb : fs_sb) : bool :=
  let L := fs_all_tickets P sb in
  List.forallb
    (fun i => let z := Z.of_nat i in
              let dn := fs_dinode P sb z in
              (Z.of_nat (fs_tick_count L z) <=? bv_unsigned (di_nlink dn)) &&
              (if bv_unsigned (di_type dn) =? T_DIR_z
               then Nat.eqb (fs_tick_count L z) 0
                    && (bv_unsigned (di_nlink dn) =? 1)
                    && (z =? ROOTINO)
               else true))
    (seq 0 (Z.to_nat (sb_ninodes sb))).

Lemma fs_links_wf_at (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  fs_links_wf P sb = true -> 0 <= z < sb_ninodes sb ->
  Z.of_nat (fs_link_count P sb z)
    <= bv_unsigned (di_nlink (fs_dinode P sb z))
  /\ (bv_unsigned (di_type (fs_dinode P sb z)) = T_DIR_z ->
      fs_link_count P sb z = 0%nat
      /\ bv_unsigned (di_nlink (fs_dinode P sb z)) = 1
      /\ z = ROOTINO).
Proof.
  intros H Hz. unfold fs_links_wf in H. cbv zeta in H.
  pose proof (forallb_seq _ (Z.to_nat (sb_ninodes sb)) (Z.to_nat z) H
                ltac:(lia)) as Hk.
  cbv beta zeta in Hk. rewrite Z2Nat.id in Hk by lia.
  apply andb_true_iff in Hk as [Hle Hdir].
  split; [apply Z.leb_le; exact Hle |].
  intros Hty. rewrite (proj2 (Z.eqb_eq _ _) Hty) in Hdir.
  rewrite !andb_true_iff in Hdir. destruct Hdir as [[Hc Hnl] Hr].
  split; [exact (proj1 (Nat.eqb_eq _ 0) Hc) |].
  split; [apply Z.eqb_eq; exact Hnl | apply Z.eqb_eq; exact Hr].
Qed.

(* ---- W3 MINUS THE LINK FLOOR: THE DURABLE PER-RECORD SANITY ----------
   [fs_inode_wf]'s [1 <= nlink] clause is a boot-time fact, not a durable
   one: a COMMITTED ORPHAN -- an inode unlinked while open, whose zeroed
   [nlink] the transaction wrote home; xv6's boot sweep ([ireclaim],
   fs.c) exists for exactly these -- keeps a live type, a sane size and
   sane addrs with [nlink = 0].  The pure durable invariant that swept
   THIS form is deleted (ruling 3); [fs_inode_wf]
   stays as-is for the boot readings (at a clean mkfs image the two
   coincide, [fs_inodes_wf_dwf]).

   **THE BEYOND-SIZE RULING (durable-disk F3; kernel-defects.md's
   RESOLVED [writei] entry).**  An inode MAY own allocated data blocks
   beyond [nblk(size)]: [itrunc] frees [addrs[0..NDIRECT)] and the whole
   indirect range REGARDLESS of the size, so a beyond-size entry is owned,
   not leaked, and [writei]'s partial-failure commits -- which install a
   block and then leave [ip->size] alone -- are inside the design.  So the
   durable form does NOT carry [fs_inode_wf]'s "an entry at or above
   [nb] is zero" clauses; what it says of EVERY entry is the resource
   layer's own [InodeInv.blkmap_wf] clause, "a nonzero entry is a data
   block", with [InodeInv.bm_covers]' clause ("every index below the size
   is allocated") beside it as the separate below-size reading.  The two
   together are exactly the boolean's two branches.                      *)
Definition fs_inode_dwf (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode)
  : bool :=
  let sz := bv_unsigned (di_size dn) in
  let nb := fs_nblk sz in
  let ib := bv_unsigned (di_addrs dn !!! 12%nat) in
  let es := fs_ind_ents P dn in
  ((bv_unsigned (di_type dn) =? T_DIR_z)
     || (bv_unsigned (di_type dn) =? T_FILE_z)
     || (bv_unsigned (di_type dn) =? T_DEVICE_z)) &&
  (sz <=? Z.of_nat FS_MAXFILE * BSIZE_z) &&
  List.forallb
    (fun k => let a := bv_unsigned (di_addrs dn !!! k) in
              if Z.of_nat k <? nb
              then fs_addr_ok sb a else (a =? 0) || fs_addr_ok sb a)
    (seq 0 FS_NDIRECT) &&
  (if nb <=? Z.of_nat FS_NDIRECT
   then (ib =? 0) || fs_addr_ok sb ib else fs_addr_ok sb ib) &&
  List.forallb
    (fun j => let e := es !!! j in
              if Z.of_nat j <? nb - Z.of_nat FS_NDIRECT
              then fs_addr_ok sb e else (e =? 0) || fs_addr_ok sb e)
    (seq 0 FS_NINDIRECT).

(* [fs_inode_ok] with its three "zero above the size" clauses replaced by
   the three ENTRY clauses of the ruling above (a nonzero entry, wherever
   it sits, is a data block).  The below-size clauses stay verbatim: they
   are the pure reading of [InodeInv.bm_covers], which the resource layer
   keeps as its own conjunct beside [blkmap_wf] and which every write path
   maintains. *)
Record fs_inode_dok (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode)
  : Prop := {
  fdi_type : bv_unsigned (di_type dn) = T_DIR_z
             \/ bv_unsigned (di_type dn) = T_FILE_z
             \/ bv_unsigned (di_type dn) = T_DEVICE_z;
  fdi_size : bv_unsigned (di_size dn) <= Z.of_nat FS_MAXFILE * BSIZE_z;
  fdi_direct : forall k : nat, (k < FS_NDIRECT)%nat ->
      Z.of_nat k < fs_nblk (bv_unsigned (di_size dn)) ->
      fs_data_start sb <= bv_unsigned (di_addrs dn !!! k) < sb_size sb;
  fdi_direct_ok : forall k : nat, (k < FS_NDIRECT)%nat ->
      bv_unsigned (di_addrs dn !!! k) <> 0 ->
      fs_data_start sb <= bv_unsigned (di_addrs dn !!! k) < sb_size sb;
  fdi_ind_ok : bv_unsigned (di_addrs dn !!! 12%nat) <> 0 ->
      fs_data_start sb <= bv_unsigned (di_addrs dn !!! 12%nat) < sb_size sb;
  fdi_ind : Z.of_nat FS_NDIRECT < fs_nblk (bv_unsigned (di_size dn)) ->
      fs_data_start sb <= bv_unsigned (di_addrs dn !!! 12%nat) < sb_size sb;
  fdi_ent : forall j : nat, (j < FS_NINDIRECT)%nat ->
      Z.of_nat j < fs_nblk (bv_unsigned (di_size dn)) - Z.of_nat FS_NDIRECT ->
      fs_data_start sb <= fs_ind_ents P dn !!! j < sb_size sb;
  fdi_ent_ok : forall j : nat, (j < FS_NINDIRECT)%nat ->
      fs_ind_ents P dn !!! j <> 0 ->
      fs_data_start sb <= fs_ind_ents P dn !!! j < sb_size sb;
}.

Lemma fs_inode_dwf_ok (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode) :
  fs_inode_dwf P sb dn = true -> fs_inode_dok P sb dn.
Proof.
  unfold fs_inode_dwf. intros H. rewrite !andb_true_iff in H.
  destruct H as [[[[Hty Hsz] Hdir] Hind] Hent].
  constructor.
  - rewrite !orb_true_iff, !Z.eqb_eq in Hty. tauto.
  - apply Z.leb_le. exact Hsz.
  - intros k Hk Hlt. apply fs_addr_ok_spec.
    pose proof (forallb_seq _ FS_NDIRECT k Hdir Hk) as Hk'.
    cbv beta zeta in Hk'. rewrite (proj2 (Z.ltb_lt _ _) Hlt) in Hk'. exact Hk'.
  - intros k Hk Hnz. apply fs_addr_ok_spec.
    pose proof (forallb_seq _ FS_NDIRECT k Hdir Hk) as Hk'.
    cbv beta zeta in Hk'.
    destruct (Z.of_nat k <? fs_nblk (bv_unsigned (di_size dn)));
      [exact Hk' |].
    rewrite orb_true_iff in Hk'. destruct Hk' as [Hz | Hok']; [| exact Hok'].
    exfalso. exact (Hnz (proj1 (Z.eqb_eq _ _) Hz)).
  - intros Hnz. apply fs_addr_ok_spec.
    destruct (fs_nblk (bv_unsigned (di_size dn)) <=? Z.of_nat FS_NDIRECT);
      [| exact Hind].
    rewrite orb_true_iff in Hind. destruct Hind as [Hz | Hok']; [| exact Hok'].
    exfalso. exact (Hnz (proj1 (Z.eqb_eq _ _) Hz)).
  - intros Hgt. apply fs_addr_ok_spec.
    rewrite (proj2 (Z.leb_gt _ _) Hgt) in Hind. exact Hind.
  - intros j Hj Hlt. apply fs_addr_ok_spec.
    pose proof (forallb_seq _ FS_NINDIRECT j Hent Hj) as Hj'.
    cbv beta zeta in Hj'. rewrite (proj2 (Z.ltb_lt _ _) Hlt) in Hj'. exact Hj'.
  - intros j Hj Hnz. apply fs_addr_ok_spec.
    pose proof (forallb_seq _ FS_NINDIRECT j Hent Hj) as Hj'.
    cbv beta zeta in Hj'.
    destruct (Z.of_nat j
              <? fs_nblk (bv_unsigned (di_size dn)) - Z.of_nat FS_NDIRECT);
      [exact Hj' |].
    rewrite orb_true_iff in Hj'. destruct Hj' as [Hz | Hok']; [| exact Hok'].
    exfalso. exact (Hnz (proj1 (Z.eqb_eq _ _) Hz)).
Qed.

(* MOVING THE SIZE (durable-disk F3.2).  The entry clauses do not read
   the size at all, so a size move owes exactly [InodeInv.bm_covers]' own
   obligation at the NEW size -- which is why the size move is not fused
   into an allocation: fusing it would force the append equation back. *)
Lemma fs_inode_dok_size (P : Z -> list (bv 8)) (sb : fs_sb)
    (dn dn' : dinode) :
  fs_inode_dok P sb dn ->
  di_type dn' = di_type dn ->
  di_addrs dn' = di_addrs dn ->
  bv_unsigned (di_size dn') <= Z.of_nat FS_MAXFILE * BSIZE_z ->
  (forall k : nat, (k < FS_MAXFILE)%nat ->
     Z.of_nat k < fs_nblk (bv_unsigned (di_size dn')) ->
     fs_blk_addr P dn k <> 0) ->
  fs_inode_dok P sb dn'.
Proof.
  intros Hd Ht Ha Hcap Hcov.
  assert (HDM : (FS_NDIRECT + FS_NINDIRECT)%nat = FS_MAXFILE)
    by reflexivity.
  assert (HNI : (0 < FS_NINDIRECT)%nat) by (unfold FS_NINDIRECT; lia).
  assert (Hent : fs_ind_ents P dn' = fs_ind_ents P dn)
    by (unfold fs_ind_ents; rewrite Ha; reflexivity).
  constructor; rewrite ?Ht, ?Ha, ?Hent.
  - exact (fdi_type P sb dn Hd).
  - exact Hcap.
  - intros k Hk Hlt. apply (fdi_direct_ok P sb dn Hd k Hk).
    pose proof (Hcov k ltac:(lia) Hlt) as Hnz.
    unfold fs_blk_addr in Hnz.
    rewrite (proj2 (Nat.ltb_lt k FS_NDIRECT) Hk) in Hnz. exact Hnz.
  - exact (fdi_direct_ok P sb dn Hd).
  - exact (fdi_ind_ok P sb dn Hd).
  - intros Hgt. apply (fdi_ind_ok P sb dn Hd).
    intros Hz.
    pose proof (Hcov FS_NDIRECT ltac:(lia) Hgt) as Hnz.
    unfold fs_blk_addr in Hnz.
    rewrite (proj2 (Nat.ltb_ge FS_NDIRECT FS_NDIRECT) ltac:(lia)) in Hnz.
    apply Hnz. rewrite Nat.sub_diag.
    unfold fs_ind_ents. rewrite Hz.
    apply lookup_total_replicate_2. unfold FS_NINDIRECT. lia.
  - intros j Hj Hlt. apply (fdi_ent_ok P sb dn Hd j Hj).
    pose proof (Hcov (FS_NDIRECT + j)%nat ltac:(lia) ltac:(lia)) as Hnz.
    unfold fs_blk_addr in Hnz.
    rewrite (proj2 (Nat.ltb_ge (FS_NDIRECT + j) FS_NDIRECT) ltac:(lia))
      in Hnz.
    replace (FS_NDIRECT + j - FS_NDIRECT)%nat with j in Hnz by lia.
    exact Hnz.
  - exact (fdi_ent_ok P sb dn Hd).
Qed.

(* THE RECORD AND THE BOOLEAN ARE THE SAME CLAIM.  Every effect proof
   establishes the [dok] clauses of the record it writes; this turns that
   into the [fs_inodes_dwf] sweep's own boolean, so no proof re-derives
   the branch structure of [fs_inode_dwf] by hand. *)
Lemma fs_inode_dok_dwf (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode) :
  fs_inode_dok P sb dn -> fs_inode_dwf P sb dn = true.
Proof.
  intros Hd. unfold fs_inode_dwf. cbv zeta.
  rewrite !andb_true_iff.
  split; [split; [split; [split |] |] |].
  - destruct (fdi_type P sb dn Hd) as [Ht | [Ht | Ht]]; rewrite Ht;
      reflexivity.
  - apply Z.leb_le. exact (fdi_size P sb dn Hd).
  - rewrite List.forallb_forall. intros k Hk.
    apply elem_of_list_In, elem_of_seq in Hk. cbv beta zeta.
    destruct (Z.ltb_spec (Z.of_nat k)
                (fs_nblk (bv_unsigned (di_size dn)))) as [Hlt | Hge].
    + apply fs_addr_ok_spec.
      exact (fdi_direct P sb dn Hd k ltac:(lia) Hlt).
    + destruct (decide (bv_unsigned (di_addrs dn !!! k) = 0))
        as [Hz | Hnz].
      * rewrite Hz. reflexivity.
      * rewrite orb_true_iff. right. apply fs_addr_ok_spec.
        exact (fdi_direct_ok P sb dn Hd k ltac:(lia) Hnz).
  - destruct (Z.leb_spec (fs_nblk (bv_unsigned (di_size dn)))
                (Z.of_nat FS_NDIRECT)) as [Hle | Hgt].
    + destruct (decide (bv_unsigned (di_addrs dn !!! 12%nat) = 0))
        as [Hz | Hnz].
      * rewrite Hz. reflexivity.
      * rewrite orb_true_iff. right. apply fs_addr_ok_spec.
        exact (fdi_ind_ok P sb dn Hd Hnz).
    + apply fs_addr_ok_spec. exact (fdi_ind P sb dn Hd Hgt).
  - rewrite List.forallb_forall. intros j Hj.
    apply elem_of_list_In, elem_of_seq in Hj. cbv beta zeta.
    destruct (Z.ltb_spec (Z.of_nat j)
                (fs_nblk (bv_unsigned (di_size dn)) - Z.of_nat FS_NDIRECT))
      as [Hlt | Hge].
    + apply fs_addr_ok_spec.
      exact (fdi_ent P sb dn Hd j ltac:(lia) Hlt).
    + destruct (decide (fs_ind_ents P dn !!! j = 0)) as [Hz | Hnz].
      * rewrite Hz. reflexivity.
      * rewrite orb_true_iff. right. apply fs_addr_ok_spec.
        exact (fdi_ent_ok P sb dn Hd j ltac:(lia) Hnz).
Qed.

Lemma fs_inode_ok_dok (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode) :
  fs_inode_ok P sb dn -> fs_inode_dok P sb dn.
Proof.
  intros Hok. constructor.
  - exact (fio_type P sb dn Hok).
  - exact (fio_size P sb dn Hok).
  - exact (fio_direct P sb dn Hok).
  - intros k Hk Hnz.
    destruct (Z.lt_ge_cases (Z.of_nat k)
                (fs_nblk (bv_unsigned (di_size dn)))) as [Hlt | Hge];
      [exact (fio_direct P sb dn Hok k Hk Hlt) |].
    exfalso. exact (Hnz (fio_direct_zero P sb dn Hok k Hk Hge)).
  - intros Hnz.
    destruct (Z.lt_ge_cases (Z.of_nat FS_NDIRECT)
                (fs_nblk (bv_unsigned (di_size dn)))) as [Hlt | Hge];
      [exact (fio_ind P sb dn Hok Hlt) |].
    exfalso. exact (Hnz (fio_ind_zero P sb dn Hok Hge)).
  - exact (fio_ind P sb dn Hok).
  - exact (fio_ent P sb dn Hok).
  - intros j Hj Hnz.
    destruct (Z.lt_ge_cases (Z.of_nat j)
                (fs_nblk (bv_unsigned (di_size dn)) - Z.of_nat FS_NDIRECT))
      as [Hlt | Hge]; [exact (fio_ent P sb dn Hok j Hj Hlt) |].
    exfalso. exact (Hnz (fio_ent_zero P sb dn Hok j Hj Hge)).
Qed.

Lemma fs_inode_wf_dwf (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode) :
  fs_inode_wf P sb dn = true -> fs_inode_dwf P sb dn = true.
Proof.
  unfold fs_inode_wf, fs_inode_dwf. cbv zeta.
  rewrite !andb_true_iff.
  intros [[[[[Hty Hnl] Hsz] Hdir] Hind] Hent].
  split; [split; [split |] |].
  - split; [exact Hty | exact Hsz].
  - rewrite List.forallb_forall. intros k Hk.
    apply elem_of_list_In, elem_of_seq in Hk.
    pose proof (forallb_seq _ FS_NDIRECT k Hdir ltac:(lia)) as Hk'.
    cbv beta zeta in Hk' |- *.
    destruct (Z.of_nat k <? fs_nblk (bv_unsigned (di_size dn)));
      [exact Hk' | rewrite Hk'; reflexivity].
  - destruct (fs_nblk (bv_unsigned (di_size dn)) <=? Z.of_nat FS_NDIRECT);
      [rewrite Hind; reflexivity | exact Hind].
  - rewrite List.forallb_forall. intros j Hj.
    apply elem_of_list_In, elem_of_seq in Hj.
    pose proof (forallb_seq _ FS_NINDIRECT j Hent ltac:(lia)) as Hj'.
    cbv beta zeta in Hj' |- *.
    destruct (Z.of_nat j
              <? fs_nblk (bv_unsigned (di_size dn)) - Z.of_nat FS_NDIRECT);
      [exact Hj' | rewrite Hj'; reflexivity].
Qed.

Definition fs_inodes_dwf (P : Z -> list (bv 8)) (sb : fs_sb) : bool :=
  List.forallb
    (fun i => let dn := fs_dinode P sb (Z.of_nat i) in
              if bv_unsigned (di_type dn) =? 0 then true
              else fs_inode_dwf P sb dn)
    (seq 0 (Z.to_nat (sb_ninodes sb))).

Lemma fs_inodes_dwf_spec (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fs_inodes_dwf P sb = true -> 0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  fs_inode_dok P sb (fs_dinode P sb i).
Proof.
  intros H Hi Hnz. apply fs_inode_dwf_ok.
  pose proof (forallb_seq _ (Z.to_nat (sb_ninodes sb)) (Z.to_nat i) H
                ltac:(lia)) as Hk.
  cbv beta zeta in Hk. rewrite Z2Nat.id in Hk by lia.
  destruct (bv_unsigned (di_type (fs_dinode P sb i)) =? 0) eqn:E;
    [| exact Hk].
  exfalso. apply Hnz, Z.eqb_eq, E.
Qed.

Lemma fs_inodes_wf_dwf (P : Z -> list (bv 8)) (sb : fs_sb) :
  fs_inodes_wf P sb = true -> fs_inodes_dwf P sb = true.
Proof.
  intros H. unfold fs_inodes_dwf.
  rewrite List.forallb_forall. intros x Hin.
  apply elem_of_list_In, elem_of_seq in Hin.
  pose proof (forallb_seq _ _ x H ltac:(lia)) as Hx.
  cbv beta zeta in Hx. cbv beta zeta.
  destruct (bv_unsigned (di_type (fs_dinode P sb (Z.of_nat x))) =? 0);
    [reflexivity |].
  apply fs_inode_wf_dwf. exact Hx.
Qed.

(* ====================================================================== *)
(*  11bis.  THE ENTRY-DERIVED USED SET (durable-disk stage F3.1)           *)
(*                                                                        *)
(*  Under the beyond-size ruling the durable used set cannot be indexed    *)
(*  by [nblk(size)]: an inode owns EVERY nonzero entry, and [itrunc]       *)
(*  frees exactly those.  So the durable W4/W5 pair reads this family --   *)
(*  one inode's nonzero slots, joined over the live inums -- while         *)
(*  [fs_used_blocks]/[fs_used_set] above stay exactly as they are for the  *)
(*  IMAGE check ([fsimg_wf], whose [vm_compute] must not move).  The two   *)
(*  agree wherever no entry sits beyond the size, which is exactly         *)
(*  [fs_inode_ok]: [fs_inode_ents_blocks] below is that bridge, and it is  *)
(*  an EQUATION, not a permutation -- the indirect block heads both lists  *)
(*  and the filter of a "nonzero below [nb], zero above" entry run IS the  *)
(*  below-[nb] prefix.                                                    *)
(*                                                                        *)
(*  THE SLOT LIST IS SPELLED AS A CONCATENATION, NOT AS A 269-WIDE         *)
(*  [fs_slot]-INDEXED FMAP, and that is forced (durable-notes, the        *)
(*  definition-nobody-computes-but-the-unifier-will rule): every          *)
(*  [fs_slot] at an indirect index carries its own copy of                 *)
(*  [fs_ind_ents P dn], so the fmap form makes ONE conversion check        *)
(*  expand 256 copies of a 256-element list and a [f_equal] then runs for  *)
(*  a quarter of an hour with no error.  Here [fs_ind_ents P dn] occurs    *)
(*  ONCE; [fs_slot_list_lookup] is the index bijection onto               *)
(*  [InodeInv.bm_slot]'s numbering.                                        *)
(* ====================================================================== *)

(* ---- the list plumbing the filter reading needs ---------------------- *)

Lemma filter_all_true {A : Type} (p : A -> bool) (l : list A) :
  (forall x : A, x ∈ l -> p x = true) -> List.filter p l = l.
Proof.
  induction l as [| a l IH]; intros H; [reflexivity |].
  cbn [List.filter]. rewrite (H a (elem_of_list_here a l)).
  f_equal. apply IH. intros x Hx. apply H, elem_of_list_further, Hx.
Qed.

Lemma filter_all_false {A : Type} (p : A -> bool) (l : list A) :
  (forall x : A, x ∈ l -> p x = false) -> List.filter p l = [].
Proof.
  induction l as [| a l IH]; intros H; [reflexivity |].
  cbn [List.filter]. rewrite (H a (elem_of_list_here a l)).
  apply IH. intros x Hx. apply H, elem_of_list_further, Hx.
Qed.

Lemma fmap_seq_split {A : Type} (f : nat -> A) (m r : nat) :
  (f <$> seq 0 (m + r)) = ((f <$> seq 0 m) ++ (f <$> seq m r))%list.
Proof.
  rewrite List.seq_app, Nat.add_0_l, fmap_app. reflexivity.
Qed.

(* the whole point: a run that is nonzero below [m] and zero from [m] to
   [n] filters to its own below-[m] prefix *)
Lemma filter_nz_prefix (f : nat -> Z) (n m : nat) :
  (m <= n)%nat ->
  (forall k : nat, (k < m)%nat -> f k <> 0) ->
  (forall k : nat, (m <= k)%nat -> (k < n)%nat -> f k = 0) ->
  List.filter (fun a => negb (a =? 0)) (f <$> seq 0 n) = f <$> seq 0 m.
Proof.
  intros Hmn Hlo Hhi.
  replace n with (m + (n - m))%nat by lia.
  rewrite (fmap_seq_split f m (n - m)), List.filter_app.
  rewrite (filter_all_true _ (f <$> seq 0 m)).
  2:{ intros x Hx. apply elem_of_list_fmap in Hx as (k & -> & Hk).
      apply elem_of_seq in Hk.
      apply negb_true_iff, Z.eqb_neq, Hlo. lia. }
  rewrite (filter_all_false _ (f <$> seq m (n - m))).
  2:{ intros x Hx. apply elem_of_list_fmap in Hx as (k & -> & Hk).
      apply elem_of_seq in Hk.
      apply negb_false_iff, Z.eqb_eq, Hhi; lia. }
  apply List.app_nil_r.
Qed.

(* a total-lookup fmap over a list's own length is that list *)
Lemma list_total_seq {A : Type} `{Inhabited A} (l : list A) :
  ((fun j => l !!! j) <$> seq 0 (length l)) = l.
Proof.
  apply list_eq. intros k. rewrite list_lookup_fmap.
  destruct (Nat.lt_ge_cases k (length l)) as [Hk | Hk].
  - rewrite (lookup_seq_lt 0 _ k Hk).
    cbn [fmap option_fmap option_map]. rewrite Nat.add_0_l.
    rewrite (list_lookup_total_alt l k).
    destruct (l !! k) as [a|] eqn:E; [reflexivity |].
    exfalso. apply lookup_ge_None in E. lia.
  - rewrite (lookup_seq_ge 0 _ k Hk). symmetry.
    apply lookup_ge_None. lia.
Qed.

(* NO DUPLICATES IN THE FILTER MEANS THE KEPT POSITIONS ARE UNIQUE -- the
   only reading of [NoDup] the injectivity clause wants *)
Lemma NoDup_filter_lookup_inj {A : Type} (p : A -> bool) (l : list A) :
  NoDup (List.filter p l) ->
  forall (i j : nat) (x : A),
    l !! i = Some x -> l !! j = Some x -> p x = true -> i = j.
Proof.
  revert l. induction l as [| a l IH]; intros Hnd i j x Hi Hj Hp.
  { destruct i; discriminate. }
  cbn [List.filter] in Hnd.
  assert (Hkeep : forall (m : nat), l !! m = Some x ->
            x ∈ List.filter p l).
  { intros m Hm. apply elem_of_list_In, List.filter_In.
    split; [apply elem_of_list_In, (elem_of_list_lookup_2 l m x Hm) | exact Hp]. }
  destruct i as [| i']; destruct j as [| j']; cbn [lookup list_lookup] in Hi, Hj.
  - reflexivity.
  - injection Hi as ->. exfalso.
    rewrite Hp in Hnd.
    exact (NoDup_cons_1_1 x (List.filter p l) Hnd (Hkeep j' Hj)).
  - injection Hj as ->. exfalso.
    rewrite Hp in Hnd.
    exact (NoDup_cons_1_1 x (List.filter p l) Hnd (Hkeep i' Hi)).
  - assert (Hnd' : NoDup (List.filter p l)).
    { destruct (p a);
        [exact (NoDup_cons_1_2 a (List.filter p l) Hnd) | exact Hnd]. }
    f_equal. exact (IH Hnd' i' j' x Hi Hj Hp).
Qed.

(* the geometry fact the entry clauses turn into "nonzero" *)
Lemma fs_data_start_pos (sb : fs_sb) : fs_sb_ok sb -> 0 < fs_data_start sb.
Proof.
  intros Hok. unfold fs_data_start.
  pose proof (sbo_bmapstart sb Hok).
  pose proof (sbo_inodestart sb Hok).
  pose proof (sbo_logstart sb Hok).
  pose proof (sbo_nlog sb Hok).
  pose proof (sbo_ninodes sb Hok). unfold ROOTINO in *.
  pose proof (Z.div_pos (sb_ninodes sb) 16 ltac:(lia) ltac:(lia)). lia.
Qed.

(* the slot reader sees the record only through [di_addrs] and the view
   only through [fs_ind_ents] -- the two facts every transport establishes *)
Lemma fs_slot_det (P P' : Z -> list (bv 8)) (dn dn' : dinode) (k : nat) :
  di_addrs dn' = di_addrs dn -> fs_ind_ents P' dn' = fs_ind_ents P dn ->
  fs_slot P' dn' k = fs_slot P dn k.
Proof.
  intros Ha He. unfold fs_slot, fs_blk_addr. rewrite Ha, He. reflexivity.
Qed.

Lemma fs_slot_lt (P : Z -> list (bv 8)) (dn : dinode) (i : nat) :
  (i < FS_MAXFILE)%nat -> fs_slot P dn i = fs_blk_addr P dn i.
Proof.
  intros Hi. unfold fs_slot. rewrite decide_False by lia. reflexivity.
Qed.

(* ---- one inode's slots, listed, and its nonzero ones ----------------- *)

Definition fs_slot_list (P : Z -> list (bv 8)) (dn : dinode) : list Z :=
  (bv_unsigned (di_addrs dn !!! 12%nat)
   :: (((fun k => bv_unsigned (di_addrs dn !!! k)) <$> seq 0 FS_NDIRECT)
       ++ fs_ind_ents P dn))%list.

(* [InodeInv.bm_slot]'s index, as a position in [fs_slot_list] *)
Definition fs_run_ix (i : nat) : nat :=
  if decide (i = FS_MAXFILE) then 0%nat else S i.

Lemma fs_run_ix_inj (i j : nat) :
  (i <= FS_MAXFILE)%nat -> (j <= FS_MAXFILE)%nat ->
  fs_run_ix i = fs_run_ix j -> i = j.
Proof.
  unfold fs_run_ix. intros Hi Hj H.
  destruct (decide (i = FS_MAXFILE)) as [-> | Hi'];
    destruct (decide (j = FS_MAXFILE)) as [-> | Hj'];
    [reflexivity | discriminate | discriminate | injection H as H; exact H].
Qed.

Lemma fs_slot_list_lookup (P : Z -> list (bv 8)) (dn : dinode) (i : nat) :
  (i <= FS_MAXFILE)%nat ->
  fs_slot_list P dn !! fs_run_ix i = Some (fs_slot P dn i).
Proof.
  intros Hi. unfold fs_slot_list, fs_run_ix.
  destruct (decide (i = FS_MAXFILE)) as [-> | Hne].
  - rewrite fs_slot_max. reflexivity.
  - assert (HiM : (i < FS_MAXFILE)%nat) by lia.
    change ((bv_unsigned (di_addrs dn !!! 12%nat)
             :: (((fun k => bv_unsigned (di_addrs dn !!! k))
                    <$> seq 0 FS_NDIRECT) ++ fs_ind_ents P dn)) !! S i)
      with ((((fun k => bv_unsigned (di_addrs dn !!! k))
                <$> seq 0 FS_NDIRECT) ++ fs_ind_ents P dn) !! i).
    rewrite (fs_slot_lt P dn i HiM). unfold fs_blk_addr.
    destruct (Nat.ltb_spec i FS_NDIRECT) as [Hd | Hd].
    + rewrite lookup_app_l by (rewrite length_fmap, length_seq; lia).
      rewrite list_lookup_fmap, (lookup_seq_lt 0 _ i Hd).
      reflexivity.
    + rewrite lookup_app_r by (rewrite length_fmap, length_seq; lia).
      rewrite length_fmap, length_seq.
      rewrite (list_lookup_total_alt (fs_ind_ents P dn) (i - FS_NDIRECT)%nat).
      destruct (fs_ind_ents P dn !! (i - FS_NDIRECT)%nat) as [a|] eqn:E;
        [reflexivity |].
      exfalso. apply lookup_ge_None in E.
      rewrite fs_ind_ents_length in E.
      unfold FS_MAXFILE, FS_NDIRECT, FS_NINDIRECT in *. lia.
Qed.

Lemma fs_slot_list_elem (P : Z -> list (bv 8)) (dn : dinode) (b : Z) :
  b ∈ fs_slot_list P dn ->
  exists i : nat, (i <= FS_MAXFILE)%nat /\ fs_slot P dn i = b.
Proof.
  assert (HDM : (FS_NDIRECT + FS_NINDIRECT)%nat = FS_MAXFILE) by reflexivity.
  unfold fs_slot_list. intros Hb.
  apply elem_of_cons in Hb as [-> | Hb].
  - exists FS_MAXFILE. split; [lia | rewrite fs_slot_max; reflexivity].
  - apply elem_of_app in Hb as [Hb | Hb].
    + apply elem_of_list_fmap in Hb as (k & -> & Hk).
      apply elem_of_seq in Hk.
      assert (HkD : (k < FS_NDIRECT)%nat) by lia.
      assert (HkM : (k < FS_MAXFILE)%nat) by lia.
      exists k. split; [lia |].
      rewrite (fs_slot_lt P dn k HkM). unfold fs_blk_addr.
      rewrite (proj2 (Nat.ltb_lt k FS_NDIRECT) HkD). reflexivity.
    + apply elem_of_list_lookup in Hb as (j & Hj).
      assert (Hjl : (j < FS_NINDIRECT)%nat).
      { apply lookup_lt_Some in Hj. rewrite fs_ind_ents_length in Hj.
        exact Hj. }
      exists (FS_NDIRECT + j)%nat.
      split; [lia |].
      rewrite (fs_slot_ent P dn (FS_NDIRECT + j)%nat
                 ltac:(lia) ltac:(lia)).
      replace (FS_NDIRECT + j - FS_NDIRECT)%nat with j by lia.
      rewrite (list_lookup_total_alt (fs_ind_ents P dn) j), Hj.
      reflexivity.
Qed.

Definition fs_inode_ents (P : Z -> list (bv 8)) (dn : dinode) : list Z :=
  List.filter (fun a => negb (a =? 0)) (fs_slot_list P dn).

(* a nonzero slot is a member... *)
Lemma fs_inode_ents_slot (P : Z -> list (bv 8)) (dn : dinode) (i : nat) :
  (i <= FS_MAXFILE)%nat -> fs_slot P dn i <> 0 ->
  fs_slot P dn i ∈ fs_inode_ents P dn.
Proof.
  intros Hi Hnz. unfold fs_inode_ents.
  apply elem_of_list_In, List.filter_In. split.
  - apply elem_of_list_In, elem_of_list_lookup.
    exists (fs_run_ix i). exact (fs_slot_list_lookup P dn i Hi).
  - apply negb_true_iff, Z.eqb_neq. exact Hnz.
Qed.

(* ...and every member is one *)
Lemma fs_inode_ents_elem (P : Z -> list (bv 8)) (dn : dinode) (b : Z) :
  b ∈ fs_inode_ents P dn ->
  exists i : nat, (i <= FS_MAXFILE)%nat /\ fs_slot P dn i = b /\ b <> 0.
Proof.
  unfold fs_inode_ents. intros Hb.
  apply elem_of_list_In, List.filter_In in Hb as (Hin & Hnz).
  apply elem_of_list_In in Hin.
  destruct (fs_slot_list_elem P dn b Hin) as (i & Hi & Heq).
  exists i. split; [exact Hi |]. split; [exact Heq |].
  apply negb_true_iff, Z.eqb_neq in Hnz. exact Hnz.
Qed.

(* every entry a live inode names is a data block -- the entry clauses of
   [fs_inode_dok], read at membership altitude *)
Lemma fs_inode_ents_range (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode)
    (b : Z) :
  fs_inode_dok P sb dn -> b ∈ fs_inode_ents P dn ->
  fs_data_start sb <= b < sb_size sb.
Proof.
  intros Hd Hb.
  destruct (fs_inode_ents_elem P dn b Hb) as (i & Hi & Heq & Hnz).
  rewrite <- Heq in Hnz |- *.
  destruct (decide (i = FS_MAXFILE)) as [-> | Hne].
  - rewrite fs_slot_max in Hnz |- *. exact (fdi_ind_ok P sb dn Hd Hnz).
  - assert (Hlt : (i < FS_MAXFILE)%nat) by lia.
    destruct (Nat.lt_ge_cases i FS_NDIRECT) as [Hdir | Hdir].
    + rewrite (fs_slot_direct P dn i Hdir) in Hnz |- *.
      exact (fdi_direct_ok P sb dn Hd i Hdir Hnz).
    + rewrite (fs_slot_ent P dn i Hdir Hlt) in Hnz |- *.
      apply (fdi_ent_ok P sb dn Hd (i - FS_NDIRECT)%nat);
        [unfold FS_MAXFILE, FS_NDIRECT, FS_NINDIRECT in *; lia | exact Hnz].
Qed.

(* [InodeInv.blkmap_wf]'s injectivity clause, off the duplicate-freedom of
   ONE inode's entry list *)
Lemma fs_slot_inj_of_ents (P : Z -> list (bv 8)) (dn : dinode) :
  NoDup (fs_inode_ents P dn) -> fs_slot_inj P dn.
Proof.
  unfold fs_inode_ents. intros Hnd i j Hi Hj Hnz Heq.
  apply (fs_run_ix_inj i j Hi Hj).
  apply (NoDup_filter_lookup_inj _ (fs_slot_list P dn) Hnd _ _
           (fs_slot P dn i)).
  - exact (fs_slot_list_lookup P dn i Hi).
  - rewrite Heq. exact (fs_slot_list_lookup P dn j Hj).
  - apply negb_true_iff, Z.eqb_neq. exact Hnz.
Qed.

(* the entry list depends on the record only through [di_addrs] and on the
   view only through [fs_ind_ents] -- the two transport premises every
   effect proof already establishes *)
Lemma fs_inode_ents_det (P P' : Z -> list (bv 8)) (dn dn' : dinode) :
  di_addrs dn' = di_addrs dn -> fs_ind_ents P' dn' = fs_ind_ents P dn ->
  fs_inode_ents P' dn' = fs_inode_ents P dn.
Proof.
  intros Ha He. unfold fs_inode_ents, fs_slot_list.
  rewrite Ha, He. reflexivity.
Qed.

(* the three chunks, for a proof that changes one of them *)
Lemma fs_inode_ents_alt (P : Z -> list (bv 8)) (dn : dinode) :
  fs_inode_ents P dn
  = ((if bv_unsigned (di_addrs dn !!! 12%nat) =? 0
      then [] else [bv_unsigned (di_addrs dn !!! 12%nat)])
     ++ List.filter (fun a => negb (a =? 0))
          ((fun k => bv_unsigned (di_addrs dn !!! k)) <$> seq 0 FS_NDIRECT)
     ++ List.filter (fun a => negb (a =? 0)) (fs_ind_ents P dn))%list.
Proof.
  unfold fs_inode_ents, fs_slot_list.
  cbn [List.filter]. rewrite List.filter_app.
  destruct (bv_unsigned (di_addrs dn !!! 12%nat) =? 0); reflexivity.
Qed.

(* ---- THE ALLOC DELTA: one empty slot becomes a block ------------------ *)

(* [NoDup] and membership travel along a permutation; the used set is a
   MULTISET fact, and an allocation inserts its block in the middle of the
   slot run rather than at the end. *)
Lemma NoDup_perm {A : Type} (l1 l2 : list A) :
  l1 ≡ₚ l2 -> NoDup l1 -> NoDup l2.
Proof.
  intros Hp Hnd. apply NoDup_ListNoDup.
  apply (Permutation_NoDup Hp). apply NoDup_ListNoDup. exact Hnd.
Qed.

Lemma elem_of_perm {A : Type} (l1 l2 : list A) (x : A) :
  l1 ≡ₚ l2 -> x ∈ l1 -> x ∈ l2.
Proof.
  intros Hp Hx. apply elem_of_list_In.
  apply (Permutation_in _ Hp). apply elem_of_list_In. exact Hx.
Qed.

Lemma filter_nz_mid (A B : list Z) (a : Z) :
  a <> 0 ->
  List.filter (fun x => negb (x =? 0)) (A ++ a :: B)
  ≡ₚ (List.filter (fun x => negb (x =? 0)) (A ++ 0 :: B) ++ [a])%list.
Proof.
  intros Ha. rewrite !List.filter_app. cbn [List.filter].
  rewrite (proj2 (negb_true_iff _) (proj2 (Z.eqb_neq _ _) Ha)).
  change (0 =? 0) with true. cbn [negb].
  rewrite <- List.app_assoc.
  apply Permutation_app_head, Permutation_cons_append.
Qed.

Lemma filter_nz_upd_perm (l : list Z) (j : nat) (a : Z) :
  l !! j = Some 0 -> a <> 0 ->
  List.filter (fun x => negb (x =? 0)) (<[j := a]> l)
  ≡ₚ (List.filter (fun x => negb (x =? 0)) l ++ [a])%list.
Proof.
  intros Hj Ha.
  assert (Hlen : (j < length l)%nat) by (apply lookup_lt_Some in Hj; lia).
  pose proof (filter_nz_mid (take j l) (drop (S j) l) a Ha) as Hm.
  rewrite (take_drop_middle l j 0 Hj) in Hm.
  rewrite (insert_take_drop l j a Hlen). exact Hm.
Qed.

Lemma fs_slot_list_length (P : Z -> list (bv 8)) (dn : dinode) :
  length (fs_slot_list P dn) = S FS_MAXFILE.
Proof.
  unfold fs_slot_list. cbn [length].
  rewrite length_app, length_fmap, length_seq, fs_ind_ents_length.
  reflexivity.
Qed.

Lemma fs_run_ix_surj (k : nat) :
  (k < S FS_MAXFILE)%nat ->
  exists i : nat, (i <= FS_MAXFILE)%nat /\ fs_run_ix i = k.
Proof.
  intros Hk. unfold fs_run_ix. destruct k as [| k'].
  - exists FS_MAXFILE. split; [lia |].
    destruct (decide (FS_MAXFILE = FS_MAXFILE)); [reflexivity | congruence].
  - exists k'. split; [lia |].
    destruct (decide (k' = FS_MAXFILE)) as [-> | Hne]; [lia | reflexivity].
Qed.

(* the slot list after ONE slot moves -- the shape [bmap]'s install has *)
Lemma fs_slot_list_upd (P P' : Z -> list (bv 8)) (dn dn' : dinode)
    (j : nat) (a : Z) :
  (j <= FS_MAXFILE)%nat ->
  fs_slot P' dn' j = a ->
  (forall k : nat, (k <= FS_MAXFILE)%nat -> k <> j ->
     fs_slot P' dn' k = fs_slot P dn k) ->
  fs_slot_list P' dn' = <[fs_run_ix j := a]> (fs_slot_list P dn).
Proof.
  intros Hj Ha Hkeep.
  assert (Hjl : (fs_run_ix j < S FS_MAXFILE)%nat).
  { unfold fs_run_ix. destruct (decide (j = FS_MAXFILE)); lia. }
  apply list_eq. intros k.
  destruct (Nat.lt_ge_cases k (S FS_MAXFILE)) as [Hk | Hk].
  - destruct (fs_run_ix_surj k Hk) as (i & Hi & <-).
    rewrite (fs_slot_list_lookup P' dn' i Hi).
    destruct (decide (i = j)) as [-> | Hne].
    + rewrite list_lookup_insert
        by (rewrite fs_slot_list_length; exact Hjl).
      rewrite Ha. reflexivity.
    + rewrite list_lookup_insert_ne
        by (intros Hc; exact (Hne (fs_run_ix_inj i j Hi Hj (eq_sym Hc)))).
      rewrite (fs_slot_list_lookup P dn i Hi), (Hkeep i Hi Hne).
      reflexivity.
  - rewrite lookup_ge_None_2 by (rewrite fs_slot_list_length; lia).
    symmetry. apply lookup_ge_None_2.
    rewrite length_insert, fs_slot_list_length. lia.
Qed.

(* THE ALLOC-SIDE ENTRY-LIST DELTA: filling an EMPTY slot adds exactly the
   fresh block to the inode's entry multiset. *)
Lemma fs_inode_ents_upd (P P' : Z -> list (bv 8)) (dn dn' : dinode)
    (j : nat) (a : Z) :
  (j <= FS_MAXFILE)%nat -> a <> 0 ->
  fs_slot P dn j = 0 -> fs_slot P' dn' j = a ->
  (forall k : nat, (k <= FS_MAXFILE)%nat -> k <> j ->
     fs_slot P' dn' k = fs_slot P dn k) ->
  fs_inode_ents P' dn' ≡ₚ (fs_inode_ents P dn ++ [a])%list.
Proof.
  intros Hj Ha Hz Ha' Hkeep.
  unfold fs_inode_ents.
  rewrite (fs_slot_list_upd P P' dn dn' j a Hj Ha' Hkeep).
  apply filter_nz_upd_perm; [| exact Ha].
  rewrite (fs_slot_list_lookup P dn j Hj), Hz. reflexivity.
Qed.

(* ---- the join over the live inums ------------------------------------ *)

Definition fs_ent_blocks (P : Z -> list (bv 8)) (sb : fs_sb) : list Z :=
  mjoin ((fun i => let dn := fs_dinode P sb (Z.of_nat i) in
                    if bv_unsigned (di_type dn) =? 0 then []
                    else fs_inode_ents P dn)
            <$> seq 0 (Z.to_nat (sb_ninodes sb))).

Definition fs_ent_set (P : Z -> list (bv 8)) (sb : fs_sb) : option (gset Z) :=
  gset_nodup (fs_ent_blocks P sb).

Lemma fs_ent_set_nodup (P : Z -> list (bv 8)) (sb : fs_sb) (u : gset Z) :
  fs_ent_set P sb = Some u -> NoDup (fs_ent_blocks P sb).
Proof. apply gset_nodup_NoDup. Qed.

Lemma fs_ent_set_elem (P : Z -> list (bv 8)) (sb : fs_sb) (u : gset Z)
    (b : Z) :
  fs_ent_set P sb = Some u -> (b ∈ u <-> b ∈ fs_ent_blocks P sb).
Proof. intros H. exact (gset_nodup_set _ u H b). Qed.

Lemma fs_ent_blocks_inode (P : Z -> list (bv 8)) (sb : fs_sb) (i b : Z) :
  0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  b ∈ fs_inode_ents P (fs_dinode P sb i) ->
  b ∈ fs_ent_blocks P sb.
Proof.
  intros Hi Hnz Hb. unfold fs_ent_blocks.
  apply elem_of_list_join. eexists. split; [exact Hb |].
  apply elem_of_list_fmap. exists (Z.to_nat i). split.
  - rewrite Z2Nat.id by lia.
    destruct (bv_unsigned (di_type (fs_dinode P sb i)) =? 0) eqn:E;
      [| reflexivity].
    exfalso. apply Hnz, Z.eqb_eq, E.
  - apply elem_of_seq. lia.
Qed.

Lemma fs_ent_blocks_nodup_inode (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  NoDup (fs_ent_blocks P sb) -> 0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  NoDup (fs_inode_ents P (fs_dinode P sb i)).
Proof.
  intros Hnd Hi Hnz. unfold fs_ent_blocks in Hnd.
  apply (NoDup_mjoin_elem _ _ Hnd).
  apply elem_of_list_fmap. exists (Z.to_nat i). split.
  - rewrite Z2Nat.id by lia.
    destruct (bv_unsigned (di_type (fs_dinode P sb i)) =? 0) eqn:E;
      [| reflexivity].
    exfalso. apply Hnz, Z.eqb_eq, E.
  - apply elem_of_seq. lia.
Qed.

Definition fs_inode_ents_set (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z)
  : gset Z := list_to_set (fs_inode_ents P (fs_dinode P sb i)).

Lemma fs_inode_ents_disjoint (P : Z -> list (bv 8)) (sb : fs_sb) (i j : Z) :
  NoDup (fs_ent_blocks P sb) ->
  0 <= i < sb_ninodes sb -> 0 <= j < sb_ninodes sb -> i <> j ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  bv_unsigned (di_type (fs_dinode P sb j)) <> 0 ->
  fs_inode_ents_set P sb i ## fs_inode_ents_set P sb j.
Proof.
  intros Hnd Hi Hj Hne Hti Htj.
  apply elem_of_disjoint. intros b Hb1 Hb2.
  unfold fs_inode_ents_set in Hb1, Hb2.
  rewrite elem_of_list_to_set in Hb1. rewrite elem_of_list_to_set in Hb2.
  unfold fs_ent_blocks in Hnd.
  apply (NoDup_mjoin_cross _ (Z.to_nat i) (Z.to_nat j)
           (fs_inode_ents P (fs_dinode P sb i))
           (fs_inode_ents P (fs_dinode P sb j)) b Hnd);
    [ | | lia | exact Hb1 | exact Hb2].
  - rewrite list_lookup_fmap, (lookup_seq_lt 0 _ (Z.to_nat i)) by lia.
    cbn [fmap option_fmap option_map].
    rewrite Nat.add_0_l, Z2Nat.id by lia.
    rewrite (proj2 (Z.eqb_neq _ _) Hti). reflexivity.
  - rewrite list_lookup_fmap, (lookup_seq_lt 0 _ (Z.to_nat j)) by lia.
    cbn [fmap option_fmap option_map].
    rewrite Nat.add_0_l, Z2Nat.id by lia.
    rewrite (proj2 (Z.eqb_neq _ _) Htj). reflexivity.
Qed.

(* ---- THE BRIDGE: where no entry sits beyond the size, the two readings  *)
(*      are the SAME LIST                                                  *)

Lemma fs_inode_ents_blocks (P : Z -> list (bv 8)) (sb : fs_sb)
    (dn : dinode) :
  fs_sb_ok sb -> fs_inode_ok P sb dn ->
  fs_inode_ents P dn = fs_inode_blocks P dn.
Proof.
  intros Hsbok Hok.
  assert (HDM : (FS_NDIRECT + FS_NINDIRECT)%nat = FS_MAXFILE) by reflexivity.
  pose proof (fs_data_start_pos sb Hsbok) as Hds.
  assert (Hnb : fs_nblk (bv_unsigned (di_size dn)) <= Z.of_nat FS_MAXFILE).
  { apply fs_nblk_max;
      [exact (proj1 (bv_unsigned_in_range _ _))
      | exact (fio_size P sb dn Hok)]. }
  assert (Hnb0 : 0 <= fs_nblk (bv_unsigned (di_size dn))).
  { unfold fs_nblk, BSIZE_z.
    pose proof (proj1 (bv_unsigned_in_range 32 (di_size dn))).
    apply Z.div_pos; lia. }
  rewrite fs_inode_ents_alt.
  unfold fs_inode_blocks. cbv zeta.
  set (nb := fs_nblk (bv_unsigned (di_size dn))) in *.
  (* the direct chunk *)
  assert (Hdir : List.filter (fun a => negb (a =? 0))
                   ((fun k => bv_unsigned (di_addrs dn !!! k))
                      <$> seq 0 FS_NDIRECT)
                 = ((fun k => bv_unsigned (di_addrs dn !!! k))
                      <$> seq 0 (Z.to_nat (Z.min nb (Z.of_nat FS_NDIRECT))))).
  { apply filter_nz_prefix; [lia | |].
    - intros k Hk.
      pose proof (fio_direct P sb dn Hok k ltac:(lia) ltac:(lia)). lia.
    - intros k Hlo Hhi.
      exact (fio_direct_zero P sb dn Hok k Hhi ltac:(lia)). }
  (* the indirect chunk *)
  assert (Hent : List.filter (fun a => negb (a =? 0)) (fs_ind_ents P dn)
                 = ((fun j => fs_ind_ents P dn !!! j)
                      <$> seq 0 (Z.to_nat (nb - Z.of_nat FS_NDIRECT)))).
  { rewrite <- (list_total_seq (fs_ind_ents P dn)) at 1.
    rewrite fs_ind_ents_length.
    apply filter_nz_prefix; [lia | |].
    - intros j Hj.
      pose proof (fio_ent P sb dn Hok j ltac:(lia) ltac:(lia)). lia.
    - intros j Hlo Hhi.
      exact (fio_ent_zero P sb dn Hok j Hhi ltac:(lia)). }
  rewrite Hdir, Hent. f_equal.
  destruct (Z.ltb_spec (Z.of_nat FS_NDIRECT) nb) as [Hgt | Hle].
  - assert (Hib : bv_unsigned (di_addrs dn !!! 12%nat) <> 0).
    { pose proof (fio_ind P sb dn Hok Hgt). lia. }
    rewrite (proj2 (Z.eqb_neq _ _) Hib). reflexivity.
  - rewrite (proj2 (Z.eqb_eq _ _) (fio_ind_zero P sb dn Hok Hle)).
    reflexivity.
Qed.

Lemma fs_ent_blocks_used (P : Z -> list (bv 8)) (sb : fs_sb) :
  fs_sb_ok sb -> fs_inodes_wf P sb = true ->
  fs_ent_blocks P sb = fs_used_blocks P sb.
Proof.
  intros Hsbok HW3. unfold fs_ent_blocks, fs_used_blocks. f_equal.
  apply list_fmap_ext. intros idx x Hx.
  apply lookup_seq in Hx as [-> Hx]. cbv beta zeta.
  destruct (bv_unsigned (di_type (fs_dinode P sb (Z.of_nat (0 + idx))))
            =? 0) eqn:Ety; [reflexivity |].
  apply (fs_inode_ents_blocks P sb _ Hsbok).
  apply (fs_inodes_wf_spec P sb (Z.of_nat (0 + idx)) HW3 ltac:(lia)).
  apply Z.eqb_neq. exact Ety.
Qed.

(* THE DISCHARGE THE IMAGE SIDE NEEDS: the image's own W4 answer IS the
   durable one.  No new computation -- a proof about the two readings, not
   a second sweep. *)
Lemma fs_ent_set_used (P : Z -> list (bv 8)) (sb : fs_sb) :
  fs_sb_ok sb -> fs_inodes_wf P sb = true ->
  fs_ent_set P sb = fs_used_set P sb.
Proof.
  intros Hsbok HW3. unfold fs_ent_set, fs_used_set.
  rewrite (fs_ent_blocks_used P sb Hsbok HW3). reflexivity.
Qed.

(* [InodeInv.bm_covers]' shape at the DURABLE record -- the below-size
   clauses, read through [fs_blk_addr] as [fs_inode_ok_blk] reads them *)
Lemma fs_inode_dok_blk (P : Z -> list (bv 8)) (sb : fs_sb) (dn : dinode)
    (k : nat) :
  fs_inode_dok P sb dn -> (k < FS_MAXFILE)%nat ->
  Z.of_nat k < fs_nblk (bv_unsigned (di_size dn)) ->
  fs_data_start sb <= fs_blk_addr P dn k < sb_size sb.
Proof.
  intros Hd Hk Hnb. unfold fs_blk_addr.
  destruct (Nat.ltb_spec k FS_NDIRECT) as [Hdd | Hdd].
  - exact (fdi_direct P sb dn Hd k Hdd Hnb).
  - apply (fdi_ent P sb dn Hd (k - FS_NDIRECT)%nat).
    + unfold FS_MAXFILE, FS_NDIRECT, FS_NINDIRECT in *. lia.
    + rewrite Nat2Z.inj_sub by exact Hdd. lia.
Qed.

(* ---- THE DURABLE-STATE SHARPENING OF W9's BOUND ----------------------
   [fs_links_wf] records only [count <= nlink] for a non-directory (its
   directory arm is mkfs's own [z = ROOTINO] pin), but the durable
   committed-view reading needs the EQUALITY: a live
   non-directory inode's [nlink] IS its ticket count, which no projection
   of W9 can supply.  A separate additive sweep rather than a
   strengthening of [fs_links_wf], because [fsimg_wf]'s conjunct list is
   frozen (its consumers destruct it) and the equality's only consumer is
   the durable predicate's image discharge.  Directories need no clause
   here (W9's mkfs pin already gives their exact counts), and free
   records carry no durable claim.  Cost shape = W9's: the ticket supply
   is [let]-bound once, one [fs_tick_count] per inum.                    *)
Definition fs_links_eq (P : Z -> list (bv 8)) (sb : fs_sb) : bool :=
  let L := fs_all_tickets P sb in
  List.forallb
    (fun i => let z := Z.of_nat i in
              let dn := fs_dinode P sb z in
              if (bv_unsigned (di_type dn) =? 0)
                 || (bv_unsigned (di_type dn) =? T_DIR_z)
              then true
              else bv_unsigned (di_nlink dn) =? Z.of_nat (fs_tick_count L z))
    (seq 0 (Z.to_nat (sb_ninodes sb))).

Lemma fs_links_eq_at (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  fs_links_eq P sb = true -> 0 <= z < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb z)) <> 0 ->
  bv_unsigned (di_type (fs_dinode P sb z)) <> T_DIR_z ->
  bv_unsigned (di_nlink (fs_dinode P sb z))
  = Z.of_nat (fs_link_count P sb z).
Proof.
  intros H Hz Hty Hnd. unfold fs_links_eq in H. cbv zeta in H.
  pose proof (forallb_seq _ (Z.to_nat (sb_ninodes sb)) (Z.to_nat z) H
                ltac:(lia)) as Hk.
  cbv beta zeta in Hk. rewrite Z2Nat.id in Hk by lia.
  rewrite (proj2 (Z.eqb_neq _ _) Hty), (proj2 (Z.eqb_neq _ _) Hnd) in Hk.
  cbn [orb] in Hk. apply Z.eqb_eq. exact Hk.
Qed.

(* ====================================================================== *)
(*  11d.  CONJUNCT (15) -- NO LIVE NON-DOT RECORD OF THE ROOT NAMES THE    *)
(*        ROOT                                                             *)
(* ====================================================================== *)

(*  WHY THIS CONJUNCT EXISTS.  Two counting disciplines meet at the boot
    composition and they exempt DIFFERENT records.  [fs_rec_ticket] above
    says a record bears a ticket exactly when it is LIVE and does NOT name
    its own home -- a SELF exemption under ANY name.  [FsStateInode.ent_tokenless] exempts only ["."] (under any
    target) and [".."] (when the directory is orphaned or the entry names
    the home).  A root record called "foo" pointing at the root therefore
    owes a link token and pays no ticket, and nothing in [fsimg_wf] rules
    it out -- so [FsState.link_elem]'s validity, which the durable boot
    needs, does not follow from W9 + (13) as they stand.

    THE WEAKEST SWEEP THAT CLOSES IT is the one below: of the root's live
    records, only the two dot NAMES may name the root.  Under it every
    non-tokenless entry of the root has a target other than the root, hence
    is live-and-not-self, hence bears a ticket -- and the entry-to-ticket
    map is injective because [DirView.dir_first] returns ONE record per
    name.  ([FsTree.dir_names_unique], W6, is NOT needed for that
    direction: it is what would be needed for the CONVERSE, tickets <=
    tokens, which nothing asks for.)  [FsDurImg.img_link_incl] is the
    bridge and [FsDurImg.img_link_valid] the theorem.

    It is stated at the ROOT ALONE and that is not a shortcut: W9's
    directory arm already forces every live directory of the image to BE
    the root ([fs_links_wf_at]'s [z = ROOTINO]), so every other node's
    entry map is empty ([FsDurImg.img_dir_entries_empty]) and has nothing
    to pay for.  COST: one [O(nrec)] pass over the root's records -- the
    same records W6/W8 already read, and the only sweep in this file that
    touches exactly one directory.                                        *)

(*  NESTED [if], NOT [||], AND THAT IS THE WHOLE COST.  [orb] is a
    FUNCTION, so [vm_compute] evaluates BOTH arguments: an
    [... || bool_decide (name = DOT) || bool_decide (name = DOTDOT)]
    spelling reads (twice) the fourteen name bytes of every record, and
    each [DirView.file_byte] rebuilds the record's whole 1024-byte block
    -- 44.8 s at the literal image.  A nested [if] is a MATCH, so the name
    is read once and only for a record that actually names the root (two
    of them): 3.4 s.  The [let i] shares the inum halfword between the
    liveness test and the self test for the same reason.                  *)
Definition fs_root_no_self (P : Z -> list (bv 8)) (sb : fs_sb) : bool :=
  let dn := fs_dinode P sb ROOTINO in
  let data := fs_data_of P dn in
  List.forallb
    (fun k => let i := dir_inum data k in
              if bool_decide (i = bv_0 16) then true
              else if bv_unsigned i =? ROOTINO
                   then (let s := dir_bname data k in
                         if bool_decide (s = DOT) then true
                         else bool_decide (s = DOTDOT))
                   else true)
    (seq 0 (dir_nrec (bv_unsigned (di_size dn)))).

Lemma fs_root_no_self_at (P : Z -> list (bv 8)) (sb : fs_sb) (k : nat) :
  fs_root_no_self P sb = true ->
  (k < dir_nrec (bv_unsigned (di_size (fs_dinode P sb ROOTINO))))%nat ->
  dir_live (fs_data_of P (fs_dinode P sb ROOTINO)) k ->
  bv_unsigned (dir_inum (fs_data_of P (fs_dinode P sb ROOTINO)) k) = ROOTINO ->
  dir_bname (fs_data_of P (fs_dinode P sb ROOTINO)) k = DOT
  \/ dir_bname (fs_data_of P (fs_dinode P sb ROOTINO)) k = DOTDOT.
Proof.
  intros H Hk Hlv Hin.
  unfold fs_root_no_self in H. cbv zeta in H.
  pose proof (forallb_seq _ _ k H Hk) as Hq. cbv beta zeta in Hq.
  rewrite (bool_decide_eq_false_2 _ Hlv) in Hq.
  rewrite (proj2 (Z.eqb_eq _ _) Hin) in Hq.
  destruct (decide (dir_bname (fs_data_of P (fs_dinode P sb ROOTINO)) k = DOT))
    as [Hd | Hd]; [by left |].
  right.
  rewrite (bool_decide_eq_false_2 _ Hd) in Hq.
  exact (proj1 (bool_decide_eq_true _) Hq).
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
  fs_root_wf P sb &&                                      (* W7 *)
  fs_dots_all P sb &&                                     (* W8 *)
  fs_links_wf P sb.                                       (* W9 *)

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
  assert (Hu : match fs_used_set P sb with
               | None => false
               | Some u => fs_bitmap_wf P sb u
               end = true) by tauto.
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

(* W8, at [DirView.dir_dots_ix] outright *)
Lemma fsimg_wf_dots (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fsimg_wf P sb = true -> 0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) = T_DIR_z ->
  dir_dots_ix i (fs_dinode P sb i) (fs_data_of P (fs_dinode P sb i)).
Proof.
  unfold fsimg_wf. rewrite !andb_true_iff. intros H Hi Hty.
  apply (fs_dots_all_spec P sb i); [tauto | exact Hi | exact Hty].
Qed.

(* W4 REINDEXED, at one live inum: [InodeInv.blkmap_wf]'s injectivity
   clause, from the global [NoDup] and nothing new *)
Lemma fsimg_wf_slot_inj (P : Z -> list (bv 8)) (sb : fs_sb) (i : Z) :
  fsimg_wf P sb = true -> 0 <= i < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb i)) <> 0 ->
  fs_slot_inj P (fs_dinode P sb i).
Proof.
  intros H Hi Hnz.
  destruct (fsimg_wf_used P sb H) as (u & _ & Hnd & _).
  apply (fs_used_nodup_slot_inj P sb i Hnd); [| exact Hi | exact Hnz].
  revert H. unfold fsimg_wf. rewrite !andb_true_iff. intros H. tauto.
Qed.

(* W6, as the raw boolean: [fs_all_tickets_range] wants the SWEEP, not one
   inum's reading, because it quantifies over the tickets and not over the
   inums. *)
Lemma fsimg_wf_dirs (P : Z -> list (bv 8)) (sb : fs_sb) :
  fsimg_wf P sb = true -> fs_dirs_wf P sb = true.
Proof.
  unfold fsimg_wf. rewrite !andb_true_iff. intros H. tauto.
Qed.

Lemma fsimg_wf_links (P : Z -> list (bv 8)) (sb : fs_sb) :
  fsimg_wf P sb = true -> fs_links_wf P sb = true.
Proof.
  unfold fsimg_wf. rewrite !andb_true_iff. intros H. tauto.
Qed.

(* ---- W9's THREE READINGS, at EVERY [z] (no range side condition) ------
   The stocking client asks the counts of the whole inode REGION, which is
   [16 * nib] records wide while W9 sweeps [ninodes]; off the sweep's range
   the count is zero by [fs_link_count_out], so each reading extends for
   free.  That is what keeps [IcacheBoot.ireg_alloc]'s premises stated over
   [region_inums] rather than over two ranges. *)

(* [z]'s authority covers the fragments the image hands out at it *)
Lemma fsimg_wf_link_le (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  fsimg_wf P sb = true ->
  Z.of_nat (fs_link_count P sb z)
    <= bv_unsigned (di_nlink (fs_dinode P sb z)).
Proof.
  intros H.
  destruct (decide (0 < z < sb_ninodes sb)) as [Hin | Hout].
  - exact (proj1 (fs_links_wf_at P sb z (fsimg_wf_links P sb H)
                    ltac:(lia))).
  - rewrite (fs_link_count_out P sb z (fsimg_wf_dirs P sb H) Hout).
    cbn [Z.of_nat].
    pose proof (proj1 (bv_unsigned_in_range _ (di_nlink (fs_dinode P sb z)))).
    lia.
Qed.

(* no record of a mkfs image names a DIRECTORY *)
Lemma fsimg_wf_link_dir (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  fsimg_wf P sb = true ->
  bv_unsigned (di_type (fs_dinode P sb z)) = T_DIR_z ->
  fs_link_count P sb z = 0%nat.
Proof.
  intros H Hty.
  destruct (decide (0 < z < sb_ninodes sb)) as [Hin | Hout].
  - exact (proj1 (proj2 (fs_links_wf_at P sb z (fsimg_wf_links P sb H)
                           ltac:(lia)) Hty)).
  - exact (fs_link_count_out P sb z (fsimg_wf_dirs P sb H) Hout).
Qed.

(* a live image directory has EXACTLY one link -- mkfs's own [nlink = 1],
   and the region's keep-alive token needs [0 < nlink]. *)
Lemma fsimg_wf_dir_nlink (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  fsimg_wf P sb = true -> 0 <= z < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb z)) = T_DIR_z ->
  bv_unsigned (di_nlink (fs_dinode P sb z)) = 1.
Proof.
  intros H Hz Hty.
  exact (proj1 (proj2 (proj2 (fs_links_wf_at P sb z
                                (fsimg_wf_links P sb H) Hz) Hty))).
Qed.

(* THE ROOT EXCLUSION: mkfs lays down exactly one directory and it is the
   root, so no image directory has a parent entry to account for. *)
Lemma fsimg_wf_dir_root (P : Z -> list (bv 8)) (sb : fs_sb) (z : Z) :
  fsimg_wf P sb = true -> 0 <= z < sb_ninodes sb ->
  bv_unsigned (di_type (fs_dinode P sb z)) = T_DIR_z -> z = ROOTINO.
Proof.
  intros H Hz Hty.
  exact (proj2 (proj2 (proj2 (fs_links_wf_at P sb z
                                (fsimg_wf_links P sb H) Hz) Hty))).
Qed.

(* ...and the ROOT's own pair, which is what the region's keep-alive token
   ([InodeRegion.ireg_keep]) is minted against at [ireg_root]: the count is
   zero and the link count is one, so the one parked token is covered.  W7
   supplies the type and W1 the range, so this costs no new image fact. *)
Lemma fsimg_wf_root_link (P : Z -> list (bv 8)) (sb : fs_sb) :
  fsimg_wf P sb = true ->
  fs_link_count P sb ROOTINO = 0%nat
  /\ bv_unsigned (di_nlink (fs_dinode P sb ROOTINO)) = 1.
Proof.
  intros H.
  pose proof (fs_root_wf_type P sb (fsimg_wf_root P sb H)) as Hty.
  pose proof (sbo_ninodes sb (fsimg_wf_sb P sb H)) as Hn.
  split.
  - exact (fsimg_wf_link_dir P sb ROOTINO H Hty).
  - apply (fsimg_wf_dir_nlink P sb ROOTINO H);
      [unfold ROOTINO in *; lia | exact Hty].
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
