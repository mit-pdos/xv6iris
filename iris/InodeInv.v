(* InodeInv.v -- struct inode's geometry, the pure model of a file's block
   map, and the two ownership bundles fs.c's proofs are stated over.
   Design: claude-notes/design/fs-inode.md.

   ---- THE GEOMETRY IS READ OFF THE CODE, NOT OFF THE HEADER ----------

   Every offset below is pinned by an instruction in the tracked image
   (kernel-rocq/KernelInstrs.v), never inferred from the C declaration:

     lw a0,0(a0)     the balloc(ip->dev) argument     ==>  dev   at +0
     lw s1,80(s3)    with s3 = ip + 4*bn              ==>  addrs at +80
     lw s1,128(a0)   ip->addrs[NDIRECT]               ==>  80 + 4*12 = 128

   The subtlety that makes reading the header wrong is an ALIGNMENT HOLE.
   The struct is

     +0   dev uint      +4  inum uint     +8  ref int
     +16  lock  struct sleeplock (48 bytes)
     +64  valid int     +68 type short    +70 major short
     +72  minor short   +74 nlink short   +76 size uint
     +80  addrs[NDIRECT+1]   (13 words, 52 bytes)
     sizeof = 132, aligned to 136

   ref ends at +12, but struct sleeplock contains a char * and is therefore
   8-ALIGNED, so lock starts at +16, not at +12.  The resulting 4-byte hole
   displaces every field after it.  Transcribing the struct text without the
   hole puts addrs at 76 and every lw in the proof then misses by four --
   and the two instructions above are what rule that out: the indexed load
   uses displacement 80, and the NDIRECT load uses 128 = 80 + 4*12, which
   is consistent only with addrs at 80.

   addrs[j] therefore sits at +80 + 4*j, and that is what the code's
   slli 0x20 / srli 0x1e pair computes: zero-extend bn to 64 bits, then
   shift left by two.

   ---- THE TWO RESOURCES ---------------------------------------------

   [inode_map] is the block MAP -- the thirteen addrs cells plus, when the
   indirect entry is nonzero, the indirect block's own logical content as
   an [fsblock] at the byte ENCODING of the entry list ([BlockWords.v]'s
   [ind_bytes]).  [inode_blocks] is the file's DATA -- one [fsblock] per
   allocated file index.  They are split because bmap needs only the first
   and a whole-file operation needs both.  ip->dev rides separately as a
   fractional cell ([i_dev ip |->4{dq} dev]); bmap only reads it. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import RiscvExtras.
Require Import InstrBytes.
Require Import ByteBuf.
Require Import DiskPtsto.
Require Import FsBlocks.
Require Import LogInv.
Require Import FsCrash.   (* [BSIZE]: the block size [bm_covers] divides by *)
Require Import BlockWords.
Require Import DinodeEnc.
Require Export IcacheRef.   (* the in-core scalar fields + the reference *)
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
From Kernel Require KernelSyms.

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  The fs.h constants                                                    *)
(* ===================================================================== *)

Definition NDIRECT  : nat := 12%nat.
Definition NINDIRECT : nat := 256%nat.        (* BSIZE / sizeof(uint) *)
Definition MAXFILE  : nat := 268%nat.         (* NDIRECT + NINDIRECT  *)

Lemma maxfile_split : MAXFILE = (NDIRECT + NINDIRECT)%nat.
Proof. reflexivity. Qed.

(* ===================================================================== *)
(*  struct inode geometry                                                 *)
(* ===================================================================== *)

(* The scalar fields, in the 12-bit displacement form the lw/sw/lh that
   reach them encode -- the [BcacheInv.buf_lock] / [ProcGeom.p_pid] idiom.

   The five IN-CORE ones ([i_dev], [i_inum], [i_ref], [i_lock], [i_valid])
   are re-exported from [IcacheRef.v], which is underneath the file table
   and hence underneath this file; see that file's header.  The ones below
   are the DINODE MIRROR, and belong with the encoding they mirror. *)
Definition i_type  (ip : mword 64) : mword 64 :=
  add_vec ip (sign_extend' 64 (mword_of_int 68 : mword 12)).
Definition i_major (ip : mword 64) : mword 64 :=
  add_vec ip (sign_extend' 64 (mword_of_int 70 : mword 12)).
Definition i_minor (ip : mword 64) : mword 64 :=
  add_vec ip (sign_extend' 64 (mword_of_int 72 : mword 12)).
Definition i_nlink (ip : mword 64) : mword 64 :=
  add_vec ip (sign_extend' 64 (mword_of_int 74 : mword 12)).
Definition i_size  (ip : mword 64) : mword 64 :=
  add_vec ip (sign_extend' 64 (mword_of_int 76 : mword 12)).

(* ip->addrs[j], at +80 + 4*j.  Stated in the CANONICAL whole-offset form;
   the two shapes the code actually computes are the bridges below. *)
Definition i_addr (ip : mword 64) (j : nat) : mword 64 :=
  add_vec ip (mword_of_int (80 + 4 * Z.of_nat j)).

Local Lemma iv_addv_assoc (a b c : mword 64) :
  add_vec (add_vec a b) c = add_vec a (add_vec b c).
Proof.
  unfold add_vec, Operators_mwords.word_binop, Operators_mwords.with_word',
    SailStdpp.Values.with_word, to_word, get_word, MachineWord.MachineWord.add.
  apply bv_eq. rewrite !bv_add_unsigned.
  unfold bv_wrap. rewrite Zplus_mod_idemp_l Zplus_mod_idemp_r Z.add_assoc.
  reflexivity.
Qed.

(* [avi_mword] restated in the raw [add_vec ... (mword_of_int ...)] shape:
   [add_vec_int] is definitionally that, but ssreflect matches syntactically. *)
Local Lemma iv_moi_add (x y : Z) :
  add_vec (mword_of_int x : mword 64) (mword_of_int y) = mword_of_int (x + y).
Proof. exact (avi_mword x y). Qed.

(* the indexed form: s3 = ip + 4*bn, then lw s1,80(s3) *)
Lemma i_addr_indexed (ip : mword 64) (j : nat) :
  i_addr ip j
  = add_vec (add_vec ip (mword_of_int (4 * Z.of_nat j)))
            (sign_extend' 64 (mword_of_int 80 : mword 12)).
Proof.
  assert (H80 : (sign_extend' 64 (mword_of_int 80 : mword 12) : mword 64)
                = mword_of_int 80)
    by (apply bv_eq; vm_compute; reflexivity).
  rewrite H80 iv_addv_assoc iv_moi_add.
  unfold i_addr.
  assert (Hc : 80 + 4 * Z.of_nat j = 4 * Z.of_nat j + 80) by lia.
  rewrite Hc. reflexivity.
Qed.

(* the literal form: lw s1,128(a0) / sw a0,128(s2) reach addrs[NDIRECT] *)
Lemma i_addr_ndirect (ip : mword 64) :
  i_addr ip NDIRECT = add_vec ip (sign_extend' 64 (mword_of_int 128 : mword 12)).
Proof.
  assert (Hx : (mword_of_int (80 + 4 * Z.of_nat NDIRECT) : mword 64)
               = sign_extend' 64 (mword_of_int 128 : mword 12))
    by (apply bv_eq; vm_compute; reflexivity).
  unfold i_addr. rewrite Hx. reflexivity.
Qed.

(* [ip->addrs[j]] sits at [ip->addrs + 4*j] -- the form the memmove SOURCE
   bridge below needs, so a run of cells can be re-anchored at one base.
   The [Z] step is a separate mword-FREE lemma because [lia] answers
   "Cannot find witness" with an [mword] merely in context
   (claude-notes/durable-notes.md). *)
Local Lemma ia_off_arith (j : nat) :
  80 + 4 * Z.of_nat j = 80 + 4 * Z.of_nat 0%nat + Z.of_nat (4 * j)%nat.
Proof. rewrite Nat2Z.inj_mul. simpl (Z.of_nat 4). simpl (Z.of_nat 0). lia. Qed.

Lemma i_addr_from_0 (ip : mword 64) (j : nat) :
  i_addr ip j = pa_add (i_addr ip 0) (4 * j)%nat.
Proof.
  rewrite /pa_add /add_vec_int /i_addr.
  rewrite iv_addv_assoc iv_moi_add (ia_off_arith j). reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(*  THE ONE SUPERBLOCK FIELD THE INODE LAYER READS                         *)
(*                                                                          *)
(*  [sb.inodestart] is at [sb + 24] -- the [lw a1,<off>(a1)] off the        *)
(*  [auipc a1,0x1d] in iupdate (+0x14) and in ilock (+0x3e) both resolve to *)
(*  0x80020868, i.e. KernelSyms.sb + 0x18.  It rides through every contract *)
(*  as a plain FRACTIONAL cell, the way SpecInitlog.v takes [sb + 20] for   *)
(*  logstart: read once, handed straight back.  There is deliberately no    *)
(*  superblock abstraction for one field.                                   *)
(*                                                                          *)
(*  It lives HERE rather than in a Spec file because iupdate and ilock both *)
(*  state their contracts on it and a Spec file must not require another    *)
(*  function's Spec (the [file_byte] relocation, same rule).                *)
(* ---------------------------------------------------------------------- *)
Definition sb_inodestart : mword 64 :=
  pa_add (mword_of_int KernelSyms.sb : mword 64) 24.

(* ===================================================================== *)
(*  The pure model: a file's block map                                    *)
(* ===================================================================== *)

Record blkmap := MkBlkmap {
  bm_dir : list (bv 32);   (* the NDIRECT direct entries; 0 = unallocated *)
  bm_ind : bv 32;          (* the indirect block itself;  0 = none        *)
  bm_ent : list (bv 32);   (* the NINDIRECT entries of that block         *)
}.

(* file index -> disk block.  Total: an out-of-range index reads the
   [Inhabited] default (all zeros), i.e. "unallocated", which is exactly
   what makes [bm_slot] below able to override index MAXFILE. *)
Definition blkmap_get (bm : blkmap) (i : nat) : bv 32 :=
  if decide ((i < NDIRECT)%nat)
  then bm_dir bm !!! i
  else bm_ent bm !!! (i - NDIRECT)%nat.

(* ONE indexing of every block the inode names: the MAXFILE file indices
   plus the indirect block itself at the extra index MAXFILE.  Injectivity
   and the coverage clause are then single quantified statements rather
   than a data/indirect cross-product; the two spellings a caller normally
   wants are the corollaries below. *)
Definition bm_slot (bm : blkmap) (i : nat) : bv 32 :=
  if decide (i = MAXFILE) then bm_ind bm else blkmap_get bm i.

Lemma bm_slot_lt (bm : blkmap) (i : nat) :
  (i < MAXFILE)%nat -> bm_slot bm i = blkmap_get bm i.
Proof.
  intros Hi. unfold bm_slot.
  destruct (decide (i = MAXFILE)) as [->|_]; [lia|reflexivity].
Qed.

Lemma bm_slot_top (bm : blkmap) : bm_slot bm MAXFILE = bm_ind bm.
Proof.
  unfold bm_slot. destruct (decide (MAXFILE = MAXFILE)); [reflexivity|congruence].
Qed.

Definition blkmap_wf (cov : gset Z) (logstart : Z) (bm : blkmap) : Prop :=
  (* the two lengths -- without them the addrs big-op and the indirect
     encoding do not line up with the cells *)
  length (bm_dir bm) = NDIRECT
  /\ length (bm_ent bm) = NINDIRECT
  (* NO INDIRECT BLOCK => NO ENTRIES.  Without this the model lets an inode
     with addrs[NDIRECT] = 0 still carry arbitrary indirect entries, and
     bmap's "allocate the indirect block" arm becomes UNPROVABLE: balloc
     hands over a block whose content is all zeroes, so the only entry list
     the new [ind_res] can be formed at is the all-zero one -- and bmap's
     postcondition ("bm' agrees with bm at every index but bn") then demands
     that the OLD entry list was all-zero too.  It is also true of every
     inode the kernel can produce: ialloc zeroes addrs[], and itrunc zeroes
     the indirect entry only after zeroing the block. *)
  /\ (bv_unsigned (bm_ind bm) = 0 -> bm_ent bm = replicate NINDIRECT (bv_0 32))
  (* every block the inode names is a covered HOME block: the premise
     bread and log_write both demand *)
  /\ (forall i : nat, (i <= MAXFILE)%nat -> bv_unsigned (bm_slot bm i) <> 0 ->
        bv_unsigned (bm_slot bm i) ∈ cov
        /\ ~ (bv_unsigned (bm_slot bm i) ∈ log_region_set logstart))
  (* INJECTIVITY on the nonzero entries, the indirect block included: two
     slots naming one disk block would make the bundles below claim two
     halves of one key, which is exactly the fact balloc's freshness has
     to re-establish at every insertion. *)
  /\ (forall i j : nat, (i <= MAXFILE)%nat -> (j <= MAXFILE)%nat ->
        bv_unsigned (bm_slot bm i) <> 0 ->
        bm_slot bm i = bm_slot bm j -> i = j).

(* ---- the corollaries a caller normally wants ------------------------ *)

Lemma blkmap_wf_dir_len cov ls bm : blkmap_wf cov ls bm -> length (bm_dir bm) = NDIRECT.
Proof. intros (H & _ & _ & _ & _). exact H. Qed.

Lemma blkmap_wf_ent_len cov ls bm : blkmap_wf cov ls bm -> length (bm_ent bm) = NINDIRECT.
Proof. intros (_ & H & _ & _ & _). exact H. Qed.

Lemma blkmap_wf_no_ind cov ls bm :
  blkmap_wf cov ls bm -> bv_unsigned (bm_ind bm) = 0 ->
  bm_ent bm = replicate NINDIRECT (bv_0 32).
Proof. intros (_ & _ & H & _ & _). exact H. Qed.

Lemma blkmap_wf_get_cov cov ls bm (i : nat) :
  blkmap_wf cov ls bm -> (i < MAXFILE)%nat -> bv_unsigned (blkmap_get bm i) <> 0 ->
  bv_unsigned (blkmap_get bm i) ∈ cov
  /\ ~ (bv_unsigned (blkmap_get bm i) ∈ log_region_set ls).
Proof.
  intros (_ & _ & _ & Hcov & _) Hi Hnz.
  specialize (Hcov i ltac:(lia)). rewrite (bm_slot_lt bm i Hi) in Hcov.
  exact (Hcov Hnz).
Qed.

Lemma blkmap_wf_ind_cov cov ls bm :
  blkmap_wf cov ls bm -> bv_unsigned (bm_ind bm) <> 0 ->
  bv_unsigned (bm_ind bm) ∈ cov
  /\ ~ (bv_unsigned (bm_ind bm) ∈ log_region_set ls).
Proof.
  intros (_ & _ & _ & Hcov & _) Hnz.
  specialize (Hcov MAXFILE ltac:(lia)). rewrite bm_slot_top in Hcov.
  exact (Hcov Hnz).
Qed.

Lemma blkmap_wf_get_inj cov ls bm (i j : nat) :
  blkmap_wf cov ls bm -> (i < MAXFILE)%nat -> (j < MAXFILE)%nat ->
  bv_unsigned (blkmap_get bm i) <> 0 -> blkmap_get bm i = blkmap_get bm j -> i = j.
Proof.
  intros (_ & _ & _ & _ & Hinj) Hi Hj Hnz Heq.
  apply (Hinj i j ltac:(lia) ltac:(lia)).
  - rewrite (bm_slot_lt bm i Hi). exact Hnz.
  - rewrite (bm_slot_lt bm i Hi) (bm_slot_lt bm j Hj). exact Heq.
Qed.

(* the indirect block is none of the file's data blocks *)
Lemma blkmap_wf_ind_ne cov ls bm (i : nat) :
  blkmap_wf cov ls bm -> (i < MAXFILE)%nat -> bv_unsigned (blkmap_get bm i) <> 0 ->
  bm_ind bm <> blkmap_get bm i.
Proof.
  intros (_ & _ & _ & _ & Hinj) Hi Hnz Heq.
  assert (Hij : i = MAXFILE).
  { apply (Hinj i MAXFILE ltac:(lia) ltac:(lia)).
    - rewrite (bm_slot_lt bm i Hi). exact Hnz.
    - rewrite (bm_slot_lt bm i Hi) bm_slot_top. exact (eq_sym Heq). }
  lia.
Qed.

(* An ALLOCATED indirect ENTRY forces the indirect BLOCK to exist.  This is
   the "no indirect block => no entries" conjunct read backwards, and it is
   what saves a no-allocation caller from having to carry a second premise:
   [bv_unsigned (blkmap_get bm i) <> 0] at an indirect index ALREADY says
   [bm_ind bm <> 0], so bmap's no-alloc contract needs only the one. *)
Lemma blkmap_wf_ind_nz cov ls bm (i : nat) :
  blkmap_wf cov ls bm -> (NDIRECT <= i)%nat -> (i < MAXFILE)%nat ->
  bv_unsigned (blkmap_get bm i) <> 0 -> bv_unsigned (bm_ind bm) <> 0.
Proof.
  intros Hwf Hge Hlt Hnz Hiz.
  apply Hnz. unfold blkmap_get.
  case_decide; [lia|].
  rewrite (blkmap_wf_no_ind cov ls bm Hwf Hiz).
  rewrite lookup_total_replicate_2; [reflexivity|].
  unfold MAXFILE, NDIRECT, NINDIRECT in *; lia.
Qed.

(* ---- reading blkmap_get off the two components ------------------------ *)

Lemma blkmap_get_dir (bm : blkmap) (i : nat) :
  (i < NDIRECT)%nat -> blkmap_get bm i = bm_dir bm !!! i.
Proof.
  intros Hi. unfold blkmap_get. destruct (decide ((i < NDIRECT)%nat)); [reflexivity|lia].
Qed.

Lemma blkmap_get_ent (bm : blkmap) (i : nat) :
  (NDIRECT <= i)%nat -> blkmap_get bm i = bm_ent bm !!! (i - NDIRECT)%nat.
Proof.
  intros Hi. unfold blkmap_get. destruct (decide ((i < NDIRECT)%nat)); [lia|reflexivity].
Qed.

(* ===================================================================== *)
(*  THE COVERAGE INVARIANT: every file block below the SIZE is allocated  *)
(* ===================================================================== *)

(* [bm_covers bm sz] is the missing fact that makes a READ never allocate.
   readi runs OUTSIDE a transaction (fileread has no begin_op/end_op), so an
   allocating bmap would hit panic("log_write outside of trans"); it never
   happens because writei allocates as it extends, but nothing in the block
   map itself said so.  This is that statement, and the whole point is that
   it is preserved by everything below (see [bm_covers_keep]) and consumed
   by exactly one lemma ([bm_covers_off]).

   The bound is stated on the BYTE offset of the block's first byte, which
   is the shape both producers and consumers have: a file of size [sz]
   occupies file blocks 0 .. (sz-1)/BSIZE, i.e. exactly those [i] with
   [i * BSIZE < sz].  Design: claude-notes/design/fs-inode.md, "readi, and
   why it forced a no-alloc bmap". *)
Definition bm_covers (bm : blkmap) (sz : Z) : Prop :=
  forall i : nat, (i < MAXFILE)%nat -> Z.of_nat i * Z.of_nat BSIZE < sz ->
    bv_unsigned (blkmap_get bm i) <> 0.

(* the direct reading: the block-index form the design doc states *)
Lemma bm_covers_get (bm : blkmap) (sz : Z) (i : nat) :
  bm_covers bm sz -> (i < MAXFILE)%nat ->
  Z.of_nat i * Z.of_nat BSIZE < sz ->
  bv_unsigned (blkmap_get bm i) <> 0.
Proof. intros Hc Hi Hlt. exact (Hc i Hi Hlt). Qed.

(* THE FORM readi ACTUALLY USES.  Its loop holds a byte offset [o] with
   [off <= o < off + n <= size] and calls bmap at [o / BSIZE]; both the
   index bound and the nonzero conclusion come out in one step.  Keeping the
   division inside this lemma is what stops every caller from re-deriving
   [o / BSIZE * BSIZE <= o]. *)
Lemma bm_covers_off (bm : blkmap) (sz o : Z) :
  bm_covers bm sz -> 0 <= o -> o < sz ->
  o < Z.of_nat MAXFILE * Z.of_nat BSIZE ->
  (Z.to_nat (o / Z.of_nat BSIZE) < MAXFILE)%nat
  /\ bv_unsigned (blkmap_get bm (Z.to_nat (o / Z.of_nat BSIZE))) <> 0.
Proof.
  intros Hc Ho0 Hosz Homax.
  assert (HB : Z.of_nat BSIZE = 1024) by (vm_compute; reflexivity).
  assert (Hdiv0 : 0 <= o / Z.of_nat BSIZE)
    by (apply Z.div_pos; [exact Ho0 | rewrite HB; lia]).
  assert (Hdivlt : o / Z.of_nat BSIZE < Z.of_nat MAXFILE).
  { apply Z.div_lt_upper_bound;
      [rewrite HB; lia | rewrite Z.mul_comm; exact Homax]. }
  assert (Hidx : (Z.to_nat (o / Z.of_nat BSIZE) < MAXFILE)%nat)
    by (unfold MAXFILE in *; lia).
  split; [exact Hidx|].
  apply (Hc _ Hidx).
  rewrite (Z2Nat.id _ Hdiv0).
  assert (Hle : o / Z.of_nat BSIZE * Z.of_nat BSIZE <= o).
  { rewrite Z.mul_comm. apply Z.mul_div_le. rewrite HB; lia. }
  lia.
Qed.

(* the file only ever gets SHORTER at a reader: readi clamps n to the size *)
Lemma bm_covers_mono (bm : blkmap) (sz sz' : Z) :
  bm_covers bm sz -> sz' <= sz -> bm_covers bm sz'.
Proof. intros Hc Hle i Hi Hlt. exact (Hc i Hi ltac:(lia)). Qed.

Lemma bm_covers_nonpos (bm : blkmap) (sz : Z) : sz <= 0 -> bm_covers bm sz.
Proof.
  intros Hsz i Hi Hlt. exfalso.
  assert (0 <= Z.of_nat i * Z.of_nat BSIZE)
    by (apply Z.mul_nonneg_nonneg; apply Nat2Z.is_nonneg).
  lia.
Qed.

(* COVERAGE SURVIVES ANY MAP CHANGE THAT NEVER UN-ALLOCATES -- which is
   precisely the clause bmap's own postcondition already carries, so a
   caller can thread [bm_covers] straight across a bmap call. *)
Lemma bm_covers_keep (bm bm' : blkmap) (sz : Z) :
  (forall i : nat, (i < MAXFILE)%nat -> bv_unsigned (blkmap_get bm i) <> 0 ->
     blkmap_get bm' i = blkmap_get bm i) ->
  bm_covers bm sz -> bm_covers bm' sz.
Proof.
  intros Hkeep Hc i Hi Hlt.
  rewrite (Hkeep i Hi (Hc i Hi Hlt)). exact (Hc i Hi Hlt).
Qed.

(* ===================================================================== *)
(*  THE FLAT FILE-BYTE VIEW, AND HOLES READ AS ZEROS                      *)
(* ===================================================================== *)

(* [inode_blocks γfs bm data] is indexed by file BLOCK, but every whole-file
   operation is about a byte RANGE that straddles blocks.  Stating an effect
   per block would force every caller to redo the straddle arithmetic, so the
   flat view is defined ONCE, here beside [inode_blocks] itself, and both
   writei's range clause and readi's delivered-bytes clause are stated on it.

   It lives in InodeInv.v rather than in either function's spec file because a
   Spec file must not depend on another function's Spec: [SpecReadi.v] used to
   require [SpecWritei.v] for this definition alone, which coupled readi's
   contract to writei's. *)
Definition file_byte (data : nat -> list (bv 8)) (k : nat) : bv 8 :=
  data (k `div` BSIZE)%nat !!! (k `mod` BSIZE)%nat.

(* Two [data]s that agree block by block agree byte by byte -- the step every
   "nothing else moved" argument takes. *)
Lemma file_byte_block (data data' : nat -> list (bv 8)) (k : nat) :
  data' (k `div` BSIZE)%nat = data (k `div` BSIZE)%nat ->
  file_byte data' k = file_byte data k.
Proof. intros H. rewrite /file_byte H. reflexivity. Qed.

(* A HOLE READS AS ZEROS.  [inode_blocks] leaves [data i] unconstrained at an
   UNALLOCATED index [i], and bmap deposits a freshly allocated block into the
   bundle at [replicate BSIZE 0] -- so without a normalisation of the
   unallocated indices, "the bytes outside my range are the bytes that were
   there" is FALSE the moment writei extends the file.  This is that
   normalisation, and it is also the xv6 file semantics.  It is threaded in
   and back out by writei; it belongs next to [inode_blocks], which is why it
   is here rather than in SpecWritei.v. *)
Definition blk_holes_zero (bm : blkmap) (data : nat -> list (bv 8)) : Prop :=
  forall i : nat, (i < MAXFILE)%nat -> bv_unsigned (blkmap_get bm i) = 0 ->
    data i = replicate BSIZE (bv_0 8).

(* ===================================================================== *)
(*  A BLOCK IS BSIZE BYTES -- itrunc's second owed premise (design §6(ii),
    landed by §13.12(b))                                                  *)
(* ===================================================================== *)

(* [bfree] hands the freed block back to [BitmapInv.free_blk], whose
   [length bs = BSIZE] conjunct is the obligation; [inode_blocks] names a
   block's contents but says nothing about their length, and
   [FsBlocks.fsblock] is a bare ghost_map half with no length side
   condition anywhere above it.  So the fact is not derivable and must be
   CARRIED.

   It cannot be carried as a caller's premise either: under SpecIlock v2
   the record and its [data] are OUTPUTS, existentially bound inside
   [IcacheEscrow.ic_loaded], so iput -- the first function to call itrunc
   on a checked-out inode -- cannot name the [data] it would quantify
   over.  The place it has to live is beside [InodeLock.inode_ok], the
   pure record ilock mints and every parked entry holds, which is where
   §13.12(b) put it.  It lives HERE rather than in IcacheInv.v (its first
   home) because [InodeLock.v] and [IcacheInv.v] are siblings and only
   [inode_ok]'s own file may name it.

   Note the BOUND.  [SpecItrunc.v] states its premise for every [i : nat];
   no holder of ilock's bundle can supply that, because both
   [inode_blocks] and [blk_holes_zero] stop at MAXFILE.  [i < MAXFILE] is
   all itrunc's loops touch.

   The design note argues the BETTER home is [fsblock] itself (the length
   is a block-layer truth, and [BitmapInv.free_blk] already pairs the two
   by hand); that change is recorded there and left unmade.               *)
Definition inode_sized (data : nat -> list (bv 8)) : Prop :=
  forall i : nat, (i < MAXFILE)%nat -> length (data i) = BSIZE.

(* itrunc's own output, and ialloc's fresh inode *)
Lemma inode_sized_zero : inode_sized (fun _ => replicate BSIZE (bv_0 8)).
Proof. intros i _. apply length_replicate. Qed.

(* bmap's deposit and writei's block update are both this *)
Lemma inode_sized_insert (data : nat -> list (bv 8)) (i : nat) (bs : list (bv 8)) :
  inode_sized data -> length bs = BSIZE ->
  inode_sized (<[i := bs]> data).
Proof.
  intros Hs Hbs j Hj.
  destruct (decide (j = i)) as [->|Hne].
  - rewrite fn_lookup_insert. exact Hbs.
  - rewrite fn_lookup_insert_ne; [|exact (not_eq_sym Hne)]. exact (Hs j Hj).
Qed.

(* a HOLE is sized for free, so a producer only ever has to think about the
   ALLOCATED indices ([blk_holes_zero] is already an [inode_ok] conjunct) *)
Lemma inode_sized_of_alloc (bm : blkmap) (data : nat -> list (bv 8)) :
  blk_holes_zero bm data ->
  (forall i : nat, (i < MAXFILE)%nat -> bv_unsigned (blkmap_get bm i) <> 0 ->
     length (data i) = BSIZE) ->
  inode_sized data.
Proof.
  intros Hholes Halloc i Hi.
  destruct (decide (bv_unsigned (blkmap_get bm i) = 0)) as [Hz|Hnz].
  - rewrite (Hholes i Hi Hz). apply length_replicate.
  - exact (Halloc i Hi Hnz).
Qed.

(* ===================================================================== *)
(*  THE EMPTIED MAP: what itrunc leaves behind                            *)
(* ===================================================================== *)

(* Every direct entry, every indirect entry, and the indirect block itself
   at zero.  itrunc's postcondition is stated at this ONE closed value
   rather than at "some map whose slots are all zero", because the caller
   that matters (iput) then needs no reasoning at all to see that the inode
   names no blocks: the resources below collapse definitionally. *)
Definition bm_empty : blkmap :=
  MkBlkmap (replicate NDIRECT (bv_0 32)) (bv_0 32)
           (replicate NINDIRECT (bv_0 32)).

Lemma bm_empty_get (i : nat) : blkmap_get bm_empty i = bv_0 32.
Proof.
  rewrite /blkmap_get /bm_empty. cbn [bm_dir bm_ind bm_ent].
  destruct (decide (i < NDIRECT)%nat) as [Hlt|Hge].
  - apply list_lookup_total_correct, lookup_replicate_2. lia.
  - destruct (decide ((i - NDIRECT) < NINDIRECT)%nat) as [Hlt2|Hge2].
    + apply list_lookup_total_correct, lookup_replicate_2. lia.
    + rewrite list_lookup_total_alt lookup_ge_None_2; [reflexivity|].
      rewrite length_replicate. lia.
Qed.

Lemma bm_empty_slot (i : nat) : bm_slot bm_empty i = bv_0 32.
Proof.
  rewrite /bm_slot. destruct (decide (i = MAXFILE)) as [->|_];
    [reflexivity | apply bm_empty_get].
Qed.

Lemma bm_empty_slot0 (i : nat) : bv_unsigned (bm_slot bm_empty i) = 0.
Proof. rewrite bm_empty_slot. reflexivity. Qed.

(* WELL-FORMED FOR FREE.  Both of [blkmap_wf]'s interesting clauses --
   coverage and injectivity -- are guarded by "this slot is nonzero", and
   no slot is; the lengths and the no-indirect-no-entries clause are
   immediate from the [replicate]s. *)
Lemma bm_empty_wf (cov : gset Z) (ls : Z) : blkmap_wf cov ls bm_empty.
Proof.
  rewrite /blkmap_wf /bm_empty. cbn [bm_dir bm_ind bm_ent].
  split; [apply length_replicate|].
  split; [apply length_replicate|].
  split; [reflexivity|].
  split.
  - intros i _ Hnz. exfalso. apply Hnz. apply bm_empty_slot0.
  - intros i j _ _ Hnz _. exfalso. apply Hnz. apply bm_empty_slot0.
Qed.

(* the truncated file reads as all zeros at every index -- the normalisation
   [blk_holes_zero] wants, at the map itrunc produces *)
Lemma bm_empty_holes (data : nat -> list (bv 8)) :
  (forall i : nat, data i = replicate BSIZE (bv_0 8)) ->
  blk_holes_zero bm_empty data.
Proof. intros H i _ _. exact (H i). Qed.

(* THE BLOCKS AN INODE NAMES, as a set: what itrunc returns to the free
   pool.  Indexed over [S MAXFILE] so the indirect block -- slot MAXFILE --
   is included; it is freed too. *)
Definition bm_blocks (bm : blkmap) : gset Z :=
  list_to_set (map (fun i => bv_unsigned (bm_slot bm i)) (seq 0 (S MAXFILE)))
  ∖ {[ 0 ]}.

Lemma bm_blocks_spec (bm : blkmap) (b : Z) :
  b ∈ bm_blocks bm <->
  (b <> 0 /\ exists i : nat, (i <= MAXFILE)%nat /\ bv_unsigned (bm_slot bm i) = b).
Proof.
  rewrite /bm_blocks elem_of_difference elem_of_singleton elem_of_list_to_set.
  split.
  - intros [Hin Hnz]. split; [exact Hnz|].
    apply elem_of_list_fmap in Hin as (i & -> & Hi).
    exists i. split; [|reflexivity].
    apply elem_of_seq in Hi. lia.
  - intros (Hnz & i & Hi & <-). split; [|exact Hnz].
    apply elem_of_list_fmap. exists i. split; [reflexivity|].
    apply elem_of_seq. lia.
Qed.

Lemma bm_blocks_empty : bm_blocks bm_empty = ∅.
Proof.
  apply set_eq. intros b. split.
  - rewrite bm_blocks_spec. intros (Hnz & i & _ & Hb).
    exfalso. apply Hnz. rewrite -Hb. apply bm_empty_slot0.
  - (* [set_solver] here forced [set_unfold] to normalise [bm_blocks
       bm_empty] -- a [list_to_set] over [seq 0 (S MAXFILE)], 269 entries --
       even though the premise [b ∈ ∅] alone refutes the goal: 14.6 s.
       [not_elem_of_empty] is the one fact this direction needs. *)
    intros Hb. exfalso. exact (not_elem_of_empty b Hb).
Qed.

(* ===================================================================== *)
(*  INSTALLING ONE BLOCK: the pure half of what bmap's three stores do    *)
(*                                                                        *)
(*  All three of bmap's installs -- [ip->addrs[bn]], [ip->addrs[NDIRECT]] *)
(*  and [a[bn-NDIRECT]] inside the indirect block -- change exactly one   *)
(*  slot of the map, so ONE general well-formedness lemma covers them,    *)
(*  parameterised by the position and driven by the three [bm_slot_*]     *)
(*  readings below.  The freshness premise is what the caller gets from   *)
(*  [inode_fresh]; everything else is bookkeeping.                        *)
(* ===================================================================== *)

Lemma bm_slot_insert_dir (bm : blkmap) (j : nat) (w : bv 32) (i : nat) :
  length (bm_dir bm) = NDIRECT -> (j < NDIRECT)%nat -> (i <= MAXFILE)%nat ->
  bm_slot (MkBlkmap (<[j := w]> (bm_dir bm)) (bm_ind bm) (bm_ent bm)) i
  = if decide (i = j) then w else bm_slot bm i.
Proof.
  intros Hlen Hj Hi. unfold bm_slot, blkmap_get. cbn [bm_dir bm_ind bm_ent].
  destruct (decide (i = MAXFILE)) as [->|Hne].
  { destruct (decide (MAXFILE = j)); [unfold MAXFILE, NDIRECT in *; lia|reflexivity]. }
  destruct (decide ((i < NDIRECT)%nat)) as [Hlt|Hge].
  - destruct (decide (i = j)) as [->|Hij].
    + rewrite list_lookup_total_insert; [reflexivity | lia].
    + rewrite list_lookup_total_insert_ne; [reflexivity | lia].
  - destruct (decide (i = j)) as [->|_]; [lia | reflexivity].
Qed.

Lemma bm_slot_insert_ent (bm : blkmap) (q : nat) (w : bv 32) (i : nat) :
  length (bm_ent bm) = NINDIRECT -> (q < NINDIRECT)%nat -> (i <= MAXFILE)%nat ->
  bm_slot (MkBlkmap (bm_dir bm) (bm_ind bm) (<[q := w]> (bm_ent bm))) i
  = if decide (i = (NDIRECT + q)%nat) then w else bm_slot bm i.
Proof.
  intros Hlen Hq Hi. unfold bm_slot, blkmap_get. cbn [bm_dir bm_ind bm_ent].
  destruct (decide (i = MAXFILE)) as [->|Hne].
  { destruct (decide (MAXFILE = (NDIRECT + q)%nat));
      [unfold MAXFILE, NDIRECT, NINDIRECT in *; lia|reflexivity]. }
  destruct (decide ((i < NDIRECT)%nat)) as [Hlt|Hge].
  - destruct (decide (i = (NDIRECT + q)%nat)); [lia | reflexivity].
  - destruct (decide (i = (NDIRECT + q)%nat)) as [->|Hij].
    + rewrite Nat.add_comm Nat.add_sub.
      rewrite list_lookup_total_insert; [reflexivity | lia].
    + rewrite list_lookup_total_insert_ne; [reflexivity | lia].
Qed.

Lemma bm_slot_insert_ind (bm : blkmap) (w : bv 32) (i : nat) :
  bm_ent bm = replicate NINDIRECT (bv_0 32) -> (i <= MAXFILE)%nat ->
  bm_slot (MkBlkmap (bm_dir bm) w (replicate NINDIRECT (bv_0 32))) i
  = if decide (i = MAXFILE) then w else bm_slot bm i.
Proof.
  intros Hent Hi. unfold bm_slot, blkmap_get. cbn [bm_dir bm_ind bm_ent].
  destruct (decide (i = MAXFILE)) as [->|Hne]; [reflexivity|].
  rewrite -Hent. reflexivity.
Qed.

(* THE general step: replace slot [p] by a block [w] that no slot of [bm]
   already names.  Injectivity survives precisely because of that
   freshness premise -- there is nothing else it could come from. *)
Lemma blkmap_wf_slot_upd (cov : gset Z) (ls : Z) (bm bm' : blkmap)
    (p : nat) (w : bv 32) :
  blkmap_wf cov ls bm ->
  length (bm_dir bm') = NDIRECT ->
  length (bm_ent bm') = NINDIRECT ->
  (p <= MAXFILE)%nat ->
  (forall i : nat, (i <= MAXFILE)%nat ->
     bm_slot bm' i = if decide (i = p) then w else bm_slot bm i) ->
  bv_unsigned w <> 0 ->
  bv_unsigned w ∈ cov ->
  ~ (bv_unsigned w ∈ log_region_set ls) ->
  (forall i : nat, (i <= MAXFILE)%nat -> bv_unsigned (bm_slot bm i) <> 0 ->
     bv_unsigned (bm_slot bm i) <> bv_unsigned w) ->
  (bv_unsigned (bm_ind bm') = 0 -> bm_ent bm' = replicate NINDIRECT (bv_0 32)) ->
  blkmap_wf cov ls bm'.
Proof.
  intros Hwf Hdl Hel Hp Hslot Hwnz Hwcov Hwlog Hfresh Hnoind.
  destruct Hwf as (_ & _ & _ & Hcov & Hinj).
  split_and!; [exact Hdl | exact Hel | exact Hnoind | | ].
  - (* coverage *)
    intros i Hi Hnz. rewrite (Hslot i Hi). rewrite (Hslot i Hi) in Hnz.
    destruct (decide (i = p)) as [_|_]; [split; assumption|].
    exact (Hcov i Hi Hnz).
  - (* injectivity *)
    intros i j Hi Hj Hnz Heq.
    rewrite (Hslot i Hi) in Hnz. rewrite (Hslot i Hi) (Hslot j Hj) in Heq.
    destruct (decide (i = p)) as [->|Hip]; destruct (decide (j = p)) as [->|Hjp].
    + reflexivity.
    + (* w = bm_slot bm j : refuted by freshness *)
      exfalso.
      destruct (decide (bv_unsigned (bm_slot bm j) = 0)) as [Hz|Hnzj].
      { apply Hwnz. rewrite -Heq in Hz. exact Hz. }
      exact (Hfresh j Hj Hnzj (f_equal bv_unsigned (eq_sym Heq))).
    + (* bm_slot bm i = w : likewise *)
      exfalso. exact (Hfresh i Hi Hnz (f_equal bv_unsigned Heq)).
    + exact (Hinj i j Hi Hj Hnz Heq).
Qed.

(* ===================================================================== *)
(*  The two resources                                                     *)
(* ===================================================================== *)

Section InodeRes.
  Context `{!riscvGS Σ, !diskGhostG Σ, !fsLogG Σ}.

  (* --- inode_map: the thirteen addrs cells, plus the indirect block --- *)

  (* the thirteen cells, as a list: the twelve direct entries then the
     indirect one, so cell [j] is [ip->addrs[j]] *)
  Definition bm_cells (bm : blkmap) : list (bv 32) :=
    (bm_dir bm ++ [bm_ind bm])%list.

  Definition inode_addrs (ip : mword 64) (l : list (bv 32)) : iProp Σ :=
    ([∗ list] j ↦ a ∈ l, i_addr ip j ↦₄ a)%I.

  (* the indirect block's own logical content, at the byte ENCODING of the
     entry list.  Nothing when there is no indirect block. *)
  Definition ind_blk (γfs : fs_names) (bm : blkmap) : iProp Σ :=
    (if decide (bv_unsigned (bm_ind bm) = 0) then True
     else fsblock γfs (bv_unsigned (bm_ind bm)) (ind_bytes (bm_ent bm)))%I.

  (* ...and the EXCLUSIVE ownership token for that same block.  Split off
     from the content half deliberately: [fsblock] is a HALF ghost_map
     element, so two of them at one key are consistent and carry no
     disjointness at all; [blk_own] is the full element and is the only
     thing that can re-establish [blkmap_wf]'s injectivity when a freshly
     allocated block is installed ([inode_fresh] below).  Keeping it a
     separate conjunct means a proof that has already spent the content
     half (bmap, across its interior [log_write]) still holds the token. *)
  Definition ind_tok (γfs : fs_names) (bm : blkmap) : iProp Σ :=
    (if decide (bv_unsigned (bm_ind bm) = 0) then True
     else blk_own γfs (bv_unsigned (bm_ind bm)))%I.

  Definition ind_res (γfs : fs_names) (bm : blkmap) : iProp Σ :=
    (ind_blk γfs bm ∗ ind_tok γfs bm)%I.

  Definition inode_map (γfs : fs_names) (ip : mword 64) (bm : blkmap) : iProp Σ :=
    (inode_addrs ip (bm_cells bm) ∗ ind_res γfs bm)%I.

  (* --- inode_blocks: one fsblock per allocated file index ------------- *)

  Definition blk_res (γfs : fs_names) (w : bv 32) (bs : list (bv 8)) : iProp Σ :=
    (if decide (bv_unsigned w = 0) then True
     else fsblock γfs (bv_unsigned w) bs ∗ blk_own γfs (bv_unsigned w))%I.

  Definition inode_blocks (γfs : fs_names) (bm : blkmap)
      (data : nat -> list (bv 8)) : iProp Σ :=
    ([∗ list] i ∈ seq 0 MAXFILE, blk_res γfs (blkmap_get bm i) (data i))%I.

  (* ------------------------------------------------------------------ *)
  (*  inode_map: extracting and reinserting one addrs cell               *)
  (* ------------------------------------------------------------------ *)

  Lemma inode_addrs_acc (ip : mword 64) (l : list (bv 32)) (j : nat) (w : bv 32) :
    l !! j = Some w ->
    inode_addrs ip l -∗
      (i_addr ip j ↦₄ w) ∗
      (∀ v : bv 32, i_addr ip j ↦₄ v -∗ inode_addrs ip (<[j := v]> l)).
  Proof.
    intros Hj. rewrite /inode_addrs.
    iApply (big_sepL_insert_acc
              (fun (k : nat) (a : bv 32) => (i_addr ip k ↦₄ a)%I) l j w Hj).
  Qed.

  Lemma bm_cells_dir (bm : blkmap) (j : nat) :
    length (bm_dir bm) = NDIRECT -> (j < NDIRECT)%nat ->
    bm_cells bm !! j = Some (blkmap_get bm j).
  Proof.
    intros Hlen Hj. rewrite /bm_cells.
    rewrite lookup_app_l; [|lia].
    rewrite (blkmap_get_dir bm j Hj).
    apply list_lookup_lookup_total_lt. lia.
  Qed.

  Lemma bm_cells_ind (bm : blkmap) :
    length (bm_dir bm) = NDIRECT -> bm_cells bm !! NDIRECT = Some (bm_ind bm).
  Proof.
    intros Hlen. rewrite /bm_cells.
    rewrite lookup_app_r; [|lia]. rewrite Hlen Nat.sub_diag. reflexivity.
  Qed.

  (* one DIRECT cell out and back, at whatever value the code stored *)
  Lemma inode_map_dir_acc (γfs : fs_names) (ip : mword 64) (bm : blkmap) (j : nat) :
    length (bm_dir bm) = NDIRECT -> (j < NDIRECT)%nat ->
    inode_map γfs ip bm -∗
      (i_addr ip j ↦₄ blkmap_get bm j) ∗
      (∀ w : bv 32, i_addr ip j ↦₄ w -∗
         inode_map γfs ip (MkBlkmap (<[j := w]> (bm_dir bm)) (bm_ind bm) (bm_ent bm))).
  Proof.
    intros Hlen Hj.
    iIntros "[Ha Hi]".
    iDestruct (inode_addrs_acc ip (bm_cells bm) j (blkmap_get bm j)
                 (bm_cells_dir bm j Hlen Hj) with "Ha") as "[Hcell Hback]".
    iFrame "Hcell". iIntros (w) "Hw".
    iDestruct ("Hback" with "Hw") as "Ha".
    rewrite /inode_map /bm_cells /=.
    rewrite insert_app_l; [|lia].
    iFrame "Ha". rewrite /ind_res /=. iExact "Hi".
  Qed.

  (* the INDIRECT cell out and back.  Its resource travels with it: a new
     indirect block arrives with its own entry list, so the reinsertion
     takes the new [ind_res] rather than returning the old one. *)
  Lemma inode_map_ind_acc (γfs : fs_names) (ip : mword 64) (bm : blkmap) :
    length (bm_dir bm) = NDIRECT ->
    inode_map γfs ip bm -∗
      (i_addr ip NDIRECT ↦₄ bm_ind bm) ∗ ind_res γfs bm ∗
      (∀ (w : bv 32) (e : list (bv 32)),
         i_addr ip NDIRECT ↦₄ w -∗ ind_res γfs (MkBlkmap (bm_dir bm) w e) -∗
         inode_map γfs ip (MkBlkmap (bm_dir bm) w e)).
  Proof.
    intros Hlen.
    iIntros "[Ha Hi]".
    iDestruct (inode_addrs_acc ip (bm_cells bm) NDIRECT (bm_ind bm)
                 (bm_cells_ind bm Hlen) with "Ha") as "[Hcell Hback]".
    iFrame "Hcell Hi". iIntros (w e) "Hw Hnew".
    iDestruct ("Hback" with "Hw") as "Ha".
    rewrite /inode_map /bm_cells /=.
    rewrite insert_app_r_alt; [|lia]. rewrite Hlen Nat.sub_diag /=.
    iFrame.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  inode_blocks: one-block access, and the deposit of a fresh block    *)
  (* ------------------------------------------------------------------ *)

  Local Lemma seq_maxfile_lookup (i : nat) :
    (i < MAXFILE)%nat -> seq 0 MAXFILE !! i = Some i.
  Proof. intros Hi. apply lookup_seq. split; [lia|exact Hi]. Qed.

  (* the frame lemma: the bundle only ever looks at indices below MAXFILE *)
  Lemma inode_blocks_frame (γfs : fs_names) (bm bm' : blkmap)
      (data data' : nat -> list (bv 8)) :
    (forall i : nat, (i < MAXFILE)%nat ->
       blkmap_get bm' i = blkmap_get bm i /\ data' i = data i) ->
    inode_blocks γfs bm data -∗ inode_blocks γfs bm' data'.
  Proof.
    intros Hag. rewrite /inode_blocks.
    iIntros "H". iApply (big_sepL_mono with "H").
    intros k y Hky.
    apply lookup_seq in Hky as [Hy Hk].
    assert (Hyk : y = k) by lia. subst y.
    destruct (Hag k Hk) as [Hf Hd]. rewrite Hf Hd. iIntros "$".
  Qed.

  (* one allocated block out and back *)
  Lemma inode_blocks_acc (γfs : fs_names) (bm : blkmap)
      (data : nat -> list (bv 8)) (i : nat) :
    (i < MAXFILE)%nat -> bv_unsigned (blkmap_get bm i) <> 0 ->
    inode_blocks γfs bm data -∗
      (fsblock γfs (bv_unsigned (blkmap_get bm i)) (data i) ∗
       blk_own γfs (bv_unsigned (blkmap_get bm i))) ∗
      (∀ bs : list (bv 8),
         fsblock γfs (bv_unsigned (blkmap_get bm i)) bs -∗
         blk_own γfs (bv_unsigned (blkmap_get bm i)) -∗
         inode_blocks γfs bm (<[i := bs]> data)).
  Proof.
    intros Hi Hnz.
    pose proof (seq_maxfile_lookup i Hi) as Hlk.
    rewrite /inode_blocks.
    rewrite (big_sepL_delete
               (fun (_ : nat) (k : nat) => blk_res γfs (blkmap_get bm k) (data k))
               (seq 0 MAXFILE) i i Hlk).
    iIntros "[Hb Hrest]".
    rewrite /blk_res.
    destruct (decide (bv_unsigned (blkmap_get bm i) = 0)) as [Hz|_];
      [exfalso; exact (Hnz Hz)|].
    iSplitL "Hb"; [iExact "Hb"|]. iIntros (bs) "Hbs Htok".
    rewrite (big_sepL_delete
               (fun (_ : nat) (k : nat) =>
                  blk_res γfs (blkmap_get bm k) ((<[i := bs]> data) k))
               (seq 0 MAXFILE) i i Hlk).
    iSplitL "Hbs Htok".
    { rewrite /blk_res fn_lookup_insert.
      destruct (decide (bv_unsigned (blkmap_get bm i) = 0)) as [Hz|_];
        [exfalso; exact (Hnz Hz)|].
      iSplitL "Hbs"; [iExact "Hbs"|iExact "Htok"]. }
    iApply (big_sepL_mono with "Hrest").
    intros k y Hky.
    apply lookup_seq in Hky as [Hy Hk].
    assert (Hyk : y = k) by lia. subst y.
    destruct (decide (k = i)) as [->|Hne]; [iIntros "$"|].
    rewrite fn_lookup_insert_ne; [|congruence]. iIntros "$".
  Qed.

  (* THE DEPOSIT (design doc, "Why the fresh block is deposited"): bmap's
     freshly allocated data block goes INTO the bundle rather than being
     returned, so the postcondition is the same shape on both paths. *)
  Lemma inode_blocks_insert (γfs : fs_names) (bm bm' : blkmap)
      (data : nat -> list (bv 8)) (bn : nat) (b : bv 32) (bs : list (bv 8)) :
    (bn < MAXFILE)%nat ->
    bv_unsigned (blkmap_get bm bn) = 0 ->
    blkmap_get bm' bn = b ->
    (forall i : nat, (i < MAXFILE)%nat -> i <> bn -> blkmap_get bm' i = blkmap_get bm i) ->
    inode_blocks γfs bm data -∗
    fsblock γfs (bv_unsigned b) bs -∗
    blk_own γfs (bv_unsigned b) -∗
    inode_blocks γfs bm' (<[bn := bs]> data).
  Proof.
    intros Hbn Hz Hb Hag.
    pose proof (seq_maxfile_lookup bn Hbn) as Hlk.
    rewrite /inode_blocks.
    rewrite (big_sepL_delete
               (fun (_ : nat) (k : nat) => blk_res γfs (blkmap_get bm k) (data k))
               (seq 0 MAXFILE) bn bn Hlk).
    rewrite (big_sepL_delete
               (fun (_ : nat) (k : nat) =>
                  blk_res γfs (blkmap_get bm' k) ((<[bn := bs]> data) k))
               (seq 0 MAXFILE) bn bn Hlk).
    iIntros "[_ Hrest] Hfs Htok".
    iSplitL "Hfs Htok".
    { rewrite /blk_res Hb fn_lookup_insert.
      destruct (decide (bv_unsigned b = 0)); [done|].
      iSplitL "Hfs"; [iExact "Hfs"|iExact "Htok"]. }
    iApply (big_sepL_mono with "Hrest").
    intros k y Hky.
    apply lookup_seq in Hky as [Hy Hk].
    assert (Hyk : y = k) by lia. subst y.
    destruct (decide (k = bn)) as [->|Hne]; [iIntros "$"|].
    rewrite (Hag k Hk Hne) fn_lookup_insert_ne; [|congruence].
    iIntros "$".
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  FRESHNESS: what re-establishes [blkmap_wf]'s injectivity            *)
  (* ------------------------------------------------------------------ *)

  (* THE lemma the three install sites want.  Holding the exclusive token
     for a block [b] -- which is exactly what balloc's success arm hands
     over -- rules [b] out of every nonzero slot the inode already names,
     because the bundles hold a token for each of those.
     This is the ONLY route to injectivity: [fsblock] is a HALF ghost_map
     element, so two of them at one key compose to a perfectly valid full
     element and carry no disjointness whatever.  [ind_tok] rather than
     [ind_res] is the premise so a caller that has spent the indirect
     block's content half (bmap, across its interior log_write) can still
     apply it. *)
  Lemma inode_fresh_at (γfs : fs_names) (bm : blkmap)
      (data : nat -> list (bv 8)) (b : Z) (i : nat) :
    (i <= MAXFILE)%nat -> bv_unsigned (bm_slot bm i) <> 0 ->
    blk_own γfs b -∗ ind_tok γfs bm -∗ inode_blocks γfs bm data -∗
    ⌜bv_unsigned (bm_slot bm i) <> b⌝.
  Proof.
    intros Hi Hnz. iIntros "Ho Ht Hd".
    destruct (decide (i = MAXFILE)) as [->|Hne].
    - rewrite bm_slot_top. rewrite bm_slot_top in Hnz.
      rewrite /ind_tok.
      destruct (decide (bv_unsigned (bm_ind bm) = 0)) as [Hz|_];
        [exfalso; exact (Hnz Hz)|].
      iApply (blk_own_ne with "Ht Ho").
    - assert (Hlt : (i < MAXFILE)%nat) by lia.
      rewrite (bm_slot_lt bm i Hlt).
      rewrite (bm_slot_lt bm i Hlt) in Hnz.
      rewrite /inode_blocks.
      iDestruct (big_sepL_lookup
                   (fun (_ : nat) (k : nat) => blk_res γfs (blkmap_get bm k) (data k))
                   (seq 0 MAXFILE) i i (seq_maxfile_lookup i Hlt) with "Hd") as "Hb".
      rewrite /blk_res.
      destruct (decide (bv_unsigned (blkmap_get bm i) = 0)) as [Hz|_];
        [exfalso; exact (Hnz Hz)|].
      iDestruct "Hb" as "[_ Hb]".
      iApply (blk_own_ne with "Hb Ho").
  Qed.

  (* the quantified form the [blkmap_wf_slot_upd] premise is stated at *)
  Lemma inode_fresh (γfs : fs_names) (bm : blkmap)
      (data : nat -> list (bv 8)) (b : Z) :
    blk_own γfs b -∗ ind_tok γfs bm -∗ inode_blocks γfs bm data -∗
    ⌜forall i : nat, (i <= MAXFILE)%nat -> bv_unsigned (bm_slot bm i) <> 0 ->
        bv_unsigned (bm_slot bm i) <> b⌝.
  Proof.
    iIntros "Ho Ht Hd". rewrite bi.pure_forall. iIntros (i).
    destruct (decide ((i <= MAXFILE)%nat)) as [Hi|Hi];
      [| iPureIntro; intros Hc; exfalso; exact (Hi Hc)].
    destruct (decide (bv_unsigned (bm_slot bm i) = 0)) as [Hz|Hnz];
      [ iPureIntro; intros _ Hc; exfalso; exact (Hc Hz) |].
    iDestruct (inode_fresh_at γfs bm data b i Hi Hnz with "Ho Ht Hd") as %Hne.
    iPureIntro. intros _ _. exact Hne.
  Qed.

  (* ------------------------------------------------------------------ *)
  (*  inode_meta: the five SCALAR metadata cells, at a pure dinode        *)
  (* ------------------------------------------------------------------ *)

  (* WHY THE WHOLE [dinode] AND NOT FIVE SCALARS.  The record is what the
     ON-DISK image is a function of ([DinodeEnc.dinode_bytes]), so iupdate's
     postcondition can be exactly [diblk_bytes (<[k := d]> ds)] -- one term,
     no re-assembly at the call site.  Its [di_addrs] field is deliberately
     NOT owned here: those thirteen cells belong to [inode_map], exclusively,
     and a second owner would be unsatisfiable.  The tie between the two is
     the caller-supplied [di_addrs d = bm_cells bm], which is the one place
     the duplication is visible and the one place a caller has to think
     about it.  (The alternative -- a five-field [dmeta] record plus a
     [dinode_of dm cells] constructor -- needs a second record, and puts the
     assembly into every caller's postcondition instead of into one
     premise.) *)
  Definition inode_meta (ip : mword 64) (d : dinode) : iProp Σ :=
    (i_type  ip ↦₂ di_type  d ∗
     i_major ip ↦₂ di_major d ∗
     i_minor ip ↦₂ di_minor d ∗
     i_nlink ip ↦₂ di_nlink d ∗
     i_size  ip ↦₄ di_size  d)%I.

  (* ------------------------------------------------------------------ *)
  (*  THE ADDRS CELLS AS A 52-BYTE BUFFER                                 *)
  (*                                                                      *)
  (*  memmove's SOURCE is [ip->addrs] read as [sizeof(ip->addrs)] = 52    *)
  (*  contiguous bytes, and its contract is stated over ByteBuf's         *)
  (*  [seq]-indexed byte window.  [ByteBuf.bb_word4_acc] goes the other    *)
  (*  way (borrow a WORD out of a byte buffer); this is the converse --    *)
  (*  present a run of word CELLS as the buffer.  Read-only, so it is one  *)
  (*  accessor whose back-wand takes the same bytes: memmove leaves its    *)
  (*  source untouched, and the wand's closure is what carries the        *)
  (*  per-cell 4-alignment that the bytes themselves no longer know.      *)
  (*                                                                      *)
  (*  The naming function is [BlockWords.ind_bytes] of the cell list --    *)
  (*  the same little-endian word-array encoding the indirect block uses,  *)
  (*  which is also [DinodeEnc]'s [addrs] field encoding, so the byte      *)
  (*  image memmove copies IS the [dinode_bytes] tail with no conversion.  *)
  (* ------------------------------------------------------------------ *)

  Local Lemma ia_shift (a : mword 64) (j : nat) :
    pa_add a (4 * S j)%nat = pa_add (pa_add a 4%nat) (4 * j)%nat.
  Proof. rewrite pa_add_add. f_equal. lia. Qed.

  (* the run of cells, at an arbitrary base: the induction's shape *)
  Local Lemma ia_cells_bytes (l : list (bv 32)) :
    forall a : mword 64,
    (forall j, (j < length l)%nat ->
       is_aligned_paddr (Physaddr (pa_add a (4 * j)%nat)) 4 = true) ->
    ([∗ list] j ↦ w ∈ l, pa_add a (4 * j)%nat ↦₄ w)
    ⊣⊢ ([∗ list] j ∈ seq 0 (4 * length l)%nat, pa_add a j ↦ₘ (ind_bytes l !!! j)).
  Proof.
    induction l as [|w l IH]; intros a Hal.
    - rewrite Nat.mul_0_r /=. reflexivity.
    - simpl length.
      replace (4 * S (length l))%nat with (4 + 4 * length l)%nat by lia.
      rewrite (bb_split a 4 (4 * length l)%nat (fun j => ind_bytes (w :: l) !!! j)).
      rewrite big_sepL_cons.
      apply bi.sep_proper.
      + (* the head cell IS its four bytes *)
        assert (Ha0 : is_aligned_paddr (Physaddr a) 4 = true).
        { pose proof (Hal 0%nat ltac:(simpl; lia)) as Hz.
          rewrite Nat.mul_0_r pa_add_0 in Hz. exact Hz. }
        rewrite Nat.mul_0_r pa_add_0.
        rewrite /word4_pointsto (bi.pure_True _ Ha0) bi.True_sep.
        apply big_sepL_proper. intros i jj Hj.
        apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
        rewrite (ind_bytes_cons_lo w l i Hlt). reflexivity.
      + (* the tail, at base [a + 4] *)
        transitivity ([∗ list] j ∈ seq 0 (4 * length l)%nat,
                        pa_add (pa_add a 4%nat) j ↦ₘ (ind_bytes l !!! j))%I.
        { transitivity ([∗ list] j ↦ w' ∈ l,
                          pa_add (pa_add a 4%nat) (4 * j)%nat ↦₄ w')%I.
          - apply big_sepL_proper. intros i w' _. rewrite ia_shift. reflexivity.
          - apply (IH (pa_add a 4%nat)).
            intros j Hj. rewrite -ia_shift. apply (Hal (S j)). simpl length. lia. }
        apply big_sepL_proper. intros i jj Hj.
        apply lookup_seq in Hj as [-> Hlt]. rewrite Nat.add_0_l.
        rewrite (ind_bytes_cons_hi w l i). reflexivity.
  Qed.

  Lemma inode_addrs_aligned (ip : mword 64) (l : list (bv 32)) (j : nat) :
    (j < length l)%nat ->
    inode_addrs ip l -∗ ⌜is_aligned_paddr (Physaddr (i_addr ip j)) 4 = true⌝.
  Proof.
    intros Hj. rewrite /inode_addrs.
    iIntros "H".
    iDestruct (big_sepL_lookup
                 (fun (k : nat) (a : bv 32) => (i_addr ip k ↦₄ a)%I) l j (l !!! j)
                 (list_lookup_lookup_total_lt l j Hj) with "H") as "Hc".
    iApply (word4_pointsto_aligned_p with "Hc").
  Qed.

  Lemma inode_addrs_aligned_all (ip : mword 64) (l : list (bv 32)) :
    inode_addrs ip l -∗
    ⌜forall j, (j < length l)%nat ->
       is_aligned_paddr (Physaddr (pa_add (i_addr ip 0) (4 * j)%nat)) 4 = true⌝.
  Proof.
    iIntros "H". rewrite bi.pure_forall. iIntros (j).
    destruct (decide ((j < length l)%nat)) as [Hj|Hj];
      [| iPureIntro; intros Hc; exfalso; exact (Hj Hc)].
    iDestruct (inode_addrs_aligned ip l j Hj with "H") as %Hal.
    iPureIntro. intros _. rewrite -i_addr_from_0. exact Hal.
  Qed.

  Lemma inode_addrs_bytes_iff (ip : mword 64) (l : list (bv 32)) :
    (forall j, (j < length l)%nat ->
       is_aligned_paddr (Physaddr (pa_add (i_addr ip 0) (4 * j)%nat)) 4 = true) ->
    inode_addrs ip l
    ⊣⊢ bb_bytes (i_addr ip 0) (4 * length l)%nat (fun j => ind_bytes l !!! j).
  Proof.
    intros Hal. rewrite /inode_addrs /bb_bytes.
    rewrite -(ia_cells_bytes l (i_addr ip 0) Hal).
    apply big_sepL_proper. intros i w _. rewrite i_addr_from_0. reflexivity.
  Qed.

  (* THE BRIDGE memmove's source wants. *)
  Lemma inode_addrs_buf (ip : mword 64) (l : list (bv 32)) :
    inode_addrs ip l -∗
      bb_bytes (i_addr ip 0) (4 * length l)%nat (fun j => ind_bytes l !!! j) ∗
      (bb_bytes (i_addr ip 0) (4 * length l)%nat (fun j => ind_bytes l !!! j) -∗
       inode_addrs ip l).
  Proof.
    iIntros "H".
    iDestruct (inode_addrs_aligned_all with "H") as %Hal.
    (* the bare rewrite hits the WHOLE [envs_entails] -- hypothesis and both
       occurrences in the goal -- which is exactly what is wanted here: the
       returning wand becomes the identity on the byte window. *)
    rewrite (inode_addrs_bytes_iff ip l Hal).
    iFrame "H". iIntros "Hb". iExact "Hb".
  Qed.

End InodeRes.
