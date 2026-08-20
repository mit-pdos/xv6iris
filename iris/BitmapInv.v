(* BitmapInv.v -- the block bitmap's resource, and the FREE POOL.
   Design: claude-notes/design/fs-bitmap.md.

   ---- THE GEOMETRY, read off balloc/bfree ---------------------------

     BPB = BSIZE * 8 = 8192 bits per bitmap block
     BBLOCK(b, sb) = b / BPB + sb.bmapstart

   balloc's [sraiw a1,s5,0xd] / [lw a5,28(s6)] / [addw] pair is what pins
   BPB = 2^13 and puts [bmapstart] at [sb + 28]; bfree's [srliw a5,a1,0xd]
   / [lw a1,-1246(a1)] (= sb + 0x1c) says the same.  [sb.size] is at
   [sb + 4] ([lw a5,-1370(a5)] = sb + 0x4, and [lw a5,4(s6)] with
   [s6 = &sb]).

   FSSIZE = 2000 < BPB, so there is exactly ONE bitmap block and balloc's
   outer loop runs a single iteration.  That is why [size <= BPB] is a
   PREMISE of every contract here and the resource is keyed at the single
   block number [bmapstart] rather than at a family of them: a two-level
   induction for a case the mkfs image cannot reach would be structure
   nobody can exercise.

   ---- THE RESOURCE --------------------------------------------------

   [bitmap_res γfs bmapstart cov logstart size used] is three things:

     - the pure well-formedness [bitmap_ok]: every CLEAR bit below
       [size] names a covered home block (in [cov], outside the log's own
       storage).  It is what turns "balloc found a zero bit" into the two
       facts bread and log_write demand of a block number;
     - the bitmap block itself, as an [fsblock] at [bitmap_bytes used] --
       the block content is kept in the IMAGE of [BitmapEnc.bm_bytes]
       over the pure set [used], so setting a bit is [used ∪ {[bi]}] and
       the byte level is only ever read back;
     - the FREE POOL: for every block below [size] whose bit is CLEAR,
       that block's [fsblock] half AND its exclusive [blk_own] token.

   The pool is the answer to the question fs-inode.md left open -- where a
   free block's [fsblock] half lives while it is free.  [FsBlocks.fs_alloc]
   already mints one half plus one [blk_own] per covered block at boot, so
   the material exists; this is where it parks.

   ---- WHY [blk_own] IS WHAT MAKES THE HANDSHAKE SOUND ----------------

   [fsblock] is a HALF ghost_map element: two owners each holding a half
   of one key are perfectly consistent, so no amount of [fsblock]
   reasoning says a block is unowned.  [blk_own] is the FULL element and
   is therefore EXCLUSIVE, and the pool holds one per clear bit.  That
   single fact does both jobs:

     - balloc hands out the token with the block, so a caller that keeps
       one per block its own structures name can conclude the new block is
       none of them ([FsBlocks.blk_own_ne]) -- the fact that re-establishes
       [InodeInv.blkmap_wf]'s injectivity, and the same fact that stopped
       the inode block map from aliasing;
     - bfree's [panic("freeing free block")] is DEAD, and
       [free_pool_own_used] is the proof: the caller arrives holding the
       block's token, so if the bit were CLEAR the pool would hold a
       SECOND token at that key, which is absurd.  So the bit is set and
       the panic arm is unreachable.  Refuting that panic is the main
       thing this invariant has to buy.

   ---- WHO OWNS [bitmap_res] BETWEEN CALLS ----------------------------

   DEFERRED, deliberately, exactly as [InodeInv.inode_map] was for bmap:
   PASS IT IN AND RETURN IT UPDATED.  In xv6 the discipline is the buffer
   sleeplock on the bitmap block -- bread gives exclusive access for the
   critical section -- so a later free-space layer can seat it there.
   Designing that layer here would block balloc behind it.               *)

From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list list_numbers functions bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_map.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import DiskPtsto.
Require Import FsBlocks.
Require Import LogInv.
Require Import FsCrash.     (* [BSIZE] *)
Require Import BitmapEnc.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types.
(* The [set_solver] override.  EXPORT, not Import: this import is         *)
(* deliberately "dead" -- the file compiles without it, just far slower --  *)
(* and the nightly dead-import sweep skips [Require Export] lines.         *)
(* It has to be HERE rather than inherited: [Require Export] only          *)
(* propagates through an unbroken chain of Exports, and this tree's        *)
(* intermediate files use [Require Import], so nothing downstream inherits *)
(* it.  See FastSetSolver.v.                                              *)
Require Export FastSetSolver.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  Geometry                                                             *)
(* ===================================================================== *)

(* bits per bitmap block: BSIZE bytes of eight bits *)
Definition BPB : Z := 8 * Z.of_nat BSIZE.

Lemma BPB_value : BPB = 8192.
Proof. reflexivity. Qed.

(* BBLOCK(b, sb) -- the bitmap block holding bit [b].  With [size <= BPB]
   (the mkfs image: FSSIZE = 2000) every in-range [b] lands on the single
   block [bmapstart], which is [BBLOCK_single] below. *)
Definition BBLOCK (b bmapstart : Z) : Z := b `div` BPB + bmapstart.

Lemma BBLOCK_single (b bmapstart : Z) :
  0 <= b < BPB -> BBLOCK b bmapstart = bmapstart.
Proof.
  intros Hb. unfold BBLOCK. rewrite (Z.div_small b BPB Hb). reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(*  The two superblock fields the allocator reads.                         *)
(*                                                                         *)
(*  Both ride through the contracts as plain FRACTIONAL cells, the way     *)
(*  SpecInitlog.v takes [sb + 20] for logstart and InodeInv.v takes        *)
(*  [sb + 24] for inodestart: read, never written, handed straight back.   *)
(*  There is deliberately still no superblock abstraction.                 *)
(* ---------------------------------------------------------------------- *)

(* balloc +0x0a: [auipc a5,0x1e / lw a5,-1370(a5)] -> 0x80020854 = sb + 4 *)
Definition sb_size : mword 64 :=
  pa_add (mword_of_int KernelSyms.sb : mword 64) 4.

(* balloc +0xa0: [lw a5,28(s6)] with s6 = &sb; bfree +0x16 resolves to
   0x8002086c = sb + 0x1c *)
Definition sb_bmapstart : mword 64 :=
  pa_add (mword_of_int KernelSyms.sb : mword 64) 28.

(* ===================================================================== *)
(*  The pure well-formedness of a bitmap                                  *)
(* ===================================================================== *)

(* Every CLEAR bit below [size] names a usable client block.  This is the
   only thing that converts balloc's scan result into the two facts bread
   and log_write demand; [x <> 0] comes free from [cov_ok]. *)
Definition bitmap_ok (cov : gset Z) (logstart size : Z) (used : gset Z) : Prop :=
  forall x : Z, 0 <= x < size -> x ∉ used ->
    x ∈ cov /\ ~ (x ∈ log_region_set logstart).

Lemma bitmap_ok_add (cov : gset Z) (ls size : Z) (used : gset Z) (bi : Z) :
  bitmap_ok cov ls size used -> bitmap_ok cov ls size (used ∪ {[bi]}).
Proof. intros H x Hx Hnu. apply H; [exact Hx|set_solver]. Qed.

Lemma bitmap_ok_del (cov : gset Z) (ls size : Z) (used : gset Z) (b : Z) :
  b ∈ cov -> ~ (b ∈ log_region_set ls) ->
  bitmap_ok cov ls size used -> bitmap_ok cov ls size (used ∖ {[b]}).
Proof.
  intros Hcov Hlog H x Hx Hnu.
  destruct (decide (x = b)) as [->|Hne]; [split; assumption|].
  apply H; [exact Hx|set_solver].
Qed.

(* the covered-ness fact a client of [bitmap_ok] actually applies *)
Lemma bitmap_ok_free (cov : gset Z) (ls size : Z) (used : gset Z) (x : Z) :
  bitmap_ok cov ls size used -> 0 <= x < size -> x ∉ used ->
  x ∈ cov /\ ~ (x ∈ log_region_set ls).
Proof. intros H ? ?. by apply H. Qed.

Lemma bitmap_ok_nonzero (cov : gset Z) (ls size : Z) (used : gset Z) (x : Z) :
  cov_ok cov -> bitmap_ok cov ls size used -> 0 <= x < size -> x ∉ used ->
  x <> 0.
Proof.
  intros Hcov H Hx Hnu. destruct (H x Hx Hnu) as [Hin _].
  specialize (Hcov x Hin). lia.
Qed.

(* ===================================================================== *)
(*  The resource                                                          *)
(* ===================================================================== *)

Section BitmapRes.
  Context `{!riscvGS Σ, !xv6G Σ}.

  (* the bitmap block's content, as the IMAGE of the pure set [used] *)
  Definition bitmap_bytes (used : gset Z) : list (bv 8) := bm_bytes BSIZE used.

  Lemma bitmap_bytes_length (u : gset Z) : length (bitmap_bytes u) = BSIZE.
  Proof. apply bm_bytes_length. Qed.

  Lemma bitmap_bytes_lookup (u : gset Z) (j : nat) :
    (j < BSIZE)%nat -> bitmap_bytes u !! j = Some (bm_byte u (Z.of_nat j)).
  Proof. apply bm_bytes_lookup. Qed.

  (* storing the one byte the code stores turns the image of [used] into
     the image of the updated set -- both directions of the allocator *)
  Lemma bitmap_bytes_set_bit (u : gset Z) (bi : Z) :
    0 <= bi < BPB ->
    <[Z.to_nat (bi `div` 8) := bm_byte (u ∪ {[bi]}) (bi `div` 8)]> (bitmap_bytes u)
    = bitmap_bytes (u ∪ {[bi]}).
  Proof.
    intros Hbi. apply bm_bytes_set; [lia|]. apply bit_byte_lt. exact Hbi.
  Qed.

  Lemma bitmap_bytes_clear_bit (u : gset Z) (bi : Z) :
    0 <= bi < BPB ->
    <[Z.to_nat (bi `div` 8) := bm_byte (u ∖ {[bi]}) (bi `div` 8)]> (bitmap_bytes u)
    = bitmap_bytes (u ∖ {[bi]}).
  Proof.
    intros Hbi. apply bm_bytes_clear; [lia|]. apply bit_byte_lt. exact Hbi.
  Qed.

  (* ---- the free pool ------------------------------------------------ *)

  (* one free block: its logical content (at SOME block-sized byte list --
     the pool makes no promise about a free block's bytes, and bzero is
     what makes the allocated one all-zero) and its EXCLUSIVE token *)
  Definition free_blk (γfs : fs_names) (b : Z) : iProp Σ :=
    (∃ bs : list (bv 8), ⌜length bs = BSIZE⌝ ∗ fsblock γfs b bs ∗ blk_own γfs b)%I.

  Definition free_set (size : Z) (used : gset Z) : gset Z :=
    (list_to_set (seqZ 0 size) : gset Z) ∖ used.

  Lemma elem_of_free_set (size : Z) (used : gset Z) (x : Z) :
    x ∈ free_set size used <-> (0 <= x < size /\ x ∉ used).
  Proof.
    unfold free_set.
    rewrite elem_of_difference elem_of_list_to_set elem_of_seqZ.
    split.
    - intros [H1 H2]. split; [lia | exact H2].
    - intros [H1 H2]. split; [lia | exact H2].
  Qed.

  Definition free_pool (γfs : fs_names) (size : Z) (used : gset Z) : iProp Σ :=
    ([∗ set] b ∈ free_set size used, free_blk γfs b)%I.

  (* ---- the resource ------------------------------------------------- *)

  Definition bitmap_res (γfs : fs_names) (bmapstart : Z)
      (cov : gset Z) (logstart size : Z) (used : gset Z) : iProp Σ :=
    (⌜bitmap_ok cov logstart size used⌝ ∗
     fsblock γfs bmapstart (bitmap_bytes used) ∗
     free_pool γfs size used)%I.

  Lemma bitmap_res_open (γfs : fs_names) (bms : Z) (cov : gset Z)
      (ls size : Z) (used : gset Z) :
    bitmap_res γfs bms cov ls size used -∗
      ⌜bitmap_ok cov ls size used⌝ ∗
      fsblock γfs bms (bitmap_bytes used) ∗
      free_pool γfs size used.
  Proof. iIntros "H". iExact "H". Qed.

  Lemma bitmap_res_close (γfs : fs_names) (bms : Z) (cov : gset Z)
      (ls size : Z) (used : gset Z) :
    bitmap_ok cov ls size used ->
    fsblock γfs bms (bitmap_bytes used) -∗
    free_pool γfs size used -∗
    bitmap_res γfs bms cov ls size used.
  Proof.
    iIntros (Hok) "Hb Hp". rewrite /bitmap_res.
    iSplitR; [iPureIntro; exact Hok|]. iFrame.
  Qed.

  (* ================================================================== *)
  (*  The handshake                                                      *)
  (* ================================================================== *)

  Lemma free_set_take (size : Z) (used : gset Z) (bi : Z) :
    free_set size used ∖ {[bi]} = free_set size (used ∪ {[bi]}).
  Proof. unfold free_set. set_solver. Qed.

  Lemma free_set_give (size : Z) (used : gset Z) (b : Z) :
    0 <= b < size ->
    free_set size (used ∖ {[b]}) = free_set size used ∪ {[b]}.
  Proof.
    intros Hb. apply set_eq. intros x.
    rewrite elem_of_union elem_of_singleton !elem_of_free_set.
    split.
    - intros [Hx Hnu]. destruct (decide (x = b)) as [->|Hne]; [by right|].
      left. split; [exact Hx|]. intros Hu. apply Hnu.
      apply elem_of_difference. split; [exact Hu|].
      rewrite elem_of_singleton. exact Hne.
    - intros [[Hx Hnu]|Hxb].
      + split; [exact Hx|]. intros Hd.
        apply elem_of_difference in Hd as [Hu _]. exact (Hnu Hu).
      + subst x. split; [lia|]. intros Hd.
        apply elem_of_difference in Hd as [_ Hns].
        apply Hns, elem_of_singleton. reflexivity.
  Qed.

  (* ALLOCATE: a clear bit yields the block's half and its token, and the
     pool shrinks by exactly that block. *)
  Lemma free_pool_take (γfs : fs_names) (size : Z) (used : gset Z) (bi : Z) :
    0 <= bi < size -> bi ∉ used ->
    free_pool γfs size used -∗
      free_blk γfs bi ∗ free_pool γfs size (used ∪ {[bi]}).
  Proof.
    intros Hbi Hnu. rewrite /free_pool.
    rewrite (big_sepS_delete _ (free_set size used) bi
               ltac:(apply elem_of_free_set; split; [exact Hbi|exact Hnu])).
    rewrite free_set_take. iIntros "[$ $]".
  Qed.

  (* THE PANIC REFUTATION.  The caller holds the block's token; if the bit
     were clear the pool would hold a SECOND one at the same key, and
     [blk_own] is a FULL-fraction ghost_map element. *)
  Lemma free_pool_own_used (γfs : fs_names) (size : Z) (used : gset Z) (b : Z) :
    0 <= b < size ->
    blk_own γfs b -∗ free_pool γfs size used -∗ ⌜b ∈ used⌝.
  Proof.
    intros Hb. iIntros "Hown Hpool".
    destruct (decide (b ∈ used)) as [Hin|Hnu]; [done|].
    rewrite /free_pool.
    rewrite (big_sepS_delete _ (free_set size used) b
               ltac:(apply elem_of_free_set; split; [exact Hb|exact Hnu])).
    iDestruct "Hpool" as "[Hb _]".
    iDestruct "Hb" as (bs) "(_ & _ & Hown2)".
    iExFalso. iApply (blk_own_excl with "Hown Hown2").
  Qed.

  (* FREE: the block's half and token go back into the pool, and the bit
     is cleared. *)
  Lemma free_pool_give (γfs : fs_names) (size : Z) (used : gset Z) (b : Z) :
    0 <= b < size -> b ∈ used ->
    free_blk γfs b -∗ free_pool γfs size used -∗
    free_pool γfs size (used ∖ {[b]}).
  Proof.
    intros Hb Hin. iIntros "Hblk Hpool". rewrite /free_pool free_set_give //.
    rewrite big_sepS_union.
    2:{ apply disjoint_singleton_r. rewrite elem_of_free_set.
        intros [_ Hnu]. exact (Hnu Hin). }
    rewrite big_sepS_singleton. iFrame.
  Qed.

  (* ================================================================== *)
  (*  What a CALLER of balloc has to hold                                *)
  (* ================================================================== *)

  (* balloc's four geometry premises, bundled once so every contract and
     every interior lemma that forwards them carries ONE hypothesis rather
     than four.  [0 < size] is what kills balloc's own [beqz a5] arm at
     +0x12 and [size <= BPB] is the single-bitmap-block simplification; the
     other two are what bread and log_write demand of the bitmap block
     itself. *)
  Definition bitmap_geom_ok (cov : gset Z) (logstart bmapstart size : Z) : Prop :=
    0 < size <= BPB
    /\ 0 <= bmapstart
    /\ bmapstart ∈ cov
    /\ ~ (bmapstart ∈ log_region_set logstart).

  (* THE BITMAP AT AN EXISTENTIAL SET.  balloc returns it one bit fuller, and
     bmap may allocate TWICE while writei calls bmap once per straddled
     block.  Carrying the exact set would make every interior lemma of both
     proofs thread it.  Indexing by the set on ENTRY and existentially
     quantifying the CURRENT one instead makes the index INVARIANT --
     [uu ⊆ uc] is preserved by every allocation -- so no loop invariant has
     to be re-plumbed, and bmap's public postcondition
     [∃ used', ⌜used ⊆ used'⌝] is literally this predicate unfolded. *)
  Definition bm_bitmap (γfs : fs_names) (cov : gset Z) (logstart bms sz : Z)
      (uu : gset Z) : iProp Σ :=
    (∃ uc : gset Z, ⌜uu ⊆ uc⌝ ∗ bitmap_res γfs bms cov logstart sz uc)%I.

  Lemma bm_bitmap_intro (γfs : fs_names) (cov : gset Z) (logstart bms sz : Z)
      (uu uc : gset Z) :
    uu ⊆ uc ->
    bitmap_res γfs bms cov logstart sz uc -∗
    bm_bitmap γfs cov logstart bms sz uu.
  Proof.
    intros Hsub. iIntros "H". rewrite /bm_bitmap. iExists uc.
    iSplitR; [iPureIntro; exact Hsub|]. iExact "H".
  Qed.

  (* the shape bfree's caller hands over: a block-sized content half plus
     the token *)
  Lemma free_blk_intro (γfs : fs_names) (b : Z) (bs : list (bv 8)) :
    length bs = BSIZE ->
    fsblock γfs b bs -∗ blk_own γfs b -∗ free_blk γfs b.
  Proof.
    iIntros (Hlen) "Hb Ho". rewrite /free_blk. iExists bs.
    iSplitR; [iPureIntro; exact Hlen|]. iFrame.
  Qed.

End BitmapRes.

(* the two monotonicity steps, as NAMED lemmas: an [ltac:(set_solver)] in an
   argument position inside a whole-function proof costs hundreds of seconds
   (claude-notes/durable-notes.md). *)
Lemma bm_used_grow (uu uc : gset Z) (x : Z) : uu ⊆ uc -> uu ⊆ uc ∪ {[x]}.
Proof. intros H. etransitivity; [exact H|]. apply union_subseteq_l. Qed.

Lemma bm_used_trans (u1 u2 u3 : gset Z) : u1 ⊆ u2 -> u2 ⊆ u3 -> u1 ⊆ u3.
Proof. intros H1 H2. etransitivity; [exact H1|exact H2]. Qed.

(* THE ALLOCATION-SIDE BUNDLE a caller of balloc carries, as ONE record and
   ONE iProp.  bmap's interior lemmas and writei's loop thread exactly this:
   one binder and one resource, rather than five of each.  Everything in it
   is either pure or a fraction that goes straight back out, so it is
   invariant across the whole call. *)
Record bm_alloc := MkBmAlloc {
  ba_log  : log_names;   (* the log the reservation is against *)
  ba_bms  : Z;           (* sb.bmapstart *)
  ba_size : Z;           (* sb.size     *)
  ba_used : gset Z;      (* the bitmap on ENTRY *)
  ba_dqb  : dfrac;
  ba_dqs  : dfrac;
  ba_pr   : gname;       (* printk's lock name, for the out-of-blocks arm *)
}.

Section BitmapAllocRes.
  Context `{!riscvGS Σ, !xv6G Σ}.

  Definition bm_alloc_res (γfs : fs_names) (cov : gset Z) (logstart : Z)
      (a : bm_alloc) : iProp Σ :=
    (⌜bitmap_geom_ok cov logstart (ba_bms a) (ba_size a)⌝ ∗
     sb_size ↦₄{ba_dqs a} (mword_of_int (ba_size a) : mword 32) ∗
     sb_bmapstart ↦₄{ba_dqb a} (mword_of_int (ba_bms a) : mword 32) ∗
     bm_bitmap γfs cov logstart (ba_bms a) (ba_size a) (ba_used a))%I.
End BitmapAllocRes.
