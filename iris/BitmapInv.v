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
     - the bitmap block itself, as an [fs_chalf] at [bitmap_bytes used] --
       the block content is kept in the IMAGE of [BitmapEnc.bm_bytes]
       over the pure set [used], so setting a bit is [used ∪ {[bi]}] and
       the byte level is only ever read back;
     - the FREE POOL: for every block below [size] whose bit is CLEAR,
       that block's [fs_chalf] half AND its exclusive [blk_own] token.

   The pool is the answer to the question fs-inode.md left open -- where a
   free block's [fs_chalf] half lives while it is free.  [FsBlocks.fs_alloc]
   already mints one half plus one [blk_own] per covered block at boot, so
   the material exists; this is where it parks.

   ---- WHY [blk_own] IS WHAT MAKES THE HANDSHAKE SOUND ----------------

   REDUNDANT SINCE THE CONSUMER FLIP, AND KEPT ONLY BECAUSE STAGE 2
   RETIRES IT WITH THE POOL (durable-disk 1c-flip step 5).  The argument
   below was written when the content resource was [fs_chalf], a HALF
   ghost_map element: two owners each holding a half of one key are
   perfectly consistent, so no amount of [fs_chalf] reasoning says a block
   is unowned.  The pool and every home-block owner hold the EXCLUSIVE byte
   run [fsblock] now, and [FsBlocks.fsblock_excl] does both jobs below on
   its own -- [free_pool_own_used]'s panic refutation especially, since two
   owners of one block's bytes is already [False].  [blk_own] is the FULL
   element and
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
From iris.base_logic.lib Require Import ghost_map invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import FsBlocks.
Require Import LogInv.
Require Import BioDefs.     (* [BSIZE] *)
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

(* balloc +0x0a: [auipc a5,0x1e / lw a5,-1370(a5)] -> 0x80020844 = sb + 4 *)
Definition sb_size : mword 64 :=
  pa_add (mword_of_int KernelSyms.sb : mword 64) 4.

(* balloc +0xa0: [lw a5,28(s6)] with s6 = &sb; bfree +0x16 resolves to
   0x8002085c = sb + 0x1c *)
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
    (∃ bs : list (bv 8), ⌜length bs = BSIZE⌝ ∗
       fsblock (fs_bytes γfs) b bs ∗ blk_own γfs b)%I.

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
     fsblock (fs_bytes γfs) bmapstart (bitmap_bytes used) ∗
     free_pool γfs size used)%I.

  Lemma bitmap_res_open (γfs : fs_names) (bms : Z) (cov : gset Z)
      (ls size : Z) (used : gset Z) :
    bitmap_res γfs bms cov ls size used -∗
      ⌜bitmap_ok cov ls size used⌝ ∗
      fsblock (fs_bytes γfs) bms (bitmap_bytes used) ∗
      free_pool γfs size used.
  Proof. iIntros "H". iExact "H". Qed.

  Lemma bitmap_res_close (γfs : fs_names) (bms : Z) (cov : gset Z)
      (ls size : Z) (used : gset Z) :
    bitmap_ok cov ls size used ->
    fsblock (fs_bytes γfs) bms (bitmap_bytes used) -∗
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

  (* the shape bfree's caller hands over: a block-sized content half plus
     the token *)
  Lemma free_blk_intro (γfs : fs_names) (b : Z) (bs : list (bv 8)) :
    length bs = BSIZE ->
    fsblock (fs_bytes γfs) b bs -∗ blk_own γfs b -∗ free_blk γfs b.
  Proof.
    iIntros (Hlen) "Hb Ho". rewrite /free_blk. iExists bs.
    iSplitR; [iPureIntro; exact Hlen|]. iFrame.
  Qed.


  (* ================================================================== *)
  (*  THE INVARIANT: who owns [bitmap_res] between calls                *)
  (* ================================================================== *)

  (* [bitmap_res] is EXCLUSIVE and there is one per file system, so it
     cannot be threaded through contracts: a holder of it would serialize
     every allocator and every freer in the kernel -- and a process carrying
     it across user mode would serialize user mode itself.  It lives here,
     in an Iris invariant, at an EXISTENTIAL set: nobody outside this file
     ever names the current [used], and no contract above balloc/bfree says
     anything about it.

     The shape is [InodeRegion]'s, verbatim, one layer over: the block's
     client half never leaves the invariant except at log_write's own ghost
     step.  A caller between bread and brelse holds the block's MACHINERY
     half in its handle, and that half against the parked client half is
     what tells it the bytes it read are [bitmap_bytes used] for SOME
     [used] -- [bitmap_read] below.  The one moment the client half is
     withdrawn is [SpecLogWrite.wp_log_write_au]'s fupd, and the two
     suppliers of that fupd are [bitmap_alloc_au] (set a bit, take the
     block out of the pool) and [bitmap_free_au] (clear a bit, put the block
     back).  Both re-park the block at the written bytes in the same
     opening, so the invariant is never open across an instruction.

     WHY THE SUPPLIERS ARE STATED AT THE CALLER'S SET.  The caller learned
     [bsl = bitmap_bytes u0] at its bread; by the time its log_write fires,
     the invariant parks SOME [u1] with [bitmap_bytes u1 = bsl] -- the
     machinery half in the handle froze the bytes, not the set.  The two
     need not be equal as sets (only below [BPB] do the bytes see them),
     and nothing downstream cares: [bitmap_bytes_eq_bit] transfers the one
     bit the caller tested, and [bitmap_bytes_ext] transfers the written
     image.  So each supplier takes the caller's [u0] and the caller's bit,
     and the [u1]-side bookkeeping stays inside this file. *)

  Global Instance bitmap_res_timeless γfs bms cov ls size used :
    Timeless (bitmap_res γfs bms cov ls size used).
  Proof. rewrite /bitmap_res /free_pool /free_blk /blk_own. apply _. Qed.

  Definition bitmapN : namespace := nroot .@ "bitmap".

  Definition bitmap_body (γfs : fs_names) (bms : Z) (cov : gset Z)
      (ls size : Z) : iProp Σ :=
    (∃ used : gset Z, bitmap_res γfs bms cov ls size used)%I.

  Global Instance bitmap_body_timeless γfs bms cov ls size :
    Timeless (bitmap_body γfs bms cov ls size).
  Proof. rewrite /bitmap_body. apply _. Qed.

  (* THE BYTE VIEW'S ROW RIDES HERE (durable-disk 1c-flip step 3).  The
     bitmap block and every free block are HOME blocks and are now owned as
     EXCLUSIVE byte runs, so a reader can no longer pin its bread bytes by
     an auth-free half/half agreement -- it opens [fs_bytes_inv].  Unlike
     [InodeRegion.ireg_inv] this invariant already carries [cov] and [ls],
     so the home set is NAMED here rather than bound, and the bitmap
     block's own membership rides beside it (nothing else states it: it is
     [bitmap_geom_ok]'s, and [bitmap_ok] speaks only about the blocks the
     pool holds). *)
  Definition bitmap_inv (γfs : fs_names) (bms : Z) (cov : gset Z)
      (ls size : Z) : iProp Σ :=
    (inv bitmapN (bitmap_body γfs bms cov ls size) ∗
     fs_bytes_inv (fs_bytes γfs) (fs_cache γfs) (fs_home_set cov ls))%I.

  Global Instance bitmap_inv_persistent γfs bms cov ls size :
    Persistent (bitmap_inv γfs bms cov ls size).
  Proof. rewrite /bitmap_inv. apply _. Qed.

  (* boot's one step: the image's bitmap, as built by
     [FsCfgBoot.bitmap_res_of_image], goes in and the set is forgotten *)
  Lemma bitmap_inv_alloc (E : coPset) (γfs : fs_names) (bms : Z)
      (cov : gset Z) (ls size : Z) (used : gset Z) :
    fs_bytes_inv (fs_bytes γfs) (fs_cache γfs) (fs_home_set cov ls) -∗
    bitmap_res γfs bms cov ls size used ={E}=∗
    bitmap_inv γfs bms cov ls size.
  Proof.
    iIntros "#Hbinv H".
    iMod (inv_alloc bitmapN E (bitmap_body γfs bms cov ls size)
            with "[H]") as "#Hi".
    { iNext. rewrite /bitmap_body. iExists used. iExact "H". }
    iModIntro. rewrite /bitmap_inv. iFrame "Hi Hbinv".
  Qed.

  (* the row at its NAMED home set -- what a client that has to build
     [LogInv.log_ctx] needs (fsinit, for initlog) *)
  Lemma bitmap_inv_bytes_at (γfs : fs_names) (bms : Z) (cov : gset Z)
      (ls size : Z) :
    bitmap_inv γfs bms cov ls size -∗
    fs_bytes_inv (fs_bytes γfs) (fs_cache γfs) (fs_home_set cov ls).
  Proof. iIntros "(_ & $)". Qed.

  Lemma bitmap_inv_bytes (γfs : fs_names) (bms : Z) (cov : gset Z)
      (ls size : Z) :
    bitmap_inv γfs bms cov ls size -∗ fs_bytes_any γfs.
  Proof.
    iIntros "(_ & Hb)". rewrite /fs_bytes_any.
    iExists (fs_home_set cov ls). iExact "Hb".
  Qed.

  (* [logN] and [bitmapN] are distinct namespaces *)
  Lemma logN_bitmapN_disj : (↑logN : coPset) ## ↑bitmapN.
  Proof. solve_ndisj. Qed.

  (* ---- the two pure bridges between the caller's set and the parked one *)

  Lemma bitmap_bytes_ext (u u' : gset Z) :
    (forall x : Z, 0 <= x < BPB -> (x ∈ u <-> x ∈ u')) ->
    bitmap_bytes u = bitmap_bytes u'.
  Proof.
    intros H. unfold bitmap_bytes, bm_bytes. apply list_eq. intros i.
    rewrite !list_lookup_fmap.
    destruct (seq 0 BSIZE !! i) as [j|] eqn:Hs; [|reflexivity].
    apply lookup_seq in Hs as [-> Hi]. simpl. f_equal.
    apply bm_byte_ext. intros k Hk. apply H. unfold BPB. lia.
  Qed.

  Lemma bitmap_bytes_eq_bit (u u' : gset Z) (bi : Z) :
    0 <= bi < BPB ->
    bitmap_bytes u = bitmap_bytes u' ->
    (bi ∈ u <-> bi ∈ u').
  Proof.
    intros Hbi Heq.
    assert (Hlt : (Z.to_nat (bi `div` 8) < BSIZE)%nat).
    { apply bit_byte_lt. unfold BPB in Hbi. lia. }
    pose proof (bitmap_bytes_lookup u _ Hlt) as H1.
    pose proof (bitmap_bytes_lookup u' _ Hlt) as H2.
    rewrite Heq in H1. rewrite H1 in H2.
    assert (Hb : bm_byte u (Z.of_nat (Z.to_nat (bi `div` 8)))
                 = bm_byte u' (Z.of_nat (Z.to_nat (bi `div` 8)))) by congruence.
    rewrite Z2Nat.id in Hb; [|apply Z.div_pos; lia].
    pose proof (bm_byte_testbit u (bi `div` 8) (bi `mod` 8)
                  (bit_off_range bi ltac:(lia))) as T1.
    pose proof (bm_byte_testbit u' (bi `div` 8) (bi `mod` 8)
                  (bit_off_range bi ltac:(lia))) as T2.
    rewrite bit_split in T1. rewrite bit_split in T2.
    rewrite Hb in T1. rewrite T1 in T2.
    split; intros Hin.
    - apply (bool_decide_unpack _). rewrite -T2. by apply bool_decide_pack.
    - apply (bool_decide_unpack _). rewrite T2. by apply bool_decide_pack.
  Qed.

  Lemma bitmap_bytes_eq_union (u u' : gset Z) (bi : Z) :
    bitmap_bytes u = bitmap_bytes u' ->
    bitmap_bytes (u ∪ {[bi]}) = bitmap_bytes (u' ∪ {[bi]}).
  Proof.
    intros Heq. apply bitmap_bytes_ext. intros x Hx.
    pose proof (bitmap_bytes_eq_bit u u' x Hx Heq) as Hb.
    rewrite !elem_of_union. tauto.
  Qed.

  Lemma bitmap_bytes_eq_diff (u u' : gset Z) (bi : Z) :
    bitmap_bytes u = bitmap_bytes u' ->
    bitmap_bytes (u ∖ {[bi]}) = bitmap_bytes (u' ∖ {[bi]}).
  Proof.
    intros Heq. apply bitmap_bytes_ext. intros x Hx.
    pose proof (bitmap_bytes_eq_bit u u' x Hx Heq) as Hb.
    rewrite !elem_of_difference. tauto.
  Qed.

  (* ---- the READ: one mask-preserving opening between bread and brelse *)

  (* The caller's handle carries the bitmap block's machinery half at the
     bytes bread returned; against the parked client half that pins the
     bytes to the image of SOME set, and [bitmap_ok] at that set is what the
     scan needs of a clear bit.  Everything goes back; only facts come out. *)
  Lemma bitmap_read (E : coPset) (γfs : fs_names) (bms : Z) (cov : gset Z)
      (ls size : Z) (bsl : list (bv 8)) :
    ↑bitmapN ⊆ E ->
    (* THE FLIP'S ONE ADDITION (durable-disk 1c-flip step 3): the parked
       resource is the block's EXCLUSIVE byte run, so pinning the caller's
       bread bytes is an OPEN of the byte view's invariant. *)
    ↑logN ⊆ E ->
    bitmap_inv γfs bms cov ls size -∗
    (bms ↪[fs_cache γfs]{#(1/2)} bsl) ={E}=∗
    ⌜exists used : gset Z,
       bsl = bitmap_bytes used /\ bitmap_ok cov ls size used⌝ ∗
    (bms ↪[fs_cache γfs]{#(1/2)} bsl).
  Proof.
    iIntros (HE HEl) "#Hinv Hhalf".
    iDestruct "Hinv" as "(#Hbi & #Hbinv)".
    assert (HlogB : (↑logN : coPset) ⊆ E ∖ ↑bitmapN)
      by (apply subseteq_difference_r; [apply logN_bitmapN_disj | exact HEl]).
    iMod (inv_acc E bitmapN with "Hbi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (used) "(>%Hok & >Hfsb & >Hpool)".
    iMod (fs_bytes_agree (E ∖ ↑bitmapN) (fs_bytes γfs) (fs_cache γfs)
            (fs_home_set cov ls) bms (bitmap_bytes used) bsl HlogB
            with "Hbinv Hfsb Hhalf") as "(%Hbytes & Hfsb & Hhalf)".
    iMod ("Hclose" with "[Hfsb Hpool]") as "_".
    { iNext. rewrite /bitmap_body. iExists used. rewrite /bitmap_res.
      iFrame. done. }
    iModIntro. iFrame "Hhalf". iPureIntro. exists used. auto.
  Qed.

  (* ...and bfree's read: the caller holds the block's token, so the bit is
     SET -- [free_pool_own_used] is the panic refutation, now stated where
     the pool lives. *)
  Lemma bitmap_read_own (E : coPset) (γfs : fs_names) (bms : Z) (cov : gset Z)
      (ls size : Z) (b : Z) (bsl : list (bv 8)) :
    ↑bitmapN ⊆ E ->
    (* see [bitmap_read] (durable-disk 1c-flip step 3) *)
    ↑logN ⊆ E ->
    0 <= b < size ->
    bitmap_inv γfs bms cov ls size -∗
    blk_own γfs b -∗
    (bms ↪[fs_cache γfs]{#(1/2)} bsl) ={E}=∗
    ⌜exists used : gset Z,
       bsl = bitmap_bytes used /\ bitmap_ok cov ls size used /\ b ∈ used⌝ ∗
    blk_own γfs b ∗
    (bms ↪[fs_cache γfs]{#(1/2)} bsl).
  Proof.
    iIntros (HE HEl Hb) "#Hinv Hown Hhalf".
    iDestruct "Hinv" as "(#Hbi & #Hbinv)".
    assert (HlogB : (↑logN : coPset) ⊆ E ∖ ↑bitmapN)
      by (apply subseteq_difference_r; [apply logN_bitmapN_disj | exact HEl]).
    iMod (inv_acc E bitmapN with "Hbi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (used) "(>%Hok & >Hfsb & >Hpool)".
    iMod (fs_bytes_agree (E ∖ ↑bitmapN) (fs_bytes γfs) (fs_cache γfs)
            (fs_home_set cov ls) bms (bitmap_bytes used) bsl HlogB
            with "Hbinv Hfsb Hhalf") as "(%Hbytes & Hfsb & Hhalf)".
    iDestruct (free_pool_own_used γfs size used b Hb with "Hown Hpool") as %Hin.
    iMod ("Hclose" with "[Hfsb Hpool]") as "_".
    { iNext. rewrite /bitmap_body. iExists used. rewrite /bitmap_res.
      iFrame. done. }
    iModIntro. iFrame "Hown Hhalf". iPureIntro. exists used. auto.
  Qed.

  (* ---- the two ATOMIC-UPDATE suppliers for [wp_log_write_au] ---- *)

  (* balloc's: the caller found bit [bi] clear in the bytes it read
     ([bi ∉ u0]), set it in the buffer, and log_writes.  The fupd surrenders
     the client half at whatever the invariant parks; log_write's own
     agreement delivers [bsl' = bitmap_bytes u0]; the closing wand takes the
     half back at the image of [u0 ∪ {[bi]}] and pays out the block --
     content half, token, and the two facts bread and log_write will demand
     of it.  [lw_au_lb0] is the adapter to the anchored shape. *)
  Lemma bitmap_alloc_au (E : coPset) (γfs : fs_names) (bms : Z) (cov : gset Z)
      (ls size : Z) (u0 : gset Z) (bi : Z) :
    ↑bitmapN ⊆ E ->
    size <= BPB ->
    0 <= bi < size ->
    bi ∉ u0 ->
    bitmap_inv γfs bms cov ls size -∗
    |={E, E ∖ ↑bitmapN}=> ∃ bsl' : list (bv 8),
      fsblock (fs_bytes γfs) bms bsl' ∗
      (⌜bsl' = bitmap_bytes u0⌝ -∗
       fsblock (fs_bytes γfs) bms (bitmap_bytes (u0 ∪ {[bi]})) ={E ∖ ↑bitmapN, E}=∗
       free_blk γfs bi ∗ ⌜bi ∈ cov /\ ~ (bi ∈ log_region_set ls)⌝).
  Proof.
    iIntros (HE Hsz Hbi Hnu) "#Hinv".
    iDestruct "Hinv" as "(#Hbi & #Hbinv)".
    iMod (inv_acc E bitmapN with "Hbi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (u1) "(>%Hok & >Hfsb & >Hpool)".
    iModIntro. iExists (bitmap_bytes u1). iFrame "Hfsb".
    iIntros (Hbytes) "Hfsb'".
    assert (Hnu1 : bi ∉ u1).
    { intros Hin. apply Hnu.
      apply (bitmap_bytes_eq_bit u1 u0 bi ltac:(lia) Hbytes). exact Hin. }
    iDestruct (free_pool_take γfs size u1 bi Hbi Hnu1 with "Hpool") as "[Hblk Hpool]".
    iMod ("Hclose" with "[Hfsb' Hpool]") as "_".
    { iNext. rewrite /bitmap_body. iExists (u1 ∪ {[bi]}). rewrite /bitmap_res.
      rewrite (bitmap_bytes_eq_union u0 u1 bi (eq_sym Hbytes)).
      iFrame. iPureIntro. apply bitmap_ok_add. exact Hok. }
    iModIntro. iFrame "Hblk". iPureIntro.
    exact (bitmap_ok_free cov ls size u1 bi Hok Hbi Hnu1).
  Qed.

  (* bfree's: the caller arrives with the block (content half and token),
     clears its bit in the buffer, and log_writes.  The block goes back into
     the pool in the same opening that re-parks the bitmap at the image of
     [u0 ∖ {[b]}].  Nothing comes out: the receipt is [emp]. *)
  Lemma bitmap_free_au (E : coPset) (γfs : fs_names) (bms : Z) (cov : gset Z)
      (ls size : Z) (u0 : gset Z) (b : Z) :
    ↑bitmapN ⊆ E ->
    0 <= b < size ->
    b ∈ cov ->
    ~ (b ∈ log_region_set ls) ->
    bitmap_inv γfs bms cov ls size -∗
    free_blk γfs b -∗
    |={E, E ∖ ↑bitmapN}=> ∃ bsl' : list (bv 8),
      fsblock (fs_bytes γfs) bms bsl' ∗
      (⌜bsl' = bitmap_bytes u0⌝ -∗
       fsblock (fs_bytes γfs) bms (bitmap_bytes (u0 ∖ {[b]})) ={E ∖ ↑bitmapN, E}=∗ emp).
  Proof.
    iIntros (HE Hb Hcov Hlog) "#Hinv Hblk".
    iDestruct "Hinv" as "(#Hbi & #Hbinv)".
    iMod (inv_acc E bitmapN with "Hbi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (u1) "(>%Hok & >Hfsb & >Hpool)".
    iModIntro. iExists (bitmap_bytes u1). iFrame "Hfsb".
    iIntros (Hbytes) "Hfsb'".
    iDestruct "Hblk" as (bs) "(%Hlen & Hb & Hown)".
    iDestruct (free_pool_own_used γfs size u1 b Hb with "Hown Hpool") as %Hin.
    iDestruct (free_pool_give γfs size u1 b Hb Hin with "[Hb Hown] Hpool") as "Hpool".
    { iApply (free_blk_intro with "Hb Hown"). exact Hlen. }
    iMod ("Hclose" with "[Hfsb' Hpool]") as "_".
    { iNext. rewrite /bitmap_body. iExists (u1 ∖ {[b]}). rewrite /bitmap_res.
      rewrite (bitmap_bytes_eq_diff u0 u1 b (eq_sym Hbytes)).
      iFrame. iPureIntro. apply bitmap_ok_del; assumption. }
    done.
  Qed.

End BitmapRes.

(* THE ALLOCATION-SIDE BUNDLE a caller of balloc carries, as ONE record and
   ONE iProp.  bmap's interior lemmas and writei's loop thread exactly this:
   one binder and one resource, rather than five of each.  Everything in it
   is pure, a fraction that goes straight back out, or the PERSISTENT
   [bitmap_inv], so it is invariant across the whole call. *)
Record bm_alloc := MkBmAlloc {
  ba_log  : log_names;   (* the log the reservation is against *)
  ba_bms  : Z;           (* sb.bmapstart *)
  ba_size : Z;           (* sb.size     *)
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
     bitmap_inv γfs (ba_bms a) cov logstart (ba_size a))%I.
End BitmapAllocRes.
