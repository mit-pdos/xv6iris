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

   [bitmap_res gfs bmapstart size used] IS [FsStateBitmap.free_bitmap_at],
   the design's free-space predicate (fs-state.md section 2), instantiated
   at the LOGGED view: [Gamma_L.fsPhi a v := a ↪[fs_bytes gfs] v], which is
   [FsBytesGamma.fs_gamma_L].  It is two things and no more:

     - the bitmap block itself, at [BitmapEnc.bm_bytes] of the pure set
       [used] -- the block content is always in the IMAGE of an encoding
       over a pure index set, so setting a bit is [used ∪ {[bi]}] and the
       byte level is only ever read back;
     - THE FREE POOL: for every block below [size] whose bit is CLEAR,
       THE BLOCK ITSELF, at content nobody has committed to.

   THERE IS NO PURE CLAUSE.  [bitmap_ok] ("every clear bit below [size]
   names a covered home block, outside the log's own storage") used to be a
   conjunct of the resource -- a MAINTAINED statement about the whole used
   set, which is exactly what fs-state.md section 0 forbids.  It is still
   stated, and every reader still gets it, but it is now DERIVED at each
   read rather than carried: HOLDING A BLOCK'S BYTE RUN IS BEING A HOME
   BLOCK ([FsBlocks.fsblock_home]), and the pool holds the run of every
   clear bit, so [bitmap_pool_home] reads the whole of [bitmap_ok] off the
   pool's OWNERSHIP against [bytes_dom].  Nothing establishes it, nothing
   preserves it, and no boot client owes it -- fs-state.md section 0's "a
   consequence of the [∗]", not a clause.  [x <> 0] still comes free from
   [cov_ok] at the caller.

   ---- WHY THE HANDSHAKE IS SOUND -------------------------------------

   Exclusivity of the byte run, and nothing else.  There is no per-block
   ownership token any more (durable-disk 2b; [FsBlocks.blk_own] is gone):

     - balloc hands out the block's EXCLUSIVE run, so a caller that keeps
       one per block its own structures name concludes the new block is
       none of them ([FsBlocks.fsblock_excl]) -- the fact that
       re-establishes [InodeInv.blkmap_wf]'s injectivity;
     - bfree's [panic("freeing free block")] is DEAD, and
       [FsStateBitmap.free_pool_used] is the proof: the caller arrives
       holding the block's run, so if the bit were CLEAR the pool would
       hold a SECOND run at the same block, and two owners of one block's
       bytes is [False].  Refuting that panic is the main thing this
       invariant has to buy.

   ---- WHO OWNS [bitmap_res] BETWEEN CALLS ----------------------------

   Nobody outside this file: it is exclusive and there is one per file
   system, so threading it through contracts would serialize every
   allocator and freer in the kernel.  It lives in the Iris invariant
   [bitmap_inv], at an EXISTENTIAL set no contract names.                *)

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
Require Import FsBytesGamma.   (* the byte view AS a [Gamma]; the bridge *)
Require Import FsStateBitmap.  (* [free_bitmap_at], the design predicate *)
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
(*  The pure READING of a bitmap -- derived, never maintained              *)
(* ===================================================================== *)

(* Every CLEAR bit below [size] names a usable client block.  This is what
   converts balloc's scan result into the two facts bread and log_write
   demand of a block number; [x <> 0] comes free from [cov_ok].  It is NOT a
   conjunct of [bitmap_res] and nothing preserves it: [bitmap_pool_home]
   below derives it, at each read, from the pool's ownership. *)
Definition bitmap_ok (cov : gset Z) (logstart size : Z) (used : gset Z) : Prop :=
  forall x : Z, 0 <= x < size -> x ∉ used ->
    x ∈ cov /\ ~ (x ∈ log_region_set logstart).

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

  (* ---- a free block ------------------------------------------------- *)

  (* what the pool holds for a clear bit, and what balloc hands out: the
     block's EXCLUSIVE byte run, at content nobody has committed to (the
     pool promises nothing about a free block's bytes; bzero is what makes
     the allocated one all-zero).  It is [FsStateBitmap.pool_elt]'s clear
     arm, read through the bridge. *)
  Definition free_blk (γfs : fs_names) (b : Z) : iProp Σ :=
    (∃ bs : list (bv 8), fsblock (fs_bytes γfs) b bs)%I.

  Lemma free_blk_intro (γfs : fs_names) (b : Z) (bs : list (bv 8)) :
    fsblock (fs_bytes γfs) b bs -∗ free_blk γfs b.
  Proof. iIntros "H". rewrite /free_blk. by iExists bs. Qed.

  Lemma free_blk_of_owned (γfs : fs_names) (b : Z) :
    (∃ bs, blk_owned (fs_gamma_L γfs) b bs) ⊣⊢ free_blk γfs b.
  Proof.
    rewrite /free_blk. iSplit.
    - iIntros "H". iDestruct "H" as (bs) "H". iExists bs.
      rewrite -gamma_blk_owned. iExact "H".
    - iIntros "H". iDestruct "H" as (bs) "H". iExists bs.
      rewrite gamma_blk_owned. iExact "H".
  Qed.

  (* ---- the resource -------------------------------------------------- *)

  (* THE DESIGN PREDICATE, at the logged view.  [cov]/[logstart] are gone
     from it: they only ever fed the deleted pure clause. *)
  Definition bitmap_res (γfs : fs_names) (bmapstart size : Z)
      (used : gset Z) : iProp Σ :=
    free_bitmap_at (fs_gamma_L γfs) bmapstart size used.

  Lemma bitmap_res_open (γfs : fs_names) (bms size : Z) (used : gset Z) :
    bitmap_res γfs bms size used ⊣⊢
      fsblock (fs_bytes γfs) bms (bitmap_bytes used)
      ∗ free_pool (fs_gamma_L γfs) size used.
  Proof.
    rewrite /bitmap_res /free_bitmap_at /bitmap_bytes gamma_blk_owned //.
  Qed.

  Global Instance bitmap_res_timeless γfs bms size used :
    Timeless (bitmap_res γfs bms size used).
  Proof. rewrite /bitmap_res. apply _. Qed.

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
     byte run never leaves the invariant except at log_write's own ghost
     step.  A caller between bread and brelse holds the block's MACHINERY
     half in its handle, and that half against the parked run is what tells
     it the bytes it read are [bitmap_bytes used] for SOME [used] --
     [bitmap_read] below.  The one moment the run is withdrawn is
     [SpecLogWrite.wp_log_write_au]'s fupd, and the two suppliers of that
     fupd are [bitmap_alloc_au] (set a bit, take the block out of the pool)
     and [bitmap_free_au] (clear a bit, put the block back).  Both re-park
     the block at the written bytes in the same opening, so the invariant is
     never open across an instruction.

     WHY THE SUPPLIERS ARE STATED AT THE CALLER'S SET.  The caller learned
     [bsl = bitmap_bytes u0] at its bread; by the time its log_write fires,
     the invariant parks SOME [u1] with [bitmap_bytes u1 = bsl] -- the
     machinery half in the handle froze the BYTES, not the set.  The two
     need not be equal as sets (only below [BPB] do the bytes see them),
     and nothing downstream cares: [bitmap_bytes_eq_bit] transfers the one
     bit the caller tested, and [bitmap_bytes_ext] transfers the written
     image.  So each supplier takes the caller's [u0] and the caller's bit,
     and the [u1]-side bookkeeping stays inside this file. *)

  Definition bitmapN : namespace := nroot .@ "bitmap".

  Definition bitmap_body (γfs : fs_names) (bms size : Z) : iProp Σ :=
    (∃ used : gset Z, bitmap_res γfs bms size used)%I.

  Global Instance bitmap_body_timeless γfs bms size :
    Timeless (bitmap_body γfs bms size).
  Proof. rewrite /bitmap_body. apply _. Qed.

  (* THE BYTE VIEW'S ROW RIDES HERE (durable-disk 1c-flip step 3).  The
     bitmap block and every free block are HOME blocks and are owned as
     EXCLUSIVE byte runs, so a reader pins its bread bytes by opening
     [fs_bytes_inv].  Unlike [InodeRegion.ireg_inv] this invariant already
     carries [cov] and [ls], so the home set is NAMED here rather than
     bound, and the bitmap block's own membership rides beside it
     ([bitmap_geom_ok]'s). *)
  Definition bitmap_inv (γfs : fs_names) (bms : Z) (cov : gset Z)
      (ls size : Z) : iProp Σ :=
    (inv bitmapN (bitmap_body γfs bms size) ∗
     fs_bytes_inv (fs_bytes γfs) (fs_cache γfs) (fs_home_set cov ls))%I.

  Global Instance bitmap_inv_persistent γfs bms cov ls size :
    Persistent (bitmap_inv γfs bms cov ls size).
  Proof. rewrite /bitmap_inv. apply _. Qed.

  (* boot's one step: the image's bitmap, as built by
     [FsCfgBoot.bitmap_res_of_image], goes in and the set is forgotten *)
  Lemma bitmap_inv_alloc (E : coPset) (γfs : fs_names) (bms : Z)
      (cov : gset Z) (ls size : Z) (used : gset Z) :
    fs_bytes_inv (fs_bytes γfs) (fs_cache γfs) (fs_home_set cov ls) -∗
    bitmap_res γfs bms size used ={E}=∗
    bitmap_inv γfs bms cov ls size.
  Proof.
    iIntros "#Hbinv H".
    iMod (inv_alloc bitmapN E (bitmap_body γfs bms size)
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

  (* ---- [bitmap_ok], READ OFF THE POOL ------------------------------- *)

  (* one block at a time, with the byte map's auth in hand: a clear bit
     means the pool owns that block's run, and holding a run IS being a home
     block ([FsBlocks.fsblock_home]).  The [∀] is a Coq quantifier over a
     PURE conclusion, so the pool is used once per instantiation and nothing
     is consumed -- the same shape as [InodeInv.inode_fresh]. *)
  Local Lemma pool_home_pure (γfs : fs_names) (L : gmap Z (bv 8))
      (home : gset Z) (size : Z) (u : gset Z) :
    bytes_dom L home ->
    ghost_map_auth (fs_bytes γfs) 1 L -∗
    free_pool (fs_gamma_L γfs) size u -∗
    ⌜forall x : Z, 0 <= x < size -> x ∉ u -> x ∈ home⌝.
  Proof.
    intros Hdm. iIntros "Ha Hpool".
    rewrite bi.pure_forall. iIntros (x).
    destruct (decide (0 <= x < size)) as [Hx|Hx];
      [| iPureIntro; intros Hc; exfalso; exact (Hx Hc)].
    destruct (decide (x ∈ u)) as [Hu|Hu];
      [ iPureIntro; intros _ Hc; exfalso; exact (Hc Hu) |].
    assert (Hx' : Z.of_nat (Z.to_nat x) = x) by lia.
    rewrite (free_pool_split (fs_gamma_L γfs) size u (Z.to_nat x)); [| lia].
    rewrite Hx' {1}/pool_elt (bool_decide_eq_false_2 _ Hu).
    iDestruct "Hpool" as "[Hb _]".
    iDestruct "Hb" as (bsx) "Hb".
    rewrite gamma_blk_owned.
    iDestruct (fsblock_home (fs_bytes γfs) L home x bsx Hdm with "Ha Hb") as %Hin.
    iPureIntro. intros _ _. exact Hin.
  Qed.

  (* ...and the whole of [bitmap_ok], in one opening of the byte view *)
  Lemma bitmap_pool_home (E : coPset) (γfs : fs_names) (home : gset Z)
      (size : Z) (u : gset Z) :
    ↑logN ⊆ E ->
    fs_bytes_inv (fs_bytes γfs) (fs_cache γfs) home -∗
    free_pool (fs_gamma_L γfs) size u ={E}=∗
      ⌜forall x : Z, 0 <= x < size -> x ∉ u -> x ∈ home⌝
      ∗ free_pool (fs_gamma_L γfs) size u.
  Proof.
    iIntros (HE) "#Hinv Hpool".
    iMod (inv_acc E logN with "Hinv") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (L C) ">(Ha & HC & %Hdom & %Hlens & %Htie & %Hdm)".
    iDestruct (pool_home_pure γfs L home size u Hdm with "Ha Hpool") as %Hres.
    iMod ("Hclose" with "[Ha HC]") as "_".
    { iNext. iExists L, C. by iFrame. }
    iModIntro. by iFrame.
  Qed.

  Lemma bitmap_ok_of_home (cov : gset Z) (ls size : Z) (u : gset Z) :
    (forall x : Z, 0 <= x < size -> x ∉ u -> x ∈ fs_home_set cov ls) ->
    bitmap_ok cov ls size u.
  Proof.
    intros H x Hx Hnu. specialize (H x Hx Hnu).
    rewrite /fs_home_set elem_of_difference in H. exact H.
  Qed.

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
     bytes bread returned; against the parked run that pins the bytes to the
     image of SOME set.  Everything goes back; only facts come out. *)
  Lemma bitmap_read (E : coPset) (γfs : fs_names) (bms : Z) (cov : gset Z)
      (ls size : Z) (bsl : list (bv 8)) :
    ↑bitmapN ⊆ E ->
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
    iDestruct "Hbody" as (used) ">Hres".
    rewrite bitmap_res_open. iDestruct "Hres" as "[Hfsb Hpool]".
    iMod (fs_bytes_agree (E ∖ ↑bitmapN) (fs_bytes γfs) (fs_cache γfs)
            (fs_home_set cov ls) bms (bitmap_bytes used) bsl HlogB
            with "Hbinv Hfsb Hhalf") as "(%Hbytes & Hfsb & Hhalf)".
    iMod (bitmap_pool_home (E ∖ ↑bitmapN) γfs (fs_home_set cov ls) size used
            HlogB with "Hbinv Hpool") as "(%Hhome & Hpool)".
    iMod ("Hclose" with "[Hfsb Hpool]") as "_".
    { iNext. rewrite /bitmap_body. iExists used. rewrite bitmap_res_open.
      iFrame. }
    iModIntro. iFrame "Hhalf". iPureIntro. exists used.
    split; [exact Hbytes | exact (bitmap_ok_of_home cov ls size used Hhome)].
  Qed.

  (* ...and bfree's read: the caller holds the block's own byte run, so the
     bit is SET -- [FsStateBitmap.free_pool_used] is the panic refutation,
     and it is exclusivity, not a clause. *)
  Lemma bitmap_read_own (E : coPset) (γfs : fs_names) (bms : Z) (cov : gset Z)
      (ls size : Z) (b : Z) (bs bsl : list (bv 8)) :
    ↑bitmapN ⊆ E ->
    ↑logN ⊆ E ->
    0 <= b < size ->
    bitmap_inv γfs bms cov ls size -∗
    fsblock (fs_bytes γfs) b bs -∗
    (bms ↪[fs_cache γfs]{#(1/2)} bsl) ={E}=∗
    ⌜exists used : gset Z,
       bsl = bitmap_bytes used /\ bitmap_ok cov ls size used /\ b ∈ used⌝ ∗
    fsblock (fs_bytes γfs) b bs ∗
    (bms ↪[fs_cache γfs]{#(1/2)} bsl).
  Proof.
    iIntros (HE HEl Hb) "#Hinv Hown Hhalf".
    iDestruct "Hinv" as "(#Hbi & #Hbinv)".
    assert (HlogB : (↑logN : coPset) ⊆ E ∖ ↑bitmapN)
      by (apply subseteq_difference_r; [apply logN_bitmapN_disj | exact HEl]).
    iMod (inv_acc E bitmapN with "Hbi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (used) ">Hres".
    rewrite bitmap_res_open. iDestruct "Hres" as "[Hfsb Hpool]".
    iMod (fs_bytes_agree (E ∖ ↑bitmapN) (fs_bytes γfs) (fs_cache γfs)
            (fs_home_set cov ls) bms (bitmap_bytes used) bsl HlogB
            with "Hbinv Hfsb Hhalf") as "(%Hbytes & Hfsb & Hhalf)".
    iEval (rewrite -gamma_blk_owned) in "Hown".
    iDestruct (free_pool_used (fs_gamma_L γfs) (fs_gamma_L_excl γfs)
                 size used b bs Hb with "Hpool Hown") as %Hin.
    iEval (rewrite gamma_blk_owned) in "Hown".
    iMod (bitmap_pool_home (E ∖ ↑bitmapN) γfs (fs_home_set cov ls) size used
            HlogB with "Hbinv Hpool") as "(%Hhome & Hpool)".
    iMod ("Hclose" with "[Hfsb Hpool]") as "_".
    { iNext. rewrite /bitmap_body. iExists used. rewrite bitmap_res_open.
      iFrame. }
    iModIntro. iFrame "Hown Hhalf". iPureIntro. exists used.
    split; [exact Hbytes |].
    split; [exact (bitmap_ok_of_home cov ls size used Hhome) | exact Hin].
  Qed.

  (* ---- the two ATOMIC-UPDATE suppliers for [wp_log_write_au] ---- *)

  (* balloc's: the caller found bit [bi] clear in the bytes it read
     ([bi ∉ u0]), set it in the buffer, and log_writes.  The fupd surrenders
     the bitmap block's run at whatever the invariant parks; log_write's own
     agreement delivers [bsl' = bitmap_bytes u0]; the closing wand takes the
     run back at the image of [u0 ∪ {[bi]}] and pays out THE BLOCK -- its
     byte run, AND NOTHING ELSE.  The two facts bread and log_write demand
     of the block number are not here: the caller learned them at its
     [bitmap_read], where they are read off the pool's ownership rather than
     off any clause.  [lw_au_lb0] is the adapter to the anchored shape. *)
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
       free_blk γfs bi).
  Proof.
    iIntros (HE Hsz Hbi Hnu) "#Hinv".
    iDestruct "Hinv" as "(#Hbmi & #Hbinv)".
    iMod (inv_acc E bitmapN with "Hbmi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (u1) ">Hres".
    rewrite bitmap_res_open. iDestruct "Hres" as "[Hfsb Hpool]".
    iModIntro. iExists (bitmap_bytes u1). iFrame "Hfsb".
    iIntros (Hbytes) "Hfsb'".
    assert (Hnu1 : bi ∉ u1).
    { intros Hin. apply Hnu.
      apply (bitmap_bytes_eq_bit u1 u0 bi ltac:(lia) Hbytes). exact Hin. }
    rewrite (free_pool_take (fs_gamma_L γfs) size u1 bi Hbi Hnu1).
    iDestruct "Hpool" as "[Hblk Hpool]".
    iMod ("Hclose" with "[Hfsb' Hpool]") as "_".
    { iNext. rewrite /bitmap_body. iExists (u1 ∪ {[bi]}).
      rewrite bitmap_res_open.
      rewrite (bitmap_bytes_eq_union u0 u1 bi (eq_sym Hbytes)). iFrame. }
    iModIntro. rewrite -free_blk_of_owned. iExact "Hblk".
  Qed.

  (* bfree's: the caller arrives with the block's byte run, clears its bit
     in the buffer, and log_writes.  The block goes back into the pool in
     the same opening that re-parks the bitmap at the image of [u0 ∖ {[b]}].
     Nothing comes out: the receipt is [emp].  The caller supplies no
     covered-ness premise -- the pool takes the block back wherever it came
     from, and the bit's being SET is [free_pool_used]'s exclusivity
     argument inside. *)
  Lemma bitmap_free_au (E : coPset) (γfs : fs_names) (bms : Z) (cov : gset Z)
      (ls size : Z) (u0 : gset Z) (b : Z) :
    ↑bitmapN ⊆ E ->
    0 <= b < size ->
    bitmap_inv γfs bms cov ls size -∗
    free_blk γfs b -∗
    |={E, E ∖ ↑bitmapN}=> ∃ bsl' : list (bv 8),
      fsblock (fs_bytes γfs) bms bsl' ∗
      (⌜bsl' = bitmap_bytes u0⌝ -∗
       fsblock (fs_bytes γfs) bms (bitmap_bytes (u0 ∖ {[b]})) ={E ∖ ↑bitmapN, E}=∗ emp).
  Proof.
    iIntros (HE Hb) "#Hinv Hblk".
    iDestruct "Hinv" as "(#Hbmi & #Hbinv)".
    iMod (inv_acc E bitmapN with "Hbmi") as "[Hbody Hclose]"; [exact HE |].
    iDestruct "Hbody" as (u1) ">Hres".
    rewrite bitmap_res_open. iDestruct "Hres" as "[Hfsb Hpool]".
    iModIntro. iExists (bitmap_bytes u1). iFrame "Hfsb".
    iIntros (Hbytes) "Hfsb'".
    iDestruct "Hblk" as (bsx) "Hblk".
    iEval (rewrite -gamma_blk_owned) in "Hblk".
    iDestruct (free_pool_give (fs_gamma_L γfs) (fs_gamma_L_excl γfs)
                 size u1 b bsx Hb with "Hblk Hpool") as "Hpool".
    iMod ("Hclose" with "[Hfsb' Hpool]") as "_".
    { iNext. rewrite /bitmap_body. iExists (u1 ∖ {[b]}).
      rewrite bitmap_res_open.
      rewrite (bitmap_bytes_eq_diff u0 u1 b (eq_sym Hbytes)). iFrame. }
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
