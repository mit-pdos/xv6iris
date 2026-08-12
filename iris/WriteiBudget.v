(* WriteiBudget.v -- THE LOG BUDGET writei ACTUALLY COSTS, and the ledger
   algebra that lets a loop carry it.

   ==== WHY THIS FILE EXISTS ============================================

   [SpecWritei.wi_cost off n = 6 * wi_blocks off n + 1] is a WORST-CASE
   over-approximation: it charges bmap's five (two ballocs at two units
   each, plus bmap's own log_write) for every straddled block, plus
   iupdate's one.  For dirlink -- sixteen bytes at a sixteen-aligned
   offset, so one block -- that is 7 and fits.  For the chunk filewrite's
   own code hands writei ([n1 = min(n - i, max)] with
   [max = ((MAXOPBLOCKS-1-1-2)/2)*BSIZE = 3072]) it is 13..25 against a
   [begin_op] grant of [MAXOPBLOCKS = 10], and NO chunk spanning more than
   one block is payable.  That is filewrite's last blocker.

   The over-approximation is not the code's fault.  The three facts it
   ignores are all already in the tree:

   1. THERE IS EXACTLY ONE BITMAP BLOCK.  [BitmapInv.bitmap_geom_ok] --
      a premise of balloc, bmap, writei and dirlink alike -- contains
      [0 < size <= BPB] with [BPB = 8192], so [BitmapInv.BBLOCK] collapses
      to [bmapstart] for EVERY allocatable block ([one_bitmap_block]
      below).  All five ballocs of a four-block chunk log_write the SAME
      block.  This is the fact the S3i sizing missed, and it is why the
      honest cost is [B + 3] and not [2B + 3].
   2. THE INDIRECT BLOCK IS ALLOCATED AT MOST ONCE PER FILE, and bmap's own
      [log_write(bp)] on the indirect path writes the very block balloc's
      [bzero] just wrote.
   3. balloc's [bzero] LOG_WRITES THE FRESH DATA BLOCK, and writei then
      log_writes THE SAME BLOCK.  The log absorbs the second.

   All three are ABSORPTIONS, and [LogInv] already models absorption: an
   op's ledger entry carries the set of blocks it has appended in this
   batch ([LogInv.log_opS]), [SpecLogWrite]'s credited arm hands the unit
   straight back when the block is in that set, and [LogInv.op_sum_absorb]
   is what keeps the header's sum tie inductive across it.  Nothing new is
   needed at the invariant level -- only a way for a LOOP to carry "these
   particular blocks are paid for" without case-splitting on how many
   iterations have run.  [SpecItrunc.bm_paid] is that shape for ONE block;
   [log_amort] below is it for a SET, which is what writei needs (the
   bitmap block AND the indirect block).

   ==== THE ALGEBRA =====================================================

   [log_amort γ F u] reads

       "u units are genuinely free, AND one unit is still held back for
        each block of F this op has not yet logged."

   as the potential function [u + size (F ∖ Sb) <= v] over the op's real
   remaining budget [v] and its real already-logged set [Sb].  It is
   IDEMPOTENT under a log_write of a block of F ([log_amort_present]):
   from the unpaid state the unit is spent and the block joins Sb, so the
   potential is unchanged; from the paid state log_write's credited arm
   absorbs and the unit comes back.  Either way [u] does not move, so a
   loop invariant mentions [log_amort γ F u] and never splits on which
   iteration happened to be the first to touch the bitmap.

   [log_amort_spend] is the other half: a log_write of a block OUTSIDE F
   costs one unit of [u], which is exactly the per-data-block charge.

   [log_amort_adopt] is what lets F GROW at the moment balloc returns the
   indirect block: enlarging F by a block that is already in Sb leaves the
   potential untouched, so writei can enter its loop reserving capacity for
   an indirect block whose identity it does not yet know.

   ==== THE RESULTING BUDGET ============================================

   [wi_cost_tight off n = wi_blocks off n + 3]: one unit per straddled data
   block, plus one each for the bitmap block, the indirect block and the
   inode block iupdate flushes.  [wi_cost_tight_fits] is the theorem that
   matters -- for any chunk of at most 3072 bytes, at ANY offset, it is at
   most MAXOPBLOCKS.  The worst case the code can produce is 7 of the 10
   begin_op pays, and dirlink's site drops from 7 to 4.

   [wi_logset_size] is the honest statement of WHY: the whole transaction's
   write set is the B data blocks plus three, whatever the interleaving.

   The two accountings recorded at the bottom ([wi_cost_armaware],
   [wi_cost_noabs]) are the intermediate repairs sized in the S3i ledger,
   both of which STILL bust 10 -- kept as machine-checked evidence that all
   three absorptions are load-bearing and none may be dropped.

   NOTHING HERE IS A STATEMENT CHANGE.  This file is additive: no existing
   contract mentions it, and [SpecWritei.wi_cost] is untouched.  It is the
   seam the writei/bmap/balloc retrofit plugs into. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import auth gmap frac.
From iris.base_logic.lib Require Import ghost_map.
Require Import FsCrash.       (* BSIZE *)
Require Import InodeInv.      (* NDIRECT, NINDIRECT, MAXFILE *)
Require Import LogInv.        (* MAXOPBLOCKS, log_op, log_opS *)
Require Import BitmapInv.     (* BPB, bitmap_geom_ok, BBLOCK *)
Require Import SpecWritei.    (* wi_blocks, wi_cost *)

Local Open Scope Z_scope.

(* ===================================================================== *)
(*  1. THE CHUNK THE CODE HANDS writei                                    *)
(* ===================================================================== *)

(* filewrite's own [max], spelled from the constants rather than as 3072 so
   that it moves if MAXOPBLOCKS ever does:
     max = ((MAXOPBLOCKS - 1 - 1 - 2) / 2) * BSIZE
   -- xv6's reading of its own budget: "one slot for the inode, one for the
   indirect, two spare, and the rest two per data block". *)
Definition FW_MAX : nat := (((MAXOPBLOCKS - 1 - 1 - 2) / 2) * BSIZE)%nat.

Lemma fw_max_value : FW_MAX = 3072%nat.
Proof. vm_compute. reflexivity. Qed.

(* A CHUNK OF AT MOST [FW_MAX] BYTES STRADDLES AT MOST FOUR BLOCKS.  Four,
   not three: [f->off] need not be block-aligned (it advances by whatever
   the last short write returned), so a 3072-byte chunk at an offset of
   1023 covers a tail, two whole blocks and a head. *)
Lemma wi_blocks_le4 (off n : nat) : (n <= FW_MAX)%nat -> (wi_blocks off n <= 4)%nat.
Proof.
  rewrite fw_max_value. intros Hn. unfold wi_blocks.
  assert (Hm : (off `mod` BSIZE < BSIZE)%nat)
    by (apply Nat.mod_upper_bound; unfold BSIZE; lia).
  assert (Hlt : ((off `mod` BSIZE + n + BSIZE - 1) `div` BSIZE < 5)%nat).
  { apply Nat.div_lt_upper_bound; unfold BSIZE in *; lia. }
  lia.
Qed.

(* ...and four IS reached, so no proof may assume three. *)
Lemma wi_blocks_four_reached : wi_blocks 1023 FW_MAX = 4%nat.
Proof. vm_compute. reflexivity. Qed.

(* dirlink's site, for contrast: sixteen bytes at a sixteen-aligned offset
   never leave one block.  This is why no caller before filewrite met the
   blocker. *)
Lemma wi_blocks_dirlink (k : nat) : (k < 64)%nat -> wi_blocks (16 * k) 16 = 1%nat.
Proof.
  intros Hk. unfold wi_blocks.
  assert (Hs : ((16 * k) `mod` BSIZE = 16 * k)%nat).
  { apply Nat.mod_small. unfold BSIZE. lia. }
  rewrite Hs.
  assert (H1 : (1 <= (16 * k + 16 + BSIZE - 1) `div` BSIZE)%nat).
  { apply Nat.div_le_lower_bound; unfold BSIZE; lia. }
  assert (H2 : ((16 * k + 16 + BSIZE - 1) `div` BSIZE < 2)%nat).
  { apply Nat.div_lt_upper_bound; unfold BSIZE; lia. }
  lia.
Qed.

(* THE BLOCKER, as an arithmetic fact.  The current contract's premise is
   unsatisfiable from a single begin_op for the code's own chunk. *)
Lemma wi_cost_loose_value : wi_cost 1023 FW_MAX = 25%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma wi_cost_loose_busts : (MAXOPBLOCKS < wi_cost 1023 FW_MAX)%nat.
Proof. vm_compute. lia. Qed.

(* ===================================================================== *)
(*  2. ONE BITMAP BLOCK                                                   *)
(* ===================================================================== *)

(* Every balloc of the whole transaction -- the indirect one and all four
   data ones -- log_writes [bmapstart].  [bitmap_geom_ok] is already a
   premise of balloc, bmap, writei and dirlink, so this costs no caller
   anything new. *)
Lemma one_bitmap_block (cov : gset Z) (logstart bmapstart fssize b : Z) :
  bitmap_geom_ok cov logstart bmapstart fssize ->
  0 <= b < fssize ->
  BBLOCK b bmapstart = bmapstart.
Proof.
  intros (Hs & _ & _ & _) Hb. apply BBLOCK_single.
  pose proof BPB_value. lia.
Qed.

(* ===================================================================== *)
(*  3. THE TRANSACTION'S WRITE SET                                        *)
(* ===================================================================== *)

Lemma gset_size_union_le (X Y : gset Z) : (size (X ∪ Y) <= size X + size Y)%nat.
Proof.
  rewrite size_union_alt.
  assert (Hs : Y ∖ X ⊆ Y) by set_solver.
  pose proof (subseteq_size _ _ Hs). lia.
Qed.

Lemma size_list_to_set_le (l : list Z) :
  (size (list_to_set l : gset Z) <= length l)%nat.
Proof.
  induction l as [|x l IH].
  - cbn [length]. change (list_to_set [] : gset Z) with (∅ : gset Z).
    rewrite size_empty. lia.
  - cbn [length].
    change (list_to_set (x :: l) : gset Z)
      with ({[x]} ∪ (list_to_set l : gset Z)).
    etrans; [apply gset_size_union_le|]. rewrite size_singleton. lia.
Qed.

(* THE DISTINCT BLOCKS one writei call log_writes:

     - the [dblks] data blocks the range straddles;
     - [bmapstart], the single bitmap block (section 2);
     - the indirect block, at most one per file;
     - [IBLOCK inum inodestart], iupdate's flush.

   EVERY log_write of the call writes one of these.  In particular
   balloc's bzero of a fresh data block and writei's own log_write of that
   block are the same block, as are balloc's bzero of the indirect block
   and bmap's own log_write of it.  The bound holds whether or not the four
   groups are disjoint -- coincidences only shrink the set. *)
Definition wi_logset (bmapstart indblk inoblk : Z) (dblks : list Z) : gset Z :=
  {[bmapstart]} ∪ {[indblk]} ∪ {[inoblk]} ∪ list_to_set dblks.

Lemma wi_logset_size (bmapstart indblk inoblk : Z) (dblks : list Z) :
  (size (wi_logset bmapstart indblk inoblk dblks) <= 3 + length dblks)%nat.
Proof.
  unfold wi_logset.
  etrans; [apply gset_size_union_le|].
  pose proof (size_list_to_set_le dblks) as Hl.
  assert (H3 : (size ({[bmapstart]} ∪ {[indblk]} ∪ {[inoblk]} : gset Z) <= 3)%nat).
  { etrans; [apply gset_size_union_le|].
    assert (H2 : (size ({[bmapstart]} ∪ {[indblk]} : gset Z) <= 2)%nat).
    { etrans; [apply gset_size_union_le|]. rewrite !size_singleton. lia. }
    rewrite size_singleton. lia. }
  lia.
Qed.

(* THE SOUNDNESS VERDICT: xv6's own chunk formula fits its own MAXOPBLOCKS,
   with three slots to spare. *)
Lemma wi_logset_fits (bmapstart indblk inoblk : Z) (dblks : list Z) :
  (length dblks <= 4)%nat ->
  (size (wi_logset bmapstart indblk inoblk dblks) <= MAXOPBLOCKS)%nat.
Proof.
  intros Hd. pose proof (wi_logset_size bmapstart indblk inoblk dblks).
  unfold MAXOPBLOCKS. lia.
Qed.

(* ===================================================================== *)
(*  4. THE TIGHT BUDGET                                                   *)
(* ===================================================================== *)

(* one unit per straddled data block, plus one each for the bitmap block,
   the indirect block and the inode block *)
Definition wi_cost_tight (off n : nat) : nat := (wi_blocks off n + 3)%nat.

(* THE THEOREM THAT UNBLOCKS filewrite: a single begin_op pays for any
   chunk the code can hand writei, at ANY offset. *)
Lemma wi_cost_tight_fits (off n : nat) :
  (n <= FW_MAX)%nat -> (wi_cost_tight off n <= MAXOPBLOCKS)%nat.
Proof.
  intros Hn. unfold wi_cost_tight.
  pose proof (wi_blocks_le4 off n Hn). unfold MAXOPBLOCKS. lia.
Qed.

Lemma wi_cost_tight_worst : wi_cost_tight 1023 FW_MAX = 7%nat.
Proof. vm_compute. reflexivity. Qed.

(* dirlink's one consumer site drops from 7 to 4 -- it holds the tight
   premise wherever it held the loose one, so the statement change costs
   that proof nothing. *)
Lemma wi_cost_tight_dirlink (k : nat) :
  (k < 64)%nat -> wi_cost_tight (16 * k) 16 = 4%nat.
Proof.
  intros Hk. unfold wi_cost_tight. rewrite (wi_blocks_dirlink k Hk). reflexivity.
Qed.

(* THE TIGHT FORM IS NOT POINTWISE BELOW THE LOOSE ONE, and that is worth
   knowing before the [SpecWritei] premise is reshaped: the two are
   incomparable at [wi_blocks = 0].

   [wi_cost 0 0 = 1] -- the loose form charges only iupdate, because a
   zero-block call runs no loop iteration -- while [wi_cost_tight 0 0 = 3],
   because the bitmap and indirect capacities are reserved unconditionally.
   So the reshaped premise is a STRENGTHENING on the empty-range arm and a
   large weakening everywhere else, and every consumer has to be re-checked
   rather than waved through as "the premise got cheaper".

   In practice nothing is hurt: a caller holding begin_op's 10 has 3, and
   writei's only in-tree consumer (dirlink) is at [wi_blocks = 1], where
   the tight form is 4 against the loose 7.  Reserving unconditionally is
   what keeps the loop invariant free of a case split on whether any block
   was straddled at all. *)
Lemma wi_cost_tight_le_loose (off n : nat) :
  (1 <= wi_blocks off n)%nat -> (wi_cost_tight off n <= wi_cost off n)%nat.
Proof. intros H. unfold wi_cost_tight, wi_cost. lia. Qed.

Lemma wi_cost_tight_incomparable : (wi_cost 0 0 < wi_cost_tight 0 0)%nat.
Proof. vm_compute. lia. Qed.

(* ===================================================================== *)
(*  5. ALL THREE ABSORPTIONS ARE LOAD-BEARING                             *)
(* ===================================================================== *)

(* (1) alone -- an arm-aware bmap budget, no absorption modelled at all:
   per block, balloc's two plus bmap's own log_write plus writei's own;
   per call, the indirect balloc's two plus iupdate's one. *)
Definition wi_cost_armaware (off n : nat) : nat := (4 * wi_blocks off n + 3)%nat.

Lemma wi_cost_armaware_value : wi_cost_armaware 1023 FW_MAX = 19%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma wi_cost_armaware_busts : (MAXOPBLOCKS < wi_cost_armaware 1023 FW_MAX)%nat.
Proof. vm_compute. lia. Qed.

(* (1)+(2) but WITHOUT the data-block absorption -- balloc's bzero of the
   fresh block and writei's own log_write of it charged separately. *)
Definition wi_cost_noabs (off n : nat) : nat := (2 * wi_blocks off n + 3)%nat.

Lemma wi_cost_noabs_value : wi_cost_noabs 1023 FW_MAX = 11%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma wi_cost_noabs_busts : (MAXOPBLOCKS < wi_cost_noabs 1023 FW_MAX)%nat.
Proof. vm_compute. lia. Qed.

(* ...and it DOES fit for a three-block chunk, which is what xv6's [max]
   formula was derived for.  The FOURTH block -- reachable only because
   [f->off] is unaligned -- is what eats the two spare slots.  So the
   fourth block is exactly the reason the data-block absorption cannot be
   left out. *)
Lemma wi_cost_noabs_three_fits : (wi_cost_noabs 0 FW_MAX <= MAXOPBLOCKS)%nat.
Proof. vm_compute. lia. Qed.

(* ===================================================================== *)
(*  6. THE LEDGER ALGEBRA -- AN AMORTISED SET OF BLOCKS                   *)
(* ===================================================================== *)

Section LogAmort.
  Context `{!logG Σ}.

  (* "u units are genuinely free, and one unit is still held back for each
     block of F this op has not yet logged."

     [v] is the op's real remaining budget and [Sb] its real already-logged
     set; both are existential, because no caller can know either.  The
     potential [u + size (F ∖ Sb)] is what stays put across a log_write of
     a block of F, which is what makes a loop invariant possible. *)
  Definition log_amort (γ : log_names) (F : gset Z) (u : nat) : iProp Σ :=
    (∃ (Sb : gset Z) (v : nat),
       ⌜(u + size (F ∖ Sb) <= v)%nat⌝ ∗ log_opS γ v Sb)%I.

  Global Instance log_amort_timeless γ F u : Timeless (log_amort γ F u).
  Proof. rewrite /log_amort. apply _. Qed.

  (* ENTERING: a caller with [u + size F] units in hand and no credits at
     all can reserve F.  This is the worst case -- every block of F still
     to be paid for. *)
  Lemma log_amort_intro γ F u v :
    (u + size F <= v)%nat -> log_op γ v -∗ log_amort γ F u.
  Proof.
    iIntros (Hv) "H". rewrite /log_op /log_amort.
    iDestruct "H" as (Sb) "H". iExists Sb, v. iFrame.
    iPureIntro.
    assert (Hsub : F ∖ Sb ⊆ F) by set_solver.
    pose proof (subseteq_size _ _ Hsub). lia.
  Qed.

  (* LEAVING: at least the [u] free units are really there.  A callee that
     wants the counted form (iupdate, end_op) takes this. *)
  Lemma log_amort_elim γ F u :
    log_amort γ F u -∗ ∃ v : nat, ⌜(u <= v)%nat⌝ ∗ log_op γ v.
  Proof.
    iIntros "H". rewrite /log_amort. iDestruct "H" as (Sb v) "(%Hv & H)".
    iExists v. iSplitR; [iPureIntro; lia|]. iApply (log_opS_op with "H").
  Qed.

  (* the two monotonicities: fewer free units is weaker, and RESERVING
     FEWER BLOCKS is weaker (F is capacity held back, not a claim) *)
  Lemma log_amort_weaken γ F u u' :
    (u' <= u)%nat -> log_amort γ F u -∗ log_amort γ F u'.
  Proof.
    iIntros (Hu) "H". rewrite /log_amort. iDestruct "H" as (Sb v) "(%Hv & H)".
    iExists Sb, v. iFrame. iPureIntro. lia.
  Qed.

  Lemma log_amort_shrink γ F F' u :
    F' ⊆ F -> log_amort γ F u -∗ log_amort γ F' u.
  Proof.
    iIntros (HF) "H". rewrite /log_amort. iDestruct "H" as (Sb v) "(%Hv & H)".
    iExists Sb, v. iFrame. iPureIntro.
    assert (Hsub : F' ∖ Sb ⊆ F ∖ Sb) by set_solver.
    pose proof (subseteq_size _ _ Hsub). lia.
  Qed.

  (* PRESENTING A BLOCK OF F to log_write.  IDEMPOTENT: [u] is the same on
     the way in and on the way out, whichever arm runs.

     - the block is already logged ([b ∈ Sb]): the credited arm absorbs and
       the unit comes back, so the potential cannot have moved;
     - it is not: the uncredited arm spends the unit, but [b] joins Sb and
       the held-back term drops by exactly one.

     The [S u] shape is what guarantees log_write's own "a unit must be in
     hand either way" premise is satisfiable even when every block of F is
     already paid for. *)
  Lemma log_amort_present γ F u (b : Z) :
    b ∈ F ->
    log_amort γ F (S u) -∗
    ∃ (Sb : gset Z) (v : nat) (cr : bool),
      ⌜cr = true -> b ∈ Sb⌝ ∗
      log_opS γ (S v) Sb ∗
      (log_opS γ (if cr then S v else v) (Sb ∪ {[b]}) -∗ log_amort γ F (S u)).
  Proof.
    iIntros (HbF) "H". rewrite /log_amort.
    iDestruct "H" as (Sb v) "(%Hv & H)".
    destruct (decide (b ∈ Sb)) as [Hin|Hout].
    - (* PAID: absorb.  v >= S u >= 1, so v = S (v - 1). *)
      destruct v as [|v']; [lia|].
      iExists Sb, v', true. iSplitR; [iPureIntro; done|]. iFrame "H".
      iIntros "H". iExists (Sb ∪ {[b]}), (S v'). iFrame.
      iPureIntro.
      assert (Hsub : F ∖ (Sb ∪ {[b]}) ⊆ F ∖ Sb) by set_solver.
      pose proof (subseteq_size _ _ Hsub). lia.
    - (* UNPAID: spend.  [b] is in [F ∖ Sb], so that set shrinks strictly. *)
      assert (Hb : b ∈ F ∖ Sb) by set_solver.
      assert (Hne : (1 <= size (F ∖ Sb))%nat).
      { assert (Hs : {[b]} ⊆ F ∖ Sb) by set_solver.
        pose proof (subseteq_size _ _ Hs). rewrite size_singleton in H. lia. }
      destruct v as [|v']; [lia|].
      iExists Sb, v', false. iSplitR; [iPureIntro; discriminate|]. iFrame "H".
      iIntros "H". iExists (Sb ∪ {[b]}), v'. iFrame.
      iPureIntro.
      assert (Hsub : F ∖ (Sb ∪ {[b]}) ⊂ F ∖ Sb) by set_solver.
      pose proof (subset_size _ _ Hsub). lia.
  Qed.

  (* SPENDING ON A BLOCK OUTSIDE F: one genuine unit of [u].  This is the
     per-data-block charge, and the block it logs may be anything -- the
     conclusion is stated over an arbitrary larger set so that a callee
     which logged more blocks than the one asked for still re-establishes
     the invariant. *)
  Lemma log_amort_spend γ F u :
    log_amort γ F (S u) -∗
    ∃ (Sb : gset Z) (v : nat),
      log_opS γ (S v) Sb ∗
      (∀ Sb' : gset Z, ⌜Sb ⊆ Sb'⌝ -∗ log_opS γ v Sb' -∗ log_amort γ F u).
  Proof.
    iIntros "H". rewrite /log_amort. iDestruct "H" as (Sb v) "(%Hv & H)".
    destruct v as [|v']; [lia|].
    iExists Sb, v'. iFrame "H".
    iIntros (Sb') "%Hsub H". iExists Sb', v'. iFrame.
    iPureIntro.
    assert (Hs : F ∖ Sb' ⊆ F ∖ Sb) by set_solver.
    pose proof (subseteq_size _ _ Hs). lia.
  Qed.

  (* ...and the same at a budget that is not [S _]: spending nothing. *)
  Lemma log_amort_reframe γ F u (Sb : gset Z) (v : nat) :
    (u + size (F ∖ Sb) <= v)%nat -> log_opS γ v Sb -∗ log_amort γ F u.
  Proof. iIntros (Hv) "H". iExists Sb, v. by iFrame. Qed.

  (* ADOPTING A BLOCK INTO F.  Enlarging F by a block THE OP HAS ALREADY
     LOGGED leaves the potential untouched, because the new member is not
     in [F ∖ Sb].  This is what lets writei reserve capacity for an
     indirect block whose identity it does not learn until balloc returns
     it: the loop enters at [F = {[bmapstart]}] and adopts the indirect
     block, at no cost, out of balloc's own credited postcondition. *)
  Lemma log_amort_adopt γ F u (b : Z) (Sb : gset Z) (v : nat) :
    b ∈ Sb ->
    (u + size (F ∖ Sb) <= v)%nat ->
    log_opS γ v Sb -∗ log_amort γ ({[b]} ∪ F) u.
  Proof.
    iIntros (Hb Hv) "H". iExists Sb, v. iFrame. iPureIntro.
    assert (Heq : ({[b]} ∪ F) ∖ Sb ⊆ F ∖ Sb) by set_solver.
    pose proof (subseteq_size _ _ Heq). lia.
  Qed.

  (* THE SHAPE writei's LOOP CARRIES, for the record: the bitmap block and
     (once it exists) the indirect block reserved, [u] units free for the
     data blocks still to come and for iupdate.  Entering costs
     [wi_cost_tight], by [log_amort_intro] at [size F <= 2]. *)
  Definition wi_amort (γ : log_names) (bmapstart : Z) (ind : Z) (u : nat) : iProp Σ :=
    log_amort γ ({[bmapstart]} ∪ {[ind]}) u.

  Lemma wi_amort_intro γ bmapstart ind u v :
    (u + 2 <= v)%nat -> log_op γ v -∗ wi_amort γ bmapstart ind u.
  Proof.
    iIntros (Hv) "H". rewrite /wi_amort.
    iApply (log_amort_intro with "H").
    assert (Hs : (size ({[bmapstart]} ∪ {[ind]} : gset Z) <= 2)%nat).
    { etrans; [apply gset_size_union_le|]. rewrite !size_singleton. lia. }
    lia.
  Qed.

  Lemma wi_amort_elim γ bmapstart ind u :
    wi_amort γ bmapstart ind u -∗ ∃ v : nat, ⌜(u <= v)%nat⌝ ∗ log_op γ v.
  Proof. rewrite /wi_amort. iApply log_amort_elim. Qed.

End LogAmort.
