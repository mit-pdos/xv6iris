(* BreadLru.v -- the STRUCTURAL layer of bread's two pointer-chasing scans.
   Everything the two loop lemmas of ProofBread need that is not a WP step:

   * the address <-> index bridge for the cursor.  Both scans carry the
     traversal position as a SPLIT of the bcache lock's LRU order list
     ([bcache_res]'s existential [ord], with [ord = seq 0 NBUF] up to
     permutation), so the cursor register holds [bnode k] for some [k] that
     the split names.  [bnode] is injective below NBUF and never equal to the
     head sentinel, which is exactly what turns the two [beq cursor,sentinel]
     tests into "the remaining segment is empty".

   * the two READ accessors on [BcacheInv.bcache_lru].  binit only ever
     SPLICED ([bcache_lru_splice]) and brelse only ever UNLINKED
     ([bcache_lru_unlink]); a scan merely reads one link field per
     iteration and must put it back untouched, at a position named by the same
     [l1 ++ a :: l2] decomposition.  Both accessors cover the sentinel's own
     two fields uniformly (the [l1 = []] / [l2 = []] boundary cases), so the
     loop bodies need no case split.

   * the two per-iteration BORROWS out of [BioInv.bio_slot_res].  The scan
     reads b->dev / b->blockno (forward) and b->refcnt (backward) of a buffer
     whose reference state it knows nothing about, so both arms of
     [bio_slot_res] must be joined FIRST -- the same "join the arms before the
     load" move ProofBpin makes for the refcnt increment.  The refcnt borrow
     additionally hands out the TIE the backward scan's [beqz] needs: the word
     reads zero exactly when the slot is free, which is what licenses the
     recycle block's [escrow_open_free].

   The [bseg] toolkit the two accessors are built from, the refcnt cell's word
   ties ([BioInv.brc_word_zero_eqv] / [brc_word_nonzero_eqv]) and the
   sign-extension injectivity the dev/blockno compares rest on
   ([RiscvExtras.sext64_32_inj]) all live in the shared files below, so nothing
   structural is restated here. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl auth gmap frac numbers.
From iris.base_logic.lib Require Import gen_heap invariants own.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import RiscvExtras.
Require Import ArrCursor.
Require Import BufOwn.
Require Import BcacheInv.
Require Import BioInv.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Require Import Xv6G.   (* the ghost-state bundle; see its header *)
Local Open Scope Z_scope.

Set Printing Depth 40.

(* ==================================================================== *)
(*  1.  The cursor: address <-> index                                    *)
(* ==================================================================== *)

(* [bnode] is injective on the indices a scan can visit -- including the
   sentinel index NBUF, so ONE statement covers both the array members and
   the head. *)
Lemma bnode_inj_le (i j : nat) :
  (i <= NBUF)%nat -> (j <= NBUF)%nat -> bnode i = bnode j -> i = j.
Proof.
  intros Hi Hj Heq.
  exact (acur_inj buf_base buf_stride i j NBUF
           buf_base_nonneg buf_stride_pos buf_end_fits Hi Hj Heq).
Qed.

Lemma bnode_ne_bhead (i : nat) : (i < NBUF)%nat -> bnode i <> bhead.
Proof.
  intros Hi Heq. unfold bhead in Heq.
  assert (Hij : i = NBUF) by (apply bnode_inj_le; [lia | lia | exact Heq]).
  lia.
Qed.

(* the two [beq cursor,sentinel] tests, at the shape the branch leaves take *)
Lemma bnode_eqv_bhead (i : nat) : (i < NBUF)%nat -> eq_vec (bnode i) bhead = false.
Proof. intro Hi. apply eq_vec_false_iff. exact (bnode_ne_bhead i Hi). Qed.

Lemma bnode_neqv_bhead (i : nat) : (i < NBUF)%nat -> neq_vec (bnode i) bhead = true.
Proof. intro Hi. unfold neq_vec. rewrite (bnode_eqv_bhead i Hi). reflexivity. Qed.

Lemma bhead_eqv_self : eq_vec bhead bhead = true.
Proof. apply eq_vec_true_iff. reflexivity. Qed.

Lemma bhead_neqv_self : neq_vec bhead bhead = false.
Proof. unfold neq_vec. rewrite bhead_eqv_self. reflexivity. Qed.

(* ==================================================================== *)
(*  2.  The order list: every index a split names is in range            *)
(* ==================================================================== *)

Lemma bord_elem_lt (ord : list nat) :
  ord ≡ₚ seq 0 NBUF -> forall k, k ∈ ord -> (k < NBUF)%nat.
Proof.
  intros Hperm k Hk.
  assert (Hk' : k ∈ seq 0 NBUF) by (rewrite -Hperm; exact Hk).
  apply elem_of_seq in Hk'. lia.
Qed.

Lemma bord_split_lt (ord l1 l2 : list nat) (k : nat) :
  ord ≡ₚ seq 0 NBUF -> ord = (l1 ++ k :: l2)%list -> (k < NBUF)%nat.
Proof.
  intros Hperm Hsplit. apply (bord_elem_lt ord Hperm).
  rewrite Hsplit. apply elem_of_app. right. by left.
Qed.

(* the two cursor spellings, at their boundary cases.  A forward cursor is
   the HEAD of the not-yet-visited suffix; a backward cursor is the LAST of
   the not-yet-visited prefix.  Both degenerate to the sentinel. *)
Lemma bcur_fwd_nil : List.hd bhead (map bnode []) = bhead.
Proof. reflexivity. Qed.

Lemma bcur_fwd_cons (k : nat) (r : list nat) :
  List.hd bhead (map bnode (k :: r)) = bnode k.
Proof. reflexivity. Qed.

Lemma bcur_bwd_nil : List.last (map bnode []) bhead = bhead.
Proof. reflexivity. Qed.

Lemma bcur_bwd_snoc (d : list nat) (k : nat) :
  List.last (map bnode (d ++ [k])%list) bhead = bnode k.
Proof.
  rewrite map_app.
  change (map bnode [k]) with ([bnode k] : list (mword 64)).
  rewrite (last_app_mid bhead (bnode k) (map bnode d) []). reflexivity.
Qed.

Lemma bcur_bwd_snoc_pred (d : list nat) (k : nat) (r : list nat) :
  (map bnode ((d ++ [k]) ++ r) = map bnode d ++ bnode k :: map bnode r)%list.
Proof. rewrite -app_assoc map_app. reflexivity. Qed.

Lemma bcur_fwd_split (d : list nat) (k : nat) (r : list nat) :
  (map bnode (d ++ k :: r) = map bnode d ++ bnode k :: map bnode r)%list.
Proof. rewrite map_app. reflexivity. Qed.

(* ==================================================================== *)
(*  3.  The two READ accessors on the circular list                      *)
(* ==================================================================== *)

Section BreadLru.
  Context `{!riscvGS Σ}.

  (* the sentinel's own two link fields *)
  Lemma bcache_lru_head_next_acc (h : mword 64) (l : list (mword 64)) :
    bcache_lru h l -∗
    bnext h ↦₈ List.hd h l ∗ (bnext h ↦₈ List.hd h l -∗ bcache_lru h l).
  Proof.
    rewrite /bcache_lru. iIntros "(Hhn & Hhp & Hseg)".
    iFrame "Hhn". iIntros "Hhn". iFrame "Hhn Hhp Hseg".
  Qed.

  Lemma bcache_lru_head_prev_acc (h : mword 64) (l : list (mword 64)) :
    bcache_lru h l -∗
    bprev h ↦₈ List.last l h ∗ (bprev h ↦₈ List.last l h -∗ bcache_lru h l).
  Proof.
    rewrite /bcache_lru. iIntros "(Hhn & Hhp & Hseg)".
    iFrame "Hhp". iIntros "Hhp". iFrame "Hhn Hhp Hseg".
  Qed.

  (* a member's [next]: the node AFTER [a] is the head of [l2], the sentinel
     when [a] is last.  Read-only, so the wand takes the cell back unchanged
     and the segment is rebuilt at the same decomposition. *)
  Lemma bcache_lru_next_acc (h a : mword 64) (l1 l2 : list (mword 64)) :
    bcache_lru h (l1 ++ a :: l2)%list -∗
    bnext a ↦₈ List.hd h l2 ∗
    (bnext a ↦₈ List.hd h l2 -∗ bcache_lru h (l1 ++ a :: l2)%list).
  Proof.
    rewrite /bcache_lru. iIntros "(Hhn & Hhp & Hseg)".
    iDestruct (bseg_app_split h h l1 (a :: l2) with "Hseg") as "[Hs1 Hs2]".
    iEval (rewrite (bseg_cons h (List.last l1 h) a l2)) in "Hs2".
    iDestruct "Hs2" as "(Hap & Han & Hs2)".
    iFrame "Han". iIntros "Han".
    iFrame "Hhn Hhp".
    iApply (bseg_app_join h h l1 (a :: l2) with "Hs1").
    rewrite (bseg_cons h (List.last l1 h) a l2). iFrame "Hap Han Hs2".
  Qed.

  (* a member's [prev]: the node BEFORE [a] is the last of [l1], the sentinel
     when [a] is first. *)
  Lemma bcache_lru_prev_acc (h a : mword 64) (l1 l2 : list (mword 64)) :
    bcache_lru h (l1 ++ a :: l2)%list -∗
    bprev a ↦₈ List.last l1 h ∗
    (bprev a ↦₈ List.last l1 h -∗ bcache_lru h (l1 ++ a :: l2)%list).
  Proof.
    rewrite /bcache_lru. iIntros "(Hhn & Hhp & Hseg)".
    iDestruct (bseg_app_split h h l1 (a :: l2) with "Hseg") as "[Hs1 Hs2]".
    iEval (rewrite (bseg_cons h (List.last l1 h) a l2)) in "Hs2".
    iDestruct "Hs2" as "(Hap & Han & Hs2)".
    iFrame "Hap". iIntros "Hap".
    iFrame "Hhn Hhp".
    iApply (bseg_app_join h h l1 (a :: l2) with "Hs1").
    rewrite (bseg_cons h (List.last l1 h) a l2). iFrame "Hap Han Hs2".
  Qed.

End BreadLru.

(* ==================================================================== *)
(*  4.  The dev / blockno compares                                       *)
(* ==================================================================== *)

(* [lw] yields the sign extension and the two arguments arrive sign-extended
   (the RV64 ABI), so the 64-bit compare is exactly the 32-bit one
   ([RiscvExtras.sext64_32_inj] is the injectivity). *)
Lemma bd_sext_eqv (a b : mword 32) :
  eq_vec (sign_extend' 64 a) (sign_extend' 64 b) = eq_vec a b.
Proof.
  destruct (eq_vec a b) eqn:Hab.
  - apply eq_vec_true_iff in Hab. subst b. apply eq_vec_true_iff. reflexivity.
  - apply eq_vec_false_iff in Hab. apply eq_vec_false_iff.
    intro Hc. apply Hab. exact (sext64_32_inj a b Hc).
Qed.

Lemma bd_sext_neqv (a b : mword 32) :
  neq_vec (sign_extend' 64 a) (sign_extend' 64 b) = neq_vec a b.
Proof. unfold neq_vec. by rewrite bd_sext_eqv. Qed.

(* ==================================================================== *)
(*  5.  The two per-iteration slot borrows                               *)
(* ==================================================================== *)

Section BreadSlots.
  Context `{!riscvGS Σ, !xv6G Σ}.

  (* THE FORWARD SCAN's borrow.  The scan reads [b->dev] and [b->blockno] of
     a buffer it knows nothing about, so the two arms of [bio_slot_res] are
     joined first: whichever it is, SOME fraction of both cells is inside
     (the whole bcache half when free, the retainder [qr] when busy, and the
     retainder never dies -- that is what [bio_slot_res]'s [q + qr = 1/2]
     tie guarantees).  Read-only: the wand takes both cells back. *)
  Lemma bio_slot_devbno_acc (bn : bio_names) (M : gmap nat (Qp * positive))
      (k : nat) (dev bno : mword 32) :
    bio_slot_res bn M k dev bno -∗
    ∃ q : Qp,
      b_dev (bpa k) ↦₄{DfracOwn q} dev ∗
      b_blockno (bpa k) ↦₄{DfracOwn q} bno ∗
      (b_dev (bpa k) ↦₄{DfracOwn q} dev -∗
       b_blockno (bpa k) ↦₄{DfracOwn q} bno -∗
       bio_slot_res bn M k dev bno).
  Proof.
    iIntros "Hslot". rewrite /bio_slot_res.
    destruct (M !! k) as [[qt n]|] eqn:HMk.
    - iDestruct "Hslot" as "(%Hn & Hcell & Hsl & Hqr)".
      iDestruct "Hqr" as (qr) "(%Htie & Hdev & Hbno)".
      iExists qr. iFrame "Hdev Hbno". iIntros "Hdev Hbno".
      iSplitR; [by iPureIntro|]. iFrame "Hcell Hsl".
      iExists qr. iSplitR; [by iPureIntro|]. iFrame "Hdev Hbno".
    - iDestruct "Hslot" as "(Hcell & Hdev & Hbno)".
      iExists (1/2)%Qp. iFrame "Hdev Hbno". iIntros "Hdev Hbno".
      iFrame "Hcell Hdev Hbno".
  Qed.

  (* THE BACKWARD SCAN's borrow.  The refcnt cell, plus the TIE its [beqz]
     needs: the word is zero exactly at [M !! k = None], and that is what
     licenses [BioInv.escrow_open_free] inside the recycle block. *)
  Lemma bio_slot_refcnt_acc (bn : bio_names) (M : gmap nat (Qp * positive))
      (k : nat) (dev bno : mword 32) :
    bio_slot_res bn M k dev bno -∗
    ∃ cw : mword 32,
      brefcnt k ↦₄ cw ∗
      ⌜(eq_vec (sign_extend' 64 cw) (zero_reg : mword 64) = true /\ M !! k = None)
       \/ (eq_vec (sign_extend' 64 cw) (zero_reg : mword 64) = false
           /\ is_Some (M !! k))⌝ ∗
      (brefcnt k ↦₄ cw -∗ bio_slot_res bn M k dev bno).
  Proof.
    iIntros "Hslot". rewrite /bio_slot_res.
    destruct (M !! k) as [[qt n]|] eqn:HMk.
    - iDestruct "Hslot" as "(%Hn & Hcell & Hsl & Hqr)".
      iExists (mword_of_int (Z.pos n) : mword 32). iFrame "Hcell".
      iSplitR.
      { iPureIntro. right. split; [exact (brc_word_nonzero_eqv n Hn) | by eexists]. }
      iIntros "Hcell". iSplitR; [by iPureIntro|]. iFrame "Hcell Hsl Hqr".
    - iDestruct "Hslot" as "(Hcell & Hdev & Hbno)".
      iExists (mword_of_int 0 : mword 32). iFrame "Hcell".
      iSplitR.
      { iPureIntro. left. split; [exact brc_word_zero_eqv | reflexivity]. }
      iIntros "Hcell". iFrame "Hcell Hdev Hbno".
  Qed.

End BreadSlots.
