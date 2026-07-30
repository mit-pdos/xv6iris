(* BrelseLru.v -- the ONE structural fact about [BcacheInv.bcache_lru] that
   brelse needs and binit did not: UNLINKING a node from the middle of the
   circular doubly-linked list.

   binit only ever splices a fresh node in right after the head, and
   [BcacheInv.bcache_lru_splice] is exactly that.  brelse's zero-refcnt arm
   first has to take the buffer OUT of wherever it currently sits:

     b->next->prev = b->prev;
     b->prev->next = b->next;

   and only then splice it back in at the front.  Both stores land on cells
   that are, depending on where [b] sits in the cycle, either inside the
   segment or one of the head sentinel's own two link fields -- so the lemma
   has to name the predecessor and successor UNIFORMLY.  Writing the cycle as
   [h] followed by [l1 ++ b :: l2], they are

     pv := List.last l1 h        (the head itself when b is first)
     nx := List.hd  h l2         (the head itself when b is last)

   and [bcache_lru_unlink] hands out b's own two link cells plus [bnext pv]
   and [bprev nx], with a wand that rebuilds [bcache_lru h (l1 ++ l2)] from
   the two spliced-around values.  Every boundary case (b first, b last, b the
   only element) is covered by those two spellings, so the proof needs no case
   split at the call site.

   The [bseg] toolkit it is built from is general and stated here rather than
   in BcacheInv.v so that this file is the only one brelse adds to the bio
   layer.  [bseg n prev l] reads: the nodes [l] in next-order, with [prev] the
   node ahead of the first and [n] the node the last one's next points at
   (BcacheInv.v spells the second argument [h] because it instantiates it at
   the head sentinel; nothing in [bseg] requires that). *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import list.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvPtsto.
Require Import BcacheInv.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.

(* ------------------------------------------------------------------ *)
(*  Pure list facts about [List.hd] / [List.last] under [++].          *)
(* ------------------------------------------------------------------ *)

Lemma last_ne_default {A : Type} (l : list A) (d1 d2 : A) :
  l <> [] -> List.last l d1 = List.last l d2.
Proof.
  induction l as [|a l IH]; [congruence|].
  intros _. destruct l as [|b l']; [reflexivity|].
  change (List.last (a :: b :: l') d1) with (List.last (b :: l') d1).
  change (List.last (a :: b :: l') d2) with (List.last (b :: l') d2).
  apply IH. discriminate.
Qed.

Lemma last_cons {A : Type} (a : A) (l : list A) (d : A) :
  List.last (a :: l) d = List.last l a.
Proof.
  destruct l as [|b l']; [reflexivity|].
  change (List.last (a :: b :: l') d) with (List.last (b :: l') d).
  apply last_ne_default. discriminate.
Qed.

Lemma hd_app {A : Type} (d : A) (l1 l2 : list A) :
  List.hd d (l1 ++ l2)%list = List.hd (List.hd d l2) l1.
Proof. destruct l1; reflexivity. Qed.

Lemma last_app_gen {A : Type} (l1 l2 : list A) (d : A) :
  List.last (l1 ++ l2)%list d = List.last l2 (List.last l1 d).
Proof.
  destruct l2 as [|b l2'].
  { rewrite app_nil_r. reflexivity. }
  induction l1 as [|c l1 IH].
  - reflexivity.
  - change ((c :: l1) ++ b :: l2')%list with (c :: (l1 ++ b :: l2'))%list.
    rewrite last_cons.
    assert (Hnn : (l1 ++ b :: l2')%list <> []).
    { destruct l1; discriminate. }
    rewrite (last_ne_default (l1 ++ b :: l2')%list c d Hnn).
    rewrite IH. rewrite (last_cons c l1 d).
    destruct l2' as [|e l2'']; [reflexivity|].
    apply last_ne_default. discriminate.
Qed.

Lemma hd_app_mid {A : Type} (d a : A) (l1 l2 : list A) :
  List.hd d (l1 ++ a :: l2)%list = List.hd a l1.
Proof. rewrite hd_app. reflexivity. Qed.

Lemma last_app_mid {A : Type} (d a : A) (l1 l2 : list A) :
  List.last (l1 ++ a :: l2)%list d = List.last l2 a.
Proof. rewrite last_app_gen. rewrite last_cons. reflexivity. Qed.

Section BrelseLru.
  Context `{!riscvGS Σ}.

  (* One layer of [bseg], as a rewrite rule: the fixpoint's own body.  Peeling
     with this (rather than [cbn [bseg]]) keeps the recursive occurrence FOLDED,
     which is what lets the induction hypotheses below match syntactically. *)
  Lemma bseg_cons (n prev a : mword 64) (l : list (mword 64)) :
    bseg n prev (a :: l) = (bprev a ↦₈ prev ∗ bnext a ↦₈ List.hd n l ∗ bseg n a l)%I.
  Proof. reflexivity. Qed.

  (* ---- [bseg] splits along [++] ---- *)

  Lemma bseg_app_split (n prev : mword 64) (l1 l2 : list (mword 64)) :
    bseg n prev (l1 ++ l2)%list -∗
    bseg (List.hd n l2) prev l1 ∗ bseg n (List.last l1 prev) l2.
  Proof.
    revert prev. induction l1 as [|a l1 IH]; intros prev.
    - iIntros "H". cbn [app List.last bseg]. iSplitR; [done | iExact "H"].
    - change ((a :: l1) ++ l2)%list with (a :: (l1 ++ l2))%list.
      rewrite (bseg_cons n prev a (l1 ++ l2)%list).
      rewrite (bseg_cons (List.hd n l2) prev a l1).
      rewrite (hd_app n l1 l2).
      rewrite (last_cons a l1 prev).
      iIntros "(Hp & Hnx & Hrest)".
      iDestruct (IH a with "Hrest") as "[H1 H2]".
      iFrame "Hp Hnx H1 H2".
  Qed.

  Lemma bseg_app_join (n prev : mword 64) (l1 l2 : list (mword 64)) :
    bseg (List.hd n l2) prev l1 -∗ bseg n (List.last l1 prev) l2 -∗
    bseg n prev (l1 ++ l2)%list.
  Proof.
    revert prev. induction l1 as [|a l1 IH]; intros prev.
    - iIntros "_ H". cbn [app List.last]. iExact "H".
    - change ((a :: l1) ++ l2)%list with (a :: (l1 ++ l2))%list.
      rewrite (bseg_cons n prev a (l1 ++ l2)%list).
      rewrite (bseg_cons (List.hd n l2) prev a l1).
      rewrite (hd_app n l1 l2).
      rewrite (last_cons a l1 prev).
      iIntros "(Hp & Hnx & H1) H2".
      iFrame "Hp Hnx".
      iApply (IH a with "H1 H2").
  Qed.

  (* ---- the two boundary accessors ---- *)

  (* the LAST node of a nonempty segment owns the [bnext] cell that points out
     of the segment; retargeting it retargets the segment's terminator. *)
  Lemma bseg_last_next (n prev c : mword 64) (l : list (mword 64)) :
    bseg n prev (c :: l) -∗
    bnext (List.last l c) ↦₈ n ∗
    (∀ n2 : mword 64, bnext (List.last l c) ↦₈ n2 -∗ bseg n2 prev (c :: l)).
  Proof.
    revert prev c. induction l as [|b l IH]; intros prev c.
    - cbn [List.hd List.last bseg].
      iIntros "(Hp & Hnx & _)". iFrame "Hnx".
      iIntros (n2) "Hnx". by iFrame "Hp Hnx".
    - rewrite (bseg_cons n prev c (b :: l)). cbn [List.hd].
      rewrite (last_cons b l c).
      iIntros "(Hp & Hnx & Hrest)".
      iDestruct (IH c b with "Hrest") as "[Hlast Hback]".
      iFrame "Hlast". iIntros (n2) "Hn2".
      iDestruct ("Hback" with "Hn2") as "Hseg".
      rewrite (bseg_cons n2 prev c (b :: l)). cbn [List.hd].
      iFrame "Hp Hnx Hseg".
  Qed.

  (* the FIRST node owns the [bprev] cell that points out of the segment. *)
  Lemma bseg_first_prev (n p1 c : mword 64) (l : list (mword 64)) :
    bseg n p1 (c :: l) -∗
    bprev c ↦₈ p1 ∗ (∀ p2 : mword 64, bprev c ↦₈ p2 -∗ bseg n p2 (c :: l)).
  Proof.
    rewrite (bseg_cons n p1 c l).
    iIntros "(Hp & Hnx & Hrest)". iFrame "Hp".
    iIntros (p2) "Hp". rewrite (bseg_cons n p2 c l). iFrame "Hp Hnx Hrest".
  Qed.

  (* ---- the two accessors, extended over the head sentinel's own cells ----

     [bseg_pred_next]: the [bnext] cell of the node BEFORE the segment [l1] --
     the sentinel's own when [l1] is empty.  [bseg_succ_prev] is the mirror. *)

  Lemma bseg_pred_next (h a : mword 64) (l1 : list (mword 64)) :
    bnext h ↦₈ List.hd a l1 -∗ bseg a h l1 -∗
    bnext (List.last l1 h) ↦₈ a ∗
    (∀ n2 : mword 64,
       bnext (List.last l1 h) ↦₈ n2 -∗ bnext h ↦₈ List.hd n2 l1 ∗ bseg n2 h l1).
  Proof.
    destruct l1 as [|c l1].
    - cbn [List.hd List.last bseg].
      iIntros "Hhn _". iFrame "Hhn". iIntros (n2) "Hhn". by iFrame "Hhn".
    - rewrite (last_cons c l1 h). cbn [List.hd].
      iIntros "Hhn Hseg".
      iDestruct (bseg_last_next a h c l1 with "Hseg") as "[Hlast Hback]".
      iFrame "Hlast". iIntros (n2) "Hn2".
      iDestruct ("Hback" with "Hn2") as "Hseg".
      cbn [List.hd]. iFrame "Hhn Hseg".
  Qed.

  Lemma bseg_succ_prev (h a : mword 64) (l2 : list (mword 64)) :
    bprev h ↦₈ List.last l2 a -∗ bseg h a l2 -∗
    bprev (List.hd h l2) ↦₈ a ∗
    (∀ p2 : mword 64,
       bprev (List.hd h l2) ↦₈ p2 -∗ bprev h ↦₈ List.last l2 p2 ∗ bseg h p2 l2).
  Proof.
    destruct l2 as [|b l2].
    - cbn [List.hd List.last bseg].
      iIntros "Hhp _". iFrame "Hhp". iIntros (p2) "Hhp". by iFrame "Hhp".
    - cbn [List.hd].
      rewrite (last_cons b l2 a).
      iIntros "Hhp Hseg".
      iDestruct (bseg_first_prev h a b l2 with "Hseg") as "[Hfp Hback]".
      iFrame "Hfp". iIntros (p2) "Hp2".
      iDestruct ("Hback" with "Hp2") as "Hseg".
      rewrite (last_cons b l2 p2). iFrame "Hhp Hseg".
  Qed.

  (* ================================================================== *)
  (*  THE UNLINK                                                         *)
  (* ================================================================== *)

  Lemma bcache_lru_unlink (h a : mword 64) (l1 l2 : list (mword 64)) :
    bcache_lru h (l1 ++ a :: l2)%list -∗
      bprev a ↦₈ List.last l1 h ∗ bnext a ↦₈ List.hd h l2 ∗
      bnext (List.last l1 h) ↦₈ a ∗ bprev (List.hd h l2) ↦₈ a ∗
      (bnext (List.last l1 h) ↦₈ List.hd h l2 -∗
       bprev (List.hd h l2) ↦₈ List.last l1 h -∗
       bcache_lru h (l1 ++ l2)%list).
  Proof.
    rewrite /bcache_lru.
    rewrite (hd_app_mid h a l1 l2) (last_app_mid h a l1 l2).
    iIntros "(Hhn & Hhp & Hseg)".
    iDestruct (bseg_app_split h h l1 (a :: l2) with "Hseg") as "[Hs1 Hs2]".
    iEval (cbn [List.hd]) in "Hs1".
    iEval (rewrite (bseg_cons h (List.last l1 h) a l2)) in "Hs2".
    iDestruct "Hs2" as "(Hap & Han & Hs2)".
    iDestruct (bseg_pred_next h a l1 with "Hhn Hs1") as "[Hpn Hpback]".
    iDestruct (bseg_succ_prev h a l2 with "Hhp Hs2") as "[Hsp Hsback]".
    iFrame "Hap Han Hpn Hsp".
    iIntros "Hn2 Hp2".
    iDestruct ("Hpback" with "Hn2") as "[Hhn Hs1]".
    iDestruct ("Hsback" with "Hp2") as "[Hhp Hs2]".
    rewrite (hd_app h l1 l2) (last_app_gen l1 l2 h).
    iFrame "Hhn Hhp".
    iApply (bseg_app_join h h l1 l2 with "Hs1 Hs2").
  Qed.

End BrelseLru.
