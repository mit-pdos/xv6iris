(* BcacheInv.v -- the buffer-cache geometry and the circular LRU list that
   binit() builds, kept apart from binit's own spec so bget/brelse can share
   them without depending on a whole-function proof.

   struct bcache { struct spinlock lock; struct buf buf[NBUF]; struct buf head; }
   (bio.c), so &bcache.lock = &bcache, the buffer array starts 24 bytes in, and
   the head SENTINEL sits immediately past the array -- i.e. at exactly the
   address the loop's end pointer holds.  That makes the head node [bnode NBUF],
   one past the last buffer, and lets one cursor ([ArrCursor]'s [acur]) name
   every node.

   struct buf's fields used here (offsets from the disassembly): the sleeplock
   at +16, prev at +72, next at +80.  All three are spelled in the EXACT form
   the instructions compute them (an [add_vec] against a sign-extended 12-bit
   immediate), so a store's address unifies with the cell without rewriting.

   binit leaves the array as a circular doubly-linked list threaded through
   [head]: [bcache_lru h l] holds when the cycle is [h] followed, in next-order,
   by [l].  Each iteration splices the next buffer in right AFTER the head
   ([bcache_lru_splice], the one lemma the loop body needs), so the list binit
   ends with is the buffers in reverse address order -- MRU first, which is what
   bget's scan-from-head-backwards expects.

   This file owns the WHOLE list ADT, not just binit's part of it: the [bseg]
   toolkit (split/join at a cursor, the four boundary link accessors) and
   [bcache_lru_unlink] live here next to [bcache_lru_splice], so that brelse's
   rotate and bread's two read-only scans share one copy. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvModelBytes.
Require Import RiscvPtsto.
Require Import ArrCursor.
Require ByteCursor.
Require Import BufOwn.
From Kernel Require KernelSyms.
Require Import Riscv.rv64d_types Riscv.rv64d Riscv.riscv_extras.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------ *)
(*  Geometry                                                           *)
(* ------------------------------------------------------------------ *)

Definition bcache_addr : mword 64 := mword_of_int KernelSyms.bcache.

Definition NBUF : nat := 30%nat.
Definition buf_stride : Z := 1112.
Definition buf_base : Z := KernelSyms.bcache + 24.

(* the [k]th node of the cache: [bnode k] for k < NBUF is [&bcache.buf[k]], and
   [bnode NBUF] is the head sentinel [&bcache.head]. *)
Definition bnode (k : nat) : mword 64 := acur buf_base buf_stride k.
Definition bhead : mword 64 := bnode NBUF.

(* the three fields of a node, in instruction-address form *)
Definition buf_lock (a : mword 64) : mword 64 :=
  add_vec a (sign_extend' 64 (mword_of_int 16 : mword 12)).
Definition bprev (a : mword 64) : mword 64 :=
  add_vec a (sign_extend' 64 (mword_of_int 72 : mword 12)).
Definition bnext (a : mword 64) : mword 64 :=
  add_vec a (sign_extend' 64 (mword_of_int 80 : mword 12)).

(* the side conditions [ArrCursor]'s cursor lemmas take, discharged once. *)
Lemma buf_base_nonneg : 0 <= buf_base.
Proof. unfold buf_base, KernelSyms.bcache. lia. Qed.
Lemma buf_stride_pos : 0 < buf_stride.
Proof. unfold buf_stride. lia. Qed.
Lemma buf_end_fits : buf_base + buf_stride * Z.of_nat NBUF < 2 ^ 64.
Proof.
  unfold buf_base, buf_stride, NBUF, KernelSyms.bcache.
  assert (H : (2 ^ 64 = 18446744073709551616)%Z) by (vm_compute; reflexivity).
  rewrite H. lia.
Qed.

(* the node's address as an integer -- the bridge every arithmetic fact about a
   buffer goes through. *)
Lemma bnode_unsigned (k : nat) : (k < NBUF)%nat ->
  bv_unsigned (bnode k) = buf_base + buf_stride * Z.of_nat k.
Proof.
  intro Hk. unfold bnode.
  apply (acur_unsigned buf_base buf_stride k NBUF
           buf_base_nonneg buf_stride_pos buf_end_fits).
  lia.
Qed.

(* EVERY BUFFER'S DATA AREA IS KERNEL DATA -- the [addr_is_kdata] premise
   virtio_disk_rw takes on b->data, discharged once for the whole cache.
   [bcache] is a .bss object at 0x80018190, so buffer k's base is
   [buf_base + 1112*k] with buf_base = bcache+24 and k < NBUF = 30: the whole
   object sits inside [text_end, ram_base+ram_size) and the address arithmetic
   never wraps.  (bwrite and bread are both rw callers and need exactly this;
   it is bcache GEOMETRY, so neither whole-function proof owns it.) *)
Local Lemma bcache_wrap64_z (a : Z) : bv_wrap 64 a = (a `mod` 18446744073709551616)%Z.
Proof. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64%Z. reflexivity. Qed.

Local Lemma bcache_kdata_z (b j : Z) :
  (2147512320 <= b)%Z -> (0 <= j)%Z -> (b + j < 2281701376)%Z ->
  (2147512320 <= ((b `mod` 18446744073709551616) + j) `mod` 18446744073709551616
     < 2281701376)%Z.
Proof.
  intros H1 H2 H3.
  rewrite (Z.mod_small b); [| lia].
  rewrite Z.mod_small; lia.
Qed.

Lemma bnode_data_kdata (k j : nat) : (k < NBUF)%nat -> (j < 1024)%nat ->
  addr_is_kdata (pa_add (b_data (bnode k)) j).
Proof.
  intros Hk Hj. unfold addr_is_kdata, b_data, text_end, ram_base, ram_size.
  rewrite RiscvExtras.uint_unsigned.
  rewrite !ByteCursor.pa_add_unsigned.
  rewrite !bcache_wrap64_z.
  rewrite (bnode_unsigned k Hk).
  change (0x80007000)%Z with 2147512320%Z.
  change (0x80000000 + 0x8000000)%Z with 2281701376%Z.
  apply bcache_kdata_z.
  - unfold buf_base, buf_stride, KernelSyms.bcache.
    pose proof (Nat2Z.is_nonneg k). lia.
  - exact (Nat2Z.is_nonneg j).
  - unfold NBUF in Hk. unfold buf_base, buf_stride, KernelSyms.bcache.
    assert (Hkz : (Z.of_nat k <= 29)%Z) by lia.
    assert (Hjz : (Z.of_nat j <= 1023)%Z) by lia.
    lia.
Qed.

(* ------------------------------------------------------------------ *)
(*  The list binit builds                                              *)
(* ------------------------------------------------------------------ *)

(* [blist j n] : nodes [j .. j+n-1] in the order binit leaves them, i.e. the
   reverse of address order (each is spliced in ahead of its predecessors). *)
Definition blist (j n : nat) : list (mword 64) := rev (map bnode (seq j n)).

(* [++] must be scope-annotated: [string_scope] is in scope here (the lock
   names), and it claims [++] too. *)
Lemma blist_step (j n : nat) : blist j (S n) = (blist (S j) n ++ [bnode j])%list.
Proof. unfold blist. cbn [seq map rev]. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(*  Pure list facts about [List.hd] / [List.last] under [++].           *)
(*                                                                     *)
(*  Every cursor into the cycle is named by a decomposition             *)
(*  [l1 ++ a :: l2], and the node before / after [a] is then            *)
(*  [List.last l1 h] / [List.hd h l2] -- the sentinel itself at the two  *)
(*  boundaries.  These six lemmas are what make that spelling           *)
(*  case-split-free, and they are what the [bseg] toolkit below is       *)
(*  proved by induction with.                                          *)
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

Section BcacheInv.
  Context `{!riscvGS Σ}.

  (* a node's two link fields, uninitialized *)
  Definition blink_raw (a : mword 64) : iProp Σ :=
    ((∃ v : mword 64, bprev a ↦₈ v) ∗ (∃ v : mword 64, bnext a ↦₈ v))%I.

  (* [bseg h prev l] : the nodes [l], in next-order, with [prev] the node ahead
     of the first and [h] the node the last one's next points back to. *)
  Fixpoint bseg (h prev : mword 64) (l : list (mword 64)) : iProp Σ :=
    match l with
    | [] => emp
    | a :: l' => (bprev a ↦₈ prev ∗ bnext a ↦₈ List.hd h l' ∗ bseg h a l')%I
    end.

  (* the whole circular list: the head sentinel [h] followed by [l]. *)
  Definition bcache_lru (h : mword 64) (l : list (mword 64)) : iProp Σ :=
    (bnext h ↦₈ List.hd h l ∗ bprev h ↦₈ List.last l h ∗ bseg h h l)%I.

  (* the state binit's two pre-loop stores leave: an empty cycle, head pointing
     at itself both ways. *)
  Lemma bcache_lru_nil (h : mword 64) :
    bnext h ↦₈ h -∗ bprev h ↦₈ h -∗ bcache_lru h [].
  Proof. iIntros "Hn Hp". rewrite /bcache_lru /=. by iFrame "Hn Hp". Qed.

  (* THE loop-body lemma.  Splicing a new node [a] in right after the head
     touches exactly four cells: the head's next, the prev of whatever the head
     currently points at (the head itself when the cycle is empty -- and in both
     cases that cell currently holds [h]), and [a]'s own two.  So the body gets
     those two cells out and a wand that takes the four updated ones back. *)
  Lemma bcache_lru_splice (h : mword 64) (l : list (mword 64)) :
    bcache_lru h l -∗
    bnext h ↦₈ List.hd h l ∗ bprev (List.hd h l) ↦₈ h ∗
    (∀ a : mword 64,
       bnext h ↦₈ a -∗ bprev (List.hd h l) ↦₈ a -∗
       bnext a ↦₈ List.hd h l -∗ bprev a ↦₈ h -∗
       bcache_lru h (a :: l)).
  Proof.
    destruct l as [| b l'].
    - iIntros "(Hhn & Hhp & _)". cbn [List.hd].
      iFrame "Hhn Hhp". iIntros (a) "Hhn Hhp Han Hap".
      rewrite /bcache_lru /=. iFrame "Hhn Hhp Hap Han".
    - iIntros "(Hhn & Hhp & Hbp & Hbn & Hseg)". cbn [List.hd].
      iFrame "Hhn Hbp". iIntros (a) "Hhn Hbp Han Hap".
      rewrite /bcache_lru. cbn [List.hd List.last bseg].
      iFrame "Hhn Hhp Hap Han Hbp Hbn Hseg".
  Qed.

  (* ================================================================== *)
  (*  THE [bseg] TOOLKIT                                                 *)
  (*                                                                     *)
  (*  Splitting and rejoining a segment at a cursor, and reading (or      *)
  (*  retargeting) the link cells at a segment's two ends.  All of it is  *)
  (*  subsystem-general: binit only ever SPLICES, brelse UNLINKS and      *)
  (*  re-splices, bread's two scans merely READ one link per iteration,   *)
  (*  and every one of those is a consumer of these seven lemmas.  Note   *)
  (*  the second argument is spelled [n] here rather than [h]: nothing in *)
  (*  [bseg] requires the terminator to be the head sentinel, and the     *)
  (*  splits below instantiate it at an interior node.                    *)
  (* ================================================================== *)

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
  (*  THE UNLINK -- [bcache_lru_splice]'s inverse                        *)
  (*                                                                     *)
  (*    b->next->prev = b->prev;   b->prev->next = b->next;               *)
  (*                                                                     *)
  (*  Both stores land on cells that are, depending on where [b] sits in   *)
  (*  the cycle, either inside the segment or one of the head sentinel's   *)
  (*  own two link fields -- so the predecessor and successor are named    *)
  (*  UNIFORMLY as [List.last l1 h] / [List.hd h l2].  Every boundary case *)
  (*  (b first, b last, b the only element) is covered by those two        *)
  (*  spellings, so the call site needs no case split.                     *)
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

End BcacheInv.
