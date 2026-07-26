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
   bget's scan-from-head-backwards expects. *)
From Stdlib Require Import ZArith Lia List.
From stdpp Require Import gmap list bitvector.definitions.
From iris.proofmode Require Import proofmode.
From iris.base_logic.lib Require Import gen_heap invariants.
Require Import SailStdpp.ConcurrencyInterface SailStdpp.ConcurrencyInterfaceBuiltins SailStdpp.ConcurrencyInterfaceTypes SailStdpp.Operators_mwords.
Require Import SailStdpp.Base SailStdpp.TypeCasts SailStdpp.Values SailStdpp.MachineWord.
Require Import RiscvLang RiscvPtsto.
Require Import ArrCursor.
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

End BcacheInv.
