(* WpLock.v -- the standard CSL/Iris spin-lock invariant for xv6's
   [struct spinlock], mirroring iris_heap_lang/lib/spin_lock.v but over the
   PHYSICAL 4-byte lock word ([lk->locked]) of the Sail RISC-V machine:

     locked γ      -- the (exclusive, ghost) lock-ownership token
     lock_inv      -- ∃ v, lock word ↦ v ∗ (v = 0 ∗ locked γ ∗ R  ∨  v ≠ 0)
     is_lock       -- inv lockN lock_inv   (persistent)

   When the word is 0 (lock free) the invariant holds the token AND the
   protected resource R; a successful acquire (its amoswap reads 0, writes 1)
   takes both out and re-closes with the "held" disjunct.  release stores 0
   and gives token + R back.  The "held" disjunct records the word's
   non-zeroness in exactly the shape the spin loop's [c.bnez] test consumes:
   [neq_vec (sign_extend' 64 v) zero_reg = true]. *)
From iris.proofmode Require Import proofmode.
From iris.algebra Require Import excl.
From iris.base_logic.lib Require Import invariants own.
Require Import SailStdpp.Base SailStdpp.Operators_mwords.
Require Import Riscv.rv64d.
Require Import RiscvPtsto.
Local Open Scope Z_scope.

Class lockG (Σ : gFunctors) := LockG { lock_inG :: inG Σ (exclR unitO) }.
Definition lockΣ : gFunctors := #[GFunctor (exclR unitO)].
Global Instance subG_lockΣ {Σ} : subG lockΣ Σ -> lockG Σ.
Proof. solve_inG. Qed.

Section Lock.
  Context `{!riscvGS Σ, !lockG Σ}.

  (* sibling of [minstretN]; the two are disjoint by construction, so a leaf
     can open [is_lock] INSIDE the step engine's [⊤ ∖ ↑minstretN] callback. *)
  Definition lockN : namespace := nroot .@ "xv6spinlock".

  Definition locked (γ : gname) : iProp Σ := own γ (Excl ()).

  (* the physical 4-byte little-endian lock word at address [lk]: the 4-byte
     word points-to [↦₄] (which also bundles the 4-byte alignment of [lk]). *)
  Definition lock_word (lk : mword 64) (v : mword 32) : iProp Σ :=
    (lk ↦₄ v)%I.

  Definition lock_inv (γ : gname) (lk : mword 64) (R : iProp Σ) : iProp Σ :=
    (∃ v : mword 32,
       lock_word lk v ∗
       (⌜v = (mword_of_int 0 : mword 32)⌝ ∗ locked γ ∗ R
        ∨ ⌜neq_vec (sign_extend' 64 v) zero_reg = true⌝))%I.

  (* the lock's NAME: [lk->name] (the 8-byte pointer field at +8) holds the
     address of a NUL-terminated string [s].  initlock writes the field once
     and nothing ever writes it again, so both the field and the string it
     points at are held at [DfracDiscarded] -- [lock_name] is PERSISTENT, and
     therefore rides along inside the (persistent) lock predicate at no
     ownership cost: no proof has to thread the name field, and every holder
     of the lock knows which lock it is by name. *)
  Definition lock_name_field (lk : mword 64) : mword 64 :=
    add_vec lk (sign_extend' 64 (mword_of_int 8 : mword 12)).

  Definition lock_name (lk : mword 64) (s : string) : iProp Σ :=
    (∃ p : mword 64, lock_name_field lk ↦₈□ p ∗ p ↦ₛ□ s)%I.

  Global Instance lock_name_persistent lk s : Persistent (lock_name lk s).
  Proof. apply _. Qed.

  (* a lock is its (immutable) name plus the invariant over its word. *)
  Definition is_lock (γ : gname) (lk : mword 64) (s : string) (R : iProp Σ) : iProp Σ :=
    (lock_name lk s ∗ inv lockN (lock_inv γ lk R))%I.

  Global Instance is_lock_persistent γ lk s R : Persistent (is_lock γ lk s R).
  Proof. apply _. Qed.

  (* the two projections + the introduction rule (the only interface the
     lock leaves and [newlock] need). *)
  Lemma is_lock_name γ lk s R : is_lock γ lk s R -∗ lock_name lk s.
  Proof. iIntros "[$ _]". Qed.
  Lemma is_lock_inv γ lk s R : is_lock γ lk s R -∗ inv lockN (lock_inv γ lk R).
  Proof. iIntros "[_ $]". Qed.
  Lemma is_lock_intro γ lk s R :
    lock_name lk s -∗ inv lockN (lock_inv γ lk R) -∗ is_lock γ lk s R.
  Proof. iIntros "#Hn #Hi". by iFrame "Hn Hi". Qed.

  Global Instance locked_timeless γ : Timeless (locked γ).
  Proof. apply _. Qed.

  Global Instance mem_pointsto_timeless a dq b : Timeless (mem_pointsto a dq b).
  Proof. rewrite /mem_pointsto. apply _. Qed.

  Global Instance lock_word_timeless lk v : Timeless (lock_word lk v).
  Proof. rewrite /lock_word /word4_pointsto. apply _. Qed.

  Lemma locked_exclusive γ : locked γ -∗ locked γ -∗ False.
  Proof.
    iIntros "H1 H2".
    iDestruct (own_valid_2 with "H1 H2") as %H.
    destruct (exclusive_l (Excl ()) (Excl ()) H).
  Qed.

  (* lock construction: a FREE physical lock word plus the resource it is to
     protect become a lock (spin_lock.v's [newlock]). *)

  (* a lock created in the HELD state: the creator keeps token + R *)
End Lock.
