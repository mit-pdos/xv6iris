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
     can open [is_lock] INSIDE the step engine's [E ∖ ↑minstretN] callback. *)
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

  Definition is_lock (γ : gname) (lk : mword 64) (R : iProp Σ) : iProp Σ :=
    inv lockN (lock_inv γ lk R).

  Global Instance is_lock_persistent γ lk R : Persistent (is_lock γ lk R).
  Proof. apply _. Qed.

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
  Lemma newlock E (lk : mword 64) (R : iProp Σ) :
    lock_word lk (mword_of_int 0) -∗ R ={E}=∗ ∃ γ, is_lock γ lk R.
  Proof.
    iIntros "Hw HR".
    iMod (own_alloc (Excl ())) as (γ) "Htok"; first done.
    iMod (inv_alloc lockN E (lock_inv γ lk R) with "[Hw HR Htok]") as "#Hinv".
    { iNext. iExists (mword_of_int 0). iFrame "Hw". iLeft. by iFrame. }
    iModIntro. iExists γ. iExact "Hinv".
  Qed.

  (* a lock created in the HELD state: the creator keeps token + R *)
  Lemma newlock_held E (lk : mword 64) (v : mword 32) (R : iProp Σ) :
    neq_vec (sign_extend' 64 v) zero_reg = true ->
    lock_word lk v ={E}=∗ ∃ γ, is_lock γ lk R ∗ locked γ.
  Proof.
    iIntros (Hnz) "Hw".
    iMod (own_alloc (Excl ())) as (γ) "Htok"; first done.
    iMod (inv_alloc lockN E (lock_inv γ lk R) with "[Hw]") as "#Hinv".
    { iNext. iExists v. iFrame "Hw". iRight. by iPureIntro. }
    iModIntro. iExists γ. iFrame "Htok". iExact "Hinv".
  Qed.
End Lock.
