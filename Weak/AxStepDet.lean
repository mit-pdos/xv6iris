/-
Weak: **head-determinism of the program half's monad-node step `pnodeStep`** (AxSL tier).

Rocq: `iris/AxStepDet.v` @ xxvzwolszwmp.

## The Rocq header, in substance

For fixed inputs `(m, rs, ib, d)` and a fixed label `l`, two `pnodeStep`s agree on every output,
EXCEPT at the two genuine nondeterminism sources of the program half:
  * the boundary `pure` arm (the `tick` bit: `m'` is `riscvStep t` for some `t`), and
  * `choose` (`m'` is `k c` for some chosen `c`).
At both exceptions every OTHER output is still determined.

The RAM-read arms (plain, exclusive and — Lean, O2 — the i-cache fetch) are deterministic because
the label carries the bytes `tvs`, which pin the read value `w` (`MachCSL.bv_eq_of_bytes`); the
MMIO arms because `devRead`/`devWrite` are functions.

## Deviations from Rocq

1. `WeakEvInst.pnodeStep` has a sixth output, the executed barrier `obar` (WeakEvInst deviation
   4); `pnodeStepDet` determines it as well (`b1 = b2` in every disjunct).
2. `Interface.Ret v` ↦ `.pure v`; `Interface.Next (Interface.Choose ty) k` ↦
   `.impure (.ok (.choose p)) k` (lean-sail's `Outcome.choose`, `p : Sail.Primitive`).
3. `tvsPinWord` is stated over `(tvs.map Prod.snd)[j]?` (Rocq `tvs.*2 !! j`) with `j < n`
   (Rocq `j < N.to_nat n`); Rocq `Local`, here public (no clash).
4. PROOF: per-arm case analysis on the `Outcome` constructor (Rocq: one generic Ltac sweep); the
   O2 fetch arm is a third read arm, separated from the other two by its label.

**File-qualified names:** none (neither name is in `notes/weak-port-dupnames.json`).

**Rocq → Lean name map.**  `tvs_pin_word` `tvsPinWord`, `pnode_step_det` `pnodeStepDet`.

**Not ported:** nothing.
-/
import Weak.WeakEvInst

namespace Weak

open MachCSL MachCSL.Stdpp Iris.Std
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D
open Wlabel

/-- The bytes carried by a load label pin the loaded word. -/
theorem tvsPinWord {n : Nat} (w1 w2 : BitVec (8 * n)) (tvs : List (Nat × BitVec 8))
    (h1 : ∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w1 j))
    (h2 : ∀ j : Nat, j < n → (tvs.map Prod.snd)[j]? = some (nthByte w2 j)) :
    w1 = w2 :=
  bv_eq_of_bytes w1 w2 fun j hj => by
    have e := h1 j hj
    rw [h2 j hj] at e
    exact (Option.some.inj e).symm

/-- HEAD-DETERMINISM of `pnodeStep`, modulo the tick and `choose`. -/
theorem pnodeStepDet (m : SailM Unit) (rs : RegFile) (ib : Ibch) (d : DevStates) (l : Wlabel)
    (m1 : SailM Unit) (o1 : Option RegFile) (f1 : Option (Bool × Bool × Bool × Bool))
    (d1 : DevStates) (i1 : Option Ibch) (b1 : Option barrier_kind)
    (m2 : SailM Unit) (o2 : Option RegFile) (f2 : Option (Bool × Bool × Bool × Bool))
    (d2 : DevStates) (i2 : Option Ibch) (b2 : Option barrier_kind)
    (h1 : pnodeStep m rs ib d l m1 o1 f1 d1 i1 b1)
    (h2 : pnodeStep m rs ib d l m2 o2 f2 d2 i2 b2) :
    (m1 = m2 ∧ o1 = o2 ∧ f1 = f2 ∧ d1 = d2 ∧ i1 = i2 ∧ b1 = b2)
    ∨ (∃ v, m = .pure v ∧
        o1 = o2 ∧ f1 = f2 ∧ d1 = d2 ∧ i1 = i2 ∧ b1 = b2 ∧
        ∃ t1 t2 : Bool, m1 = riscvStep t1 ∧ m2 = riscvStep t2)
    ∨ (∃ p k, m = .impure (.ok (.choose p)) k ∧
        o1 = o2 ∧ f1 = f2 ∧ d1 = d2 ∧ i1 = i2 ∧ b1 = b2 ∧
        ∃ c1 c2, m1 = k c1 ∧ m2 = k c2) := by
  cases m with
  | pure v =>
    -- the tick
    obtain ⟨t1, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h1
    obtain ⟨t2, -, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h2
    exact Or.inr (Or.inl ⟨v, rfl, rfl, rfl, rfl, rfl, rfl, t1, t2, rfl, rfl⟩)
  | impure c k =>
    cases c with
    | error e => exact h1.elim
    | ok o =>
      cases o
      case memRead n va req =>
        dsimp only [pnodeStep] at h1 h2
        split at h1 <;> split at h2 <;> try contradiction
        · -- MMIO read: `devRead` is a function
          obtain ⟨w1, hr1, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h1
          obtain ⟨w2, hr2, -, rfl, rfl, rfl, rfl, rfl⟩ := h2
          rw [hr1] at hr2
          cases hr2
          exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
        · -- RAM reads: the label's bytes pin the word
          rcases h1 with ⟨-, w1, tvs1, -, hb1, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
            ⟨-, ⟨-, w1, tvs1, -, hb1, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
              ⟨-, w1, tvs1, -, hb1, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩ <;>
          rcases h2 with ⟨-, w2, tvs2, -, hb2, hl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
            ⟨-, ⟨-, w2, tvs2, -, hb2, hl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
              ⟨-, w2, tvs2, -, hb2, hl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩ <;>
          cases hl <;>
          (obtain rfl := tvsPinWord w1 w2 _ hb1 hb2
           exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩)
      case memWrite n va req =>
        dsimp only [pnodeStep] at h1 h2
        split at h1 <;> split at h2 <;> try contradiction
        · -- MMIO write: `devWrite` is a function
          split at h1
          · next v1 hv1 =>
            split at h2
            · next v2 hv2 =>
              rw [hv1] at hv2
              cases hv2
              obtain ⟨hw1, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h1
              obtain ⟨hw2, -, rfl, rfl, rfl, rfl, rfl⟩ := h2
              rw [hw1] at hw2
              cases hw2
              exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
            · exact h2.elim
          · exact h1.elim
        · -- RAM writes: the three arms carry distinct labels
          split at h1
          · next v1 hv1 =>
            split at h2
            · next v2 hv2 =>
              rw [hv1] at hv2
              cases hv2
              rcases h1 with ⟨-, ⟨-, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
                ⟨-, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩⟩ <;>
              rcases h2 with ⟨-, ⟨-, hl, rfl, rfl, rfl, rfl, rfl, rfl⟩ |
                ⟨-, ⟨hl, rfl, rfl, rfl, rfl, rfl, rfl⟩ | ⟨hl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩⟩ <;>
              cases hl <;>
              exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
            · exact h2.elim
          · exact h1.elim
      case choose p =>
        -- the chosen value
        obtain ⟨c1, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h1
        obtain ⟨c2, -, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h2
        exact Or.inr (Or.inr ⟨p, k, rfl, rfl, rfl, rfl, rfl, rfl, c1, c2, rfl, rfl⟩)
      case readRam => exact h1.elim
      case writeRam => exact h1.elim
      all_goals
        obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h1
        obtain ⟨-, rfl, rfl, rfl, rfl, rfl, rfl⟩ := h2
        exact Or.inl ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end Weak
