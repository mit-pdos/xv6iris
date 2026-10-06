/-
Weak: **the weak-tier stack ownership bundle** (M4 batch 4).

Rocq: `iris/WkStackOwn.v` @ xxvzwolszwmp.

The Rocq header, in substance (Rocq vocabulary).

The `↦w₈`/`wpt8` respell of `StackOwn.stack_own_phys`, for the weak ports of the
M-mode boot functions (`wwp_timerinit`/`wwp_start` and the composed entry cone):
the porting-table swap `a ↦ₚ₈{dq} w  →  vwp_hold (wpt8 a dq w) ws` applied to the
whole `stack_own_phys` suite.

The bundle is a `vProp` (`wstack_own_phys`), consumed by the chains under
`vwp_hold` at the hart's current `wstate`; because `vProp`s are monotone in the
view, `vwp_hold_mono` carries it across every step for free (`wstack_own_mono`
below is that instance).  The lemma suite mirrors `StackOwn`'s scripts -- the
only change is the BI it lives in.

NOTE (recorded porting-table delta): `phys_word_pointsto` lives in the era
`gen_heap`, whose domain is RAM by construction, so the SC chains never state
`addr_is_ram` for stack slots.  `wpt8` is address-keyed ghost state with no RAM
tie, so the weak chains carry explicit `addr_is_ram (pa_add (pa_stk sp k) j)`
PREMISES over the symbolic frame slots -- that pure side is deliberately NOT
bundled here.

**Deviations from Rocq.**

1. NAMES: the tree's camelCase (map below); vocabulary as `Weak/WeakWord8.lean`
   deviation 1 (`bv 64` ↦ `BitVec 64`, `Arch.pa` ↦ `PAddr`, `S i` ↦ `i + 1`).
2. `pa_stk` (+ `pa_stk_assoc`, `pa_stk_shift`) is defined in the SC
   `StackOwn.v`, which has no literal Lean port (its Lean analog is
   `MachCSL.KCtx.stackOwn`, which spells slot addresses inline as
   `sp - 8#64 * BitVec.ofNat 64 k`).  The weak line needs it (WkStartNew,
   WkTimerinit use it), so it is ported HERE as `paStk sp k := sp - 8#64 *
   BitVec.ofNat 64 k` (Rocq `add_vec_int sp (- (8 * k))`; equal modulo `2^64`),
   with `paStkAssoc` / `paStkShift`, plus the Lean-only `paStkShift'` (the
   `k + a + 1` summand order that `bigSepL_append` produces).
3. `wstack_own_phys` uses the ambient `cpu_id`; Lean has no ambient hart, so the
   hart is an explicit first argument `c : CPU` of `wstackOwnPhys` and of every
   lemma (as WeakWord8 deviation 4).
4. STATEMENT SHAPES (WeakWord8 deviation 2): Rocq `A -∗ B -∗ C` is `A ⊢ B -∗ C`.
5. Rocq's `Print Assumptions` has no Lean counterpart (the lint bans axioms).

**Rocq → Lean name map.**  `pa_stk` `paStk`, `pa_stk_assoc` `paStkAssoc`,
`pa_stk_shift` `paStkShift`, `wstack_own_phys` `wstackOwnPhys`,
`wstack_own_phys_0` `wstackOwnPhys_0`, `wstack_own_phys_app` `wstackOwnPhys_app`,
`wstack_own_phys_split` `wstackOwnPhys_split`, `wstack_own_phys_1`
`wstackOwnPhys_1`, `wstack_own_phys_1_intro` `wstackOwnPhys_1_intro`,
`wstack_own_phys_split_1` `wstackOwnPhys_split_1`, `wstack_own_phys_split_2`
`wstackOwnPhys_split_2`, `wstack_own_phys_2_elim` `wstackOwnPhys_2_elim`,
`wstack_own_phys_2_intro` `wstackOwnPhys_2_intro`, `vwp_hold_ent`
`WkStackOwn.vwpHold_ent` (FILE-QUALIFIED: duplicated name), `wstack_own_mono`
`wstackOwnMono`.

**Dropped lemmas.**  None.
-/
import Weak.WeakWord8

namespace Weak

open Iris Iris.BI Iris.BI.MonPred Iris.ProofMode Iris.Std
open MachCSL MachCSL.Stdpp

/-! ## The stack-slot address (`StackOwn.pa_stk`) -/

/-- `paStk sp k` is the address `8*k` bytes below `sp` -- the base of the `k`-th
stack slot counted downward from `sp`. -/
def paStk (sp : PAddr) (k : Nat) : PAddr := sp - 8#64 * BitVec.ofNat 64 k

/-- Stacking two downward shifts adds the depths. -/
theorem paStkAssoc (sp : PAddr) (a b : Nat) : paStk (paStk sp a) b = paStk sp (a + b) := by
  unfold paStk; bv_omega

theorem paStkShift (sp : PAddr) (a i : Nat) : paStk sp (a + i + 1) = paStk (paStk sp a) (i + 1) := by
  unfold paStk; bv_omega

/-- Lean-only: the summand order `bigSepL_append` produces. -/
theorem paStkShift' (sp : PAddr) (a i : Nat) : paStk sp (i + a + 1) = paStk (paStk sp a) (i + 1) := by
  unfold paStk; bv_omega

/-! ## The bundle -/

section wstackOwnPhys
variable {GF : BundledGFunctors} [WeakGS GF]

/-- The weak stack bundle: `StackOwn.stack_own_phys` with `↦ₚ₈` swapped for
`wpt8Own`, at the `VProp` altitude. -/
def wstackOwnPhys (c : CPU) (sp : PAddr) (n : Nat) : VProp GF :=
  iprop(∃ ws : List (BitVec 64), ⌜ws.length = n⌝ ∗
    [∗list] i ↦ w ∈ ws, wpt8Own (GF := GF) c (paStk sp (i + 1)) w)

theorem wstackOwnPhys_0 (c : CPU) (sp : PAddr) : wstackOwnPhys (GF := GF) c sp 0 ⊣⊢ emp := by
  unfold wstackOwnPhys
  constructor
  · iintro -; itrivial
  · iintro -
    iexists []
    isplitr
    · ipureintro; rfl
    · iapply BigSepL.bigSepL_nil.2; itrivial

theorem wstackOwnPhys_app (c : CPU) (sp : PAddr) (n1 n2 : Nat) :
    wstackOwnPhys (GF := GF) c sp (n1 + n2) ⊣⊢
      wstackOwnPhys c sp n1 ∗ wstackOwnPhys c (paStk sp n1) n2 := by
  unfold wstackOwnPhys
  constructor
  · iintro ⟨%ws, %hlen, H⟩
    icases (BigSepL.bigSepL_take_drop (n := n1)).1 $$ H with ⟨H1, H2⟩
    isplitl [H1]
    · iexists ws.take n1
      isplitr
      · ipureintro; simp only [List.length_take]; omega
      · iexact H1
    · iexists ws.drop n1
      isplitr
      · ipureintro; simp only [List.length_drop]; omega
      · simp only [← paStkShift]
        iexact H2
  · iintro ⟨⟨%ws1, %h1, H1⟩, ⟨%ws2, %h2, H2⟩⟩
    iexists ws1 ++ ws2
    isplitr
    · ipureintro; simp only [List.length_append]; omega
    · iapply BigSepL.bigSepL_append.2
      isplitl [H1]
      · iexact H1
      · simp only [h1, paStkShift']
        iexact H2

theorem wstackOwnPhys_split (c : CPU) (sp : PAddr) (a n : Nat) (hle : a ≤ n) :
    wstackOwnPhys (GF := GF) c sp n ⊣⊢
      wstackOwnPhys c sp a ∗ wstackOwnPhys c (paStk sp a) (n - a) := by
  have h := wstackOwnPhys_app (GF := GF) c sp a (n - a)
  rwa [Nat.add_sub_of_le hle] at h

theorem wstackOwnPhys_1 (c : CPU) (sp : PAddr) :
    wstackOwnPhys (GF := GF) c sp 1 ⊣⊢ ∃ w : BitVec 64, wpt8Own c (paStk sp 1) w := by
  unfold wstackOwnPhys
  constructor
  · iintro ⟨%ws, %hlen, H⟩
    rcases ws with _ | ⟨w, _ | ⟨w', ws⟩⟩
    · simp at hlen
    · iexists w
      icases BigSepL.bigSepL_singleton.1 $$ H with H
      iexact H
    · simp at hlen
  · iintro ⟨%w, H⟩
    iexists [w]
    isplitr
    · ipureintro; rfl
    · iapply BigSepL.bigSepL_singleton.2
      iexact H

theorem wstackOwnPhys_1_intro (c : CPU) (sp : PAddr) (w : BitVec 64) :
    wpt8Own (GF := GF) c (paStk sp 1) w ⊢ wstackOwnPhys c sp 1 := by
  refine Entails.trans ?_ (wstackOwnPhys_1 c sp).2
  iintro H; iexists w; iexact H

theorem wstackOwnPhys_split_1 (c : CPU) (sp : PAddr) (a n : Nat) (hle : a ≤ n) :
    wstackOwnPhys (GF := GF) c sp n ⊢
      wstackOwnPhys c sp a ∗ wstackOwnPhys c (paStk sp a) (n - a) :=
  (wstackOwnPhys_split c sp a n hle).1

theorem wstackOwnPhys_split_2 (c : CPU) (sp : PAddr) (a n : Nat) (hle : a ≤ n) :
    wstackOwnPhys (GF := GF) c sp a ∗ wstackOwnPhys c (paStk sp a) (n - a) ⊢
      wstackOwnPhys c sp n :=
  (wstackOwnPhys_split c sp a n hle).2

theorem wstackOwnPhys_2_elim (c : CPU) (sp : PAddr) :
    wstackOwnPhys (GF := GF) c sp 2 ⊢ ∃ w1 w2 : BitVec 64,
      wpt8Own c (paStk sp 1) w1 ∗ wpt8Own c (paStk sp 2) w2 := by
  refine (wstackOwnPhys_app (GF := GF) c sp 1 1).1.trans ?_
  iintro ⟨H1, H2⟩
  icases (wstackOwnPhys_1 c sp).1 $$ H1 with ⟨%w1, H1⟩
  icases (wstackOwnPhys_1 c (paStk sp 1)).1 $$ H2 with ⟨%w2, H2⟩
  iexists w1, w2
  isplitl [H1]
  · iexact H1
  · rw [show paStk sp 2 = paStk (paStk sp 1) 1 from (paStkAssoc sp 1 1).symm]
    iexact H2

theorem wstackOwnPhys_2_intro (c : CPU) (sp : PAddr) (w1 w2 : BitVec 64) :
    wpt8Own (GF := GF) c (paStk sp 1) w1 ⊢
      wpt8Own c (paStk sp 2) w2 -∗ wstackOwnPhys c sp 2 := by
  iintro H1 H2
  iapply (wstackOwnPhys_app (GF := GF) c sp 1 1).2
  isplitl [H1]
  · iapply wstackOwnPhys_1_intro; iexact H1
  · iapply wstackOwnPhys_1_intro
    rw [paStkAssoc]
    iexact H2

/-! ## The `vwpHold` side: what the chains actually thread -/

theorem wstackOwnMono (c : CPU) (sp : PAddr) (n : Nat) (ws ws' : Wstate) :
    wsLe ws ws' →
      vwpHold (wstackOwnPhys (GF := GF) c sp n) ws ⊢ vwpHold (wstackOwnPhys (GF := GF) c sp n) ws' :=
  fun h => vwpHold_mono _ h

end wstackOwnPhys

section vwpHoldEnt
variable {GF : BundledGFunctors}

/-- An entailment between `VProp`s transports under `vwpHold` pointwise. -/
theorem WkStackOwn.vwpHold_ent (P Q : VProp GF) (ws : Wstate) :
    (P ⊢ Q) → vwpHold P ws ⊢ vwpHold Q ws :=
  fun h => vwpHold_mono' ws h

end vwpHoldEnt

end Weak
