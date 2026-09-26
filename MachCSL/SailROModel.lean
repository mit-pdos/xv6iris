/-
MachCSL: the model's read-only, total computations (`SailRO`, lane
AND-ELIM): the leaf lemmas `sail_ro` uses.

* `ceOk e`: `currentlyEnabled e` is read-only and total.  It fails for 32
  extensions: the 29 the generated `currentlyEnabled` has NO clause for
  (its `assert false` fall-through: `Zkr`, `Zfh`, `Zfhmin`, `Zdinx`, `Zhinx`,
  `Zhinxmin`, `Zfa`, `Zfbfmin`, `Zcd`, `Zcf`, `Zbkx`, `Zibi`, the scalar and
  vector crypto extensions, `Zvabd`, `Zvbb`, `Zvbc`, `Zvfbfmin`, `Zvfbfwma`),
  and three whose clause EAGERLY reaches a failure: `Zvfh` (`Zfhmin`),
  `Zvfhmin` (`Zvfh`), `Zicfilp` (`get_xLPE` of a virtual privilege is an
  `internal_error`, and the privilege is read, any value).
* `ro_currentlyEnabled`: by the definition's own well-founded order
  (`currentlyEnabled_measure`), one lemma per measure level, the mutual
  helpers (`is_sstateen_accessible`, `get_sstateen`,
  `virtual_memory_supported`, `is_hstateen_accessible`, `get_hstateen`,
  `check_stateen_bit`, `is_zfinx_enabled_by_stateen`) at their own levels.
-/
import MachCSL.SailRO

namespace MachCSL

open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- `currentlyEnabled e` is read-only and total (see the header). -/
def ceOk : extension → Bool
  | .Ext_Zibi | .Ext_Zicfilp | .Ext_Zfa | .Ext_Zfbfmin | .Ext_Zfh | .Ext_Zfhmin | .Ext_Zdinx
  | .Ext_Zcd | .Ext_Zcf | .Ext_Zbkx | .Ext_Zknd | .Ext_Zkne | .Ext_Zknh | .Ext_Zkr | .Ext_Zksed
  | .Ext_Zksh | .Ext_Zhinx | .Ext_Zhinxmin | .Ext_Zvabd | .Ext_Zvfbfmin | .Ext_Zvfbfwma
  | .Ext_Zvfh | .Ext_Zvfhmin | .Ext_Zvbb | .Ext_Zvbc | .Ext_Zvkb | .Ext_Zvkg | .Ext_Zvkned
  | .Ext_Zvknha | .Ext_Zvknhb | .Ext_Zvksed | .Ext_Zvksh => false
  | _ => true

/-- One measure level of `currentlyEnabled`. -/
local macro "ro_ce_level" : tactic => `(tactic| (
  intro e hm hok
  cases e <;> (first | (exfalso; revert hm; decide) | (exfalso; revert hok; decide) | skip)
  all_goals (simp only [currentlyEnabled]; sail_ro)))

theorem ro_ce0 : ∀ e, currentlyEnabled_measure e = 0 → ceOk e = true →
    SailRO (currentlyEnabled e) := by ro_ce_level

macro_rules | `(tactic| sail_ro_leaf) => `(tactic| (apply ro_ce0 <;> decide))

theorem ro_ce1 : ∀ e, currentlyEnabled_measure e = 1 → ceOk e = true →
    SailRO (currentlyEnabled e) := by ro_ce_level

macro_rules | `(tactic| sail_ro_leaf) => `(tactic| (apply ro_ce1 <;> decide))

theorem ro_is_sstateen_accessible : SailRO (is_sstateen_accessible ()) := by
  sail_ro

macro_rules | `(tactic| sail_ro_leaf) => `(tactic| exact ro_is_sstateen_accessible)

theorem ro_ce2 : ∀ e, currentlyEnabled_measure e = 2 → ceOk e = true →
    SailRO (currentlyEnabled e) := by ro_ce_level

macro_rules | `(tactic| sail_ro_leaf) => `(tactic| (apply ro_ce2 <;> decide))

theorem ro_get_sstateen (idx : Nat) : SailRO (get_sstateen idx) := by
  sail_ro

theorem ro_virtual_memory_supported : SailRO (virtual_memory_supported ()) := by
  sail_ro

macro_rules | `(tactic| sail_ro_leaf) => `(tactic| exact ro_get_sstateen _)
macro_rules | `(tactic| sail_ro_leaf) => `(tactic| exact ro_virtual_memory_supported)

theorem ro_ce3 : ∀ e, currentlyEnabled_measure e = 3 → ceOk e = true →
    SailRO (currentlyEnabled e) := by ro_ce_level

macro_rules | `(tactic| sail_ro_leaf) => `(tactic| (apply ro_ce3 <;> decide))

theorem ro_ce4 : ∀ e, currentlyEnabled_measure e = 4 → ceOk e = true →
    SailRO (currentlyEnabled e) := by ro_ce_level

macro_rules | `(tactic| sail_ro_leaf) => `(tactic| (apply ro_ce4 <;> decide))

theorem ro_is_hstateen_accessible : SailRO (is_hstateen_accessible ()) := by
  sail_ro

macro_rules | `(tactic| sail_ro_leaf) => `(tactic| exact ro_is_hstateen_accessible)

theorem ro_ce5 : ∀ e, currentlyEnabled_measure e = 5 → ceOk e = true →
    SailRO (currentlyEnabled e) := by ro_ce_level

macro_rules | `(tactic| sail_ro_leaf) => `(tactic| (apply ro_ce5 <;> decide))

theorem ro_get_mstateen (idx : Nat) : SailRO (get_mstateen idx) := by
  sail_ro

theorem ro_get_hstateen (idx : Nat) : SailRO (get_hstateen idx) := by
  sail_ro

macro_rules | `(tactic| sail_ro_leaf) => `(tactic| exact ro_get_mstateen _)
macro_rules | `(tactic| sail_ro_leaf) => `(tactic| exact ro_get_hstateen _)

theorem ro_check_stateen_bit (p : Privilege) (b : stateen_bit) (k : Nat) :
    SailRO (check_stateen_bit p b k) := by
  sail_ro

macro_rules | `(tactic| sail_ro_leaf) => `(tactic| exact ro_check_stateen_bit _ _ _)

theorem ro_is_zfinx_enabled_by_stateen : SailRO (is_zfinx_enabled_by_stateen ()) := by
  sail_ro

macro_rules | `(tactic| sail_ro_leaf) => `(tactic| exact ro_is_zfinx_enabled_by_stateen)

theorem ro_ce9 : ∀ e, currentlyEnabled_measure e = 9 → ceOk e = true →
    SailRO (currentlyEnabled e) := by ro_ce_level

/-- **`currentlyEnabled` is read-only and total** for every extension with a
live, total clause. -/
theorem ro_currentlyEnabled (e : extension) (h : ceOk e = true) :
    SailRO (LeanRV64D.Functions.currentlyEnabled e) := by
  cases e <;> first
    | (exfalso; revert h; decide)
    | exact ro_ce0 _ (by decide) h
    | exact ro_ce1 _ (by decide) h
    | exact ro_ce2 _ (by decide) h
    | exact ro_ce3 _ (by decide) h
    | exact ro_ce4 _ (by decide) h
    | exact ro_ce5 _ (by decide) h
    | exact ro_ce9 _ (by decide) h

macro_rules | `(tactic| sail_ro_leaf) => `(tactic| (apply ro_currentlyEnabled; decide))

end MachCSL
