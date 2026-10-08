/-
Weak: **the `rfF` (read-footprint) fact of c.ret's expanded JALR of xv6's real `mycpu`**
(`AxSpinE7.ins1e`).  Split from AxSpinE7 for check time.

Rocq: `iris/AxSpinE7c.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. Tactics: Rocq `rfF_auto` / `rfF_solve` ↦ `rff_auto` (AxSpineOk2), with the callee lemmas
   applied first at reducible transparency (local macro `ax_spin_e7c_auto`).  The final
   `rfF_ins1e` script (`first [ … | idtac ]`) is the same callee list.
2. `zreg` writes: `rfFOfRf0` (AxSpinE7d) of AxSymEngine2 `rf0WXBits` (Rocq `rf0_wX_bits` after
   `unfold zreg`).  Lean `execute_JALR` reads the link address before the target (as Rocq).

**Rocq → Lean name map.**  `rfF_cE_Zicfilp` `rfFCEZicfilp`, `rfF_update_elp_state`
`rfFUpdateElpState`, `rfF_jump_to` `rfFJumpTo`, `rfF_ins1e` `rfFIns1e` (none in the
duplicated-name table).  No Lean-only declarations.

**Dropped:** nothing (Rocq 4 lemmas; Lean 4).  **Not ported:** the `Print Assumptions` line
(the lint's axiom check covers it).
-/
import Weak.AxSpinE7d

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `rfF_cE_Zicfilp`. -/
theorem rfFCEZicfilp : rfF (currentlyEnabled .Ext_Zicfilp) := by rff_auto

/-- Rocq `rfF_update_elp_state`. -/
theorem rfFUpdateElpState (r : regidx) : rfF (update_elp_state r) := by
  unfold update_elp_state
  refine rfFBind _ _ rfFCEZicfilp (fun b => ?_)
  cases b
  · exact trivial
  · rff_auto

/-- `rff_auto` with the JALR callees first (deviation 1). -/
local macro "ax_spin_e7c_auto" : tactic => `(tactic| repeat (first
      | with_reducible exact rfFCurrentlyEnabledZca
      | with_reducible exact rfFUpdateElpState _
      | rff_step
      | (refine ⟨?_, ?_⟩)
      | (intro h; rcases h with h | h <;> cases h)
      | (intro _)
      | exact True.intro
      | rfl))

/-- Rocq `rfF_jump_to`. -/
theorem rfFJumpTo (tg : BitVec 64) : rfF (jump_to tg) := by
  unfold jump_to
  ax_spin_e7c_auto

/-- Rocq `rfF_ins1e`. -/
theorem rfFIns1e : rfF (execute ins1e) := by
  show rfF (execute_JALR (zeros (n := 12)) (.Regidx 1#5) zreg)
  unfold execute_JALR
  refine rfFBind0 _ _ (rfFUpdateElpState _) ?_
  refine rfFBind _ _ (by unfold get_next_pc; rff_auto) (fun la => ?_)
  refine rfFBind _ _ (rfFOfRf0 _ (rf0RXBits 1#5)) (fun x => ?_)
  refine rfFBind _ _ trivial (fun tg => ?_)
  refine rfFBind _ _ (rfFJumpTo _) (fun r => ?_)
  split
  · exact rfFBind0 _ _ (rfFOfRf0 _ (rf0WXBits _ _)) trivial
  · exact trivial

end Weak
