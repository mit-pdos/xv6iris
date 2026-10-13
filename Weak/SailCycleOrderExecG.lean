/-
Weak: **W-SCO (A) — `execute` and its one `ExecuteAs` redirect under the residual invariant**
(plan rev 36 §C W-SCO (A) (1)(b)): at phase `instr` (after a non-sfence announce) every arm of
`execute` is admitted — `fence.i`'s ONE `Barrier_RISCV_i` needs exactly that phase, the 121 other
arms are footprints (`fpExecNotFI`); a decoded SFENCE.VMA word (one of `isS`) executes as a
footprint with no redirect at any phase.  Lean-only.
-/
import Weak.SailCycleOrderFetch
import Weak.SailCycleOrderAllExec

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
namespace SailCycleOrderFp
open SailCycleOrderK SailCycleOrderGW

/-! ## `execute` -/

set_option maxHeartbeats 3000000 in
/-- Every `execute` arm at phase `instr` (after a non-sfence announce): `fence.i`'s barrier is
admitted there, every other arm is a footprint. -/
@[g_reg] theorem gExecute (i : instruction) :
    good (fun _ _ => True) Rboot (fun p _ => p = .instr) .instr (execute i) := by
  cases h : isFI i
  · exact fpGood _ _ _ (fpExecNotFI i h) _ _ (fun _ _ => rfl)
  · cases i
    all_goals first
      | (exfalso; revert h; simp only [isFI]; decide)
      | good_walk

/-- `uxaExecAs` at phase `instr`: the ONE `ExecuteAs` redirect runs `execute` again there. -/
@[g_reg] theorem gExecAs (i : instruction) :
    good (fun _ _ => True) Rboot (fun p _ => p = .instr) .instr (uxaExecAs i) := by
  unfold uxaExecAs
  exact gBindQF _ _ _ _ _ _ _ (gExecute i) (fun p r hp => by
    subst hp
    cases r
    all_goals first
      | exact gExecute _
      | exact (rfl : Ph.instr = Ph.instr))

/-- `uxaExecAs` of a decoded SFENCE.VMA word (one of `isS`), at any phase: a footprint, no
redirect. -/
@[g_reg] theorem gExecAsS (i : instruction) (hi : isS i = true) (ph : Ph) :
    good (fun _ _ => True) Rboot (fun p _ => p = ph) ph (uxaExecAs i) := by
  unfold uxaExecAs
  exact gBindQF _ _ (fun p r => p = ph ∧ isExecAs r = false) _ _ _ _
    (fpGood _ _ _ (fpExecuteS i hi) _ ph (fun _ h => ⟨rfl, h⟩))
    (fun p r hr => by
      obtain ⟨hp, hr⟩ := hr
      subst hp
      cases r
      all_goals first
        | exact (rfl : p = p)
        | (simp [isExecAs] at hr))

end SailCycleOrderFp
end Weak
