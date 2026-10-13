/-
Weak: **W-SCO (A) — the `execute` dispatcher** (plan rev 36 §C W-SCO (A) (1)(b)): every one of the
122 arms of `execute` (`model/Lean_RV64D/LeanRV64D/InstsEnd.lean:18769`, one per `instruction`
constructor) other than `FENCEI` is a "no cycle event" tree, by the per-clause lemmas of
`Weak/SailCycleOrderAllExec{1,2,3,4}.lean` (121 clauses; the 46 `ExecuteAs` clauses are `pure`).
`FENCEI` (the one `Barrier_RISCV_i`) is handled in `Weak/SailCycleOrderExecG.lean` (`gExecute`).
Lean-only.
-/
import Weak.SailCycleOrderAllExec1
import Weak.SailCycleOrderAllExec2
import Weak.SailCycleOrderAllExec3
import Weak.SailCycleOrderAllExec4

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
namespace SailCycleOrderFp

/-- The `fence.i` instruction (the one `execute` arm with a `Barrier_RISCV_i`). -/
def isFI (i : instruction) : Bool :=
  match i with
  | .FENCEI _ => true
  | _ => false

set_option maxHeartbeats 40000000 in
set_option maxRecDepth 20000 in
/-- **Every `execute` arm but `fence.i` is a "no cycle event" tree.** -/
theorem fpExecNotFI (i : instruction) (h : isFI i = false) : fpT (execute i) := by
  cases i
  all_goals first
    | (exfalso; revert h; simp only [isFI]; decide)
    | fp_walk

end SailCycleOrderFp
end Weak
