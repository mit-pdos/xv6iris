/-
Weak: **W-SCO (A) — the phase-neutral stretches of the cycle** (plan rev 36 §C W-SCO (A) (1)(c)):
`ucPrelude`, `ucDispatch`, `run_hart_waiting`, `ucFinish` (every arm of the per-step match and
the epilogue), `tick_clock` are "no cycle event" footprints.  Lean-only.
-/
import Weak.SailCycleOrderFetch
import MachCSL.UCycleDefs

namespace Weak
open MachCSL Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open Sail.ArchSem (FreeM)
namespace SailCycleOrderFp
open SailCycleOrderK SailCycleOrderGW

/-! ## The phase-neutral stretches -/

set_option maxHeartbeats 3000000 in
@[fp_reg] theorem fpPrelude : fpT ucPrelude := by
  fp_walk

set_option maxHeartbeats 3000000 in
@[fp_reg] theorem fpDispatch : fpT ucDispatch := by
  fp_walk

set_option maxHeartbeats 3000000 in
@[fp_reg] theorem fpWaiting (wr : WaitReason) (ib : BitVec 32) :
    fpT (run_hart_waiting 0 wr ib false) := by
  fp_walk

set_option maxHeartbeats 3000000 in
@[fp_reg] theorem fpFinish (st : Step) : fpT (ucFinish st) := by
  fp_walk

set_option maxHeartbeats 3000000 in
@[fp_reg] theorem fpTickClock : fpT (tick_clock ()) := by
  fp_walk

end SailCycleOrderFp
end Weak
