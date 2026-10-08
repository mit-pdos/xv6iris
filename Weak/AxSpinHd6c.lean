/-
Weak: **the `rfF` (read-footprint) fact of holding's `jal mycpu`** (`AxSpinHd.h16`): nextPC and
PC reads, `jump_to`, the link write.  Split for check time.

Rocq: `iris/AxSpinHd6c.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. KERNEL DRIFT (`AxSpinHd` deviation 1): `h16`'s immediate is `3412#21` (Rocq `3374`); the
   proof is generic in it.
2. Script: Rocq `rfF_bind`/`rfF_read_reg; nseip`/`rfF_jump_to`/`rfF_bind0`/`rf0_wX_bits` ↦
   `rfFBind`/`rfFReadReg _ (AxSymEngine2.notPin …)`/`rfFJumpTo`/`rfFBind0`/`rf0WXBits`
   (AxSymCtl4, AxSpinE7c, AxSymEngine2); `destruct r` is `cases r`.

**Rocq → Lean name map.**  `rfF_h16` `rfFH16` (not in the duplicated-name table; not defined
elsewhere in the tree).  No Lean-only declarations.

**Dropped:** nothing (Rocq 1 lemma; Lean 1).  **Not ported:** the `Print Assumptions` line
(the lint's axiom check covers it).
-/
import Weak.AxSpinHd
import Weak.AxSpinE7c
import Weak.AxSymCtl4

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `rfF_h16`. -/
theorem rfFH16 : rfF (execute h16) := by
  show rfF (execute_JAL (3412#21) (.Regidx 1#5))
  unfold execute_JAL get_next_pc
  refine rfFBind _ _ (rfFReadReg _ (AxSymEngine2.notPin _ (by decide) (by decide))) (fun _ => ?_)
  refine rfFBind _ _ (rfFReadReg _ (AxSymEngine2.notPin _ (by decide) (by decide))) (fun _ => ?_)
  refine rfFBind _ _ (rfFJumpTo _) (fun r => ?_)
  cases r
  · exact rfFBind0 _ _ (rfFOfRf0 _ (rf0WXBits _ _)) trivial
  all_goals exact trivial

end Weak
