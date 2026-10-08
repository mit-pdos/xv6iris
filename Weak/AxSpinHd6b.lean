/-
Weak: **the `rfF` (read-footprint) fact of holding's c.bnez** (`AxSpinHd.h02`, BTYPE BNE): two
register reads, then on the taken branch a PC read and `jump_to`.  Split for check time.

Rocq: `iris/AxSpinHd6b.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. TYPES (as `AxSpinHd` deviation 2): `c7'` is `creg5 (.Cregidx 7#3)` (AxSymCtl2; Rocq
   `creg5 (Cregidx (mword_of_int 7))`), `rz'` is `zero_extend (m := 5) 0b00#2`; both
   `BitVec 5`.  The Rocq `change` to `execute_BTYPE … (Regidx rz') (Regidx c7') BNE` is a
   `show` (`zreg` and `creg2reg_idx (.Cregidx 7#3)` are those indices definitionally).
2. Script: Rocq `rfF_bind`/`rfF_of_rf0`/`rf0_rX_bits`/`rfF_read_reg; nseip`/`rfF_jump_to` ↦
   `rfFBind`/`rfFOfRf0`/`rf0RXBits`/`rfFReadReg _ (AxSymEngine2.notPin …)`/`rfFJumpTo`
   (AxSymCtl4, AxSpinE7c); the branch on `taken` is `cases` on the Bool.

**Rocq → Lean name map.**  `c7'` `AxSpinHd6b.c7'`, `rz'` `AxSpinHd6b.rz'` (file-qualified: short
names), `rfF_h02` `rfFH02` (none in the duplicated-name table; none defined elsewhere in the
tree).  No Lean-only declarations.

**Dropped:** nothing (Rocq 3 declarations; Lean 3).  **Not ported:** the `Print Assumptions`
line (the lint's axiom check covers it).
-/
import Weak.AxSpinHd
import Weak.AxSpinE7c
import Weak.AxSymCtl4

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `c7'`: compressed register 7 (`a5`). -/
def AxSpinHd6b.c7' : BitVec 5 := creg5 (.Cregidx 7#3)
/-- Rocq `rz'`: the zero register index. -/
def AxSpinHd6b.rz' : BitVec 5 := zero_extend (m := 5) 0b00#2

/-- Rocq `rfF_h02`. -/
theorem rfFH02 : rfF (execute h02) := by
  show rfF (execute_BTYPE (sign_extend (m := 13) (3#8 +++ 0b0#1)) (.Regidx AxSpinHd6b.rz')
    (.Regidx AxSpinHd6b.c7') .BNE)
  unfold execute_BTYPE
  refine rfFBind _ _ ?_ (fun taken => ?_)
  · refine rfFBind _ _ (rfFOfRf0 _ (rf0RXBits _)) (fun _ => ?_)
    exact rfFBind _ _ (rfFOfRf0 _ (rf0RXBits _)) (fun _ => trivial)
  · cases taken
    · exact trivial
    · exact rfFBind _ _ (rfFReadReg _ (AxSymEngine2.notPin _ (by decide) (by decide)))
        (fun _ => rfFJumpTo _)

end Weak
