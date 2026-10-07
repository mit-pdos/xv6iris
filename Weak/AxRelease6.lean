/-
Weak: **`rf0` of `execute (ITYPE (_, _, _, ADDI))`** — the register-only footprint the compressed
arm of `AxRelease.instr4` asks for c.addi sp / c.addi4spn / c.addi16sp (RTYPE ADD, c.mv, is
`rf0ExecuteRTYPEADD` in `AxSymEngine2`).

Rocq: `iris/AxRelease6.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. TYPES (as `AxSymEngine2` deviation 6): `mword 5` / `mword 12` ↦ `BitVec 5` / `BitVec 12`.
   The proof is `AxSymEngine2`'s `ax_sym2_rf0_solve` (Rocq's explicit `rf0_bind`/`rf0_bind0`
   script) after unfolding `execute_ITYPE`.

**Rocq → Lean name map.**  `rf0_execute_ITYPE_ADDI` `rf0ExecuteITYPEADDI` (not in the
duplicated-name table).  No Lean-only declarations.

**Dropped:** nothing (Rocq 1 lemma; Lean 1).  **Not ported:** the `Print Assumptions` line (the
lint's axiom check covers it).
-/
import Weak.AxSymEngine2

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

theorem rf0ExecuteITYPEADDI (rs1 rd : BitVec 5) (imm : BitVec 12) :
    rf0 (execute (.ITYPE (imm, .Regidx rs1, .Regidx rd, .ADDI))) := by
  show rf0 (execute_ITYPE imm (.Regidx rs1) (.Regidx rd) .ADDI)
  unfold execute_ITYPE
  ax_sym2_rf0_solve

end Weak
