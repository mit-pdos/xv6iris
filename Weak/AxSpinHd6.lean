/-
Weak: **the `rfF` (read-footprint) facts of the register-only / control expanded instructions
of xv6's real `holding`** (`AxSpinHd.hxx`): c.li / c.addi / c.addi4spn / c.addi16sp (ADDI),
c.mv (ADD), sub (RTYPE SUB), seqz (ITYPE SLTIU); both c.ret are `AxSpinE7c.rfFIns1e` (the same
JALR); c.bnez and jal are in AxSpinHd6b / AxSpinHd6c.  Split for check time (template
AxSpinE7d / AxSpinE7c).

Rocq: `iris/AxSpinHd6.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. TYPES (as `AxSpinE7d` deviation 1): `mword 5` / `mword 12` ↦ `BitVec 5` / `BitVec 12`;
   Rocq `Regidx rs1` is `.Regidx rs1`.  `rf0Sub` / `rf0Sltiu` are `ax_sym2_rf0_solve`
   (AxSymEngine2) after unfolding `execute_RTYPE` / `execute_ITYPE` (Rocq's explicit
   `rf0_bind`/`rf0_bind0` scripts).
2. `rfFH06` / `rfFH2a`: `h06`, `h2a` and `AxSpinE7.ins1e` are the same term, so the facts are
   `rfFIns1e` (as Rocq).

**Rocq → Lean name map.**  `rf0_sub` `rf0Sub`, `rf0_sltiu` `rf0Sltiu`, `rfF_h04` `rfFH04`,
`rfF_h06` `rfFH06`, `rfF_h08` `rfFH08`, `rfF_h10` `rfFH10`, `rfF_h14` `rfFH14`, `rfF_h1a`
`rfFH1a`, `rfF_h1e` `rfFH1e`, `rfF_h28` `rfFH28`, `rfF_h2a` `rfFH2a` (none in the
duplicated-name table; none defined elsewhere in the tree).  No Lean-only declarations.

**Dropped:** nothing (Rocq 11 lemmas; Lean 11).  **Not ported:** the `Print Assumptions` line
(the lint's axiom check covers it).
-/
import Weak.AxSpinHd
import Weak.AxSpinE7c

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

/-- Rocq `rf0_sub`. -/
theorem rf0Sub (rs2 rs1 rd : BitVec 5) :
    rf0 (execute (.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, .SUB))) := by
  show rf0 (execute_RTYPE (.Regidx rs2) (.Regidx rs1) (.Regidx rd) .SUB)
  unfold execute_RTYPE
  ax_sym2_rf0_solve

/-- Rocq `rf0_sltiu`. -/
theorem rf0Sltiu (rs1 rd : BitVec 5) (imm : BitVec 12) :
    rf0 (execute (.ITYPE (imm, .Regidx rs1, .Regidx rd, .SLTIU))) := by
  show rf0 (execute_ITYPE imm (.Regidx rs1) (.Regidx rd) .SLTIU)
  unfold execute_ITYPE
  ax_sym2_rf0_solve

/-- Rocq `rfF_h04`. -/
theorem rfFH04 : rfF (execute h04) := rfFOfRf0 _ (rf0Addi _ _ _)
/-- Rocq `rfF_h06`. -/
theorem rfFH06 : rfF (execute h06) := rfFIns1e
/-- Rocq `rfF_h08`. -/
theorem rfFH08 : rfF (execute h08) := rfFOfRf0 _ (rf0Addi _ _ _)
/-- Rocq `rfF_h10`. -/
theorem rfFH10 : rfF (execute h10) := rfFOfRf0 _ (rf0Addi _ _ _)
/-- Rocq `rfF_h14`. -/
theorem rfFH14 : rfF (execute h14) := rfFOfRf0 _ (rf0Add _ _ _)
/-- Rocq `rfF_h1a`. -/
theorem rfFH1a : rfF (execute h1a) := rfFOfRf0 _ (rf0Sub _ _ _)
/-- Rocq `rfF_h1e`. -/
theorem rfFH1e : rfF (execute h1e) := rfFOfRf0 _ (rf0Sltiu _ _ _)
/-- Rocq `rfF_h28`. -/
theorem rfFH28 : rfF (execute h28) := rfFOfRf0 _ (rf0Addi _ _ _)
/-- Rocq `rfF_h2a`. -/
theorem rfFH2a : rfF (execute h2a) := rfFIns1e

end Weak
