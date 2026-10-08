/-
Weak: **the `rfF` (read-footprint) facts of nine of the ten register-only / control expanded
instructions of xv6's real `mycpu`** (`AxSpinE7.ins_xx`).  Split from AxSpinE7 for check time.
The nine are proved from the syntactic all-branches footprints `rf0` (AxSymEngine2 /
AxRelease6, plus SLLI and AUIPC here) via `rfFOfRf0`; c.ret's JALR is Rocq
`AxSpinE7c.rfF_ins1e`.

Rocq: `iris/AxSpinE7d.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. TYPES (as `AxSymEngine2` deviation 6): `mword 5` / `mword 6` / `mword 20` ↦ `BitVec 5` /
   `BitVec 6` / `BitVec 20`; Rocq `Regidx rs1` is `.Regidx rs1`.  `rfFOfRf0` is by induction on
   the `FreeM` tree, one case per outcome (Rocq's `destruct oc; simpl; …` script).
   `rf0Addi`/`rf0Add`/`rf0Addiw` case-split the `regidx` arguments (Rocq `destruct r1, r2`) and
   apply `rf0ExecuteITYPEADDI` / `rf0ExecuteRTYPEADD` / `rf0ExecuteADDIW`.  `rf0Slli`/`rf0Auipc`
   are `ax_sym2_rf0_solve` after unfolding `execute_SHIFTIOP` / `execute_UTYPE` (Rocq's explicit
   `rf0_bind`/`rf0_bind0` script; AUIPC's `PC` read is off both pins, `AxSymEngine2.rf0ReadPure`).
2. KERNEL DRIFT (`AxSpinE7` deviation 1): `ins12` carries this tree's immediate; its `rfF` is
   the same `rf0Addi` proof (generic in the immediate).

**Rocq → Lean name map.**  `rfF_of_rf0` `rfFOfRf0`, `rf0_addi` `rf0Addi`, `rf0_add` `rf0Add`,
`rf0_addiw` `rf0Addiw`, `rf0_slli` `rf0Slli`, `rf0_auipc` `rf0Auipc`, `rfF_ins00` … `rfF_ins1c`
`rfFIns00` … `rfFIns1c` (none in the duplicated-name table).  No Lean-only declarations.

**Dropped:** nothing (Rocq 15 lemmas; Lean 15).  **Not ported:** the `Print Assumptions` line
(the lint's axiom check covers it).
-/
import Weak.AxSpinE7
import Weak.AxRelease6

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- Rocq `rfF_of_rf0`. -/
theorem rfFOfRf0 {X : Type} (m : SailM X) : rf0 m → rfF m := by
  induction m with
  | pure y => intro _; trivial
  | impure call k ih =>
    intro hm
    cases call with
    | error e => trivial
    | ok o =>
      cases o
      case regRead r => exact ⟨hm.1, fun v => ih v (hm.2 v)⟩
      case regWrite r v => exact ⟨hm.1, ih _ hm.2⟩
      case instrAnnounce n w => exact ⟨hm.1, ih _ hm.2⟩
      case branchAnnounce n a => exact ih _ hm
      case cacheOp c => exact ih _ hm
      case tlbi c => exact ih _ hm
      case takeException c => exact ih _ hm
      case returnException c => exact ih _ hm
      case translationStart c => exact ih _ hm
      case translationEnd c => exact ih _ hm
      case cycleCount => exact ih _ hm
      case message c => exact ih _ hm
      case getCycleCount => exact ih _ hm
      all_goals exact hm.elim

/-- Rocq `rf0_addi`. -/
theorem rf0Addi (r1 r2 : regidx) (imm : BitVec 12) : rf0 (execute (.ITYPE (imm, r1, r2, .ADDI))) := by
  cases r1; cases r2
  exact rf0ExecuteITYPEADDI _ _ _

/-- Rocq `rf0_add`. -/
theorem rf0Add (r1 r2 r3 : regidx) : rf0 (execute (.RTYPE (r1, r2, r3, .ADD))) := by
  cases r1; cases r2; cases r3
  exact rf0ExecuteRTYPEADD _ _ _

/-- Rocq `rf0_addiw`. -/
theorem rf0Addiw (r1 r2 : regidx) (imm : BitVec 12) : rf0 (execute (.ADDIW (imm, r1, r2))) := by
  cases r1; cases r2
  exact rf0ExecuteADDIW _ _ _

/-- Rocq `rf0_slli`. -/
theorem rf0Slli (rs1 rd : BitVec 5) (shamt : BitVec 6) :
    rf0 (execute (.SHIFTIOP (shamt, .Regidx rs1, .Regidx rd, .SLLI))) := by
  show rf0 (execute_SHIFTIOP shamt (.Regidx rs1) (.Regidx rd) .SLLI)
  unfold execute_SHIFTIOP
  ax_sym2_rf0_solve

/-- Rocq `rf0_auipc`. -/
theorem rf0Auipc (rd : BitVec 5) (imm : BitVec 20) :
    rf0 (execute (.UTYPE (imm, .Regidx rd, .AUIPC))) := by
  show rf0 (execute_UTYPE imm (.Regidx rd) .AUIPC)
  unfold execute_UTYPE get_arch_pc
  repeat (first
    | exact AxSymEngine2.rf0Pure _
    | exact rf0RXBits _
    | exact rf0WXBits _ _
    | exact ⟨AxSymEngine2.notPin _ (by decide) (by decide), fun _ => trivial⟩
    | intro _
    | apply rf0Bind)

/-- Rocq `rfF_ins00`. -/
theorem rfFIns00 : rfF (execute ins00) := rfFOfRf0 _ (rf0Addi _ _ _)
/-- Rocq `rfF_ins06`. -/
theorem rfFIns06 : rfF (execute ins06) := rfFOfRf0 _ (rf0Addi _ _ _)
/-- Rocq `rfF_ins08`. -/
theorem rfFIns08 : rfF (execute ins08) := rfFOfRf0 _ (rf0Add _ _ _)
/-- Rocq `rfF_ins0a`. -/
theorem rfFIns0a : rfF (execute ins0a) := rfFOfRf0 _ (rf0Addiw _ _ _)
/-- Rocq `rfF_ins0c`. -/
theorem rfFIns0c : rfF (execute ins0c) := rfFOfRf0 _ (rf0Slli _ _ _)
/-- Rocq `rfF_ins0e`. -/
theorem rfFIns0e : rfF (execute ins0e) := rfFOfRf0 _ (rf0Auipc _ _)
/-- Rocq `rfF_ins12`. -/
theorem rfFIns12 : rfF (execute ins12) := rfFOfRf0 _ (rf0Addi _ _ _)
/-- Rocq `rfF_ins16`. -/
theorem rfFIns16 : rfF (execute ins16) := rfFOfRf0 _ (rf0Add _ _ _)
/-- Rocq `rfF_ins1c`. -/
theorem rfFIns1c : rfF (execute ins1c) := rfFOfRf0 _ (rf0Addi _ _ _)

end Weak
