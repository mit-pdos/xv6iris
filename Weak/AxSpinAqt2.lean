/-
Weak: **`textOkB` of the compressed words 0x87ba, 0x2781, 0xffe5, 0xe888 of xv6's real
`acquire`, generic in the pc** (`AxSpinE7.tokR`); 0x2781 (`sext.w a5`) has mycpu's AST
`AxSpinE7.ins0a`; 0xe888 (`c.sd a0,16(s1)`) expands to `AxSpinAq.a28`.  Split by check time.

Rocq: `iris/AxSpinAqt2.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. KERNEL WORDS: these halfwords are `AxSpinAq.acquireText`'s (acquire + 0x1a / 0x20 / 0x22 /
   0x28) and match Rocq; they are tied to `Xv6/KernelImage.lean` by `AxSpinAq.aqCodeImg`.
2. DECODE (as `AxSpinAqt1` deviation 2): the decode premise is the read-only kernel walk at
   `MachCSL.drefMisa` + `execOfRunRead`; Rocq `kd_XXXX` not ported.  Rocq's generated
   `ke_e888` (the `C_SD` expansion) is not ported: the expansion is `fun _ => rfl` (as the
   `c.sw` expansions in `AxSpinPOt2`/`AxSpinPOt3`); Rocq `exec_execute_C_*` ↦ `execExecuteC*`.
3. Section variables (`σi T satp0`) are explicit arguments; the Rocq `Ltac tw` is the
   file-local macro `ax_spin_aqt2_tokr`.  Stage C plays no role (no row positions).

**Rocq → Lean name map.**  `twa_87ba` `twa87ba`, `twa_2781` `twa2781`, `twa_ffe5` `twaFfe5`,
`twa_e888` `twaE888` (none in the duplicated-name table; all grepped absent from the tip).
No Lean-only declarations.

**Dropped:** nothing (Rocq 4 lemmas; Lean 4).  **Not ported:** the `Print Assumptions` line
(the lint's axiom check covers it).
-/
import Weak.AxSpinAq
import Weak.AxRelease7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- Rocq `tw`: `tokR` with the decode by the kernel walk at `drefMisa`. -/
local macro "ax_spin_aqt2_tokr" h:term:max i0:term:max hex:term:max ht:term:max : tactic =>
  `(tactic| (
    refine tokR _ _ _ _ $h $i0 _ $ht ?_ ?_ True.intro $hex
    · unfold ext_decode_compressed encdec_compressed_backwards
      simp (config := { decide := true }) only [↓reduceIte]
      rff_auto
    · intro s hm
      refine execOfRunRead drefMisa _ s _ true ?_ (by ax_epi_ledger_krfl)
      intro r v hv
      unfold drefMisa at hv
      split at hv <;> simp only [Option.some.injEq, reduceCtorEq] at hv
      subst hv
      exact hm))

section toks
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `twa_87ba`: `c.mv a5, a4` (0x87ba). -/
theorem twa87ba (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x87ba)) :
    textOkB σi T satp0 pc true a1a := by
  ax_spin_aqt2_tokr (0x87ba#16) (.C_MV (.Regidx 15#5, .Regidx 14#5)) (execExecuteCMV _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `twa_2781`: `c.addiw a5, 0` = `sext.w a5` (0x2781). -/
theorem twa2781 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x2781)) :
    textOkB σi T satp0 pc true ins0a := by
  ax_spin_aqt2_tokr (0x2781#16) (.C_ADDIW (0#6, .Regidx 15#5)) (execExecuteCADDIW _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `twa_ffe5`: `c.bnez a5, +0x1a` (0xffe5, the spin back-edge). -/
theorem twaFfe5 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0xffe5)) :
    textOkB σi T satp0 pc true a22 := by
  ax_spin_aqt2_tokr (0xffe5#16) (.C_BNEZ (252#8, .Cregidx 7#3)) (execExecuteCBNEZ _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `twa_e888`: `c.sd a0, 16(s1)` (0xe888; deviation 2). -/
theorem twaE888 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0xe888)) :
    textOkB σi T satp0 pc true a28 := by
  ax_spin_aqt2_tokr (0xe888#16) (.C_SD (2#5, .Cregidx 1#3, .Cregidx 2#3)) (fun _ => rfl) H

end toks

end Weak
