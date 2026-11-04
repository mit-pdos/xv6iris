/-
Weak: **`textOkB` of the 4-byte words `Wq30`, `Wp08`, `Wp0c`, `Wp16` of xv6's real `push_off` /
`pop_off`, generic in the pc**: the decode footprints (`rfF` of `ext_decode` at the word, a
constant so `rff_auto` does not crawl the decoder) and `AxSpinE7.tokB`.  Split by check time.

Rocq: `iris/AxSpinPOd2.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. KERNEL DRIFT (`AxSpinPO` deviation 1): the `jal mycpu` word is this tree's
   `Wp08 = 0x4bd000ef` (Rocq 0x497000ef) and decodes to the drifted `p08` (immediate 3260); the
   other three words match Rocq.
2. DECODE (as `AxSpinE7` deviation 5): Rocq's `kd_XXXXXXXX` (KernelDecode*) are not ported; the
   decode premise of `tokB` is `WkEntryNew.execAnyCfg` of the kernel walks of the decoder on the
   machine reference map (`AxSpinPO.walk*M`) and the supervisor reference map (the Lean-only
   `AxSpinPOd2.walk*S` here, `kernel_rfl`).  The `rfF` footprints are `rff_auto` after pruning the
   decoder's pattern tests on the literal (the `AxSpinE7.rfFDec0e` recipe).
3. Q7 (`AxSpinE7` deviation 4): `tokB` takes `sfAnnB 32 w = false`, discharged inside each
   proof by `decide` at the literal word (the statements are Rocq's).
4. TYPES (`AxSpinPO` deviation 2): `mword_of_int W : mword 32` ↦ the `BitVec 32` constant `W`,
   `text_at4_S` ↦ `textAt4S`, `text_okB` ↦ `textOkB`; section variables `σi T satp0` are
   explicit arguments.

**Rocq → Lean name map.**  `rfF_dq30` `rfFDq30`, `rfF_dp08` `rfFDp08`, `rfF_dp0c` `rfFDp0c`, `rfF_dp16` `rfFDp16`,
`tw4_q30` `tw4Q30`, `tw4_p08` `tw4P08`, `tw4_p0c` `tw4P0c`, `tw4_p16` `tw4P16` (none in the
duplicated-name table).  Lean-only (file-qualified): `AxSpinPOd2.walkQ30S`, `AxSpinPOd2.walkP08S`, `AxSpinPOd2.walkP0cS`, `AxSpinPOd2.walkP16S`.

**Dropped:** nothing (Rocq 8 lemmas; Lean 8 + 4 Lean-only).  **Not ported:** the `Print
Assumptions` line (the lint's axiom check covers it).
-/
import Weak.AxSpinPO

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_dq30`: `srli a5,s1,1` (0x0014d793). -/
theorem rfFDq30 : rfF (ext_decode Wq30) := by
  unfold Wq30 ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_dp08`: `jal mycpu` (0x4bd000ef). -/
theorem rfFDp08 : rfF (ext_decode Wp08) := by
  unfold Wp08 ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_dp0c`: `csrr a5,sstatus` (0x100027f3). -/
theorem rfFDp0c : rfF (ext_decode Wp0c) := by
  unfold Wp0c ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_dp16`: `bge zero,a5,panic` (0x02f05363). -/
theorem rfFDp16 : rfF (ext_decode Wp16) := by
  unfold Wp16 ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

/-! Lean-only (deviation 2): the decode walks on the supervisor reference map. -/

/-- (Lean-only, deviation 2) the decode walk of `Wq30` on the supervisor reference map. -/
theorem AxSpinPOd2.walkQ30S : runRead WkEntryNew.drefS0 (ext_decode Wq30) = some (q30, false) := by
  kernel_rfl

/-- (Lean-only, deviation 2) the decode walk of `Wp08` on the supervisor reference map. -/
theorem AxSpinPOd2.walkP08S : runRead WkEntryNew.drefS0 (ext_decode Wp08) = some (p08, false) := by
  kernel_rfl

/-- (Lean-only, deviation 2) the decode walk of `Wp0c` on the supervisor reference map. -/
theorem AxSpinPOd2.walkP0cS : runRead WkEntryNew.drefS0 (ext_decode Wp0c) = some (p0c, false) := by
  kernel_rfl

/-- (Lean-only, deviation 2) the decode walk of `Wp16` on the supervisor reference map. -/
theorem AxSpinPOd2.walkP16S : runRead WkEntryNew.drefS0 (ext_decode Wp16) = some (p16, false) := by
  kernel_rfl

section toks
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-- Rocq `tw4_q30` (deviations 2, 3). -/
theorem tw4Q30 (pc : BitVec 64) : textAt4S σi T pc Wq30 → textOkB σi T satp0 pc false q30 :=
  fun H => tokB σi T satp0 _ _ _ H (by decide) rfFDq30
    (WkEntryNew.execAnyCfg _ _ AxSpinPO.walk30M AxSpinPOd2.walkQ30S)

/-- Rocq `tw4_p08` (deviations 2, 3). -/
theorem tw4P08 (pc : BitVec 64) : textAt4S σi T pc Wp08 → textOkB σi T satp0 pc false p08 :=
  fun H => tokB σi T satp0 _ _ _ H (by decide) rfFDp08
    (WkEntryNew.execAnyCfg _ _ AxSpinPO.walkP08M AxSpinPOd2.walkP08S)

/-- Rocq `tw4_p0c` (deviations 2, 3). -/
theorem tw4P0c (pc : BitVec 64) : textAt4S σi T pc Wp0c → textOkB σi T satp0 pc false p0c :=
  fun H => tokB σi T satp0 _ _ _ H (by decide) rfFDp0c
    (WkEntryNew.execAnyCfg _ _ AxSpinPO.walkP0cM AxSpinPOd2.walkP0cS)

/-- Rocq `tw4_p16` (deviations 2, 3). -/
theorem tw4P16 (pc : BitVec 64) : textAt4S σi T pc Wp16 → textOkB σi T satp0 pc false p16 :=
  fun H => tokB σi T satp0 _ _ _ H (by decide) rfFDp16
    (WkEntryNew.execAnyCfg _ _ AxSpinPO.walkP16M AxSpinPOd2.walkP16S)

end toks

end Weak
