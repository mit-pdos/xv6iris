/-
Weak: **`textOkB` of the 4-byte words `Wa0c` (`jal push_off`), `Wa12` (`jal holding`), `Wa24`
(`jal mycpu`) of xv6's real `acquire`, generic in the pc**: the decode footprints (`rfF` of
`ext_decode` at the word, a constant so `rff_auto` does not crawl the decoder) and
`AxSpinE7.tokB`.  (The fourth word, the amoswap `Wa1c`, is decoded by the amoswap leaf.)

Rocq: `iris/AxSpinAqd.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. KERNEL DRIFT (`AxSpinAq` deviation 1): the `jal mycpu` word is this tree's
   `Wa24 = 0x4e1000ef` (Rocq 0x4bb000ef) and decodes to the drifted `a24` (immediate 3296);
   `Wa0c = 0xfbbff0ef` and `Wa12 = 0xf89ff0ef` match Rocq.  All three are tied to
   `Xv6/KernelImage.lean` by `AxSpinAq.aqCodeImg` (acquire + 0x0c / 0x12 / 0x24).
2. DECODE (as `AxSpinPOd` deviation 2): Rocq's `kd_fbbff0ef`/`kd_f89ff0ef`/`kd_4bb000ef`
   (KernelDecode*) are not ported; the decode premise of `tokB` is `WkEntryNew.execAnyCfg` of
   the kernel walks of the decoder on the machine reference map (`AxSpinAq.walk0cM`/`walk12M`/
   `walk24M`) and the supervisor reference map (the Lean-only `AxSpinAqd.walk*S` here,
   `kernel_rfl`).  The `rfF` footprints are `rff_auto` after pruning the decoder's pattern
   tests on the literal (the `AxSpinE7.rfFDec0e` recipe).
3. Q7 (`AxSpinE7` deviation 4): `tokB` takes `sfAnnB 32 w = false`, discharged inside each
   proof by `decide` at the literal word (the statements are Rocq's).
4. TYPES (`AxSpinAq` deviation 2): `mword_of_int W : mword 32` ↦ the `BitVec 32` constant `W`,
   `text_at4_S` ↦ `textAt4S`, `text_okB` ↦ `textOkB`; section variables `σi T satp0` are
   explicit arguments.  Stage C plays no role (no row positions).

**Rocq → Lean name map.**  `rfF_da0c` `rfFDa0c`, `rfF_da12` `rfFDa12`, `rfF_da24` `rfFDa24`,
`tw4_a0c` `tw4A0c`, `tw4_a12` `tw4A12`, `tw4_a24` `tw4A24` (none in the duplicated-name table;
all grepped absent from the tip).  Lean-only (file-qualified): `AxSpinAqd.walk0cS`,
`AxSpinAqd.walk12S`, `AxSpinAqd.walk24S`.

**Dropped:** nothing (Rocq 6 lemmas; Lean 6 + 3 Lean-only).  **Not ported:** the `Print
Assumptions` line (the lint's axiom check covers it).
-/
import Weak.AxSpinAq

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open LeanRV64D LeanRV64D.Functions

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_da0c`: `jal push_off` (0xfbbff0ef). -/
theorem rfFDa0c : rfF (ext_decode Wa0c) := by
  unfold Wa0c ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_da12`: `jal holding` (0xf89ff0ef). -/
theorem rfFDa12 : rfF (ext_decode Wa12) := by
  unfold Wa12 ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_da24`: `jal mycpu` (0x4e1000ef, deviation 1). -/
theorem rfFDa24 : rfF (ext_decode Wa24) := by
  unfold Wa24 ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

/-! Lean-only (deviation 2): the decode walks on the supervisor reference map. -/

/-- (Lean-only, deviation 2) the decode walk of `Wa0c` on the supervisor reference map. -/
theorem AxSpinAqd.walk0cS : runRead WkEntryNew.drefS0 (ext_decode Wa0c) = some (a0c, true) := by
  kernel_rfl

/-- (Lean-only, deviation 2) the decode walk of `Wa12` on the supervisor reference map. -/
theorem AxSpinAqd.walk12S : runRead WkEntryNew.drefS0 (ext_decode Wa12) = some (a12, true) := by
  kernel_rfl

/-- (Lean-only, deviation 2) the decode walk of `Wa24` on the supervisor reference map. -/
theorem AxSpinAqd.walk24S : runRead WkEntryNew.drefS0 (ext_decode Wa24) = some (a24, true) := by
  kernel_rfl

section toks
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-- Rocq `tw4_a0c` (deviations 2, 3). -/
theorem tw4A0c (pc : BitVec 64) : textAt4S σi T pc Wa0c → textOkB σi T satp0 pc false a0c :=
  fun H => tokB σi T satp0 _ _ _ H (by decide) rfFDa0c
    (WkEntryNew.execAnyCfg _ _ AxSpinAq.walk0cM AxSpinAqd.walk0cS)

/-- Rocq `tw4_a12` (deviations 2, 3). -/
theorem tw4A12 (pc : BitVec 64) : textAt4S σi T pc Wa12 → textOkB σi T satp0 pc false a12 :=
  fun H => tokB σi T satp0 _ _ _ H (by decide) rfFDa12
    (WkEntryNew.execAnyCfg _ _ AxSpinAq.walk12M AxSpinAqd.walk12S)

/-- Rocq `tw4_a24` (deviations 1, 2, 3). -/
theorem tw4A24 (pc : BitVec 64) : textAt4S σi T pc Wa24 → textOkB σi T satp0 pc false a24 :=
  fun H => tokB σi T satp0 _ _ _ H (by decide) rfFDa24
    (WkEntryNew.execAnyCfg _ _ AxSpinAq.walk24M AxSpinAqd.walk24S)

end toks

end Weak
