/-
Weak: **`textOkB` of the 4-byte words `Wq0a`, `Wq10`, `Wq18`, `Wq2c` of xv6's real `push_off` /
`pop_off`, generic in the pc**: the decode footprints (`rfF` of `ext_decode` at the word, a
constant so `rff_auto` does not crawl the decoder) and `AxSpinE7.tokB`.  Split by check time.

Rocq: `iris/AxSpinPOd.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. KERNEL DRIFT (`AxSpinPO` deviation 1): the three `jal mycpu` words are this
   tree's `Wq10 = 0x52f000ef`, `Wq18 = 0x527000ef`, `Wq2c = 0x513000ef` (Rocq 0x509000ef /
   0x501000ef / 0x4ed000ef) and decode to the drifted `q10`/`q18`/`q2c` (immediates 3374 / 3366 /
   3346); `Wq0a = 0x100177f3` matches Rocq.
2. DECODE (as `AxSpinE7` deviation 5): Rocq's `kd_XXXXXXXX` (KernelDecode*) are not ported; the
   decode premise of `tokB` is `WkEntryNew.execAnyCfg` of the kernel walks of the decoder on the
   machine reference map (`AxSpinPO.walk*M`) and the supervisor reference map (the Lean-only
   `AxSpinPOd.walk*S` here, `kernel_rfl`).  The `rfF` footprints are `rff_auto` after pruning the
   decoder's pattern tests on the literal (the `AxSpinE7.rfFDec0e` recipe).
3. Q7 (`AxSpinE7` deviation 4): `tokB` takes `sfAnnB 32 w = false`, discharged inside each
   proof by `decide` at the literal word (the statements are Rocq's).
4. TYPES (`AxSpinPO` deviation 2): `mword_of_int W : mword 32` ↦ the `BitVec 32` constant `W`,
   `text_at4_S` ↦ `textAt4S`, `text_okB` ↦ `textOkB`; section variables `σi T satp0` are
   explicit arguments.

**Rocq → Lean name map.**  `rfF_dq0a` `rfFDq0a`, `rfF_dq10` `rfFDq10`, `rfF_dq18` `rfFDq18`, `rfF_dq2c` `rfFDq2c`,
`tw4_q0a` `tw4Q0a`, `tw4_q10` `tw4Q10`, `tw4_q18` `tw4Q18`, `tw4_q2c` `tw4Q2c` (none in the
duplicated-name table).  Lean-only (file-qualified): `AxSpinPOd.walkQ0aS`, `AxSpinPOd.walkQ10S`, `AxSpinPOd.walkQ18S`, `AxSpinPOd.walkQ2cS`.

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
/-- Rocq `rfF_dq0a`: `csrrci a5,sstatus,2` (0x100177f3). -/
theorem rfFDq0a : rfF (ext_decode Wq0a) := by
  unfold Wq0a ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_dq10`: `jal mycpu` (0x52f000ef). -/
theorem rfFDq10 : rfF (ext_decode Wq10) := by
  unfold Wq10 ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_dq18`: `jal mycpu` (0x527000ef). -/
theorem rfFDq18 : rfF (ext_decode Wq18) := by
  unfold Wq18 ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_dq2c`: `jal mycpu` (0x513000ef). -/
theorem rfFDq2c : rfF (ext_decode Wq2c) := by
  unfold Wq2c ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

/-! Lean-only (deviation 2): the decode walks on the supervisor reference map. -/

/-- (Lean-only, deviation 2) the decode walk of `Wq0a` on the supervisor reference map. -/
theorem AxSpinPOd.walkQ0aS : runRead WkEntryNew.drefS0 (ext_decode Wq0a) = some (q0a, false) := by
  kernel_rfl

/-- (Lean-only, deviation 2) the decode walk of `Wq10` on the supervisor reference map. -/
theorem AxSpinPOd.walkQ10S : runRead WkEntryNew.drefS0 (ext_decode Wq10) = some (q10, false) := by
  kernel_rfl

/-- (Lean-only, deviation 2) the decode walk of `Wq18` on the supervisor reference map. -/
theorem AxSpinPOd.walkQ18S : runRead WkEntryNew.drefS0 (ext_decode Wq18) = some (q18, false) := by
  kernel_rfl

/-- (Lean-only, deviation 2) the decode walk of `Wq2c` on the supervisor reference map. -/
theorem AxSpinPOd.walkQ2cS : runRead WkEntryNew.drefS0 (ext_decode Wq2c) = some (q2c, false) := by
  kernel_rfl

section toks
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

/-- Rocq `tw4_q0a` (deviations 2, 3). -/
theorem tw4Q0a (pc : BitVec 64) : textAt4S σi T pc Wq0a → textOkB σi T satp0 pc false q0a :=
  fun H => tokB σi T satp0 _ _ _ H (by decide) rfFDq0a
    (WkEntryNew.execAnyCfg _ _ AxSpinPO.walk0aM AxSpinPOd.walkQ0aS)

/-- Rocq `tw4_q10` (deviations 2, 3). -/
theorem tw4Q10 (pc : BitVec 64) : textAt4S σi T pc Wq10 → textOkB σi T satp0 pc false q10 :=
  fun H => tokB σi T satp0 _ _ _ H (by decide) rfFDq10
    (WkEntryNew.execAnyCfg _ _ AxSpinPO.walk10M AxSpinPOd.walkQ10S)

/-- Rocq `tw4_q18` (deviations 2, 3). -/
theorem tw4Q18 (pc : BitVec 64) : textAt4S σi T pc Wq18 → textOkB σi T satp0 pc false q18 :=
  fun H => tokB σi T satp0 _ _ _ H (by decide) rfFDq18
    (WkEntryNew.execAnyCfg _ _ AxSpinPO.walk18M AxSpinPOd.walkQ18S)

/-- Rocq `tw4_q2c` (deviations 2, 3). -/
theorem tw4Q2c (pc : BitVec 64) : textAt4S σi T pc Wq2c → textOkB σi T satp0 pc false q2c :=
  fun H => tokB σi T satp0 _ _ _ H (by decide) rfFDq2c
    (WkEntryNew.execAnyCfg _ _ AxSpinPO.walk2cM AxSpinPOd.walkQ2cS)

end toks

end Weak
