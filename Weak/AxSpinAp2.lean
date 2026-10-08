/-
Weak: **the remaining four 4-byte decodes of Rocq's `allocpid`** (`jal acquire` + 0x12,
`addiw a4,s1,1` + 0x20, `addi a0,a0,-1724` + 0x2a, `jal release` + 0x2e) with their read-free
footprints.  Split from AxSpinAp for check time.

Rocq: `iris/AxSpinAp2.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. KERNEL DRIFT (`AxSpinAp` deviation 1, Q18): the words `WA12`/`WA20`/`WA2a`/`WA2e` are
   Rocq's; this tree's kernel inlines `allocpid`, so they are not connected to the Lean image
   (the facts here are about the words alone and hold regardless).
2. DECODE PROOFS (as `AxSpinAp` deviation 4): Rocq's `kd_a18ff0ef`/`kd_0014871b`/
   `kd_94450513`/`kd_a84ff0ef` (KernelDecode*) are not ported; `decA12`/`decA20`/`decA2a`/
   `decA2e` are kernel walks of the decoder on the machine and supervisor reference maps
   (`AxSpinAp2.walkA*M/S`) combined by `WkEntryNew.execAnyCfg`; the `rfF` facts are `rff_auto`
   after pruning the decoder's pattern tests on the literal (Rocq `rfF_auto`).  The `misa`
   premise is `s.regs .misa = misaC` (Rocq `register_lookup misa s.(sregs) = MISA_C`).

**Rocq → Lean name map.**  `rfF_decA12`/`A20`/`A2a`/`A2e` `rfFDecA12`/`rfFDecA20`/`rfFDecA2a`/
`rfFDecA2e`, `decA12`/`decA20`/`decA2a`/`decA2e` same (none in the duplicated-name table).
Lean-only (file-qualified): `AxSpinAp2.walkA12M/S`, `AxSpinAp2.walkA20M/S`,
`AxSpinAp2.walkA2aM/S`, `AxSpinAp2.walkA2eM/S`.

**Dropped:** nothing (Rocq 8 lemmas; Lean 8 + 8 Lean-only).  **Not ported:** the
`Print Assumptions` line (the lint's axiom check covers it).
-/
import Weak.AxSpinAp

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_decA12`. -/
theorem rfFDecA12 : rfF (ext_decode WA12) := by
  unfold WA12 ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_decA20`. -/
theorem rfFDecA20 : rfF (ext_decode WA20) := by
  unfold WA20 ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_decA2a`. -/
theorem rfFDecA2a : rfF (ext_decode WA2a) := by
  unfold WA2a ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- Rocq `rfF_decA2e`. -/
theorem rfFDecA2e : rfF (ext_decode WA2e) := by
  unfold WA2e ext_decode encdec_backwards
  simp (config := { decide := true }) only [↓reduceIte]
  rff_auto

section walks
attribute [local semireducible] LeanRV64D.Functions.hartSupports
  LeanRV64D.Functions.currentlyEnabled

/-- (Lean-only, deviation 2) the decode walk of `WA12` on the machine reference map. -/
theorem AxSpinAp2.walkA12M : runRead drefM (ext_decode WA12) = some (ap12, true) := by kernel_rfl
/-- (Lean-only, deviation 2) the decode walk of `WA12` on the supervisor reference map. -/
theorem AxSpinAp2.walkA12S : runRead WkEntryNew.drefS0 (ext_decode WA12) = some (ap12, true) := by
  kernel_rfl
/-- (Lean-only, deviation 2) the decode walk of `WA20` on the machine reference map. -/
theorem AxSpinAp2.walkA20M : runRead drefM (ext_decode WA20) = some (ap20, true) := by kernel_rfl
/-- (Lean-only, deviation 2) the decode walk of `WA20` on the supervisor reference map. -/
theorem AxSpinAp2.walkA20S : runRead WkEntryNew.drefS0 (ext_decode WA20) = some (ap20, true) := by
  kernel_rfl
/-- (Lean-only, deviation 2) the decode walk of `WA2a` on the machine reference map. -/
theorem AxSpinAp2.walkA2aM : runRead drefM (ext_decode WA2a) = some (ap2a, true) := by kernel_rfl
/-- (Lean-only, deviation 2) the decode walk of `WA2a` on the supervisor reference map. -/
theorem AxSpinAp2.walkA2aS : runRead WkEntryNew.drefS0 (ext_decode WA2a) = some (ap2a, true) := by
  kernel_rfl
/-- (Lean-only, deviation 2) the decode walk of `WA2e` on the machine reference map. -/
theorem AxSpinAp2.walkA2eM : runRead drefM (ext_decode WA2e) = some (ap2e, true) := by kernel_rfl
/-- (Lean-only, deviation 2) the decode walk of `WA2e` on the supervisor reference map. -/
theorem AxSpinAp2.walkA2eS : runRead WkEntryNew.drefS0 (ext_decode WA2e) = some (ap2e, true) := by
  kernel_rfl

end walks

/-- Rocq `decA12` (deviation 2). -/
theorem decA12 (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA12) s = some (ap12, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp2.walkA12M AxSpinAp2.walkA12S s

/-- Rocq `decA20` (deviation 2). -/
theorem decA20 (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA20) s = some (ap20, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp2.walkA20M AxSpinAp2.walkA20S s

/-- Rocq `decA2a` (deviation 2). -/
theorem decA2a (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA2a) s = some (ap2a, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp2.walkA2aM AxSpinAp2.walkA2aS s

/-- Rocq `decA2e` (deviation 2). -/
theorem decA2e (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA2e) s = some (ap2e, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp2.walkA2eM AxSpinAp2.walkA2eS s

end Weak
