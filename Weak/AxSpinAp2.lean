/-
Weak: **the remaining ten 4-byte decodes of the inlined allocpid copy** (`allocproc + 0x68 ..
+ 0x94`: `addiw a1,a3,1`, the scan's `auipc/addi a5 = proc`, `beq a4,a3`, `addi a5,a5,376`,
`bne a5,a2`, the nextpid write's `auipc a5` / `sw a1,1936(a5)`, `addi a0,a0,-1790`,
`jal release`) with their read-free footprints.  Split from AxSpinAp for check time.

Rocq: `iris/AxSpinAp2.v` @ xxvzwolszwmp (owner ruling Q18: RETARGETED to the inlined code).

## Deviations from Rocq

1. KERNEL INLINING (`AxSpinAp` deviation 1 and its design section, Q18): the words are the
   inlined copy's (`AxSpinAp.apCodeImg` checks them against the Lean kernel image), not Rocq
   allocpid's `WA12`/`WA20`/`WA2a`/`WA2e`; Rocq's `rfF_decA12`/`A20`/`A2a`/`A2e`,
   `decA12`/`A20`/`A2a`/`A2e` are REPLACED by `rfFDecA68` … `rfFDecA94`, `decA68` … `decA94`
   (same role: the `rfF` and decode premises of `tokB`).
2. DECODE PROOFS (as `AxSpinAp` deviation 4): no KernelDecode* lemmas; `decA*` are kernel walks
   of the decoder on the machine and supervisor reference maps (`AxSpinAp2.walkA*M/S`, which
   also confirm each instruction AST against its word) combined by `WkEntryNew.execAnyCfg`; the
   `rfF` facts are `rff_auto` after pruning the decoder's pattern tests on the literal (Rocq
   `rfF_auto`).  The `misa` premise is `s.regs .misa = misaC`.

**Rocq → Lean name map.**  See deviation 1 (none in the duplicated-name table).  Lean-only
(file-qualified): `AxSpinAp2.walkA*M/S` (10 × 2).

**Dropped:** Rocq allocpid's four decodes (deviation 1).  **Not ported:** the
`Print Assumptions` line (the lint's axiom check covers it).
-/
import Weak.AxSpinAp

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- `rfF` of a 4-byte decode at a word constant (file-local). -/
local macro "ax_spin_ap2_rffdec" w:ident : tactic =>
  `(tactic| (
    unfold $w ext_decode encdec_backwards
    simp (config := { decide := true }) only [↓reduceIte]
    rff_auto))

set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA68` (`addiw a1,a3,1`). -/
theorem rfFDecA68 : rfF (ext_decode WA68) := by ax_spin_ap2_rffdec WA68
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA6c` (`auipc a5,0x11`). -/
theorem rfFDecA6c : rfF (ext_decode WA6c) := by ax_spin_ap2_rffdec WA6c
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA70` (`addi a5,a5,-686`). -/
theorem rfFDecA70 : rfF (ext_decode WA70) := by ax_spin_ap2_rffdec WA70
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA76` (`beq a4,a3,-0x1a`). -/
theorem rfFDecA76 : rfF (ext_decode WA76) := by ax_spin_ap2_rffdec WA76
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA7a` (`addi a5,a5,376`). -/
theorem rfFDecA7a : rfF (ext_decode WA7a) := by ax_spin_ap2_rffdec WA7a
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA7e` (`bne a5,a2,-0xa`). -/
theorem rfFDecA7e : rfF (ext_decode WA7e) := by ax_spin_ap2_rffdec WA7e
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA82` (`auipc a5,0x8`). -/
theorem rfFDecA82 : rfF (ext_decode WA82) := by ax_spin_ap2_rffdec WA82
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA86` (`sw a1,1936(a5)`). -/
theorem rfFDecA86 : rfF (ext_decode WA86) := by ax_spin_ap2_rffdec WA86
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA90` (`addi a0,a0,-1790`). -/
theorem rfFDecA90 : rfF (ext_decode WA90) := by ax_spin_ap2_rffdec WA90
set_option maxRecDepth 200000 in
set_option maxHeartbeats 8000000 in
/-- `rfF` of the decode of `WA94` (`jal release`). -/
theorem rfFDecA94 : rfF (ext_decode WA94) := by ax_spin_ap2_rffdec WA94

section walks
attribute [local semireducible] LeanRV64D.Functions.hartSupports
  LeanRV64D.Functions.currentlyEnabled

/-- (Lean-only, deviation 2) decode walk of `WA68`, machine reference map. -/
theorem AxSpinAp2.walkA68M : runRead drefM (ext_decode WA68) = some (ap68, false) := by kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA68`, supervisor reference map. -/
theorem AxSpinAp2.walkA68S : runRead WkEntryNew.drefS0 (ext_decode WA68) = some (ap68, false) := by
  kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA6c`, machine reference map. -/
theorem AxSpinAp2.walkA6cM : runRead drefM (ext_decode WA6c) = some (ap6c, false) := by kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA6c`, supervisor reference map. -/
theorem AxSpinAp2.walkA6cS : runRead WkEntryNew.drefS0 (ext_decode WA6c) = some (ap6c, false) := by
  kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA70`, machine reference map. -/
theorem AxSpinAp2.walkA70M : runRead drefM (ext_decode WA70) = some (ap70, false) := by kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA70`, supervisor reference map. -/
theorem AxSpinAp2.walkA70S : runRead WkEntryNew.drefS0 (ext_decode WA70) = some (ap70, false) := by
  kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA76`, machine reference map. -/
theorem AxSpinAp2.walkA76M : runRead drefM (ext_decode WA76) = some (ap76, false) := by kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA76`, supervisor reference map. -/
theorem AxSpinAp2.walkA76S : runRead WkEntryNew.drefS0 (ext_decode WA76) = some (ap76, false) := by
  kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA7a`, machine reference map. -/
theorem AxSpinAp2.walkA7aM : runRead drefM (ext_decode WA7a) = some (ap7a, false) := by kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA7a`, supervisor reference map. -/
theorem AxSpinAp2.walkA7aS : runRead WkEntryNew.drefS0 (ext_decode WA7a) = some (ap7a, false) := by
  kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA7e`, machine reference map. -/
theorem AxSpinAp2.walkA7eM : runRead drefM (ext_decode WA7e) = some (ap7e, false) := by kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA7e`, supervisor reference map. -/
theorem AxSpinAp2.walkA7eS : runRead WkEntryNew.drefS0 (ext_decode WA7e) = some (ap7e, false) := by
  kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA82`, machine reference map. -/
theorem AxSpinAp2.walkA82M : runRead drefM (ext_decode WA82) = some (ap82, false) := by kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA82`, supervisor reference map. -/
theorem AxSpinAp2.walkA82S : runRead WkEntryNew.drefS0 (ext_decode WA82) = some (ap82, false) := by
  kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA86`, machine reference map. -/
theorem AxSpinAp2.walkA86M : runRead drefM (ext_decode WA86) = some (ap86, false) := by kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA86`, supervisor reference map. -/
theorem AxSpinAp2.walkA86S : runRead WkEntryNew.drefS0 (ext_decode WA86) = some (ap86, false) := by
  kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA90`, machine reference map. -/
theorem AxSpinAp2.walkA90M : runRead drefM (ext_decode WA90) = some (ap90, false) := by kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA90`, supervisor reference map. -/
theorem AxSpinAp2.walkA90S : runRead WkEntryNew.drefS0 (ext_decode WA90) = some (ap90, false) := by
  kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA94`, machine reference map. -/
theorem AxSpinAp2.walkA94M : runRead drefM (ext_decode WA94) = some (ap94, false) := by kernel_rfl
/-- (Lean-only, deviation 2) decode walk of `WA94`, supervisor reference map. -/
theorem AxSpinAp2.walkA94S : runRead WkEntryNew.drefS0 (ext_decode WA94) = some (ap94, false) := by
  kernel_rfl

end walks

/-- The decode of `WA68` (deviation 2). -/
theorem decA68 (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA68) s = some (ap68, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp2.walkA68M AxSpinAp2.walkA68S s
/-- The decode of `WA6c` (deviation 2). -/
theorem decA6c (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA6c) s = some (ap6c, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp2.walkA6cM AxSpinAp2.walkA6cS s
/-- The decode of `WA70` (deviation 2). -/
theorem decA70 (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA70) s = some (ap70, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp2.walkA70M AxSpinAp2.walkA70S s
/-- The decode of `WA76` (deviation 2). -/
theorem decA76 (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA76) s = some (ap76, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp2.walkA76M AxSpinAp2.walkA76S s
/-- The decode of `WA7a` (deviation 2). -/
theorem decA7a (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA7a) s = some (ap7a, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp2.walkA7aM AxSpinAp2.walkA7aS s
/-- The decode of `WA7e` (deviation 2). -/
theorem decA7e (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA7e) s = some (ap7e, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp2.walkA7eM AxSpinAp2.walkA7eS s
/-- The decode of `WA82` (deviation 2). -/
theorem decA82 (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA82) s = some (ap82, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp2.walkA82M AxSpinAp2.walkA82S s
/-- The decode of `WA86` (deviation 2). -/
theorem decA86 (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA86) s = some (ap86, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp2.walkA86M AxSpinAp2.walkA86S s
/-- The decode of `WA90` (deviation 2). -/
theorem decA90 (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA90) s = some (ap90, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp2.walkA90M AxSpinAp2.walkA90S s
/-- The decode of `WA94` (deviation 2). -/
theorem decA94 (s : ExecSt) : s.regs .misa = misaC → cfgOk s →
    exec (ext_decode WA94) s = some (ap94, s) :=
  WkEntryNew.execAnyCfg _ _ AxSpinAp2.walkA94M AxSpinAp2.walkA94S s

end Weak
