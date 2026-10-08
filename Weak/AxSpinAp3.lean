/-
Weak: **`TokC` (the pc-independent decode + expansion footprints, `AxSpinAp.TokC`) of the
halfwords 1101 ec06 e822 e426 1000 of Rocq's `allocpid`.**  Split for check time (template
AxSpinE7b).

Rocq: `iris/AxSpinAp3.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. KERNEL DRIFT (`AxSpinAp` deviation 1, Q18): the halfwords are Rocq's; this tree's kernel
   inlines `allocpid`, so they are not connected to the Lean image (`TokC` is a fact about
   the halfword alone and holds regardless).
2. DECODE (as `AxSpinE7b` deviation 2, the `AxRelease7.dcOf` recipe): Rocq's `kd_XXXX`
   (KernelDecode*) are not ported; `TokC`'s decode conjunct is the decoder's read-only kernel
   walk at `MachCSL.drefMisa` (`ax_epi_ledger_krfl`) turned into an `exec` fact by
   `execOfRunRead`; its `rfF` is `rff_auto` after pruning the decoder's pattern tests on the
   literal (Rocq `rfF_auto`); the expansion's `rfF` is `True.intro` (a compressed `execute`
   is a `pure`).
3. The Rocq `Ltac tkc kd ex` is the file-local macro `ax_spin_ap3_tkc`; it takes the
   halfword literal, the decoded compressed instruction (Rocq's evar) and the expansion fact.

**Rocq → Lean name map.**  `tkc_00` `tkc00`, `tkc_02` `tkc02`, `tkc_04` `tkc04`, `tkc_06` `tkc06`,
`tkc_08` `tkc08`
(none in the duplicated-name table).  No Lean-only declarations.

**Dropped:** nothing (Rocq 5 lemmas; Lean 5).  **Not ported:** the `Print Assumptions` line
(the lint's axiom check covers it).
-/
import Weak.AxSpinAp
import Weak.AxRelease7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- Rocq `tkc`: the four `TokC` conjuncts (decode by the kernel walk at `drefMisa`). -/
local macro "ax_spin_ap3_tkc" h:term:max i0:term:max hex:term:max : tactic =>
  `(tactic| (
    show TokC $h _
    unfold TokC
    refine ⟨$i0, ?_, ?_, True.intro, $hex⟩
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

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tkc_00`: `c.addi sp,-32` (0x1101). -/
theorem tkc00 : TokC (AxSpinE7.hw 0x1101) ap00 := by
  ax_spin_ap3_tkc (0x1101#16) (.C_ADDI (32#6, .Regidx 2#5)) (execExecuteCADDI _ _)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tkc_02`: `c.sdsp ra,24(sp)` (0xec06). -/
theorem tkc02 : TokC (AxSpinE7.hw 0xec06) ap02 := by
  ax_spin_ap3_tkc (0xec06#16) (.C_SDSP (3#6, .Regidx 1#5)) (execExecuteCSDSP _ _)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tkc_04`: `c.sdsp s0,16(sp)` (0xe822). -/
theorem tkc04 : TokC (AxSpinE7.hw 0xe822) ap04 := by
  ax_spin_ap3_tkc (0xe822#16) (.C_SDSP (2#6, .Regidx 8#5)) (execExecuteCSDSP _ _)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tkc_06`: `c.sdsp s1,8(sp)` (0xe426). -/
theorem tkc06 : TokC (AxSpinE7.hw 0xe426) ap06 := by
  ax_spin_ap3_tkc (0xe426#16) (.C_SDSP (1#6, .Regidx 9#5)) (execExecuteCSDSP _ _)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tkc_08`: `c.addi4spn s0,sp,32` (0x1000). -/
theorem tkc08 : TokC (AxSpinE7.hw 0x1000) ap08 := by
  ax_spin_ap3_tkc (0x1000#16) (.C_ADDI4SPN (.Cregidx 0#3, 8#8)) (execExecuteCADDI4SPN _ _)

end Weak
