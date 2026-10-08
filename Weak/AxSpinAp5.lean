/-
Weak: **`TokC` (the pc-independent decode + expansion footprints, `AxSpinAp.TokC`) of the
halfwords 6442 64a2 6105 8082 of Rocq's `allocpid`.**  Split for check time (template AxSpinE7b).

Rocq: `iris/AxSpinAp5.v` @ xxvzwolszwmp.

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
3. The Rocq `Ltac tkc kd ex` is the file-local macro `ax_spin_ap5_tkc`; it takes the
   halfword literal, the decoded compressed instruction (Rocq's evar) and the expansion fact.

**Rocq → Lean name map.**  `tkc_36` `tkc36`, `tkc_38` `tkc38`, `tkc_3a` `tkc3a`, `tkc_3c` `tkc3c`
(none in the duplicated-name table).  No Lean-only declarations.

**Dropped:** nothing (Rocq 4 lemmas; Lean 4).  **Not ported:** the `Print Assumptions` line
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
local macro "ax_spin_ap5_tkc" h:term:max i0:term:max hex:term:max : tactic =>
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
/-- Rocq `tkc_36`: `c.ldsp s0,16(sp)` (0x6442). -/
theorem tkc36 : TokC (AxSpinE7.hw 0x6442) ap36 := by
  ax_spin_ap5_tkc (0x6442#16) (.C_LDSP (2#6, .Regidx 8#5)) (execExecuteCLDSP _ _)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tkc_38`: `c.ldsp s1,8(sp)` (0x64a2). -/
theorem tkc38 : TokC (AxSpinE7.hw 0x64a2) ap38 := by
  ax_spin_ap5_tkc (0x64a2#16) (.C_LDSP (1#6, .Regidx 9#5)) (execExecuteCLDSP _ _)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tkc_3a`: `c.addi16sp sp,32` (0x6105). -/
theorem tkc3a : TokC (AxSpinE7.hw 0x6105) ap3a := by
  ax_spin_ap5_tkc (0x6105#16) (.C_ADDI16SP 2#6) (execExecuteCADDI16SP _)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tkc_3c`: `c.ret` (0x8082). -/
theorem tkc3c : TokC (AxSpinE7.hw 0x8082) ap3c := by
  ax_spin_ap5_tkc (0x8082#16) (.C_JR (.Regidx 1#5)) (execExecuteCJR _)

end Weak
