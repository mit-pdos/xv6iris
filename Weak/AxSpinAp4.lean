/-
Weak: **`TokC` (the pc-independent decode + expansion footprints, `AxSpinAp.TokC`) of the
halfwords 86ae 85aa of the inlined allocpid copy in `allocproc`** — the retry `c.mv a3,a1` (+
0x60) and the wrap `c.mv a1,a0` (+ 0x62). Split for check time (template AxSpinE7b).

Rocq: `iris/AxSpinAp4.v` @ xxvzwolszwmp (owner ruling Q18: RETARGETED to the inlined code).

## Deviations from Rocq

1. KERNEL INLINING (`AxSpinAp` deviation 1 and its design section, Q18): the halfwords are the
   inlined copy's (`AxSpinAp.apCodeImg` checks them against the Lean kernel image), not Rocq
   allocpid's 4384 c398 8526 60e2; Rocq's `tkc_1e`, `tkc_24`, `tkc_32`, `tkc_34` are REPLACED by
   `tkc60`, `tkc62` (same role: `TokC` of each compressed instruction of the code).
2. DECODE (as `AxSpinE7b` deviation 2, the `AxRelease7.dcOf` recipe): Rocq's `kd_XXXX`
   (KernelDecode*) are not ported; `TokC`'s decode conjunct is the decoder's read-only kernel
   walk at `MachCSL.drefMisa` (`ax_epi_ledger_krfl`) turned into an `exec` fact by
   `execOfRunRead`; its `rfF` is `rff_auto` after pruning the decoder's pattern tests on the
   literal (Rocq `rfF_auto`); the expansion's `rfF` is `True.intro` (a compressed `execute`
   is a `pure`).
3. The Rocq `Ltac tkc kd ex` is the file-local macro `ax_spin_ap4_tkc`; it takes the
   halfword literal, the decoded compressed instruction (Rocq's evar) and the expansion fact.

**Rocq → Lean name map.**  See deviation 1 (none in the duplicated-name table).  No Lean-only
declarations.

**Dropped:** Rocq allocpid's `tkc_XX` (deviation 1).  **Not ported:** the `Print Assumptions`
line (the lint's axiom check covers it).
-/
import Weak.AxSpinAp
import Weak.AxRelease7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- Rocq `tkc`: the four `TokC` conjuncts (decode by the kernel walk at `drefMisa`). -/
local macro "ax_spin_ap4_tkc" h:term:max i0:term:max hex:term:max : tactic =>
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
/-- `allocproc + 0x60`: `c.mv a3,a1` (0x86ae). -/
theorem tkc60 : TokC (AxSpinE7.hw 0x86ae) ap60 := by
  ax_spin_ap4_tkc (0x86ae#16) (.C_MV (.Regidx 13#5, .Regidx 11#5)) (execExecuteCMV _ _)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- `allocproc + 0x62`: `c.mv a1,a0` (0x85aa). -/
theorem tkc62 : TokC (AxSpinE7.hw 0x85aa) ap62 := by
  ax_spin_ap4_tkc (0x85aa#16) (.C_MV (.Regidx 11#5, .Regidx 10#5)) (execExecuteCMV _ _)

end Weak
