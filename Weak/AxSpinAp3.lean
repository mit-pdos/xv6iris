/-
Weak: **`TokC` (the pc-independent decode + expansion footprints, `AxSpinAp.TokC`) of the
halfwords 4505 a021 of the inlined allocpid copy in `allocproc`** — the wrap constant `c.li
a0,1` (+ 0x50) and the jump into the loop `c.j` (+ 0x5a). Split for check time (template
AxSpinE7b).

Rocq: `iris/AxSpinAp3.v` @ xxvzwolszwmp (owner ruling Q18: RETARGETED to the inlined code).

## Deviations from Rocq

1. KERNEL INLINING (`AxSpinAp` deviation 1 and its design section, Q18): the halfwords are the
   inlined copy's (`AxSpinAp.apCodeImg` checks them against the Lean kernel image), not Rocq
   allocpid's 1101 ec06 e822 e426 1000; Rocq's `tkc_00`, `tkc_02`, `tkc_04`, `tkc_06`, `tkc_08`
   are REPLACED by `tkc50`, `tkc5a` (same role: `TokC` of each compressed instruction of the
   code).
2. DECODE (as `AxSpinE7b` deviation 2, the `AxRelease7.dcOf` recipe): Rocq's `kd_XXXX`
   (KernelDecode*) are not ported; `TokC`'s decode conjunct is the decoder's read-only kernel
   walk at `MachCSL.drefMisa` (`ax_epi_ledger_krfl`) turned into an `exec` fact by
   `execOfRunRead`; its `rfF` is `rff_auto` after pruning the decoder's pattern tests on the
   literal (Rocq `rfF_auto`); the expansion's `rfF` is `True.intro` (a compressed `execute`
   is a `pure`).
3. The Rocq `Ltac tkc kd ex` is the file-local macro `ax_spin_ap3_tkc`; it takes the
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
/-- `allocproc + 0x50`: `c.li a0,1` (0x4505). -/
theorem tkc50 : TokC (AxSpinE7.hw 0x4505) ap50 := by
  ax_spin_ap3_tkc (0x4505#16) (.C_LI (1#6, .Regidx 10#5)) (execExecuteCLI _ _)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- `allocproc + 0x5a`: `c.j +8` (0xa021). -/
theorem tkc5a : TokC (AxSpinE7.hw 0xa021) ap5a := by
  ax_spin_ap3_tkc (0xa021#16) (.C_J (4#11)) (execExecuteCJ _)

end Weak
