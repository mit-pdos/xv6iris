/-
Weak: **`TokC` (the pc-independent decode + expansion footprints, `AxSpinAp.TokC`) of the
halfwords 5b98 d894 of the inlined allocpid copy in `allocproc`** — the scan's `c.lw a4,48(a5)`
(+ 0x74, `q->pid`) and the `p->pid` store `c.sw a3,48(s1)` (+ 0x8a). Split for check time
(template AxSpinE7b).

Rocq: `iris/AxSpinAp5.v` @ xxvzwolszwmp (owner ruling Q18: RETARGETED to the inlined code).

## Deviations from Rocq

1. KERNEL INLINING (`AxSpinAp` deviation 1 and its design section, Q18): the halfwords are the
   inlined copy's (`AxSpinAp.apCodeImg` checks them against the Lean kernel image), not Rocq
   allocpid's 6442 64a2 6105 8082; Rocq's `tkc_36`, `tkc_38`, `tkc_3a`, `tkc_3c` are REPLACED by
   `tkc74`, `tkc8a` (same role: `TokC` of each compressed instruction of the code).
2. DECODE (as `AxSpinE7b` deviation 2, the `AxRelease7.dcOf` recipe): Rocq's `kd_XXXX`
   (KernelDecode*) are not ported; `TokC`'s decode conjunct is the decoder's read-only kernel
   walk at `MachCSL.drefMisa` (`ax_epi_ledger_krfl`) turned into an `exec` fact by
   `execOfRunRead`; its `rfF` is `rff_auto` after pruning the decoder's pattern tests on the
   literal (Rocq `rfF_auto`); the expansion's `rfF` is `True.intro` (a compressed `execute`
   is a `pure`).  The expansions of the compressed load/store are `rfl` (as Rocq's
   `ke_4384`/`ke_c398`).
3. The Rocq `Ltac tkc kd ex` is the file-local macro `ax_spin_ap5_tkc`; it takes the
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
/-- `allocproc + 0x74`: `c.lw a4,48(a5)` (0x5b98). -/
theorem tkc74 : TokC (AxSpinE7.hw 0x5b98) ap74 := by
  ax_spin_ap5_tkc (0x5b98#16) (.C_LW (12#5, .Cregidx 7#3, .Cregidx 6#3)) (fun _ => rfl)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- `allocproc + 0x8a`: `c.sw a3,48(s1)` (0xd894). -/
theorem tkc8a : TokC (AxSpinE7.hw 0xd894) ap8a := by
  ax_spin_ap5_tkc (0xd894#16) (.C_SW (12#5, .Cregidx 1#3, .Cregidx 5#3)) (fun _ => rfl)

end Weak
