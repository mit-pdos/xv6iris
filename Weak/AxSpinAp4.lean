/-
Weak: **`TokC` (the pc-independent decode + expansion footprints, `AxSpinAp.TokC`) of the
halfwords 4384 c398 8526 60e2 of Rocq's `allocpid`.**  Split for check time (template AxSpinE7b).

Rocq: `iris/AxSpinAp4.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. KERNEL DRIFT (`AxSpinAp` deviation 1, Q18): the halfwords are Rocq's; this tree's kernel
   inlines `allocpid`, so they are not connected to the Lean image (`TokC` is a fact about
   the halfword alone and holds regardless).
2. DECODE (as `AxSpinE7b` deviation 2, the `AxRelease7.dcOf` recipe): Rocq's `kd_XXXX`
   (KernelDecode*) are not ported; `TokC`'s decode conjunct is the decoder's read-only kernel
   walk at `MachCSL.drefMisa` (`ax_epi_ledger_krfl`) turned into an `exec` fact by
   `execOfRunRead`; its `rfF` is `rff_auto` after pruning the decoder's pattern tests on the
   literal (Rocq `rfF_auto`); the expansion's `rfF` is `True.intro` (a compressed `execute`
   is a `pure`).  Rocq's `ke_4384`/`ke_c398` (KernelDecode* expansion
   facts) are `rfl` (`execute` of a compressed load/store is a `pure`).
3. The Rocq `Ltac tkc kd ex` is the file-local macro `ax_spin_ap4_tkc`; it takes the
   halfword literal, the decoded compressed instruction (Rocq's evar) and the expansion fact.

**Rocq → Lean name map.**  `tkc_1e` `tkc1e`, `tkc_24` `tkc24`, `tkc_32` `tkc32`, `tkc_34` `tkc34`
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
/-- Rocq `tkc_1e`: `c.lw s1,0(a5)` (0x4384). -/
theorem tkc1e : TokC (AxSpinE7.hw 0x4384) ap1e := by
  ax_spin_ap4_tkc (0x4384#16) (.C_LW (0#5, .Cregidx 7#3, .Cregidx 1#3)) (fun _ => rfl)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tkc_24`: `c.sw a4,0(a5)` (0xc398). -/
theorem tkc24 : TokC (AxSpinE7.hw 0xc398) ap24 := by
  ax_spin_ap4_tkc (0xc398#16) (.C_SW (0#5, .Cregidx 7#3, .Cregidx 6#3)) (fun _ => rfl)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tkc_32`: `c.mv a0,s1` (0x8526). -/
theorem tkc32 : TokC (AxSpinE7.hw 0x8526) ap32 := by
  ax_spin_ap4_tkc (0x8526#16) (.C_MV (.Regidx 10#5, .Regidx 9#5)) (execExecuteCMV _ _)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tkc_34`: `c.ldsp ra,24(sp)` (0x60e2). -/
theorem tkc34 : TokC (AxSpinE7.hw 0x60e2) ap34 := by
  ax_spin_ap4_tkc (0x60e2#16) (.C_LDSP (3#6, .Regidx 1#5)) (execExecuteCLDSP _ _)

end Weak
