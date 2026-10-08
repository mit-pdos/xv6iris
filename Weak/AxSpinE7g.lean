/-
Weak: **`textOkB` of instructions 06, 08 of the 14 of xv6's real `mycpu`** (decode +
compressed expansion as read-free `EvA` facts at every regime state), from
`AxSpinE7.mycpuText`.  Split from AxSpinE7 for check time.

Rocq: `iris/AxSpinE7g.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. KERNEL WORDS: the text (0x0800, 0x8792 at mycpu + 0x06/0x08) is `AxSpinE7.mycpuText`'s, checked against this
   tree's kernel text by `AxSpinSpikeRun.mycpuInstrs_text` (mycpu = 0x8000195c here); the
   halfwords match Rocq.
2. DECODE (as `AxRelease7` deviation 2, the `AxRelease7.dcOf` recipe): Rocq's `kd_XXXX`
   (KernelDecode*, `rvc_oneshot`) are not ported; `tokR`'s decode premise is the decoder's
   read-only kernel walk at `MachCSL.drefMisa` (`ax_epi_ledger_krfl`) turned into an `exec`
   fact by `execOfRunRead` (the `misa = misaC` premise answers the walk's one register read).
   Its `rfF` is `rff_auto` after pruning the decoder's pattern tests on the literal (Rocq
   `rfF_auto`); the expansion's `rfF` is `True.intro` (a compressed `execute` is a `pure`).
3. Section variables (`σi T satp0`, `Htxt`) are explicit arguments; the Rocq `Ltac tokr` is the
   file-local macro `ax_spin_e7g_tokr` (it also takes the decoded instruction, Rocq `eapply`'s
   evar, and the literal halfword).

**Rocq → Lean name map.**  `tok06` `tok06`, `tok08` `tok08` (none in the duplicated-name table).  No Lean-only
declarations.

**Dropped:** nothing (Rocq 2 lemmas; Lean 2).  **Not ported:** the `Print Assumptions`
line (the lint's axiom check covers it).
-/
import Weak.AxSpinE7
import Weak.AxRelease7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- Rocq `tokr`: `tokR` with the decode by the kernel walk at `drefMisa`. -/
local macro "ax_spin_e7g_tokr" h:term:max i0:term:max hex:term:max ht:term:max : tactic =>
  `(tactic| (
    refine tokR _ _ _ _ $h $i0 _ $ht ?_ ?_ True.intro $hex
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

section toks
variable (σi : ExecSt) (T : PTree) (satp0 : BitVec 64)

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tok06`: `c.addi4spn s0, sp, 16` (0x0800). -/
theorem tok06 (Htxt : mycpuText σi T) : textOkB σi T satp0 (pcm 0x06) true ins06 := by
  ax_spin_e7g_tokr (0x0800#16) (.C_ADDI4SPN (.Cregidx 0#3, 4#8)) (execExecuteCADDI4SPN _ _) Htxt.2.2.2.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tok08`: `c.mv a5, tp` (0x8792). -/
theorem tok08 (Htxt : mycpuText σi T) : textOkB σi T satp0 (pcm 0x08) true ins08 := by
  ax_spin_e7g_tokr (0x8792#16) (.C_MV (.Regidx 15#5, .Regidx 4#5)) (execExecuteCMV _ _) Htxt.2.2.2.2.1

end toks

end Weak
