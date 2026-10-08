/-
Weak: **`textOkB` of instructions 0a, 0c, 16, 18 of the 14 of xv6's real `mycpu`** (decode +
compressed expansion as read-free `EvA` facts at every regime state), from
`AxSpinE7.mycpuText`.  Split from AxSpinE7 for check time.

Rocq: `iris/AxSpinE7e.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. KERNEL WORDS: the text (0x2781, 0x079e, 0x953e, 0x60a2 at mycpu + 0x0a/0x0c/0x16/0x18) is `AxSpinE7.mycpuText`'s, checked against this
   tree's kernel text by `AxSpinSpikeRun.mycpuInstrs_text` (mycpu = 0x8000195c here); the
   halfwords match Rocq.
2. DECODE (as `AxRelease7` deviation 2, the `AxRelease7.dcOf` recipe): Rocq's `kd_XXXX`
   (KernelDecode*, `rvc_oneshot`) are not ported; `tokR`'s decode premise is the decoder's
   read-only kernel walk at `MachCSL.drefMisa` (`ax_epi_ledger_krfl`) turned into an `exec`
   fact by `execOfRunRead` (the `misa = misaC` premise answers the walk's one register read).
   Its `rfF` is `rff_auto` after pruning the decoder's pattern tests on the literal (Rocq
   `rfF_auto`); the expansion's `rfF` is `True.intro` (a compressed `execute` is a `pure`).
3. Section variables (`σi T satp0`, `Htxt`) are explicit arguments; the Rocq `Ltac tokr` is the
   file-local macro `ax_spin_e7e_tokr` (it also takes the decoded instruction, Rocq `eapply`'s
   evar, and the literal halfword).

**Rocq → Lean name map.**  `tok0a` `tok0a`, `tok0c` `tok0c`, `tok16` `tok16`, `tok18` `tok18` (none in the duplicated-name table).  No Lean-only
declarations.

**Dropped:** nothing (Rocq 4 lemmas; Lean 4).  **Not ported:** the `Print Assumptions`
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
local macro "ax_spin_e7e_tokr" h:term:max i0:term:max hex:term:max ht:term:max : tactic =>
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
/-- Rocq `tok0a`: `c.addiw a5, 0` (0x2781). -/
theorem tok0a (Htxt : mycpuText σi T) : textOkB σi T satp0 (pcm 0x0a) true ins0a := by
  ax_spin_e7e_tokr (0x2781#16) (.C_ADDIW (0#6, .Regidx 15#5)) (execExecuteCADDIW _ _) Htxt.2.2.2.2.2.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tok0c`: `c.slli a5, 7` (0x079e). -/
theorem tok0c (Htxt : mycpuText σi T) : textOkB σi T satp0 (pcm 0x0c) true ins0c := by
  ax_spin_e7e_tokr (0x079e#16) (.C_SLLI (7#6, .Regidx 15#5)) (execExecuteCSLLI _ _) Htxt.2.2.2.2.2.2.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tok16`: `c.add a0, a5` (0x953e). -/
theorem tok16 (Htxt : mycpuText σi T) : textOkB σi T satp0 (pcm 0x16) true ins16 := by
  ax_spin_e7e_tokr (0x953e#16) (.C_ADD (.Regidx 10#5, .Regidx 15#5)) (execExecuteCADD _ _) Htxt.2.2.2.2.2.2.2.2.2.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tok18`: `c.ldsp ra, 8(sp)` (0x60a2). -/
theorem tok18 (Htxt : mycpuText σi T) : textOkB σi T satp0 (pcm 0x18) true ins18 := by
  ax_spin_e7e_tokr (0x60a2#16) (.C_LDSP (1#6, .Regidx 1#5)) (execExecuteCLDSP _ _) Htxt.2.2.2.2.2.2.2.2.2.2.1

end toks

end Weak
