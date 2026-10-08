/-
Weak: **`textOkB` of instructions 1a, 1c, 1e, 0e, 12 of the 14 of xv6's real `mycpu`** (decode +
compressed expansion as read-free `EvA` facts at every regime state), from
`AxSpinE7.mycpuText`.  Split from AxSpinE7 for check time.

Rocq: `iris/AxSpinE7f.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. KERNEL WORDS: the text (0x6402, 0x0141, 0x8082 at mycpu + 0x1a/0x1c/0x1e and the words
   `W0e`, `W12` at + 0x0e/0x12) is `AxSpinE7.mycpuText`'s, checked against this tree's kernel
   text by `AxSpinSpikeRun.mycpuInstrs_text` (mycpu = 0x8000195c here); the
   halfwords match Rocq (`W12` carries the drifted immediate, `AxSpinE7` deviation 1).
2. DECODE (as `AxRelease7` deviation 2, the `AxRelease7.dcOf` recipe): Rocq's `kd_XXXX`
   (KernelDecode*, `rvc_oneshot`) are not ported; `tokR`'s decode premise is the decoder's
   read-only kernel walk at `MachCSL.drefMisa` (`ax_epi_ledger_krfl`) turned into an `exec`
   fact by `execOfRunRead` (the `misa = misaC` premise answers the walk's one register read).
   Its `rfF` is `rff_auto` after pruning the decoder's pattern tests on the literal (Rocq
   `rfF_auto`); the expansion's `rfF` is `True.intro` (a compressed `execute` is a `pure`).
3. Section variables (`σi T satp0`, `Htxt`) are explicit arguments; the Rocq `Ltac tokr` is the
   file-local macro `ax_spin_e7f_tokr` (it also takes the decoded instruction, Rocq `eapply`'s
   evar, and the literal halfword).
4. Q7 (`AxSpinE7` deviation 4): the two 4-byte `tokB` calls take `sfAnnB 32 w = false`
   (`decide` at the literal word); the decodes are `AxSpinE7.dec0e`/`dec12` (kernel walks).

**Rocq → Lean name map.**  `tok1a` `tok1a`, `tok1c` `tok1c`, `tok1e` `tok1e`, `tok0e` `tok0e`,
`tok12` `tok12` (none in the duplicated-name table).  No Lean-only declarations.

**Dropped:** nothing (Rocq 5 lemmas; Lean 5).  **Not ported:** the `Print Assumptions`
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
local macro "ax_spin_e7f_tokr" h:term:max i0:term:max hex:term:max ht:term:max : tactic =>
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
/-- Rocq `tok1a`: `c.ldsp s0, 0(sp)` (0x6402). -/
theorem tok1a (Htxt : mycpuText σi T) : textOkB σi T satp0 (pcm 0x1a) true ins1a := by
  ax_spin_e7f_tokr (0x6402#16) (.C_LDSP (0#6, .Regidx 8#5)) (execExecuteCLDSP _ _) Htxt.2.2.2.2.2.2.2.2.2.2.2.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tok1c`: `c.addi sp, 16` (0x0141). -/
theorem tok1c (Htxt : mycpuText σi T) : textOkB σi T satp0 (pcm 0x1c) true ins1c := by
  ax_spin_e7f_tokr (0x0141#16) (.C_ADDI (16#6, .Regidx 2#5)) (execExecuteCADDI _ _) Htxt.2.2.2.2.2.2.2.2.2.2.2.2.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tok1e`: `c.ret` (0x8082). -/
theorem tok1e (Htxt : mycpuText σi T) : textOkB σi T satp0 (pcm 0x1e) true ins1e := by
  ax_spin_e7f_tokr (0x8082#16) (.C_JR (.Regidx 1#5)) (execExecuteCJR _) Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Rocq `tok0e` (deviation 4: the word is not an sfence word). -/
theorem tok0e (Htxt : mycpuText σi T) : textOkB σi T satp0 (pcm 0x0e) false ins0e :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.1 (by decide) rfFDec0e dec0e

/-- Rocq `tok12` (deviation 4: the word is not an sfence word). -/
theorem tok12 (Htxt : mycpuText σi T) : textOkB σi T satp0 (pcm 0x12) false ins12 :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.1 (by decide) rfFDec12 dec12

end toks

end Weak
