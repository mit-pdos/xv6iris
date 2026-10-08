/-
Weak: **`textOkB` of the compressed words 0x1101, 0xec06, 0xe822, 0xe426, 0x1000, 0x84be of xv6's real `push_off` /
`pop_off`, generic in the pc**: from `textAtS` at any `pc`, the decode and the compressed
expansion as read-free `EvA` facts at every regime state (`AxSpinE7.tokR`).  Split by check time.

Rocq: `iris/AxSpinPOt1.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. KERNEL WORDS: these halfwords are `AxSpinPO.pushOffText`/`popOffText`'s and match Rocq (the
   kernel drift of `push_off`/`pop_off`/`mycpu` changes only the `jal` words, `AxSpinPO`
   deviation 1).
2. DECODE (as `AxRelease7` deviation 2, the `AxSpinE7b` recipe): Rocq's `kd_XXXX`
   (KernelDecode*, `rvc_oneshot`) are not ported; `tokR`'s decode premise is the decoder's
   read-only kernel walk at `MachCSL.drefMisa` (`ax_epi_ledger_krfl`) turned into an `exec`
   fact by `execOfRunRead` (the `misa = misaC` premise answers the walk's one register read).
   Its `rfF` is `rff_auto` after pruning the decoder's pattern tests on the literal (Rocq
   `rfF_auto`); the expansion's `rfF` is `True.intro` (a compressed `execute` is a `pure`).
3. Section variables (`σi T satp0`) are explicit arguments; the Rocq `Ltac tw` is the
   file-local macro `ax_spin_pot1_tokr` (it also takes the literal halfword and the decoded
   instruction, Rocq `eapply`'s evar).

**Rocq → Lean name map.**  `tw_1101` `tw1101`, `tw_ec06` `twEc06`, `tw_e822` `twE822`, `tw_e426` `twE426`, `tw_1000` `tw1000`, `tw_84be` `tw84be` (none in the
duplicated-name table).  No Lean-only declarations.

**Dropped:** nothing (Rocq 6 lemmas; Lean 6).  **Not ported:** the `Print Assumptions` line
(the lint's axiom check covers it).
-/
import Weak.AxSpinPO
import Weak.AxRelease7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- Rocq `tw`: `tokR` with the decode by the kernel walk at `drefMisa`. -/
local macro "ax_spin_pot1_tokr" h:term:max i0:term:max hex:term:max ht:term:max : tactic =>
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
/-- Rocq `tw_1101`: `c.addi sp, -32` (0x1101). -/
theorem tw1101 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x1101)) :
    textOkB σi T satp0 pc true q00 := by
  ax_spin_pot1_tokr (0x1101#16) (.C_ADDI (32#6, .Regidx 2#5)) (execExecuteCADDI _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_ec06`: `c.sdsp ra, 24(sp)` (0xec06). -/
theorem twEc06 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0xec06)) :
    textOkB σi T satp0 pc true q02 := by
  ax_spin_pot1_tokr (0xec06#16) (.C_SDSP (3#6, .Regidx 1#5)) (execExecuteCSDSP _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_e822`: `c.sdsp s0, 16(sp)` (0xe822). -/
theorem twE822 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0xe822)) :
    textOkB σi T satp0 pc true q04 := by
  ax_spin_pot1_tokr (0xe822#16) (.C_SDSP (2#6, .Regidx 8#5)) (execExecuteCSDSP _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_e426`: `c.sdsp s1, 8(sp)` (0xe426). -/
theorem twE426 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0xe426)) :
    textOkB σi T satp0 pc true q06 := by
  ax_spin_pot1_tokr (0xe426#16) (.C_SDSP (1#6, .Regidx 9#5)) (execExecuteCSDSP _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_1000`: `c.addi4spn s0, sp, 32` (0x1000). -/
theorem tw1000 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x1000)) :
    textOkB σi T satp0 pc true q08 := by
  ax_spin_pot1_tokr (0x1000#16) (.C_ADDI4SPN (.Cregidx 0#3, 8#8)) (execExecuteCADDI4SPN _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_84be`: `c.mv s1, a5` (0x84be). -/
theorem tw84be (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x84be)) :
    textOkB σi T satp0 pc true q0e := by
  ax_spin_pot1_tokr (0x84be#16) (.C_MV (.Regidx 9#5, .Regidx 15#5)) (execExecuteCMV _ _) H

end toks

end Weak
