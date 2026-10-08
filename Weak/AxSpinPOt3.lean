/-
Weak: **`textOkB` of the compressed words 0x64a2, 0x6105, 0x8082, 0x8b85, 0xdd7c, 0xb7c5 of xv6's real `push_off` /
`pop_off`, generic in the pc**: from `textAtS` at any `pc`, the decode and the compressed
expansion as read-free `EvA` facts at every regime state (`AxSpinE7.tokR`).  Split by check time.

Rocq: `iris/AxSpinPOt3.v` @ xxvzwolszwmp.

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
   file-local macro `ax_spin_pot3_tokr` (it also takes the literal halfword and the decoded
   instruction, Rocq `eapply`'s evar).
4. EXPANSIONS: Rocq's `ke_8b85`, `ke_dd7c` (KernelDecode*, the expansions
   onto `AxSpinPO`'s literal instruction) are not ported; the expansion premise is
   `fun _ => rfl` (a compressed `execute` is a `pure` of the expanded instruction; Lean's ExecSC
   has no `execExecuteCSW`/`execExecuteCANDI`, and `execExecuteCLW`'s `zero_extend`/`creg2reg_idx`
   form reaches the literal instruction only by conversion, which `rfl` performs).

**Rocq → Lean name map.**  `tw_64a2` `tw64a2`, `tw_6105` `tw6105`, `tw_8082` `tw8082`, `tw_8b85` `tw8b85`, `tw_dd7c` `twDd7c`, `tw_b7c5` `twB7c5` (none in the
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
local macro "ax_spin_pot3_tokr" h:term:max i0:term:max hex:term:max ht:term:max : tactic =>
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
/-- Rocq `tw_64a2`: `c.ldsp s1, 8(sp)` (0x64a2). -/
theorem tw64a2 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x64a2)) :
    textOkB σi T satp0 pc true q26 := by
  ax_spin_pot3_tokr (0x64a2#16) (.C_LDSP (1#6, .Regidx 9#5)) (execExecuteCLDSP _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_6105`: `c.addi16sp sp, 32` (0x6105). -/
theorem tw6105 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x6105)) :
    textOkB σi T satp0 pc true q28 := by
  ax_spin_pot3_tokr (0x6105#16) (.C_ADDI16SP 2#6) (execExecuteCADDI16SP _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_8082`: `c.ret` (0x8082). -/
theorem tw8082 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x8082)) :
    textOkB σi T satp0 pc true ins1e := by
  ax_spin_pot3_tokr (0x8082#16) (.C_JR (.Regidx 1#5)) (execExecuteCJR _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_8b85`: `c.andi a5, 1` (0x8b85) (deviation 4). -/
theorem tw8b85 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x8b85)) :
    textOkB σi T satp0 pc true q34 := by
  ax_spin_pot3_tokr (0x8b85#16) (.C_ANDI (1#6, .Cregidx 7#3)) (fun _ => rfl) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_dd7c`: `c.sw a5, 124(a0)` (0xdd7c) (deviation 4). -/
theorem twDd7c (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0xdd7c)) :
    textOkB σi T satp0 pc true q36 := by
  ax_spin_pot3_tokr (0xdd7c#16) (.C_SW (31#5, .Cregidx 2#3, .Cregidx 7#3)) (fun _ => rfl) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_b7c5`: `c.j -32` (0xb7c5). -/
theorem twB7c5 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0xb7c5)) :
    textOkB σi T satp0 pc true q38 := by
  ax_spin_pot3_tokr (0xb7c5#16) (.C_J 2032#11) (execExecuteCJ _) H

end toks

end Weak
