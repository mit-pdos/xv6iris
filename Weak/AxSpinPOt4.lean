/-
Weak: **`textOkB` of the compressed words 0x1141, 0xe406, 0xe022, 0x0800, 0x8b89, 0xef99 of xv6's real `push_off` /
`pop_off`, generic in the pc**: from `textAtS` at any `pc`, the decode and the compressed
expansion as read-free `EvA` facts at every regime state (`AxSpinE7.tokR`).  Split by check time.

Rocq: `iris/AxSpinPOt4.v` @ xxvzwolszwmp.

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
   file-local macro `ax_spin_pot4_tokr` (it also takes the literal halfword and the decoded
   instruction, Rocq `eapply`'s evar).
4. EXPANSIONS: Rocq's `ke_8b89` (KernelDecode*, the expansions
   onto `AxSpinPO`'s literal instruction) are not ported; the expansion premise is
   `fun _ => rfl` (a compressed `execute` is a `pure` of the expanded instruction; Lean's ExecSC
   has no `execExecuteCSW`/`execExecuteCANDI`, and `execExecuteCLW`'s `zero_extend`/`creg2reg_idx`
   form reaches the literal instruction only by conversion, which `rfl` performs).

**Rocq → Lean name map.**  `tw_1141` `tw1141`, `tw_e406` `twE406`, `tw_e022` `twE022`, `tw_0800` `tw0800`, `tw_8b89` `tw8b89`, `tw_ef99` `twEf99` (none in the
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
local macro "ax_spin_pot4_tokr" h:term:max i0:term:max hex:term:max ht:term:max : tactic =>
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
/-- Rocq `tw_1141`: `c.addi sp, -16` (0x1141). -/
theorem tw1141 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x1141)) :
    textOkB σi T satp0 pc true ins00 := by
  ax_spin_pot4_tokr (0x1141#16) (.C_ADDI (48#6, .Regidx 2#5)) (execExecuteCADDI _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_e406`: `c.sdsp ra, 8(sp)` (0xe406). -/
theorem twE406 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0xe406)) :
    textOkB σi T satp0 pc true ins02 := by
  ax_spin_pot4_tokr (0xe406#16) (.C_SDSP (1#6, .Regidx 1#5)) (execExecuteCSDSP _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_e022`: `c.sdsp s0, 0(sp)` (0xe022). -/
theorem twE022 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0xe022)) :
    textOkB σi T satp0 pc true ins04 := by
  ax_spin_pot4_tokr (0xe022#16) (.C_SDSP (0#6, .Regidx 8#5)) (execExecuteCSDSP _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_0800`: `c.addi4spn s0, sp, 16` (0x0800). -/
theorem tw0800 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x0800)) :
    textOkB σi T satp0 pc true ins06 := by
  ax_spin_pot4_tokr (0x0800#16) (.C_ADDI4SPN (.Cregidx 0#3, 4#8)) (execExecuteCADDI4SPN _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_8b89`: `c.andi a5, 2` (0x8b89) (deviation 4). -/
theorem tw8b89 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x8b89)) :
    textOkB σi T satp0 pc true p10 := by
  ax_spin_pot4_tokr (0x8b89#16) (.C_ANDI (2#6, .Cregidx 7#3)) (fun _ => rfl) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_ef99`: `c.bnez a5, +30` (0xef99). -/
theorem twEf99 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0xef99)) :
    textOkB σi T satp0 pc true AxSpinPO.p12 := by
  ax_spin_pot4_tokr (0xef99#16) (.C_BNEZ (15#8, .Cregidx 7#3)) (execExecuteCBNEZ _ _) H

end toks

end Weak
