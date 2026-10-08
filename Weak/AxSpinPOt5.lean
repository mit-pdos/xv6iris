/-
Weak: **`textOkB` of the compressed words 0x37fd, 0xe789, 0x5d7c, 0xc399 of xv6's real `push_off` /
`pop_off`, generic in the pc**: from `textAtS` at any `pc`, the decode and the compressed
expansion as read-free `EvA` facts at every regime state (`AxSpinE7.tokR`).  Split by check time.

Rocq: `iris/AxSpinPOt5.v` @ xxvzwolszwmp.

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
   file-local macro `ax_spin_pot5_tokr` (it also takes the literal halfword and the decoded
   instruction, Rocq `eapply`'s evar).
4. EXPANSIONS: Rocq's `ke_5d7c` (KernelDecode*, the expansions
   onto `AxSpinPO`'s literal instruction) are not ported; the expansion premise is
   `fun _ => rfl` (a compressed `execute` is a `pure` of the expanded instruction; Lean's ExecSC
   has no `execExecuteCSW`/`execExecuteCANDI`, and `execExecuteCLW`'s `zero_extend`/`creg2reg_idx`
   form reaches the literal instruction only by conversion, which `rfl` performs).

**Rocq → Lean name map.**  `tw_37fd` `tw37fd`, `tw_e789` `twE789`, `tw_5d7c` `tw5d7c`, `tw_c399` `twC399` (none in the
duplicated-name table).  No Lean-only declarations.

**Dropped:** nothing (Rocq 4 lemmas; Lean 4).  **Not ported:** the `Print Assumptions` line
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
local macro "ax_spin_pot5_tokr" h:term:max i0:term:max hex:term:max ht:term:max : tactic =>
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
/-- Rocq `tw_37fd`: `c.addiw a5, -1` (0x37fd). -/
theorem tw37fd (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x37fd)) :
    textOkB σi T satp0 pc true p1a := by
  ax_spin_pot5_tokr (0x37fd#16) (.C_ADDIW (63#6, .Regidx 15#5)) (execExecuteCADDIW _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_e789`: `c.bnez a5, +10` (0xe789). -/
theorem twE789 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0xe789)) :
    textOkB σi T satp0 pc true p1e := by
  ax_spin_pot5_tokr (0xe789#16) (.C_BNEZ (5#8, .Cregidx 7#3)) (execExecuteCBNEZ _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_5d7c`: `c.lw a5, 124(a0)` (0x5d7c) (deviation 4). -/
theorem tw5d7c (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x5d7c)) :
    textOkB σi T satp0 pc true p20 := by
  ax_spin_pot5_tokr (0x5d7c#16) (.C_LW (31#5, .Cregidx 2#3, .Cregidx 7#3)) (fun _ => rfl) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_c399`: `c.beqz a5, +6` (0xc399). -/
theorem twC399 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0xc399)) :
    textOkB σi T satp0 pc true p22 := by
  ax_spin_pot5_tokr (0xc399#16) (.C_BEQZ (3#8, .Cregidx 7#3)) (execExecuteCBEQZ _ _) H

end toks

end Weak
