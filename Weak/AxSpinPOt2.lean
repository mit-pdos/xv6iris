/-
Weak: **`textOkB` of the compressed words 0x5d3c, 0xcb99, 0x2785, 0xdd3c, 0x60e2, 0x6442 of xv6's real `push_off` /
`pop_off`, generic in the pc**: from `textAtS` at any `pc`, the decode and the compressed
expansion as read-free `EvA` facts at every regime state (`AxSpinE7.tokR`).  Split by check time.

Rocq: `iris/AxSpinPOt2.v` @ xxvzwolszwmp.

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
   file-local macro `ax_spin_pot2_tokr` (it also takes the literal halfword and the decoded
   instruction, Rocq `eapply`'s evar).
4. EXPANSIONS: Rocq's `ke_5d3c`, `ke_dd3c` (KernelDecode*, the expansions
   onto `AxSpinPO`'s literal instruction) are not ported; the expansion premise is
   `fun _ => rfl` (a compressed `execute` is a `pure` of the expanded instruction; Lean's ExecSC
   has no `execExecuteCSW`/`execExecuteCANDI`, and `execExecuteCLW`'s `zero_extend`/`creg2reg_idx`
   form reaches the literal instruction only by conversion, which `rfl` performs).

**Rocq → Lean name map.**  `tw_5d3c` `tw5d3c`, `tw_cb99` `twCb99`, `tw_2785` `tw2785`, `tw_dd3c` `twDd3c`, `tw_60e2` `tw60e2`, `tw_6442` `tw6442` (none in the
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
local macro "ax_spin_pot2_tokr" h:term:max i0:term:max hex:term:max ht:term:max : tactic =>
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
/-- Rocq `tw_5d3c`: `c.lw a5, 120(a0)` (0x5d3c) (deviation 4). -/
theorem tw5d3c (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x5d3c)) :
    textOkB σi T satp0 pc true qlw := by
  ax_spin_pot2_tokr (0x5d3c#16) (.C_LW (30#5, .Cregidx 2#3, .Cregidx 7#3)) (fun _ => rfl) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_cb99`: `c.beqz a5, +22` (0xcb99). -/
theorem twCb99 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0xcb99)) :
    textOkB σi T satp0 pc true q16 := by
  ax_spin_pot2_tokr (0xcb99#16) (.C_BEQZ (11#8, .Cregidx 7#3)) (execExecuteCBEQZ _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_2785`: `c.addiw a5, 1` (0x2785). -/
theorem tw2785 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x2785)) :
    textOkB σi T satp0 pc true q1e := by
  ax_spin_pot2_tokr (0x2785#16) (.C_ADDIW (1#6, .Regidx 15#5)) (execExecuteCADDIW _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_dd3c`: `c.sw a5, 120(a0)` (0xdd3c) (deviation 4). -/
theorem twDd3c (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0xdd3c)) :
    textOkB σi T satp0 pc true qsw := by
  ax_spin_pot2_tokr (0xdd3c#16) (.C_SW (30#5, .Cregidx 2#3, .Cregidx 7#3)) (fun _ => rfl) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_60e2`: `c.ldsp ra, 24(sp)` (0x60e2). -/
theorem tw60e2 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x60e2)) :
    textOkB σi T satp0 pc true q22 := by
  ax_spin_pot2_tokr (0x60e2#16) (.C_LDSP (3#6, .Regidx 1#5)) (execExecuteCLDSP _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_6442`: `c.ldsp s0, 16(sp)` (0x6442). -/
theorem tw6442 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x6442)) :
    textOkB σi T satp0 pc true q24 := by
  ax_spin_pot2_tokr (0x6442#16) (.C_LDSP (2#6, .Regidx 8#5)) (execExecuteCLDSP _ _) H

end toks

end Weak
