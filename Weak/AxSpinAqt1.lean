/-
Weak: **`textOkB` of the compressed words 0x84aa, 0x8526, 0x4705, 0xed11 of xv6's real
`acquire`, generic in the pc**: from `textAtS` at any `pc`, the decode and the compressed
expansion as read-free `EvA` facts at every regime state (`AxSpinE7.tokR`).  Split by check time.

Rocq: `iris/AxSpinAqt1.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. KERNEL WORDS: these halfwords are `AxSpinAq.acquireText`'s (acquire + 0x0a / 0x10 / 0x16 /
   0x18) and match Rocq; they are tied to `Xv6/KernelImage.lean` by `AxSpinAq.aqCodeImg` (the
   kernel drift of `acquire` changes only the `jal mycpu` word, `AxSpinAq` deviation 1).
2. DECODE (as `AxSpinPOt1` deviation 2, the `AxSpinE7b` recipe): Rocq's `kd_XXXX`
   (KernelDecode*, `rvc_oneshot`) are not ported; `tokR`'s decode premise is the decoder's
   read-only kernel walk at `MachCSL.drefMisa` (`ax_epi_ledger_krfl`) turned into an `exec`
   fact by `execOfRunRead` (the `misa = misaC` premise answers the walk's one register read).
   Its `rfF` is `rff_auto` after pruning the decoder's pattern tests on the literal (Rocq
   `rfF_auto`); the expansion's `rfF` is `True.intro` (a compressed `execute` is a `pure`).
   Rocq `exec_execute_C_*` ↦ `execExecuteC*` (ExecSC).
3. Section variables (`σi T satp0`) are explicit arguments; the Rocq `Ltac tw` is the
   file-local macro `ax_spin_aqt1_tokr` (it also takes the literal halfword and the decoded
   instruction, Rocq `eapply`'s evar).  Stage C plays no role (no row positions).

**Rocq → Lean name map.**  `twa_84aa` `twa84aa`, `twa_8526` `twa8526`, `twa_4705` `twa4705`,
`twa_ed11` `twaEd11` (none in the duplicated-name table; all grepped absent from the tip).
No Lean-only declarations.

**Dropped:** nothing (Rocq 4 lemmas; Lean 4).  **Not ported:** the `Print Assumptions` line
(the lint's axiom check covers it).
-/
import Weak.AxSpinAq
import Weak.AxRelease7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- Rocq `tw`: `tokR` with the decode by the kernel walk at `drefMisa`. -/
local macro "ax_spin_aqt1_tokr" h:term:max i0:term:max hex:term:max ht:term:max : tactic =>
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
/-- Rocq `twa_84aa`: `c.mv s1, a0` (0x84aa). -/
theorem twa84aa (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x84aa)) :
    textOkB σi T satp0 pc true a0a := by
  ax_spin_aqt1_tokr (0x84aa#16) (.C_MV (.Regidx 9#5, .Regidx 10#5)) (execExecuteCMV _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `twa_8526`: `c.mv a0, s1` (0x8526). -/
theorem twa8526 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x8526)) :
    textOkB σi T satp0 pc true a10 := by
  ax_spin_aqt1_tokr (0x8526#16) (.C_MV (.Regidx 10#5, .Regidx 9#5)) (execExecuteCMV _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `twa_4705`: `c.li a4, 1` (0x4705). -/
theorem twa4705 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x4705)) :
    textOkB σi T satp0 pc true a16 := by
  ax_spin_aqt1_tokr (0x4705#16) (.C_LI (1#6, .Regidx 14#5)) (execExecuteCLI _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `twa_ed11`: `c.bnez a0, panic` (0xed11). -/
theorem twaEd11 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0xed11)) :
    textOkB σi T satp0 pc true a18 := by
  ax_spin_aqt1_tokr (0xed11#16) (.C_BNEZ (14#8, .Cregidx 2#3)) (execExecuteCBNEZ _ _) H

end toks

end Weak
