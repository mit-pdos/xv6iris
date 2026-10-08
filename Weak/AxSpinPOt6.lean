/-
Weak: **`textOkB` of the compressed words 0x60a2, 0x6402, 0x0141 of xv6's real `push_off` /
`pop_off`, generic in the pc**: from `textAtS` at any `pc`, the decode and the compressed
expansion as read-free `EvA` facts at every regime state (`AxSpinE7.tokR`).  Split by check time.

Rocq: `iris/AxSpinPOt6.v` @ xxvzwolszwmp.

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
   file-local macro `ax_spin_pot6_tokr` (it also takes the literal halfword and the decoded
   instruction, Rocq `eapply`'s evar).

**Rocq → Lean name map.**  `tw_60a2` `tw60a2`, `tw_6402` `tw6402`, `tw_0141` `tw0141` (none in the
duplicated-name table).  No Lean-only declarations.

**Dropped:** nothing (Rocq 3 lemmas; Lean 3).  **Not ported:** the `Print Assumptions` line
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
local macro "ax_spin_pot6_tokr" h:term:max i0:term:max hex:term:max ht:term:max : tactic =>
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
/-- Rocq `tw_60a2`: `c.ldsp ra, 8(sp)` (0x60a2). -/
theorem tw60a2 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x60a2)) :
    textOkB σi T satp0 pc true ins18 := by
  ax_spin_pot6_tokr (0x60a2#16) (.C_LDSP (1#6, .Regidx 1#5)) (execExecuteCLDSP _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_6402`: `c.ldsp s0, 0(sp)` (0x6402). -/
theorem tw6402 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x6402)) :
    textOkB σi T satp0 pc true ins1a := by
  ax_spin_pot6_tokr (0x6402#16) (.C_LDSP (0#6, .Regidx 8#5)) (execExecuteCLDSP _ _) H

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `tw_0141`: `c.addi sp, 16` (0x0141). -/
theorem tw0141 (pc : BitVec 64) (H : textAtS σi T pc (AxSpinE7.hw 0x0141)) :
    textOkB σi T satp0 pc true ins1c := by
  ax_spin_pot6_tokr (0x0141#16) (.C_ADDI (16#6, .Regidx 2#5)) (execExecuteCADDI _ _) H

end toks

end Weak
