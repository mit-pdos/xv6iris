/-
Weak: **`textOkB` of instructions 14, 22, 24, 26 of the 21 of xv6's real `holding`** (decode +
compressed expansion as read-free `EvA` facts at every regime state), from
`AxSpinHd.holdingText`.  Split for check time (template `AxSpinE7b`).

Rocq: `iris/AxSpinHd4.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. KERNEL WORDS: the text (0x84be at holding + 0x14, 0x60e2 at holding + 0x22, 0x6442 at holding +
   0x24, 0x64a2 at holding + 0x26) is
   `AxSpinHd.holdingText`'s, checked against this tree's kernel text (`Xv6/KernelImage.lean`,
   holding = 0x80000bf2 here; `AxSpinHd` deviation 1); the halfwords match Rocq.
2. DECODE (as `AxSpinE7b` deviation 2, the `AxRelease7.dcOf` recipe): Rocq's `kd_XXXX`
   (KernelDecode*, `rvc_oneshot`) are not ported; `tokR`'s decode premise is the decoder's
   read-only kernel walk at `MachCSL.drefMisa` (`ax_epi_ledger_krfl`) turned into an `exec`
   fact by `execOfRunRead`.  Its `rfF` is `rff_auto` after pruning the decoder's pattern tests on
   the literal (Rocq `rfF_auto`); the expansion's `rfF` is `True.intro` (a compressed `execute`
   is a `pure`).  The expansion facts are the `ExecSC` `execExecuteC*` lemmas (Rocq
   `exec_execute_C_*`).
3. Section variables (`σi T satp0`, `Htxt`) are explicit arguments; the Rocq `Ltac tokr` is the
   file-local macro `ax_spin_hd4_tokr` (it also takes the literal halfword and the decoded
   instruction, Rocq `eapply`'s evar).

**Rocq → Lean name map.**  `htok14` `htok14`, `htok22` `htok22`, `htok24` `htok24`, `htok26`
`htok26` (none in the duplicated-name table).  No Lean-only declarations.

**Dropped:** nothing (Rocq 4 lemmas; Lean 4).  **Not ported:** the `Print Assumptions`
line (the lint's axiom check covers it).
-/
import Weak.AxSpinHd
import Weak.AxRelease7

namespace Weak

open MachCSL
open Sail Sail.ConcurrencyInterfaceV1
open Sail.ArchSem (FreeM)
open LeanRV64D LeanRV64D.Functions

/-- Rocq `tokr`: `tokR` with the decode by the kernel walk at `drefMisa`. -/
local macro "ax_spin_hd4_tokr" h:term:max i0:term:max hex:term:max ht:term:max : tactic =>
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
/-- Rocq `htok14`: `c.mv s1, a5` (0x84be). -/
theorem htok14 (Htxt : holdingText σi T) : textOkB σi T satp0 (pch 0x14) true h14 := by
  ax_spin_hd4_tokr (0x84be#16) (.C_MV (.Regidx 9#5, .Regidx 15#5)) (execExecuteCMV _ _)
    Htxt.2.2.2.2.2.2.2.2.2.2.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `htok22`: `c.ldsp ra, 24(sp)` (0x60e2). -/
theorem htok22 (Htxt : holdingText σi T) : textOkB σi T satp0 (pch 0x22) true h22 := by
  ax_spin_hd4_tokr (0x60e2#16) (.C_LDSP (3#6, .Regidx 1#5)) (execExecuteCLDSP _ _)
    Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `htok24`: `c.ldsp s0, 16(sp)` (0x6442). -/
theorem htok24 (Htxt : holdingText σi T) : textOkB σi T satp0 (pch 0x24) true h24 := by
  ax_spin_hd4_tokr (0x6442#16) (.C_LDSP (2#6, .Regidx 8#5)) (execExecuteCLDSP _ _)
    Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `htok26`: `c.ldsp s1, 8(sp)` (0x64a2). -/
theorem htok26 (Htxt : holdingText σi T) : textOkB σi T satp0 (pch 0x26) true h26 := by
  ax_spin_hd4_tokr (0x64a2#16) (.C_LDSP (1#6, .Regidx 9#5)) (execExecuteCLDSP _ _)
    Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

end toks

end Weak
