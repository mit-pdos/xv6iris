/-
Weak: **`textOkB` of instructions 0a, 0c, 0e, 10, 12 of the 21 of xv6's real `holding`** (decode +
compressed expansion as read-free `EvA` facts at every regime state), from
`AxSpinHd.holdingText`.  Split for check time (template `AxSpinE7b`).

Rocq: `iris/AxSpinHd3.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. KERNEL WORDS: the text (0xec06 at holding + 0x0a, 0xe822 at holding + 0x0c, 0xe426 at holding +
   0x0e, 0x1000 at holding + 0x10, 0x691c at holding + 0x12) is
   `AxSpinHd.holdingText`'s, checked against this tree's kernel text (`Xv6/KernelImage.lean`,
   holding = 0x80000bf2 here; `AxSpinHd` deviation 1); the halfwords match Rocq.
2. DECODE (as `AxSpinE7b` deviation 2, the `AxRelease7.dcOf` recipe): Rocq's `kd_XXXX`
   (KernelDecode*, `rvc_oneshot`) are not ported; `tokR`'s decode premise is the decoder's
   read-only kernel walk at `MachCSL.drefMisa` (`ax_epi_ledger_krfl`) turned into an `exec`
   fact by `execOfRunRead`.  Its `rfF` is `rff_auto` after pruning the decoder's pattern tests on
   the literal (Rocq `rfF_auto`); the expansion's `rfF` is `True.intro` (a compressed `execute`
   is a `pure`).  The expansion facts are the `ExecSC` `execExecuteC*` lemmas (Rocq
   `exec_execute_C_*`); Rocq `ke_691c` (KernelDecode12) is `rfl` (no `ExecSC` lemma for `C_LD`).
3. Section variables (`σi T satp0`, `Htxt`) are explicit arguments; the Rocq `Ltac tokr` is the
   file-local macro `ax_spin_hd3_tokr` (it also takes the literal halfword and the decoded
   instruction, Rocq `eapply`'s evar).

**Rocq → Lean name map.**  `htok0a` `htok0a`, `htok0c` `htok0c`, `htok0e` `htok0e`, `htok10`
`htok10`, `htok12` `htok12` (none in the duplicated-name table).  No Lean-only declarations.

**Dropped:** nothing (Rocq 5 lemmas; Lean 5).  **Not ported:** the `Print Assumptions`
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
local macro "ax_spin_hd3_tokr" h:term:max i0:term:max hex:term:max ht:term:max : tactic =>
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
/-- Rocq `htok0a`: `c.sdsp ra, 24(sp)` (0xec06). -/
theorem htok0a (Htxt : holdingText σi T) : textOkB σi T satp0 (pch 0x0a) true h0a := by
  ax_spin_hd3_tokr (0xec06#16) (.C_SDSP (3#6, .Regidx 1#5)) (execExecuteCSDSP _ _) Htxt.2.2.2.2.2.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `htok0c`: `c.sdsp s0, 16(sp)` (0xe822). -/
theorem htok0c (Htxt : holdingText σi T) : textOkB σi T satp0 (pch 0x0c) true h0c := by
  ax_spin_hd3_tokr (0xe822#16) (.C_SDSP (2#6, .Regidx 8#5)) (execExecuteCSDSP _ _)
    Htxt.2.2.2.2.2.2.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `htok0e`: `c.sdsp s1, 8(sp)` (0xe426). -/
theorem htok0e (Htxt : holdingText σi T) : textOkB σi T satp0 (pch 0x0e) true h0e := by
  ax_spin_hd3_tokr (0xe426#16) (.C_SDSP (1#6, .Regidx 9#5)) (execExecuteCSDSP _ _)
    Htxt.2.2.2.2.2.2.2.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `htok10`: `c.addi4spn s0, sp, 32` (0x1000). -/
theorem htok10 (Htxt : holdingText σi T) : textOkB σi T satp0 (pch 0x10) true h10 := by
  ax_spin_hd3_tokr (0x1000#16) (.C_ADDI4SPN (.Cregidx 0#3, 8#8)) (execExecuteCADDI4SPN _ _)
    Htxt.2.2.2.2.2.2.2.2.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `htok12`: `c.ld a5, 16(a0)` (0x691c). -/
theorem htok12 (Htxt : holdingText σi T) : textOkB σi T satp0 (pch 0x12) true h12 := by
  ax_spin_hd3_tokr (0x691c#16) (.C_LD (2#5, .Cregidx 2#3, .Cregidx 7#3)) (fun _ => rfl)
    Htxt.2.2.2.2.2.2.2.2.2.1

end toks

end Weak
