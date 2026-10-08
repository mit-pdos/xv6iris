/-
Weak: **`textOkB` of instructions 02 of the 21 of xv6's real `holding`** (decode +
compressed expansion as read-free `EvA` facts at every regime state), from
`AxSpinHd.holdingText`.  Split for check time (template `AxSpinE7b`).

Rocq: `iris/AxSpinHd2c.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. KERNEL WORDS: the text (0xe399 at holding + 0x02) is
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
   file-local macro `ax_spin_hd2c_tokr` (it also takes the literal halfword and the decoded
   instruction, Rocq `eapply`'s evar).

**Rocq → Lean name map.**  `htok02` `htok02` (none in the duplicated-name table).  No Lean-only
declarations.

**Dropped:** nothing (Rocq 1 lemmas; Lean 1).  **Not ported:** the `Print Assumptions`
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
local macro "ax_spin_hd2c_tokr" h:term:max i0:term:max hex:term:max ht:term:max : tactic =>
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
/-- Rocq `htok02`: `c.bnez a5, +6` (0xe399). -/
theorem htok02 (Htxt : holdingText σi T) : textOkB σi T satp0 (pch 0x02) true h02 := by
  ax_spin_hd2c_tokr (0xe399#16) (.C_BNEZ (3#8, .Cregidx 7#3)) (execExecuteCBNEZ _ _) Htxt.2.1

end toks

end Weak
