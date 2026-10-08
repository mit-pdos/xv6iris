/-
Weak: **`textOkB` of instructions 28, 2a, 16, 1a, 1e of the 21 of xv6's real `holding`** (decode +
compressed expansion as read-free `EvA` facts at every regime state), from
`AxSpinHd.holdingText`.  Split for check time (template `AxSpinE7b`).

Rocq: `iris/AxSpinHd5.v` @ xxvzwolszwmp.

## Deviations from Rocq

1. KERNEL WORDS: the text (0x6105 at holding + 0x28, 0x8082 at holding + 0x2a, `W16` at holding +
   0x16, `W1a` at holding + 0x1a, `W1e` at holding + 0x1e) is `AxSpinHd.holdingText`'s, checked
   against this tree's kernel text (`Xv6/KernelImage.lean`, holding = 0x80000bf2 here); the
   halfwords and `W1a`/`W1e` match Rocq; `W16` = 0x555000ef carries the drifted `jal` immediate
   (`AxSpinHd` deviation 1, `h16` = `.JAL (3412#21, .Regidx 1#5)`; Rocq 0x52f000ef / 3374).
2. DECODE (as `AxSpinE7b` deviation 2, the `AxRelease7.dcOf` recipe): Rocq's `kd_XXXX`
   (KernelDecode*, `rvc_oneshot`) are not ported; `tokR`'s decode premise is the decoder's
   read-only kernel walk at `MachCSL.drefMisa` (`ax_epi_ledger_krfl`) turned into an `exec`
   fact by `execOfRunRead`.  Its `rfF` is `rff_auto` after pruning the decoder's pattern tests on
   the literal (Rocq `rfF_auto`); the expansion's `rfF` is `True.intro` (a compressed `execute`
   is a `pure`).  The expansion facts are the `ExecSC` `execExecuteC*` lemmas (Rocq
   `exec_execute_C_*`).
3. Q7 (`AxSpinE7` deviation 4): the three 4-byte `tokB` calls take `sfAnnB 32 w = false`
   (`decide` at the literal word); the decodes are `AxSpinHd.dec16`/`dec1a`/`dec1e` (kernel walks).
4. Section variables (`σi T satp0`, `Htxt`) are explicit arguments; the Rocq `Ltac tokr` is the
   file-local macro `ax_spin_hd5_tokr` (it also takes the literal halfword and the decoded
   instruction, Rocq `eapply`'s evar).

**Rocq → Lean name map.**  `htok28` `htok28`, `htok2a` `htok2a`, `htok16` `htok16`, `htok1a`
`htok1a`, `htok1e` `htok1e` (none in the duplicated-name table).  No Lean-only declarations.

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
local macro "ax_spin_hd5_tokr" h:term:max i0:term:max hex:term:max ht:term:max : tactic =>
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
/-- Rocq `htok28`: `c.addi16sp sp, 32` (0x6105). -/
theorem htok28 (Htxt : holdingText σi T) : textOkB σi T satp0 (pch 0x28) true h28 := by
  ax_spin_hd5_tokr (0x6105#16) (.C_ADDI16SP (2#6)) (execExecuteCADDI16SP _)
    Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

set_option maxRecDepth 200000 in
set_option maxHeartbeats 4000000 in
/-- Rocq `htok2a`: `c.ret` (0x8082). -/
theorem htok2a (Htxt : holdingText σi T) : textOkB σi T satp0 (pch 0x2a) true h2a := by
  ax_spin_hd5_tokr (0x8082#16) (.C_JR (.Regidx 1#5)) (execExecuteCJR _)
    Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

/-- Rocq `htok16`: `jal ra, mycpu` (`W16` = 0x555000ef, drifted). -/
theorem htok16 (Htxt : holdingText σi T) : textOkB σi T satp0 (pch 0x16) false h16 :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfFDec16 dec16

/-- Rocq `htok1a`: `sub a0, s1, a0`. -/
theorem htok1a (Htxt : holdingText σi T) : textOkB σi T satp0 (pch 0x1a) false h1a :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfFDec1a dec1a

/-- Rocq `htok1e`: `seqz a0, a0`. -/
theorem htok1e (Htxt : holdingText σi T) : textOkB σi T satp0 (pch 0x1e) false h1e :=
  tokB σi T satp0 _ _ _ Htxt.2.2.2.2.2.2.2.2.2.2.2.2.2.1 (by decide) rfFDec1e dec1e

end toks

end Weak
