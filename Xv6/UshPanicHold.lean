/-
**The write tower's two-sided monotonicity** (Rocq `UShPanicHold.v`, 187
lines, pinned `1900b8a43`; lane INIT-FILE, round 6 item A).

Rocq's file is the prompt law with a linear frame; of it the union's cone
reaches ONE lemma, the structural move `ksh_w_mono` (weaken the input,
strengthen the output of one `write` hole).

CONE (re-walked on the pinned globs: 1/8 reached): `ksh_w_mono`.
DROPPED (unreached): `shp_write`, `alt_panic_len`, `alt_execfail_len` (this
file's local copies; `UshPanicStub` ports `UShPanic`'s reached ones),
`ksh_w_hold`, `ksh_w_ex`, `sh_prompt_law_hold`, `sh_prompt_law_ex`.

## Deviations from Rocq

1. **Name**: Rocq `UShPanicHold.ksh_w_mono` is `kshW_mono_io` --
   `UshMainDefs.kshW_mono` is Rocq `UkSh.ksh_w_mono` (the output side
   alone), a different lemma of the same Rocq name.
2. Classes: `UshMainDefs`' set, at the abstract deposit class `SG`.
-/
import Xv6.UshMainDefs

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL
open Std (ExtTreeSet)

set_option linter.unusedSectionVars false

section UshPanicHold
variable {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [CtokG GF] [SG : UexecSG GF] [PS : UprogSG GF]
  [GhostMapG GF Nat (BitVec 8) RegMapF] [GhostVarG GF Nat] [GhostMapG GF (Option Nat) UfdCell UfdMapF]
  [GhostVarG GF (ExtTreeSet GName compare)] [GhostVarG GF Int] [Xv6G GF]

/-- **Rocq `UShPanicHold.ksh_w_mono`** (deviation 1): the write hole is
contravariant in its input and covariant in its output. -/
theorem kshW_mono_io (N : UkNames GF) (fdw ua : BitVec 64) (nb : Nat) (Ci Ci' Co Co' : IProp GF) :
    ⊢ (Ci' -∗ Ci) -∗ (Co -∗ Co') -∗
      kshW (hlc := hlc) N fdw ua nb Ci Co -∗ kshW (hlc := hlc) N fdw ua nb Ci' Co' := by
  iintro Hin Hout Hw
  unfold kshW
  iintro %h %m %avail %h0 %h1 %h2 #Hc HCi Hrun Hcont
  ihave HCi := Hin $$ HCi
  iapply Hw $$ %h %m %avail %h0 %h1 %h2 Hc HCi Hrun
  iintro %h' %ret HCo Hrun
  iapply Hcont $$ %h' %ret [Hout HCo] Hrun
  iapply Hout $$ HCo

end UshPanicHold

end Xv6
