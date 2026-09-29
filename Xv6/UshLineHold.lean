/-
**The seam's banner-owed reading, with a linear frame** (R-sh lane, union
wave U3; Rocq `UShLineHold.v`, pinned `1900b8a43`).

Rocq's header, in short: `ushWcInp` / `ushWbInp` are READ-BACKS -- the
credential goes in and the same credential comes back beside a persistent
fact -- so a linear conjunct that is not looked at rides through untouched.

CONE: 1/4 reached -- `ush_wb_inp_hold` (ported).  Unreached, not ported:
`ush_wc_inp_hold`, `ush_wc_inp_ex`, `ush_wb_inp_ex`.

Deviations: `UshLineDefs` deviation 1 (names).
-/
import Xv6.UshLineDefs

namespace Xv6

open Iris Iris.BI Iris.ProofMode MachCSL

/-- **Rocq `ush_wb_inp_hold`**: the banner-owed reading survives a linear
conjunct beside the credential. -/
theorem ushWbInpHold {hlc : HasLC} {GF : BundledGFunctors} [MachGS hlc GF] [Xv6G GF] [DiskG GF] [EchoOutG GF]
    (γ : EchoGn) (T : IProp GF) (Wb Hold : List (BitVec 8) → IProp GF) (hw : ushWbInp (hlc := hlc) γ T Wb) :
    ushWbInp (hlc := hlc) γ T (fun I => iprop(Wb I ∗ Hold I)) := by
  intro I
  dsimp only
  iintro ⟨Hc, Hh⟩
  ihave Hr := hw I $$ Hc
  icases Hr with ⟨Hc, Hr⟩
  iframe Hr
  iframe Hc Hh

end Xv6
