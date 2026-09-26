/-
**`astate`: THE γtop AUTHORITY, READ THROUGH `absOf`** (Rocq `FsAbs.v`
§3a, `/shared/xv6rocq/iris/FsAbs.v` lines 285-339 at `1900b8a43`).

Rocq's note: AT A FRACTION.  The running authority is SPLIT between the
kernel (`InodeRegion.ftop_body`, the half every AU commit shape lends) and
the application (`AppInv.app_inv`); the durable one is whole.  `astate_q`
names the fraction; `astate` -- the READING every pin and every hop is
stated over -- is at SOME fraction, so it is introduced from whichever the
reader holds and eliminated only up to that fraction.  `astate` is a
READING of the authority, so both directions are the definition.

A PARTIAL port of FsAbs.v §3 (`Xv6/FsAbsWalk.lean`'s header lists the
section as deferred with the rest of FsAbs.v's iProp half, D15): §3a's
`astate_q`/`astate` and their intro/elim only, which the union cone reads
(`PinnedObs`) and which name no `nview`.  The fragment `nview_dq`/`nview`,
`astate_q_nview_dq` and the rest of §3 stay DEFERRED with D15.

## Deviations from Rocq

1. `ghost_map_auth (γtop Γ) q I` is `Γ.top ↪●MAP{DFrac.own q} I`; the raw
   map is `RegMapF FsNode` and `abs_view` is `absView` (`FsAbsDefs`
   deviations 1-2).
2. Names: `astate_q` → `astateQ`, `astate_q_intro` → `astateQ_intro`,
   `astate_of_q` → `astate_of_q`, …; the `Timeless` instances are
   `astateQ_timeless`/`astate_timeless`.
-/
import Xv6.FsAbsDelta
import Xv6.FsStateTop

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std MachCSL

section AState
variable {GF : BundledGFunctors} [FsTopG GF]

/-- Rocq `astate_q`: the authority at fraction `q`, read. -/
def astateQ (Γ : FsViewNames GF) (q : Qp) (av : Aview) : IProp GF :=
  iprop(∃ I : RegMapF FsNode, (Γ.top ↪●MAP{DFrac.own q} I) ∗ ⌜av = absView I⌝)

/-- Rocq `astate`: at SOME fraction. -/
def astate (Γ : FsViewNames GF) (av : Aview) : IProp GF :=
  iprop(∃ q : Qp, astateQ Γ q av)

instance astateQ_timeless (Γ : FsViewNames GF) (q : Qp) (av : Aview) :
    Timeless (astateQ Γ q av) := by
  unfold astateQ; infer_instance

instance astate_timeless (Γ : FsViewNames GF) (av : Aview) : Timeless (astate Γ av) := by
  unfold astate; infer_instance

/-- Rocq `astate_q_intro`. -/
theorem astateQ_intro (Γ : FsViewNames GF) (q : Qp) (I : RegMapF FsNode) :
    (Γ.top ↪●MAP{DFrac.own q} I) ⊢ astateQ Γ q (absView I) := by
  unfold astateQ
  iintro Ha
  iexists I
  isplitl [Ha]
  · iexact Ha
  · ipureintro; rfl

/-- Rocq `astate_q_elim`. -/
theorem astateQ_elim (Γ : FsViewNames GF) (q : Qp) (av : Aview) :
    astateQ Γ q av ⊢ iprop(∃ I : RegMapF FsNode, (Γ.top ↪●MAP{DFrac.own q} I) ∗ ⌜av = absView I⌝) :=
  .rfl

/-- Rocq `astate_of_q`. -/
theorem astate_of_q (Γ : FsViewNames GF) (q : Qp) (av : Aview) : astateQ Γ q av ⊢ astate Γ av := by
  unfold astate
  iintro H
  iexists q
  iexact H

/-- Rocq `astate_intro`. -/
theorem astate_intro (Γ : FsViewNames GF) (q : Qp) (I : RegMapF FsNode) :
    (Γ.top ↪●MAP{DFrac.own q} I) ⊢ astate Γ (absView I) :=
  (astateQ_intro Γ q I).trans (astate_of_q Γ q _)

/-- Rocq `astate_elim`. -/
theorem astate_elim (Γ : FsViewNames GF) (av : Aview) :
    astate Γ av ⊢
      iprop(∃ (q : Qp) (I : RegMapF FsNode), (Γ.top ↪●MAP{DFrac.own q} I) ∗ ⌜av = absView I⌝) := by
  unfold astate astateQ
  iintro ⟨%q, H⟩
  iexists q
  iexact H

end AState

end Xv6
