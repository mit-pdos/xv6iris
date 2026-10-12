/-
**THE ACCESS DISCIPLINE, CLOSED** (weak-allocproc plan rev 30 §C top
[R25.2] (iii); the (r2) SIBLING root [OWN.37], on the W3 pattern
`LinkTextAdequacy.xv6TextAdequacy_closed`): `xv6DiscAdequacy_xv6GF` at
`userProof`, with `xv6FsAdequacy_closed`'s three boot hypotheses.  A `Link`
file because it consumes `ProofUser` (tools/check_layering.sh: only Link
files import Proof files).

Whenever the power is on, the machine's memory obeys W8's export
`AccessDiscipline.xv6AccessDisc`, provisionally (W8-β′) `lockWordDiscAt ∧
cpuStaticAt`: every static spinlock's two word histories obey the spinlock
kit's discipline, and `cpus[h]`'s cells are written only by hart `h` after
power-on.  W8 (f2-ctx) only strengthens the conjunction.
-/
import Xv6.SystemAdequacyDisc
import Xv6.ProofUser

namespace Xv6

open Iris Iris.BI Iris.ProofMode Iris.Std Std MachCSL
open Iris.ProgramLogic Language.Notation PrimStep

/-- **THE ACCESS DISCIPLINE, `USER` discharged**: from the machine off, never
booted, with `fs.img` on its disk, every reachable thread is reducible and,
whenever the power is on, the machine's memory obeys `xv6AccessDisc`. -/
theorem xv6DiscAdequacy_closed {hlc : HasLC}
    (g : GState) (Hgen0 : g.gen = 0) (Hpow : g.pow = false) (Hdisk : diskOf g.m.devs = fsImgDisk)
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ (g2.pow = true → AccessDiscipline.xv6AccessDisc g2.m) :=
  xv6DiscAdequacy_xv6GF (hlc := hlc) userProof g Hgen0 Hpow Hdisk n κs t2 g2 hsteps

end Xv6

#print axioms Xv6.xv6DiscAdequacy_closed
