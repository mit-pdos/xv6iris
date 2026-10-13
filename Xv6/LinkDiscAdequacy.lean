/-
**THE ACCESS DISCIPLINE, CLOSED** (weak-allocproc plan rev 30 §C top
[R25.2] (iii); the (r2) SIBLING root [OWN.37], on the W3 pattern
`LinkTextAdequacy.xv6TextAdequacy_closed`): `xv6DiscAdequacy_xv6GF` at
`userProof`, with `xv6FsAdequacy_closed`'s three boot hypotheses.  A `Link`
file because it consumes `ProofUser` (tools/check_layering.sh: only Link
files import Proof files).

Whenever the power is on, the machine's memory obeys W8's export
`AccessDiscipline.xv6AccessDisc` = `chainOkAt ∧ lockWordDiscAt ∧ cpuStaticAt`
(W8 (f2-ctx); three of §C W8's six conjuncts): every foreign hart entry a
hart's coherence floor names is SYNC-CHAINED to it (release → acquire hops
through the spinlocks' lock bytes, or the boot hop through `started`) unless
its byte is exempt as of the entry -- a lock-layer or publication word, a
page-table byte of either table (WITH the freed-page window: a page freed by
`freewalk`/`proc_freepagetable` until the pointer naming it is cleared, which
the follow-up item W8 (pte-ghost) CLOSES [OWN.57]), an audited racy word
(`ip->ref`, finding F-RACY) or a device-ring page (the virtio used ring,
finding F-DISKTAIL) -- the last two NAMED WEAKENINGS pending the owner's
ruling; every static spinlock's two word histories obey the spinlock kit's
discipline; and `cpus[h]`'s cells are written only by hart `h` after
power-on.  Not yet exported: `pteDiscAt`, and W8 (f3-rest)'s
`cpuProcDiscAt`/`utextDiscAt`; later items only strengthen the conjunction.
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
