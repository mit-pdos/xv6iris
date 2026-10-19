/-
**THE ACCESS DISCIPLINE, CLOSED** (weak-allocproc plan rev 30 §C top
[R25.2] (iii); the (r2) SIBLING root [OWN.37], on the W3 pattern
`LinkTextAdequacy.xv6TextAdequacy_closed`): `xv6DiscAdequacy_xv6GF` at
`userProof`, with `xv6FsAdequacy_closed`'s three boot hypotheses.  A `Link`
file because it consumes `ProofUser` (tools/check_layering.sh: only Link
files import Proof files).

Whenever the power is on, the machine's memory obeys W8's export
`AccessDiscipline.xv6AccessDisc` = `chainOkAt ∧ lockWordDiscAt ∧ cpuStaticAt
∧ lkCpuReadAt ∧ pteDiscAt ∧ utextDiscAt ∧ uptDiscAt ∧ kptMapsExp ∧ relProvAt ∧
dynLockWinZAt ∧ ksFrameAt` (eleven conjuncts; mcslrec (3) X1 [OWN.90] [OWN.104] (b): `ksFrameAt`;
row 5′ E4 (c) [OWN.107]: `dynLockWinZAt`; mcslrec (2) [OWN.82] (a1): `relProvAt`; mcslrec (1)
[OWN.99]; W8 (f3-utext) O1 + T4 [OWN.89]; W8 (f2-ctx): three of §C W8's six conjuncts; W8
(f3-hold) [OWN.64]; W8 (f3-racy) [OWN.63]; W8 (f3-pipelk) [OWN.65]; W8 (f3-ptek) [OWN.66]): every foreign hart entry a hart's coherence
floor names is SYNC-CHAINED to it (release → acquire hops through the
spinlocks' lock bytes -- static, or a pipe lock's live as of the acquire --, or the boot hop through `started`) unless its byte is
exempt as of the entry -- a lock-layer or publication word, or a LIVE
page-table byte of either table (no window: a freed page of a process table
stops being covered at its push, W8 (pte-ghost) [OWN.57]; the as-of-entry
residual accepted [OWN.67]) -- or, on `ip->ref`, the word as of the entry is
`≥ 1` (`racyValOk`; the virtio used ring is chained, W8 (f3-gate) [OWN.62]);
every spinlock's two word histories obey the spinlock kit's discipline --
a static lock's whole histories, a live pipe lock's over its window (W8
(f3-pipelk) [OWN.65], mechanism [OWN.71]); `cpus[h]`'s cells are written
only by hart `h` after power-on; a non-holder's read of any such lock's
`lk->cpu` never returns its own pointer; and after the kernel page table's seal every entry of it is written
only by a hart, whole, with an A/D variant of its sealed value; the release
sites' provenance is recorded per store; a live pipe lock's word is 0 at its
window's opening; and a kernel-stack byte is, from then on, in no exempt class
and written by harts only (no DMA).  The
`ip->ref` and `holding()` clauses are ONE benign-race class (unlocked reads
of lock-protected words, harmless by a value argument).  The user tables'
half of the A/D clause is `uptDiscAt` (W8 (f3-utext) T4); `cpuProcDiscAt` is
permanently out of the export ([OWN.80]); later items only strengthen the
conjunction.
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
