/-
`begin_op` meets its specification, closed with the proved
`sleep_prepare`, `acquire`, `release` and `sleep`.  Mirrors Rocq
`LinkBeginOp.v`.
-/
import Xv6.ProofBeginOp
import Xv6.LinkAcquire
import Xv6.LinkRelease
import Xv6.LinkSleep
import Xv6.LinkSleepPrepare
import Xv6.LinkSched

namespace Xv6

theorem BeginOp : BEGIN_OP :=
  beginOp_proof (SleepPrepare Myproc Acquire Release) Acquire Release
    (Sleep Myproc Acquire Release Sched)

end Xv6
