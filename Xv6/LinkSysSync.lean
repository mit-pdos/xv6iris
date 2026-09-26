/-
`sys_sync` meets its specification, closed with the proved
`sleep_prepare`, `acquire`, `release` and `sleep`.  Mirrors Rocq
`LinkSysSync.v`.
-/
import Xv6.ProofSysSync
import Xv6.LinkAcquire
import Xv6.LinkRelease
import Xv6.LinkSleep
import Xv6.LinkSleepPrepare
import Xv6.LinkSched

namespace Xv6

/-- The proved `sys_sync` interface. -/
theorem SysSync : SYS_SYNC :=
  sysSync_proof (SleepPrepare Myproc Acquire Release) Acquire Release
    (Sleep Myproc Acquire Release Sched)

end Xv6
