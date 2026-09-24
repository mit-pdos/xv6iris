/-
Link `sys_uptime`: the sealed proof instance clients import.  `sys_uptime`
calls `acquire` and `release`; its proof is closed with their linked
interfaces.
-/
import Xv6.ProofSysUptime
import Xv6.LinkAcquire
import Xv6.LinkRelease

namespace Xv6

/-- The proved `sys_uptime` interface. -/
theorem SysUptime : SYSUPTIME := sys_uptime_proof Acquire Release

end Xv6
