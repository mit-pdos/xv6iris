/-
Link `uartwrite`: the proof instance clients import.  `uartwrite` calls
`sleep_prepare`, `acquire`, `release` and `sleep`; the spinlock interfaces
are closed with their sealed linked ones, so only `myproc` and `sched`
(which `sleep_prepare`/`sleep` need) stay parameters.
-/
import Xv6.ProofUartwrite
import Xv6.LinkAcquire
import Xv6.LinkRelease
import Xv6.LinkSleep
import Xv6.LinkSleepPrepare

namespace Xv6

/-- The proved `uartwrite` interface, given `myproc` and `sched`. -/
theorem Uartwrite (MP : MYPROC) (SC : SCHED) : UARTWRITE :=
  uartwrite_proof (SleepPrepare MP Acquire Release) Acquire Release
    (Sleep MP Acquire Release SC)

end Xv6
