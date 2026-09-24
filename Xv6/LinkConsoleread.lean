/-
Link `consoleread`: the proof instance clients import.  `consoleread`
calls `acquire`/`release`, `myproc`, `killed`, `sleep_prepare`/`sleep` and
`either_copyout`; all are closed with their linked interfaces (`copyout`
still takes the page-table walkers as parameters).
-/
import Xv6.ProofConsoleread
import Xv6.LinkAcquire
import Xv6.LinkRelease
import Xv6.LinkMyproc
import Xv6.LinkKilled
import Xv6.LinkSleepPrepare
import Xv6.LinkSleep
import Xv6.LinkSched
import Xv6.LinkEitherCopyout
import Xv6.LinkMemmove

namespace Xv6

/-- The proved `consoleread` interface, given `copyout`. -/
theorem Consoleread (CO : COPYOUT) : CONSOLEREAD :=
  consoleread_proof Acquire Release Myproc Killed (SleepPrepare Myproc Acquire Release)
    (Sleep Myproc Acquire Release Sched) (EitherCopyout Myproc CO Memmove)

end Xv6
