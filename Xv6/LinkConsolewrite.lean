/-
Link `consolewrite`: the proof instance clients import.  `consolewrite`
calls `either_copyin` and `uartwrite`; both are closed with their linked
interfaces (`copyin` still takes `walkaddr`/`vmfault` as parameters).
-/
import Xv6.ProofConsolewrite
import Xv6.LinkEitherCopyin
import Xv6.LinkUartwrite
import Xv6.LinkMemmove
import Xv6.LinkSched

namespace Xv6

/-- The proved `consolewrite` interface, given `copyin`. -/
theorem Consolewrite (CI : COPYIN) : CONSOLEWRITE :=
  consolewrite_proof (EitherCopyin Myproc CI Memmove) (Uartwrite Myproc Sched)

end Xv6
