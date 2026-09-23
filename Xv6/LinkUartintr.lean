/-
Link `uartintr`: the sealed proof instance clients import.  `uartintr`
calls `wakeup` and, at port 0, `consoleintr` through `uarts[0].rx`; its
proof is closed with their linked interfaces.
-/
import Xv6.ProofUartintr
import Xv6.LinkConsoleintr
import Xv6.LinkWakeup

namespace Xv6

/-- The proved `uartintr` interface. -/
theorem Uartintr : UARTINTR := uartintr_proof Consoleintr Wakeup

end Xv6
