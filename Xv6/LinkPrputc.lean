/-
Link `prputc`: the sealed proof instance clients import.  `prputc` calls
`uartputc_sync` on port 1; its proof is closed with the linked interface.
-/
import Xv6.ProofPrputc
import Xv6.LinkUartputcSync

namespace Xv6

/-- The proved `prputc` interface. -/
theorem Prputc : PRPUTC := prputc_proof UartputcSync

end Xv6
