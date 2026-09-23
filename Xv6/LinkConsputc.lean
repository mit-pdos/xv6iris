/-
Link `consputc`: the sealed proof instance clients import.  `consputc`
calls `uartputc_sync`; its proof is closed with the linked interface.
-/
import Xv6.ProofConsputc
import Xv6.LinkUartputcSync

namespace Xv6

/-- The proved `consputc` interface. -/
theorem Consputc : CONSPUTC := consputc_proof UartputcSync

end Xv6
