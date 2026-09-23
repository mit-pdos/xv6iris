/-
Link `uartputc_sync`: the sealed proof instance clients import.
`uartputc_sync` calls `acquire` and `release`; its proof is closed with
their linked interfaces.
-/
import Xv6.ProofUartputcSync
import Xv6.LinkAcquire
import Xv6.LinkRelease

namespace Xv6

/-- The proved `uartputc_sync` interface. -/
theorem UartputcSync : UARTPUTC_SYNC := uartputc_sync_proof Acquire Release

end Xv6
