/-
Link `consoleintr`: the sealed proof instance clients import.  `consoleintr`
calls `acquire`, `release`, `consputc` and `wakeup`; its proof is closed
with their linked interfaces.
-/
import Xv6.ProofConsoleintr
import Xv6.LinkConsputc
import Xv6.LinkAcquire
import Xv6.LinkRelease
import Xv6.LinkWakeup

namespace Xv6

/-- The proved `consoleintr` interface. -/
theorem Consoleintr : CONSOLEINTR := consoleintr_proof Consputc Acquire Release Wakeup

end Xv6
