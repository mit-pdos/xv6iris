/-
`log_write` meets its specification, closed with the proved `acquire`,
`release` and `bpin`.
-/
import Xv6.ProofLogWrite
import Xv6.LinkAcquire
import Xv6.LinkRelease
import Xv6.LinkBpin

namespace Xv6

theorem LogWrite : LOG_WRITE := logWrite_proof Acquire Release Bpin

end Xv6
