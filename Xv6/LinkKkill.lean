/-
Link `kkill`: the sealed proof instance clients import.  It takes the proc
lock on every slot it scans, so it closes over the linked `acquire` /
`release`.
-/
import Xv6.ProofKkill
import Xv6.LinkAcquire
import Xv6.LinkRelease

namespace Xv6

/-- The proved `kkill` interface. -/
theorem Kkill : KKILL := kkill_proof Acquire Release

end Xv6
