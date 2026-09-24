/-
Link `killed`: the sealed proof instance clients import.  It takes the
proc lock, so it closes over the linked `acquire` / `release`.
-/
import Xv6.ProofKilled
import Xv6.LinkAcquire
import Xv6.LinkRelease

namespace Xv6

/-- The proved `killed` interface. -/
theorem Killed : KILLED := killed_proof Acquire Release

end Xv6
