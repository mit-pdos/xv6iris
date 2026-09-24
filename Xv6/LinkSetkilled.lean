/-
Link `setkilled`: the sealed proof instance clients import.  It takes the
proc lock, so it closes over the linked `acquire` / `release`.
-/
import Xv6.ProofSetkilled
import Xv6.LinkAcquire
import Xv6.LinkRelease

namespace Xv6

/-- The proved `setkilled` interface. -/
theorem Setkilled : SETKILLED := setkilled_proof Acquire Release

end Xv6
