/-
Link `yield`: the sealed proof instance clients import.
-/
import Xv6.ProofYield
import Xv6.LinkAcquire
import Xv6.LinkRelease
import Xv6.LinkSched

namespace Xv6

/-- The proved `yield` interface. -/
theorem Yield : YIELD := yield_proof Myproc Acquire Release Sched

end Xv6
