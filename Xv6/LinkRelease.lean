/-
Link `release`: the sealed proof instance clients import.  `release` calls
`holding` and `pop_off`; its proof is closed with their linked interfaces.
-/
import Xv6.ProofRelease
import Xv6.LinkHolding
import Xv6.LinkPopoff

namespace Xv6

/-- The proved `release` interface. -/
theorem Release : RELEASE := release_proof Holding Popoff

end Xv6
