/-
Link `release`: the sealed proof instance clients import.  `release` calls
`holding` and `pop_off`; its proof is closed with their linked interfaces.
-/
import Xv6.ProofRelease
import Xv6.LinkHolding
import Xv6.LinkPopoff

namespace Xv6

/-- The proved HOOKED `release` interface (the primitive form). -/
theorem ReleaseHook : RELEASE_HOOK := release_hook_proof Holding Popoff

/-- The proved `release` interface: the identity-hook instance. -/
theorem Release : RELEASE := ReleaseHook.toRELEASE

end Xv6
