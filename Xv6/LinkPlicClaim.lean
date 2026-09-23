/-
Link `plic_claim`: the sealed proof instance clients import.
`plic_claim` calls `cpuid`; its proof is closed with `cpuid`'s linked
interface.
-/
import Xv6.ProofPlicClaim
import Xv6.LinkCpuid

namespace Xv6

/-- The proved `plic_claim` interface. -/
theorem PlicClaim : PLIC_CLAIM := plic_claim_proof Cpuid

end Xv6
