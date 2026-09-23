/-
Link `plicinithart`: the sealed proof instance clients import.
`plicinithart` calls `cpuid`; its proof is closed with `cpuid`'s linked
interface.
-/
import Xv6.ProofPlicinithart
import Xv6.LinkCpuid

namespace Xv6

/-- The proved `plicinithart` interface. -/
theorem Plicinithart : PLICINITHART := plicinithart_proof Cpuid

end Xv6
