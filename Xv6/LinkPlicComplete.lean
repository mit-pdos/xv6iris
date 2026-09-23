/-
Link `plic_complete`: the sealed proof instance clients import.
`plic_complete` calls `cpuid`; its proof is closed with `cpuid`'s linked
interface.
-/
import Xv6.ProofPlicComplete
import Xv6.LinkCpuid

namespace Xv6

/-- The proved `plic_complete` interface. -/
theorem PlicComplete : PLIC_COMPLETE := plic_complete_proof Cpuid

end Xv6
