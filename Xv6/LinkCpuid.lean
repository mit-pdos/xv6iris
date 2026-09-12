/-
Link `cpuid`: the sealed proof instance clients import.
-/
import Xv6.ProofCpuid

namespace Xv6

/-- The proved `cpuid` interface. -/
theorem Cpuid : CPUID := cpuid_proof

end Xv6
