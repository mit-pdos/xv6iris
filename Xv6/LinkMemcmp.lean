/-
Link `memcmp`: the sealed proof instance clients import.
-/
import Xv6.ProofMemcmp

namespace Xv6

/-- The proved `memcmp` interface. -/
theorem Memcmp : MEMCMP := memcmp_proof

end Xv6
