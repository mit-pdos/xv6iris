/-
Link `memset`: the sealed proof instance clients import.
-/
import Xv6.ProofMemset

namespace Xv6

/-- The proved `memset` interface. -/
theorem Memset : MEMSET := memset_proof

/-- The proved raw (visibility-free) `memset` interface. -/
theorem MemsetFree : MEMSET_FREE := memset_free_proof

end Xv6
