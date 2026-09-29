/-
**sh's `cmdalloc`, linked** (lane D1-img; Rocq `UkShCmdalloc.v` at xv6
d66e41c): the walk at one engine `UL` and sh-main's `memset`
(`USH_MEMSET`); the allocator stays the contract every caller states
(`ushmMallocTyLe N 168`).  `LinkShParse` hands it to the three constructors.
-/
import Xv6.ProofShCmdalloc

namespace Xv6

/-- **sh's `cmdalloc`**, at the engine and `memset`. -/
theorem shCmdalloc_linked (UL : UK_LEAVES) (MS : USH_MEMSET) : SH_CMDALLOC :=
  shCmdalloc_holds UL MS

end Xv6
