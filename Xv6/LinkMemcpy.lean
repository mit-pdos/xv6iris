/-
Link `memcpy`: the sealed proof instance clients import.  `memcpy` calls
`memmove`, so its proof is parameterised by the `memmove` interface and is
closed here with the linked `Memmove`.
-/
import Xv6.ProofMemcpy
import Xv6.LinkMemmove

namespace Xv6

/-- The proved `memcpy` interface. -/
theorem Memcpy : MEMCPY := memcpy_proof Memmove

end Xv6
