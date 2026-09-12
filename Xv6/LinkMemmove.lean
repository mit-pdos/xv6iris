/-
Link `memmove`: the sealed proof instance clients import.
-/
import Xv6.ProofMemmove

namespace Xv6

/-- The proved `memmove` interface. -/
theorem Memmove : MEMMOVE := memmove_proof

end Xv6
