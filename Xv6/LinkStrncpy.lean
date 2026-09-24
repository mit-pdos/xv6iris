/-
Link `strncpy`: the sealed proof instance clients import.
-/
import Xv6.ProofStrncpy

namespace Xv6

/-- The proved `strncpy` interface. -/
theorem Strncpy : STRNCPY := strncpy_proof

end Xv6
