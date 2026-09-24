/-
Link `strncmp`: the sealed proof instance clients import.
-/
import Xv6.ProofStrncmp

namespace Xv6

/-- The proved `strncmp` interface. -/
theorem Strncmp : STRNCMP := strncmp_proof

end Xv6
