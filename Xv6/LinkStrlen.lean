/-
Link `strlen`: the sealed proof instance clients import.
-/
import Xv6.ProofStrlen

namespace Xv6

/-- The proved `strlen` interface. -/
theorem Strlen : STRLEN := strlen_proof

end Xv6
