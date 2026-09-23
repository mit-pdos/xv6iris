/-
Link `plicinit`: the sealed proof instance clients import.
-/
import Xv6.ProofPlicinit

namespace Xv6

/-- The proved `plicinit` interface. -/
theorem Plicinit : PLICINIT := plicinit_proof

end Xv6
