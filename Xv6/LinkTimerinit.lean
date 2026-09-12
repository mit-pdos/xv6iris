/-
Link `timerinit`: the sealed proof instance clients import.
-/
import Xv6.ProofTimerinit

namespace Xv6

/-- The proved `timerinit` interface. -/
theorem Timerinit : TIMERINIT := TimerinitProof

end Xv6
