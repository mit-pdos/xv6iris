/-
Link `mycpu`: the sealed proof instance clients import.
-/
import Xv6.ProofMycpu

namespace Xv6

/-- The proved `mycpu` interface. -/
theorem Mycpu : MYCPU := mycpu_proof

end Xv6
