/-
Link `holding`: the sealed proof instance clients import.  `holding` calls
`mycpu`, so its proof is parameterised by that interface and is closed
here with the linked `Mycpu`.
-/
import Xv6.ProofHolding
import Xv6.LinkMycpu

namespace Xv6

/-- The proved `holding` interface. -/
theorem Holding : HOLDING := holding_proof Mycpu

end Xv6
