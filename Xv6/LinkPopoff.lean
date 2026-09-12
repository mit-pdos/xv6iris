/-
Link `pop_off`: the sealed proof instance clients import.  `pop_off` calls
`mycpu`, so its proof is parameterised by the `mycpu` interface and is
closed here with the linked `Mycpu`.
-/
import Xv6.ProofPopoff
import Xv6.LinkMycpu

namespace Xv6

/-- The proved `pop_off` interface. -/
theorem Popoff : POPOFF := pop_off_proof Mycpu

end Xv6
