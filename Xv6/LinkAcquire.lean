/-
Link `acquire`: the sealed proof instance clients import.  `acquire` calls
`push_off`, `holding` and `mycpu`; its proof is closed with their linked
interfaces.
-/
import Xv6.ProofAcquire
import Xv6.LinkPushoff
import Xv6.LinkHolding
import Xv6.LinkMycpu

namespace Xv6

/-- The proved `acquire` interface. -/
theorem Acquire : ACQUIRE := acquire_proof Pushoff Holding Mycpu

end Xv6
