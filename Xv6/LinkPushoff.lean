/-
Link `push_off`: the sealed proof instance clients import.  `push_off`
calls `mycpu`, so its proof is parameterised by the `mycpu` interface and
is closed here with the linked `Mycpu`.
-/
import Xv6.ProofPushoff
import Xv6.LinkMycpu

namespace Xv6

/-- The proved `push_off` interface. -/
theorem Pushoff : PUSHOFF := push_off_proof Mycpu

end Xv6
