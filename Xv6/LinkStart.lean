/-
Link `start`: the sealed proof instance clients import.  `start` calls
`timerinit`, so its proof is parameterised by the `timerinit` interface and
is closed here with the linked `Timerinit`.
-/
import Xv6.ProofStart
import Xv6.LinkTimerinit

namespace Xv6

/-- The proved `start` interface. -/
theorem Start : START := StartProof Timerinit

end Xv6
