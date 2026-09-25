/-
userret, linked (Rocq `LinkUserret.v`): the trampoline's userret meets its
interface.  No parameter: userret calls nothing; `SpecUser.USER` is not
needed here -- the continuation is the caller's user machine (the slot or
`USER` applies after it, in the closed loop).
-/
import Xv6.ProofUserret

namespace Xv6

/-- **The userret interface is inhabited.** -/
theorem userret_link : USERRET := userret_proof

end Xv6
