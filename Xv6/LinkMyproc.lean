/-
Link `myproc`: the sealed proof instance clients import.  `myproc` calls
`push_off` and `pop_off`, so its proof is parameterised by their interfaces
and is closed here with the linked `Pushoff` and `Popoff`.
-/
import Xv6.ProofMyproc
import Xv6.LinkPushoff
import Xv6.LinkPopoff

namespace Xv6

/-- The proved `myproc` interface. -/
theorem Myproc : MYPROC := myproc_proof Pushoff Popoff

end Xv6
