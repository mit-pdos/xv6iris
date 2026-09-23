/-
`free_desc`'s interface, instantiated from its proof.
-/
import Xv6.ProofFreeDesc
import Xv6.LinkWakeup

namespace Xv6

theorem FreeDesc : FREE_DESC := free_desc_proof Wakeup

end Xv6
