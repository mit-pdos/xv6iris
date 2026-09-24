/-
Link `procdump`: the proof instance clients import.  `procdump`'s only
callee is `printk`, which is now proved, so `PROCDUMP` closes here.
-/
import Xv6.ProofProcdump
import Xv6.LinkPrintk

namespace Xv6

/-- The proved `procdump` interface. -/
theorem Procdump : PROCDUMP := procdump_proof Printk

end Xv6
