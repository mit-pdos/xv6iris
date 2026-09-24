/-
`panic` meets its specification, closed with the proved `printk`.
-/
import Xv6.ProofPanic
import Xv6.LinkPrintk

namespace Xv6

/-- The proved `panic` interface. -/
theorem Panic : PANIC := panic_proof Printk

end Xv6
