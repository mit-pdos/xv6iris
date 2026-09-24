/-
Link `printk`: the proof instance clients import.  `printk` calls
`acquire`, `release`, `prputc` and `printint`; all four are proved, so
`PRINTK` closes here.
-/
import Xv6.ProofPrintk
import Xv6.LinkAcquire
import Xv6.LinkRelease
import Xv6.LinkPrputc
import Xv6.LinkPrintint

namespace Xv6

/-- The proved `printk` interface. -/
theorem Printk : PRINTK := printk_proof Acquire Release Prputc Printint

end Xv6
