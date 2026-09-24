/-
Link `printint`: the sealed proof instance clients import.  `printint`'s
only callee is `prputc` (the SECOND 16550's `uartputc_sync`), whose
interface is already proved, so `PRINTINT` closes here.
-/
import Xv6.ProofPrintint
import Xv6.LinkPrputc

namespace Xv6

/-- The proved `printint` interface. -/
theorem Printint : PRINTINT := printint_proof Prputc

end Xv6
