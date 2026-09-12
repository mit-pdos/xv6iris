/-
Link `printk`: the proof instance clients import.  `printk` calls
`acquire`, `release`, `consputc` and `printint`; the lock calls are closed
with their linked interfaces, the two console calls remain parameters until
the UART device model lands (`CONSPUTC`, `PRINTINT` are stated in
`SpecConsputc`/`SpecPrintint` and not yet proved).
-/
import Xv6.ProofPrintk
import Xv6.LinkAcquire
import Xv6.LinkRelease

namespace Xv6

/-- The proved `printk` interface, given the console interfaces. -/
theorem Printk (CP : CONSPUTC) (PI : PRINTINT) : PRINTK := printk_proof Acquire Release CP PI

end Xv6
