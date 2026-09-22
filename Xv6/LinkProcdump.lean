/-
Link `procdump`: the proof instance clients import.  `procdump`'s only
callee is `printk`, which is itself still parametric in the console
interfaces (`CONSPUTC`/`PRINTINT`), so `PRINTK` stays a parameter here.
-/
import Xv6.ProofProcdump

namespace Xv6

/-- The proved `procdump` interface, given `printk`. -/
theorem Procdump (PK : PRINTK) : PROCDUMP := procdump_proof PK

end Xv6
