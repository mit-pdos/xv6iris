/-
`panic` meets its specification, closed with `printk`.  `printk` is itself
still parametric in the console interfaces (`PRPUTC`/`PRINTINT`), so
`PRINTK` stays a parameter here, exactly as in `Xv6/LinkProcdump.lean`.
-/
import Xv6.ProofPanic

namespace Xv6

/-- The proved `panic` interface, given `printk`. -/
theorem Panic (PK : PRINTK) : PANIC := panic_proof PK

end Xv6
