/-
Link the boot path: `_entry` + `start` (+ `timerinit`), sealed.
-/
import Xv6.ProofBoot
import Xv6.LinkEntry
import Xv6.LinkStart

namespace Xv6

/-- The proved boot path, from the reset address to `main` in supervisor mode. -/
theorem Boot : BOOT := BootProof Entry Start

end Xv6
