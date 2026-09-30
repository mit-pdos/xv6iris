/-
Link `spin`: the sealed proof instance clients import (Rocq `LinkSpin.v`).
`spin` has no callees, so this only names the instance uniformly.

Nothing consumes it, here or in Rocq: `_entry`'s `jal start` never returns
(start's contract continues at `main`), so no hart reaches the park loop and
no top theorem depends on this contract.
-/
import Xv6.ProofSpin

namespace Xv6

/-- The proved `spin` interface. -/
theorem Spin : SPIN := spin_proof

end Xv6
