/-
`bpin` meets its specification, closed with the proved `acquire` and
`release`.
-/
import Xv6.ProofBpin
import Xv6.LinkAcquire
import Xv6.LinkRelease

namespace Xv6

theorem Bpin : BPIN := bpin_proof Acquire Release

end Xv6
