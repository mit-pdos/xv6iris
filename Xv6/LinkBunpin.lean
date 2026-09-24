/-
`bunpin` meets its specification, closed with the proved `acquire` and
`release`.
-/
import Xv6.ProofBunpin
import Xv6.LinkAcquire
import Xv6.LinkRelease

namespace Xv6

theorem Bunpin : BUNPIN := bunpin_proof Acquire ReleaseHook

end Xv6
