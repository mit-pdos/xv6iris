/-
`releasesleep` meets its interface, given the interfaces of `acquire`,
`release` and `wakeup`.
-/
import Xv6.ProofReleasesleep

namespace Xv6

theorem Releasesleep (AC : ACQUIRE) (RE : RELEASE) (WK : WAKEUP) : RELEASESLEEP :=
  releasesleep_proof AC RE WK

end Xv6
