/-
`brelse` meets its specification, closed with the proved `holdingsleep`,
`releasesleep`, `acquire` and `release`.
-/
import Xv6.ProofBrelse
import Xv6.LinkHoldingsleep
import Xv6.LinkReleasesleep
import Xv6.LinkAcquire
import Xv6.LinkRelease
import Xv6.LinkMyproc
import Xv6.LinkWakeup

namespace Xv6

theorem Brelse : BRELSE :=
  brelse_proof (Holdingsleep Acquire Release Myproc)
    (Releasesleep Acquire Release Wakeup) Acquire Release

end Xv6
