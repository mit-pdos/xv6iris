/-
`iunlock` meets its specification (Rocq `LinkIunlock.v`), closed with the
proved `holdingsleep` and the hooked `releasesleep` (and, through them,
`acquire`, `release`, `myproc`, `wakeup`).
-/
import Xv6.ProofIunlock
import Xv6.LinkHoldingsleep
import Xv6.LinkReleasesleep
import Xv6.LinkMyproc
import Xv6.LinkWakeup

namespace Xv6

theorem Iunlock : IUNLOCK :=
  iunlock_proof (Holdingsleep Acquire Release Myproc) (ReleasesleepHook Acquire ReleaseHook Wakeup)

end Xv6
