/-
`iget` meets its specification, closed with the proved `acquire`, the
hooked `release` and `panic` (itself closed with the proved `printk`) --
Rocq `LinkIget.v`: `Module Iget := IgetProof Acquire Release Panic`
(Rocq's `RELEASE` carries the hooked form; in Lean that is the separate
`RELEASE_HOOK` interface).  The "iget: no inodes" arm is LIVE and is
discharged against `Panic`.  This file imports `ProofIget` (the only Proof
file it may import).
-/
import Xv6.ProofIget
import Xv6.LinkAcquire
import Xv6.LinkRelease
import Xv6.LinkPanic

namespace Xv6

/-- The proved `iget` interface. -/
theorem Iget : IGET := iget_proof Acquire ReleaseHook Panic

end Xv6
