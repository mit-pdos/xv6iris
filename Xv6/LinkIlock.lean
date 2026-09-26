/-
`ilock` meets its specification, closed with the proved `acquiresleep`
(the store-order form), `bread`, `memmove`, `brelse` and `panic` (Rocq
`LinkIlock.v`: all callees PROVEN).
-/
import Xv6.ProofIlock
import Xv6.LinkBread
import Xv6.LinkMemmove
import Xv6.LinkBrelse

namespace Xv6

/-- The proved `ilock` interface. -/
theorem Ilock : ILOCK :=
  ilock_proof
    (AcquiresleepLlb AcquireLlb Release Myproc
      (SleepPrepare Myproc Acquire Release) (Sleep Myproc Acquire Release Sched))
    Bread Memmove Brelse Panic

end Xv6
