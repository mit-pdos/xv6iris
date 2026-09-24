/-
`bread` meets its specification, closed with the proved `acquire`,
`release` (the hooked form), `acquiresleep` (the store-order form),
`virtio_disk_rw` and `panic`.

`panic` is still parametric in `printk`, which is itself parametric in the
console interfaces (`PRPUTC`/`PRINTINT`), so `PRINTK` stays a parameter
here -- exactly as in `Xv6/LinkProcdump.lean` and `Xv6/LinkPanic.lean`.
-/
import Xv6.ProofBread
import Xv6.LinkAcquire
import Xv6.LinkRelease
import Xv6.LinkAcquiresleep
import Xv6.LinkVirtioDiskRw
import Xv6.LinkPanic
import Xv6.LinkMyproc
import Xv6.LinkSleep
import Xv6.LinkSleepPrepare
import Xv6.LinkSched

namespace Xv6

/-- The proved `bread` interface, given `printk`. -/
theorem Bread (PK : PRINTK) : BREAD :=
  bread_proof Acquire ReleaseHook
    (AcquiresleepLlb AcquireLlb Release Myproc
      (SleepPrepare Myproc Acquire Release) (Sleep Myproc Acquire Release Sched))
    VirtioDiskRw (Panic PK)

end Xv6
