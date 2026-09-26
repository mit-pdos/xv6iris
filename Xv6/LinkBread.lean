/-
`bread` meets its specification, closed with the proved `acquire`,
`release` (the hooked form), `acquiresleep` (the store-order form),
`virtio_disk_rw` and `panic` (itself closed with the proved `printk`).
-/
import Xv6.ProofBread
import Xv6.LinkAcquiresleep
import Xv6.LinkVirtioDiskRw
import Xv6.LinkPanic

namespace Xv6

/-- The proved `bread` interface. -/
theorem Bread : BREAD :=
  bread_proof Acquire ReleaseHook
    (AcquiresleepLlb AcquireLlb Release Myproc
      (SleepPrepare Myproc Acquire Release) (Sleep Myproc Acquire Release Sched))
    VirtioDiskRw Panic

end Xv6
