/-
`virtio_disk_intr`'s interface, instantiated from its proof.  It calls
`acquire`, `release` and `wakeup`, all three closed with their linked
interfaces, and NOTHING stays open: the disk's accessors are all proved
(`Xv6/DiskAcc.lean`), and the handler's entry credential comes out of the
lock's payload (`Xv6.diskPayWm`).
-/
import Xv6.ProofVirtioDiskIntr
import Xv6.LinkAcquire
import Xv6.LinkRelease
import Xv6.LinkWakeup

namespace Xv6

/-- The proved `virtio_disk_intr` interface. -/
theorem VirtioDiskIntr : VIRTIO_DISK_INTR :=
  virtio_disk_intr_proof Acquire Release Wakeup

end Xv6
