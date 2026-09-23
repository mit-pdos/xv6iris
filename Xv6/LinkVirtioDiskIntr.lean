/-
`virtio_disk_intr`'s interface, instantiated from its proof.  It calls
`acquire`, `release` and `wakeup`, all three closed with their linked
interfaces; what stays open is the disk's ASSUMED accessor interface
(`Xv6.DISK_ACC_ASSUMPTIONS`, now just `disk_collect`, which waits on the
in-flight read chain's block snapshot).  The handler's entry credential is
no longer an assumption: it comes out of the lock's payload
(`Xv6.diskPayWm`).
-/
import Xv6.ProofVirtioDiskIntr
import Xv6.LinkAcquire
import Xv6.LinkRelease
import Xv6.LinkWakeup

namespace Xv6

/-- The proved `virtio_disk_intr` interface, given the disk's accessor
assumption. -/
theorem VirtioDiskIntr (HA : DISK_ACC_ASSUMPTIONS) : VIRTIO_DISK_INTR :=
  virtio_disk_intr_proof HA Acquire Release Wakeup

end Xv6
