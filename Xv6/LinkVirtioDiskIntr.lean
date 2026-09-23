/-
`virtio_disk_intr`'s interface, instantiated from its proof.  It calls
`acquire`, `release` and `wakeup`, all three closed with their linked
interfaces; what stays open is the disk's ASSUMED accessor interface
(`Xv6.DISK_ACC_ASSUMPTIONS`, the used-element and status reads and
`disk_collect`, which wait on the completion side's per-position rows) and
the four arms `Xv6.DISK_INTR_EXTRA` collects (see its doc comments): the
used page's geometry, the used-element read at the width the code uses,
the link from a completion record to an armed slot, and `b->disk` in the
armed chain's claim.
-/
import Xv6.ProofVirtioDiskIntr
import Xv6.LinkAcquire
import Xv6.LinkRelease
import Xv6.LinkWakeup

namespace Xv6

/-- The proved `virtio_disk_intr` interface, given the disk's accessor
assumptions and the handler's four extra arms. -/
theorem VirtioDiskIntr (HA : DISK_ACC_ASSUMPTIONS) (HE : DISK_INTR_EXTRA) : VIRTIO_DISK_INTR :=
  virtio_disk_intr_proof HA HE Acquire Release Wakeup

end Xv6
