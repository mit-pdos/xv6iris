/-
Link `devintr`: the proof instance clients import.  `devintr` calls
`plic_claim`, `plic_complete`, `uartintr`, `virtio_disk_intr` and
`clockintr`; all five are closed with their linked
interfaces; what stays open is the disk handler's assumed accessor
interface (`Xv6.DISK_ACC_ASSUMPTIONS`) and its extra arms
(`Xv6.DISK_INTR_EXTRA`).
-/
import Xv6.ProofDevintr
import Xv6.LinkPlicClaim
import Xv6.LinkPlicComplete
import Xv6.LinkUartintr
import Xv6.LinkVirtioDiskIntr
import Xv6.LinkClockintr

namespace Xv6

/-- The proved `devintr` interface, given the disk handler's assumed
accessor interface and its extra arms. -/
theorem Devintr (HA : DISK_ACC_ASSUMPTIONS) (HE : DISK_INTR_EXTRA) : DEVINTR :=
  devintr_proof PlicClaim PlicComplete Uartintr (VirtioDiskIntr HA HE) Clockintr

end Xv6
