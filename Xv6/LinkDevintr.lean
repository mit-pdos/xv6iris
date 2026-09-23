/-
Link `devintr`: the proof instance clients import.  `devintr` calls
`plic_claim`, `plic_complete`, `uartintr`, `virtio_disk_intr` and
`clockintr`; the first three are closed with their linked interfaces, the
disk's and the timer's handlers remain parameters until their proofs land
(`virtio_disk_intr` is specified but not yet proved; `clockintr` needs the
S-mode `rdtime`/`csrw stimecmp` rules).
-/
import Xv6.ProofDevintr
import Xv6.LinkPlicClaim
import Xv6.LinkPlicComplete
import Xv6.LinkUartintr

namespace Xv6

/-- The proved `devintr` interface, given `virtio_disk_intr` and `clockintr`. -/
theorem Devintr (VI : VIRTIO_DISK_INTR) (CI : CLOCKINTR) : DEVINTR :=
  devintr_proof PlicClaim PlicComplete Uartintr VI CI

end Xv6
