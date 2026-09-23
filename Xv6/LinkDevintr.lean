/-
Link `devintr`: the proof instance clients import.  `devintr` calls
`plic_claim`, `plic_complete`, `uartintr`, `virtio_disk_intr` and
`clockintr`; all five are closed with their linked interfaces, and
nothing stays open.
-/
import Xv6.ProofDevintr
import Xv6.LinkPlicClaim
import Xv6.LinkPlicComplete
import Xv6.LinkUartintr
import Xv6.LinkVirtioDiskIntr
import Xv6.LinkClockintr

namespace Xv6

/-- The proved `devintr` interface. -/
theorem Devintr : DEVINTR :=
  devintr_proof PlicClaim PlicComplete Uartintr VirtioDiskIntr Clockintr

end Xv6
