/-
Link `kerneltrap`: the proof instance clients import.  kerneltrap calls
`devintr`, `myproc` and `yield`; devintr and myproc are closed with their
linked interfaces, so what is left open is exactly devintr's two unproved
handlers (`virtio_disk_intr`, `clockintr`) and `yield`.
-/
import Xv6.ProofKerneltrap
import Xv6.LinkDevintr
import Xv6.LinkMyproc

namespace Xv6

/-- The proved `kerneltrap` interface, given `virtio_disk_intr`,
`clockintr` and `yield`. -/
theorem Kerneltrap (VI : VIRTIO_DISK_INTR) (CI : CLOCKINTR) (YI : YIELD) : KERNELTRAP :=
  kerneltrap_proof (Devintr VI CI) Myproc YI

end Xv6
