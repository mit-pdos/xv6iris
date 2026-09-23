/-
Link `kerneltrap`: the proof instance clients import.  kerneltrap calls
`devintr`, `myproc` and `yield`; devintr and myproc are closed with their
linked interfaces, so what is left open is exactly the disk handler's
assumed accessors (`Xv6.DISK_ACC_ASSUMPTIONS`, `Xv6.DISK_INTR_EXTRA`) and
`yield`.
-/
import Xv6.ProofKerneltrap
import Xv6.LinkDevintr
import Xv6.LinkMyproc

namespace Xv6

/-- The proved `kerneltrap` interface, given the disk handler's assumed
accessor interface, its extra arms, and `yield`. -/
theorem Kerneltrap (HA : DISK_ACC_ASSUMPTIONS) (HE : DISK_INTR_EXTRA) (YI : YIELD) :
    KERNELTRAP :=
  kerneltrap_proof (Devintr HA HE) Myproc YI

end Xv6
