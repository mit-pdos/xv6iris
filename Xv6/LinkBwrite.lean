/-
`bwrite` meets its specification, closed with the proved `holdingsleep`
(over `acquire`, `release` and `myproc`) and `virtio_disk_rw`.
-/
import Xv6.ProofBwrite
import Xv6.LinkHoldingsleep
import Xv6.LinkVirtioDiskRw

namespace Xv6

theorem Bwrite : BWRITE := bwrite_proof (Holdingsleep Acquire Release Myproc) VirtioDiskRw

end Xv6
