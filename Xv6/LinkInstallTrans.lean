/-
`install_trans` meets its specification (BOTH arms: `end_op`'s commit-time
install and `initlog`'s crash recovery), closed with the proved `bread`,
`bunpin`, `bwrite`, `brelse`, `memmove` and `printk`.
-/
import Xv6.ProofInstallTrans
import Xv6.LinkBread
import Xv6.LinkBunpin
import Xv6.LinkBwrite
import Xv6.LinkBrelse
import Xv6.LinkMemmove

namespace Xv6

/-- The proved `install_trans` interface. -/
theorem InstallTrans : INSTALL_TRANS :=
  installTrans_proof Bread Bunpin Bwrite Brelse Memmove Printk

end Xv6
