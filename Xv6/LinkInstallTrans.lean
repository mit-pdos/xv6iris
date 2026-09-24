/-
`install_trans` meets its specification (the recovering arm; the commit arm
is premised away -- see `Xv6/SpecInstallTrans.lean`'s header), closed with
the proved `bread`, `bwrite`, `brelse`, `memmove` and `printk`.
-/
import Xv6.ProofInstallTrans
import Xv6.LinkBread
import Xv6.LinkBwrite
import Xv6.LinkBrelse
import Xv6.LinkMemmove
import Xv6.LinkPrintk

namespace Xv6

/-- The proved `install_trans` interface. -/
theorem InstallTrans : INSTALL_TRANS := installTrans_proof Bread Bwrite Brelse Memmove Printk

end Xv6
