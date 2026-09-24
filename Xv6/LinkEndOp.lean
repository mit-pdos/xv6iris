/-
`end_op` meets its specification, closed with the proved `bread`,
`bwrite`, `brelse`, `memmove`, `write_head`, `install_trans`, `acquire`,
`release` and `wakeup`.  Mirrors Rocq `LinkEndOp.v`.
-/
import Xv6.ProofEndOp
import Xv6.LinkBread
import Xv6.LinkBwrite
import Xv6.LinkBrelse
import Xv6.LinkMemmove
import Xv6.LinkWriteHead
import Xv6.LinkInstallTrans
import Xv6.LinkAcquire
import Xv6.LinkRelease
import Xv6.LinkWakeup

namespace Xv6

/-- The proved `end_op` interface. -/
theorem EndOp : END_OP :=
  endOp_proof Bread Bwrite Brelse Memmove WriteHead InstallTrans Acquire Release Wakeup

end Xv6
