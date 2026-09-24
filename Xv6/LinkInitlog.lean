/-
`initlog` meets its specification, closed with the proved `initlock`,
`bread`, `brelse`, `install_trans` (recovering arm) and `write_head`.

**IT IS NOT CLOSED IN THE TWO NAMED HYPOTHESES**, and cannot be until the
files they belong to change; `Xv6/ProofInitlog.lean`'s header and the two
definitions in `Xv6/LogBoot.lean` say exactly why.

* `Xv6.LogHdrCleanTie` -- the bio layer's MISSING PAYLOAD HOOK (Rocq's
  `il_pay_agree`, unavailable because this port's `Xv6.bufPay` carries the
  disk-image fragment rather than `bio_view.bv_clean`; see
  `Xv6/FsBlocks.lean`) together with the clean-header premise Rocq's own
  `SpecFsinit` still carries, which `Xv6/SpecInstallTrans.lean`'s
  home-client-half deviation forces here.
* `Xv6.LogTxAuthBridge` -- a `GhostMapG` instance collision between
  `BcacheG.gmSlotG` and `LogG.gmTx`; one line in `Xv6/LogDefs.lean` and
  `Xv6/LogInv.lean` retires it.
-/
import Xv6.ProofInitlog
import Xv6.LinkInitlock
import Xv6.LinkBread
import Xv6.LinkBrelse
import Xv6.LinkInstallTrans
import Xv6.LinkWriteHead

namespace Xv6

/-- The proved `initlog` interface, modulo the two residuals. -/
theorem Initlog (hdrtie : LogHdrCleanTie) (hbridge : LogTxAuthBridge) : INITLOG :=
  initlog_proof hdrtie hbridge Initlock Bread Brelse InstallTrans WriteHead

end Xv6
