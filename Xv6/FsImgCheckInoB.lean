/-
**W3 AT THE LITERAL IMAGE, inums 8-12** (Rocq
`FsImgCheck.fsimg_wf_ok`'s W3 share; `Xv6/FsImgCheckBase.lean` says why it
is split).  Each live inum with an indirect block costs ~8 s of kernel
evaluation (the 256-entry indirect sweep), a direct-only one ~2 s.
-/
import Xv6.FsImgCheckBase

namespace Xv6

theorem fsimgInoOk_8 : fsimgInoOk 8 = true := by decide +kernel
theorem fsimgInoOk_9 : fsimgInoOk 9 = true := by decide +kernel
theorem fsimgInoOk_10 : fsimgInoOk 10 = true := by decide +kernel
theorem fsimgInoOk_11 : fsimgInoOk 11 = true := by decide +kernel
theorem fsimgInoOk_12 : fsimgInoOk 12 = true := by decide +kernel

end Xv6
