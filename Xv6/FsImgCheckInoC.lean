/-
**W3 AT THE LITERAL IMAGE, inums 13-17** (Rocq
`FsImgCheck.fsimg_wf_ok`'s W3 share; `Xv6/FsImgCheckBase.lean` says why it
is split).  Each live inum with an indirect block costs ~8 s of kernel
evaluation (the 256-entry indirect sweep), a direct-only one ~2 s.
-/
import Xv6.FsImgCheckBase

namespace Xv6

theorem fsimgInoOk_13 : fsimgInoOk 13 = true := by decide +kernel
theorem fsimgInoOk_14 : fsimgInoOk 14 = true := by decide +kernel
theorem fsimgInoOk_15 : fsimgInoOk 15 = true := by decide +kernel
theorem fsimgInoOk_16 : fsimgInoOk 16 = true := by decide +kernel
theorem fsimgInoOk_17 : fsimgInoOk 17 = true := by decide +kernel

end Xv6
