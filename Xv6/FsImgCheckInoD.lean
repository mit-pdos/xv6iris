/-
**W3 AT THE LITERAL IMAGE, inums 18-22** (Rocq
`FsImgCheck.fsimg_wf_ok`'s W3 share; `Xv6/FsImgCheckBase.lean` says why it
is split).  Each live inum with an indirect block costs ~8 s of kernel
evaluation (the 256-entry indirect sweep), a direct-only one ~2 s.
-/
import Xv6.FsImgCheckBase

namespace Xv6

theorem fsimgInoOk_18 : fsimgInoOk 18 = true := by decide +kernel
theorem fsimgInoOk_19 : fsimgInoOk 19 = true := by decide +kernel
theorem fsimgInoOk_20 : fsimgInoOk 20 = true := by decide +kernel
theorem fsimgInoOk_21 : fsimgInoOk 21 = true := by decide +kernel
theorem fsimgInoOk_22 : fsimgInoOk 22 = true := by decide +kernel

end Xv6
