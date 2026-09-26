/-
**W3 AT THE LITERAL IMAGE, inums 0-7 and the free tail 24-199** (Rocq
`FsImgCheck.fsimg_wf_ok`'s W3 share; `Xv6/FsImgCheckBase.lean` says why it
is split).  Each live inum with an indirect block costs ~8 s of kernel
evaluation (the 256-entry indirect sweep), a direct-only one ~2 s.
-/
import Xv6.FsImgCheckBase

namespace Xv6

theorem fsimgInoOk_0 : fsimgInoOk 0 = true := by decide +kernel
theorem fsimgInoOk_1 : fsimgInoOk 1 = true := by decide +kernel
theorem fsimgInoOk_2 : fsimgInoOk 2 = true := by decide +kernel
theorem fsimgInoOk_3 : fsimgInoOk 3 = true := by decide +kernel
theorem fsimgInoOk_4 : fsimgInoOk 4 = true := by decide +kernel
theorem fsimgInoOk_5 : fsimgInoOk 5 = true := by decide +kernel
theorem fsimgInoOk_6 : fsimgInoOk 6 = true := by decide +kernel
theorem fsimgInoOk_7 : fsimgInoOk 7 = true := by decide +kernel

/-- The free inums past the last live one: one sweep of type decodes. -/
theorem fsimgInoOk_free : (List.range' 24 176).all fsimgInoOk = true := by decide +kernel

end Xv6
