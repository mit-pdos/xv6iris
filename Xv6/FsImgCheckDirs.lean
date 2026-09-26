/-
**THE DIRECTORY SWEEPS AT THE LITERAL IMAGE** (Rocq `FsImgCheck.v`: W6-W8 of
`fsimg_wf_ok`, and `fsimg_root_no_self`), over the computing form
(`Xv6/FsImgCheckBase.lean` says why the check is split).  Measured: W6
~26 s, W7 ~1 s, W8 ~13 s, conjunct (15) ~8 s of kernel evaluation.
-/
import Xv6.FsImgCheckBase

namespace Xv6

/-- W1 and W2: the superblock arithmetic and the clean log. -/
theorem fsimgSbWf : fsSbWf fsimgSb = true := by decide +kernel

theorem fsimgLogCleanB : fsLogClean fsImgBlock fsimgSb = true := by decide +kernel

/-- W6: every directory's records. -/
theorem fsimgDirsWfB : fsDirsWf fsImgBlock fsimgSb = true := by decide +kernel

/-- W7: the root. -/
theorem fsimgRootWfB : fsRootWf fsImgBlock fsimgSb = true := by decide +kernel

/-- W8: every directory's dot records at index 0 and 1. -/
theorem fsimgDotsAllB : fsDotsAll fsImgBlock fsimgSb = true := by decide +kernel

/-- Conjunct (15): no live non-dot root record names the root. -/
theorem fsimgRootNoSelfB : fsRootNoSelf fsImgBlock fsimgSb = true := by decide +kernel

end Xv6
