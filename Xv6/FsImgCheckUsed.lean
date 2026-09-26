/-
**THE BLOCK-OWNERSHIP AND LINK SWEEPS AT THE LITERAL IMAGE** (Rocq
`FsImgCheck.v`: W4+W5 and W9 of `fsimg_wf_ok`), over the computing form
(`Xv6/FsImgCheckBase.lean` says why the check is split).  Measured: W4+W5
~33 s (the used set of ~950 blocks, then the bitmap), W9 ~11 s.
-/
import Xv6.FsImgCheckBase
import Xv6.FsImgUsed
import Xv6.FsImgDir

namespace Xv6

/-- W4 + W5: no block is claimed twice, and the bitmap is the used set. -/
theorem fsimgUsedWfB :
    (match fsUsedSet fsImgBlock fsimgSb with
     | none => false
     | some u => fsBitmapWf fsImgBlock fsimgSb u) = true := by decide +kernel

/-- W9: the per-inum link counts. -/
theorem fsimgLinksWfB : fsLinksWf fsImgBlock fsimgSb = true := by decide +kernel

end Xv6
