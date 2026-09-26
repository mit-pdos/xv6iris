/-
**THE REGION AND DURABLE-SIDE SWEEPS AT THE LITERAL IMAGE** (Rocq
`FsImgCheck.v`: `fsimg_region_free`, `fsimg_region_nlink`,
`fsimg_region_bare`, `fsimg_links_eq`, the live-set sweep, and
`fsimg_parse_sb`), over the computing form (`Xv6/FsImgCheckBase.lean` says
why the check is split).  Measured: ~17 s each for the three region sweeps
and `fsLinksEq`, under a second for the parse.
-/
import Xv6.FsImgCheckBase
import Xv6.FsImgDir

namespace Xv6

/-- Block 1's bytes ARE `fsimgSb`. -/
theorem fsimgParseSbB : fsParseSb fsImgBlock = some fsimgSb := by decide +kernel

/-- The region's tail (inums 200-207) is free. -/
theorem fsimgRegionFreeB : fsRegionFree fsImgBlock fsimgSb 13 = true := by decide +kernel

/-- L3/L4 over the whole 208-record region. -/
theorem fsimgRegionNlinkB : fsRegionNlink fsImgBlock fsimgSb 13 = true := by decide +kernel

/-- Conjunct (14): every free record of the region is bare. -/
theorem fsimgRegionBareB : fsRegionBare fsImgBlock fsimgSb 13 = true := by decide +kernel

/-- Conjunct (13): a live file's `nlink` IS its ticket count. -/
theorem fsimgLinksEqB : fsLinksEq fsImgBlock fsimgSb = true := by decide +kernel

/-- The live records are exactly `1 .. 23` (Rocq `fsimg_live_set`'s sweep). -/
theorem fsimgLiveSweepB :
    (List.range 200).all (fun z =>
      (!decide ((fsDinode fsImgBlock fsimgSb z).diType.toNat = 0)) ==
        decide (1 ≤ z ∧ z ≤ 23)) = true := by decide +kernel

end Xv6
