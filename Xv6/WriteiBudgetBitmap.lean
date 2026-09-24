/-
**ONE BITMAP BLOCK**, ported from section 2 of
`/shared/xv6rocq/iris/WriteiBudget.v` -- the one section of that file that
is stated over `BitmapInv.bitmap_geom_ok`, and which the `LogAmort` port
(`Xv6/WriteiBudget.lean`, section 6) therefore deferred.

**WHY IT MATTERS.**  Every `balloc` of a whole transaction -- the indirect
one and all four data ones -- `log_write`s `bmapstart`, because `BBLOCK`
collapses to `bmapstart` for EVERY allocatable block.  Only the first
pays; the rest ABSORB.  That is why `itrunc`'s 269 `bfree`s cost two log
units instead of 270, and why a four-block chunk of `writei` fits inside
`MAXOPBLOCKS = 10` at all (Rocq's `wi_cost_noabs_busts` is the
counterfactual).

`bitmapGeomOk` is already a premise of `balloc`, `bmap`, `writei` and
`dirlink`, so this costs no caller anything new.

**WHY A FILE OF ITS OWN.**  The port's standing rule is one Lean file per
Rocq file; this is the exception the wave-0b brief calls for, because
`Xv6/WriteiBudget.lean` landed before `Xv6/BitmapInv.lean` existed and
this wave edits no existing file.  When the two are merged, this
declaration moves into `Xv6/WriteiBudget.lean` unchanged.

**DEVIATIONS.**  Block numbers are `Nat` (the port's standing log-layer
deviation), so Rocq's `0 <= b < fssize` is `b < fssize`; `BBLOCK` and
`BBLOCK_single` are `Xv6/FsGeom.lean`'s and are NOT redefined here (that
file's own header records the split: "the raw arithmetic it rests on" is
there, the consequence under `bitmapGeomOk` is here).

**WHAT IS STILL DEFERRED from `WriteiBudget.v`.**  Sections 1, 3, 4, 5,
7, 8, 9, 10 and 11 (`FW_MAX`, `wi_cost*`, `wi_logset`, `wi_fset`,
`bm_iter_cost`, `bm_pot`, `wi_inv_*`, `wi_ad_of_alloced`) are stated over
`SpecWritei.wi_blocks`, `SpecBmap.bmap_cost` and `InodeInv.blkmap`, none
of which this port has yet; they land with `writei`.
-/
import Xv6.BitmapInv

namespace Xv6

open Std

/-- Rocq's `one_bitmap_block`: under `bitmapGeomOk`'s `size ≤ BPB`, every
in-range block lands on the SINGLE bitmap block `bmapstart`. -/
theorem oneBitmapBlock (cov : ExtTreeSet Nat compare) (logstart bmapstart fssize b : Nat)
    (hg : bitmapGeomOk cov logstart bmapstart fssize) (hb : b < fssize) :
    BBLOCK b bmapstart = bmapstart :=
  BBLOCK_single b bmapstart (by have hs := hg.2.1; omega)

end Xv6
