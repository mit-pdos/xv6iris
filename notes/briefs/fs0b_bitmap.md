# Brief: wave 0b B4b — the block bitmap invariant (main tree, no edits to existing files)

Read notes/briefs/fs0_common.md (rules) and notes/fs-lean-design.md §3 (BitmapInv/SbPark; the
"who owns bitmap_res between calls" story from Rocq's claude-notes/design/fs-bitmap.md) and §6.
Port, in order, building only your own modules (`lake build Xv6.<M>`):
1. `Xv6/FsStateBitmap.lean` from /shared/xv6rocq/iris/FsStateBitmap.v — stated over the landed
   `Xv6/FsStateDefs.lean` (`FsViewNames` with only `phi`; `phiExcl` in wand form) and the byte
   view (`Xv6/FsBytes*.lean`: `fsblock`, `byteRange`, `excOwn`, `fsBytesAt`).
2. `Xv6/BitmapInv.lean` from BitmapInv.v (678 lines): `bitmap_geom_ok` (its clause joins
   `FsGeomOk` in FsCfgDefs — if that requires editing FsCfgDefs, report the exact edit instead),
   `bitmap_inv` (persistent), `bitmap_res`, the per-bit accessors over `Xv6/BitmapEnc.lean`
   (`bmBit_*`, `bmBytes_upd`, `BitSet`), `BBLOCK`/`BPB` from `Xv6/FsGeom.lean` (never redefine),
   the free-pool predicates and every lemma balloc/bfree's specs cite (survey §3.3/§3.4).
3. Then the `one_bitmap_block` / `bitmap_geom_ok` section of WriteiBudget.v that the LogAmort
   port deferred, as `Xv6/WriteiBudgetBitmap.lean` (do not edit Xv6/WriteiBudget.lean).
Every Rocq lemma ported and proved; no `sorry`; short tactic blocks. Report files, line counts,
build last lines, deviations, reused names, and any needed edit to an existing file.
