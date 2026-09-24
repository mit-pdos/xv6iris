# Brief: wave 0b small batch (main tree, no edits to existing files)

Read notes/briefs/fs0_common.md (rules) and notes/fs-lean-design.md §1, §3, §4, §5, §6.
Port, in order, building only your own modules (`lake build Xv6.<M>`):
1. `Xv6/FsImg.lean` from /shared/xv6rocq/iris/FsImg.v (superblock `fs_sb`/`fsimg_wf`; survey §2.14).
   Needs 0a's `Xv6/FsGeom.lean` (constants) — reuse, never redefine.
2. `Xv6/FsCfgDefs.lean` — design §1: the ambient `fscfg`/`icfg` records as typeclasses.
3. `Xv6/FsStateDefs.lean` (only the `phi` field of `fs_view_names`, design §3.4 option (ii)) and
   `Xv6/FsBytesGamma.lean`.
4. `Xv6/SbPark.lean` from SbPark.v (standalone; NOT imported by LogInv).
5. `Xv6/WriteiBudget.lean` — ONLY the `logAmort` section (design §4): `unpaid F Sb :=
   (F.filter (· ∉ Sb)).length`, `logAmort` + its family with `logAmort_shrink` over
   `F'.Sublist F`; stated over the existing `logOpS`/`logOpb`/`logOpS_opb`. The rest of
   WriteiBudget.v waits for wave 5 (writei).
`Xv6/BitmapInv.lean` + `Xv6/FsStateBitmap.lean` (B4b) come AFTER the byte view lands (needs B2c).
No Xv6.lean edits, no commits; report files, line counts, deviations.
