# Brief: wave 0c — the inode region (three sequential sub-batches, main tree)

Read notes/briefs/fs0_common.md (rules: build only your own modules, no bare `lake build`, no
edits to existing files — report them, no Xv6.lean edits, no git). Survey sections to read
first: notes/fs-rocq-summary.md §2.6 (inode shape/cells/ownership), §2.8 (InodeRegion), §2.11
(abstract state — only what §2.8 cites), §2.12 (DirView), §2.15 (DinodeSlot/OffBox), §6 pitfalls
for ilock/iupdate/iget; design note notes/fs-lean-design.md §1 (ambient `Fscfg`).
Landed vocabulary to reuse: Xv6/FsGeom, DinodeEnc (dinode encoders, `halfBytes`), BlockWords,
InodeDefs, ByteBuf/ByteCursor/ArrCursor, FsBytes*/FsStateDefs/FsBytesGamma (byte view:
`fsblock`, `byteRange`, `excOwn`), FsCfgDefs (`Fscfg`), BcacheInv/BioPool (`bioLocked`,
`bufHold0`, `bioPay`, `bslot`), LogInv (`logOpS`, `loggedAt`), SleepLockDefs (`isSleeplock`),
MachCSL/CtxBox.lean (Rocq CtxBox — OffBox is stated over it), KA.«itable»/KA.«sb» (Xv6/KernelImage).

## 0c-1  DinodeSlot, InodeLock, InodeInv, FsNode + the FsStateInode subset
Rocq: /shared/xv6rocq/iris/DinodeSlot.v (905), InodeLock.v (171), InodeInv.v (1754), FsNode.v (37),
and from FsStateInode.v (2097) ONLY what InodeRegion.v/InodeInv.v/InodeLock.v consume
(`fn_bare`, `fn_file_bytes`, `fn_nlink`, `fn_size`, `fn_type`, `inode_local`, `inode_local_bare`
and their lemmas) — put that subset in `Xv6/FsStateInode.lean` with a header listing what was
deferred. Lean files: `Xv6/DinodeSlot.lean`, `Xv6/InodeLock.lean` (`inode_ok`/`dir_ok`/
`inode_ref_spos`), `Xv6/InodeInv.lean` (`inode_meta`, the `i_*` field addresses at stride 136
off KA.«itable», `ireg_blocks_ok`, `blkmap_wf`/`bm_covers`/`blk_holes_zero`/`inode_sized`),
`Xv6/FsNode.lean`, `Xv6/FsStateInode.lean`. (InodeRef.v waits for 0d: it imports IrefSlots/
IcacheRefDefs.)

## 0c-2  InodeRegion (5578 lines → split into 3–4 Lean files)
Rocq InodeRegion.v: `dinode_at`, `ireg_slot`, `ireg_inv`, `ireg_withdraw`, `fresh_shape`,
`diblk_wf`, `ftop_inv`, "OPTION A: region_pending". Split by section into
`Xv6/InodeRegionDefs.lean`, `Xv6/InodeRegion.lean`, `Xv6/InodeRegionWithdraw.lean`,
`Xv6/InodeRegionFresh.lean` (or similar; keep each under ~1500 Lean lines). It imports
IcacheRef/EscrowDefs in Rocq but (checked) uses nothing from them — do not pull 0d in.

## 0c-3  DirView, OffBox
`Xv6/DirView.lean` from DirView.v (1447; the `dir_*` family over DirentEnc/InodeDefs),
`Xv6/OffBox.lean` from OffBox.v (581; the inode's off rows over MachCSL/CtxBox.lean).

Every Rocq lemma ported and proved; no `sorry`; short tactic blocks; one Lean file per Rocq file
except the InodeRegion split. Report files, line counts, build last lines, deviations, reused
names, and any edit an existing file needs (exact old → new).
