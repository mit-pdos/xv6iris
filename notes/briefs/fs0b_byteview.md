# Brief: wave 0b — the byte view (B2a → B2b → B2c, then B2d + B4c)

Read notes/briefs/fs0_common.md (rules) and notes/fs-lean-design.md §0, §2, §6 (the decision and
the exact blast radius). Work in the worktree /shared/lean-xv6/.claude/worktrees/fw2 on branch
`byteview` (already created off lean-v2; it has its own .lake caches). You are the only builder
there, so a bare `lake build` at the end is allowed and REQUIRED before you report.

Order:
1. B2a `Xv6/FsBytes.lean` (`byteRange{,Q}`, `fsblock{,Q}`, `blkSplice`, exclusivity + split kit)
   plus the `FsNames` +2 fields and `fsGhostAlloc` edit in `Xv6/FsBlocks.lean`.
2. B2b `Xv6/FsBytesMap.lean` (`mapSeq` + `mapSeq_get?`/`_inj`/`_slice`, `byteRange_lookup`/
   `_update`) — the hardest pure file; split lemmas aggressively.
3. B2c `Xv6/FsBytesInv.lean` (`exc*`, `bytesDom`/`bytesTie{,Exc}`/`bytesExcVal`, `fsBytesBody`/
   `fsBytesInv`, `fsblock_home{,_open}`, `fs_bytes_agree{,_exc,_q}`, `byteRange_log_update`,
   `fsblock_update`, `fsblock_install_exc`). Rocq: /shared/xv6rocq/iris/FsBlocks.v (the byte-view
   half), FsBytesGamma.v.
4. B2d `Xv6/FsBytesMint.lean` (`byteMapGrow`, `fsBytesAlloc`, `fsAlloc`, `fsBytesAt/Row/Any/AnyAt`).
5. B4c THE LOG RE-WIRE, exactly as design §2.6/§6.3: `logCtx` gains the persistent `fsBytesAny`
   conjunct; `SpecLogWrite` `fsChalf → fsblock` at one resource; `SpecInstallTrans` recovering rows
   → `emp` + `excOwn` thread, `ProofInstallTrans` home update via `fsblock_install_exc`
   (`wpLoop_bupd → wpLoop_fupd`); `ProofLogWrite`'s two home `fsCache_update`s → `fsblock_update`;
   `SpecInitlog` DROPS `hhdr0` and takes `excOwn (fs_exc γfs) (hdrDec bsHdr).2` (Rocq's shape);
   `ProofInitlog` gains the `excSeal` step; `ProofEndOp`/`LogBoot` arity only. `logStateAt`/
   `logResAt`/`write_head`/`end_op`/`begin_op` specs must NOT change. Do NOT wire `sbParked`
   into `logCtx` (design §3/§6: fsinit-only, later).
Commit on `byteview` with explicit paths after each green step; append new modules to Xv6.lean.
Report: files + line counts, every statement that changed, the final root build line.
