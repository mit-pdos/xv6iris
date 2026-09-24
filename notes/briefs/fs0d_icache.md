# Brief: wave 0d — the inode cache (and the rest of the inode region)

Read notes/briefs/fs0_common.md first. Its rules all apply: build only your own modules, never a
bare `lake build`, no edits to existing files (report them instead), no Xv6.lean edits, no git.
Its **cleanup paragraph** applies too, with the stricter rule given below.

**The user's standing instruction, verbatim: "the file system is a tricky piece of spec/proof. It's
important to consult the Rocq version whenever you might be possibly in doubt about the right way
to spec/prove something; it has the whole thing fully specified and proven."** In practice: before
you choose a statement shape, an invariant arm, a mask, or a proof route, open the Rocq file and
copy what it does. The Rocq proof is the reference answer. When you depart from it, you need a
reason, and the reason goes in the file header.

**Cleanup (user, Sept 24).** "The big ideas come from Rocq (definitions, invariants, spec shapes,
proof strategy), but cleanup IS welcome, because a fair bit of gunk has accumulated in the Rocq
proofs." You may drop dead lemmas, duplicate helpers, historical shims (round-numbered "r25"-style
workarounds whose reason does not apply in Lean) and unused parameters or conjuncts. **Only
simplify when you can see the complete picture.** A local simplification can clash with a
downstream spec or proof. So before any cleanup, trace the item's uses through ALL later Rocq
files: definitions, `Spec*`, `Proof*` and `Link*` of the fs functions and the syscall layer
(`grep -rnw <name> /shared/xv6rocq/iris/*.v`, ignoring comments). If you cannot confirm that the
simplified form serves every consumer, keep the Rocq form. List each cleanup in the file header as
"Dropped/simplified vs Rocq: <item> — uses checked: <files or 'none'> — reason".
The per-file gunk lists in §4 say what I checked. Items marked **unverified** stay unless you check
them yourself.

Survey sections: notes/fs-rocq-summary.md §2.2.3 (`icfg`), §2.7 (reference algebra), §2.9
(escrow and pool), §2.10 (IgetLic, EscrowDefs/EscrowInode), §2.15 (OffBox), §2b(B) (the icache
design story, especially B.10's standing rules), §6 T18 (the icache traps), and §7.1 batch 0d
(superseded by this brief). For ambient classes, read notes/fs-lean-design.md §1.
The pre-compaction design doc that Rocq headers cite as "fs-icache.md §13.x/§14.x/§20.x" is at
`git -C /shared/xv6rocq show 1a86ed5f3^:claude-notes/design/fs-icache.md`. `completed/iclaim-ledger.md`
is live.

## 0. What landed, what is in flight, what this wave adds

- **Landed** (use; do not duplicate): FsGeom, DinodeEnc, BlockWords, InodeDefs, BlkmapDefs,
  ByteBuf/ByteCursor/ArrCursor, FsBytes*/FsBlocks/FsStateDefs/FsBytesGamma, FsImg, FsStateBitmap,
  BitmapInv, FsCfgDefs (`Fscfg`, `FsGeomOk`), LogDefs/LogInv (`LogG.gmTx` = Rocq `ln_tx`),
  SleepLockDefs (`slhTok`, `slhAuth`, `SlhRF = Auth (Option UFrac)`, `slh_mint`, `slh_return`,
  `slh_return_last`, `slh_mint_none`, `isSleeplockGen`), FileDefs (`fileStride`, `fileBase`, `fnode`,
  `aFoff`, …), DinodeSlot, InodeLock, InodeInv, FsNode, FsStateInode (the pure `fn*` subset only),
  MachCSL/CtxBox.lean (unit-mass box, see §3 D3), MachCSL/WordHist.lean (`wordCell`, racy reads).
- **Landed from wave 0c (untracked at the time of writing):** Xv6/DirView.lean,
  Xv6/InodeRegionDefs.lean (Rocq InodeRegion.v 1–1275), Xv6/InodeRegion.lean (a subset of Rocq
  1281–5578: `dinodeAt`, `imark`, `iregOut`, `iregCouple`, `iregIn`, `iregLinkOk`, `iregNl`/`iregMult`,
  `ctyPin`, `iregN`/`ftopN`, `iregBlkSlot`, `iregWdTy`/`ilkPost`, and the `IregG` class with **`Int`
  keys**). Its header lists every deferred item by Rocq line. **Those deferred items are this
  wave's work** (files InodeRegionSlot/Inv/Movers/Withdraw/Link below).
- **In flight (another agent), will exist before batch A:** Xv6/IcacheRefDefs.lean (the `Icfg`
  ambient class, `IcNames`, itable geometry `ientry`/`i_*`, the icache camera encodings from Rocq
  Xv6Cameras §11 and `IcacheG`, `Section IcacheIty` with `ity_shot`/`ireg_boot`/`ireg_open`/
  `ireg_regime`, `icfg_alloc`), Xv6/IrefSlots.lean (`IrefslotG`, `iref_slots`), Xv6/InodeRef.lean,
  and Xv6/FsTree.lean (wave 0c). **Grep these before you define anything** that Rocq puts in those
  files. If a name you need is missing there, report it; do not re-create it in your file.

## 1. Coordinator gate before batch A (edits to existing files; agents must not make them)

- **P1 — DONE (coordinator, Sept 24 2026).** `FsNames.link/top`, `FsViewNames.link/top`, `fsGammaL` fills them, `fsGhostAlloc (γlk γtp)` takes them as parameters (Rocq `fs_alloc`). Original text: **P1 (needed by A2/A3/B6): the abstract-state gnames.** Xv6/FsStateDefs.lean deviation 1 dropped
  `γlink`/`γtop`, saying "the record grows when that layer lands". This wave is that layer. The
  change: `FsNames` (Xv6/FsBlocks.lean) gains `link : GName` and `top : GName` after `exc` (it has
  no constructor sites). `FsViewNames` gains `link top : GName`. `fsGammaL` fills them from
  `γfs.link`/`γfs.top`. The two other `{ phi := … }` sites (FsStateDefs.lean:290,
  FsStateBitmap.lean:132) become `{ Γ with phi := … }`. Rocq: `fs_link`/`fs_top`, `γlink`/`γtop`.
- **P2 — DONE (coordinator).** `Fscfg` gained `fscIc`/`fscItlock`; the duplicates `fscLog`/`fscInodestart` are REMOVED (Rocq keeps them in `icfg` only: use `icfgLog`/`icfgIst`/`icfgNib`/`icfgDev`); `FsGeomOk [Fscfg] [Icfg]` now has Rocq's full clause list (`fgoRootdev`, `fgoNibPos`, `fgoIreg` over `icfgIst icfgNib` — the old one wrongly used the inode count —, `fgoNinLo/Hi/31`, `fgoUshort`; `fgo_ist_nn` vacuous at Nat). Original text: **P2: `Fscfg`.** Add `fscIc : IcNames` and `fscItlock : GName` (Rocq `fsc_ic`/`fsc_itlock`,
  FsCfg.v:129–130), importing Xv6.IcacheRefDefs. Later, add the icache clauses of Rocq
  `fs_geom_ok`: `fgo_rootdev`, `fgo_nib_pos`, `fgo_nin_lo`/`_hi`/`_31`, `fgo_ushort`. Settle ONE
  source of truth for the two duplicates. Lean has `fscInodestart` where Rocq has `icfg_ist`. Lean's
  `iregBlocksOk` is stated over `fscNinodes` where Rocq's `ireg_blocks_ok` uses `icfg_nib`, and the
  region's inum range is `16 * icfg_nib` in Rocq. `fscLog` "moves to Icfg when the icache lands"
  (FsCfgDefs deviation 2): decide. No 0d file needs P2, because everything here is "structurally
  below" `Fscfg` and takes `cn`/`γl`/`γi` as parameters, exactly as Rocq does. The fs.c specs will
  need it.
- **D3 (blocks B4, C5, G2): a box WITH MASSES — DECIDED (user, Sept 24 2026): GENERALISE
  MachCSL/CtxBox.lean** to Rocq CtxBox.v's full design (stamped-share masses, `qsum`/`mscale`/
  `reference_split`/`reference_join`/`reference_llb`/`stamps_frag`/`max_stamp`, the hooked forms,
  `box_q_update`/`box_q1_update`, general `box_withdraw_L1`/`box_deposit_L1`), with the bcache
  instantiating unit masses as Rocq's bcache does. One box, as in Rocq; NO separate CtxBoxQ. This
  is done by a coordinator-run worktree agent before B4; A6/B8 below are therefore that agent's
  work, not batch items.
- **D4 — DECIDED (coordinator, on the A10 spike): OPTION (b), re-express over `wordCell`; read notes/fs0d-pinw-design.md and follow it (it lists every changed statement, §7).** Original text: **D4 (blocks B4's `cred_floor`/`live_fracc`, C4, D5): the racy `ref` read.** Rocq A6.145 puts the
  50 `ip->ref` words under a TSO word-set PIN (`TsoCtx.phys_ledger_pinw`, `TsoMemPa.TsPinw`,
  `CtxPinw.ledger_read_pinw_latest`, `MemClaim.wordw_claim`). The (g, lo) epoch rides the liveness
  slice (`live_genlo`, `cred_floor`, `icfg_istmp`). **None of that exists in Lean.** Lean's
  racy-read discipline is MachCSL/WordHist.lean: `wordCell pa n lo v0 W`, where a racy load returns
  a whole entry of `W` or `v0` (`read_cases`), and MachCSL/Lock.lean uses it for the spinlock word.
  So `iref_pin_rows`, `pinw_slot`, `iref_claims`, `iref_set_read` and IcachePinwObl must be
  RE-EXPRESSED over `wordCell`: the value-set invariant `iref_set` = "every entry of `W` (and `v0`)
  is in `1..IREFSLOTS`". That is the one place where 0d cannot port literally. A10 below settles it
  before B4/C4 start.

- **P3 — DONE (batch-A merge): `Xv6/FileGeom.lean`.** Move `NFILE`, `FDSPARE`/`FDSLOTS`,
  `ftableAddr`, `fileStride`, `fileBase`, `fnode`, `aFtype`…`aFmajor` out of Xv6/FileDefs.lean into a
  light file imported by FileDefs, FileOffCell and IrefSlots (Rocq's FdSlots.v split; avoids the cycle
  FileDefs → OffBox → FileOffCell → FileDefs once the file table's inode arm lands).
- **W7 follow-up (not 0d):** the file table's off conjunct. Lean `fileFieldsAt` gives every reference a
  VALUED fractional share of `f->off` (`∃ off, wordAtN ξ (aFoff k) 4 (DFrac.own q) off`; FileFrac,
  ProofFileclose:300, ProofPipealloc:569/581). Rocq `FileInvDefs.file_core_off` = the off box for
  FD_INODE, `off_free k q` (alignment + unvalued bytes) otherwise. Replace when the file layer is
  re-ported (wave 7), after C5 OffBox.

- **KEY-TYPE SEAM (standing rule).** Rocq keys inums by `Z` everywhere. In Lean, the region map
  (`IregMapF`, Int for the negative marker) and the link camera (`FsStateLink`, `FsLinkMapF`) are
  `Int`-keyed; the icache/escrow cameras (`IcacheG`, `regionPending`, `committedA`) and FsStateInode's
  dirent targets are `Nat`. Do NOT introduce a third convention. Where a file meets both, state the
  bridge ONCE as named lemmas (e.g. `z.toNat` under `0 ≤ z`, `(n : Int)` casts) in the lowest file
  that sees both, and reuse them.

## 2. Per-Rocq-file facts

Legend: [L] ported in Lean (file name), [F] in flight, [P] partial in Lean, [-] not in Lean (who
ports it here), [M] framework name mapped to a MachCSL analogue.
Framework mappings used throughout: RiscvPtsto/RiscvExtras/RiscvModelBytes/RiscvLang [M] MachCSL
(`nth_byte` = `nthByte`, `pa_add` = BitVec `+`); TsoCtx/TsoGhost/CtxIdDefs [M] MachCSL/Ctx.lean and
CtxLaws.lean (`CurCtx`, `CtxMorph`, `ctxFloor`, `ctxStamped`, `llb`, `wordAtN ξ a 4 dq v` for
`↦₄`); `GenId`+`CurCtx` section contexts [M] per-declaration `[CurCtx]` (tools/curctx_binders.py);
CtxMorphTac `ctx_morph_solve` [M] `infer_instance` on `CtxMorph` (FileDefs.lean does it this way);
WpLock [L] MachCSL/WpLock.lean; SleepLock [P] Xv6/SleepLockDefs.lean (`is_sleeplock_genl`,
`sl_fresh`, `sl_free_tok`, `sl_fresh_new_genl` are missing; only IcacheEscrow §6b and IcacheBoot §4
use them); Xv6Cameras/Xv6G [M] one capacity class per layer (Lean has no single bundle; do NOT
create one); FastSetSolver [M] `simp`/`decide`; BioDefs `BSIZE` [M] DiskDefs; ProcGeom `NPROC`,
FdSlots `NFILE` [M] existing Lean constants; KernelSyms [M] `KA`.
TsoMemPa/CtxPinw/MemClaim [-] handled by D4. SepThread (`big_sepL_fupd_thread`) and WpLockAt
(`lock_free_tok`, `newlock_at_llb`) [-] are used only by IcacheBoot §4 (and one IcacheEscrow alloc
lemma). For these, see MachCSL/LockBornHook.lean and Xv6/BioInit.lean for the Lean boot-lock idiom.

| Rocq file | lines | non-stdlib Requires → status | what is actually used from the not-yet-ported ones | cameras (Xv6Cameras) → Lean |
|---|---:|---|---|---|
| IcacheRef.v | 2210 | RiscvPtsto, SleepLock [P], CtxBox [P→D3], Xv6Cameras, IcacheRefDefs [F], TsoCtx [M] | CtxBox: `qsum`,`mscale`,`reference_*`,`stamps_frag`,`max_stamp` (box part only); TsoCtx `ctx_floor`,`ctx_wrote`,`ctx_word4_pointsto_{agree,frac_split}` | icacheG members (icacheUR, iliveUR, linkUR/linkElemUR, ityR, icntUR, frzmUR, hpnUR, frzUR/ctyUR) → `IcacheG` [F]; lockG → SleepLockG; icboxG (stampsR ic_bid, slot_reg, l2_reg) → none, B4 defines it over CtxBoxQ; kallocG binder only |
| IcacheInv.v | 4326 | RiscvPtsto/Extras, SleepLock [P], Xv6Cameras, MemClaim [-D4], TsoCtx, RiscvModelBytes, LogInv [L], IcacheRef, InodeInv [L], DinodeEnc [L], FsBlocks [L], InodeRegion [P], AppCfg [-], IgetLic, IrefSlots [F], Xv6G | InodeRegion (§5b only): ~40 `ireg_*` incl. `ireg_frz_ok`, `ireg_key_split`, `ireg_rcol_*`, `ireg_frzm_read`, `ireg_frz_pin_read`; IgetLic: `iname`,`ilic`,`is_claim`,`iname_not_frozen`,`iname_buf_list`,`iname_mint_ok`; AppCfg: section binder only (rides `ireg_inv`) | icacheUR `● M`, mono_nat (`icfg_istmp`), irefslotG; the pinw ledger → D4 |
| EscrowDefs.v | 135 | RiscvPtsto, IcacheRefDefs [F] | — | mono_nat, `exclR unit` (tickG), ghost_map Z (gname*gname) (regG), ghost_map Z icorpse (pcrpG): all `IcacheG` [F] |
| EscrowInode.v | 262 | FsBlocks, FsState [-A2: `top_frag` only], FsBytesGamma, IcacheRef [link §: `ifreeze_off`,`ifreeze_post`], EscrowDefs, Xv6G | — | mono_nat, tickG, `inv` |
| EscrowDeposit.v | 387 | LogInv, FsBlocks, DinodeEnc, FsStateDefs, FsBytesGamma, InodeRegion [~45 names, Slot+Inv], AppInv [`appN` only], AppCfg [binder], EscrowDefs, EscrowInode, IcacheEscrow [pool §: `ipool_deposit_corpse`,`ipoolN`,`ipool_inv`,`CrpPre`], Xv6G | IcacheInv `islot` (§6) | — |
| IcacheEscrow.v | 6376 | RiscvPtsto/Extras, WpLock [L], TsoCtx, FsBlocks, DinodeEnc, DirView [L], FsTree [F: `dir_uniq` + `dir_names_unique`], InodeInv, InodeLock [L], SleepLock, InodeRegion [only `imark`,`dinode_at`,`iregN`,`ireg_reg`,`di_nlink_nonneg`], AppCfg [binder], FsState [`top_frag`], FsBytesGamma, LogDefs, TxPin [-A2], FsStateEra [-: 17 names up to Rocq line 2041, see B7/C2], EscrowDefs, EscrowInode, IrefSlots, IgetLic [`iname`,`ilic`,`iname_freeze_off`], IcacheInv [§5+§6 only: `icacheN`,`itable_inv(_pinw)`,`frz_slot_kill_pinw`,`icM_wf`,`isl_pool`,`iref_claims`,`frz_park`,`islot_rest_at`,`islot_free_at`], IcacheHeld [`inode_ident_morph`], Xv6G, TsoGhost, CtxBox [~30, box §], OffBox [`off_cfg`,`off_rows(_dep)`,…], CtxMorphTac, SepThread | | IcacheG members ic_dep/ic_id ghost_vars, regG, lkG, poolG, ptrnG, pcrpG; icboxG; `bioslotG` and `irefslotG` are **unused section binders** (§4) |
| IcacheHeld.v | 607 | RiscvPtsto, SleepLock, Xv6Cameras, IcacheRef, TsoCtx | IcacheRef §4 (`inode_refp`,`live_fracc`,`cred_floor`,`inode_shr_genlo`,…) | icacheG, icboxG, lockG, kallocG binders |
| IcacheCover.v | 348 | RiscvPtsto, Xv6Cameras, FsBlocks, IcacheRefDefs, InodeRegion [`imark`], FsStateInode [`node_dir_local`], LogDefs, TxPin, FsStateEra [`era_node`,`node_dir_local_of_ok`], IrefSlots, Xv6G, CtxIdDefs, CtxBox [`box_arm`,`in_arm`,`box_body`,`box_view`,`box_rows`; Lean has `boxArm`/`inArm`/`boxBody`/`boxView`/`boxRows`], IcacheEscrow [box §] | | |
| IcachePinwObl.v | 181 | RiscvModelBytes, RiscvPtsto, RiscvLang, RiscvExec, TsoMemPa, TsoGhost, TsoCtx, CtxPinw, IcacheRef, IcacheInv, Xv6G | all of it is the pinw read obligation → D4 | |
| IcacheBoot.v | 1704 | + ArrCursor, WpLock, MemClaim, CtxBox, SepThread, WpLockAt, SleepLock, BlockWords, DirView, InodeInv, InodeLock, InodeRegion [Slot+Inv], AppInv [`app_inv`], AppCfg, FsState, FsBytesGamma, FsStateEra, IrefSlots, IcacheInv, FsTree, IcacheEscrow [~44], OffBox, LogInv, FastSetSolver, Xv6G | §1 is pure; §4 needs the boot-lock idiom | everything |
| IgetLic.v | 786 | FsBlocks, LogInv, DinodeEnc, IcacheRef [`iclaim`,`ifreeze`], InodeRegion [Slot+Inv + `ireg_read`], AppCfg [binder], FsStateLink [-A3: `link_tok`], FsBytesGamma, Xv6G | | fsLinkG |
| OffBox.v | 581 | RiscvLang, RiscvPtsto, TsoGhost, TsoCtx, CtxMorphTac, Xv6Cameras, CtxBox [~24 incl. `qsum`,`reference_*`,`box_withdraw_L1_free`,`box_checkout`,`box_park`,`box_alloc_at`], RiscvModelBytes, IcacheRefDefs [`icfg` for `icfg_off`], FileOffCell | | offboxG (`box_names`, `l2_reg nat`, `slot_reg`) → none, A7/C5 |
| FileOffCell.v | 128 | RiscvPtsto/Extras, ArrCursor, BioDefs, InodeInv [`MAXFILE`], TsoCtx, Xv6Cameras, OffGv | the geometry (`file_stride`…`a_fmajor`) duplicates Xv6/FileDefs.lean: **reuse it**, port only `off_wf`*, `a_foff_aligned`, `off_resident`* | offboxG |
| OffGv.v | 139 | RiscvPtsto, Xv6Cameras | | offboxG's `ghost_var Z` |
| — prerequisites this wave also ports — | | | | |
| InodeRegion.v 1595–5578 | ~4000 | IcacheRef [link §], EscrowDefs, TxPin, FsState [`top_frag`], FsStateLink [`link_auth`,`link_tok`], FsStateInode [`rec_owned_at`, `inode_local`], FsAbsDefs [`abs_view`,`abs_of`], AppCfg/AppInv [`app_inv`,`appN`,`app_top_update*`,`app_pred`,`app_run`,`app_sup`], IcacheRefDefs [F], LogDefs | also `IcacheRef.inode_claimed`/`inode_ref` in ONE lemma (`inode_claimed_to_ClaimK`, 4713) | iregG [L `IregG`], icacheG, fsLinkG, fsTopG, LogG.gmTx |
| TxPin.v | 167 | Xv6Cameras, LogDefs | whole file | LogG.gmTx [L] |
| FsState.v | 910 | only `top_frag`/`top_frag_q` + split/agree (FsState.v 229–300) are used by 0d; the rest (`fs_state`, `fs_inodes`, …) is wave 6 | | fsTopG: ghost_map Z fs_node → none, A2 |
| FsStateLink.v | 553 | FsStateDefs, Xv6Cameras | whole file (link_auth/link_tok/link_toks, gather, law) | fsLinkG: `authUR (gmapUR Z (authR (gmultisetUR ity)))` → none; iris-lean has Auth, LeibnizMultiSet, GenMap |
| FsStateInode.v 48–2085 | ~1900 | BioDefs, BlockWords, DinodeEnc, DirView, InodeDefs, FsTree [F], FsImg, FsNode, FsStateLink | §1 remainder (`fn_nrec`,`fn_is_dir`,`dir_entries`) + §2/2a/2b (`inode_local`…, 94–421); §3 RecOwned (422–672); §3c InodeOwned (675–2085: `inode_dat`,`ent_toks`,`inode_owned`,…, needed by FsStateEra) | fsLinkG |
| FsAbsDefs.v, AppCfg.v, AppInv.v | 679+74+448 | FsAbsDefs is pure (FsStateInode readings, FsTree, DirView; its `Require Export FsState` is not needed for its own content); AppCfg = class `appcfg Σ` (a `Type` field and an `iProp` field); AppInv needs fsTopG + icfg | whole files (AppInv §1 "raw credentials" are used by `app_sup`, which InodeRegion names) | fsTopG |
| FsStateEra.v | 3196 | FsStateLink, FsStateInode, FsState [`top_frag(_q)`], FsBytesGamma, DirView, FsTree, InodeInv, InodeLock, … | 0d uses up to line ~2060 (`era_node` 202 … `ent_toks_x_era_nrec0` 2041); 2060–3175 is for later function proofs | — |

## 3. Lean file plan (split by Rocq section)

| new Lean file | Rocq source (lines) | ≈ lines |
|---|---|---:|
| IcacheRefLink | IcacheRef.v header + §3d `Section IcacheLink` (1–827: `iclaim`, `ifreeze*`, `icnt_at`, `frzm_at`, `hpn_at`, link-ledger movers) | 830 |
| IcacheRefGhost | IcacheRef.v `Section IcacheRefGhost` (829–1273: `iref_frag`/`iref_tok`, `live_frac*`, `live_gen*`, `frzsel`, `runit`, `itable_half`) | 445 |
| IcacheRef | IcacheRef.v §4 (1276–2210: `inode_ident`, `cred_floor`, `live_fracc`, `ic_stamps`, `inode_ref`/`inode_shr` and the gen/genlo/short forms, carve/gather, `inode_refp`, `inode_claimed`) | 935 |
| IcacheInvAlg | IcacheInv.v §1–§4 (1–1453) | 1450 |
| IcacheInvRef | IcacheInv.v §5 (1454–2303) + §6 (4171–4326; §6 uses nothing from §5b) | 1010 |
| IcacheInvFrz / IcacheInvStore | IcacheInv.v §5b (2304–3080 freeze mirror and `ireg_icnt_*_acc`; 3081–4168 the `*_store_pinw_au` movers) | 780 / 1090 |
| IcacheEscrowTok | IcacheEscrow.v 1–1284 (§0 names, §1 tokens, §2 payloads to the read arm) | 1280 |
| IcacheEscrowDep | IcacheEscrow.v 1285–2104 (the freeze token on the payload, `ic_dep_*`, `ic_out_*`, `ic_loaded_flat_body`) | 820 |
| IcacheEscrowPool | IcacheEscrow.v 2105–3360 (§5–5c'': pool, partition, transit, corpse ledgers) | 1255 |
| IcacheBoxAmb | IcacheEscrow.v 3361–4081 (the box-instance header M-1'…F20, `Section IcacheBoxAmb`) | 720 |
| IcacheBox | IcacheEscrow.v 4082–5516 (`Section IcacheBox`) | 1435 |
| IcacheTable | IcacheEscrow.v 5517–6376 (§6 `itable_res2`/`is_itable2`, §6b sleeplocks, §6c env morphs, §7 alloc) | 860 |
| EscrowDefs, EscrowInode, EscrowDeposit, IcacheHeld, IcacheCover, IcachePinwObl, IgetLic, OffGv, FileOffCell, OffBox, TxPin | whole files | as Rocq |
| IcacheBootDecode / IcacheBootRegion / IcacheBootTable | IcacheBoot.v 1–284 / 285–1134 / 1135–1704 | 285 / 850 / 570 |
| InodeRegionSlot | InodeRegion.v 1595–2759 (receipts, freeze mirror/shelter, `ireg_rcol`, type register, top park, claim share, `ireg_slot`) | 1165 |
| InodeRegionInv | InodeRegion.v 2760–3594 (byte unit `ireg_recs`, `ireg_blk`/`ireg_body`, `ftop_inv`, `ireg_inv`, retags, `ireg_blk_mono`/`ireg_blks_acc_upd`/`ireg_slots_acc_upd`) | 835 |
| InodeRegionMovers | InodeRegion.v 3595–4670 (`ireg_read` … `ireg_frz_pin_read`) | 1075 |
| InodeRegionWithdraw | InodeRegion.v 4671–5039 (+ `inode_claimed_to_ClaimK`, which imports IcacheRef) | 370 |
| InodeRegionLink | InodeRegion.v 5040–5578 (`ireg_link_pin` …) | 540 |
| FsStateTop | FsState.v 229–300 (`top_frag`, `top_frag_q`, split/agree) + `FsTopG` | 80 |
| FsStateLink | FsStateLink.v (+ `FsLinkG`) | 553 |
| FsStateInodeLocal / FsStateRecOwned / FsStateInodeOwned | FsStateInode.v 48–421 (minus what Xv6/FsStateInode.lean has) / 422–672 / 675–2085 | 330 / 250 / 1410 |
| FsAbsDefs, AppCfg, AppInv | whole files | 679+74+448 |
| FsStateEraPure / FsStateEraRes / FsStateEraResB | FsStateEra.v 1–1021 / 1022–~2060 / ~2060–3196 (cut at a lemma boundary after `ent_toks_x_era_nrec0`) | 1020 / 1040 / 1140 |
| MachCSL/CtxBoxQ / MachCSL/CtxBoxQOps | CtxBox.v 1–~715 (helpers `qsum`…, defs, `reference_*`, rows) / ~716–1775 (withdraw/deposit/ref/checkout/park/l1_to_l2/q_update/view/alloc) | 715 / 1060 |

Class ownership, so that two agents never define the same one: `FsTopG`→A2, `FsLinkG`→A3, the generic
mass-box camera class→A6, `IcboxG`→B4, `OffboxG` (+ its box instance)→A7 (the ghost var) and C5
(the box part). `IcacheG`/`IrefslotG`/`Icfg`/`IcNames` come from the in-flight files. Leave
`IregG` in Xv6/InodeRegion.lean.

## 4. Schedule — batches (one agent per line; all agents in a batch are independent)

Deps name batch items; "gate" = §1 plus the in-flight files.

**Batch A (10 parallel)**
- [DONE] A1 IcacheRefLink — gate.
- [DONE] A2 EscrowDefs + TxPin + FsStateTop — gate, P1.
- [DONE] A3 FsStateLink — gate, P1.
- A4 [DONE — Xv6/FsStateInode.lean now has `InodeLocal`, `inodeLocal_bare`, `dirEntries`, `fnIsDir`, `fnNrec`; `inodeLocal_freeNode` is in InodeRegionDefs] FsStateInodeLocal — gate (DirView, FsTree).
- A5 [DONE — `recOwned`/`recOwnedAt`/`inodePhi`/`inodeDat`/`indOwned` and their lemmas are in Xv6/FsStateInode.lean] FsStateRecOwned — gate.
- A6 [SUPERSEDED — D3 decided: CtxBox.lean is generalised in place by a separate worktree agent] MachCSL/CtxBoxQ — D3. Port Rocq CtxBox.v literally. Reuse MachCSL/CtxBox.lean's proofs where
  the unit-mass version already did the work. (This file and B8's are an explicit exception to
  fs0_common's "only under Xv6/" rule. Build with `timeout 1800 lake build MachCSL.CtxBoxQ`.)
- [DONE] A7 OffGv + FileOffCell — gate.
- [DONE] A8 IcacheRefGhost — gate.
- [DONE] A9 IcacheBootDecode (pure 1024-byte ↔ 16 dinodes decode) — gate.
- A10 [DONE — notes/fs0d-pinw-design.md, option (b) approved] **pinw design spike** (no Lean file). Read IcacheInv §5, IcacheRef 1276–1426, IcachePinwObl,
  MemClaim.v, and MachCSL/WordHist.lean + Lock.lean. Write notes/fs0d-pinw-design.md: the Lean
  shapes of `iref_pin_rows`/`pinw_slot`/`iref_claims`/`cred_floor`/`live_fracc`/`iref_set_read`
  over `wordCell`, and which Rocq lemmas become trivial or change statement. The coordinator
  approves it before B4/C4. (This note is the only non-Xv6 file A10 writes.)

**Batch B (8)**
- [DONE] B1 InodeRegionSlot (KEY TYPES: the icache/escrow maps — `IcacheG.regG`/`pcrpG`, `regionPending`, `committedA` — are `Nat`-keyed; the region map `IregMapF` stays `Int`-keyed for the negative marker `imarkKey`. Rocq uses `Z` for both, so bridge at the seam with `z.toNat` under `0 ≤ z`, stated once as helper lemmas, not ad hoc) — A1, A2, A3.
- [DONE] B2 FsAbsDefs + AppCfg + AppInv — A4, A2 (FsTopG).
- [DONE] B3 FsStateInodeOwned (NOTE: this is now the REST of FsStateInode.v — the link-camera parts (`ent_tok*`, `inode_ghost`, `inode_owned`, §6, §8/8b) AND the `ity`-typed parts (`fn_ity_ok(_ex)`, `ent_ty_ok`, `node_ent_ok`; `Ity` is now in IcacheRefDefs, which does not import FsStateInode) — edit Xv6/FsStateInode.lean, see its DEFERRED header) — A3, A4, A5.
- [DONE] B4 IcacheRef (CtxBox generalised: use `reference`/`stampsFrag`/`StampMap`/`qsum`/`maxStamp`/hooked forms from MachCSL/CtxBox.lean; `IcboxG.stampsG : ElemG GF (StampsRF IcBid)`; `icBoxRaw_allocAt` feeds `boxAllocAt`) — A1, A8, A6, A10.
- [DONE] B5 IcacheInvAlg — A8.
- [DONE] B6 EscrowInode — A1, A2.
- [DONE] B7 FsStateEraPure — A4.
- B8 [SUPERSEDED — part of the CtxBox generalisation] MachCSL/CtxBoxQOps — A6.

**Batch C (5)**
- [DONE] C1 InodeRegionInv (NOTE from B2: `appBody` holds `γfs.top ↪●MAP{DFrac.own (1 : Qp).half} I`; `ftop_body` must hold the kernel's half at the same `(1 : Qp).half` spelling so the halves join) — B1, B2, A4, A5.
- [DONE] C2 FsStateEraRes (NOTE from B7: FsStateEraPure dropped `inode_ok_data_ext` because its only consumer `inode_owned_era_era_node_ok` (FsStateEra.v:1962) is listed dead in §5 — re-verify that; if you keep it, port `inode_ok_data_ext` (6 lines) too. Rocq's FsStateEra `dir_nrec_bound` is `dirNrec_boundMax` in Lean. `DOT_dot_name` was dropped as a duplicate: use `DOT_dot`. Start at `Section EraRes`, line 1022, with `big_sepL_seq_map`) — B3, B7, A2.
- [DONE] C3 IcacheHeld — B4.
- [DONE] C4 IcacheInvRef — B5, B4, A1, A10.
- [DONE] C5 OffBox — B8, A7.

**Batch D (6)**
- [DONE] D1 InodeRegionMovers — C1.
- [DONE] D2 InodeRegionWithdraw — C1, B4.
- [DONE] D3 InodeRegionLink — C1.
- [DONE] D4 IcacheEscrowTok — C2, B4, B6, A2.
- [DONE] D5 IcachePinwObl — C4.
- [DONE] D6 FsStateEraResB — C2 (leaf; nothing in 0d waits on it).

**Batch E (2)**
- [DONE] E1 IgetLic — D1, B1, C1, A3.
- [DONE] E2 IcacheEscrowDep — D4.

**Batch F (3)**
- F1 IcacheInvFrz — E1, D1, C4.
- F2 IcacheEscrowPool — D4, E1, C1, B6.
- F3 IcacheBoxAmb — D4, E2, C4.

**Batch G (4)**
- G1 IcacheInvStore — F1 (leaf).
- G2 IcacheBox — F2, F3, C5, B8.
- G3 EscrowDeposit — F2, C1, B2, B6, C4.
- G4 IcacheBootRegion — F2, C1, B2, C2, D4.

**Batch H (2)**
- H1 IcacheTable — G2, C3, C4.
- H2 IcacheCover — G2, B7.

**Batch I (1)**
- I1 IcacheBootTable — H1, G4, C5. It is consumed only by the deferred boot kits (FsCfgKits/FsCfgSnap).
  It may be deferred if the WpLockAt/SepThread/MemClaim analogues are not there. `icache_boot` is
  superseded by `icache_boot_at` (§5).

The critical path is A → B → C → D → E → F → G → H: FsStateLink/FsStateInode → InodeOwned →
FsStateEraRes → EscrowTok → EscrowDep/IgetLic → Pool/BoxAmb → Box → Table. The InodeRegion tail
(D1–D3), the IcacheInv §5b pair (F1, G1), D5 and D6 are off it.
Every Lean file keeps the Rocq file's header prose for its sections, plus its own deviations and
cleanups.

## 5. Gunk candidates (per file)

**CAUTION (batch B):** this list is NOT authoritative. B2 found entries marked dead that have live
consumers (`abs_tree`, `apath_at_tree` are used in FsAbs.v; `app_top_update` by InodeRegion.v and the
FsAbs*Fire files). Every agent must re-grep all of /shared/xv6rocq/iris (comment-stripped, incl.
Spec*/Proof*/FsAbs*) before dropping anything listed here.

Method: I traced reachability from every declaration in every OTHER /shared/xv6rocq/iris/*.v file,
with comments stripped and instances excluded. **"checked, 0 uses"** = no declaration anywhere in
the tree (defs, Spec, Proof, Link, syscall layer) reaches it, directly or transitively. Before
dropping, grep once more: an `Ltac` body or a `Hint` can hide a use.

- **IcacheRef** — checked, 0 uses: `cred_floor_0`, `ic_lent_stamps_canon`, `inode_claimed_elim`,
  `inode_ref_agree`, `inode_ref_at_intro`, `inode_ref_canon`, `inode_ref_gather_gen`,
  `inode_ref_gen_bare(_split)`, `inode_ref_genlo_bare(_gen,_split)`, `inode_ref_genlo_gen`,
  `inode_ref_short_genlo_gen`, `inode_ref_short_(genlo_)shr_gen_agree`, `inode_ref_short_shr_agree`,
  `inode_ref_shr_agree`, `inode_ref_tok` (the "old reading"), `inode_refb_{elim,intro,false_refp}`,
  `inode_refp_{canon,carve,gather,intro,spend}`, `inode_shr_agree`, `inode_shr_gen_bare(_split)`,
  `inode_shr_gen_pin_on_keep`, `inode_shr_genlo_bare_{gen,split}`, `inode_shr_split`,
  `iref_tok0(_tok)`, `live_frac0_{absorb,bump,fracc,full_excl(_frac),join,pin,split}`,
  `live_frac_{bound,bump,full_excl,halve,join,split}`, `live_fracc_{frac,halve,join}`,
  `live_gen_{bound,bump,halve}`. The six-way `_gen`/`_genlo`/`_bare`/`_short` family is the main
  multiplicity. The LIVE members are used by specs (`inode_shr_gen` in 9 files, `inode_shr_genlo`
  in 13, `inode_ref_genlo` in 5, `inode_refp` in 6), so keep those names. Header staleness:
  "IrefSlots imports FileInv" (it imports FdSlots now).
- **IcacheInv** — checked, 0 uses: the whole standalone liveness-pool cluster (`live_norm`,
  `live_frzn`, `live_slot`, `live_pool` and all `live_slot_*`/`live_pool_*`/`live_norm_*`/
  `live_frzn_*` lemmas, `live_whole_share_absurd`). A6.145 merged liveness into `pinw_slot`, and
  the file HEADER still describes the old pool (stale). Also the superseded `_step` family
  (`iref_alloc_step`, `iref_incr_step(_lv)`, `iref_dup_step(_genlo)`, `iref_close_step`,
  `iref_close_last_step`, `iref_close_last_frz_step`; the live ones are `_noarm`/`*_store_pinw_au`),
  `iref_dup_store_pinw_au`, `iref_cells`/`iref_cells_acc(_upd,_del)`, `islots_acc_upd`,
  `icM_wf_count_slots`, `ic_pos_succ_1_add`, `iref_frag_two_lookup`, `iref_set_word`,
  `iref_word_live`. Aliases, checked: `itable_body_pinw`/`itable_inv_pinw` = `itable_body`/
  `itable_inv` ("the _pinw names survive as aliases"), used only in IcacheInv/IcacheEscrow/
  IcachePinwObl (17 occurrences), so collapse them. `icfg_ieplo` is "superseded (kept allocated,
  unused)" and appears only in IcacheRefDefs.v/IcacheInv.v; 0d must not use it.
- **IcacheEscrow** — checked, 0 uses: `ic_bundle_{loaded,unloaded}_{intro,elim}`,
  `ic_dep_half(_gname,_intro)`, `ic_dep_own(_ident,_live,_of_shr)`, `ic_dep_res(_live)`,
  `ic_dep_lo_of_shr`, `ic_guard_deposit(_gen)`, `ic_hdr_dead_intro`, `ic_hdr_excl`,
  `ic_hdr_{ident,nlink}_acc`, `ic_ids_pin`, `ic_inode_leg_{ghost,owned,phi_at}`, `ic_loaded_shed`,
  `ic_mk_unloaded`, `ic_out_frz`, `ic_out_rd(_none)`, `ic_payload_arm(_frz,_decide_frz)`,
  `ic_payload_at(_pack_np)`, `ic_payload_{split,join,to_arm}`, `ic_rd_join`, `ic_rest_excl`,
  `ic_rest_raw_unloaded`, `ic_slp_dep_llb`, `ic_tok_excl`, `ic_tok_exclusive`, `ic_tok_fun_alloc`,
  `ic_word4_excl`, `ic_x_gen`, `ipool_cover_inum`, `ipool_id_lend`, `itable_rows_to_llb`.
  Several are the pre-R3 five-arm escrow. The HEADER (lines 1–150: PARKED/EMPTY/OUT/MID/HELD) is
  the superseded design: since R3.3 `ic_escrow := ic_box`, so port the box and keep the header as
  rationale only. "In this skeleton the record [ic_boxes] stands in…" is stale. Aliases, checked:
  `ic_escrow`/`ic_escrows` = `ic_box`/`ic_boxes_all` ("kept for the ~70 files"). `ic_escrow` is in
  43 files, `ic_escrows` in 68 (Spec/Proof/FsReady), `ic_box` in 2, `ic_boxes_all` in 8
  (ProofDirlink, SpecFileclose, …). Keep ONE name per pair (the `ic_escrow*` spelling) and record
  the mapping in the header. **Not** an alias: `ic_deposit` (the ghost-var half, used by
  SpecIlock/SpecIunlock/SpecCreate) and `ic_deposit2` (the box holder row, ProofIlock/Iunlock).
  Keep both. Unused section binder, checked: `bioslotG` (appears only in `Context` lines), so do
  not add a `[BioslotG]` binder. Lean includes instance variables in every theorem, so an unused
  binder is not free. `irefslotG` is used in §6 only.
- **IcacheHeld** — checked, 0 uses: `inode_held_{gather,refp,shed,short}`,
  `inode_shr_held_gen_{bound,forget}`, `inode_shr_held_split`. Also the `GONE`/shim note at 404.
- **IcacheCover** — checked, 0 uses: `ic_arm`, `ic_arm_cover(_close,_side,_view)`, `ic_cover_read`,
  `ic_escrow_is_inv`, `ic_np_read`, `ic_rd_arm_read`. That is 9 of 16 declarations: port only the
  reachable ones (the collection lemma the commit uses) and check what FsCollect*.v calls.
- **IcacheBoot** — checked, 0 uses: `dummy_reg_key`, `ic_dv_dummy`, `ic_id_forget`, `iref_cells_boot`,
  `icache_boot` (superseded by `icache_boot_at`, used by ProofMain/FsCfgKits/FsCfgSnap).
  **Keep** `ipool_alloc_all_free` even though nothing uses it: it is the witness that the boot
  premise is satisfiable (header, T17).
- **IgetLic** — checked, 0 uses: `iname_{linked,root,buf}_alloc`.
- **OffBox** — checked, 0 uses: `off_ref_stamps_mass_eq`, `off_rows_insert`, `off_rows_take`. The
  comment "SKELETON statements, proofs in lane (ii)" at 293 is stale (the header says PROVEN). Port
  the proven statements: three lemmas carry `STATEMENT CHANGE (L6 skeleton→proof)`.
- **OffGv / FileOffCell** — checked, 0 uses: `off_gv_update`, `off_permit`, `off_user_inv_permit`,
  `off_resident_intro`. The FileOffCell geometry duplicates Xv6/FileDefs.lean: reuse it (checked:
  same stride 40, base `ftable+24`, same field offsets).
- **EscrowDefs** — checked, 0 uses: `crp_elem_excl`. OPTION A is the LIVE design (the reordered
  iput's per-inum escrow). It is not a superseded variant.
- **InodeRegion (the deferred part)** — checked, 0 uses: `ireg_reg_app`, `ireg_top_retag_step`,
  `ireg_top_retag_armed_step`. **TxPin**: `tx_pin_join_q`, `tx_pin_split`. **FsStateLink**: 16
  (`link_auth_of_elem`, `link_auth_reps_le`, `link_auth_tok_list`, `link_family_alloc`,
  `link_full_elem_valid`, `link_full_split`, `link_toks_elem_add`, `link_toks_le_split`,
  `link_toks_list(_at)`, `link_toks_of_elem`, `link_toks_one`, `own_gather_list(_opt)`,
  `own_gather_map`, `tok_elem_list`). **AppInv**: `app_step_id`, `app_top_update_{same,step}`,
  `app_xfer_acc`, `app_xfer_raw_{pers_or_pure,pure,triv}`. **FsAbsDefs**: `abs_fsnode(_node_of)`,
  `abs_of_{dir_inv,is_Some,nlink}`, `abs_tree(_ent)`, `abs_view_lookup_{Some,is_Some}`,
  `apath_at_{app,arun,tree}`, `arow_at_of_{None,Some}`. (The `*_eq_dec`/`*_inhabited` are
  instances; keep them.) **FsStateEra**: 21, including `inode_owned_era_{blk_acc,era_node_ok,home,
  home_all,of_q,ok,q_blk_read,q_local,rec,rec_upd,retag,split,trunc}`, `ent_toks_era_*`,
  `era_node_ent`, `inode_ok_data_ext`, `inode_rd_era_bytes`.
- **Unverified — keep unless checked:** (a) the `appcfg` section binder in IcacheInv/IgetLic/
  IcacheEscrow/EscrowDeposit/IcacheBoot. It is used only through `ireg_inv`'s implicit argument,
  so follow whatever InodeRegionInv does. (b) Whether `ic_payload_np`/`ipool_shape_np` ("np") and
  their pinned twins can merge. (c) Unused `nib`/`logstart`/`cov` parameters on pool/escrow
  predicates. (d) The `kallocG`/`lockG` binders on IcacheRef §4/IcacheHeld: Rocq says they are the
  box's cameras, so they may vanish under CtxBoxQ. Check.

## 6. Pitfalls recorded in the Rocq comments (port the reasons into docstrings)

- **Live panics stay live.** `iget: no inodes` (it fires while holding itable.lock, paid by
  `n + 3 < 2^31` and the rank edge "itable" < "pr") and `ilock: no type`. Nothing in 0d may add an
  allocatedness premise that would refute them (survey §1d, T2).
- **REF-1 and `positiveR` has no zero**: a SHARE carries no count fragment and cannot become a
  reference. `ref < 1` guards read through the LIVENESS slice (`iref_live_load_au`), not a count.
  The canonical pairing (IcacheRef header: three fractions that are always the same number) is
  load-bearing: `inode_ref_carve`/`inode_ref_gather`, and iput's last close retires the slot "by
  arithmetic".
- **`iref_slot` is what proves `ref++` stays an `int`**: "false at 2^31-1 and no axiom may assert it"
  (IrefSlots/IcacheInv `islot`). Do not replace it with a bound premise.
- **IcacheEscrow "ONE DEVIATION FROM THE C3a BRIEF"**: splitting a reference's fraction also splits
  its count, so it is not an entailment. OUT holds a WHOLE `inode_ref`.
- **The two-parkers problem**: `ic_deposit`'s descriptor is what tells iunlock's parker from iput's.
  It is not bookkeeping (§14.8).
- **Count coupling (iclaim-ledger §2.2)**: the five `*_store_au` wrappers take `ireg_inv` and nest
  an `↑iregN` open INSIDE the `↑icacheN` one. Keep the mask order. `icnt_freeze_forces_one` is what
  retired one of IputFreeLocked's admits, so it must be proved, not assumed. EscrowDeposit's masks
  nest `iregN`, `escAN z`, `ipoolN`, `ftopN`, `appN` in a fixed order.
- **Namespaces must match Rocq**: `icacheN = nroot.@"icache"`, `ipoolN = "ipool"`,
  `icBoxN = "xv6icbox"`, `offBoxN = "xv6offbox"`, `escAN z = nroot.@"icescA".@z`,
  `foffN = "app"."foff"`, `appN = "app"`. The disjointness facts (`logN_iregN_disj`,
  `appN_sub_ftop`, …) depend on them.
- **`pool_pending` is NOT timeless** (`escA_inv` is an `inv`), so open that arm without the `>`
  strip. The corpse ledger is a `ghost_map` precisely because the off-lock deposit must locate its
  row by the element alone.
- **IgetLic's enumeration is closed**: every constructor must be refutable at an in-transition box
  (`iname_not_frozen`). `HeldL` carries `nlink ≠ 0`, and `BufL` carries `exc_sealed` and
  `ireg_boot` (boot-only). Do not add a constructor.
- **"r25 shapes"** (a tso-cutover review round): OffBox's names ride in `icfg` (`icfg_off`,
  `icfg_box`) so that OffBox can build BEFORE FileInvDefs. `ip->lock`'s payload carries the off
  rows. The itable payload takes its own `ξ` (the "sixth final shape"), and the three `itable_res2*`
  CtxMorph instances were built by `ctx_morph_solve`. In Lean the import-order reason still holds
  (FileInvDefs is not ported yet), so keep the placement. The CtxMorph instances become
  `infer_instance`. §6c's env-row transports live in IcacheEscrow "because EnvMorph imports
  FsReady", which is a Rocq import-order artefact: check whether Lean needs it.
- **OffGv's pinned class**: two `ghost_varG Σ Z` instances give "two paths to one inG, two
  propositions that print identically". In Lean, route every use through the `offGv` wrapper and
  its own class field.
- **IcacheBoot T17**: image-wf premises (`inode_ok`, `dir_ok`, `dir_dots_ix`, `dir_orphan_clean`,
  `dir_uniq` of mkfs inodes) are THREADED hypotheses, "never an axiom".
- **Key types**: InodeRegion(Defs).lean keys the region map by `Int` (the marker lives at a
  negative key). Rocq's inum-keyed `gset Z`/`gmap Z` in the pool, the corpse ledger and
  `region_inums` must agree with that choice at every meet point. State the key type in the header.
- **Stale headers**: IcacheInv's (the live pool), IcacheEscrow's (the five arms), and
  InodeRegionDefs/0c's claim that InodeRegion "uses nothing from" IcacheRef/EscrowDefs (false:
  see the Xv6/InodeRegion.lean header).

## 7. Report (per agent)

Report files with line counts and the last line of each build. Give every deviation from Rocq with
its reason, every cleanup in the form "item — uses checked — reason", every name reused from
landed Lean instead of ported, and any edit an existing file needs (exact old → new). A10 reports
the design note path and the list of Rocq statements it proposes to change.
