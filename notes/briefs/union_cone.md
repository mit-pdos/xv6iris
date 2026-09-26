# Union cone audit (U0-X): the real cone of `union_adequacy_closed`

Read-only audit, 2026-09-26. Rocq `/shared/xv6rocq` @ `1900b8a43` (DU1 pin; tree clean). Lean
`lean-v2` @ `184d4fb1f`, plus the untracked files the U0 agents were writing during the audit (marked
"in flight" where they matter). No Lean file or git state was touched.

## 0. Method, and what it can and cannot see

- **Build.** The GCP VM tree for `/shared/xv6rocq` (`/mnt/rocq/trees/_shared_xv6rocq`) was seeded
  from the built `_shared_xv6iris-3` tree (same lineage, 19 `.v` files behind the pin). The pinned
  tree was then synced, and `make UInitUnion.vo` was run in `iris/`. It recompiled 63 files, all green.
  Every `.glob` in the Require cone carries the MD5 of the pinned `.v`, so none is stale.
- **Three cones.**
  - The **Require cone** is coqdep-style.
  - The **file-level glob cone** follows the glob `R` records between files.
  - The **declaration-level cone** is the one this note uses.
    - It follows glob references from `UInitUnion.union_adequacy_closed`, declaration to declaration.
    - A reference is charged to the enclosing declaration by position.
    - Record constructors resolve to their record, and `Module`/`Module Type` references pull in the
      module's members.
    - A section variable counts only where it is named.
- **Blind spots.** A glob records no typeclass resolution, no Ltac use and no `Hint` use.
  - Every file reported below as not needed was checked by hand for `Instance`, `Existing Instance`,
    `Ltac`, `Hint`, `Canonical` and `Coercion`. None of them provides an implicit dependency, with one
    exception: the three DU9 decider files (§1.2), which are reached only through `Decision` instances.
  - The declaration-level walk also loses the kernel's functor chain (`Link*`/`Proof*`). The kernel is
    Lean-ported already, so this affects only the system-cone half. It does not affect the union-side
    files that this note classifies.
- **Scratch.** The scripts and intermediate data were in the session scratchpad and were not kept. The
  numbers here are the record. To re-derive them, redo the build and the glob walk above.

## 1. The real cone

### 1.1 Headline numbers

| measure | files | lines |
|---|---:|---:|
| Require cone of `UInitUnion` | 1,691 | 1,356,587 |
| … of which the Require cone of `SystemAdequacy` (Lean's system theorem) | 1,400 | 1,025,923 |
| **union-only Require cone** (the brief's "292 / 331,464"; the regex fix added `WpAuipc` to the system side) | **291** | **330,664** |
| file-level glob cone of `UInitUnion` (Require over-approximates by only **13 files / 5.5k** at file level) | 1,678 | 1,351,063 |
| system-cone files Lean never ported that the union needs (brief §1.4: the engine, the run layer, echo's old tier, the pipe queue; all reached) | 32 | 43,818 |
| **the union's work list** = union-only (291) + those 32 | **323** | **372,529** |
| … with ≥ 1 declaration reached from `union_adequacy_closed` | 304 | — |
| … **needed** after DU8 (§2), DU9 (the 3 deciders) and the not-needed files below | — | **≈ 342,100** |

**The 13 Require-only files (in the Require cone, not in the file-level glob cone).**

| group | files |
|---|---|
| system-side, used through Ltac or instances | FastLia 461, FastSetSolver 130, SetShrink 284, WpRvcBridge 249, HartMDecode 192, PtTreeMorph 55 |
| system-side, dead imports | HartPilot 551, InodeRef 41, WpSmodeLeafBase 37 |
| union-side, instance-only | **UnionDecU 2,092, PipesDecE 794, FileDiscDec 416**. UnionOut's ledger counter runs `decide (lm_disc U h)` against `UnionDecU.lm_disc_ulmG_dec`, so these are needed by instance. That is exactly DU9's target |
| union-side, a dead import | **EchoLinksBan 222** (imported by UInitBoot; nothing referenced) |

### 1.2 Union-side files that are NOT needed (no declaration reached)

15 files, **12,818 lines**. None has an instance, Ltac or hint that a reached declaration could use.

| file | lines | brief row | why it is unreached |
|---|---:|---|---|
| TreeView | 3,731 | U1-T | the tree application's view; the union reaches `TreeImg`'s `img_root_*` instead |
| AppTree | 2,676 | U1-T | `treeG` is not in `unionΣ`, and nothing reached uses the tree app |
| UkSeccVprintfS | 2,698 | P-printf | only `UkSeccFprintf.wp_ksecc_fprintf_s` uses it, and that is unreached (seccomp needs putc/vprintf/fprintf, no `%s`) |
| EchoLinksLine | 998 | U0-C | its 9 instances are `Timeless` on its own unreached predicates |
| UkShCat | 738 | sh-exec | the union's `cat` child goes through `UkShEcho`'s arm |
| StageRec | 430 | U0-C | its one `Existing Instance ck_cur_tl` re-exports another file's lemma |
| GenLinks / GenLinksGl | 254 / 103 | U0-C | — |
| EchoLinksBan | 222 | U0-C | dead import |
| TreeObs | 215 | U1-T | — |
| PipesLedPure | 210 | U0-3 | — |
| UEchoPipe | 185 | P-echo | — |
| FsFPin | 154 | U0-2 | — |
| UkShRedirGtk | 121 | DU8 shell | — |
| LineModelInst | 83 | U0-1 | — |

**Special case: RefParseBridge (729).** It is unreached AT THE PIN because the union still walks the
legacy parsers (§2). It becomes needed as soon as DU8 re-points them: Rocq's own plan (step 2 of
`claude-notes/projects/user-once.md` "RESUME HERE") puts the N-stage `ushq_bars → ref_parsepipe` bridge
in this file.

**Low-reach files worth porting partially.** The "reached / total" column in §1.3 shows these (most of
the rest of each file is corollary or tree-application material):

| file | lines | declarations reached / total |
|---|---:|---:|
| EchoOut | 4,130 | 69 / 256 |
| PipeDisc | 1,931 | 16 / 196 |
| EchoOutPure | 1,854 | 28 / 107 |
| ProgTreePipes | 1,381 | 23 / 107 |
| EchoLinks | 1,226 | 6 / 82 |
| UEchoOut | 991 | 4 / 31 |
| FileLinksLine | 738 | 8 / 92 |
| UnionDiscDec | 714 | 4 / 128 |
| FileOutPure | 703 | 1 / 55 |

### 1.3 Corrections to the brief

1. **ElfUser is not a sanity leaf** (brief §1.2 says it is). `UInitUnionBoot.union_Hinit_boot_at`
   reaches `ElfUser.init_elf` directly, and the Fs*Pin files, UShEcho/UShCat/UShGrep and the image
   entries reach the other ELF literals. U0-7's in-flight `Xv6/ElfUser.lean` covers them (§3).
2. **UexecCond is not entirely out of the cone.** One lemma is reached:
   `cond_entry_slot_pay`, via `UexecExecMint.uslot_mint_all` → `UInitFileLeaves.file_gen_mint`. Lean
   already has `uslotMint_all`.
3. **The sync gate is out, which confirms DU1.** `UkSync`, `UCodeSync` and `USyncKernel` have 0
   declarations reached.
4. **DU8's premise does not hold at the pin** (§2).

### 1.4 The work list, file by file

Columns:
- **decls reached/total**: declaration-level reach (definitions, lemmas, records, abbreviations and
  instances; local notations excluded).
- **note**: DU8/DU9 status, or not needed.
- **camera classes**: the ghost classes the file binds.
  - **Bold** = the union's own classes.
  - `rGS`/`rFix`/`rGen` = `riscvGS` / `riscv_fixedGS` / `riscvF_genGS`.
  - `uxSG`/`upSG` = `uexecSG` / `uprogSG`.
  - `gvZ`/`gvGset` = `ghost_varG Z` / `ghost_varG (gset gname)`.
  - The rest are the Rocq class names, shortened.

All layers: 372,529 lines; needed after the DU8 drops, the DU9 deciders and the not-needed files: 342,142.

#### L1 pure — 58 files, 43,711 lines (needed after DU8/DU9/dead: 39,892)

| file | lines | decls reached/total | note | camera classes |
|---|---:|---:|---|---|
| EchoDisc | 2,822 | 119/312 |  |  |
| EchoFsPure | 32 | 1/1 |  |  |
| EchoOutPure | 1,854 | 28/107 |  |  |
| ElfLoadable | 153 | 8/12 |  |  |
| ExecWords | 70 | 7/8 |  |  |
| FileClass | 183 | 15/20 |  |  |
| FileDisc | 3,337 | 168/406 |  |  |
| FileDiscDec | 416 | 0/40 | instance-only (Decision); DU9 replaces |  |
| FileFsPure | 90 | 6/6 |  |  |
| FileHooks | 528 | 22/54 |  |  |
| FileLineWit | 99 | 3/3 |  |  |
| FileName | 312 | 13/37 |  |  |
| FileOutPure | 703 | 1/55 |  |  |
| FileState | 245 | 13/27 |  |  |
| FsFPin | 154 | 0/12 | **NOT NEEDED** (no decl reached) |  |
| GenOutHist | 659 | 15/31 |  |  |
| GenOutPure | 1,002 | 36/72 |  |  |
| GenOutWild | 515 | 12/16 |  |  |
| GrepFilt | 653 | 32/63 |  |  |
| GrepTree | 655 | 44/73 |  |  |
| LineBytes | 285 | 13/24 |  |  |
| LineModel | 1,192 | 50/87 |  |  |
| LineModelInst | 83 | 0/6 | **NOT NEEDED** (no decl reached) |  |
| LineModelLinks | 1,653 | 126/139 |  |  |
| LineWords | 1,762 | 134/199 |  |  |
| PipeBothNPure | 1,123 | 98/124 |  |  |
| PipeDisc | 1,931 | 16/196 |  |  |
| PipeOutPure | 493 | 3/41 |  |  |
| PipesCut | 924 | 37/72 |  |  |
| PipesDecE | 794 | 0/73 | instance-only (Decision); DU9 replaces |  |
| PipesDisc | 2,659 | 160/309 |  |  |
| PipesDiscDec | 668 | 22/56 |  |  |
| PipesFire | 1,317 | 104/122 |  |  |
| PipesLedPure | 210 | 0/14 | **NOT NEEDED** (no decl reached) |  |
| PipesPair | 87 | 5/17 |  |  |
| PipesUline | 317 | 18/28 |  |  |
| PipesView | 143 | 8/13 |  |  |
| ProgTree | 1,584 | 87/173 |  |  |
| ProgTreeFile | 47 | 3/3 |  |  |
| ProgTreePipes | 1,381 | 23/107 |  |  |
| RefParse | 413 | 32/45 | general walk |  |
| RefParseBridge | 729 | 0/40 | unreached at the pin; NEEDED once DU8 re-points (the N-stage bridge lands here) |  |
| RefParseSym | 1,354 | 104/114 | general walk |  |
| UNameBytes | 126 | 17/18 |  |  |
| UNamePath | 165 | 18/18 |  |  |
| UShLexRedir | 442 | 9/16 |  |  |
| UkProgAbi | 69 | 4/4 |  |  |
| UkShParseSym | 639 | 40/60 | DU8 trim |  |
| UkShPipeLex | 812 | 7/62 | DU8 trim |  |
| UkShPipesLex | 945 | 30/52 | DU8 trim |  |
| UkShRedirCut | 42 | 1/3 | general walk |  |
| UkShRedirLex | 70 | 4/6 | DU8 drop (after re-point) |  |
| UkShRedirLine | 388 | 16/18 |  |  |
| UkShWords | 586 | 33/39 |  |  |
| UnionDecU | 2,092 | 0/147 | instance-only (Decision); DU9 replaces |  |
| UnionDisc | 871 | 86/103 |  |  |
| UnionDiscDec | 714 | 4/128 |  |  |
| UnionView | 119 | 11/11 |  |  |

#### L2 run layer / echo old tier / pipe queue (Rocq system cone, unported) — 14 files, 22,851 lines (needed after DU8/DU9/dead: 22,851)

| file | lines | decls reached/total | note | camera classes |
|---|---:|---:|---|---|
| PipeNames | 78 | 15/22 |  |  |
| PipeQueue | 715 | 26/60 |  | pipeQ rGS |
| PipeReg | 260 | 8/15 |  | rGS xv6G |
| UCodeEcho | 1,815 | 161/175 |  | rGS |
| UEchoKernel | 502 | 14/24 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkAbi | 996 | 14/54 |  |  |
| UkEcho | 2,986 | 38/53 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkRun | 2,904 | 73/120 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkRunLeaf | 1,346 | 39/46 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkRunMem | 893 | 25/26 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkRunSys | 6,697 | 58/81 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UmodeAbi | 986 | 10/66 |  |  |
| UmodeArith | 486 | 42/43 |  |  |
| UserHeap | 2,187 | 103/124 |  | rGS ufd gvZ |

#### L2a ENGINE (UK_LEAVES; user lane) — 18 files, 20,967 lines (needed after DU8/DU9/dead: 20,967)

| file | lines | decls reached/total | note | camera classes |
|---|---:|---:|---|---|
| UkBranch | 367 | 10/10 |  | ctok rGS uxSG |
| UkLeaf | 1,608 | 35/43 |  | ctok rGS uxSG |
| UkLoad | 1,757 | 20/20 |  | ctok rGS uxSG ufd |
| UkLoadText | 922 | 10/10 |  | ctok rGS uxSG ufd |
| UkStep | 2,154 | 40/41 |  | ctok rGS uxSG ufd |
| UkStore | 2,132 | 24/24 |  | ctok rGS uxSG ufd |
| UmodeCap | 218 | 1/14 |  | rGS |
| UmodeFetch | 1,096 | 25/32 |  | rGS |
| UmodeFetchX | 640 | 10/10 |  | rGS |
| UmodeMem | 384 | 21/28 |  | rGS |
| UmodeRegs | 90 | 3/6 |  | rGS |
| UmodeText | 508 | 39/50 |  | rGS |
| WpUmodeBranch | 593 | 4/13 |  | rGS |
| WpUmodeFetch | 1,277 | 37/37 |  | rGS |
| WpUmodeLoad | 1,653 | 30/48 |  | rGS |
| WpUmodeStep | 2,467 | 66/86 |  | rGS |
| WpUmodeStore | 2,182 | 42/61 |  | rGS |
| WpUmodeTextLoad | 919 | 15/16 |  | rGS |

#### L3 claims/pins — 63 files, 51,503 lines (needed after DU8/DU9/dead: 42,874)

| file | lines | decls reached/total | note | camera classes |
|---|---:|---:|---|---|
| AppEcho | 1,709 | 33/88 |  | **echoOut** **unionLine** file rGS rFix uartG |
| AppFile | 1,589 | 98/135 |  | **echoOut** **fileApp** **unionLine** bio fds file iref pav rGS wch xv6G |
| AppFileCons | 447 | 19/25 |  | **echoOut** **fileApp** **unionLine** |
| AppTree | 2,676 | 0/148 | **NOT NEEDED** (no decl reached) | **tree** |
| EchoLinks | 1,226 | 6/82 |  | **echoOut** rGS rFix |
| EchoLinksBan | 222 | 0/6 | **NOT NEEDED** (no decl reached) | **echoOut** rGS |
| EchoLinksLine | 998 | 0/82 | **NOT NEEDED** (no decl reached) | **echoOut** rGS |
| EchoLinksPro | 439 | 1/27 |  | **echoOut** rGS |
| EchoOut | 4,130 | 69/256 |  | **echoOut** rGS rFix |
| ExecBundle | 280 | 5/6 |  | bio fds file iref pav rGS ufd wch xv6G |
| ExecEntry | 261 | 7/10 |  | ctok |
| FileDeltas | 1,383 | 84/112 |  |  |
| FileLinkGen | 379 | 17/40 |  | **echoOut** **fileApp** **fileOut** **unionLine** rGS |
| FileLinks | 102 | 1/3 |  | **echoOut** **fileApp** **fileOut** **unionLine** rGS rFix |
| FileLinksLine | 738 | 8/92 |  | **echoOut** **fileApp** **fileOut** **unionLine** rGS |
| FileOpen | 2,481 | 66/78 |  | **echoOut** **fileApp** **unionLine** bio fds file iref pav rGS wch xv6G |
| FileOut | 695 | 41/89 |  | **echoOut** **fileApp** **fileOut** **unionLine** |
| FileWrite | 718 | 21/24 |  | **echoOut** **fileApp** **unionLine** bio fds file iref pav rGS wch xv6G |
| FileWritePart | 135 | 2/2 |  | **echoOut** **fileApp** **unionLine** bio fds file iref pav rGS wch xv6G |
| FsAbsWritePart | 145 | 1/3 |  | bio fds file iref pav rGS wch xv6G |
| FsCatPin | 472 | 19/26 |  | diskImg fsLink fsTop |
| FsConsPin | 668 | 26/45 |  |  |
| FsDurSyscall | 665 | 4/29 |  | diskImg fsCrash fsLink fsTop lock |
| FsEchoPin | 471 | 19/26 |  | diskImg fsLink fsTop |
| FsGrepPin | 433 | 19/26 |  | diskImg fsLink fsTop |
| FsInitPin | 541 | 31/34 |  | fsLink fsTop |
| FsInitPinBoot | 388 | 5/16 |  | diskImg fsLink fsTop |
| FsSeccPin | 433 | 19/26 |  | diskImg fsLink fsTop |
| FsShPin | 476 | 19/26 |  | diskImg fsLink fsTop |
| GenLinks | 254 | 0/15 | **NOT NEEDED** (no decl reached) | **echoOut** rGS rFix |
| GenLinksGl | 103 | 0/5 | **NOT NEEDED** (no decl reached) | **echoOut** rGS rFix |
| GenLinksLine | 1,373 | 106/117 |  | **echoOut** rGS |
| GenOut | 1,858 | 24/37 |  | **echoOut** |
| LinkRec | 902 | 17/55 |  | **echoOut** rGS |
| PinnedExec | 575 | 4/8 |  | bio fds file iref pav rGS ufd wch xv6G |
| PinnedObs | 1,481 | 33/65 |  | bio fds file iref pav rGS wch xv6G |
| PinnedOpen | 536 | 7/11 |  | bio fds file iref pav rGS wch xv6G |
| PipeBothN | 957 | 45/54 |  | rGS rFix gv(A) |
| PipeOut | 777 | 41/90 |  | **echoOut** **pipeOut** |
| PipeOutN | 1,572 | 62/87 |  | **echoOut** **pipeOut** rGS rFix |
| PipeOutNEv | 1,012 | 17/38 |  | **echoOut** **pipeOut** |
| PipeOutW | 975 | 39/55 |  | **echoOut** **pipeOut** |
| PipeProto | 2,446 | 72/175 |  | **pipeProto** rGS xv6G |
| PipesLinksV | 402 | 4/22 |  | **echoOut** **pipeOut** rGS rFix |
| PipesOut | 269 | 7/14 |  | **echoOut** **pipeOut** |
| ReadRec | 297 | 2/9 |  | **echoOut** rGS uartG |
| StageRec | 430 | 0/26 | **NOT NEEDED** (no decl reached) | **echoOut** rGS |
| TreeImg | 439 | 5/31 |  | **tree** |
| TreeObs | 215 | 0/7 | **NOT NEEDED** (no decl reached) | **tree** bio fds file iref pav rGS wch xv6G |
| TreeView | 3,731 | 0/300 | **NOT NEEDED** (no decl reached) |  |
| UConsLine | 357 | 1/14 |  | **echoOut** ctok rGS uartG uxSG ufd upSG gvGset gvZ |
| UConsOpen | 681 | 30/34 |  | **echoOut** **unionLine** bio fds file iref pav rGS ufd wch xv6G gvZ |
| UImgWordDefs | 78 | 2/2 |  |  |
| UInitFd | 452 | 33/50 |  | ufd |
| UStrImg | 125 | 9/10 |  |  |
| UexecSecc | 881 | 60/69 |  | bio fds file iref pav rGS ufd wch xv6G |
| UnionLinkInst | 397 | 27/40 |  | **echoOut** **fileApp** **fileOut** **pipeOut** **unionLine** rGS xv6G |
| UnionLinkInstAt | 246 | 17/25 |  | **echoOut** **fileApp** **fileOut** **pipeOut** **unionLine** rGS xv6G |
| UnionLinks | 423 | 24/37 |  | **echoOut** **fileApp** **fileOut** **pipeOut** **unionLine** rGS rFix |
| UnionOut | 787 | 45/67 |  | **echoOut** **fileApp** **fileOut** **pipeOut** **unionLine** |
| UnionReadInst | 290 | 11/12 |  | **echoOut** **fileApp** **fileOut** **pipeOut** **unionLine** rGS rFix xv6G |
| UnionReadInstAt | 313 | 17/20 |  | **echoOut** **fileApp** **fileOut** **pipeOut** **unionLine** bio fds file iref pav rGS rFix ufd wch xv6G |
| UserConsole | 569 | 29/46 |  | rGS uartG xv6G |

#### code catalogs — 10 files, 46,994 lines (needed after DU8/DU9/dead: 46,994)

| file | lines | decls reached/total | note | camera classes |
|---|---:|---:|---|---|
| UCodeCat | 5,937 | 450/689 |  | rGS |
| UCodeGrep | 8,906 | 811/1049 |  | rGS |
| UCodeInit | 5,591 | 298/640 |  | rGS |
| UCodeSeccomp | 5,353 | 242/612 |  | rGS |
| UCodeShK | 9,024 | 749/1052 |  | rGS |
| UCodeShM | 2,823 | 228/294 |  | rGS |
| UCodeShP | 8,998 | 903/1032 |  | rGS |
| UkCatLit | 103 | 6/6 |  | rGS |
| UkInitLit | 103 | 6/6 |  | rGS |
| UkSeccLit | 156 | 11/17 |  | rGS |

#### L4 handlers — 29 files, 24,348 lines (needed after DU8/DU9/dead: 24,348)

| file | lines | decls reached/total | note | camera classes |
|---|---:|---:|---|---|
| ExecArgs | 766 | 16/32 |  | ctok rGS ufd gvZ |
| ExecRun | 1,012 | 10/35 |  | bio fds file iref pav rGS ufd wch xv6G gvZ |
| UkCatFEntries | 226 | 7/10 |  | **cifReg** **echoOut** **fileApp** **pipeOut** **pipeProto** **pipesN** **unionLine** bio fds file iref pav rGS rFix ufd upSG wch xv6G |
| UkCatFIface | 1,905 | 118/131 |  | **cifReg** **echoOut** **fileApp** **pipeOut** **pipeProto** **pipesN** **unionLine** bio fds file iref pav rGS rFix ufd upSG wch xv6G |
| UkCatFprintf | 1,361 | 15/28 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkConsOut | 1,122 | 34/59 |  | **echoOut** **fileApp** **fileOut** **unionLine** bio fds file iref pav rGS ufd upSG wch xv6G gvGset gvZ |
| UkFileDev | 1,366 | 43/53 |  | **echoOut** **fileApp** **unionLine** bio fds file iref pav rGS ufd upSG wch xv6G |
| UkFileIface | 1,862 | 104/114 |  | **echoOut** **fifReg** **fileApp** **fileOut** **unionLine** bio fds file iref pav rGS rFix ufd upSG wch xv6G |
| UkFileOpen | 1,604 | 19/31 |  | **echoOut** **fileApp** **unionLine** bio fds file iref pav rGS ufd upSG wch xv6G |
| UkFork | 1,471 | 31/39 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkFreeHandler | 368 | 13/13 |  | bio fds file iref pav rGS ufd upSG wch xv6G gvGset gvZ |
| UkHandler | 908 | 25/30 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkPipeDev | 1,179 | 32/48 |  | **pipeProto** bio fds file iref pav rGS ufd upSG wch xv6G gvGset gvZ |
| UkPipesEntries | 548 | 17/20 |  | **echoOut** **pipeOut** **pipeProto** **pipesN** **pnsReg** **unionLine** bio fds file iref pav rGS rFix ufd upSG wch xv6G |
| UkPipesIface | 2,631 | 151/170 |  | **echoOut** **pipeOut** **pipeProto** **pipesN** **pnsReg** **unionLine** bio fds file iref pav rGS rFix ufd upSG wch xv6G |
| UkReadCons | 452 | 9/10 |  | bio fds file iref pav rGS ufd upSG wch xv6G gvGset gvZ |
| UkReadFile | 605 | 4/15 |  | bio fds file iref pav rGS ufd upSG wch xv6G gvGset gvZ |
| UkReadPipe | 693 | 10/14 |  | bio fds file iref pav rGS ufd upSG wch xv6G gvGset gvZ |
| UkReadRows | 396 | 10/11 |  | bio fds file iref pav rGS ufd wch xv6G gvGset gvZ |
| UkRunBr | 173 | 3/5 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkRunExecRef | 395 | 5/8 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkRunSecc | 126 | 1/1 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkStub | 297 | 23/23 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkTree | 337 | 34/35 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkTreeRead | 631 | 1/13 |  | **tree** bio fds file iref pav rGS ufd wch xv6G gvZ |
| UkWriteClosed | 292 | 14/16 |  | bio fds file iref pav rGS ufd upSG wch xv6G gvGset gvZ |
| UkWriteFile | 536 | 2/13 |  | bio fds file iref pav rGS ufd wch xv6G gvGset gvZ |
| UkWriteLeaf | 587 | 12/21 |  | bio fds file iref pav rGS ufd wch xv6G gvGset gvZ |
| UkWritePipe | 499 | 2/10 |  | bio fds file iref pav rGS ufd wch xv6G gvGset gvZ |

#### L5 programs — 82 files, 132,254 lines (needed after DU8/DU9/dead: 114,315)

| file | lines | decls reached/total | note | camera classes |
|---|---:|---:|---|---|
| UEchoFile | 317 | 8/12 |  | **echoOut** **fileApp** **unionLine** bio fds file iref pav rGS ufd wch xv6G gvGset gvZ |
| UEchoOut | 991 | 4/31 |  | **echoOut** bio fds file iref pav rGS ufd upSG wch xv6G gvGset gvZ |
| UEchoPipe | 185 | 0/14 | **NOT NEEDED** (no decl reached) | **pipeProto** bio fds file iref pav rGS ufd upSG wch xv6G gvGset gvZ |
| UkCat | 1,322 | 23/69 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkCatCat | 2,074 | 26/41 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkCatMain | 1,965 | 37/46 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkCatPutc | 557 | 9/23 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkCatTree | 555 | 39/39 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkCatVprintf | 2,195 | 29/34 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkCatVprintfS | 2,712 | 39/43 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkGrepFprintf | 2,136 | 23/38 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkGrepLib | 1,794 | 71/73 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkGrepLoop | 2,324 | 101/104 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkGrepMain | 1,997 | 47/51 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkGrepMatch | 2,138 | 41/42 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkGrepPutc | 856 | 14/62 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkGrepTree | 267 | 11/11 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkGrepVprintf | 2,198 | 29/34 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkGrepVprintfS | 2,715 | 39/43 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkInit | 2,415 | 58/86 |  | ctok rGS uartG uxSG ufd upSG gvGset gvZ |
| UkInitMain | 2,967 | 36/49 |  | ctok rGS uartG uxSG ufd upSG gvGset gvZ |
| UkInitPrintf | 689 | 14/25 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkInitPutc | 542 | 9/23 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkInitVprintf | 2,065 | 28/33 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkSeccEntry | 203 | 4/4 |  | bio fds file iref pav rGS uartG ufd upSG wch xv6G gvGset gvZ |
| UkSeccFprintf | 1,363 | 14/28 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkSeccMain | 1,229 | 24/27 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkSeccPutc | 858 | 13/62 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkSeccVprintf | 2,198 | 29/34 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkSeccVprintfS | 2,698 | 0/43 | **NOT NEEDED** (no decl reached) | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkSh | 9,734 | 197/242 |  | ctok rGS uartG uxSG ufd upSG gvGset gvZ |
| UkShArgs | 3,056 | 53/61 | general walk | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShCat | 738 | 0/44 | **NOT NEEDED** (no decl reached) | ctok rGS uartG uxSG ufd upSG gvGset gvZ |
| UkShCatForkTwin | 143 | 6/6 |  | ctok rGS uartG uxSG ufd upSG gvGset gvZ |
| UkShCd | 405 | 4/40 |  | ctok rGS uartG uxSG ufd upSG gvGset gvZ |
| UkShDiag | 9,155 | 91/221 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShDiagAt | 197 | 4/4 |  | ctok rGS uartG uxSG ufd upSG gvGset gvZ |
| UkShEcho | 2,083 | 54/88 |  | ctok rGS uartG uxSG ufd upSG gvGset gvZ |
| UkShFork | 1,359 | 27/54 |  | ctok rGS uartG uxSG ufd upSG gvGset gvZ |
| UkShGettoken | 2,111 | 37/43 | general walk | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShLoop | 286 | 8/15 |  | ctok rGS uartG uxSG ufd upSG gvGset gvZ |
| UkShMain | 377 | 11/26 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShMalloc | 4,845 | 52/60 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShParse | 3,634 | 145/167 | DU8 trim | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShParseCmd | 3,469 | 48/59 | DU8 trim | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShParseExec | 2,467 | 40/46 | DU8 drop (after re-point) | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShParseLex | 2,354 | 65/79 | DU8 trim | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShParseRedir | 722 | 21/44 | DU8 drop (after re-point) | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShParseTok | 3,183 | 45/55 | DU8 trim | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShParser | 4,373 | 87/99 | general walk | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShPipe | 3,567 | 36/62 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShPipeCm | 3,320 | 32/59 | DU8 drop (after re-point) | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShPipeCmd | 715 | 17/25 | general walk | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShPipeEx | 260 | 10/21 | DU8 drop (after re-point) | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShPipeEx2 | 1,161 | 26/46 | DU8 drop (after re-point) | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShPipeForkTwin | 922 | 40/42 |  | ctok rGS uartG uxSG ufd upSG gvGset gvZ |
| UkShPipeNode | 201 | 8/52 | general walk | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShPipePaid | 402 | 8/10 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShPipeParse | 890 | 23/55 | DU8 drop (after re-point) | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShPipePex | 1,630 | 34/47 | DU8 drop (after re-point) | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShPipePr | 683 | 20/33 | DU8 drop (after re-point) | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShPipeRight | 400 | 17/20 | DU8 drop (after re-point) | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShPipeSeam | 204 | 1/17 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShPipeTok | 122 | 10/10 | DU8 drop (after re-point) | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShPipeWait | 160 | 4/4 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShPipesCmd | 584 | 24/26 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShPipesFork | 86 | 3/4 |  |  |
| UkShPipesParse | 338 | 13/14 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShPipesRound | 539 | 16/21 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShPipesSeam | 229 | 13/16 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShRedir | 1,023 | 16/26 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShRedirAns | 198 | 5/7 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShRedirBody | 831 | 25/36 |  | ctok rGS uartG uxSG ufd upSG gvGset gvZ |
| UkShRedirChild | 225 | 2/2 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShRedirCmd | 999 | 28/30 | general walk | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShRedirGtk | 121 | 0/10 | **NOT NEEDED** (no decl reached) | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShRedirPaid | 284 | 10/11 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShRedirPr | 2,542 | 7/43 | DU8 drop (after re-point) | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShRedirSeam | 763 | 15/26 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShRedirs | 2,136 | 41/52 | general walk | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShRun | 3,896 | 62/102 |  | ctok rGS uxSG ufd upSG gvGset gvZ |
| UkShSeam | 1,607 | 51/60 | general walk | ctok rGS uxSG ufd upSG gvGset gvZ |

#### L6 rounds/init — 38 files, 27,212 lines (needed after DU8/DU9/dead: 27,212)

| file | lines | decls reached/total | note | camera classes |
|---|---:|---:|---|---|
| UInitArgv | 81 | 4/6 |  | rGS |
| UInitBanner | 525 | 21/44 |  | **echoOut** bio fds file iref pav rGS ufd upSG wch xv6G gvGset gvZ |
| UInitBoot | 376 | 7/7 |  | **echoOut** **unionLine** bio fds file iref pav rGS uartG ufd wch xv6G gvZ |
| UInitCons | 1,318 | 37/68 |  | **echoOut** **unionLine** bio fds file iref pav rGS ufd wch xv6G |
| UInitConsFile | 644 | 21/22 |  | **echoOut** **fileApp** **unionLine** bio fds file iref pav rGS ufd wch xv6G gvZ |
| UInitConsK | 989 | 23/29 |  | **echoOut** **unionLine** bio fds file iref pav rGS ufd wch xv6G gvZ |
| UInitDiag | 405 | 14/34 |  | **echoOut** bio fds file iref pav rGS ufd upSG wch xv6G gvGset gvZ |
| UInitFileLeaves | 350 | 14/15 |  | **echoOut** **fileApp** **fileOut** **unionLine** bio fds file iref pav rGS rFix uartG ufd upSG wch xv6G gvGset gvZ |
| UInitKernel | 790 | 15/15 |  | ctok rGS uartG uxSG ufd upSG gvGset gvZ |
| UInitSh | 1,652 | 41/53 |  | **echoOut** bio fds file iref pav rGS uartG ufd wch xv6G gvZ |
| UShCat | 877 | 19/33 |  | bio fds file iref pav rGS uartG ufd upSG wch xv6G gvGset gvZ |
| UShCatFStage | 458 | 26/29 |  | **cifReg** **echoOut** **fileApp** **pipeOut** **pipeProto** **pipesN** **pnsReg** **unionLine** bio fds file iref pav rGS rFix uartG ufd wch xv6G gvZ |
| UShCatPay | 461 | 6/18 |  | bio fds file iref pav rGS uartG ufd upSG wch xv6G gvGset gvZ |
| UShConsK | 533 | 14/18 |  | **echoOut** **unionLine** bio fds file iref pav rGS ufd wch xv6G gvZ |
| UShEcho | 1,367 | 45/75 |  | bio fds file iref pav rGS uartG ufd wch xv6G gvGset gvZ |
| UShEchoOut | 152 | 3/3 |  |  |
| UShEchoPipePay | 266 | 3/8 |  | **pipeProto** bio fds file iref pav rGS uartG ufd upSG wch xv6G gvGset gvZ |
| UShExecPin | 513 | 41/45 |  | bio fds file iref pav rGS ufd wch xv6G gvZ |
| UShFileRedir | 458 | 11/11 |  | **echoOut** **fifReg** **fileApp** **fileOut** **unionLine** bio fds file iref pav rGS uartG ufd wch xv6G |
| UShGeom | 874 | 24/25 |  |  |
| UShGrep | 1,080 | 33/38 |  | bio fds file iref pav rGS uartG ufd upSG wch xv6G gvGset gvZ |
| UShKernel | 1,193 | 21/24 |  | ctok rGS uartG uxSG ufd upSG gvGset gvZ |
| UShLine | 1,595 | 27/58 |  | **echoOut** bio fds file iref pav rGS ufd wch xv6G gvGset gvZ |
| UShLineHold | 102 | 1/4 |  | **echoOut** bio fds file iref pav rGS ufd wch xv6G gvGset gvZ |
| UShOut | 457 | 10/28 |  | **echoOut** bio fds file iref pav rGS uartG ufd upSG wch xv6G gvGset gvZ |
| UShPanic | 964 | 31/38 |  | **echoOut** bio fds file iref pav rGS ufd upSG wch xv6G gvGset gvZ |
| UShPanicHold | 187 | 1/8 |  | **echoOut** bio fds file iref pav rGS ufd upSG wch xv6G gvGset gvZ |
| UShPipeCall | 281 | 6/7 |  | bio fds file iref pav rGS ufd upSG wch xv6G gvGset gvZ |
| UShPipeLeaves | 434 | 13/13 |  | **echoOut** **pipeOut** **pipeProto** bio fds file iref pav rGS uartG ufd upSG wch xv6G gvGset gvZ |
| UShPipesDefs | 743 | 67/94 |  | **echoOut** **pipeOut** **pipeProto** **pipesN** **pnsReg** **unionLine** bio fds file iref pav rGS ufd wch xv6G |
| UShPipesNode | 1,125 | 83/88 |  | **echoOut** **pipeOut** **pipeProto** **pipesN** **pnsReg** **unionLine** bio fds file iref pav rGS rFix uartG ufd wch xv6G gvZ |
| UShPipesStage | 805 | 38/43 |  | **echoOut** **pipeOut** **pipeProto** **pipesN** **pnsReg** **unionLine** bio fds file iref pav rGS rFix uartG ufd wch xv6G gvZ |
| UShSecc | 781 | 17/24 |  |  |
| UShUPipes | 906 | 46/49 |  | **cifReg** **echoOut** **fifReg** **fileApp** **fileOut** **pipeOut** **pipeProto** **pipesN** **pnsReg** **unionLine** bio fds file iref pav rGS rFix uartG ufd wch xv6G |
| UShURound | 1,571 | 72/76 |  | **echoOut** **fifReg** **fileApp** **fileOut** **pipeOut** **unionLine** bio fds file iref pav rGS rFix uartG ufd wch xv6G |
| UShURoundDefs | 927 | 78/88 |  | **echoOut** **fileApp** **fileOut** **pipeOut** **unionLine** bio fds file iref pav rGS rFix uartG ufd wch xv6G |
| UShURoundLaws | 879 | 48/50 |  | **echoOut** **fileApp** **fileOut** **pipeOut** **pipesN** **unionLine** bio fds file iref pav rGS rFix uartG ufd wch xv6G |
| UShURoundShapes | 93 | 4/4 |  | **echoOut** **fileApp** **fileOut** **pipeOut** **pipesN** **unionLine** rGS |

#### L7 top — 7 files, 2,689 lines (needed after DU8/DU9/dead: 2,689)

| file | lines | decls reached/total | note | camera classes |
|---|---:|---:|---|---|
| App | 669 | 6/19 |  | bio bioslotGpreS fds fdslotGpreS file fileGpreS inv iref irefslotGpreS pav pavGpreS rGen rGS riscvGpreS rFix ufd wch wchGpreS xv6G |
| AppUnionRec | 410 | 17/30 |  | **echoOut** **fileApp** **fileOut** **pipeOut** **unionLine** bio bioslotGpreS fds fdslotGpreS file fileGpreS iref irefslotGpreS pav pavGpreS rGen rGS riscvGpreS rFix uartG ufd wch wchGpreS xv6G |
| UInitUnion | 102 | 2/2 |  | **cifReg** **echoOut** **fifReg** **fileApp** **fileOut** **pipeOut** **pipeProto** **pipesN** **pnsReg** **unionLine** bioslotGpreS fdslotGpreS fileGpreS irefslotGpreS pavGpreS riscvGpreS ufd wchGpreS xv6G |
| UInitUnionBoot | 429 | 2/2 |  | **cifReg** **echoOut** **fifReg** **fileApp** **fileOut** **pipeOut** **pipeProto** **pipesN** **pnsReg** **unionLine** bio fds file iref pav rGS rFix ufd wch xv6G |
| UInitUnionCC | 575 | 20/23 |  | **echoOut** **fileApp** **fileOut** **pipeOut** **pipesN** **unionLine** bio fds file iref pav rGS rFix uartG ufd wch xv6G |
| UUnionBootAdequacy | 191 | 5/7 |  | **echoOut** **fileApp** **fileOut** **pipeOut** **unionLine** bio bioslotGpreS fds fdslotGpreS file fileGpreS iref irefslotGpreS pav pavGpreS rGen rGS riscvGpreS rFix ufd wch wchGpreS xv6G |
| UnionOutPure | 313 | 4/18 |  |  |
## 2. DU8: the per-shape parser walks

**Finding: at the pin the walks are NOT corollary-only. The union still goes through them.** Rocq's
integration branch kept upstream's full shells: `user-once.md` "RESUME HERE" says the N-stage layer
`UkShPipes{Lex,Parse,Cmd,Seam,Round}` "is an induction stacked on the one-bar shells". Re-pointing
that layer at the general walk is Rocq's own step 2, and deleting the shells is step 3. Neither has
landed. Declaration-level reachability shows two live routes into the shells:

- **The exec child.** The path is
  `union_adequacy_closed → union_Hinit_boot_at → UShUPipes.sh_round_holds_union_closed →
  UShURound.uHchild_cat → UkShEcho.wp_kshm_child_x_holds → UkShParseCmd.wp_kshp_parser → parsecmd →
  parseline → parsepipe → UkShParseExec.wp_kshp_parseexec → UkShParseRedir.wp_kshp_parseredirs`,
  plus `UkShParseTok.wp_kshp_gettoken`. `UkShEcho.v:1604` and `:1740` still `iApply
  UkShParseCmd.wp_kshp_parser`, even though `UkShSeam.wp_ref_child_exec` (the general child) exists.
- **The N-stage pipes.** The path is
  `UShUPipes.upipes_child_law_echo → UkShPipesRound.wp_kshm_child_pipes_g →
  UkShPipesCmd.wp_kshp_parsecmd_pipes`. From there:
  - `UkShPipeCm.wp_kshp_{parsecmd,parseline,parsepipe}_bar_g`;
  - `UkShPipesParse.wp_kshp_parsepipe_bars`, which goes on to `UkShPipePex.wp_kshp_parseexec_barw` →
    `UkShPipeEx2` / `UkShPipePr` / `UkShPipeEx` / `UkShPipeTok`, and to `UkShPipeRight.ushq_shift` /
    `wp_kshp_parsepipe_tail`;
  - `UkShPipesCmd.wp_kshp_nulterminate_pipes`, which goes on to `UkShPipeParse` and
    `UkShParseCmd.wp_kshp_nulterminate`;
  - two lemmas of `UkShRedirPr` (`ushs_peek_res_nsym`, `wp_kshp_frame_pro_at`).

**Simulation of DU8.** The simulation cut every edge into the shells and gave each cut consumer an
edge to `UkShSeam.wp_ref_child_{exec,pipe,redir}` instead. The cone was then recomputed.

**11 consumer declarations in 3 files would have to be re-proved:**

| file | declarations |
|---|---|
| `UkShEcho` | `wp_kshm_child_x_holds`, `wp_kshm_child_x_v_holds` |
| `UkShPipesCmd` | `wp_kshp_parsecmd_pipes`, `wp_kshp_parseline_pipes`, `wp_kshp_nulterminate_pipes`, `ushp_pipe_node`, `ushq_tree_pipe_node` |
| `UkShPipesParse` | `wp_kshp_parsepipe_bars`, `ushq_pex_left_at_holds`, `ushq_tree_pipe`, `ushp_pipe_node` |

The `ushp_pipe_node` references go to `UkShPipeParse`'s duplicate of `UkShPipeNode`'s predicate: a
re-home, not a proof.

**These 12 files, 14,267 lines, then leave the cone entirely:**

| file | lines |
|---|---:|
| UkShPipeCm | 3,320 |
| UkShRedirPr | 2,542 |
| UkShParseExec | 2,467 |
| UkShPipePex | 1,630 |
| UkShPipeEx2 | 1,161 |
| UkShPipeParse | 890 |
| UkShParseRedir | 722 |
| UkShPipePr | 683 |
| UkShPipeRight | 400 |
| UkShPipeEx | 260 |
| UkShPipeTok | 122 |
| UkShRedirLex | 70 |

`UkShRedirGtk` (121) is unreached even today. `UkShRedirEx` is not in the Require cone at all.

**Kept files lose only their walk lemmas.** The general walk needs the rest (count = declarations
needed after the re-point):

| file | declarations | dropped |
|---|---:|---|
| UkShParseCmd | 17 → 12 | `wp_kshp_parser`/`parsecmd`/`parseline`/`parsepipe`/`nulterminate` (keep `ushp_ext`, `ushp_nulfold`, `ushp_setb`, `wp_kshp_nul_{loop,fin}` …) |
| UkShParseTok | 21 → 16 | `wp_kshp_gettoken`, `wp_kshp_gtk_disp`, `ushp_gettok_{end,fin,res}` |
| UkShParseLex | 36 → 27 | the nine `*_sym` lemmas |
| UkShParse | 135 → 129 | — |
| UkShParseSym | 40 → 37 | — |
| UkShPipeLex | 7 → 3 | — |
| UkShPipesLex | 30 → 23 | the `*_barw` lemmas |

**What this means for the ruling.** "Port only the general walks" is sound as a TARGET: the general
child lemmas exist (`UkShSeam.wp_ref_child_exec/_redir/_pipe`), and `UkShParser.wp_ref_parser` is
closed. But it means Lean does Rocq's unlanded step 2 first. That step is:
1. the exec arm at `wp_ref_child_exec`. Its bridge is landed: `RefParseBridge.ref_parsecmd_nosym`
   takes `ushp_no_symbols ∧ ushp_tokens` to `ref_parsecmd … = Some (UshpExec toks)`, so this is
   re-wiring, not new math;
2. the N-stage bridge `ushq_bars len f c a rest → ref_parsepipe … = Some (ushq_ptree a rest, fin)`,
   with `ushq_nulfolds = ushp_zero_at (ref_nulcut …)` and the room arithmetic `48 + 6·length rest` vs
   `ushp_pp_room` (plus A2e's two-word slack), proved by induction on the bars.

Item 2 has **no Rocq proof yet**. Only the ONE-bar bridge `RefParseBridge.ref_parsecmd_pipe` is
landed. It is ~11 declarations' worth of re-proof, against 14.3k lines of
per-shape walks.
- **Recommended: take DU8 with that re-point** and record it as a deviation in `UkShEcho`'s and
  `UkShPipes*`'s Lean headers. Re-survey at the U1→U2 boundary: if Rocq lands step 2 first, port its
  bridge verbatim.
- **The fallback** is to port the 12 shells as they are (14.3k Rocq lines, about 8k in Lean).
- This refines, and does not reverse, the user's DU8 ruling ("general parser walk only (audit
  first)"). The coordinator should confirm that the re-point is in scope for **sh-parse** / **sh-exec**.

## 3. Rocq→Lean name table for the kernel boundary (brief §3.2)

**What counts.** The table takes every Rocq declaration that meets three conditions:
- it is defined in a file of the SYSTEM cone;
- it is not one of the 32 unported engine/run/echo/pipe-queue files;
- it is referenced by a reached declaration of a union-side file, excluding the 18 engine files that
  sit behind UK_LEAVES.

That comes to **893 names in 117 Rocq files**. Each name was matched against the Lean declarations in
`Xv6/` and `MachCSL/` in this order: exact name, then the snake→camel spelling, then a match ignoring
underscores and case. For each name that still had no match, the Lean sources were grepped for the
Rocq name in backticks: headers and docstrings record renames and deliberate non-ports that way.

| class | names | present in Lean | mentioned in Lean (renamed / absorbed / "not ported" / in flight) | **missing** |
|---|---:|---:|---:|---:|
| 3.A kernel boundary | 814 | 539 | 45 + 51 (ElfUser, in flight) | **179** |
| 3.B engine-internal, read by the run layer | 15 | 1 | 2 | 12 |
| 3.C representation-level (Sail/bitvector/regfile helpers) | 64 | 11 | 10 | 43 |

**§3.2's rows, resolved.** "missing" means no Lean declaration by any spelling. "Lean mentions" means
a Lean header documents what became of the name.

| §3.2 row | present (Lean spelling) | missing → owner |
|---|---|---|
| **UexecRet / UexecSG / UexecSlot / UexecExecInst / UexecExecMint / InitBoot** | UexecRet 42 of 48 (`uvb`, `ukc`, `uslot*`, `uexecRet_ecall`, `tfOf_num`, `uwaitAns_of_pid`, …); UexecSlot 6 of 10 (`Uvis`, `tfResumeGpr_*`); UexecExecInst 9 of 13 (`Xfam`, …); UexecExecMint `uslotMint_all`; InitBoot 3 of 3; UexecSG 4 of 4 | `tf_of_arg0/1/2`, `uvis_of_run_fd`, `uvis_of_run_cwd`, `uwait_ans_pid_m_forget` → **U0-6/K5**. `secc_all` (ProcDefs + UexecSlot), `uvis_num`, `uvis_num_full0`, `usys_eff_secc_all` → **K3/bump** (the brief's `uvis_secc` is spelled `uvis_num` + `secc_all` at the pin). `udepw_law_of_sup_{read,write,close}`, `udepw_law_of_sup`, `udepw_cl_of_reg_close`, `udep_free` → **K4** (UexecExecMint's header marks them NOT PORTED). `srow_reg_of_pipe_reg`, `spost_at_pipe_elim` → **K4/PQ**. `xfam_exec`, `exec_sbundle` are absorbed (header: `xfam_pt`, `exec_sbundle` cited) — check at U1-P |
| **UsysMemOk rows** | 29 of 38 (`usysMemOk_quiet/_lazy/_execRow/_waitNull`, `usysFdOk_quiet`, `usysCwdOk_quiet`, …) | `USYS_seccomp`, `usys_secc_ok(_quiet)`, `usys_eff` → **K3/bump**. `usys_gen_ok_quiet`, `usys_ch_ok_quiet`, `usys_fd_ok_pipe_neg1`, `usys_mem_ok_read_ret` → **U1-R/K5**. `usys_read_ret` is in SyscallArmsFdDefs's docstring (read's answer row) — reuse it |
| **SpecSyscall / SyscallArms*** | nothing reaches them directly from the union; they are read through UexecRet/UsysMemOk | — |
| **pipe specs / PipeQueue** | none (Lean `PipeNames` has no queue fields) | the whole §3.D vocabulary → **K2 (PQ-a)**; `fileclose_cpay(s)` → **K4** (SyscallArmsFdDefs / SyscallArmsExit headers say "no Lean counterpart") |
| **console (ConsLog, ConsoleInv, WpUart, AppInv, RiscvPtsto)** | ConsLog 13 of 14, ConsoleInv 14 of 16, WpUart 9 of 13 (`outLink_mono`, `uartObsPermit_ledger`, …), AppInv 9 of 12, RiscvPtsto 4 of 13 (`AppIface`, `riscv_rx_tag`→MachCSL `rxTag` family, `riscv_cons_res`→`consRes*`, `riscvGS`→`MachGS`) | **K3:** `wild_ev`, `cons_placed`, `cons_swallow_placed`, `cons_licence_at`, `cons_licence_at_of_wild`, `cons_read_pay_triv_at`, `out_link_of_licence_at`, `app_rdcred`, `app_rdcred_of_rdwild`, `app_rdcred_of_sup`, `riscv_wild`, `riscv_rdwild`. **Union lane:** `wp_triv` (a trivial WP wrapper), `app_taint` (UsertrapKexit's header: no Lean counterpart) |
| **UserFd** | 30 of 54 (`ufdOwn_*`, `ufdAuth_len`, `ufd`, `ufdShut`, …) | **K3 / U1-T**, the whole-table view: `ustd_at`, `ustd_ok`, `ush_view_ok` and their 17 lemmas (`ustd_at_ustd`, `ustd_ok_ustd`, `ush_view_ok_{open,dup,tab,fdt0}`, `ustd_ok_taint`, …), `utab`, `utab_agree`, `ualloc_v(_std,_hi)`, `ufd_{own_agree,own_ne_lowest,alloc_least,alloc_std}_at`, `tab_le_refl`. `ufdG` is folded into `FileG.gmUfdG` (UserFd.lean header) |
| **FdSlots** | 11 of 22 (`fdLeastClosed_{free,lt,below}` in UsysMemOk; `fd_lowest_closed_*` are documented there) | `fdst_nopipe(_closed)`, `fdv_nopipe(_lookup,_closed)`, `fd_least_closed_unique`, `fd_lowest_closed_app` → **U0-6/U1-R** (read by UkRun/UkRunSys); `fdslotGpreS` → §4 |
| **FsAbs / SysOpen** | FsAbsDefs 23 of 23, FsAbsDelta 15 of 15, FsAbsEra 10 of 11, FsAbsCreateFire 11 of 11, SysOpenDefs 14 of 27, SpecSysOpen 6 of 14, FsAbsWriteFire 1 of 7, FsAbsReadFire 2 of 5 | **K5:** all of **FsAbsCreateNm** (10: `acre_commit_at(_gen)_nm(+_mono,_cur_mono)`, `npar_nm(_elim)`, `nlast_elem`, `aunarm_commit_at_nd`, `aunarm_of_arm_nd`, `cre_child_unfired_nd`); the SysOpenDefs trunc family (13: `open_trunc_at`, `trunc_{term,tie}_{arg,at}`, `trunc_term_at_of_arg`, `trunc_permit_{of,ex}`, `atrunc_of_permit`, `atrunc_commit_i(_of_at)`, `atrunc_commit_at_unit_pers`, `cre_ft_kept`); SpecSysOpen (8: `cur_kept`, `cre_permit(_ex)`, `cre_trunc_kept(_ex)`, `cre_fail_kept`, `plain_cur_of_kept`, `plain_trunc_kept_forget`); `awrite_{chain,part,full}_adv(+_0,_S,_mono)`, `aread_commit_adv`, `aread_in_om`, `read_arms_mapped`; FsAbs `astate_q_intro`, `astate_of_q`; FsAbsEra `elend_aents` (DEFERRED in its header); SysMknodDefs `npar_cur(_elim)`; SysWriteDefs `wchunk_at` (FsAbsWriteFire header: "NOT YET PORTED … RELAY 3"), `wchunks_one` |
| **misc** | UserCwd 4 of 4 (in flight: `Xv6/UserCwd.lean`); ChildTok 12 of 12 (`childTok_pid`, `exitTok_pid`, …); UserChildren 12 of 12 (`uchAny_of`); ObsTrace 18 of 22 (`cyclesOf_io`, `obsBoots_app`, `openSeg_io`, …); KexecDefs 11 of 11 (`kxcSp_range`, `kxcSpFinal_*`); KexecBuilt 10 of 11 (`kexecSzAfter_*`) | ObsTrace `obs_ins(_app,_in)`, `open_seg_prefix_of_boots` → **K5**. KexecBuilt `kxc_sp_mono` (named in KexecCParts's header as a local; re-export it). **OffGv `off_link`, `off_link_of`, `off_link_taint` → K5.** **FsImgCheck** 4 of 32: `fname_{sh,echo,cat,init,grep,seccomp,sync}`, `fsimg_{sh,echo,cat,init,grep,seccomp}_{at,path,type}`, `fsimg_byte`, `fsimg_root_{data,nrec}` → **K5 after the bump** (the fs.img literal). ElfUser → **U0-7, in flight** |

Other kernel-side gaps the table turned up that §3.2 did not list:
- **UserPerm / UserPtTree / ProcPtOwn / UptTree** page-table lemmas, read only by `UserHeap`/`UkRun`/
  `UkRunSys` (so owned by **U0-6**): `live_pages(_mem,_bound)`, `live_set`, `lazy_free_wmapped`,
  `pte_vu_of_valid_u`, `proc_pt_wf(_uleaf_wf)`, `uleaf_wf_lt`, `usz_ok_live`, `perm_of_X`,
  `pgroundup_{ge,mono}`, `uva_{w,r}mapped_page`, `umem_wr(_step,_ext)`, `umem_grow_id`,
  `umem_write_lookup_{in,out}`, `tf_vpn_unsigned`, `svpn_of_unsigned_gen`. Several have Lean forms
  documented under other names:
  - `umem_write_lookup_*` = `KexecBuilt.umemGet_write_*`;
  - `umem_grow_id` = SyscallArmsSbrk's lazy-view lemma;
  - `proc_pt_wf` = `procPtAt`'s `uptWf`;
  - `live_pages` = UPtDefs's fill lemma.

  Reuse these. Do not re-port them.
- **SpecCopyin** `uimg_word_at` (Lean: SpecFetchaddr's `bytesToWord (umemRead …)`), `ubytes_at_inj`.
- **SpecSysExec** `exec_path_of(_uniq)` (Lean: `ArgPath.argPathOf`, which SpecSysExec's header
  documents).
- **SpecSysRead** `sys_rw_count(_lt)` (Lean: `SpecArgfd.argZ`).
- **SpecFilewrite** `wr_tb`, `filewrite_in_held` (FsAbsInvFire's header: Lean's inode arm has no
  held/parked split).
- **UserOff** `foff_pub(_of_held)`.
- **FsDurImg** `dir_view_agree`, `img_node_file_byte` (FsDurImgView's header: "NOT re-ported").
- **PathElems** `pe_skip_app_ns`.
- **DevModel** (`dev_state`, `uart_loopback`, `uart_acc`, `uart_tx_pop`, `uart_rx_push`). AppLaws.lean,
  in flight, maps them to `Uart.txPop`/`Uart.recv`/`cresAt`. `dev_state` ≈ MachCSL `Dev/Fabric.lean` `DevStates`.
- **FsImg** `T_FILE_z` / `FS_MAXFILE` = `Xv6.T_FILE` / `Xv6.MAXFILE` (FsStateInode's header).
- **LogDefs** `fs_home_set` = `fsHomeList`.
- **FsImgDisk** `fsimg_dk` = `fsImgDisk`.

**3.B / 3.C** belong to the engine and to the representation layer. They are read by the run layer
(UkRun*, UserHeap, UmodeAbi, UkAbi):
- `Du_r`/`Du_w`/`Du_gpr_of_Z(_r)`/`Du_{r,w}_nPC`/`dstateU`/`D_u`/`goodmb_execute_*`/`u_gm_*`/
  `decode_state_bridge`. These belong in UK_LEAVES' statement vocabulary; `SpecUkLeaves.lean`, in
  flight, already names `dstateU`/`D_u`.
- the bitvector/Sail lemmas: RiscvExtras 23, VcGen 3, UserBits 3, RiscvModelBytes 3, InstrBytes,
  KstackArith, `RegFile.upd_{eq,ne}`, `WpGpr.gpr_of_Z`, WpMmodeLeafBase's compressed-instruction
  decoders. Port them locally (UmodeArith, in flight, already has `usext6_12_64` for Rocq
  `sext6_12_64`).

### 3.D The pipe-queue vocabulary the union reads (Rocq PipeNames / PipeQueue / PipeReg; none in Lean)

This is K2 (PQ-a) and K4 (PQ-b). Readers include kernel files (SpecFileread/Filewrite/Fileclose,
FsAbsInvFire, FileInvDefs, UexecExecInst/Mint) and union files (PipeProto, UexecSecc, UkPipeDev,
UkPipesIface, UkReadPipe, UkWritePipe, UShPipeCall, UShPipesNode). The exact list:

| Rocq file | names |
|---|---|
| PipeNames | `pipe_names`, `pipe_st`, `pst0`, `pst_{close,empty,eof,next,read,write}`, `pst_{close,read,write}_{rp,ws}` |
| PipeQueue | `pipe_qauth`, `pipe_qfrag`, `pipe_queue_{agree,update}`, `pipe_{w,r}link`, `pipe_{w,r}olink`, `pipe_{w,r}chain`, `pipe_clink`, `pipe_{r,w,c}pay`, `pipe_{r,w,c}pay_taint`, `pipe_cpost`, `pipe_wpost(_cursor)`, `pipe_rpost_img(_cursor)`, `pipe_rstop_noobs` |
| PipeReg | `pipe_reg`, `pipe_row_reg(_nopipe,_persistent)`, `fileclose_cpay_of_reg_true`, `fileclose_cpays_of_regs` |

### 3.E The full table, by Rocq file

Each file lists:
- `present`: the Rocq name, then `→` the Lean spelling when it differs;
- **MISSING**: the kind, then the union files that read the name;
- the Lean text that mentions a name that has no declaration.

#### 3.E.1 Kernel-boundary names

**ElfUser** — 51 names, all per-program ELF literal facts (`<p>_elf`, `_elf_wf/_segments/_entry/_end/_length/_image(_concrete)`, `<p>_bss_lo/_size`, p ∈ init sh echo cat grep seccomp). IN FLIGHT (untracked, U0-7): `Xv6/ElfUser.lean` + `Xv6/User/<P>ElfRaw.lean` state them per namespace `Xv6.User.<P>` as `elf`, `elf_wf`, `elf_segments`, `elf_entry`, `elf_end`, `elf_length`, `elf_image` (docstrings cite each Rocq name). Users: UShEcho/UShCat/UShGrep, Fs*Pin, UInitUnionBoot, UkTreeEntry, UkFileEntries, UkPipesEntries, UInitSh. NOTE: brief §1.2 calls ElfUser a sanity leaf; it is not -- `union_Hinit_boot_at` reaches `init_elf` directly.

**FsImgCheck** — 4 present, 28 missing (Lean: FsImgCheck.lean, FsImgCheckBase.lean)
- present: `fsimg_path_root`→`fsimgPathRoot`, `fsimg_sb`→`fsimgSb`, `fsimg_wf_log_clean`→`fsimgWfLogClean`, `fsimg_wf_ok`→`fsimgWfOk`
- **MISSING**: `fname_cat` [def; FileDeltas, FileName, FileWrite…], `fname_echo` [def; AppEcho, FileDeltas, FileName…], `fname_grep` [def; FileDeltas, FileName, FileWrite…], `fname_init` [def; AppEcho, FileDeltas, FileName…], `fname_seccomp` [def; FileDeltas, FileWrite, FsSeccPin], `fname_sh` [def; AppEcho, FileDeltas, FileName…], `fname_sync` [def; FileName], `fsimg_byte` [def; FsConsPin], `fsimg_cat_at` [prf; FsCatPin], `fsimg_cat_path` [prf; FsCatPin], `fsimg_cat_type` [prf; FsCatPin], `fsimg_echo_at` [prf; FsEchoPin], `fsimg_echo_path` [prf; FsEchoPin], `fsimg_echo_type` [prf; FsEchoPin], `fsimg_grep_at` [prf; FsGrepPin], `fsimg_grep_path` [prf; FsGrepPin], `fsimg_grep_type` [prf; FsGrepPin], `fsimg_init_at` [prf; FsInitPin], `fsimg_init_path` [prf; FsInitPin], `fsimg_init_type` [prf; FsInitPin], `fsimg_root_data` [def; TreeImg], `fsimg_root_nrec` [def; TreeImg], `fsimg_seccomp_at` [prf; FsSeccPin], `fsimg_seccomp_path` [prf; FsSeccPin], `fsimg_seccomp_type` [prf; FsSeccPin], `fsimg_sh_at` [prf; FsShPin], `fsimg_sh_path` [prf; FsShPin], `fsimg_sh_type` [prf; FsShPin]

**UserFd** — 30 present, 24 missing (Lean: UserFd.lean, IgetLic.lean)
- present: `NSTD`, `tab_le`→`Table`, `ualloc`, `ualloc_at`→`uallocAt`, `ualloc_hi`, `ualloc_ledger`, `ualloc_std`, `ufd`, `ufd_agree`, `ufd_alloc_least`, `ufd_alloc_least_any`, `ufd_alloc_least_closed`, `ufd_auth`→`ufdAuth`, `ufd_auth_len`→`ufdAuth_len`, `ufd_close_hi`, `ufd_close_std`, `ufd_ge`, `ufd_ne`, `ufd_own`→`ufdOwn`, `ufd_own_after`→`ufdOwn_after`, `ufd_own_agree`→`ufdOwn_agree`, `ufd_own_hi`→`ufdOwn_hi`, `ufd_own_ne_lowest`→`ufdOwn_ne_lowest`, `ufd_own_std`→`ufdOwn_std`, `ufd_sub_hi`, `ustd`, `ustd_after`→`ustdAfter`, `ustd_agree`, `ustd_any`→`ustdAny`, `ustd_len`
- **MISSING**: `tab_le_refl` [prf; UkRun], `ualloc_v` [def; UConsOpen, UInitFd, UkInit…], `ualloc_v_hi` [prf; UkSh], `ualloc_v_std` [prf; UInitFd, UkSh], `ufd_alloc_least_at` [prf; UkRunSys], `ufd_alloc_std_at` [prf; UkFork, UkRun], `ufd_own_agree_at` [prf; UkRunSys], `ufd_own_ne_lowest_at` [prf; UkRunSys], `ush_view_ok` [def; UInitKernel, UInitSh, UShKernel…], `ush_view_ok_dup` [prf; UkInit], `ush_view_ok_fdt0` [prf; UInitUnionBoot], `ush_view_ok_open` [prf; UInitConsK, UkSh], `ush_view_ok_tab` [prf; UInitSh], `ustd_at` [def; UConsOpen, UInitBanner, UInitDiag…], `ustd_at_agree` [prf; UShExecPin, UkFork, UkRunSys…], `ustd_at_tab` [prf; UInitSh, UShExecPin, UkFork], `ustd_at_ustd` [prf; UConsOpen, UInitSh, UkRun…], `ustd_ok` [def; UInitConsK, UInitFd, UInitKernel…], `ustd_ok_taint` [prf; UInitFd], `ustd_ok_ustd` [prf; UInitFd, UkInit, UkInitMain…], `ustd_ustd_at` [prf; UkInitMain, UkShRun], `utab` [def; UkRunSecc, UkSeccMain], `utab_agree` [prf; UkRunSecc]
- no Lean decl, but Lean MENTIONS `ufdG` in UexecRet.lean: “…two are definitionally equal. 6. The `ufdG` section binder is not ported: no definition here reads the…”

**SysOpenDefs** — 14 present, 13 missing (Lean: SysOpenDefs.lean)
- present: `aopen_commit_at`→`aopenCommitAt`, `namei_walk_dead_era`→`nameiWalkDeadEra`, `om_arg`→`omArg`, `om_create`→`omCreate`, `om_rdwr_modes`→`omRdwr_modes`, `om_rdwr_plain`→`omRdwr_plain`, `om_readable`→`omReadable`, `om_trunc`→`omTrunc`, `om_writable`→`omWritable`, `open_au_create_at`→`openAuCreateAt`, `open_au_plain_at`→`openAuPlainAt`, `open_fd_rcpt`→`openFdRcpt`, `open_trunc_piece`→`openTruncPiece`, `open_trunc_piece_none`→`openTruncPiece_none`
- **MISSING**: `atrunc_commit_at_unit_pers` [prf; PinnedOpen], `atrunc_commit_i` [def; FileOpen], `atrunc_commit_i_of_at` [prf; PinnedOpen], `atrunc_of_permit` [def; FileOpen, PinnedOpen], `cre_ft_kept` [def; FileOpen], `open_trunc_at` [def; FileOpen, PinnedOpen, UInitCons], `trunc_permit_ex` [def; FileOpen], `trunc_permit_of` [def; FileOpen], `trunc_term_arg` [def; PinnedOpen, UInitCons], `trunc_term_at` [def; PinnedOpen], `trunc_term_at_of_arg` [prf; PinnedOpen], `trunc_tie_arg` [def; FileOpen], `trunc_tie_at` [def; FileOpen]

**FdSlots** — 11 present, 11 missing (Lean: UsysMemOk.lean, FileDefs.lean, UserFd.lean)
- present: `fd_least_closed`→`fdLeastClosed`, `fd_least_closed_free`→`fdLeastClosed_free`, `fd_least_closed_lt`→`fdLeastClosed_lt`, `fd_lowest_closed`→`fdLowestClosed`, `fd_st_of_key`→`fdStOfKey`, `fdslotG`→`FdslotG`, `fdstate`→`FdState`, `fdt0`, `fdt0_length`, `fdtype`→`FdType`, `offmode`→`OffMode`
- **MISSING**: `fd_least_closed_unique` [prf; UkRunSys], `fd_lowest_closed_app` [prf; UkRunSys], `fdslotGpreS` [rec; App, UInitUnion, UUnionBootAdequacy], `fdst_nopipe` [def; PipeReg, UConsOpen, UkFileDev…], `fdst_nopipe_closed` [prf; UkRun, UkRunSys], `fdv_nopipe` [def; UInitKernel, UkRun], `fdv_nopipe_closed` [prf; UInitUnionBoot], `fdv_nopipe_lookup` [prf; UkRun]
- no Lean decl, but Lean MENTIONS `fd_lowest_closed_below` in UsysMemOk.lean: “…/-- NOTHING SMALLER IS CLOSED (Rocq `fd_lowest_closed_below`). -/ theorem fdLeastClosed_below : ∀ {l : List FdState} {fd…”
- no Lean decl, but Lean MENTIONS `fd_lowest_closed_bound` in UsysMemOk.lean: “…e (l := l) (fd := k) hl /-- Rocq `fd_lowest_closed_bound` / `fd_least_closed_lt`. -/ theorem fdLeastClosed_lt {l : Li…”
- no Lean decl, but Lean MENTIONS `fd_lowest_closed_is_closed` in UsysMemOk.lean: “…fdLowestClosed sts = some fd /-- Rocq `fd_lowest_closed_is_closed` / `fd_least_closed_free`. -/ theorem fdLeastClosed_free : ∀…”

**FsAbsCreateNm** — 0 present, 10 missing
- **MISSING**: `acre_commit_at_gen_nm` [def; FileOpen, UInitCons], `acre_commit_at_gen_nm_cur_mono` [prf; FileOpen], `acre_commit_at_gen_nm_mono` [prf; FileOpen], `acre_commit_at_nm` [def; FileOpen, UInitCons], `aunarm_commit_at_nd` [def; UInitCons], `aunarm_of_arm_nd` [def; UInitCons], `cre_child_unfired_nd` [def; UInitCons], `nlast_elem` [def; FileOpen, UInitCons], `npar_nm` [def; FileOpen], `npar_nm_elim` [prf; FileOpen, UInitCons]

**UserPerm** — 8 present, 10 missing (Lean: UserPerm.lean, UPtDefs.lean, UexecRet.lean)
- present: `lazy_free`→`lazyFree`, `perm_of`→`permOf`, `perm_of_lookup`→`permOf_lookup`, `perm_of_mapped_U`→`permOf_mapped_U`, `uperm`→`UPerm`, `uperm_at`→`upermAt`, `uperm_rw`→`upermRw`, `usz_ok`→`uszOk`
- **MISSING**: `lazy_free_wmapped` [prf; UserHeap], `live_pages_bound` [prf; UkRunSys], `live_pages_mem` [prf; UkRunSys], `pgroundup_ge` [prf; UkRunSys, UkShMalloc, UserHeap], `proc_pt_wf_uleaf_wf` [prf; UserHeap], `pte_vu_of_valid_u` [prf; UserHeap], `uleaf_wf_lt` [prf; UserHeap], `usz_ok_live` [prf; UkRun]
- no Lean decl, but Lean MENTIONS `live_pages` in UPtDefs.lean: “…is empty** (Rocq `UserPerm.lazy_free`, `live_pages sz ⊆ dom um`): every page below `PGROUNDUP(sz)` is in the table, so no p…”
- no Lean decl, but Lean MENTIONS `perm_of_X` in UserPerm.lean: “…ssion check, `flags6`, `uleaf_*`), §4 (`perm_of_X/W/R` over a `uptd`, `image_byte_mapped`, `uva_*`), the `perm_of_…”

**UserPtTree** — 7 present, 10 missing (Lean: UPtDefs.lean, SpecFreerange.lean, UsysMemOk.lean)
- present: `pgroundup`→`pgRoundUp`, `umem_grow`→`umemGrow`, `umem_write`→`umemWrite`, `uptd`→`UPtd`, `uva_rmapped`→`uvaRmapped`, `uva_rmapped_of_wmapped`→`uvaRmapped_of_wmapped`, `uva_wmapped`→`uvaWmapped`
- **MISSING**: `live_set` [def; UkRunSys, UserHeap], `pgroundup_mono` [prf; UkRunSys], `umem_wr_ext` [prf; UkRunSys], `umem_wr_step` [prf; UkRunSys], `uva_rmapped_page` [prf; UserHeap], `uva_wmapped_page` [prf; UserHeap]
- no Lean decl, but Lean MENTIONS `umem_grow_id` in SyscallArmsSbrk.lean: “…m this⟩ /-- **Rocq `sbrk_ok_still` / `umem_grow_id`, at the lazy view**: the image at a LARGER break is the ima…”
- no Lean decl, but Lean MENTIONS `umem_wr` in ConsolereadGhost.lean: “…emWrite`/`viewFaulted` convention; Rocq `Mo = umem_wr Ment dst d bs`), its pages mapped. -/ def crWrote (P0 : UPtd) (M : Nat → L…”
- no Lean decl, but Lean MENTIONS `umem_write_lookup_in` in KexecBuilt.lean: “…/-- **A byte the write hits** (Rocq `umem_write_lookup_in`), where the view was defined (Rocq's `umem_write_dom` premi…”
- no Lean decl, but Lean MENTIONS `umem_write_lookup_out` in KexecBuilt.lean: “…/-- **A byte the write misses** (Rocq `umem_write_lookup_out`). -/ theorem umemGet_write_out (P : UPtd) (M : Nat → List (…”

**RiscvPtsto** — 4 present, 9 missing (Lean: MachCSL/Resources.lean, AppIface.lean)
- present: `app_iface`→`AppIface`, `obsN`, `obs_inv`→`obsInv`, `power_interp`→`powerInterp`
- **MISSING**: `riscvFixedGS` [rec; App, UInitUnionBoot, UUnionBootAdequacy], `riscv_rdwild` [def; UInitUnionBoot, UInitUnionCC, UShURoundDefs…], `riscv_wild` [def; UInitUnionBoot, UShUPipes, UShURound…], `wp_triv` [def; UConsOpen, UInitUnionBoot, UShCatFStage…]
- no Lean decl, but Lean MENTIONS `app_taint` in UsertrapKexit.lean: “…substance; Rocq's `fileclose_cpays` / `app_taint` tear-down package has no Lean counterpart (SpecKexit takes…”
- no Lean decl, but Lean MENTIONS `riscvGS` in EscrowDefs.lean: “…CE IS `MachGS`'s** (`MachFixedGS.mono`), Rocq's "mono_natG is ambient from riscvGS"; it is also the instance `IcacheRefDefs.icfgAl…”
- no Lean decl, but Lean MENTIONS `riscv_cons_res` in MachCSL/Power.lean: “…CLAIM, FOUNDED (Rocq `power_boot_res`'s `riscv_cons_res (S gen) [] (MkCH [] [] [] None)`): the application's yield at the power-on…”
- no Lean decl, but Lean MENTIONS `riscv_rx_tag` in MachCSL/Resources.lean: “…me /-- THE INPUT TAG FAMILY (Rocq `riscv_rx_tag`): every byte the environment pushes into a UART carries a…”
- no Lean decl, but Lean MENTIONS `svpn_of` in KexecBuilt.lean: “…once, at the commit). Rocq's page key `kexec_pg b = svpn_of b` is `b / 4096` here, and its bitvector arithmetic (`kexec_pg…”

**UsysMemOk** — 29 present, 9 missing (Lean: UsysMemOk.lean)
- present: `USYS_chdir`, `USYS_close`, `USYS_dup`, `USYS_exec`, `USYS_exit`, `USYS_fork`, `USYS_fstat`, `USYS_open`, `USYS_pipe`, `USYS_read`, `USYS_sbrk`, `USYS_wait`, `uecall_scause`→`uecallScause`, `usys_argfd`→`usysArgfd`, `usys_cwd_ok_quiet`→`usysCwdOk_quiet`, `usys_fd_ok`→`usysFdOk`, `usys_fd_ok_quiet`→`usysFdOk_quiet`, `usys_mem_ok`→`usysMemOk`, `usys_mem_ok_exec_row`→`usysMemOk_execRow`, `usys_mem_ok_lazy`→`usysMemOk_lazy`, `usys_mem_ok_quiet`→`usysMemOk_quiet`, `usys_mem_ok_wait_null`→`usysMemOk_waitNull`, `usys_num`→`usysNum`, `usys_rdcount`→`usysRdcount`, `usys_sbrk_arg`→`usysSbrkArg`, `usys_sbrk_eager`→`usysSbrkEager`, `usys_sbrk_img`→`usysSbrkImg`, `usys_sbrk_perm`→`usysSbrkPerm`, `usys_sbrk_ret`→`usysSbrkRet`
- **MISSING**: `USYS_seccomp` [def; UexecSecc, UkRunSecc, UkRunSys…], `usys_ch_ok_quiet` [prf; UkPipeDev, UkRunExecRef, UkRunSys], `usys_eff` [def; UexecSecc], `usys_fd_ok_pipe_neg1` [prf; UkRunSys], `usys_gen_ok_quiet` [prf; UexecSecc, UkPipeDev, UkRunExecRef…], `usys_mem_ok_read_ret` [prf; UkRunSys], `usys_secc_ok` [def; UexecSecc, UkRunSecc], `usys_secc_ok_quiet` [prf; UkPipeDev, UkRunExecRef, UkRunSys]
- no Lean decl, but Lean MENTIONS `usys_read_ret` in SyscallArmsFdDefs.lean: “…ide) /-- **read's answer row** (Rocq `usys_read_ret`): `-1`, or the window's length, which the count bounds. -/…”

**SpecSysOpen** — 6 present, 8 missing (Lean: SpecSysOpen.lean)
- present: `open_in`→`openIn`, `open_post_fail_create`→`openPostFailCreate`, `open_post_fail_plain`→`openPostFailPlain`, `open_receipt`→`openReceipt`, `open_receipt_create`→`openReceiptCreate`, `open_receipt_plain`→`openReceiptPlain`
- **MISSING**: `cre_fail_kept` [def; FileOpen], `cre_permit` [def; FileOpen], `cre_permit_ex` [def; FileOpen], `cre_trunc_kept` [def; FileOpen], `cre_trunc_kept_ex` [def; FileOpen], `cur_kept` [def; FileOpen, PinnedOpen, UConsOpen], `plain_cur_of_kept` [prf; PinnedOpen], `plain_trunc_kept_forget` [prf; PinnedOpen]

**FsAbsWriteFire** — 1 present, 6 missing (Lean: FsAbsWriteFire.lean)
- present: `awrite_chain_at_cursor`→`awriteChainAt_cursor`
- **MISSING**: `awrite_chain_adv` [def; UEchoFile, UkFileDev], `awrite_chain_adv_0` [prf; UkFileDev], `awrite_chain_adv_S` [prf; UkFileDev], `awrite_full_adv` [def; FileWrite, UEchoFile], `awrite_full_adv_mono` [prf; UkFileDev], `awrite_part_adv` [def; FileWritePart, FsAbsWritePart, UkFileDev]

**UexecExecMint** — 1 present, 6 missing (Lean: UexecExecMint.lean)
- present: `uslot_mint_all`→`uslotMint_all`
- **MISSING**: `udepw_law_of_sup_close` [prf; UkFreeHandler], `udepw_law_of_sup_read` [prf; UkFreeHandler], `udepw_law_of_sup_write` [prf; UInitFileLeaves, UInitUnionBoot, UkFreeHandler]
- no Lean decl, but Lean MENTIONS `udep_free` in UexecExecMint.lean: “…program-tier suppliers** `udep_gen`, `udep_free`, `udepw_free`, `udepw_of_sup(_read/_write/_close/_exit)`…”
- no Lean decl, but Lean MENTIONS `udepw_cl_of_reg_close` in UexecExecMint.lean: “…_of_sup*`, `udepw_row_of_reg_close`, `udepw_cl_of_reg_close`: their statements are over `UkRun.udep`/`udepw`/`udepw_l…”
- no Lean decl, but Lean MENTIONS `udepw_law_of_sup` in UexecExecMint.lean: “…_sup(_read/_write/_close/_exit)`, `udepw_law_of_sup*`, `udepw_row_of_reg_close`, `udepw_cl_of_reg_close`: thei…”

**UexecRet** — 42 present, 6 missing (Lean: UexecRet.lean, UexecSlot.lean)
- present: `bump`, `bump_at`→`bumpAt`, `sext_neg1_64`, `tf_of`→`tfOf`, `tf_of_num`→`tfOf_num`, `tf_resume_gpr0`→`tfResumeGpr0`, `uexec_fork_F`→`uexecForkF`, `uexec_fork_parent_F`→`uexecForkParentF`, `uexec_kill_arm_F`→`uexecKillArmF`, `uexec_live_ok`→`uexecLiveOk`, `uexec_pay_dep`→`uexecPayDep`, `uexec_pay_dep_ret`→`uexecPayDep_ret`, `uexec_pay_dep_triv`→`uexecPayDep_triv`, `uexec_ret`→`uexecRet`, `uexec_ret_F`→`uexecRetF`, `uexec_ret_cont_F`→`uexecRetContF`, `uexec_ret_cont_gen`→`uexecRetContGen`, `uexec_ret_ecall`→`uexecRet_ecall`, `uexec_wait_F`→`uexecWaitF`, `ufork_ans`→`uforkAns`, `ukb_F`→`ukbF`, `ukc`, `ukcq`, `ukcq_ukc`, `ukill_cred_at_of_owed`→`ukillCredAt_of_owed`, `ukont_F`→`ukontF`, `upay_at`→`upayAt`, `user_trap_frame_trapped`→`userTrapFrame_trapped`, `uslot`, `uslot_bump_at_run`→`uslot_bumpAt_run`, `uslot_bump_run`, `uslot_bupd`, `uslot_run`, `uslot_ukc`, `uslot_unfold`, `uvb`, `uvb_F`→`uvbF`, `uvis_of_run`→`uvisOfRun`, `uwait_ans`→`uwaitAns`, `uwait_ans_at`→`uwaitAnsAt`, `uwait_ans_of_pid`→`uwaitAns_of_pid`, `uwait_ans_pid`→`uwaitAnsPid`
- **MISSING**: `tf_of_arg0` [prf; ExecRun, UConsOpen, UInitConsK…], `tf_of_arg1` [prf; ExecRun, UConsOpen, UInitConsK…], `tf_of_arg2` [prf; UInitConsK, UShLine, UkFileDev…], `uvis_of_run_cwd` [prf; UkRunSys], `uvis_of_run_fd` [prf; UShLine, UkFileDev, UkPipeDev…], `uwait_ans_pid_m_forget` [prf; UkRunSys]

**DevModel** — 2 present, 5 missing (Lean: MachCSL/Dev/DevIds.lean, MachCSL/Dev/Uart.lean)
- present: `uart_id`→`UartId`, `uart_state`→`UartState`
- **MISSING**: `dev_state` [rec; App, AppUnionRec, UInitUnion…], `uart_acc` [def; App], `uart_loopback` [def; App]
- no Lean decl, but Lean MENTIONS `uart_rx_push` in AppLaws.lean: “…rt.recv` for Rocq's `uart_tx_pop`/`uart_rx_push`, and `cresAt` for Rocq's `if i is Uart0 then … else emp`…”
- no Lean decl, but Lean MENTIONS `uart_tx_pop` in AppLaws.lean: “…art.txPop`/`Uart.recv` for Rocq's `uart_tx_pop`/`uart_rx_push`, and `cresAt` for Rocq's `if i is Uart0 t…”

**ObsTrace** — 18 present, 4 missing (Lean: MachCSL/ObsTrace.lean)
- present: `cycles_of`→`cyclesOf`, `cycles_of_io`→`cyclesOf_io`, `cycles_rev`→`cyclesRev`, `cycles_rev_app`→`cyclesRev_app`, `hist_ext`→`histExt`, `is_io`→`isIo`, `obs_boots`→`obsBoots`, `obs_boots_app`→`obsBoots_app`, `obs_ends_in`→`obsEndsIn`, `obs_ends_in_inj`→`obsEndsIn_inj`, `obs_ends_in_snoc`→`obsEndsIn_snoc`, `obs_step`→`obsStep`, `obs_wf`→`obsWf`, `obs_wire`→`obsWire`, `open_seg`→`openSeg`, `open_seg_io`→`openSeg_io`, `trace_shape`→`traceShape`, `trace_shape_cycles`→`traceShape_cycles`
- **MISSING**: `obs_ins` [def; EchoDisc], `obs_ins_app` [prf; EchoDisc], `obs_ins_in` [prf; EchoDisc], `open_seg_prefix_of_boots` [prf; GenOutWild]

**UexecExecInst** — 9 present, 4 missing (Lean: UexecExecInst.lean)
- present: `uexecSG_xv6`→`uexecSGXv6`, `uprogSG_free`→`uprogSGFree`, `xfam`→`Xfam`, `xfam_at`→`xfamAt`, `xfam_exec_at`→`xfamExecAt`, `xfam_pt`→`xfamPt`, `xk_a`→`xkA`, `xv6_sbundle`→`xv6Sbundle`, `xv6_spost`→`xv6Spost`
- **MISSING**: `spost_at_pipe_elim` [prf; UexecSecc, UkReadPipe], `srow_reg_of_pipe_reg` [prf; UkReadPipe]
- no Lean decl, but Lean MENTIONS `exec_sbundle` in UexecExecInst.lean: “…[CtokG GF] [Fscfg] [Icfg] /-- **Rocq `exec_sbundle`**: the pay fact at the key's generation and own payload, be…”
- no Lean decl, but Lean MENTIONS `xfam_exec` in UexecExecInst.lean: “…dGFunctors} /-- **Rocq `xfam_pt`** (`xfam_exec` at the trivial families): every family trivial, the payload…”

**UexecSlot** — 6 present, 4 missing (Lean: UexecSlot.lean)
- present: `tf_resume_gpr_a0`→`tfResumeGpr_a0`, `tf_resume_gpr_a1`→`tfResumeGpr_a1`, `tf_resume_gpr_sp`→`tfResumeGpr_sp`, `tf_resume_pc`→`tfResumePc`, `tf_w`→`tfW`, `uvis`→`Uvis`
- **MISSING**: `usys_eff_secc_all` [prf; UkFork], `uvis_num` [def; UexecSecc, UkFork, UkPipeDev…], `uvis_num_full0` [prf; UkFork, UkPipeDev, UkRunExecRef…]
- no Lean decl, but Lean MENTIONS `secc_all` in AppLaws.lean: “…`app_turn A c (S gen_id)` and yields `init_boot_bundle … secc_all fdt0`. Today's hook `EraInitBoot` has neither; K1 adds the turn…”

**WpUart** — 9 present, 4 missing (Lean: UartLinks.lean, UartGhosts.lean, UartInv.lean)
- present: `chist_at`→`chistAt`, `cons_link`→`consLink`, `cons_read_pay`→`consReadPay`, `out_link`→`outLink`, `out_link_mono`→`outLink_mono`, `uartN`, `uart_ghosts`→`uartGhosts`, `uart_obs_permit`→`uartObsPermit`, `uart_obs_permit_ledger`→`uartObsPermit_ledger`
- **MISSING**: `cons_licence_at` [def; UexecSecc], `cons_licence_at_of_wild` [prf; UexecSecc], `cons_read_pay_triv_at` [prf; UexecSecc], `out_link_of_licence_at` [prf; UexecSecc]

**Xv6Cameras** — 5 present, 4 missing (Lean: SlotGen.lean, SlotSupply.lean, OffGv.lean)
- present: `bioslotG`→`BioslotG`, `fsLinkG`→`FsLinkG`, `fsTopG`→`FsTopG`, `offboxG`→`OffboxG`, `wchG`→`WchG`
- **MISSING**: `bioslotGpreS` [rec; App, UInitUnion, UUnionBootAdequacy], `bioslotΣ` [def; UUnionBootAdequacy], `uartGhostG` [rec; UkInit, UkSh]
- no Lean decl, but Lean MENTIONS `wchGpreS` in SlotGen.lean: “…p` / `sgenUR` / `orph_map` / `ipidUR` / `wchGpreS` / `wchG`), wave 7 decision D8 (the fork/exit generation mac…”

**AppInv** — 9 present, 3 missing (Lean: AppInv.lean)
- present: `appE`, `appN`, `app_body`→`appBody`, `app_claim_update`→`appClaimUpdate`, `app_inv`→`appInv`, `app_step`→`appStep`, `app_step_acc`→`appStep_acc`, `app_sup`→`appSup`, `app_sup_raw`→`appSupRaw`
- **MISSING**: `app_rdcred` [def; UShLine, UexecSecc, UkReadCons…], `app_rdcred_of_rdwild` [prf; UexecSecc], `app_rdcred_of_sup` [prf; UShLine]

**FsAbsReadFire** — 2 present, 3 missing (Lean: FsAbsReadFire.lean)
- present: `read_arms`→`readArms`, `read_post_ok`→`readPostOk`
- **MISSING**: `aread_commit_adv` [def; FileOpen, UkReadFile], `aread_in_om` [def; UkReadFile], `read_arms_mapped` [prf; FileOpen]

**OffGv** — 0 present, 3 missing
- **MISSING**: `off_link` [def; FsAbsWritePart], `off_link_of` [prf; FileOpen, FileWrite, FileWritePart], `off_link_taint` [prf; FileOpen, FileWrite, FileWritePart]

**ConsoleInv** — 14 present, 2 missing (Lean: ConsoleInvDefs.lean, ConsoleRing.lean, ConsoleTags.lean)
- present: `CONSOLE`, `cons_acc`→`consAcc`, `cons_acc_cred`→`consAcc_cred`, `cons_acc_reader`→`consAcc_reader`, `cons_chain`→`consChain`, `cons_dirty_cred`→`consDirtyCred`, `cons_out`→`consOut`, `cons_reader`→`consReader`, `cons_stored_lb`→`consStoredLb`, `cons_swallow`→`consSwallow`, `cons_window`→`consWindow`, `cons_xlate`→`consXlate`, `cons_xlate_cr`→`consXlate_cr`, `cons_xlate_other`→`consXlate_other`
- **MISSING**: `cons_placed` [def; UkReadCons], `cons_swallow_placed` [def; UShLine, UkReadCons]

**FsAbs** — 2 present, 2 missing (Lean: FsAbsWalk.lean)
- present: `ax_hop`→`axHop`, `ax_hops_from`→`axHopsFrom`
- **MISSING**: `astate_of_q` [prf; PinnedObs], `astate_q_intro` [prf; PinnedObs]

**FsDurImg** — 3 present, 2 missing (Lean: FsDurImgView.lean, FsDurImg.lean)
- present: `img_root_entries`→`imgRoot_entries`, `img_snap_ok`→`imgSnapOk`, `img_state`→`imgState`
- no Lean decl, but Lean MENTIONS `dir_view_agree` in FsDurImgView.lean: “…'s local copy), `dir_wins_agree`, `dir_view_agree`, `img_node_data` and `img_node_file_byte` are NOT re-por…”
- no Lean decl, but Lean MENTIONS `img_node_file_byte` in FsDurImgView.lean: “…_view_agree`, `img_node_data` and `img_node_file_byte` are NOT re-ported. Uses checked: FsDurImg.v and FsInitP…”

**FsImg** — 11 present, 2 missing (Lean: FsImgTree.lean, FsImgDinode.lean, FsImgWf.lean)
- present: `ROOTINO`, `fs_data_of`→`fsDataOf`, `fs_dinode`→`fsDinode`, `fs_root_wf_type`→`fsRootWf_type`, `fs_sb`→`FsSb`, `fsimg_wf`→`fsimgWf`, `fsimg_wf_root`→`fsimgWf_root`, `node_at`→`nodeAt`, `node_at_live`→`nodeAt_live`, `path_at_disk_dir`→`pathAt_disk_dir`, `tree_of_disk`→`treeOfDisk`
- no Lean decl, but Lean MENTIONS `FS_MAXFILE` in FsStateInode.lean: “…2. **`FS_NDIRECT` / `FS_NINDIRECT` / `FS_MAXFILE` ARE `Xv6.NDIRECT` / `NINDIRECT` / `MAXFILE`.** Rocq dup…”
- no Lean decl, but Lean MENTIONS `T_FILE_z` in FsStateInode.lean: “…d there is nothing to duplicate. `T_FILE_z` / `T_DEVICE_z` are `Xv6.T_FILE` / `T_DEVICE` (`Xv6/FsImg…”

**ProcAvail** — 0 present, 2 missing
- **MISSING**: `pavGpreS` [rec; App, UInitUnion, UUnionBootAdequacy]
- no Lean decl, but Lean MENTIONS `pavG` in FsAbsReadFire.lean: “…5. Class binders: Rocq's section list (`riscvGS, xv6G, bioslotG, fdslotG, fileG, irefslotG, pavG, wchG, CurCtx`) is replaced by e…”

**ProcPtOwn** — 0 present, 2 missing
- **MISSING**: `svpn_of_unsigned_gen` [prf; UkRunSys]
- no Lean decl, but Lean MENTIONS `proc_pt_wf` in SpecUserretClosed.lean: “…, `upt_acc_wf`, `ud_data = ud_pas`, `proc_pt_wf` are `procPtAt`'s `uptWf`. 3. **The slot is taken at the KEY…”

**SpecCopyin** — 1 present, 2 missing (Lean: SysWriteDefs.lean)
- present: `ubytes_at`→`ubytesAt`
- **MISSING**: `ubytes_at_inj` [prf; FileWrite]
- no Lean decl, but Lean MENTIONS `uimg_word_at` in SpecFetchaddr.lean: “…rd (umemRead _ addr 8)`, Rocq's `uimg_word_at`), read at ROCQ'S SINGLE IMAGE, fixed before the call: `…”

**SpecFileclose** — 0 present, 2 missing
- no Lean decl, but Lean MENTIONS `fileclose_cpay` in SyscallArmsFdDefs.lean: “…ose payment (Rocq `sysc_dep_close` / `fileclose_cpay` / `fileclose_cpost_any`) -- the byte-queue layer (Rocq d…”
- no Lean decl, but Lean MENTIONS `fileclose_cpays` in SyscallArmsExit.lean: “…Rocq's exit deposit (`sysc_dep_exit`: `fileclose_cpays sts`) has no Lean taker -- Lean's sys_exit takes `∃ sts, fdFr…”

**SpecFilewrite** — 8 present, 2 missing (Lean: SpecFilewrite.lean)
- present: `filewrite_extra`→`filewriteExtra`, `filewrite_in`→`filewriteIn`, `filewrite_ret`→`filewriteRet`, `write_arms_at`→`writeArmsAt`, `write_arms_at_ret`→`writeArmsAt_ret`, `write_cons_arms`→`writeConsArms`, `write_post_fail_at`→`writePostFailAt`, `write_post_ok_at`→`writePostOkAt`
- **MISSING**: `wr_tb` [def; UkFileDev]
- no Lean decl, but Lean MENTIONS `filewrite_in_held` in FsAbsInvFire.lean: “…n the row's `held`/`parked` mode (no `filewrite_in_held` right arm), so the dischargers take the one arm. 3. (ret…”

**SpecSysExec** — 3 present, 2 missing (Lean: SpecSysExec.lean)
- present: `exec_args_of`→`execArgsOf`, `sys_exec_au_pre`→`sysExecAuPre`, `sys_exec_slot_pre`→`sysExecSlotPre`
- **MISSING**: `exec_path_of_uniq` [abbrev; ExecBundle]
- no Lean decl, but Lean MENTIONS `exec_path_of` in SpecSysExec.lean: “…CABULARY: `ArgPath.argPathOf` (Rocq's `exec_path_of` is a parsing-only alias of `arg_path_of`; the Lean contract…”

**SpecSysRead** — 0 present, 2 missing
- **MISSING**: `sys_rw_count_lt` [prf; UkPipesIface]
- no Lean decl, but Lean MENTIONS `sys_rw_count` in SpecSysRead.lean: “…es fileread's `a2` is `argZ v2` (Rocq `sys_rw_count`), the 32-bit signed reading of the trapframe word -- `-2^…”

**SysMknodDefs** — 2 present, 2 missing (Lean: SysMknodDefs.lean)
- present: `dev_arg`→`devArg`, `npar_elems`→`nparElems`
- **MISSING**: `npar_cur` [def; FileOpen], `npar_cur_elim` [prf; FileOpen]

**SysWriteDefs** — 4 present, 2 missing (Lean: SysWriteDefs.lean)
- present: `FW_MAX`, `wchunks`, `wr_fail_why_refute`→`wrFailWhy_refute`, `wri_pre`→`wriPre`
- **MISSING**: `wchunks_one` [prf; UEchoFile]
- no Lean decl, but Lean MENTIONS `wchunk_at` in FsAbsWriteFire.lean: “…full arm's chunk-length conjunct (`wchunk_at`, RELAY 3), the partial arm's short-chunk and single-block…”

**UserOff** — 3 present, 2 missing (Lean: UserOff.lean)
- present: `uoff`, `uoff_advance`, `uoff_agree_k`
- **MISSING**: `foff_pub` [def; FileOpen, UkFileDev, UkFileOpen], `foff_pub_of_held` [prf; UShURound]

**ConsLog** — 13 present, 1 missing (Lean: ConsLog.lean)
- present: `cons_erase`→`consErase`, `cons_ev`→`ConsEv`, `cons_ev_ok`→`consEvOk`, `cons_step`→`consStep`, `echo_of`→`echoOf`, `gap_ok`→`gapOk`, `hist_chain`→`histChain`, `hist_chain_lt`→`histChain_lt`, `log_echoed`→`logEchoed`, `log_echoed_nonnil`→`logEchoed_nonnil`, `log_ok`→`logOk`, `log_ok_lt`→`logOk_lt`, `read_ok`→`readOk`
- **MISSING**: `wild_ev` [def; AppUnionRec]

**FileInvDefs** — 1 present, 1 missing (Lean: FileDefs.lean)
- present: `fileG`→`FileG`
- **MISSING**: `fileGpreS` [rec; App, UInitUnion, UUnionBootAdequacy]

**FsAbsEra** — 10 present, 1 missing (Lean: FsAbsEra.lean)
- present: `ax_hops_triv`→`axHops_triv`, `elend`, `ep_hops_done`→`epHops_done`, `ep_hops_from`→`epHopsFrom`, `ep_start`→`epStart`, `ex_hop`→`exHop`, `ex_hops_from`→`exHopsFrom`, `ex_start`→`exStart`, `np_elems`→`npElems`, `um_start_of`→`umStartOf`
- no Lean decl, but Lean MENTIONS `elend_aents` in FsAbsEra.lean: “…ads`, `elend_astate_q`, `elend_astate`, `elend_aents` / DEFERRED / over `lend_agrees`/`nview`/`astate` (FsAbs §3-…”

**FsImgDisk** — 1 present, 1 missing (Lean: FsImgDisk.lean)
- present: `fsimg_P`→`fsimgP`
- no Lean decl, but Lean MENTIONS `fsimg_dk` in FsImgDisk.lean: “…tal, zero past the image, as Rocq's `fsimg_dk` (a real virtio disk hands back zeroes past the end of it…”

**IrefSlots** — 1 present, 1 missing (Lean: IrefSlots.lean)
- present: `irefslotG`→`IrefslotG`
- no Lean decl, but Lean MENTIONS `irefslotGpreS` in IrefSlots.lean: “…cq's does (`irefslot_name`). Rocq's `irefslotGpreS` (the capacity alone) is `Xv6G` itself, which carries the…”

**KexecBuilt** — 10 present, 1 missing (Lean: KexecBuilt.lean)
- present: `kexec_pg`→`kexecPg`, `kexec_seg_pages`→`kexecSegPages`, `kexec_seg_perm`→`kexecSegPerm`, `kexec_sz_after`→`kexecSzAfter`, `kexec_sz_after_nil`→`kexecSzAfter_nil`, `kexec_sz_after_snoc_le`→`kexecSzAfter_snoc_le`, `kx_grow`→`kxGrow`, `kx_uvmalloc`→`kxUvmalloc`, `kxc_sp_final_gap`, `kxc_sp_gap`
- no Lean decl, but Lean MENTIONS `kxc_sp_mono` in KexecCParts.lean: “…di`, `kxc_sp_le_top`, `kxc_pa_stk_add`, `kxc_sp_mono`, `kxc_ustack_collapse_ex`, `kxc_ustack_slot_addr`). The ph…”

**LogDefs** — 1 present, 1 missing (Lean: LogDefs.lean)
- present: `fs_restrict`→`fsRestrict`
- no Lean decl, but Lean MENTIONS `fs_home_set` in BitmapInv.lean: “…t cov ls`**, the list form of Rocq's `fs_home_set cov ls`, because that is what `Xv6.fsBytesAt` is indexed by. 7. **`…”

**PathElems** — 10 present, 1 missing (Lean: PathElems.lean)
- present: `SLASH`, `noslash`, `path_elems`→`pathElems`, `pe_elem`→`peElem`, `pe_elem_ne`→`peElem_ne`, `pe_rest`→`peRest`, `pe_rest_ne`→`peRest_ne`, `pe_skip`→`peSkip`, `skipelem`, `skipelem_is_last`
- **MISSING**: `pe_skip_app_ns` [prf; UNamePath]

**ProcDefs** — 0 present, 1 missing
- no Lean decl, but Lean MENTIONS `secc_all` in AppLaws.lean: “…`app_turn A c (S gen_id)` and yields `init_boot_bundle … secc_all fdt0`. Today's hook `EraInitBoot` has neither; K1 adds the turn…”

**RiscvAdequacy** — 5 present, 1 missing (Lean: MachCSL/Adequacy.lean, AppIface.lean)
- present: `boot_fixedGS`→`bootFixedGS`, `obs_ledger_at`→`obsLedgerAt`, `obs_ledger_at_alloc_cl`→`obsLedgerAt_alloc_cl`, `obs_ledger_at_phi`→`obsLedgerAt_phi`, `obs_ledger_at_step`→`obsLedgerAt_step`
- **MISSING**: `riscvGpreS` [rec; App, UInitUnion, UUnionBootAdequacy]

**SystemAdequacy** — 4 present, 1 missing (Lean: SystemSlot.lean, FsImgCheck.lean, SystemAdequacy.lean)
- present: `app_xfer_boot_raw`→`appXferBootRaw`, `fsimg_image_wf`→`fsimgImageWf`, `xv6_power_adequacy_gen`→`xv6PowerAdequacyGen`, `xv6_slot`→`xv6Slot`
- no Lean decl, but Lean MENTIONS `xv6Σ` in Xv6GF.lean: “…- **THE CONCRETE FUNCTOR LIST** (Rocq `xv6Σ`): one slot per camera. -/ def xv6GF : BundledGFunctors :=…”

**UptTree** — 0 present, 1 missing
- **MISSING**: `tf_vpn_unsigned` [prf; UkRun]

**AppCfg** — 1 present, 0 missing (Lean: AppCfg.lean)
- present: `appcfg`→`Appcfg`

**ArgPath** — 3 present, 0 missing (Lean: ArgPath.lean)
- present: `arg_path_of`→`argPathOf`, `arg_path_of_uniq`→`argPathOf_uniq`, `arg_path_shape`→`argPathShape`

**BioDefs** — 1 present, 0 missing (Lean: DiskDefs.lean)
- present: `BSIZE`

**ChildTok** — 12 present, 0 missing (Lean: ChildTok.lean)
- present: `child_tok`→`childTok`, `child_tok_pid`→`childTok_pid`, `ctokG`→`CtokG`, `exit_tok`→`exitTok`, `exit_tok_pid`→`exitTok_pid`, `exit_tok_tok_ne`→`exitTok_tok_ne`, `gen_pay`, `gen_pay_timeless`, `gen_uniq_tok`→`genUniq_tok`, `kill_owed`→`killOwed`, `kill_shot`→`killShot`, `my_pay`→`myPay`

**CtxIdDefs** — 1 present, 0 missing (Lean: MachCSL/Ctx.lean)
- present: `CurCtx`

**DinodeEnc** — 1 present, 0 missing (Lean: DinodeEnc.lean)
- present: `dinode`→`Dinode`

**DirView** — 2 present, 0 missing (Lean: DirView.lean)
- present: `T_DIR_z`, `dir_win_agree`→`dirWinAgree`

**DirentEnc** — 1 present, 0 missing (Lean: FsGeom.lean)
- present: `DIRSIZ`

**ElfFile** — 9 present, 0 missing (Lean: ElfFile.lean)
- present: `elf_bytes`→`ElfBytes`, `elf_ehdr`→`ElfEhdr`, `elf_entry`→`elfEntry`, `elf_image`→`elfImage`, `elf_loads`→`elfLoads`, `elf_parse_ehdr`→`elfParseEhdr`, `elf_phdr`→`ElfPhdr`, `elf_phdrs`→`elfPhdrs`, `elf_segments`→`elfSegments`

**FsAbsCreateFire** — 11 present, 0 missing (Lean: FsAbsCreateFire.lean)
- present: `aarm_commit_at`→`aarmCommitAt`, `aunarm_commit_at`→`aunarmCommitAt`, `aunarm_of_arm`→`aunarmOfArm`, `cre_acre_fired`→`creAcreFired`, `cre_arm_fired`→`creArmFired`, `cre_child_pair`→`creChildPair`, `cre_child_unfired`→`creChildUnfired`, `cre_ex_fired`→`creExFired`, `cre_unarm_fired`→`creUnarmFired`, `dlookup_commit_at`→`dlookupCommitAt`, `dlookup_commit_at_unit`→`dlookupCommitAt_unit`

**FsAbsDefs** — 23 present, 0 missing (Lean: FsAbsDefs.lean)
- present: `abs_node`→`absNode`, `abs_of`→`absOf`, `abs_of_live`→`absOf_live`, `abs_row`→`absRow`, `abs_row_dir`→`absRow_dir`, `abs_view`→`absView`, `abs_view_lookup_of`→`absView_lookup_of`, `absnode`→`Absnode`, `aents`, `anode`→`Anode`, `anode_ents`→`anodeEnts`, `apath_at`→`apathAt`, `apath_at_cons`→`apathAt_cons`, `apath_at_nil`→`apathAt_nil`, `arow_at`→`arowAt`, `arow_at_gone`→`arowAt_gone`, `arow_at_live`→`arowAt_live`, `arow_at_pinned`→`arowAt_pinned`, `arun`→`Arun`, `arun_step_tot`, `astep`, `aview`→`Aview`, `fn_is_dir_typed`→`fnIsDir_typed`

**FsAbsDelta** — 15 present, 0 missing (Lean: FsAbsDelta.lean)
- present: `acre_bump`→`acreBump`, `cre_pre`→`crePre`, `cre_pre_ne`→`crePre_ne`, `delta_arm`→`deltaArm`, `delta_arm_lookup_same`→`deltaArm_lookup_same`, `delta_create`→`deltaCreate`, `delta_create_armed`→`deltaCreate_armed`, `delta_create_dev`→`deltaCreate_dev`, `delta_trunc`→`deltaTrunc`, `delta_trunc_lookup`→`deltaTrunc_lookup`, `delta_unarm`→`deltaUnarm`, `delta_write`→`deltaWrite`, `delta_write_absent`→`deltaWrite_absent`, `delta_write_lookup`→`deltaWrite_lookup`, `delta_write_other`→`deltaWrite_other`

**FsAbsInvFire** — 2 present, 0 missing (Lean: FsAbsInvFire.lean)
- present: `fsabs_chdir_pre`→`fsabsChdirPre`, `fsabs_exec_half`→`fsabsExecHalf`

**FsBlocks** — 2 present, 0 missing (Lean: FsBlocks.lean, FsBytes.lean)
- present: `blk_splice`→`blkSplice`, `fs_names`→`FsNames`

**FsBootParams** — 3 present, 0 missing (Lean: FsBootParams.lean)
- present: `XV6_DISK_BYTES`, `fsimg_cov`→`fsimgCov`, `fsimg_nib`→`fsimgNib`

**FsBytesGamma** — 1 present, 0 missing (Lean: FsBytesGamma.lean)
- present: `fs_gamma_L`→`fsGammaL`

**FsCfg** — 1 present, 0 missing (Lean: FsCfgDefs.lean)
- present: `fscfg`→`Fscfg`

**FsCfgBoot** — 3 present, 0 missing (Lean: FsCfgBoot.lean)
- present: `fs_boot_image_wf`→`fsBootImageWf`, `img_node`→`imgNode`, `img_nodes_lookup`→`imgNodes_lookup`

**FsCrash** — 3 present, 0 missing (Lean: FsCrashPure.lean, FsCrashSector.lean)
- present: `fs_blocks`→`fsBlocks`, `fs_recovery`→`fsRecovery`, `fs_recovery_clean`→`fsRecovery_clean`

**FsDurSnap** — 6 present, 0 missing (Lean: FsDurSnapBytes.lean, InodeRegionDefs.lean)
- present: `ind_bytes_inj`→`indBytes_inj`, `rec_in_blk_inj`→`recInBlk_inj`, `sk_bytes`→`skBytes`, `sk_local`→`skLocal`, `snap_bytes`→`SnapBytes`, `snap_ok`→`snapOk`

**FsNode** — 1 present, 0 missing (Lean: FsNode.lean)
- present: `fs_node`→`FsNode`

**FsState** — 1 present, 0 missing (Lean: FsState.lean)
- present: `fs_state_rec`→`FsStateRec`

**FsStateDefs** — 1 present, 0 missing (Lean: FsStateDefs.lean)
- present: `fs_view_names`→`FsViewNames`

**FsStateInode** — 9 present, 0 missing (Lean: FsStateInode.lean)
- present: `dir_entries`→`dirEntries`, `fn_file_bytes`→`fnFileBytes`, `fn_indb`→`fnIndb`, `fn_is_dir`→`fnIsDir`, `fn_naddr`→`fnNaddr`, `fn_nlink`→`fnNlink`, `fn_size`→`fnSize`, `fn_type`→`fnType`, `inode_local`→`InodeLocal`

**FsTree** — 9 present, 0 missing (Lean: FsTree.lean, FsNode.lean)
- present: `DOT`, `DOTDOT`, `dir_view`→`dirView`, `dir_view_lookup`→`dirView_lookup`, `file_bytes`→`fileBytes`, `fname`→`Fname`, `fsnode`→`FsNode`, `node_of`→`nodeOf`, `path_at`→`pathAt`

**IcacheEscrow** — 1 present, 0 missing (Lean: IcacheEscrowPool.lean)
- present: `region_inums_spec`→`regionInums_spec`

**InitBoot** — 3 present, 0 missing (Lean: InitBoot.lean)
- present: `init_boot_bundle`→`initBootBundle`, `init_boot_bytes`→`initBootBytes`, `init_boot_path`→`initBootPath`

**InodeDefs** — 1 present, 0 missing (Lean: InodeDefs.lean)
- present: `file_byte`→`fileByte`

**InodeInv** — 2 present, 0 missing (Lean: FsGeom.lean)
- present: `MAXFILE`, `ROOTINO`

**KexecDefs** — 11 present, 0 missing (Lean: KexecDefs.lean)
- present: `MAXARG`, `kxc_argc_bound`, `kxc_len_bound`, `kxc_round16`→`kxcRound16`, `kxc_sp`→`kxcSp`, `kxc_sp_final`→`kxcSpFinal`, `kxc_sp_final_ge`→`kxcSpFinal_ge`, `kxc_sp_final_range`→`kxcSpFinal_range`, `kxc_sp_range`→`kxcSp_range`, `kxc_span`→`kxcSpan`, `kxc_tf_sp_idx`→`kxcTfSpIdx`

**LogEntryDefs** — 5 present, 0 missing (Lean: MachCSL/LogEntryDefs.lean)
- present: `cons_arm`→`ConsArm`, `cons_hist`→`ConsHist`, `le_byte`→`leByte`, `le_hist`→`leHist`, `log_entry`→`LogEntry`

**PieceFam** — 6 present, 0 missing (Lean: PieceFam.lean)
- present: `pf_at`→`pfAt`, `pf_at_intro`→`pfAt_intro`, `pf_at_refund`→`pfAt_refund`, `pf_at_triv`→`pfAt_triv`, `pfam`→`Pfam`, `pfam_triv`→`pfamTriv`

**PipeInvDefs** — 1 present, 0 missing (Lean: PipeInvDefs.lean)
- present: `pipe_rw_ret`→`pipeRwRet`

**ProcGeom** — 5 present, 0 missing (Lean: ProcGeom.lean, SlotSupply.lean, KexecDefs.lean)
- present: `NOFILE`, `PIDMAX`, `exit_xs`→`exitXs`, `tf_arg_idx`→`tfArgIdx`, `tf_sp_idx`→`tfSpIdx`

**PtTree** — 1 present, 0 missing (Lean: UPtDefs.lean)
- present: `pte_vu`→`pteVU`

**SpecConsoleintr** — 1 present, 0 missing (Lean: ConsoleDefs.lean)
- present: `cons_echo_shift`→`consEchoShift`

**SpecConsolewrite** — 1 present, 0 missing (Lean: SpecConsolewrite.lean)
- present: `cons_out_chain`→`consOutChain`

**SpecFileread** — 4 present, 0 missing (Lean: SpecFileread.lean)
- present: `console_receipt`→`consoleReceipt`, `fileread_extra_core`→`filereadExtraCore`, `fileread_in`→`filereadIn`, `fileread_ret`→`filereadRet`

**SpecKexec** — 13 present, 0 missing (Lean: KexecImageOk.lean, KexecLoad.lean, SpecKexec.lean)
- present: `exec_au_pre`→`execAuPre`, `exec_key_ok`→`execKeyOk`, `exec_key_ok_fd`→`execKeyOk_fd`, `exec_slot_pre`→`execSlotPre`, `kexec_image_ok`→`kexecImageOk`, `kexec_image_ok_below`→`kexecImageOk_below`, `kexec_image_ok_fd`→`kexecImageOk_fd`, `kexec_image_ok_pc`→`kexecImageOk_pc`, `kexec_loadable`→`kexecLoadable`, `kexec_sz`→`kexecSz`, `kexec_top`→`kexecTop`, `kexec_ustack`→`kexecUstack`, `loads_ascending`→`loadsAscending`

**SpecSysMknod** — 4 present, 0 missing (Lean: SpecSysMknod.lean)
- present: `mknod_arms`→`mknodArms`, `mknod_au_at`→`mknodAuAt`, `mknod_post_fail`→`mknodPostFail`, `mknod_post_ok`→`mknodPostOk`

**SpecWritei** — 1 present, 0 missing (Lean: SpecWritei.lean)
- present: `wi_blocks`→`wiBlocks`

**SysReadDefs** — 5 present, 0 missing (Lean: SysReadDefs.lean)
- present: `anode_size_ok`→`anodeSizeOk`, `ard_count`→`ardCount`, `ard_count_le`→`ardCount_le`, `ard_count_sub`→`ardCount_sub`, `ard_ret_tie`→`ardRetTie`

**UartNames** — 2 present, 0 missing (Lean: ConsNames.lean, UartTrace.lean)
- present: `cons_names`→`ConsNames`, `uart_names`→`UartNames`

**UexecSG** — 4 present, 0 missing (Lean: UexecSG.lean)
- present: `free_num`→`freeNum`, `sbundle_pay`→`sbundlePay`, `uexecSG`→`UexecSG`, `uprogSG`→`UprogSG`

**UexecWp** — 4 present, 0 missing (Lean: UexecWp.lean)
- present: `loop_ok`→`loopOk`, `uexec_F`→`uexecF`, `uexec_wp`→`uexecWp`, `uexec_wp_unfold`→`uexecWp_unfold`

**UserChildren** — 12 present, 0 missing (Lean: UserChildren.lean)
- present: `uch`, `uch_agree`, `uch_alloc`, `uch_any`→`uchAny`, `uch_any_of`→`uchAny_of`, `uch_auth`→`uchAuth`, `uch_update`, `upid`, `upid_agree`, `upid_alloc`, `upid_auth`→`upidAuth`, `wait_ans`→`waitAns`

**UserCwd** — 4 present, 0 missing (Lean: UserCwd.lean)
- present: `ucwd`, `ucwd_agree`, `ucwd_alloc`, `ucwd_auth`→`ucwdAuth`

**VirtioModel** — 1 present, 0 missing (Lean: MachCSL/Dev/Virtio.lean)
- present: `virtio_state`→`VirtioState`

**Xv6G** — 1 present, 0 missing (Lean: UartTrace.lean)
- present: `xv6G`→`Xv6G`


#### 3.E.2 Engine-internal names the RUN layer reads (belong behind UK_LEAVES / the user lane, DU2)

**UserTotalU** — 0 present, 5 missing
- **MISSING**: `Du_r_nPC` [prf; UkRunLeaf], `Du_w_nPC` [prf; UkRunLeaf], `goodmb_execute_C_JR` [prf; UkRunLeaf], `u_gm_zca` [prf; UkRunLeaf], `u_gm_zicfilp` [prf; UkRunLeaf]

**UserFrame** — 0 present, 4 missing
- **MISSING**: `Du_gpr_of_Z` [prf; UkRunLeaf], `Du_gpr_of_Z_r` [prf; UkRunLeaf], `Du_r` [def; UkFork, UkPipeDev, UkRunExecRef…], `Du_w` [def; UkFork, UkPipeDev, UkRunExecRef…]

**DecodeTotalU** — 0 present, 2 missing
- no Lean decl, but Lean MENTIONS `D_u` in SpecUkLeaves.lean: “…ap `udrefU` -- Rocq's `dstateU` / `D_u` (`DecodeTotalU.v`): User, `misa`, `menvcfg = MENVCFG_S`,…”
- no Lean decl, but Lean MENTIONS `dstateU` in SpecUkLeaves.lean: “…reference map `udrefU` -- Rocq's `dstateU` / `D_u` (`DecodeTotalU.v`): User, `misa`, `menvcfg = MEN…”

**UserExecFacts** — 0 present, 2 missing
- **MISSING**: `goodmb_execute_ECALL_U` [prf; UkFork, UkPipeDev, UkRunExecRef…], `goodmb_execute_JALR_total` [prf; UkRunLeaf]

**WpDecodeBridge** — 0 present, 1 missing
- **MISSING**: `decode_state_bridge` [prf; UCodeCat, UCodeEcho, UCodeGrep…]

**UserExec** — 1 present, 0 missing (Lean: UserExec.lean)
- present: `ucfg`→`UCfg`


#### 3.E.3 Representation-level names (Sail/bitvector/regfile/decoder helpers: Lean encodes these differently; port as local helpers or restate over Lean's encoding)

**RiscvExtras** — 1 present, 23 missing (Lean: UexecSlot.lean)
- present: `ret_pc`→`retPc`
- **MISSING**: `add_vec64_unsigned` [prf; ExecArgs, UkRun, UkRunLeaf…], `add_vec_unsigned` [prf; UkGrepLoop, UkRunMem, UkShEcho…], `and_vec64_unsigned` [prf; UexecSecc, UkSeccLit, UkShParseTok], `auipc_off` [def; UkCatCat, UkEcho, UkInitMain…], `avi0` [prf; UEchoFile], `avi_mword` [prf; UkPipeDev], `bvw32_small` [prf; UkCatMain, UkCatTree, UkGrepLoop…], `bvw64_small` [prf; UConsOpen], `eq_vec_refl` [prf; UkCatCat], `moi32_unsigned` [prf; UkCatMain, UkCatTree, UkGrepLoop…], `moi64_small` [prf; UCodeShK], `moi64_unsigned` [prf; ExecArgs, UConsOpen, UkCat…], `ret_pc_jalr` [prf; UkRunLeaf], `sext64_32_inj` [prf; UkInitMain], `sext64_moi32_unsigned` [prf; UkShMalloc], `sub_vec32_unsigned` [prf; UmodeArith], `sub_vec64_unsigned` [prf; UmodeArith], `subrange_31_0_unsigned` [prf; UEchoOut, UkConsOut, UkReadRows…], `subrange_dec_unsigned_lo0` [prf; UmodeArith], `svpn_of_unsigned_lo` [prf; UCodeShK, UserHeap], `trunc32_sext64` [prf; UkShPipe], `uint_unsigned` [prf; ExecArgs, UCodeShK, UEchoOut…]
- no Lean decl, but Lean MENTIONS `trunc32` in FsAbsMknodFire.lean: “…tages consume is theirs to pick; `trunc32` is `extractLsb' 0 32`. 4. `bv_unsigned` is `.toNat`; `<[s :…”

**WpMmodeLeafBase** — 0 present, 8 missing
- **MISSING**: `caddi16sp_imm` [def; UkRunLeaf, UkShParse, UkShRedirPr…], `caddi4spn_imm` [def; UkCatCat, UkCatFprintf, UkCatMain…], `cli_rs1` [def; UkRunLeaf], `csp_rs1` [def; UEchoKernel, UInitKernel, UInitSh…], `exec_execute_C_JR` [prf; UkRunLeaf], `exec_execute_JALR_ret_zca` [prf; UkRunLeaf], `luival` [def; UkRunLeaf, UkSeccLit, UkSeccMain]
- no Lean decl, but Lean MENTIONS `sext6_12_64` in UmodeArith.lean: “…itVec.eq_of_toNat_eq simp /-- Rocq `sext6_12_64`: sign extension composes. -/ theorem usext6_12_64 (imm : Bi…”

**RiscvLang** — 5 present, 3 missing (Lean: MachCSL/Lang.lean, MachCSL/Resources.lean, SpecCpuid.lean)
- present: `CpuId`→`CPUID`, `GenId`→`genId`, `Loop`, `gstate`→`GState`, `mstate`→`MState`
- **MISSING**: `mexpr` [ind; App, UInitUnion, UUnionBootAdequacy]
- no Lean decl, but Lean MENTIONS `mobs` in UartTrace.lean: “…rived at (`UartNames.rxpop`; Rocq's `ghost_varG (nat * option (list mobs))`) -/ [gvPopG : GhostVarG GF (Nat × Option (List Obs))]…”
- no Lean decl, but Lean MENTIONS `riscv_lang` in UlibRun.lean: “…un`; see the header). `goal` is Rocq's `mWP (Loop : expr riscv_lang)`. -/ structure UlibRun (GF : BundledGFunctors) where /-- R…”

**RiscvModelBytes** — 2 present, 3 missing (Lean: MachCSL/TsoMem.lean, ElfEnc.lean)
- present: `assemble_bytes`→`assembleBytes`, `nth_byte`→`nthByte`
- **MISSING**: `bv_le_nth_byte` [prf; UImgWordDefs, UShGeom], `nth_byte_unsigned` [prf; UkCat, UkGrepLib, UkGrepPutc…]
- no Lean decl, but Lean MENTIONS `nth_byte_assemble_len` in DirView.lean: “…`BitVec.ofNat 16`. The port has no `nth_byte_assemble_len`, so `dirInum_byte0` / `_byte1` are proved directly on `t…”

**UserBits** — 0 present, 3 missing
- **MISSING**: `bit0_update0_64` [prf; UkRunLeaf], `uint_add_vec_int_small` [prf; UShOut, UStrImg, UkRunSys], `uint_unsigned_n` [prf; UkProgAbi, UkSh, UkShParse…]

**VcGen** — 0 present, 3 missing
- **MISSING**: `mword_of_int_uint` [prf; UkCatTree, UkGrepMain], `trunc32_mword_of_int` [prf; UkCatMain, UkCatTree, UkGrepLoop…], `trunc32_subrange` [prf; UEchoOut, UkCatTree, UkConsOut…]

**ByteBuf** — 0 present, 2 missing
- no Lean decl, but Lean MENTIONS `bb_cstr` in SysExecBreak.lean: “…argstr fetched, as kexec's `pfun` (`bb_cstr pfun plen`). -/ theorem sysExecBreak_nn (pl : List (BitVec 8)) (h : ar…”
- no Lean decl, but Lean MENTIONS `bb_nonul` in ByteBuf.lean: “…since this port has no naming-function `bb_nonul` / NOT PORTED, because this port already has them (do not d…”

**RegFile** — 1 present, 2 missing (Lean: MachCSL/Lang.lean)
- present: `regfile`→`RegFile`
- **MISSING**: `upd_eq` [prf; UInitConsK, UShConsK, UShFileRedir…]
- no Lean decl, but Lean MENTIONS `upd_ne` in CreateSharedRegs.lean: “…er bundles are over `RegMap` functions: `upd_ne` / `callee_saved_lookup` / `dlk_*` tactics are `RegMap.se…”

**InstrBytes** — 0 present, 1 missing
- **MISSING**: `nth_byte_subrange_lo` [prf; UkRun]

**KstackArith** — 0 present, 1 missing
- **MISSING**: `bvsigned_moi_small` [prf; UkConsOut]

**PageGeom** — 0 present, 1 missing
- no Lean decl, but Lean MENTIONS `PGSIZE` in SysExecParts.lean: “…s2 = i`, `s3 = &argv[i]`, `s5 = &uarg`, `s6 = PGSIZE`, `s7 = MAXARG`. -/ abbrev sysExecLoopPins (k : KCtx) (R : R…”

**StringBytes** — 0 present, 1 missing
- **MISSING**: `string_bytes` [def; EchoDisc, ProgTree]

**TsoCtx** — 0 present, 1 missing
- no Lean decl, but Lean MENTIONS `own_context` in UserExec.lean: “…lends (SpecUser's premise, Rocq's `own_context cur_ctx` accessor). 4. **Fractions**: Rocq splits `medeleg`/`senvcfg…”

**WpGpr** — 0 present, 1 missing
- **MISSING**: `gpr_of_Z` [def; UkRunLeaf]

**BlockWords** — 2 present, 0 missing (Lean: BlockWords.lean)
- present: `ind_bytes`→`indBytes`, `nth_byte_zero`→`nthByte_zero`

## 4. Camera classes for `unionGF`

**Per-file classes.** These are in the last column of §1.4. The table below inverts that column,
counting only files that have at least one reached declaration. Its Lean column applies the rule of one
instance per camera: each Rocq component is mapped onto an existing `xv6GF` slot (`Xv6/Xv6GF.lean`)
when the camera type is the same, and marked NEW otherwise.

### 4.1 The union's own classes (Rocq `unionΣ` minus `xv6Σ`, `UUnionBootAdequacy.v:118`)

| Rocq class (file) | components | used by (reached files) | Lean slot |
|---|---|---|---|
| `echoOutG` (EchoOut) | `mono_natG`; `ghost_varG nat`; `ghost_mapG nat era_pins`; `mono_list nat`; `mono_list (list mobs * bv 8)` | 73 files: every console/file/pipe claim, all the USh* rounds, all the UInit* files, the handlers | mono_nat → **MachGS's own** (slot 8; Rocq's comment warns that a second `mono_natG` is ambiguous, and Lean's `MonoNatG` is name-bearing, as EscrowDefs' header says); gv nat → **slot 25** (`Xv6G.gvNatG`); `mono_list nat` → **slot 86** (`xgfMl Nat`, DiskG); `mono_list (List Obs × BitVec 8)` → **slot 40** (`Xv6G.mlStoredG`); `ghost_map Nat EraPins` → **NEW** |
| `unionLineΣ` (UUnionBootAdequacy) | `inG (mono_listR (leibnizO Z))` | 49 files (App*, File*, UInit*, UShURound*, UShPipes*, the Uk*Iface/Entries files, Union*) | **NEW** `xgfMl Int` |
| `fileAppG` (AppFile) | `ghost_varG dst` (`dst = gmap fname (Z * list (bv 8))`); `mono_list fwline`; `mono_list esc_rec` | 38 files | 3 × **NEW** |
| `fileOutG` (FileOut) | `ghost_mapG nat file_era`; `mono_list fstate` | 26 files | 2 × **NEW** |
| `pipeOutG` (PipeOut) | `ghost_mapG nat pipe_era`; `ghost_varG (nat * gname * bool)` | 32 files | 2 × **NEW** |
| `pipeProtoG` (PipeProto) | `mono_list (bv 8)`; `inG pipe_eofR` (= `csum (excl ()) (agree (list (bv 8)))`); `inG pipe_roR` (= `csum (excl ()) (agree ())`); `ghost_varG nat`; `inG (exclR unitO)` | 15 files | `mono_list (BitVec 8)` → **slot 23** (`Xv6G.monoListG`, the UART trace); gv Nat → **slot 25**; `Excl Unit` → **slot 48**; `pipe_eofR`, `pipe_roR` → 2 × **NEW** |
| `pipesNG` (UkPipesIface) | `ghost_varG (option (list (bv 8)))` | 14 files | **NEW** (slot 35 is `Option (List Obs)`, a different type) |
| `pnsRegG` (UkPipesIface), `fifRegG` (UkFileIface), `cifRegG` (UkCatFIface) | `discrete_funUR (nat → optionUR (dfrac_agreeR (leibnizO X)))` at X = `pdev` / `fdev` / `cfdev` | 9 / 8 / 6 files | 3 × **NEW**, one shared functor shape `Nat → Option (DFracAgree X)` at three types |
| `bioslotΣ` | — | 74 files | **exists** (`BioslotG`, `xv6GF_bioslotG`) |

**Totals: 10 classes, 22 components.** `bioslotΣ` is not counted, since it exists.
- **15 components need new slots:** EraPins, `mono_list Int`, dst, fwline, esc_rec, file_era,
  fstate, pipe_era, `(ℕ × GName × Bool)`, pipe_eof, pipe_ro, `Option (List (BitVec 8))`, and the three
  registries.
- **7 components reuse existing slots:** 8, 23, 25 (twice), 40, 48 and 86.

### 4.2 Ambient classes the union files bind (all exist in Lean)

| Rocq class | Lean home |
|---|---|
| `riscvGS` / `riscv_fixedGS` / `riscvF_genGS` | `MachGS` (+ `MachFixedGS`) |
| `xv6G` | `Xv6G` |
| `ufdG` (167 files) | **not a class in Lean**: `FileG.gmUfdG`, slot 64 `xgfGm Nat FdState` (UserFd.lean header) |
| `uexecSG` / `uprogSG` | `UexecSG`, `UprogSG` (global instances, not slots) |
| `ctokG` | `CtokG` |
| `fileG` / `fdslotG` / `irefslotG` / `pavG` / `wchG` / `bioslotG` | exist; the `*GpreS` variants are `xv6GF_*` constructors |
| `uartGhostG` | folded into `Xv6G` (slots 23/24/…) |
| `fsLinkG` / `fsTopG` | `FsLinkG` / `FsTopG` |
| `diskImgG` (`ghost_mapG Z (bv 8)`) | slot 19 (`Nat ↦ BitVec 8`) |
| `fsCrashG` | `Xv6G.mlHistG` |
| `lockG` | the lock slots |
| `pipeG` (only PipeQueue: `frac`, `dfrac`, `pipeqR`) | **K2 decides**; `pipeqR` is new |

**The run layer's two anonymous ghost-var classes, and one open choice for U0-6.**
- `ghost_varG Z` (UkRun's break ghost, 136 files) → **slot 74**, `GhostVarF Int` (OffboxG).
- `ghost_varG (gset gname)` (the children set, 122 files) → **slot 51**, `GhostVarF (ExtTreeSet Nat
  compare)`. Xv6GF's header records that it already merges with `UserChildren`.
- **UserHeap's `utext`/`ubyte` maps are an open choice.** They are Rocq's `riscvF_diskGS`
  `ghost_mapG Z (bv 8)` (UserHeap.v:48: "no new ghost class"). Lean's only byte map is slot 19,
  which is `Nat`-keyed. If U0-6 keys user VAs by `Int` (brief §3.3), that is a **16th new slot**
  (`xgfGm Int (BitVec 8) IntMapF`, the functor family of slot 78). If it keys them by `Nat`, it reuses
  slot 19. The choice belongs to U0-6 and should be made once.

**Not needed:**
- `treeG`: `TreeImg`/`UkTreeRead` bind it, but no reached declaration uses it, and it is not in
  `unionΣ`.
- `PipeBothN`'s `ghost_varG A`: a section parameter, instantiated by its callers at the types above.
- `invGS`: App's own adequacy.
