# Brief: wave 1 — the fs.c LEAF FUNCTIONS (stati, namecmp, idup, iget, iupdate, ilock, iunlock, balloc, bfree)

Read notes/briefs/fs0_common.md first. Its rules apply unchanged: build only your own modules
(`timeout 1800 lake build Xv6.<Module>`), never run a bare `lake build`, no edits to existing files
(report the exact change instead), no Xv6.lean edits, no git, no `sorry`. Its cleanup paragraph
also applies, with the stricter rule restated below.

## 0. Standing rules (the user's words, verbatim; they bind every agent in this wave)

- "the file system is a tricky piece of spec/proof. It's important to consult the Rocq version
  whenever you might be possibly in doubt about the right way to spec/prove something; it has the
  whole thing fully specified and proven."
- "broadly speaking, don't reinvent the wheel; check the Rocq version instead."
- "some cleanup is helpful, as there is a fair bit of gunk accumulated in the Rocq proofs, but the
  big ideas should be taken from there."
- "it's not a good idea to simplify without having the full picture or plan, because then the risk
  is, the simplification will turn out to be at odds with some later part of the proof/spec."

In practice: the Rocq `Spec<F>.v` sets the contract shape and the Rocq `Proof<F>.v` sets the proof
route, including the stage lemmas, the ghost moves and the order of invariant opens. Before any
cleanup, grep `/shared/xv6rocq/iris/*.v` (comments stripped, `.claude/worktrees` ignored) for every
downstream consumer: the later fs functions AND the syscall layer (`ProofSys*`, `ProofCreate*`,
`ProofFile*`, `ProofNamex*`, `ProofKexec*`). Record every cleanup in the file header as "Dropped/
simplified vs Rocq: <item> — uses checked: <files> — reason". If you cannot see every consumer,
keep the Rocq form.

**Project rules.**
- One kernel function per file triple: `Xv6/Spec<Fn>.lean`, `Xv6/Proof<Fn>.lean`,
  `Xv6/Link<Fn>.lean`. A big proof may be split into `Xv6/Proof<Fn><Part>.lean` files; the
  `ProofVirtioDiskRw{A..F}` precedent is fine, and so are descriptive suffixes like
  `ProofIgetScan`. Every file belongs to that one function.
- A `Spec<Fn>.lean` imports only the definitional layer and callee `Spec*` files, never a `Proof*`
  or `Code*` file.
- **Proofs must be fast: no theorem over a few seconds.** Stage the proof as Rocq does: one
  `theorem` per code segment (epilogue, tail, loop body, each arm), each entered with its
  continuation as a named hypothesis or a named `def` (Rocq's `*_cont`/`*_frame`), and state the
  ghost-only moves as separate lemmas outside the instruction walk. Use
  `set_option maxHeartbeats N in` only per theorem, and only as the existing proofs do. If a
  theorem gets slow, split it; do not raise limits.
- `tools/check_layering.sh` must stay green.

## 1. Templates and idioms (read before writing)

- **The fs.c template.** `Xv6/SpecIinit.lean`, `Xv6/ProofIinit.lean` and `Xv6/LinkIinit.lean`
  (iinit is proved). The shape:
  - `def wp_<f>_body … (hK : N ≤ k.avail) … : Prop := kctx cpu k ∗ pcIs cpu <f>Addr ∗ … ∗ wpNext k.sie k.proc cpu (fun cpu' => …) ⊢ wpLoop cpu`
  - `structure <F> : Prop where wp_<f> : ∀ …, wp_<f>_body …`
  - `theorem <f>_proof (C1 : CALLEE1) … : <F>` in the Proof file
  - `theorem <F>' (C1 : …) : <F> := <f>_proof …` in the Link file (see `LinkIinit.lean`).
- **Instruction walking.** `k_step (wp_s_<op> c _ (KA.«f» + 0x..#64) is_rvc …) $$ [...]` and
  `k_step_gen … next c1 hp1` (MachCSL/WpSmodeFrame.lean:178–249); `icases kctx_kernelText _ _ $$ Hk
  with ⟨#HT, Hk⟩` then `from (text_instr _ _ _ _ rfl rfl) HT`. Return-address facts are stated as
  `theorem xx_ret_… : jumpPc (KA.«f» + 0x..#64) = … := by decide`.
  - Straight-line: `Xv6/ProofFilealloc.lean` (scan by fuel induction, shared tail `fa_tail`).
  - Lock-held word update: `Xv6/ProofFileclose.lean`.
  - The bread/log_write/brelse cone: `Xv6/ProofLogWrite.lean`, `Xv6/ProofInstallTrans.lean` and
    `Xv6/ProofEndOp.lean` (these call `BREAD.wp_bread`; ProofInstallTrans also calls `PRINTK` via
    the `panicEnv` pattern, `it_printk` ~l.372).
  - A LIVE panic call: `Xv6/ProofBread.lean`.
  - A dead `unreachable` arm: `Xv6/ProofBwrite.lean`.
- **Callee templates.**

  | callee | Lean caller to copy |
  |---|---|
  | `ACQUIRE.wp_acquire` | ProofKalloc:330, ProofAcquiresleep:247 |
  | `RELEASE_HOOK.wp_release_hook` | ProofReleasesleep |
  | `RELEASESLEEP_HOOK.wp_releasesleep_gen_hook` | ProofBrelse |
  | `wp_s_lw_au` (accessor load) | ProofVirtioDiskIntr |
  | `wp_s_sw_mint` | ProofInitlock |
  | `wp_log_write_au` | ProofLogWrite (the derivations of `_gen`) |

- **Addresses.** Use `KA.«f» + 0x..#64`; the Lean image is the reference. **Never copy absolute
  addresses or immediates from Rocq comments:** the Lean text sits 6 bytes lower, and several Rocq
  headers are stale even for Rocq. Dump a function with
  `riscv64-linux-gnu-objdump -d --section=.text xv6-riscv/kernel/kernel | awk '/<f>:$/,/^$/'`.
- **Machine-layer vocabulary mapping** (Rocq → Lean, already settled by earlier waves):

  | Rocq | Lean |
  |---|---|
  | `sie_cap_gpr` + `cpu_own n eb p b lks` | `kctx cpu k`, with `k.noff`, `k.sie`, `k.locks`, `k.proc`, `k.avail` |
  | `K_f ≤ K` | `hK : N ≤ k.avail` |
  | `locks_below lks "x"` | explicit `"x" ∉ k.locks` premises (Lean has no lock ranks), or `k.locks = []` where a callee (bread, acquiresleep) pins it |
  | `trap_csrs_ext`/`cpu_claim_ext` | `trapCsrs cpu ∗ cpuClaim cpu k.proc ∗ intrRes cpu` |
  | `proc_priv_bare pj pidv Upr` | `wordPointsTo (pPid k.proc) 4 dqp pidv` |
  | `procs_inv γs` | `procsInv Γ` (drop `gs`/`gl`) |
  | `dev_inv`/`disk_geom`/`is_lock … disk_res_at` | `diskCaps V.gd γdl pd pav pu` + `descPageRw pd` |
  | `panic_env` | `panicEnv`; `printk_env` = the same credentials (see `it_printk`) |
  | `llb T` | `topLb T` |
  | `ctx_floor` | `ctxFloor` |
  | `kernel_data` | `kctx_kernelData` |
  | `gset Z` `Sb ∪ {[b]}` | `List Nat` `b :: Sb` (LogDefs deviation) |
  | `log_region_set` | `logRegion`/`fsHome` |
  | `Z` inums/`z` | `Nat` (KEY-TYPE SEAM of fs0d_icache.md §1) |

- **The `sie` question, settled for this wave.** Lean `BREAD`, `ACQUIRESLEEP(_LLB)`, `BEGIN_OP`
  and `END_OP` are pinned to `k.sie = false ∧ k.noff = 0 ∧ k.locks = []`, and have no `eb`
  parameter. Every contract that calls bread or acquiresleep (iupdate, ilock, balloc, bfree) is
  therefore stated at that pin, and Rocq's `eb`/`b` genericity collapses. This is a recorded
  deviation, not a cleanup. Contracts whose callees are sie-generic (stati, namecmp, idup, iget,
  iunlock) stay sie-generic, as in Rocq.
- **`unreachable`.** This kernel calls `unreachable(msg)` (0x80000860), not `panic`, on the arms
  Rocq proves dead. There is no Lean spec for it and none is needed: every `unreachable` arm is
  refuted before the `jal` (ProofBwrite precedent). `panic` (0x80000838) marks the two LIVE arms.

## 2. Status of the ground you build on

- **Landed (use, do not duplicate):** the whole wave-0 layer. The groups are:
  - FsGeom, DinodeEnc/DinodeSlot, DirentEnc, BitmapEnc/BitmapInv/FsStateBitmap, FsBytes*,
    FsBlocks, LogDefs/LogInv (`logOp`, `logOpS`, `logOpSe`, `logOpSw(e)`, `logCredit`,
    `logEpochLb`, `logTx`), TxPin, InodeInv/InodeLock/InodeRegion*.
  - IcacheRef*, IcacheInv*, IcacheEscrow*, IcacheBox*, IcacheHeld, IcacheCover, IcachePinwObl,
    IgetLic, Escrow*, OffBox, FsState*, AppCfg/AppInv, FsAbsDefs.
  - Callees: all green (`BREAD`, `BRELSE`, `LOG_WRITE`, `MEMMOVE`, `MEMSET`, `STRNCMP`,
    `ACQUIRE`, `RELEASE_HOOK`, `ACQUIRESLEEP_LLB`, `HOLDINGSLEEP`, `RELEASESLEEP_HOOK`, `PANIC`,
    `PRINTK`).
- **Gate H1: `Xv6/IcacheTable.lean`** (`isItable2`, `itableRes2(_llb)`, `itableCtxHook`,
  `islots2_acc_upd`, `icEscrows_lookup`, `icSleeplocks`, `itableSlotRes_acc_upd(_llb)`) exists
  (1155 lines) but is UNTRACKED at the time of writing (fs0d batch H1). **idup and iget must not
  start until H1 is committed.** The others do not touch it.
- **Wave-1 prerequisites (not landed): §4 items W1-M1…M3, W1-LW, W1-TX.** Each function below
  names the ones it needs.
- **Lean lemma naming is mixed.** The port writes `camelHead_snakeTail` (`frzPark_shr_off`,
  `isItable2_lock`), and some movers kept their Rocq snake names verbatim
  (`iref_load_locked_pinw_au`, `iref_upgrade_mir_store_pinw_au`, `iref_readAU`). Grep for both
  spellings before concluding a name is missing.

## 3. Per-function facts

Rocq line numbers are for `/shared/xv6rocq/iris/<File>.v`. The survey (notes/fs-rocq-summary.md)
§3.n has each spec verbatim, §1d the residuals, §4C the budgets, §6.2 the per-function pitfalls.
The stack budget `N` is the Rocq `K_f`: own frame plus the deepest callee. The Lean `*Slots` defs
agree (`breadSlots = 6 + panicSlots = 62`, `panicSlots = 56`, `logWriteSlots = 18`). Define
`<f>Slots : Nat := <frame> + <callee>Slots` in the Spec file, as bread does.

### 3.1 stati — EASY (~250 Lean lines, 1 proof file)

- **Rocq.** SpecStati.v 190, ProofStati.v 517, LinkStati.v 7.
- **Image.** `KA.«stati»` = 0x800036a4, 46 B, 19 instrs, straight-line, a 16-B frame. It uses
  **`lh`** (68(a0), 74(a0)), `sh`, `lw`/`sw`, **`lwu`**+`sd`.
- **Budget.** `K_stati = 2`.
- **Callees.** None.
- **Contract** (`wp_stati_sconf_body`, SpecStati.v 142–178):
  - Premise: a0 = ip, a1 = st; ip is ANY pointer (no `ientry k`).
  - Pre: `iDev ip ↦₄{dqd} dev`, `iInum ip ↦₄{dqn} inum`, `inodeMeta ip dn`,
    `statAt st dev0 ino0 ty0 nl0 sz0`.
  - Post: the three inode cells back, and
    `statAt st dev inum (diType dn) (diNlink dn) (zeroExtend 64 (diSize dn))`.
  - No locks, log units or bslots. sie-generic.
- **Consumes.** `iDev`/`iInum` (IcacheRefDefs:436/438), `inodeMeta` (InodeInv:1424),
  `iType`/`iNlink`/`iSize` (InodeInv:156–164), `Dinode` fields (DinodeEnc:66).
- **Missing, and yours to define** in SpecStati.lean: `stDev…stSize` and `statAt` (SpecStati.v
  103–137; five cells ↦₄ ↦₄ ↦₂ ↦₂ ↦₈; bytes 12..15 deliberately NOT owned).
- **Needs** W1-M1 (`wp_s_lh`).
- **Watch.** The `lwu` → `sd` zero-extension at +0x20/+0x24; the `lh`/`sh` pairs cancel via
  trunc16∘sext.

### 3.2 namecmp — EASY (~300 lines, 1 proof file)

- **Rocq.** SpecNamecmp.v 100 (`K_namecmp` at l.264, body 265–289), ProofNamecmp.v 481
  (pure bridge 66–120, walk 160–477), LinkNamecmp.v 6.
- **Image.** `KA.«namecmp»` = 0x800038ca, 22 B: 16-B frame, `li a2,14`, `jal strncmp`, epilogue.
- **Budget.** `K = 4`.
- **Callee.** `STRNCMP.wp_strncmp` (SpecStrncmp.lean:56/69).
- **Contract.**
  - Pre: the two 14-byte runs `[∗list] j ∈ seq 0 14, s+j ↦{dq} f j`.
  - Post: runs back, and `⌜a0 = 0 ↔ bname 14 f = bname 14 g⌝`. The signed difference is
    deliberately NOT exposed.
- **Consumes.** `bname`, `ncStop`, `ncStop_iff`, `ncZero_iff`, `namecmp_bridge` (DirentEnc.lean
  695–906), `strncmpStop`/`strncmpRes` (SpecStrncmp).
- **The one real issue.** The Lean `STRNCMP` is LIST-based (`byteBuf a dq bs`, premises
  `n ≤ bs.length`, `n < 2^31`), while `bname`/`ncStop` are over `Nat → BitVec 8`.
  - State namecmp's runs as Rocq does, then bridge once, as a named lemma, to `byteBuf` of the
    list `(List.range 14).map f`.
  - Or state them as `byteBuf` of a length-14 list, and check that dirlookup (wave 4, SpecDirlookup)
    can supply it; Rocq's dirlookup passes the function form. Look at ProofDirlookup's call before
    choosing.
  - Port `nc_byte_of_zero`, `nc_stop_of_strncmp` and `nc_res_iff`.
- **Needs** nothing new.

### 3.3 idup — MEDIUM (~800 lines, 2 files)

- **Rocq.** SpecIdup.v 276 (`K_idup` l.187, body 189–266), ProofIdup.v 1044 (core
  `wp_idup_core` 163–984 at a SHARE; wrapper `wp_idup_sconf` 994–1040), LinkIdup.v 11.
- **Image.** `KA.«idup»` = 0x800032c2, 54 B:
  - frame 4 slots; acquire(&itable)
  - `lw a5,8(s1)` / `addiw` / `sw a5,8(s1)` (ip->ref++ under the lock)
  - release; return ip.
- **Budget.** `K = 14`.
- **Callees.** `ACQUIRE.wp_acquire` (R := `itableRes2 …`) and **`RELEASE_HOOK.wp_release_hook`**
  (Rocq calls `wp_release_hook_sconf` with `Rin := itableRes2`, `R := itableRes2Llb` and hook
  `itableCtxHook`). So `Idup (AC : ACQUIRE) (RH : RELEASE_HOOK) : IDUP`, not `RELEASE`.
- **Contract.**
  - Premises: `k < NINODE`, a0 = `ientry k`, `noff + 1 < 2^31`, `"itable" ∉ k.locks`.
  - Pre: `isItable2 …`, `itableInv`, `iregInv …`, `irefSlot`, `inodeHeldAt (ientry k) z`.
  - Post: `inodeHeldAt (ientry k) z` TWICE, a0 = ientry k, `kctx` balanced. sie-generic.
- **Ghost route (keep Rocq's order).**
  1. `isItable2_lock/_claims/_escrows` → `icEscrows_lookup` → `iref_share_lookup_pinw_au`
     (IcacheInvRef:705) → `islots2_acc_upd` → `inodeIdent_agree` → `frzPark_shr_off`
     (IcacheInvRef:992) → `irefSlots_combine/_no_overflow/_supply` → `irefClaims_at` →
     `itableSlotRes_acc_upd_llb` → `icHitIncr` (IcacheBoxSites:352).
  2. LOAD: `wp_s_lw_au` (sie = false after acquire) with `iref_readAU_locked`
     (IcachePinwObl:188) and `iref_load_locked_pinw_au` (IcacheInvRef:666).
  3. STORE: `wp_s_sw_au` + `irefPinRows_push` (IcacheInvRef:381) + `irefSet_count` (Rocq
     `pinw_write_c`, see fs0d-pinw-design §3 table), with AU `iref_upgrade_mir_store_pinw_au`
     (IcacheInvStore:749).
  4. Close with `inodeIdent_split`, `frzPark_intro_off` and `islPool_acc_upd`; rebuild
     `itableRes2Llb`, then `itableCtxHook` at release.
  5. The wrapper: `inode_ref_shed` → core → `inode_ref_gather`.
- **Missing.** Rocq's `locks_below_*` lemmas; they become list reasoning.
- **Needs** gate H1. idup is the FIRST Lean consumer of the AU load/store pair over `itableInv`;
  its lemmas are the template iget copies. **No panic** (unlike filedup).
- **Stale in Rocq.** Header l.21 names `iref_dup_store_au`; the code uses
  `iref_upgrade_mir_store_pinw_au`. `sie_b_agree` (137–149) is not needed in Lean.
- **Wave-7 note.** `Xv6/FsEnv.lean:97` models idup abstractly (`FsEntryNB idupAddr`) for kfork.
  Reconciling it is wave 7's job, not yours.
- **Split.** `ProofIdupCore.lean` holds the ghost critical-section lemmas; `ProofIdup.lean` holds
  the walk and the wrapper.

### 3.4 iget — HARD (~2000 lines, 4–6 files); LIVE PANIC

- **Rocq.** SpecIget.v 301 (header 1–173, `K_iget` l.211, body 213–290), ProofIget.v 2618,
  LinkIget.v 16.
- **Image.** `KA.«iget»` = 0x80002f5a, 170 B, frame 6 slots:
  - acquire(&itable); scan of `itable.inode[0..50)` (cursor s1, stride 136, sentinel `&log`)
  - live-slot `lw 8(s1)` / `blez` / dev and inum compare
  - hit: `addiw`/`sw 8(s1)`, release
  - miss: remember the first free slot in s3; at the sentinel `beqz s3` → `panic("iget: no inodes")`
  - recycle: `sw` dev, inum, `ref = 1`, `valid = 0`, release.
- **Budget.** `K = 62` (6 + panic 56).
- **Callees.** `ACQUIRE`, `RELEASE_HOOK` (two release sites, both with `itableCtxHook`), `PANIC`.
- **Contract** (the one form).
  - Premises: `n + 3 < 2^31` (acquire +1, printk +2 on the panic arm INSIDE the lock),
    `inum < 16·icfgNib`, `0 < inum`, a0 = sext `icfgDev`, a1 = sext inum, and the lock premises
    `"itable" ∉ k.locks`, `"pr" ∉ k.locks`, `"uart1" ∉ k.locks` (Rocq: `locks_below lks "itable"`
    plus the rank edge "itable" < "pr").
  - Pre: `isItable2`, `itableInv`, `icEscrows`, `iregReg`, `panicEnv`, `irefSlot` and the
    LICENCE `iname … inum l` (IgetLic).
  - Post: `wpNext k.sie` (iget never sleeps), `∃ k' q`, `k' < NINODE`, a0 = `ientry k'`,
    `inodeRefb (isClaim l) k' q icfgDev inum`, and the licence returned at the SAME `l`.
- **LIVE PANIC, KEEP IT LIVE** (survey §1d; fs0d_icache §6): nothing a caller can state rules out
  a full table. Discharge it against `PANIC.wp_panic` at `noff + 1` with `"itable"` held, and drop
  the licence and the held lock (partial correctness). Do NOT add a premise that refutes it.
- **Proof route** (ProofIget.v).
  - Pure `ig_*` (147–388).
  - Prologue + acquire (499–707).
  - Shared tail TAILC (800–1010), proved first as the continuation.
  - SCAN (1011–1815) by fuel induction on `NINODE − j`. Invariant: no live slot `< j` carries
    (dev, inum); s3 = 0 or a free entry; `M`, `ci` fixed.
  - Sentinel + panic (1125–1207).
  - RECYCLE (1208–1795):
    - `icRecycleWithdraw` → dev store → `icRecycleFlip` (uses the licence) → inum store
    - **`ref = 1` via `wp_s_sw_mint`** + `irefPinRows_mint` + `ownCtx_key_topLb` (IcacheInvRef)
      + `iref_alloc_pinw_install` (Rocq `pinw_arm_write_c` + `ctx_wrote_register`;
      fs0d-pinw-design §3)
    - `valid = 0` → `icRecycleDeposit`, `frzPark_intro_off`
    - release-hook, then `credFloor_of_wrote`.
  - Live-slot load (1815–2082): `wp_s_lw_au` + `iref_readAU_locked` + `iref_load_locked_pinw_au`.
    The dev and inum compares are plain reads via `islots2_acc_upd`.
  - HIT (2083–2462): `frzPark_lic_off`, `irefSlots_*`, `icEscrows_lookup`, `icHitIncr`, then
    `wp_s_sw_au` with `irefPinRows_push` and `iref_incr_store_pinw_au`, then release-hook.
  - Free slot (2463–2600): a plain `lw` of the payload's ctx cell.
- **Consumes** (all present): IcacheTable (H1), `itableInv`, `icEscrows` (IcacheBox), `iregReg`,
  `irefSlot`, `iname`/`isClaim`/`Ilic` (IgetLic), `inodeRefb`/`inodeIdent` (IcacheRef),
  `ientry*`, `ipool`/`regionInums`/`ciInums`/`icCiWf` (IcacheEscrowPool),
  `icId_quartersSplit`, `regionInums_spec`/`ciInums_spec`.
- **Needs** gate H1. No new MachCSL rule: all loads and stores are under the spinlock (sie = false).
- **Stale in Rocq.** ProofIget header 16–60 and the SpecIget header name superseded lemmas
  (`ic_open_empty_dev`, `ipool_take`, `iref_alloc_step`, `iref_incr_store_au`); follow the code.
- **Split** (suggested): ProofIgetParts (pure, message), ProofIgetTail, ProofIgetRecycle (+ panic
  arm), ProofIgetHit, ProofIgetScan (loop step, miss, free slot), ProofIget (prologue, acquire,
  assembly).

### 3.5 iupdate — MEDIUM-HARD (~1500 lines, 3–4 files)

- **Rocq.** SpecIupdate.v 1264 (`K_iupdate` l.121), ProofIupdate.v 2329, LinkIupdate.v 6.
- **Image.** `KA.«iupdate»` = 0x80003244, 126 B, 4-slot frame:
  - `lw 4(a0)` / **`srliw 4`** / `lw sb+0x18` / `addw` → bread(dev, IBLOCK)
  - `andi 15`/`slli 6` → the dinode slot
  - four **`lh`**→`sh` pairs, and `lw`→`sw` of size
  - `memmove(dip->addrs, ip->addrs, 52)` → log_write → brelse.
- **Budget.** `K = 66` (4 + bread 62). bslots 2.
- **Callees.** `BREAD`, `MEMMOVE` (52 B), `LOG_WRITE` (**range form, W1-LW**), `BRELSE`.
- **Contracts.** Six in Rocq. All six are sealed directly from ONE internal core, `iu_main_gen`
  (ProofIupdate.v 916–1988), via three region steps `iu_step_out`/`_link`/`_unlink` (125–394).
  The Spec banners at 652–663/1218–1223 claiming "credgen is primitive, derive the rest" are
  STALE.

  | form | Spec lines | downstream callers |
  |---|---|---|
  | `wp_iupdate_credgen_body` | 666–791 | ProofItrunc:362, ProofWritei:1218 |
  | `wp_iupdate_link_body` | 839–996 | ProofCreateAlloc, ProofCreateMkdir, ProofSysLink |
  | `wp_iupdate_unlink_body` | 1049–1156 | ProofCreateFail(Mkdir), ProofSysUnlinkW5D/F, ProofSysLinkTails |
  | sconf 125–287, gen 303–459, cred 475–639 | | no call sites (Module obligations and comments only; ProofIput's IUPDATE parameter is dead) |

  **Ship credgen, link and unlink as the `IUPDATE` fields.** Derive `gen` (and `sconf`, via
  `logOp_openS`/`logOpS_op`) as theorems only if each is under ~60 lines. `cred` is subsumed
  once `eb` collapses. Record the drop with the uses checked above.
- **Common premises and resources.**
  - Premises: `logGeomOk`, `IBLOCK inum ist ∈ cov`, `∉ logRegion`, `inum < 16·nib`,
    `diTypeStable dn dn0`, `diType dn ≠ 0`, `diAddrs dn = bmCells bm`, `(bmDir bm).length = NDIRECT`.
  - Resources: `iDev`/`iInum` cells, `inodeMeta ip dn`, `inodeMap`,
    `wordPointsTo sbInodestart 4 dqs _`, `iregInv`, `dinodeAt … inum dn0`, `bioCtx`, `logCtx`,
    `bslots 2`, bread's machine bundle.
  - Pinned `k.sie = false`, `noff = 0`, `locks = []` (bread).
- **Per-form differences.**
  - credgen: `logEpochLb v`, `logCredit cru Sb e0 IBLOCK`, `logOpSe (u+1) Sb e0` in;
    `logOpS (if cru then u+1 else u) (IBLOCK :: Sb)` + `∃ e, loggedAt e IBLOCK ∗ ⌜v ≤ e⌝` out;
    payout `iregOut`.
  - link: `diNlink dn = diNlink dn0 + 1`, `≠ 32767`, `iregLinkPin`, `linkToks` out.
  - unlink: the Z-form decrement, `linkToks` in.
- **Consumes** (present): `iregRead`, `iregWrite_au`, `iregWriteLink_reg`,
  `iregWriteUnlink_reg`, `diblkSlot_acc`, `dislotAcc`, `inodeAddrs_buf`, `diblkBytes_splice`,
  `izrcpt`, `iblkOf_IBLOCK`, `gammaByteRange`, the `logOpS_named`/`logCredit_own`/
  `logEpochLb_0`/`logOpSwe_opSw`/`logOpSw_witness` family, and the DinodeSlot helpers
  `dsSrliw4`, `dsAddwIbl`, `dsAndi15`, `dsSlli6`, `dsAlign`, `dsHold_k/_swap`, `dsBuf_bytes`,
  `dsSlots_split/_join`, `dsPay_content`, `dsHeld_L`, `wordPointsTo_byte_to2/_of2`.
- **Needs** W1-M1 (`wp_s_lh`) and **W1-LW** (the log_write byte-range form + `lwAuRec` +
  `lwRecWindow`). Without W1-LW there is no way to hand `iregWrite_au`'s record-granular fupd to
  log_write.
- **No panic, no racy read.**
- **Split.** ProofIupdateSteps (defs + the three region steps), ProofIupdateTail (+0x66..+0x7c:
  log_write, brelse, epilogue), ProofIupdateMain (+0x00..+0x62; cut at bread's return if slow),
  ProofIupdate (the seals).

### 3.6 ilock — HARD (~2000 lines, 3–4 files); LIVE PANIC; RACY READ

- **Rocq.** SpecIlock.v 809 (`K_ilock` l.204; `wp_ilock_dep_sconf_body` 205–465 PRIMITIVE;
  `wp_ilock_tx_sconf_body` 481–721; `wp_ilock_tx_of_dep` 734–774 IN THE SPEC FILE), ProofIlock.v
  2885, LinkIlock.v 7.
- **Image.** `KA.«ilock»` = 0x800032f8, 174 B, 4-slot frame (s2 saved lazily on the slow paths):
  - +0x0a `beqz a0`: dead → unreachable
  - **+0x0e `lw a5,8(a0)`: the RACY `ip->ref` read, no lock held**
  - +0x10 `blez`: dead → unreachable
  - acquiresleep(&ip->lock)
  - +0x1a `lw 64(s1)` (valid); `bnez` → return (cached arm)
  - uncached arm:
    - `srliw 4` + `lw sb+0x18` + `addw` → bread; slot address (`andi 15`, `slli 6`)
    - four **`lh`**→`sh`, `lw`→`sw` size, memmove 52, brelse
    - `sw 1 → valid`, `lh 68(s1)` (type)
    - `beqz` → **`panic("ilock: no type")` LIVE**.
- **Budget.** `K = 66`. One `bslot`.
- **Callees.** `ACQUIRESLEEP_LLB.wp_acquiresleep_gen_llb` (H := `slhTok (icfgIsl k)`,
  `q := s`, `tl := max Tl (maxStamp …)`), `BREAD`, `MEMMOVE`, `BRELSE`, `PANIC`.
- **Contract (dep form).**
  - Premises: `icDepShr d = some (s, icfgDev, inum, g, lo)`, `icDepRd d → ∃ ty, o = ShotK ty`,
    `k < NINODE`, `logGeomOk`, `IBLOCK inum ist ∈ cov`, `inum < 16·nib`, a0 = `ientry k`; pinned
    sie/noff/locks.
  - Pre:
    - `itableInv`, `icEscrow … k`, `iregInv`
    - `isSleeplockGen … (iLock ip) "inode" (icSlp cn k) (slhTok (icfgIsl k))`
    - the racy-read credential `⌜lo ≤ tl⌝ ∗ credFloor lo tl ∗ irefClaims`
    - the share `inodeShrGenlo k s dev inum g lo` (consumed)
    - `icDepSide d`, `iregWdLic o g inum`, `sbInodestart` cell, bread's bundle, `bslot`,
      `∀ Tl, topLb Tl`.
  - Post (`wpNext true`, `∀ dn bm filled`):
    - `sleeplockedQ`, `icHandle cn k d`, `offRows`
    - `iDev`/`iInum` ↦{½}, `iValid ↦ validWord true`
    - `icDepHeld … d k inum dn bm`, `ityShot g (diType dn)`, `ifreezeOff inum`
    - `⌜filled → freshShape dn⌝`, `iregWdBack o g inum`, `⌜ilkPost o filled dn⌝`
    - `∃K, Tl ≤ K ∗ ctxFloor curCtx K`.
- **Tx form.** Swaps `icDepSide d` for `logTx icfgLog` and `icHandle`/`icDepHeld` for
  `icTxDep`/`icLoaded`. Derive it in SpecIlock.lean exactly as Rocq does, with `logTx_halve` →
  dep form at `DepTx … (1/2)` → `icTxDep_intro`. Needs **W1-TX**. Lean shape: `structure ILOCK`
  with the dep field only, plus `theorem ILOCK.wp_ilock_tx` (the `ACQUIRESLEEP.wp_acquiresleep`
  pattern).
- **Both forms are live downstream.** dep: ProofCreate*, ProofFileread/stat, ProofSysOpenWalk,
  ProofSysUnlinkW2/3. tx: ProofIreclaim, ProofNamex, ProofFilewrite, ProofSysLink*, ProofSysChdir,
  ProofKexecACode.
- **LIVE PANIC** "ilock: no type" (SpecIlock header; survey §1d): allocatedness is not knowable
  here and the pool holds free inodes. Discharge against `PANIC` and drop the held sleeplock. Do
  NOT refute it. The +0x28 "ilock" arms (null ip, ref < 1) are DEAD, refuted by
  `ientry_unsigned`/`il_entry_nonzero` and by `inodeRef_spos` on the racy read's `0 < v`.
- **The racy read** (ProofIlock 2405–2475). `irefClaims_at` → `kctx_token_acc` (ownCtx) →
  `ownCtx_credFloor_vis` (IcachePinwObl:107) → `iref_readAU` (IcachePinwObl:139, over the share's
  `liveGenlo k s g lo`) → the load rule. Because ilock is pinned at sie = false, the existing
  `wp_s_lw_au` (hsie) suffices and the hart cannot move. W1-M2 (`wp_s_lw_au_key`) is the
  Rocq-faithful sie-generic leaf; use it if it has landed, otherwise `wp_s_lw_au`.
- **Checkout** (2587–2660). `icDepCheckout`, `kctx_token_acc`, `icCheckoutRd` (DepRd) or
  `icCheckout` (via `icBody_ofShr`, `icDepMass_ofShr`, `icDepSide_qSide`), then
  `icHdrHeld_validAcc`.
  - Cached arm (2698–2782): `icBundle_loadedElimHeld`, `frz_slot_kill_pinw`, `liveGenlo_agree`,
    `iregClaimNoOut`.
  - Uncached arm (2783–2862): `icBundle_unloadedElimHeld`, `icRaw_ofRest`,
    `ityPending_shot_excl`, then `il_load`.
  - Check how Lean's `icCheckout` (rd hard-coded false) and `icCheckoutRd` line up with Rocq's
    `ic_hdr_held … (ic_dep_rd d)`.
- **The fill** (`il_load`, 696–2236).
  - Bread, then `dsHeld_L` + `iregRead_blk` → `diblkBytes ds`, then `diblkSlot_acc`.
  - The three-case ghost fill (1114–1355) is a ghost-only lemma; stage it standalone. It covers
    the pool's allocated arm (`icInodeLeg_eraOpen`, `inodeOwnedEra_*`, `iregRead`,
    `iregClaimNoOut`), the marker over type 0, and the marker over nonzero type (`iregWithdraw`,
    `iregTopRetag_same`, empty bundle).
  - Then `ityShoot`, five field copies, memmove, brelse, `valid = 1`, the type test, then
    `icMkLoaded` → epilogue.
- **Missing.** `logTx_halve`/`logTx_join` (W1-TX), the proof-local `il_addrs_buf_upd`,
  `il_bmcells_empty`, `il_ind_res_empty`, `il_blocks_empty`, `il_payload`, `il_cont`.
- **Needs** W1-M1 (`lh`), W1-TX.
- **Stale in Rocq.** Headers name `iref_live_load_au`, `ic_swap_checkout`, `wp_lw_au_s_sconf`;
  the code uses `iref_load_pinw_au` + `iref_read_obl` + `ic_checkout(_rd)`. The panic-banner
  offsets are wrong. The `dq` binder is unused (drop it and record the drop).
- **Split.** ProofIlockParts (pure, message, empty-bundle lemmas, the fill and checkout ghost
  lemmas), ProofIlockLoad (`il_load`; cut at brelse if slow), ProofIlock (epilogue, main, the
  racy read, the tx derivation if not in Spec).

### 3.7 iunlock — MEDIUM (~500 lines, 1–2 files); RACY READ

- **Rocq.** SpecIunlock.v 370 (`K_iunlock` l.106; dep 107–204 PRIMITIVE; tx 211–303;
  `wp_iunlock_tx_of_dep` 307–338 in the Spec), ProofIunlock.v 861, LinkIunlock.v 6.
- **Image.** `KA.«iunlock»` = 0x800033a6, 64 B, 4-slot frame:
  - `beqz a0` (dead)
  - holdingsleep(&ip->lock); `beqz` (dead)
  - **`lw a5,8(s1)` racy ref read**; `blez` (dead)
  - releasesleep; all dead arms go to `unreachable`.
- **Budget.** `K = 26`.
- **Callees.** `HOLDINGSLEEP.wp_holdingsleep_gen`, `RELEASESLEEP_HOOK.wp_releasesleep_gen_hook`
  (hook `icSlp_fold`, `Rin := fun _ => icSlpDep cn k Tc`). Both are sie-generic.
- **Contract (dep).**
  - Premises: `icDepShr d = some (s,dev,inum,g,lo)`, `k < NINODE`, a0 = `ientry k`,
    `"sleep lock" ∉ k.locks`.
  - Pre: `itableInv`, `icEscrow`, `isSleeplockGen`, `sleeplockedQ`, `⌜lo ≤ tl⌝ ∗ credFloor ∗
    irefClaims`, `icHandle cn k d`, `∃ T, offRowsDep`, the ½ dev/inum cells, `iValid`,
    `icDepHeld`, `ityShot`, `ifreezeOff`.
  - Post: `wpNext k.sie` (no sleep), `inodeShrGenlo k s dev inum g lo` and `icDepSide d`.
  - Tx derived via `icTxDepAt_ofHalf` → dep at `DepTx … (1/2)` → `logTx_join` (W1-TX).
  - Callers: dep (ProofFileread/stat, ProofIunlockput); tx (ProofFilewrite, ProofIreclaim,
    ProofNamex, ProofSysChdir/Link/OpenTails).
- **Racy read** (422–513). It borrows the handle's `liveGenlo k ½ g lo` through
  `icHandle`/`icDeposit2`/`icPayLive_ofShr`, then `liveGenlo_agree`, `iref_load_pinw_au`,
  `iref_readAU`. (Headers saying `ic_open_out` are stale.)
- **Park** (565–600). `icDepHeld_bmLen`, `icDepHeld_introHeld`, `icPark … (IcLoaded g dn' bm')`,
  `icParkSide_depSide`, `icSlpDep_ofDep`, releasesleep, then `qsum_singleton` to rebuild the share.
- **sie.** Rocq's iunlock is sie-generic and so are both Lean callees, so KEEP IT sie-generic.
  That needs **W1-M2 `wp_s_lw_au_key`** (fs0d-pinw-design §5.1). Every present Lean caller runs at
  sie = false (all of them come through bread/ilock), so pinning iunlock to sie = false and using
  `wp_s_lw_au` is a possible fallback. It is a simplification, though: take it only with the
  coordinator's approval, and only if M2 stalls.
- **Needs** W1-M2, W1-TX.

### 3.8 balloc — HARD (~2500 lines, 5–6 files); LIVE printk ARM

- **Rocq.** SpecBalloc.v 415 (`K_balloc` l.132; sconf 133–254; **`wp_balloc_gen_body`
  255–374**), ProofBalloc.v 4458, ProofBallocParts.v 521, LinkBalloc.v 18
  (`Bread LogWrite Brelse MemsetArray PrintkGen`).
- **Image.** `KA.«balloc»` = 0x80002e54, 262 B, 80-B frame (s2..s8 saved only after the
  `sb.size` test):
  - `lw sb+4` / `beqz` (+0x12, dead from `0 < size`)
  - outer loop: `sraiw 13` + `lw sb+28` → bread(bitmap)
  - inner scan (+0xb6..+0xe6): `bgeu`, `andi 7`, **`sllw`**, the signed /8 sequence
    (`sraiw 31`/`srliw 29`/`addw`/`sraiw 3`), `add`, `lbu 88`, `and`, `beqz`, `addiw`×2,
    `bne s4 (8192)`
  - set path (+0x38): `or`, `sb 88`, log_write, brelse
  - bzero inlined (+0x4c..): bread, memset 1024, log_write, brelse
  - exhaust: brelse, `addw` b += BPB, `bgeu` (the second outer iteration is dead from
    `size ≤ BPB`)
  - out (+0xe8): `printk("balloc: out of blocks\n")`, return 0.
- **Budget.** `K = 72`.
- **Callees.**
  - `BREAD` (twice).
  - `LOG_WRITE.wp_log_write_au` (bitmap block; `logOpS_named` → `logCredit_own` (pure cr) →
    `bitmapAllocAu` → `lwAu_lb0` at `Efs = ⊤ \ ↑bitmapN`; after the call,
    `logOpSwe_opSw` → `logOpSw_witness`).
  - `LOG_WRITE.wp_log_write_gen` (the zeroed block, `cr = false`; takes `fsblock` at the old
    content from `freeBlk` plus `bufHold0 ∗ bioPay`).
  - `BRELSE`, `MEMSET.wp_memset` (the `byteBuf` form).
  - `PRINTK.wp_printk` (Lean's `PRINTK` is already the general-varargs form, so Rocq's
    `PRINTK_GEN` maps onto it; format `KStr.«balloc: out of blocks\n»`; credentials by the
    `panicEnv` pattern of `it_printk`).
- **Contract.** Ship `_gen` as the field and derive `_sconf` (Rocq 4407–4454: `logOp_openS` at
  `cr = false`, `logOpS_op`).
  - Premises: `logGeomOk`, `0 < size ≤ BPB`, `bmapstart ∈ cov`, `∉ logRegion`,
    `cr = true → bmapstart ∈ Sb`, a0 = sext dev; pinned sie/noff/locks.
  - Pre: `printk` credentials, `bioCtx`, `logCtx`, cells `sbSizeAddr`/`sbBmapstartAddr` (BitmapInv
    121/125), `bitmapInv γfs bms cov ls size` (persistent), `bslots 2`, `logOpS (2+u) Sb`.
  - Post, two arms:
    - FAIL: a0 = 0, `logOpS (2+u) Sb`.
    - SUCCESS: `∃ blk ≠ 0`, `blk ∈ cov`, `∉ logRegion`, `fsblock γfs blk (replicate BSIZE 0)`,
      `logOpS (if cr then u+1 else u) (blk :: bmapstart :: Sb)`.
  - Callers: ProofBmap:3635/3719 (gen only).
- **The out-of-blocks arm is LIVE.** Nothing in `bitmapRes` rules out a full bitmap, and this
  kernel returns 0 where stock xv6 panics (survey §1e.1). The two dead arms are +0x12 and the
  +0x98 fall-through.
- **Proof route** (stage lemmas, right to left, as Rocq):
  - `ba_epilogue` 346–602, `ba_out` 612–977, `ba_exhaust` 988–1206, `ba_restore` 1215–1466
  - `ba_bzero` 1476–2039 (`dsPay_content` = Rocq `iu_held_content`)
  - `ba_alloc` 2050–2500 (`bitmapOk_free`/`_nonzero`, `bitmapBytes_set_bit`)
  - **`ba_scan` 2518–3351**: fuel ≥ BPB − bi. The invariant is only `0 ≤ bi ≤ BPB`, the
    registers, `bslots 1`, the `bioLocked` of `bitmapBytes used`, `logOpS (2+u) Sb` and the `cr`
    fact; nothing about the bits already scanned.
  - `ba_main` 3381–4375 (`bitmapRead` via `dsHeld_L`).
  - Split `ba_scan` further into a `ba_scan_test` (+0xba..+0xdc) and the induction wrapper.
- **Consumes** (present): BitmapInv (`bitmapInv`, `bitmapRes`, `bitmapN`, `freeBlk(_intro)`,
  `bitmapOk*`, `bitmapBytes*`, `bitmapRead(Own)`, `bitmapAllocAu`, `logN_sub_diff_bitmapN`),
  BitmapEnc (`bmByte`, `bmBit_*_64`, `bmByte_and/lor_pow2_64`), FsStateBitmap (`freePool*`),
  `BBLOCK_single`, `oneBitmapBlock`, `fsblock*`, `bioLocked_split`, `bslots`.
- **Missing.** The `bal_*`/`ba_*` arithmetic of ProofBallocParts.v; port it as
  `Xv6/ProofBallocParts.lean` (the balloc agent owns it).
- **Needs** W1-M3 (`wp_s_sllw`).
- **Stale in Rocq.** "PRINTK as a hypothesis" (SpecBalloc 156); "gen pinned at eb = true"
  (4429); "A THIRD DEAD ARM" (there are two); drifted immediates in comments.
- **Split** (suggested): ProofBallocParts (pure), ProofBallocDefs (frame, arms, cont, borrows),
  ProofBallocTail (epilogue/out/exhaust/restore), ProofBallocBzero, ProofBallocAlloc,
  ProofBallocScan, ProofBalloc (main + seals).

### 3.9 bfree — MEDIUM (~900 lines, 2 files)

- **Rocq.** SpecBfree.v 373 (`K_bfree` l.102; **`wp_bfree_gen_body` 103–226**; sconf 228–332),
  ProofBfree.v 1862 (arith 112–440, defs 464–545, `bf_tail` 551–981, `wp_bfree_gen` 991–1815,
  `wp_bfree_sconf` 1816), LinkBfree.v 8.
- **Image.** `KA.«bfree»` = 0x80003004, 108 B, 4-slot frame:
  - **`srliw 13`**, `lw sb+28`, `addw` → bread
  - `andi 7`, `li 1`, **`sllw`**, `slli 51`/`srli 54` (b/8 mod 128), `lbu 88`, `and`
  - `beqz` → unreachable (DEAD, via `freePool_used` + `bmBit_test`)
  - `xori -1`, `and`, `sb 88`, log_write, brelse.
- **Budget.** `K = 66`. bslots 2.
- **Callees.** `BREAD`, `LOG_WRITE.wp_log_write_au` (with `bitmapFreeAu`, `freeBlk_intro`,
  `lwAu_lb0`), `BRELSE`.
- **Contract.** `_gen` as the field, `_sconf` derived (Rocq 1816: `logCredit_own false`).
  - Premises: balloc's geometry, `bno < size`, `bs.length = BSIZE`, a1 = sext bno; pinned.
  - Pre: `panicEnv` (bread needs it), the `sbBmapstartAddr` cell, `bitmapInv`,
    `fsblock γfs bno bs` (the freed block's exclusive run), `bslots 2`,
    **`logCredit γ cr Sb e0 bmapstart`** (a RESOURCE, at a named epoch; this is what lets itrunc
    group its 269 frees) and `logOpSe (u+1) Sb e0`.
  - Post: `logOpSe (if cr then u+1 else u) (bmapstart :: Sb) e0`.
  - Callers: ProofItrunc:1053/1605/2348 (gen only).
  - Note the ASYMMETRY with balloc: balloc's `_gen` takes a pure `cr` over `logOpS`; bfree's
    takes the `logCredit` resource over `logOpSe`. Do not unify them. itrunc needs bfree's form
    and bmap needs balloc's.
- **Missing.** The `bf_*` arithmetic (`bf_srliw13`, `bf_andi7`, `bf_sllw1`, `bf_slli51`,
  `bf_srli54`, `bf_test_val`, `bf_clear_val`, `bf_lnot_bridge`). Keep them in ProofBfreeParts.lean
  (or the top of ProofBfree.lean). The overlap with balloc's lemmas is a handful, and Rocq also
  keeps them separate, so do not create a shared file two agents would race on.
- **Needs** W1-M3 (`wp_s_sllw`).
- **Stale in Rocq.** ProofBfree header 17–19 calls the main lemma `wp_bfree_sconf`; it is
  `wp_bfree_gen`.
- **Template.** The survey's advice is to do bfree before balloc: bfree's `_gen` body is the
  template balloc's alloc arm copies.

## 4. Prerequisites (their own items; they edit or add MachCSL/existing files, coordinator-approved)

**W1-M1: `wp_s_lh`** (signed halfword load). Needed by stati, iupdate, ilock.
- Add `execSpecF_lh` + `wp_s_lh` beside `execSpecF_lhu`/`wp_s_lhu` (MachCSL/WpSmodeFrame12b.lean
  166/193). The instruction is `LOAD (imm, rs1, rd, false, 2)`; the result is
  `BitVec.signExtend 64 w`.
- Put it in a NEW file, `MachCSL/WpSmodeLh.lean` (and `sllw` below), to avoid editing existing
  files.
- Small: copy `lhu` and change the extension.

**W1-M2: `wp_s_lw_au_key`** (sie-generic racy lw; fs0d-pinw-design §5.1). Needed by iunlock;
optional for ilock.
- A 4-byte accessor load with no `hsie` premise. The accessor takes `lkFloor curCtx f` (or the
  `credFloor` pieces) and cashes it in-step against the running hart's `ownCtx cpu'` (from
  hexec's `ctxTok cpu'`, the pattern `wp_s_sw_mint` uses), then hands `readAU cpu' … K ts Ψ`.
- Templates: `wp_s_lw_au` (MachCSL/WpSmodeAuRules.lean:366) and `wp_s_sw_mint`
  (MachCSL/WpSmodeMint.lean:244). Rocq analogue: `WpAu4.wp_lw_au_rel_s_sconf`.
- About 150 lines. Also check that `iref_readAU`'s shape (IcachePinwObl:139) composes with it
  without the hart being fixed in advance. This is the one piece of real framework work in the
  wave.

**W1-M3: `wp_s_sllw`** (`RTYPEW … SLLW`). Needed by balloc, bfree.
- Copy `wp_s_addw`/`wp_s_subw` (MachCSL/WpSmodeRules.lean ~440–466).
- The result is `signExtend 64 ((rs1[31:0]) <<< (rs2 &&& 31))`. State it with the shift amount as
  `(k.rget cpu' rs2).toNat % 32` so the `1 <<< (bi % 8)` arithmetic is `omega`/`bv_decide`
  friendly.
- One agent can do M1 + M3 together (same file pattern, under an hour).

**W1-LW: the log_write byte-range form.** Needed by iupdate, and later ialloc and iput.
- SpecLogWrite.lean deviation 1 says "arrives with the inode wave"; this is that wave.
- Port Rocq SpecLogWrite.v:
  - `wp_log_write_au_range_body` (355–433)
  - `lw_au_whole` (435), `lw_au_rec` (475, over `FsStateDefs.byteRange (fsGammaL γfs)` via
    `gammaByteRange`, anchored at `logEpochLb_0`), `lw_rec_window` (508)
  - the range proof in ProofLogWrite.
- Rocq has the range form as primitive and the whole-block form as a corollary via `lw_au_whole`.
  Recommended: add `wp_log_write_au_range` as a new `LOG_WRITE` field proved in ProofLogWrite by
  generalising the whole-block proof, and re-derive `wp_log_write_au` from it (the Rocq
  structure). This EDITS SpecLogWrite/ProofLogWrite/LinkLogWrite, and every `LOG_WRITE` consumer must
  still build. Today the only consumers outside the triple are the mentions in
  `Xv6/WriteiBudget.lean`; re-grep `LOG_WRITE` first. It is coordinator-approved, own agent, and must be
  done before iupdate's tail stage.
- If the edit is judged too wide, a separate `structure LOG_WRITE_RANGE` in a new
  `SpecLogWriteRange.lean` + `ProofLogWriteRange.lean` + `LinkLogWriteRange.lean` is the fallback.
  The coordinator decides.

**W1-TX: `logTx_halve` / `logTx_join`** (Rocq LogInv.v:836/844:
`logTx γ ⊢ ∃ t, txPin γ t ½ ∗ txPin γ t ½` and back). Needed by the tx derivations of ilock and
iunlock.
- Tiny; add to Xv6/TxPin.lean (coordinator edit), or to a new `Xv6/TxPinHalve.lean`.
- Check first that `logTx` (LogDefs:573) and `txPin` (TxPin) unfold compatibly.

**Gate H1:** `Xv6/IcacheTable.lean` committed (idup, iget).

## 5. Dependency order and batch schedule

The nine functions are mutually independent: their callees are all outside fs.c. What orders them
is the prerequisites above. One agent owns one function's triple (plus that function's `*Parts`
files). Nobody edits a file another agent owns.

**Batch W1-A (6 in parallel, start now):**
- A1 MachCSL leaves: W1-M1 `wp_s_lh` + W1-M3 `wp_s_sllw` (new MachCSL file).
- A2 MachCSL: W1-M2 `wp_s_lw_au_key`.
- A3 W1-LW (log_write range form + `lwAuRec`/`lwRecWindow`/`lwAuWhole`) + W1-TX.
- A4 namecmp (needs nothing).
- A5 idup (gate H1).
- A6 iget (gate H1).

**Batch W1-B (6 in parallel; each starts as soon as ITS prerequisites land, not the whole batch):**
- B1 stati: A1.
- B2 bfree: A1 (sllw). Start it early; it is balloc's template.
- B3 balloc: A1. Its Spec file, pure Parts and the epilogue/out/exhaust/bzero stages need no
  sllw and may start at once.
- B4 ilock: A1 (lh), A3 (TX). Parts/checkout/fill ghost lemmas may start at once.
- B5 iunlock: A2, A3 (TX). SpecIunlock + the park lemma may start at once.
- B6 iupdate: A1, A3 (LW). The region-step lemmas (ProofIupdateSteps) may start at once.

Pairing advice from the survey: ilock + iunlock share the dep/tx derivation, and bfree + balloc
share the credited-log argument. They are separate owners; let each pair read the other's Spec as
it lands.

**Critical path:** A3 (the LW edit) → iupdate, and the two HARD proofs: iget (A6) and
ilock (B4, which waits only on the quick A1/A3-TX). balloc is the longest single proof but has no
downstream in this wave.

**After wave 1:** bmap (balloc), ialloc (iget), itrunc (bfree + iupdate); see survey §7.3.

## 6. Risks

1. **W1-LW is a cross-cutting edit** to the landed LogWrite triple. If its statement shape is
   wrong, iupdate, ialloc and iput all move. Port Rocq's `wp_log_write_au_range_body` literally
   (the view as a parameter, the list set) and keep `wp_log_write_au`'s current statement
   unchanged as the corollary.
2. **W1-M2 is the only real framework work.** If it stalls, iunlock blocks (ilock does not). The
   fallback (iunlock at sie = false) is a simplification and needs coordinator sign-off per the
   user's rule.
3. **idup/iget are the first consumers of the AU load/store movers over `itableInv`**
   (`iref_load_locked_pinw_au`, `iref_upgrade_mir/incr_store_pinw_au`,
   `iref_alloc_pinw_install`, `irefPinRows_push/_mint`) and of IcacheTable (H1). Expect statement
   mismatches in the landed 0d files. Report them as exact edits; do not work around them locally
   by restating a mover.
4. **Live panics must stay live:** iget's "no inodes" (while holding itable.lock; the
   `noff + 3 < 2^31` and "pr"/"uart1" premises pay for it) and ilock's "no type". Also balloc's
   out-of-blocks printk arm. Adding an allocatedness or non-full premise would make the contracts
   unusable by namex/ialloc/bmap.
5. **The `sie`/`locks` pinning** (bread, acquiresleep) collapses Rocq's `eb`/`b` genericity for
   iupdate/ilock/balloc/bfree. That is consistent with every existing Lean fs-cone caller, but
   record it in each Spec header. For stati/namecmp/idup/iget/iunlock keep Rocq's genericity.
6. **iupdate's six → three contracts** is a cleanup. The uses were checked (§3.5); re-grep before
   dropping, and keep `iu_main_gen` general enough that sconf/gen are one-screen corollaries if a
   later wave wants them.
7. **Proof speed.** iget, ilock and balloc are 2.6–4.5k-line Rocq proofs. Follow the stage
   decomposition above; Lean `k_step` proofs usually run 2–4× shorter than Rocq. Any theorem that
   takes more than a few seconds gets split before the file is reported done.
8. **Stale Rocq prose** (headers of ProofIget, ProofIlock, ProofIunlock, SpecIupdate banners,
   SpecBalloc) names superseded lemmas. The CODE is the reference; the survey agents confirmed the
   live names listed above.
9. **namecmp's list/function seam** must suit dirlookup (wave 4). Look at ProofDirlookup's call
   before fixing the Spec shape.

## 7. Report (per agent)

- Files with line counts and the last line of each build.
- The slowest theorem's elaboration time (`set_option profiler true` spot-check).
- Every deviation from Rocq with its reason, and every cleanup as "item — uses checked — reason".
- Every landed name reused.
- Any edit an existing file needs (exact old → new), in particular statement mismatches found in
  the 0d movers or IcacheTable.
