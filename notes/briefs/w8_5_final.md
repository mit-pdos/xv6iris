> **USER RULINGS (2026-09-26):** USER (the user-mode machine layer, D24) is to be PROVED next (after the xv6 checkpoint). Himg is to be DISCHARGED on the actual fs.img, as Rocq's FsImgCheck/FsImgDisk do (in progress).
> **USER RULINGS (2026-09-25):** D46 = abstract GF + concrete xv6GF spike (promote when it lands). D47 = FIX THE BOOT IMAGE IN THE LANGUAGE (MachCSL: boot memory a language constant, as Rocq's boot_image) — no BootImage premise. D48: the user's real target is the APPLICATION adequacy theorem, UNION adequacy in particular (Rocq UUnionBootAdequacy via App.xv6_app_adequacy at AppUnionRec.app_union); the xv6 trace/system theorem is a checkpoint. ORDER: finish the xv6 system theorem FIRST, then union. D49 = port Rocq's single application-interface record (App.v), since union plugs into it (coordinator recommendation after plain-language re-explanation; user did not object).

# Brief: batch 8-5, the final xv6 system theorem (BootShared, BootChain, SystemAdequacy)

Surveyed Sept 25 2026 against `lean-v2` @ `de4a093f3` and `/shared/xv6rocq/iris` on `main` @ `f22c1c9ca`.
The standing rules are `notes/coord/wave7b_prompt.txt`, wave8_top.md §0 rules 1–3, and crash_layer.md.
USER RULINGS already in force: D23 (Rocq's full theorem, crash durability included), D24 (`USER` is an
explicit parameter), D34 (`Himg` is a premise), D37 (generic application slot, as Rocq), and BootReset
in wave 9 (the reset table `resetVal`/`bootFacts` is TRUSTED until then).

> **DECISIONS PENDING (user).** Numbering continues from crash_layer.md's D45. Each has a
> recommendation.
>
> | # | decision | recommendation |
> |---|---|---|
> | **D46** | **What `GF` the final theorem is stated at.** Rocq's audit target `xv6_fs_adequacy_xv6Σ` is at the CONCRETE functor list `xv6Σ`, so "nothing about the ghost state is assumed" is checked. Lean has no concrete `BundledGFunctors` anywhere in the tree. iris-lean offers `BundledGFunctors.set` but has no `subG`-style precedent. A concrete list would need about 25 `ElemG`/`GhostMapG`/`GhostVarG` instances to resolve through it. | **(a) State the final theorem at an ABSTRACT `GF`**, taking `[MachGpreS hlc GF]` plus the capacity-only classes as instance arguments. That is Rocq's `xv6_power_adequacy Σ` level. Every NAME-bearing class is minted inside the era fupd (§4). **(b) Run a parallel spike, SA-G `Xv6/Xv6GF.lean`**, that builds `xv6GF` with `.set` and instantiates (a). If the spike lands, its corollary becomes the audited final theorem. If not, record it as a deviation. |
> | **D47** | **The kernel-image premise.** Rocq's language fixes boot memory to the literal ELF (`RiscvLang.boot_mem`), so it has no premise. Lean's `GState.image` is arbitrary: `powerInterp` pins it to `MachFixedGS.bootImage` and `bootFacts σ g.image` holds at every boot. The carve takes `BootImage image` as a premise (BootCarve deviation 1). | **(a) `Hkimg : BootImage g.image` is a premise of the final theorem**, beside `Himg`. It is recorded as a statement about the hardware setup (the loaded kernel), not about the software. Its discharge by a bounded computation against the ELF dump is a later step (the D34 precedent). (b) The alternative is making the image a language constant in MachCSL. That is invasive, and it breaks MachCSL's kernel-agnosticism |
> | **D48** | **Which corollaries 8-5 ports.** D23 fixes the durability theorem. Rocq also has the trace family `xv6_trace_adequacy(_xv6Σ)` and `xv6_obs_wf_xv6Σ` (well-formed observable trace at the image). | **Port them in the same file, after the main theorem.** They are cheap (about 150 lines) because `MachCSL.riscvTraceAdequacy` and `obsLedgerAt_*` already exist. They are droppable if they cost more than a day |
> | **D49** | **The application interface of the GENERIC theorem.** Rocq's `xv6_power_adequacy_gen` takes `Ai : CT → app_iface` (tag family, kill credential and console claim as ONE record) and `Tnn` (the era's turn, a PowerOn yield handed to `<init>`). Lean's MachCSL record has the three slots `Tg`/`Kc`/`Cres` in place of `Ai` and does not port `Tnn` (Adequacy.lean header). | **(a) State the generic theorem over what MachCSL has**: `Tg`/`Kc`/`Cres` in place of `Ai`, no `Tnn`, and `Hinit_boot` without the turn argument. Record it as an inherited deviation. The `Unit` instance, and hence the final theorem, is unaffected, because `Tnn = emp` there. (b) Add `Tnn` to `powerBootRes`/`Hobs` first. That needs a MachCSL worktree, and only echo-style applications need it (out of scope, D23) |

## 0. Findings that shape the plan (read first)

1. **`USER` enters in exactly one place.** The closed trap loop, forkret and the syscall seal are all
   linked without `USER` (`LinkUserretClosed`, `LinkForkret`, `LinkForkretParkPaid` take no
   parameters, SpecUserretClosed deviation 8). `USER` is consumed only by the GENERIC application's
   discharge of `Hinit_boot`:
   `UexecExecMint.initBootBundle_of_mint (appSup) (uKillCred) (consLicence) (□ uexecWp)`, where
   `□ uexecWp` is `(ProofUexecWp.uexecWp_gen US).…`. This matches Rocq `init_boot_of_sup` (`UG.uexec_wp_gen`).
   So the GENERIC theorem `xv6PowerAdequacyGen` is `USER`-free, and `USER` is a parameter of the
   `Unit` instance and of the final theorem only.
2. **The crash/durability side is essentially complete in Lean.** C-4 and C-5 landed:
   - `pFs_alloc`/`pFs_project`/`pFs_swap`/`pFsLendAt`, `imgPDurAlloc`;
   - `fsRecovery_total/_det/_clean/_restrict`, `hdrWf_zero`, `fsRecView(_len/_raw/_slot)`;
   - `fsSnap_topAcc`, `fsSnap_readOk_keep`, `appDurRaw(_open/_pack/_clone)`, `appGuest`;
   - `fsCrashSeamAt`/`fsCrashSeam_ofAt`, `logMirrorBorn`, `fsExtent_ofImage`, `fsBootPure`;
   - `fsCfgAllocSnap(_wf)`, `fsGeomOk_ofWf`, `firstFsinitPures_ofWf`, `fsBootSupply`.

   What is missing on that side is only SystemAdequacy's own glue (§5, SA-4).
3. **The long pole is the BOOT CARVE AND THE ERA MINTS, not the crash layer.**
   - `mainGlobalsRaw`/`mainLocksRaw`/`mainLogRaw`/`mainSbRaw` have NO producer. `SpecMain` is their only
     mention, and BootCarveMain stops at bcache/kmem/kinit.
   - There is no per-hart `.bss` carve (`cpus[c]`, `cpuCtxFree`, boot stack slice).
   - There are no UART ghost/invariant mints and no `SchedNames` mint.
4. **Two landed statements are unusable at the top as they stand.**
   - `SpecBoot.wp_boot_body` takes the GOT word at `DFrac.own 1`. Eight harts cannot share that. Rocq
     uses `↦ₚ₈□` (discarded). `SpecEntry` is already `dq`-generic, and ProofBoot instantiates it at
     `own 1`.
   - `SpecMainSecondary.mainDeposit` (and hence `MAIN_SECONDARY`, and SpecMain's recipe) takes
     `pd pav pu` as PARAMETERS. `started_alloc` must fix the payload `P` before main runs, while
     `virtio_disk_init` picks the pages by `kalloc`. Rocq's `main_deposit` has them `∃`-bound. The
     edit is forced (G6).
5. **Stale texts (fix while passing):**
   - BootHart deviation 3 and BootBridge deviation 4: `MachCSL.resetVal` now pins
     `mstateen0`/`sstateen0` (`Lang.lean:281`), so `bootHartRes` is UNBLOCKED.
   - DiskBoot deviation 3: `riscvPowerAdequacy`'s `Hboot` now receives `∃ ds0, σ.devs = ds0.reset`.
   - wave8_top §5.1: SystemAdequacy.v is now 2318 lines, RiscvAdequacy.v 2027.
   - SpecMain deviation 5 bullets: rewrite once W8-N lands.
6. **`notes/coord/pending_edits.txt` has no separate C-4/C-5 "handoff" section.** The handoff items
   are its C-2b line (C-4's list), the FsCfgKits and FileBoot lines, W8-I gaps (a)–(g), and the
   C-4/C-5 file headers (FirstTok, FsCfgSnap, FsCfgSnapFirst, FsBootSupply). §6 wires every one of them.

---

## 1. (a) Rocq: BootShared / BootChain / SystemAdequacy

| file | lines | key items |
|---|---|---|
| **SystemAdequacy.v** | 2318 | §1–2 helpers: `cpu_enum_cons`, `big_sepL_cpu_split/peel/glue`, `cov_facts_of_image`:165, `app_xfer_boot_raw`:230 (+`_persistent`, `app_xfer_raw_of_boot`:241, `_triv`:253), `cons_res_triv_founded`, `turn_triv_founded`, `app_dur_at`:293 (+`_pack`:298, `_agree`:307), `fs_boot_supply_uart`:327, **`xv6_slot`:354**, **`xv6_slot_project`:365**, `fs_trace_hook`:385, **`xv6_trace_pure`:423**, `xv6_trace_hook`:429. Section SystemBoot: **`xv6_boot_era`:~560–1006** (one era's `Hboot`, about 450 lines). §2b `init_boot_of_sup`:1027, `init_boot_of_triv`:1056. §3 **`xv6_power_adequacy_gen`:1075** (statement to :1195, proof to :1605), `xv6_power_adequacy`:1611 (unit app), `xv6_trace_adequacy`:1682. §4 `xv6Σ`:1903, `fsimg_image_wf`:1955, `fsimg_snap_ok`:2022, `xv6_power_adequacy_xv6Σ`:2096, **`xv6_fs_adequacy_xv6Σ`:2150**, `xv6_trace_adequacy_xv6Σ`:2184, `xv6_obs_wf_xv6Σ`:2271 |
| **BootShared.v** | 2436 | geometry lemmas :101–258; §BootBss `boot_hart_stack_raw`:294, `boot_cpu_slot_raw`:351; §BootBssChain `boot_hart_bss`:459, **`boot_bss_carve`:497** (to :1019); `main_data_raw`:1159, UART word pins :1185–1250; §BootAlloc `hart_strans/sie/spp/spie/locks/resv`, **`power_boot_res_unpack`:1373**, `boot_hart_pre_combine`:1506, `boot_hart_pre`:1542, **`boot_shared_alloc`:1603** (statement to :1860, proof to :2436; calls `fs_cfg_alloc_snap` at :2281) |
| **BootChain.v** | 534 | `boot_entry_bridge`:114 (reset → `<main>` → sconf), `boot_hart_secondary`:274, **`boot_hart_primary`:329** (about 200 lines of premises: the whole boot supply) |
| RiscvAdequacy.v | 2027 | `power_boot_res`, `boot_fixedGS`, `riscv_power_adequacy`, `disk_proj_trace`, `power_interp_disk_auth`, `riscv_trace_adequacy` (**Lean: MachCSL/Adequacy.lean, landed**) |
| BootCarve / BootCarveMain | 1943 / 2441 | Lean 633 / 292 |
| BootHart / BootBridge / BootConfig | 440 / 529 / 662 | Lean 229 / 251 / 210 |
| BootReset / ColdBoot / PowerBoot | 878 / 409 / 195 | **wave 9** (reset table trusted). PowerBoot's witness state is Lean's `resetRegs_resetWith` |

**The final statement** (SystemAdequacy.v :2150):
```
Corollary xv6_fs_adequacy_xv6Σ (g : gstate)
    (Hgen0 : g.(ggen) = 0) (Hpow : g.(gpow) = false)
    (Hdisk : v_disk (g.(gdev).(dvirtio)) = FsImgDisk.fsimg_dk) :
  ∀ t2 g2, rtc erased_step ([PowerLoopE], g) (t2, g2) →
    (∀ e2 ∈ t2, reducible e2 g2) ∧ xv6_trace_pure fsimg_cov (sb_logstart fsimg_sb) g2.
xv6_trace_pure cov ls g := fs_boot_pure cov ls (v_disk …) ∧ (gpow g → resv_ok g)
fs_boot_pure cov ls dk := fs_extent ∧ ∃ D, fs_recovery (fs_blocks dk) D cov ls ∧ hdr_wf ∧ ∃ S, snap_ok S D
```
The ladder is `xv6_power_adequacy_gen` (generic app, `Himg` premise) → `xv6_power_adequacy` (unit
app) → `_xv6Σ` (concrete Σ; `Himg` discharged from `Hdisk` by `fsimg_image_wf`) →
`xv6_fs_adequacy_xv6Σ` (`phi := xv6_trace_pure`, via `xv6_trace_hook`). With D34, Lean stops one rung
short of `Hdisk`: `Himg` stays.

## 2. (b) What Lean already has

| piece | Lean state |
|---|---|
| **MachCSL/Adequacy.lean** (602) | `powerAdequacyCore`, **`bootFixedGS`** (the record literal: crash fields `diskName/diskSize/bootImage/crashPred/swapName`, the slots `Tg/Kc/Cres`, obs), **`riscvPowerAdequacy`** with Rocq's hooks `Hbirth, Pc/HPc, Ppure/Hproj, Mof, Rb, Hswap, Pt/HPt, Hobs, phi/Hphi, Hboot` (`Hboot` is told `F = bootFixedGS …`, gets `bootFacts σ g.image`, `∃ ds0, σ.devs = ds0.reset`, `Ppure (diskOf σ.devs)`, `obsInv ∗ powerBootRes Mof (Rb c) E gen σ`, and owes `[∗list] hartWP` and `[∗list] d ∈ DevId.all, devWP`), `powerInterp_era`, `powerInterp_mmOk`, `obsPredAt(_alloc/_alloc_cl/_step)`, `obsLedgerAt*`, `bootFixedGS_obsPredTriv`, `riscvTraceAdequacy`. **Missing:** Rocq's `disk_proj_trace` and `power_interp_disk_auth` (G7) |
| **The boot image** | pinned: `powerInterp g ⊢ ⌜g.image = MachFixedGS.bootImage⌝`, and `bootFixedGS … g.image …`. `BootCarve.BootImage image` (a structure: ram/text/rodata/got/data/bss) is the carve's premise (D47) |
| MachCSL/Power.lean | `powerBootRes` (kpt root var, `genCertAt`, reg cells, `memCells`, `∃ξ ctxTokAt` per hart, `lockSetAt`, kmap auth plus `kmapStaticAt`, **`wireInvAt E`**, dev frags, `consRes (gen+1) [] ⟨⟩`, mirror half at `Mof (diskOf σ.devs)`, `swapLb (gen+1)`, `Rb gen (diskOf σ.devs)`, `crashInv`), `MachGS.ofEra E gen cP cI eP ePe`, **`wpLoop_ofEra`** (`genCertAt ∗ wpLoop ⊢ hartWP`), `ownCtx_boot` |
| BootConfig / BootHart / BootBridge | `regCellsEx(_take/_takeList/_takeListAt)`, `mBoot_of_cells`, `entry_sym_addr`; `spOf`, `bootStack_rw`, `bootEntryPre(_ofEra)`, `bootGprRest`; **`bootBridge`** (sConf + gprFile + stack words + stvec + `cpus[c]` words + lockSet + hartCsrs + ctxToken + clock ⊢ `kctx cpu (bootKCtx R n)`). **Missing:** `bootHartRes` (BootHart dev 3, now unblocked) |
| BootCarve / BootCarveMain | `bootRan*`, `bootRo`, `bootRan_persist`, `kernelText_intro`, `kernelData_intro`, `bootImg_ctxBytes`, `bootImg_wordAtN(_ex/_bss)`, `bootCarve_image/_owned/_got/_era`; `bootBss_cellAt(_ex)`, `bootBss_wordAt`, `bootCarve_buf/_bcache/_lockWords/_kmem/_kinitRun` (discharges `bdBss`). **Missing:** everything `mainGlobalsRaw`/`mainLocksRaw` names, `.data` rows, per-hart `cpus[c]`/context/stack (G2, G3) |
| DiskBoot / FsBoot | `diskBootAlloc` (dead `diskInv` sealed with the device mirror, `diskCfgOwn`, `diskInitGhosts`, `diskRoot`, **crashPermInv sealed**, block image `diskBlock γ b (fsBlocks v.disk b)` for `b < nb`); `fsCovIn(_0)`, `fsBootCarve`, `fsBootGhosts`, `fsHomeList` |
| FsCfgBoot / FsCfgSnap* / FsBootSupply | `fsBootImageWf` (Rocq's 15 conjuncts), `fsBootSnapWf` (9 rows); **`fsCfgAllocSnap(_wf)`**: diskBlocks ∗ `▷ appPred appRun (absView S.fssInodes)` ∗ `appXfer` ∗ `fsCrashSeamAt appGuest cov ls` ∗ `fsSnap …` ⊢ `|={E}=> ∃ I F, fsCfgSnapPost I F …` (= `fsBootSupply` at `Rspent := snapSpent S nib`, `Xexc := hdrWset …`); `fsGeomOk_ofWf`, `firstFsinitPures_ofWf`; `fsBootSupply(_open/_ties/_appInv)` |
| FirstTok (after C-4) | Rocq-literal rows: `firstBootPersist` carries `fsCrashSeam fscCov fscLogst ∗ genCert`; `firstFsinit` holds kit 2, `logMirrorBorn (mirrorOf (fsBlocks dk))`, the pure block; `fsabsEnv` back; `fsExtent_ofImage`, `colGeom_ofConfig` |
| FsCrash* / FsDur* / AppDur / FsBootParams | `pFsAt`, `pFsRecNamedAt`, **`pFsNamedAt`**, `pFsLendAt`, **`pFs_project`** (its pure output IS `fsBootPure` at `N`), **`pFs_swap`**, **`pFs_alloc`**, `pFsRecNamed_wf`; `pFsComp`, `fsCrashSeamAt`, `fsCrashSeam(_ofAt)`; `pDurAt`, `fsSnap`, `snapGuest`, `fsSnap_topAcc`, `fsSnap_readOk(_keep)`, `pDurAt_tie`; **`imgPDurAlloc`**, `imgSnapOk`; `appDurRaw(_open/_pack/_clone)`, `appGuest`; `XV6_DISK_BYTES`, `fsimgCov`, `fsimgNib`, **`fsBootPure`** |
| SpecMain / SpecMainSecondary / LinkMainSecondary | `MAIN` (provisional, deviation 5), `mainDepositRecipe`, `mainGlobalsRaw`, `mainLocksRaw`, `mainUartRaw`, `mainHartRaw`; `MAIN_SECONDARY`, `mainDeposit` (**pd pav pu as parameters**, G6); `LinkMainSecondary.MainSecondary : MAIN_SECONDARY` (closed) |
| Boot path | `LinkBoot.Boot : BOOT` (closed; GOT at `own 1`, G3) |
| Device loops | `wpDev_uart_inv` (needs `uartObsPermit`), **`wpDev_uart_inv_triv`** (obsPred/rxTag triv), `wpDev_plic_inv` (`plicInv ∗ wireInv ∗ genCert`), `wpDev_disk_inv` (`diskInv ∗ genCert ∗ diskDrainEnv ∗ diskRoot`) |
| Generic app / user | `appSup_of_triv`, `consLicence_triv`, `consEchoShift_triv`, `initBootBundle_of_mint`, `uexecWp_gen : USER → UEXEC_GEN`, `SpecUser.USER` |
| Mints | `started_alloc`, `plicInv_alloc`, `wireInv_alloc` (unneeded: `wireInvAt E` comes from `powerBootRes`), `consGhostsAlloc`, `consCredInv_alloc`, `devswTable_alloc`, `fileBoot_ghostsAlloc`, `fdSlots_alloc`/`bslots_alloc`/`irefSlots_alloc` (∃ class instance), `childrenRes_alloc` (∃ `WchG`), `lockGhostAlloc`, `procsInv_alloc`. **Missing:** UART ghosts + `uartInv` (both ports), `SchedNames` + `procsAvailAt (some NPROC) true` + hart/pstate rows, a fresh `ctxStamped` context (G4, G5, G7) |

**What 8-5 needs from W8-N (`LinkMain.Main : MAIN`, closed, no parameters).** `MAIN.wp_main_boot` in
this form. Rows marked ★ differ from today's SpecMain.
- `X`, `Γ [ClaimIs]`, `γ0 γ1 γc γl0 γl1 γd γdl γt`, `[EnvIs … Γ γ0 γ1 γc γl0 γl1 γd γdl γt]`,
  `cpu k cn l0 l1 c0 dk sb nib cov ndisk S Pb` ★`Rspent` `tlb0 γi ξd`. **★ No `pd pav pu`
  parameters.**
- Keep the pure premises `hcpu hX hK hsie hnoff hlocks hproc hl0 hl1 hdead hcn hsnap`. **★ `hties` is
  gone.**
- Resources:
  - `kctxL false cpu k ∗ pcIs cpu mainAddr ∗ cpuCtxFree cpu ∗ mainHartRaw cpu tlb0`;
  - `startedInv γi ξd P ∗ startedPrim γi`, with ★ `P := mainDepositE Γ γ0 … γt` fixed, or `P`
    abstract with a recipe that is `□ ∀ pd pav pu γpr root t M, … -∗ P X.curCtx` (Rocq);
  - `consEchoShift ∗ mainLocksRaw ∗ mainGlobalsRaw cn` (★ plus `[∗list] k ∈ range NFILE, fentryRaw
    curCtx k`, per pending FileBoot);
  - `first ↦ 1 ∗ nextpid ↦ 1`, hart/pstate rows, `procsAvailAt Γ (some NPROC) true`, `childrenBoot`;
  - `lockFreeTok` for `γc γl0 γl1 γt` and `Γ.lock i` (★ no `γdl`, which is tied to `fscDlock` per
    Rocq, pending FileBoot/FsCfgKits (3));
  - ★ `fsBootSupply dk sb nib cov γ0 γd cn Rspent Pb (hdrWset (fsBlocks dk) sb.sbLogstart)`;
  - `logMirrorBorn (mirrorOf (fsBlocks dk)) ∗ irefSlots IREFBOOT ∗ irefSlotsAuth ∗ genCert ∗
    fsCrashSeam cov sb.sbLogstart`;
  - ★ `initBootBundle ROOTINO.toNat fdt0` (linear);
  - `uartInv ×2 ∗ plicInv γ0 γ1 ∗ diskInv γd ∗ wireInv ∗ mainUartRaw ×2 ∗ diskCfgOwn γd c0 ∗
    diskInitGhosts γd ∗ diskInitCells …`;
  - kpt root var, `kmapName ↪●MAP KernelMap.static`, `pageRange kinitBase kinitPages`.
- Conclusion: `⊢ wpLoop cpu`.
- The trampoline claim `kmapAt trampVpn` is minted INSIDE main (kvminit), not a premise. `DISK_INIT_WM`
  is retired. `FsGeomOk`/`firstFsinitPures`/`firstBootPersist`/`firstFsinit` are built INSIDE ProofMain
  (Rocq ProofMain `mn_grp_fs`) from `hsnap` + the supply ties.

If W8-N keeps an abstract `P`, BootShared instantiates it at `mainDepositE` (below). Either way the
secondary's payload must be the SAME `P`.

## 3. (c) The Lean statement

New definitions, in `Xv6/SystemSlot.lean`:
```lean
/-- Rocq `xv6_trace_pure`. -/
def xv6TracePure (cov : ExtTreeSet Nat compare) (ls : Nat) (g : GState) : Prop :=
  fsBootPure cov ls (diskOf g.m.devs) ∧ (g.pow = true → mmOk g.m)   -- Lean's mmOk carries resv_ok

/-- Rocq `xv6_slot`: the crash slot = the FS record at its snapshot map ∗ the app's durable claim there. -/
def xv6Slot {CT : Type} (N : Type) (appFs : CT → N → Aview → IProp GF)
    (cov : ExtTreeSet Nat compare) (ls : Nat) (γd γsw γreg γst : GName) (c : CT) : IProp GF :=
  iprop(∃ gt : GName, pFsNamedAt gt γd XV6_DISK_BYTES γsw γreg γst cov ls ∗ appDurRaw (appFs c) gt)
```

The final theorem, in `Xv6/SystemAdequacy.lean` (the Lean analogue of `xv6_fs_adequacy_xv6Σ` at
D34/D46(a)/D47):
```lean
theorem xv6FsAdequacy (US : USER)                                   -- D24
    {hlc : HasLC} {GF : BundledGFunctors} [MachGpreS hlc GF]
    -- CAPACITY-ONLY classes (no gnames); the exact list is the union of the binders of
    -- MAIN / BootShared / FsCrash's section, which SA-7 computes and reports:
    [Xv6G GF] [WchGpre GF] [CtokG GF] [DiskG GF] [IcacheG GF] [IcboxG GF] [LogG GF]
    [FsBlocksG GF] [IregG GF] [FsTopG GF] [FsLinkG GF] [SleepLockG GF] [BcacheG GF]
    [OffboxG GF] [OffboxBoxG GF] [FileG GF]
    (g : GState) (sb : FsSb) (nib : Nat) (cov : ExtTreeSet Nat compare)
    (Hgen0 : g.gen = 0) (Hpow : g.pow = false)
    (Hkimg : BootImage g.image)                                          -- D47
    (Himg : fsBootImageWf (diskOf g.m.devs) XV6_DISK_BYTES sb nib cov)   -- D34
    (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
    (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
    (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ xv6TracePure cov sb.sbLogstart g2
```
- The NAME-bearing classes (`FdslotG BioslotG IrefslotG WchG Icfg Fscfg Appcfg`, plus `ClaimIs`/`EnvIs`)
  are NOT binders. They are minted per era and used under `letI`, like Rocq's `fileGpreS` → `∃ HF`.
- `KernelMap`/`KernelGeom`/`KernelImage` are Xv6's global instances.
- `UexecSG` is the concrete `uexecSGXv6`.

**Premises, in full:**
- `US : USER`, the only assumed interface (D24);
- `Hgen0`/`Hpow`, as Rocq;
- `Hkimg` (D47, Lean-only);
- `Himg` (D34; Rocq discharges it from `Hdisk`).

**Trusted, not in the statement:** MachCSL's reset table (`resetVal`/`bootFacts`/`bootShape`, the
language's PowerOn), until BootReset (wave 9). Record this in the header, beside Rocq's
`SystemAssumptions` note.

**The rungs above it** (same file):
- `xv6PowerAdequacyGen`: USER-free, generic application (D37/D49). Its parameters, in Rocq order:
  - `CT Cl Hbirth`, `N appFs`, `appBoot`;
  - `Tg/Kc/Cres` (+ instances) in place of `Ai`;
  - `Happ_boot : ∀ c k, ⊢ appXferBootRaw (appFs c) (appBoot c k)`;
  - `Happ_init : ∀ c, ⊢ |==> ∃ r, appFs c r (absView (imgState (fsBlocks (diskOf g.m.devs)) sb nib).fssInodes)`;
  - `Hkill_sup`, `Hout_sup` (at `Cres`);
  - `Hinit_boot : ∀ E-classes … [Appcfg GF], appcfg = ⟨N, appFs c, r⟩ → record-slot equations →
    ⊢ appInv fscFs -∗ appBoot c (gen+1) r ==∗ initBootBundle ROOTINO fdt0`;
  - `Happ_echo : ∀ …, ⊢ consEchoShift`, `Pt HPt Hobs`;
  - `Hperm` (the per-port `obsInv -∗ uartObsPermit i γ`, at the era's `fscUart`);
  - `phi Hphi`, `Hgen0 Hpow Hkimg Himg`.
- `xv6PowerAdequacy (US)`: the `Unit` instance, `phi` free. It uses `appSup_of_triv`,
  `consLicence_triv`, `consEchoShift_triv`, `wpDev_uart_inv_triv`, `obsPredAt`, and
  `initBootBundle_of_mint … (uexecWp_gen US)`.
- `xv6FsAdequacy`: `phi := fun g _ => xv6TracePure cov sb.sbLogstart g`, via `xv6TraceHook`.
- D48: `xv6TraceAdequacy`, `xv6ObsWf`.
- The optional literal-geometry corollary at `fsimgCov`/`fsimgNib` needs a Lean `fsimgSb`, which does
  not exist yet (deferred with D34's discharge).
- Keep the `nsteps` form of `riscvPowerAdequacy`. Add an `-·->ₜₚ*` (erased-steps) corollary only if
  iris-lean has the `erased_steps_nsteps` bridge.

## 4. (d) Proof plan

### 4.1 Hooks of `riscvPowerAdequacy` (ndisk := `XV6_DISK_BYTES`, `Pc := xv6Slot N appFs cov ls`, `ls := sb.sbLogstart`)

| hook | runs | instantiated with | pieces |
|---|---|---|---|
| `Hbirth` | once, first | client's (unit: `∃ ()`) | — |
| `HPc` | once, at the initial image `dk0 := diskOf g.m.devs` | **`xv6Slot_alloc`** (SA-4) | `fsRecovery_total` → `D0`; `hdrWf_zero` + `fsimgWf_log` (image log clean) → `hhwf`; `fsRecovery_clean` rewrites `D0 = fsRestrict (fsBlocks dk0) home`; `imgPDurAlloc … Himg` → epoch + `snapGuest gt (imgState …).fssInodes`; **`pFs_alloc`** → `pFsAt`; `Happ_init c` → `r`; pack `pFsNamedAt` (`∃ dk := dk0`, the fragments from `HPc`'s premise, `fsExtent` from **`fsExtent_ofImage`** off `Himg`'s conjuncts 1/6/7/8) and `appDurRaw` (the guest half is `snapGuest`, by `rfl`) |
| `Ppure`/`Hproj` | every PowerOn | `fsBootPure cov ls` / **`xv6Slot_project`** | `appDurRaw` framed, **`pFs_project`** at `N := XV6_DISK_BYTES` (its pure output is `fsBootPure` verbatim) |
| `Mof` | every PowerOn | `fun dk => mirrorOf (fsBlocks dk)` | — |
| `Rb` | every PowerOn | `fun c gen dk => ∃ gt r, pFsLendAt gt cov ls dk ∗ ▷ appDurAt (appFs c) gt r ∗ appBoot c (gen+1) r` | — |
| `Hswap` | every PowerOn | **`xv6Slot_swap`** (SA-4) | open the slot; `appDurRaw_open` → `(r, I)`; **`pFs_swap`** (mirror born at `Mof dk`, half into custody, `swapLb (gen+1)`, cloned lend `∃ gt', pFsLendAt gt' … ∗ snapGuest gt' I`); `Happ_boot c (gen+1)` (`appXferBootRaw`) copies the claim and yields `appBoot c (gen+1) rnew`; `appDurAt_pack` onto `gt'`; re-pack the slot. Place every conjunct BY NAME (Rocq's note: no bare `iframe` past the 2 MB disk big-op) |
| `Pt`/`HPt`/`Hobs` | birth / every power event | unit: `obsPredAt γobs`, `obsPredAt_alloc_cl`, `obsPredAt_step … consResTriv` | generic: client's |
| `Tg`/`Kc`/`Cres` | record slots | unit: `rxTagTriv`/`killCredTriv`/`consResTriv` | generic: client's (D49) |
| `phi`/`Hphi` | end of the run | `xv6TracePure` / **`xv6TraceHook`** | `powerInterp_mmOk` (pure, spends nothing), then **`diskProjTrace`** (G7: `powerInterp_diskAuth` lends `diskFixedAuth (diskOf g'.m.devs)` out of `powerInterp`'s last conjunct) applied to `xv6Slot_project` |
| `Hboot` | every era | **`xv6BootEra`** (§4.2) | — |

**Per power cycle:**
- **PowerOff**: `Hobs` only (history += `PowerOff`; the durable auth is lent and returned).
- **PowerOn** at `gen`: `Hobs` (history += `PowerOn`, founding `Cres c (gen+1) [] ⟨⟩`), then
  `Hproj` → `Ppure (diskOf σ.devs)`, then `Hswap` → mirror/`swapLb`/`Rb`, then `Hboot` on
  `powerBootRes Mof (Rb c) E gen σ`.
- Crashes need nothing: `crashInv` (fixed layer) is opened only at virtio's drain (C-M/C-2) and by
  `Hproj`/`Hphi`.

### 4.2 One era: `xv6BootEra` (Rocq `xv6_boot_era`), in order
1. `subst` the record equation. `crashPred` is now `xv6Slot … c` by `rfl`. Destructure
   `fsBootPure` into `hext, D, hrec, hhwf`.
2. **Unpack `powerBootRes`** (a Lean analogue of Rocq's `power_boot_res_unpack`: pure conversion,
   no mint). It yields:
   - `kptRootName` var, `genCertAt gen E` (= `genCert` at `ofEra`, `rfl`);
   - per-hart `regCellsNoPins`, `memCells E σ.mem`, per-hart `∃ ξ, ctxTokAt`, per-hart `lockSetAt [];`
   - kmap auth and `kmapStaticAt E`, `wireInvAt E`, the four `devFragAt`s;
   - `consRes (gen+1)`, the mirror half, `swapLb (gen+1)`, `Rb`, `crashInv`.
3. **The lend → the era's fs state** (Rocq :680–750):
   - `∃ gt r`, `pFsLendAt` → `D0`; `fsRecovery_det` makes `D0 = D`.
   - `pDurAt` → `gsn gln S`, `fsSnap`.
   - `fsSnap_topAcc` + `appDurAt_agree` → `▷ appFs c r (absView S.fssInodes)`.
   - `fsSnap_readOk_keep` (`fsRecovery_blocks_full`) → `snapOk`.
   - `Pb := fsRecView (fsBlocks dk) D`. Build `fsBootSnapWf dk XV6_DISK_BYTES S Pb S.fssSb (fsNib S) cov`
     from `fsRecovery_restrict`, `fsRecView_len/_raw/_slot`, `hhwf`, and `covFacts_ofImage Himg`
     (`fsCovIn`, log region ⊆ cov, `ls = 2`, the last pinning `S.fssSb.sbLogstart = sb.sbLogstart`).
   - Rewrite `fsSnap`'s map to `fsRestrict Pb home`.
   - This is one lemma, `xv6LendUnpack` (SA-4).
4. **The seam** (C-4 item): `fsCrashSeamAt (appDurRaw (appFs c)) cov ls` holds by `iintro !>`
   (both directions are the identity once `crashPred` is unfolded at the literal). Then
   **`fsCrashSeam_ofAt`** gives MAIN's `fsCrashSeam cov sb.sbLogstart`. `appGuest` at the era's
   `Appcfg := ⟨N, appFs c, r⟩` is `appDurRaw (appFs c)` by `rfl`, so the same term feeds
   `fsCfgAllocSnap`.
5. **The mirror** (C-4 item): `logMirrorBorn (mirrorOf (fsBlocks dk))` is the mirror half plus
   `swapLb (gen+1)`, definitional at `ofEra E gen` (`logMirrorHalf` = `E.mirrorName` half, `genId = gen`).
6. **Names first, then the instance.**
   - Mint `Γ` (G5), `γ0 γ1` (G4), `cn` (`consGhostsAlloc`), `γd` (inside `diskBootAlloc`), the lock
     tokens `γc γl0 γl1 γt` (`lockGhostAlloc`), `γi`, and a stamped `ξd` (G7).
   - Then `letI : MachGS := ofEra E gen (procClaim Γ) … (envFam Γ γ0 γ1 γc γl0 γl1 γd γdl γt) …`,
     with `ClaimIs`/`EnvIs` by `⟨fun _ _ => rfl⟩`/`⟨fun _ => rfl⟩`. `γdl` is `fscDlock`, so the fs
     record has to be built before `EnvIs`. Build the record with `fsCfgSnapRec` at pre-minted names,
     or take `EnvIs` after the mint. Both are fine because `envP` is only read by kernelvec at run time.
7. **`bootSharedAlloc`** (§4.3) runs at the boot hart's `CurCtx := ⟨ξ0, .bare⟩` (ξ0 is hart 0's
   `ctxTokAt` witness, taken BEFORE the carve, Rocq :770).
8. `initBootBundle` from `Hinit_boot` (unit: `initBootBundle_of_mint` with `uexecWp_gen US`).
   `consEchoShift` from `Happ_echo`.
9. **Harts**: split `cpus` at hart 0 (Rocq `cpu_enum_cons`/`big_sepL_cpu_peel`). Hart 0 gets
   `bootHartPrimary`, the others `bootHartSecondary`. Each yields `wpLoop`, then `wpLoop_ofEra` gives
   `hartWP gen cpu`.
10. **Devices**:
    - `wpDev_uart_inv(_triv)` for `.uart0`/`.uart1` (the permit from `Hperm`, or `uartObsPermit_triv`
      at `bootFixedGS_obsPredTriv` + the `rxTagTriv` literal);
    - `wpDev_plic_inv` (`plicInv γ0 γ1 ∗ wireInv ∗ genCert`);
    - `wpDev_disk_inv` (`diskInv γd ∗ genCert ∗ diskDrainEnv γd ∗ diskRoot γd`, where
      `diskDrainEnv = crashInv ∗ crashPermInv gen γd.cperm`, both in hand).

    The order matches `DevId.all`.

### 4.3 `bootSharedAlloc` (Rocq `boot_shared_alloc`)
Inputs: the unpacked `powerBootRes` rows, `BootImage g.image`, `fsBootSnapWf …`,
`▷ appPred appRun (absView S.fssInodes)`, `appXfer` (= `appXferRaw_ofBoot (Happ_boot …)`),
`fsCrashSeamAt appGuest cov ls`, and `fsSnap …`.

Steps, in Rocq's order:
1. **Read-only image**: `bootCarve_era` gives `kernelText ∗ kernelData ∗ kmapStatic` (`KernelImage.ro`)
   and the owned half `[_data, PHYSTOP)`.
2. **GOT** (W8-J deferral, part 1): `bootRan_persist` the eight GOT bytes. Each hart gets
   `pwordPointsTo stack0Slot 8 DFrac.discard KA.«stack0»` at its OWN context (a new
   `bootRo_ctxBytes`, G3). This needs SpecBoot to be `dq`-generic, which Rocq's `↦ₚ₈□` is.
3. **Per-hart `.bss`** (W8-J deferral, part 2, Rocq `boot_bss_carve`):
   - for each `c`, the `cpus[c]` cells (`aCpuProc/Noff/Intena`) plus `cpuCtxFree c` (14 context words
     in a fresh stamped context, `viewLb c 0`), and hart `c`'s `stack0` slice;
   - the slice gives `wp_boot_body`'s four frame words and `bootBridge`'s `bootStackSlots` words
     (`bootImg_wordAtN_bss`);
   - the slices `[stack0 + 4096c, +4096)` are disjoint by `bootRan_stride`.
4. **Globals** (G2): `mainLocksRaw`, `mainGlobalsRaw cn`, `mainSbRaw`, `mainLogRaw`, `first ↦ 1`,
   `nextpid ↦ 1`, `uarts[]` words (`mainUartRaw`), `diskInitCells`, `pageRange kinitBase kinitPages`
   (`bootCarve_kinitRun`), bcache (`bootCarve_bcache`), `fentryRaw` ×NFILE.
5. **Ghost mints**:
   - `fdSlots_alloc`, `bslots_alloc`, `irefSlots_alloc` (split `IREFBOOT` + `NPROC*(1+IREFSPARE)` +
     `NFILE`);
   - `childrenRes_alloc` (∃ `WchG`, `childrenBoot`), `Γ` rows (G5);
   - `consGhostsAlloc`, `devswTable_alloc`, `fileBoot_ghostsAlloc`;
   - `plicInv_alloc`, UART ghosts + `uartInv` ×2 (G4), `diskBootAlloc` (the block image over
     `ndisk / BSIZE`).
6. **The fs mint** (C-5): **`fsCfgAllocSnap_wf fsCfgSnapRec`** on
   `diskBlocks ∗ ▷ appPred appRun … ∗ appXfer ∗ fsCrashSeamAt appGuest ∗ fsSnap`. It gives
   `∃ (I : Icfg) (F : Fscfg), fsCfgSnapPost …`, which is `fsBootSupply … (snapSpent S nib) Pb (hdrWset …)`.
7. **The handover**:
   - `started_alloc ⊤ ξd P 0` with `P := mainDepositE Γ γ0 γ1 γc γl0 γl1 γd γdl γt` (the
     `∃ pd pav pu` deposit, G6); hand out `startedPrim γi`;
   - the recipe for MAIN (if W8-N keeps it) is `iintro` + `iexists pd pav pu` + `iframe`, as in
     Rocq's BootChain §5.
8. **Output**: everything `bootHartPrimary` takes, everything `bootHartSecondary` takes per hart,
   and the device-loop inputs.

### 4.4 `BootChain` (Rocq `BootChain.v`)
- **`bootEntryBridge`**: `bootEntryPre_ofEra` + the GOT `□` word + stack words ⊢
  `Boot.wp_boot` (`BOOT`, `dq`-generic) → its continuation → `bootBridge` → `kctx cpu (bootKCtx R n)`
  plus `mainHartRaw` (tlb and trap CSRs taken off `regCellsEx … bootEntryTaken`) plus `pcIs mainAddr`.
  Also state the Lean `bootHartRes` here or in BootHart (BootHart deviation 3 is unblocked).
- **`bootHartSecondary`** (`fin c ≠ 0`): `MainSecondary.wp_main_secondary` at `startedInv γi ξd P`.
- **`bootHartPrimary`** (`c = 0`): `Main.wp_main_boot` with the whole supply. `hK : mainSlots ≤ n`
  holds because `mainSlots = 114 ≤ 510 = bootStackSlots` (prove by `decide`; recheck after W8-N).

## 5. (e) Gaps

| # | gap | severity | owner |
|---|---|---|---|
| G1 | **MAIN's final statement and a closed `LinkMain`** (§2 box: `fsBootSupply` row + `Rspent`, `initBootBundle` row, `fentryRaw`, no `pd pav pu` params / `∀ pd` recipe, no `lockFreeTok γdl`, trampoline minted inside, `DISK_INIT_WM` retired) | **blocker** | W8-N (in flight) |
| G2 | **Main-globals carve**: no producer of `mainLocksRaw`/`mainGlobalsRaw`/`mainSbRaw`/`mainLogRaw`/`.data` rows/`diskInitCells`/`fentryRaw`. This is Rocq BootCarveMain's remaining ~2.1k lines plus BootShared `main_data_raw`/UART word pins. Rows mix `.bss` cells at `curCtx` with ghosts (`parentsResAt`, `ticksResAt`, `consResAt`/`consReader`/`consCleanTok`, `killPaidAt` in `procPubRest`, `bdBss`) | **high** (largest item) | SA-3a/SA-3b |
| G3 | **Per-hart**: GOT word at `DFrac.discard` per hart (+ `bootRo_ctxBytes`) and **SpecBoot/ProofBoot `dq`-generic** (landed edit; `SpecEntry` is already `dq`-generic, and ProofBoot just instantiates it at `own 1`); the `cpus[c]` carve + `cpuCtxFree`; boot-stack slices; `bootHartRes` | **high** | SA-2 (+ SA-E for SpecBoot) |
| G4 | UART ghost + `uartInv` mint for both ports (Rocq `WpUart.uart_ghosts_alloc`/`uart_inv_alloc`; `UartNames` has 8+ gnames incl. `init` one-shot). No Lean counterpart | medium | SA-1 |
| G5 | `SchedNames` mint: `hartFull Γ i 0`, `pstateFull Γ i UNUSED`, `procsAvailAt Γ (some NPROC) true`, `used`/`park` names, `lockFreeTok (Γ.lock i)` ×NPROC (Rocq mints these in `power_boot_res`; Lean's framework has no NPROC, so the client mints) | medium | SA-1 |
| G6 | `SpecMainSecondary.mainDeposit` → Rocq's `∃ pd pav pu` (`mainDepositE`), and `ProofMainSecondary`/`MainSecondaryParts` re-proved (one `idestruct` more). Forced: `started_alloc` precedes `virtio_disk_init` | medium (small edit, landed files) | SA-E (or fold into W8-N) |
| G7 | MachCSL: `powerInterp_diskAuth` + `diskProjTrace` (Rocq `power_interp_disk_auth`/`disk_proj_trace`); a fresh stamped context `ctxStamped_boot : ⊢ \|==> ∃ ξ, ctxStamped ξ 0 ∗ …` (Rocq `ctx_stamped_alloc`, for `cpuCtxFree` ×8 and `ξd`) | low | SA-M |
| G8 | SystemAdequacy glue: `covFacts_ofImage`, `appXferBootRaw` (+ persistent, `_ofBoot`, `_triv`), `appDurAt` (+ `_pack`, `_agree`), `xv6Slot`, `xv6Slot_alloc/_project/_swap`, `xv6LendUnpack`, `fsTraceHook`, `xv6TracePure`, `xv6TraceHook` | low (all ingredients exist) | SA-4 |
| G9 | Concrete `xv6GF` (D46b) | decision / spike | SA-G |
| G10 | `BootImage g.image` discharge (D47) and `Himg` discharge (D34) | deferred (premises) | later |
| G11 | Deviations to record in the headers, none new: no `Tnn`/echo window (D49); record slots `Tg/Kc/Cres` for `Ai`; client-side hart/pstate mint (G5); block-granular era disk image (DiskBoot deviation 1); no SIE ghost (D27); reset table trusted (wave 9) | — | each file |
| G12 | Stale notes (§0.5) | trivial | SA-2 / SA-7 |

Nothing on the crash side is missing beyond G7/G8: C-4's items all have landed producers (§4.1–4.2).
FsCfgKits' open items are closed: binit/kinit are at the configured names (`a59c9a1d9`).

## 6. (f) Agent split (disjoint files), order, and axioms

Rules: wave7b prompt conventions; stage files without the `Proof` prefix; one function per file does
not apply (these are adequacy files, not kernel functions); no theorem over a few seconds; carve files
under `ulimit -v 40000000; timeout 300` (memory: lean-runaway-memory, and Rocq's "no bare iFrame past
the 2 MB disk big-op").

**Wave A (start now, parallel; main tree, new files only):**

| agent | files | Rocq | needs |
|---|---|---|---|
| **SA-M** | `MachCSL/AdequacyDisk.lean` (`powerInterp_diskAuth`, `diskProjTrace`), `MachCSL/CtxBoot.lean` (`ctxStamped_boot`) | RiscvAdequacy `power_interp_disk_auth`/`disk_proj_trace`; TsoCtx `ctx_stamped_alloc` | — |
| **SA-1** | `Xv6/UartBoot.lean` (UART ghosts + `uartInv` mint, both ports), `Xv6/ProcBoot.lean` (`SchedNames` mint + rows + proc lock tokens) | WpUart `uart_ghosts_alloc`/`uart_inv_alloc`; ProcAvail `procs_avail_alloc`; `power_boot_res`'s proc rows | — |
| **SA-2** | `Xv6/BootCarveHart.lean` (GOT `□` per hart, `bootRo_ctxBytes`, `cpus[c]` cells, `cpuCtxFree`, stack slices; `bootHartRes`) | BootShared §BootBss/§BootBssChain :272–1019, BootHart §3 | SA-M (`ctxStamped_boot`) |
| **SA-3a** | `Xv6/BootCarveProc.lean` (procs raw rows, `pChan`/`procPubRest`/`pPid`, `parentsResAt`, `initproc`, `ticksResAt`, devsw, kmem freelist, `kernel_pagetable`, `.data` `first`/`nextpid`/`uarts` words, `mainUartRaw` cells, cons ring `consResAt`/reader/clean) | BootCarveMain `boot_procs_raw`, `boot_ctx_cells`, `boot_cons_res`, `main_data_raw`, UART pins | SA-1's names (UART rows only) |
| **SA-3b** | `Xv6/BootCarveFs.lean` (`mainLocksRaw`, `mainSbRaw`, `mainLogRaw`, itable `sleepLockIn`/`ientryRaw`, ftable `fentryRaw`, bcache head, `diskInitCells`) | BootCarveMain `boot_main_locks_raw`, `boot_inode_entries`, `boot_file_entries`, `boot_log_raw`, `boot_disk_slots` | — |
| **SA-4** | `Xv6/SystemSlot.lean` (G8) | SystemAdequacy §1–§2 (:140–450) + the lend-unpack of `xv6_boot_era` (:680–760) | SA-M |
| **SA-E** (worktree, serial, small) | `SpecBoot`/`ProofBoot`/`LinkBoot` (`dq`-generic GOT); `SpecMainSecondary`/`ProofMainSecondary`/`MainSecondaryParts` (`mainDepositE`, ∃ pd pav pu). Report old→new contracts. **Coordinate with W8-N**: `mainDepositRecipe`'s arguments must match; if W8-N has not started SpecMain's recipe, hand it the SpecMainSecondary change instead | SpecMainSecondary `main_deposit`; SpecBoot's `↦ₚ₈□` | — |
| **SA-G** (spike) | `Xv6/Xv6GF.lean` (concrete functor list via `BundledGFunctors.set`, instances for every capacity class of §3) | `xv6Σ`:1903 | D46 |

**Wave B (after W8-N's `LinkMain`, SA-1..SA-4, SA-E):**

| agent | files |
|---|---|
| **SA-5** | `Xv6/BootSharedDev.lean` (device + proc + slot mints, at the unpacked `powerBootRes`), `Xv6/BootSharedFs.lean` (the fs mint call + supply routing), `Xv6/BootShared.lean` (`powerBootRes_unpack`, `bootSharedAlloc`) |
| **SA-6** | `Xv6/BootChain.lean` (`bootEntryBridge`, `bootHartSecondary`, `bootHartPrimary`) (can start on MAIN's STATEMENT before LinkMain lands, since it applies `MAIN` as a hypothesis until `Main` exists) |

**Wave C:**

| agent | files |
|---|---|
| **SA-7** | `Xv6/SystemBootEra.lean` (`xv6BootEra`), `Xv6/SystemAdequacy.lean` (`xv6PowerAdequacyGen`, `xv6PowerAdequacy`, **`xv6FsAdequacy`**, D48's trace corollaries, `#print axioms`); `Xv6.lean` imports reported |

**`#print axioms xv6FsAdequacy` expectation.** The baseline was measured on `Xv6.UserretClosed` at
`de4a093f3`. It must be exactly:
- the Lean core axioms `propext`, `Classical.choice`, `Quot.sound`;
- the six Sail platform externs (`LeanRV64D/RiscvExtras.lean`): `cancel_reservation`,
  `load_reservation`, `match_reservation`, `valid_reservation`, `plat_term_write`,
  `sys_enable_experimental_extensions`;
- the auxiliary `…._native.bv_decide.ax_*` axioms that `bv_decide` emits per lemma (388 already at
  UserretClosed; the count will grow). These are `Lean.ofReduceBool`-class trust in the compiled
  decision procedure, and they are listed so a reader can tell them from a regression.

Any `sorryAx`, any `Xv6.*`/`MachCSL.*` plain `axiom`, or any other `_native` kind is a regression.
`USER`, `BootImage g.image` and `Himg` appear as HYPOTHESES in the statement, not as axioms. The
reset table is inside MachCSL's language definition (trusted by construction, wave 9). Add a
`notes/` baseline listing with the six externs by name, the analogue of Rocq's "adequacy-print
baseline".

**Every commit:** `timeout 3500 lake build Xv6 MachCSL` + `tools/check_layering.sh` + sorry grep
(memory: root build before push).
