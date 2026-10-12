VERDICT: NOT SATISFIED

# Review R26 of `notes/weak-allocproc-plan.md` (rev 29)

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git or jj, no subagents).  Every cite
below was read at the working-copy tip of `../xv6iris-weak` (plan mtime 2026-10-12 01:51).  Scope per the R26 brief:
verify that rev 29 applied R25's three required changes correctly ([R25.1] `Cust.pte` + `pteDiscAt` + the `chainOkAt`
exemption; [R25.2] W8-β′ pinned to three Lean statements incl. the (r2) twin now; [R25.3] R-ctx's 21 files incl.
`ProofSwtch`/`PipeBirth`), and decide whether **W8-β′** and **R-ctx** are launchable as written.  W4 F9 and W5 CORE
are RUNNING and were not re-reviewed (R25 found them launchable; nothing in rev 29 touches their briefs — `:1195-1197`,
`:1221-1225` unchanged in substance).  Items (a)/(b) of the standing brief were settled in R1–R25 and are not re-opened
(`tools/ci/roots.txt:6,19`, `tools/audit/baseline.json:11,63`, `tools/tcb/expected.json:509,2194` — unchanged).

**Sign-off.**  NO — two required changes, both S text in W8-β′'s brief, no owner question.  **All three R25 fixes
are applied correctly** (every `:N` in rev 29's new text resolves to the named declaration at the tip; details
below).  **R-ctx is LAUNCHABLE as written.**  **W8-β′ is NOT**: **[R26.1]** its deliverable (ii) is pinned on a
registry inclusion stated in the WRONG direction — "MachCSL registry ⊆ `xv6LockWord σ`" (`:1205`, `:2638-2639`,
`W8-design.md:452-453`) is FALSE at reachable states (`pipealloc` runs `initlock(&pi->lock)` BEFORE `(*f0)->pipe =
pi`, `Xv6/SpecPipealloc.lean:10-12`; `fileclose` unlinks the end BEFORE `pipeclose` reclaims, `Xv6/SpecFileclose.lean:
10-12`), and the extraction `reservedOk σ reg → lockWordDiscAt σ` needs the CONVERSE (`xv6LockWord σ b t → b ∈ reg`);
**[R26.2]** deliverable (i) leaves `reg` unbound and the registration MECHANISM unnamed: the state interpretation is
updated only inside the `swp` step rules, so neither `newlock_written` (`|={E}=>`, `Lock.lean:682-687`) nor
`lock_pay_born` (`|==>`, `:488`) nor `lkFresh`'s consumer can deposit "half of each reserved byte" into it; the
registry needs a NEW era gname (the only existing lock ghost, `lockSetName`, is a per-hart set of HELD lock NAMES,
`Ctx.lean:96-101` — not an address registry), which touches `EraGS`/`MachGS` (`Resources.lean:105-135,420-438,
476-477`), `MachGS.ofEra` (`Power.lean:771-776`), the era minting at PowerOn, `PowerText.lean`'s twin and the nine
`Xv6/` files that build `MachGS` instances — not in the "6–8 MachCSL files" list, and it makes W8-design §8's "no
PowerOn hook" claim partly false.  Both are plan text in the sound direction (proof organisation; every option
FAITHFUL — the published quantifier and conclusions do not move).

## What was checked and holds

- **[R25.1] applied correctly.**  Header `:3-10`; skeleton `:2509-2538`: `Cust` gains `| pte` with the kernel-table
  comment (`:2509-2512`), `chainOkAt` gains `custAt σ a e.t ≠ .pte →` (`:2524`), `pteDiscAt` is declared with the
  `KptInv.pteVariant`/`kptBody` pointer (`:2526-2529`), `xv6AccessDisc` is the six-way conjunction (`:2537-2538`);
  the "SUPERSEDED at the three `pte` points" sentence and the Spec-for-the-record line `:2544-2550` are present; the
  reachable counterexample `:2550-2558` is correct; W11 (i)'s "PTE bytes need NO arm" `:2684-2686`; R-ctx's `pte-key`
  arm `:1216-1217`, `:2612-2615`; the census's **C6** row `:2411-2414` and the exclusion list's correction `:2416-2417`;
  `:510`'s `menvcfg = ADUE | STCE … FIOM = 0`; §A(4) `:330` and §B(2) `:582` point at `pteDiscAt`.  Every cite holds:
  `KptInv.lean:4-8` (the shared table, concurrent A/D write-back), `pteVariant :38-41`, `kptBody :85`;
  `WpPtWalk.lean:3-7` (`read_pte`/`read_pte_exclusive`/`write_pte_conditional`), `swp_read_pte :48-57`,
  `swp_write_pte_conditional :156-165` (`exclWriteAU`), `swp_update_and_write_pte_kpt :455-470` with `hadue`;
  `Lang.lean:151-156` (`MState.store … (hartAgent cpu)`), `:373-375` ("or a page-table walk"), the plain arm `:400`
  (`σ.afterLoad`); `TsoMem.lean:354-356`/`:361-363`; `WeakKptStale.lean:26` ("PINNED at `.WCexcl`");
  `SpecStart.lean:29,40` (`menvcfg := 0xA000000000000000` = bits 63 STCE, 61 ADUE); `TransPt.lean:310` (`hadue :=
  hok.2.2.2.2`); `BootCarveProc.lean:348` (`kernel_pagetable = 0x8000a408`); `KernelImage.lean:17614` (`fence.i`),
  `SpecUserret.lean:6`.  ✓
- **[R25.2] applied as text.**  `:1200-1209` and `:2652-2658` pin the three statements (i) `⌜reservedOk σ reg⌝` beside
  `⌜mmOk σ⌝` in `memModelAt` (`Resources.lean:951-956` ✓ — `memModelAt` ends in `⌜mmOk σ⌝`), (ii)
  `powerInterp_accessDiscβ`, (iii) `xv6DiscAdequacy_closed` at `lockWordDiscAt ∧ cpuStaticAt`, registered in the three
  files; the lane `:1978-1983` and §C W8 (5)/(6) `:2635-2644` re-sized; the recorded alternative `:2581-2582`.  The
  (r2) twin's pattern is right: `xv6TextAdequacy_closed` (`LinkTextAdequacy.lean:26-31`) is the shape quoted at
  `:2539-2542`; `PowerText.lean:9-30` explains why W3 needed a PowerOn TRACE hook (the window had to be persisted
  while the era was being minted), which β′'s facts — conjuncts of `memModelAt` — do not need.  But see [R26.1] and
  [R26.2]: as text the pins are there; as a BRIEF two of them cannot be executed as stated.
- **[R25.3] applied correctly.**  `:1210-1215`, `:2617-2624`: 21 files; counts by grep at the tip — `ctx_absorb` 6/3,
  `ownCtx_floor_view` 8/4, `ctxStamped_raise` 5/2, `lockHook_llb` 13/10, `ownCtx_key_vis` 3/2, `ctx_unstamp` 1,
  `ctx_park` 3 (2 files), `ctx_move` 1 (`ProofForkretPark.lean:250`; `:21,34` and `ForkretRecord.lean:16,35` are
  prose), `kctx_move_in/out` 5 in `ProofSwtch.lean:251,253,268,270,274` + 1 in `ProofScheduler.lean:1000`,
  `lock_pay_born` 1 (`PipeBirth.lean:303`; the other four hits are prose) ✓; all 21 files exist; `lkFresh` in 30
  `Xv6/` files ✓; the output table's handoff and walker rows and the `notes/W8-Rctx.md` deliverable `:2659` ✓.
- **R-ctx as written (`:1210-1221`, `:2610-2624`, `:2658-2660`).**  Read-only, no build, no Lean edit; inputs named
  (the 21 files, the law list with counts, the floors `SpecRelease.lean:164-169`/`BcacheLock.lean:132`/
  `SpecAcquire.lean:96-103`, `DiskInvDefs`/`ProofVirtioDiskIntr`); the invariant to check against is named
  (`W8-design.md:343-344`); the categories CHAINED / DEVICE-KEY / PTE-KEY / RESISTS and the two extra rows are
  pinned; deliverable `notes/W8-Rctx.md`.  Nothing in [R26.1]/[R26.2] changes R-ctx's inputs (it checks the CONTEXT
  laws, not the registry).  **LAUNCHABLE.**
- **The three RULED/REPORT questions** keep their "*Spec (FIRST).*" lines (`:2795`, `:2840`, `:2881`) and the
  2026-10-10 format.  ✓
- **W4 F9 / W5 CORE briefs**: unchanged in substance from rev 28 (R25: launchable); the running workers need no
  change.  ✓

## REQUIRED changes

- **[R26.1] W8-β′ (ii)'s registry agreement is stated in the wrong direction; as written it is FALSE at reachable
  states and does not yield the extraction.**
  *What is wrong (evidence).*  `:1205` "(ii) … with the registry agreement (MachCSL registry ⊆ `xv6LockWord σ`) as its
  `Xv6/` side"; `:2638-2639` "the registry agreement (MachCSL ghost registry ⊆ `xv6LockWord σ`) a small `Xv6/`
  invariant inside the twin"; `W8-design.md:452-453` the same.  (1) The inclusion is false on the SC tree's own runs:
  `xv6LockWord σ b t` is σ-DERIVED — "static image locks + sleeplocks' inner spinlocks + **pipe locks reachable from
  the open-file table**" (`W8-design.md:124-126`) — while a pipe lock is REGISTERED at its birth, `lkFresh` →
  `lock_pay_born`/`newlock_written` inside `pipealloc`, which runs `initlock(&pi->lock, "pipe")` (`Xv6/SpecPipealloc.
  lean:10`) BEFORE the publication `(*f0)->pipe = pi; (*f1)->pipe = pi` (`:11-12`; the file's own header: "A file's
  PAYLOAD is published as `f->pipe` is written", `:24`), so between the two the registry holds a word `xv6LockWord σ`
  does not; symmetrically `fileclose` does `f->ref = 0; f->type = FD_NONE; release(&ftable.lock)` and only THEN
  `pipeclose(ff.pipe, …)` (`Xv6/SpecFileclose.lean:10-12`), so between the unlink and the reclaim the registered lock
  is again not ftable-reachable.  (2) It is also the wrong direction for the proof: `lockWordDiscAt σ` is a PURE
  predicate on `MState` (`:2525`; `xv6AccessDisc σ` has no registry argument, `:2537-2538`), so it must quantify over
  the σ-derived `xv6LockWord σ b t`; to derive it from `reservedOk σ reg` ("per registered region every
  post-registration entry is by the structural author", `:1201-1203`) one needs **`xv6LockWord σ b t → b ∈ reg`**
  (every σ-visible lock word IS registered) — which DOES hold at every reachable state by the two orderings above
  (publication after birth, unlink before reclaim).  The converse ("every registered word is an xv6 lock word") is
  what W8-design §5 wanted for W11's zero-write-WCrel argument (`:2631-2634`) — but that argument runs on σ's
  custody (`custAt σ a t = .lockw b`, `:2681-2684`), not on the ghost registry, and belongs to W8 (f2-ctx)/W11, not
  to β′.  A worker holding to (ii) as written would try to prove a false invariant inside the twin.
  *Exact change (`:1205`, `:2638-2639`, §C W8 Acceptance `:2654-2656`; W8-design §5's pointer).*  State (ii) as:
  "`powerInterp_accessDiscβ : powerInterp g ⊢ … -∗ ⌜g.pow = true → lockWordDiscAt g.m ∧ cpuStaticAt g.m⌝`, where
  `lockWordDiscAt σ := ∀ b t, xv6LockWord σ b t → ⟨the word's `lockWordAt`/`lkCpuAt` discipline on `b`'s and `b+16`'s
  histories up to `t`, `Lock.lean:53-56,18-22`⟩`, obtained from `reservedOk g.m reg` through the `Xv6/`-side
  **registration lemma `xv6LockWord σ b t → b ∈ reg`** (every σ-visible lock word is registered: image locks at
  their `initlock`, sleeplocks' inner locks likewise, pipe locks because `pipealloc` births the lock BEFORE `f->pipe`
  is written, `SpecPipealloc.lean:10-12`, and `fileclose` unlinks BEFORE `pipeclose` reclaims, `SpecFileclose.lean:
  10-12`) — NOT the converse, which is false between a pipe lock's birth and its publication."  Record the converse
  as W8 (f2-ctx)/W11's concern via `custAt .lockw`, if needed at all.  S text.  Not a memory-model question (every
  option FAITHFUL).
- **[R26.2] W8-β′ (i) names no home for `reg` and no STEP at which a byte becomes reserved; the mechanism as
  described cannot be executed by a `|==>` lemma, and its true file list and PowerOn footprint are understated.**
  *What is wrong (evidence).*  `:1198-1203` / `:2652-2654`: "a MachCSL 'reserved region' (the state interpretation
  holds half of each reserved byte's points-to …) for `cpus[h]` and the lock layer's own words registered at lock
  birth (`lkFresh`, `Lock.lean:727`; `lock_pay_born :488`) … (i) the MachCSL invariant `⌜reservedOk σ reg⌝` beside
  `⌜mmOk σ⌝` in `memModelAt`".  (1) `reg` is free in that statement.  A pure `reservedOk σ reg` with "every
  post-REGISTRATION entry" needs `reg` to carry each region's kind AND its registration timestamp, and the extraction
  (ii) needs a PERSISTENT membership fact (`b ∈ reg`) the `Xv6/` proof can produce for every lock it has born — i.e.
  an auth/frag registry ghost.  No such ghost exists: `EraGS`'s lock ghost `lockSetName : CPU → GName`
  (`Resources.lean:125`, `MachGS :434`) is hart `cpu`'s set of HELD lock NAMES — `lockSetAt cpu (locks : List
  String)`, `lkInAt cpu (s : String)` (`Ctx.lean:96-101`) — not an address registry; `kptRootName`/`kmapName`
  (`:128,135`) are the kernel-table root and the kernel mapping.  So β′ must ADD an era gname: `EraGS`
  (`Resources.lean:105-135`), `MachGS` (`:420-438`) and its projection list (`:476-477`), `MachGS.ofEra`
  (`Power.lean:771-776`), the era's ghost allocation at the PowerOn step (the `PowerOn` arm of `wp_power`, which mints
  `E`), `riscvPowerAdequacy` (`Adequacy.lean`), the W3 twin `PowerText.lean` (a near-copy of both, `:1-30`), AND the
  nine `Xv6/` files that construct `MachGS` instances (`BootSharedText`, `SystemBootEra`, `UartBoot`,
  `TextPristine`, `AppUnionLaws`, `BootShared`, `NiAdequacy`, `BootHart`, `AppLaws`; `grep MachGS.ofEra Xv6/`) — none
  of which is in "6–8 MachCSL files (`Resources`, `Lock`, `WpLock`, `LockBornHook`, `KCtx`, the cpu-cell rule file)
  + ≤ 30 `Xv6/` (`lkFresh`)" (`:1208-1209`, `:2641-2642`).  (2) The deposit of "half of each reserved byte's
  points-to" into the state interpretation can happen ONLY inside a physical step: `memModelAt` is a conjunct of
  `eraInterp` (`Resources.lean:1012-1016`), the WP's state interpretation, which only the `swp` step rules open.  The
  lock birth the brief names is NOT a step: `newlock_written` is `… ⊢ |={E}=> (ownCtx cpu curCtx ∗ ∃ γ, isLock γ lk s
  R)` (`Lock.lean:682-687`) and `lock_pay_born` is a `|==>` (`:488-490`); `lkFresh` (`:727-730`) is the pair of
  own-1 word cells those lemmas CONSUME — it is produced by `initlock`'s two plain stores through the generic store
  rule.  Likewise `cpus[h]`: `cpuCells` holds `wordPointsTo … (DFrac.own 1)` (`KCtx.lean:556-560`) carved at boot
  (`BootCarveHart.lean:81,84`).  So the brief must say WHICH STEP registers: either a dedicated store rule for the
  initialising stores (`initlock`'s `sw zero,0(a0)`/`sd zero,16(a0)`, and the boot carve's first touch of `cpus[h]`)
  that performs the store, allocates the registry element and leaves the interpretation with the half; or a lazy
  "register at first dedicated access" rule.  Without this the worker discovers mid-item that the half-points-to
  idea has no entry point, and that "no PowerOn hook" (`:2663`, W8-design §8 `:498`) is PARTLY wrong: no W3-style
  TRACE hook is needed, but the gname IS allocated at PowerOn.  (3) The time index: `reservedOk σ reg` must read
  "every entry on a region byte at a timestamp ≥ the region's registration stamp (and, for a cancellable lock, < its
  reclaim) is by the region's structural author" — a pipe page's bytes carry pre-birth `kalloc`-fill and post-reclaim
  `kfree`-fill entries by generic rules (`PipeBirth.lean:1-20`, `PipeInv.lean`), so an un-indexed "every
  post-registration entry" over a CURRENT set `reg` is unprovable at reclaim unless the element is removed (and then
  `lockWordDiscAt` for the reclaimed interval is lost — harmless for W13 (K), which reads a LIVE lock, but the brief
  should say so).
  *Exact change (`:1197-1209`, §C W8 (3) `:2570-2582`, Acceptance `:2652-2658`, Sizes `:2641-2642`, Unverified
  `:2663-2664`, lane `:1979-1983`).*  Pin: (a) **`reg`'s home** — a new era ghost `rsvName : GName` in `EraGS`/
  `MachGS` (an auth map `PAddr ↦ (kind × tReg)`, kinds `cpu h` / `lockw` / `lockcpu`; fragments persistent;
  `MachGS.ofEra` projects it; allocated with the other era ghosts at the `PowerOn` step), with `memModelAt E σ`
  gaining `(E.rsvName ↪●MAP reg) ∗ ([∗map] a ↦ _ ∈ reg, ∃ H, pointsTo (G := E.mem) a (DFrac.own ½) H) ∗ ⌜reservedOk σ
  reg⌝` (or the equivalent the worker prefers — the brief must name ONE); (b) **the registration STEP** — new
  `swp`-level rules (or `wp_m_*` wrappers) for the initialising stores that register and keep the half, applied at
  `initlock`'s two stores (so `lkFresh` becomes the two HALF cells + the registry fragments — the "`lkFresh`'s
  modality changes" case the brief already prices at ≤ 30 files) and at the boot carve of `cpus[h]`; `cpuCells`'
  three `own 1` cells become halves, the ≈ 11 dedicated cpu-cell rule uses re-proved; (c) **the time index** in
  `reservedOk` (entries at `t ≥ tReg`, cancellable locks de-registered at reclaim — say that the reclaimed interval
  is not exported and that W13 (K) needs only a live lock); (d) **the file list**: + `Power.lean`, `PowerText.lean`,
  `Adequacy.lean`, the nine `MachGS`-instance `Xv6/` files (mechanical: one field each), the `Vtest` twins if they
  build `MachGS` (`tools/ci/vtest.sh check` is already in the acceptance, `:1161-1162`); re-size M–L ≈ 1.3–2.3k, still
  ONE cone rebuild; (e) **W8-design §8 / `:2663`**: "no PowerOn TRACE hook (W3's `HtextRec`) — the registry gname is
  allocated with the era's other ghosts at PowerOn; the twin's extraction is `powerInterp_mmOk`'s pattern
  (`Adequacy.lean:481`), not `powerInterp_textPristine`'s (which needs `eraRegistered` + the persisted window,
  `TextPristine.lean:122-123`)".  S text.  Not a memory-model question (proof organisation; every option FAITHFUL).

## SUGGESTIONS

- **[R26.s1] Extraction pattern.**  `:1203-1205` and `:2654-2655` say "on `powerInterp_textPristine`'s pattern" —
  β′'s facts are conjuncts of `memModelAt`, so the right twin is **`powerInterp_mmOk`** (`MachCSL/Adequacy.lean:481`),
  which `TextPristine.lean:119-120` itself calls the parent pattern ("`powerInterp_mmOk`'s twin").  Folded into
  [R26.2] (e); listed here so the cite is fixed even if the owner takes the alternative on (i).
- **[R26.s2] `pteDiscAt`'s named consumer is not an SC-export consumer.**  `:2528`, `:2651-2652`, `:2685-2686` say it is
  "consumed ONLY by the walker's racy absorption (`WeakKptStale`)".  `wtlbResPtTranslateAddrStaleAt`
  (`Weak/WeakKptStale.lean:488-502`) is a theorem over the pf model's `Wmstate` under the Weak-side invariant `wkptN`
  — it takes no premise about `MState` histories, so at Stage 2 either a bridge from `pteDiscAt σ` to that
  invariant's premise must be NAMED (where, by whom), or the clause is a DOCUMENTATION clause (the honest naming of
  the A/D write-back assumption — fine, and credible to an xv6 expert) with no Stage-2 consumer.  Say which; the
  (f2-ctx) worker should not be asked to prove an invariant nobody consumes without knowing that.
- **[R26.s3] `.pte` custody can be anchored MachCSL-side.**  The kernel table's root is already an era ghost
  (`kptRootName`, `Resources.lean:135,438`) and a constant (`bcp_kpt_val : kernel_pagetable = 0x8000a408`,
  `BootCarveProc.lean:348`); `custAt σ a t = .pte` as "a page of `kptOn t M`'s tree reachable from the word at
  `0x8000a408` as of `t`" is σ-derivable without `Xv6/` custody.  Worth one clause at `:2509-2512`, since (f2-ctx)'s
  MachCSL-generic load rule must express the exemption without `Xv6/` (an open design point of (f2-ctx), not of β′
  or R-ctx — see [R26.s4]).
- **[R26.s4] An (f2-ctx) design point R-ctx cannot settle, to record under *Unverified points* `:2663-2664`.**  §C W8
  says a load rule "establishes `chainOkAt` at its post-state GENERICALLY" (`:2608-2610`), but `chainOkAt` is an
  `Xv6/` predicate (`custAt`, `xv6LockWord`) and MachCSL cannot import `Xv6/` (`:2576`).  So (f2-ctx) needs a
  MachCSL-generic chain invariant parametrised by the registry (the `.lockw` exemption via `reg`, the `.pte`
  exemption via `kptRootName`, DMA via `devBytes`) from which `Xv6/` derives `chainOkAt` — the same shape as
  [R26.1]'s registration lemma.  One line now saves the (f2-ctx) worker a false start; no change to R-ctx.
- **[R26.s5] R-ctx's law list: `ctx_park` is 3 uses in 2 files** (`:1213` says "3"; fine as a count).  Cosmetic.
- **[R26.s6] `:1198-1200` wording.**  "the lock layer's own words registered at lock birth (`lkFresh`, `Lock.lean:727`;
  `lock_pay_born :488`)" — after [R26.2] (b) the registration is at `initlock`'s stores, and `lock_pay_born` is the
  PAYLOAD's move (it never sees the words); cite `newlock_written :682-687` as the consumer of the (now half) cells.

## Owner questions the plan is missing

None.  [R26.1] and [R26.2] are proof-organisation fixes to an INTERNAL brief; per the OWNER RULE they are not
memory-model questions — RVWMO, the Sail model, Zifencei and the PMAs are silent on how a proof registers reserved
bytes or states a registry inclusion, and every option above is FAITHFUL (the published quantifier, the trusted
base and the conclusions are unchanged).  The plan's RULED/REPORT questions (Q-W8-feed `:2790`, Q-HOLDING `:2839`,
Q-GFDEV-delta `:2880`) keep their "*Spec (FIRST).*" lines and the 2026-10-10 format.
