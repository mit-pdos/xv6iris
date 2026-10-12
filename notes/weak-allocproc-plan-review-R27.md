VERDICT: SATISFIED

# Review R27 of `notes/weak-allocproc-plan.md` (rev 30)

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git or jj, no subagents).  Every cite
below was read at the working-copy tip of `../xv6iris-weak` (plan mtime 2026-10-12 08:59).  Scope per the R27 brief
(narrow): verify that rev 30 applied R26's two required changes to W8-β′ correctly — [R26.1] the registration lemma's
direction, [R26.2] `reg`'s home (`rsvName`) and the reserving STEP, taken as **[R26.2-alt]** (the `PowerOn` mint over a
client-supplied static list `KernelRsv.static`; pipe locks move to W8 (f2-ctx)) — judge the -alt against
`Adequacy.lean` / `BootCarveHart` / `EraGS`-`MachGS`, and decide whether **W8-β′ is launchable as written**.  W4 F9, W5
CORE and R-ctx are RUNNING and were not re-reviewed; rev 30 touches none of their briefs (`:1221-1225`, `:1273-1290`,
`:1292-1300` unchanged in substance).  Items (a)/(b) of the standing brief were settled in R1–R26 and are not re-opened.

**Sign-off.**  YES.  **Both R26 fixes are applied correctly, the -alt is SOUND and better than R26's step proposal, and
W8-β′ is LAUNCHABLE as written.**  No required change: everything below is file-list / sizing precision (S text, no
design change, every option FAITHFUL) that the worker would otherwise discover in the first build — the owner should
hand the three items marked **(tell the worker at launch)** to the W8-β′ worker with the brief.  No owner question:
RVWMO, the Sail model, Zifencei and the PMAs are silent on how a proof registers reserved bytes (proof organisation,
not memory-model semantics), so per the OWNER RULE nothing here is a memory-model question.

## What was checked and holds

- **[R26.1] applied correctly, at every site.**  `:1256-1263` (§C top), `:2652`, `:2721-2726` (§C W8 (5)), `:2744`
  (Acceptance): the extraction is the registration lemma **`xv6LockWord σ b t → b ∈ reg`** (every σ-visible lock word
  is registered), the converse recorded as FALSE between a pipe lock's birth and its publication
  (`Xv6/SpecPipealloc.lean:10-12`: `initlock(&pi->lock)` before `(*f0)->pipe = pi`) and between the unlink and the
  reclaim (`Xv6/SpecFileclose.lean:10-12`), and parked as W8 (f2-ctx)/W11's concern via `custAt .lockw`.  In β′ the
  lemma is list membership on `KernelRsv.static` — right, since the PROVISIONAL `lockWordDiscAt` quantifies over the
  static words.  `W8-design.md:452-453` still carries the wrong direction; the plan supersedes it explicitly
  (`:2723-2726`) — see [R27.s5].  ✓
- **[R26.2] applied, as the -alt.**  `:1228-1251`, `:2648-2651`, `:2740-2741`, `:2751-2754`: (a) `reg`'s home is a NEW
  era ghost `rsvName : GName` in `EraGS`/`MachGS` — the structure `Resources.lean:105-135` (14 fields today), the class
  `:420-438`, the `MachGS.era` tuple `:470-477`, `MachGS.ofEra` `Power.lean:771-776` ✓; the only existing lock ghost is
  indeed `lockSetName`, a per-hart set of HELD lock NAMES (`Ctx.lean:96-101`) ✓; (b) `memModelAt E σ`
  (`Resources.lean:951-956`, ending in `⌜mmOk σ⌝`) gains the auth, the `[∗map]` of halves and `⌜staticIn reg ∧ reservedOk
  σ reg⌝` ✓; (c) the reserving step is the `PowerOn` mint over `KernelRsv.static`, on the `KernelMap.static` pattern —
  verified: `class KernelMap` (`KMap.lean:120-123`), xv6's instance (`Xv6/KernelMap.lean:156-160`), allocated at the
  mint (`Power.lean:558` `ghost_map_alloc … KernelMap.static`; `PowerText.lean:273` the twin), handed to the boot client
  in `powerBootRes` (`Power.lean:336-345`) / `powerBootResT` (`PowerText.lean:113-122`) ✓; the halves on the
  `powerBootResT` split shape (`memCells_win`/`memCellsOut`, `PowerText.lean:76-110`: `memCells` split into the
  persisted window and the owned rest — exactly the shape a ½/½ split needs, with NO `HtextRec` trace hook) ✓.
- **The -alt's two reasons are correct.**  (a) "the carve is a pure ownership split, not a step": `BootCarveHart` derives
  the `cpus[c]` cells from `memCells` by `⊢`/`|==>` (`:354-356`, `:448-450`, own-1 `wordPointsTo`), never inside a `swp`
  step — nothing there can open the state interpretation ✓ (the cite `:81,84` lands on the geometry defs `bhStackLo`/
  `bhCpuLo`; cosmetic, [R27.s6]).  (b) "the final hook is `… ⊢ ◇ ⌜phi g' h⌝`": `Adequacy.lean:359-368` — `Hphi`'s
  premise is `powerInterp g' ∗ (γobs ↪VAR{½} h) ∗ ⌜obsWf h g'⌝ ∗ ▷ Pc ∗ ▷ Pt`, conclusion `◇ ⌜phi g' h⌝`, no fancy
  update, no invariant token — so a persistent fragment `b ↪◯ lockw` held by a lock invariant is unreachable from the
  hook, and the extraction can use `b ∈ reg` only if `memModelAt` makes membership PURE (`⌜staticIn reg⌝`) ✓.  The
  extraction pattern is `powerInterp_mmOk` (`Adequacy.lean:481-492`: `unfold powerInterp eraCur`, `cases g.pow`, `unfold
  eraInterp memModelAt`, `ipureintro`) ✓ — `TextPristine.lean:119-123` is the parent's twin needing `eraRegistered`,
  correctly NOT the pattern here.
- **Soundness of the half-points-to mechanism against EVERY non-dedicated writer** (the audit the brief asks for in
  spirit: can a generic rule, the walker or DMA write a reserved byte and break `reservedOk`?).  No: every writer other
  than the dedicated rules carries own-1 of its target — the generic store rules (`wp_s_sd`, `WpSmodeRules.lean:369-373`:
  `wordPointsTo … (DFrac.own 1) old`; `wp_s_sw :712`; the mint rules `WpSmodeMint.lean:40-46,126-132` likewise own 1),
  the kernel-table write-back (`swp_update_and_write_pte_kpt`, `WpPtWalk.lean:455-470`, consumes `kptOn t M` whose
  `kptBody` is `pteCell` = `wordCellT … (fun _ => DFrac.own 1)`, `KptInv.lean:85`, `WordHist.lean:333-335`), and the
  disk's DMA (`dmaWriteLease`, `WpDevDma.lean:46-50`: `histBytes pa n (fun _ => DFrac.own 1)`).  With the
  interpretation holding ½ of every reserved byte, gen_heap validity makes own-1 at a reserved address impossible, so
  `a ∉ reg` is derivable at each of those sites — the W8-design §4 argument (`W8-design.md:418-420`) holds for all
  three writer classes, not only for the S-mode store rules.  ✓  (Where those sites live is the one footprint gap,
  [R27.s1].)
- **`reservedOk` as stated is satisfiable on the static words.**  Entries at `t ≠ 0` on a static lock's two words are:
  `initlock`'s `sw zero,0(a0)` / `sd zero,16(a0)` (already through `wp_s_sw_mint`/`wp_s_sd_mint`, `ProofInitlock.lean:56,
  68` ✓ — zero writes, consistent with the free state `curVal W 0 = 0` and with "every entry is 0 or the writer's own
  `&cpus[c]`", `Lock.lean:53-56,18-22`), then the `WpLock.lean` rules.  The `name` field at `+8` is written by the plain
  `wp_s_sd` (`ProofInitlock.lean:50-51`) and is NOT reserved (`lkFresh :727-730` covers `lk..+4` and `lk+16..+24`) ✓.
  No `memset` touches a static spinlock (`proc[j]`, `bcache.buf[i]`, `itable.inode[i]` are never memset; the kalloc/
  kfree fills are the PIPE case, correctly moved to (f2-ctx)) ✓.  `cpus[h]`'s three cells are written only by
  `wp_s_sd_proc` (`WpSmodeProc.lean:107`), `wp_s_sw_intena :1076`, `wp_s_sw_noff_lend :1159`, read by `wp_s_lw_noff :966`
  — each at `aCpu* cpu` of the EXECUTING hart (`haddr`), so `e.tid = hartAgent h` ✓; the 14 `cpus[h].context` words
  (`cpuCtxFree`) are outside the three cells ✓.  `e.t ≠ 0` excludes the image entry at the mint (`mmOk_boot`,
  `Resources.lean:899`; `hmem0` in the mint) ✓.  "Registered from `t = 0`, no time index, no de-registration" is right
  for a static region.
- **Scope note is correct.**  Every lock on `allocproc`'s verified trace is static: `proc[j].lock`, `pid_lock`
  (`allocpid`), `kmem.lock` (`kalloc` from `allocproc`/`proc_pagetable`); `wait_lock` (`:1262`) is static but not on
  the trace — harmless.  W13 (K) needs only live STATIC locks ✓.
- **File-list cites that hold.**  `Weak/WeakAdequacy.lean:109-128` IS a `MachGS` literal (`weakAdeqMachGS … where`,
  every name spelled) → one new field ✓; `Xv6/AppUnionPre.lean:88-91` (`atFixedGS`) and `Xv6/AppPreGS.lean:53-56` are
  the two `Xv6/` literals ✓; `MachGS.ofEra` has 15 `Xv6/` caller files (+ `Power.lean`), all passing an `E : EraGS` —
  no edit ✓ (R26's "nine" corrected rightly); `Vtest` = `vtest-lean/` (`lakefile.toml:47-49`) builds no `MachGS`/`EraGS`
  ✓; the 14-field era tuple `⟨names, γh, γm, vn, ivn, rvn, γtop, γauth, γresv, lsn, γkmap, γkroot, dn, γmir⟩` appears
  ≈ 12× in `Power.lean:565-653` and ≈ 10× in `PowerText.lean:280-330` — mechanical ✓.
- **The three RULED/REPORT questions** keep their "*Spec (FIRST).*" lines (`:2795`, `:2840`, `:2881`) and the
  2026-10-10 format; header `:26-27` and `:2839-2840` say "no owner question" with the OWNER-RULE justification ✓.

## REQUIRED changes

None.

## SUGGESTIONS

- **[R27.s1] (tell the worker at launch) The MachCSL file list misses the three PRIMITIVE writer sites and the class
  threading.**  `reservedOk σ reg` is re-established where `mmOk` is today: `mmOk_store` is applied in exactly
  **`MachCSL/Wp.lean`** (the primitive store) and **`MachCSL/WpAtomic.lean`** (the AMO), `mmOk_storeDma` in
  **`MachCSL/WpDma.lean`**, `mmOk_afterLoad` in `Wp.lean`/`WpSmodeFenceFloor.lean` (loads add no entry — trivial),
  `mmOk_boot` in `Power.lean`/`PowerText.lean` (the mint).  The pure lemmas (`Resources.lean:825,863`) cannot take an
  ownership premise, so each of the three store sites needs the one-line "own-1 at `a` ∗ interpretation's ½ ⊢ `a ∉ reg`"
  argument, and the ½+fragment variants for the dedicated rules (the "half + fragment" mode `:1248-1250` implies) are
  NEW primitives beside them (`Wp.lean`-level store for `cpus[h]`/`initlock`, `WpAtomic.lean`-level AMO for `acquire`),
  which `WpSmodeMint`/`WpSmodeProc`/`WpSmodeRules`/`WpLock` then wrap.  Also: `powerBootRes`/`wp_power`/`powerBootResT`/
  `wp_powerT` carry `[KernelMap]` (`Power.lean:336,438`; `PowerText.lean:113,142`) AND so do **`riscvPowerAdequacy`
  (`Adequacy.lean:266`)** and `riscvPowerAdequacyT` (`PowerText.lean:512`) — `[KernelRsv]` must be threaded the same way,
  so "`Adequacy.lean` spells no era tuple — likely untouched" (`:1269`) is wrong by one binder (trivial, but say it).
  Net: ≈ 15 MachCSL files, not ≈ 11 (`:1267-1269`, `:2728`, `:2043-2045`).  No design change; the size band M–L stays.
- **[R27.s2] (tell the worker at launch) The `Xv6/` footprint is ≈ 45–50 files, not "≤ 30 `lkFresh` + `BootCarveHart`
  + 2 literals + twin" (`:1269-1272`).**  Two omissions: (i) the `memCells` row of `powerBootRes` changes shape, so its
  14 consumers change — `grep -l 'memCells\|powerBootRes' Xv6/`: `AppIface`, `BootBridge`, `BootCarve`, `BootCarveHart`,
  `BootConfig`, `BootHart`, `BootShared`, `BootSharedDev`, `BootSharedFs`, `BootSharedText`, `LogMirrorHalf`,
  `SystemBootEra`, `SystemBootEraText`, `UartBoot`; (ii) the IMAGE lock words are carved out of `.bss` windows by
  `bootCarve_lockWords` (`Xv6/BootCarveMain.lean:167`, used for `proc[i]`'s `procRaw` at `BootCarveProc.lean:194` and
  for `mainLocksBare`), by `FileBoot`/`DiskBoot`, and handed own-1 into the init specs `SpecBinit`/`SpecIinit`/
  `SpecFileinit`/`SpecInitlog`/`SpecInitsleeplock`/`SpecKinit` (the 17 "`initlock` but not `lkFresh`" files) — the
  halves must be threaded through all of them, not only through `BootCarveHart`.  Also the population: `KernelRsv.static`
  is ≈ **156 spinlocks** (`NPROC` 64 + `NBUF` 30 + `NINODE` 50 sleeplock inner locks + ≈ 12 singletons:
  `SlotSupply.lean:49`, `BioPool.lean:52`, `FsGeom.lean:96`), ≈ 1.9k bytes + `cpus[h]`'s 128 — "the ≈ 14 `initlock`
  callers' addresses" (`:2755-2756`) counts call SITES, most inside loops.  Size: 1.3–2.3k → ≈ 1.6–2.6k; still M–L, still
  ONE cone rebuild.
- **[R27.s3] (tell the worker at launch) Do not unfold the reserved map.**  ≈ 2k byte entries in `[∗map] a ↦ _ ∈ reg`
  is the `KernelMap.static` situation in miniature (`KMap.lean:128-130`: "the proof mode cannot afford to look inside a
  33k-entry map literal"; `Xv6/KernelMap.lean:150-153` makes it `irreducible` and exposes lookup lemmas).  Prefer
  `KernelRsv.static : List Region` (addr, len, kind; ≈ 180 entries) with the interpretation's halves as
  `[∗list] r ∈ static, histBytes r.addr r.len (fun _ => ½) _`, accessed only through `bigSepL_lookup_acc` and a
  decidable `inRsv a` with lookup lemmas — the "equivalent camera is the worker's call" clause (`:1233`) already allows
  it; naming the pitfall saves a false start.
- **[R27.s4] The (r2) twin is ≈ 0.1–0.3k, not "≤ 1.8k, likely lower".**  `Xv6/SystemAdequacy.lean:476-491`
  **`xv6PowerAdequacy`** already takes an arbitrary `phi : GState → Prop` with `Hphi : powerInterp (…literal…) g' ∗ ▷
  xv6Slot … ⊢ ◇ ⌜phi g'⌝` at the TRIVIAL slot (`obsPredAt`) — exactly β′'s shape (facts pure in `memModelAt`, no era
  registration needed).  So `xv6DiscAdequacy` = `xv6PowerAdequacy` at `phi := fun g => g.pow = true → xv6AccessDisc g.m`
  with `Hphi` by `powerInterp_accessDiscβ` (drop `▷ xv6Slot`), then `_xv6GF`/`_closed` on `LinkSystemAdequacyClosed.lean:
  20`'s / `LinkTextAdequacy.lean`'s 35-line pattern.  None of `PowerText`/`BootSharedText`/`SystemBootEraText`/
  `SystemAdequacyText` (W3's 1,795 lines, `:2717-2719`) is needed — those exist because W3 changed the POWER THREAD.
  Sharpen `:2717-2721` and §C W8 (6); it also makes "RECOMMENDED and APPLIED: the twin at β′" (`:2654`) cheaper than
  argued.
- **[R27.s5] `notes/W8-design.md` still states the superseded design in three places** — §4 "registered at lock birth
  (`lkFresh` …; `lock_pay_born`) and released at the cancellable lock's reclaim" (`:423-425`), §5 "MachCSL ghost
  registry ⊆ `xv6LockWord σ`" (`:452-453`), §6's "6–8 MachCSL files" and §8 "no PowerOn hook" (`:498`).  The plan calls
  §1 "the binding text" for the skeleton (`:2573`) and overrides §4/§5/§8 in prose; a worker reading W8-design first
  may follow §4/§5.  One owner line at the top of each of §4/§5/§8 — "superseded by plan rev 30: [R26.1]/[R26.2-alt]"
  — or an explicit "W8-design §4/§5/§8 are superseded; read the plan's §C top" in the brief's first paragraph.
- **[R27.s6] Cosmetic cites.**  `BootCarveHart.lean:81,84` (`:1240`, `:2572`) are the geometry defs; the carve of the
  three cpu cells is `:354-356`/`:448-450` (`bootHartBss`/`bootHartBss_open`).  `:1262` "`wait_lock`" is not on
  `allocproc`'s trace (`kmem.lock` is, and is static).  `staticIn reg` should be spelled once —
  `∀ r ∈ KernelRsv.static, reg r.addr = some r.kind` — so that (f2-ctx)'s dynamic entries can GROW `reg` without
  changing β′'s conjunct (`:1233`, `:2740`).
- **[R27.s7] For (f2-ctx)'s open design point, not for β′.**  The hook problem (`:2757-2760`) has a MachCSL-side exit the
  plan does not record: `powerAdequacyCore`'s own hook is a FANCY update, `|={⊤,∅}=> ⌜phi g2 h⌝` (`Adequacy.lean:103-108`);
  `riscvPowerAdequacy` weakens it to `◇ ⌜phi⌝` for its clients (`:367-368`).  A twin exposing the `|={⊤,∅}=>` form
  would let an `Xv6/` extraction open the pipe-lock invariants and read the dynamic fragments — a third option beside
  "a PURE σ↔`reg` tie" and "export the pipe part another way".  One line under *Unverified points*; FAITHFUL (proof
  organisation).

## Owner questions the plan is missing

None.  Every item above is proof organisation inside an INTERNAL brief; RVWMO, the Sail model, Zifencei and the PMAs
are silent on how a proof registers reserved bytes, which files hold the primitive store rules, or how a root twin is
assembled — every option is FAITHFUL (the published quantifier, the trusted base and the conclusions do not move).  The
plan's existing RULED/REPORT questions (Q-W8-feed `:2862-2936`, Q-HOLDING, Q-GFDEV-delta) keep their "*Spec (FIRST).*"
lines and the 2026-10-10 format.
