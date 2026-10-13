VERDICT: NOT SATISFIED

# Review R35 of `notes/weak-allocproc-plan.md` (rev 38)

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git or jj, no subagents).  Every cite below was
read at the working-copy tip of `../xv6iris-weak` (plan rev 38, 5,063 lines), `~/dev/weak-orch/parked/PROGRESS-W8f2.md`,
`~/dev/weak-orch/parked/w8f2-s2-wip/*.lean.txt` and `~/dev/weak-orch/allocproc_W8f2_prompt.txt`.  Scope per the R35 brief
(narrow): rev 38's record of R34, the W8 (f2-ctx) S1 merge and its three findings, the two provisional (a) options
(Q-F2-PIPEHOP, Q-F2-BOOTGATE), the RELAUNCH paragraph and the W8 (f3-rest) item.  W-SCO (A) is running in w4; its brief was not
read for change and is not changed.  Items (a)/(b)/(d) of the standing brief were settled in R1–R34 and are not re-opened.

**Sign-off.**  NO — TWO required changes, both S text in Q-F2-PIPEHOP (a) / Q-F2-BOOTGATE (a) and the RELAUNCH paragraph that
executes them; no memory-model change, no shrinking, no new owner ruling needed before relaunch (the two questions stay OPEN,
provisionally (a), but (a)'s text must be corrected BEFORE the owner rules on it and before a worker builds it).  Everything rev 38
RECORDS checks out in the tip (below); the relaunch paragraph is right about the WIP, the wiring order, S2b/S3/S4, acceptance,
the parallel-lane rule and size.  It is NOT executable as written because (i) Q-F2-PIPEHOP (a) defines the pipe-lock hop
predicate by a fact the plan itself records as FALSE at reachable states, names a registry (`rsvName`) that the merged state
interpretation pins to the static list, and relies on a hop lemma whose registry is un-timed and only grows — [R35.1]; (ii)
Q-F2-BOOTGATE (a)'s "`started = 1` through the reserved-store rule" names a rule whose obligation is history-free and hence
unprovable for a one-shot word, and the reservation of `started` moves `StartedInv`'s cell and the boot carve — files and size
absent from the brief — [R35.2].  Both are FAITHFUL as options; neither is implementable from the text as it stands.

## What was checked and holds

- **R34 applied in the launch brief and recorded.**  `../weak-orch/allocproc_W8f2_prompt.txt` carries the ADDENDUM [R34.1]
  (four of six, `W8 (f3-rest)`), [R34.2] (the `W8-Rctx.md` carve-out, [OWN.39]), [R34.3] (route A, `Weak/WeakAdequacy.lean`
  the only `Weak/` file) and the s1–s6 line ✓; the plan's header (`:3-29`), `:461`, the launch paragraph (`:1744-1802`: title
  line names [OWN.37] + [OWN.41] [R34.s3]; deliverable (5) enumerates the six conjuncts and lands four [R34.1]; the `W8-Rctx.md`
  carve-out sentence [R34.2]; Files "13 MachCSL [R34.3]", route (A) landed; `Vtest` = `vtest-lean/Vtest/` [R34.s4]; the two greps
  22 / 16 [R34.s5]; the per-row table [R34.s6]) ✓; `PROGRESS-W8f2.md` opens with the scope line ("FOUR of six … W8 (f3-rest) …
  pte-key arm [OWN.39] … route A") ✓ and keeps the per-row table (its last section) ✓.
- **S1 MERGED — in the tip, as recorded.**  `MachCSL/ChainDefs.lean` 369 lines: `memExt :59`, `lockByteIn :121`, `syncHop :129`,
  `hopChain :135`, `ChainEnv :220`, `pubCover :244`, `gateOk :257`, `ChainCert :271`, `valid :306`, `pubOneShot :339`, `valid_hop :347`
  ✓; `MachCSL/ChainCert.lean` 202 lines: `memModel_certIssue :122`, `memModel_gateIssue :129`, `memModel_chainRetime :141`,
  `memModel_chainHop :170` ✓; `MachCSL.lean:261 import MachCSL.ChainCert` ✓ (so the `lint.sh` drift finding the worker reported is
  ALREADY closed — see [R35.s4]); `Resources.lean`: `EraGS.chainName :161`, `MachGS.chainName :491`, `pubByteIn :1052`,
  `chainEnvAt :1056`, `certsOk :1061`, `rsvLockByte :1166`, `chainEnv :1170`, `chainModelAt :1185`, `rsvModelAt :1193` carrying
  `chainModelAt` ✓; `CtxId` with `chain : CPU → GName` and `gate : GName` (`:432-441`; the plan writes `:432-438`) ✓;
  `Reserved.lean` `| pub (w : CPU)` at `:123` (the plan writes `:120`), `regionOk`'s `.pub` arm `:166` ✓; `Ctx.lean`:
  `chainCertAt :80`, `gatePassedAt :92`, `vecAt :271`, `chainKey :278`, `vecCertsAt :600`, `chainTokAt :614` — defined, NOT in
  `keyAt`/`ownCtxAt` (the tip's `keyAt :187` is the TSO one) ✓; `Weak/WeakAdequacy.lean:130 chainName := 0` ✓; `Xv6/KernelRsv.lean:173`
  the `.pub _ => true` arm ✓; `tools/tcb/expected.json` lists `MachCSL.ChainDefs` on 4 roots (`:99,232,446,752`) ✓.
- **The S2a WIP is where the plan says.**  `~/dev/weak-orch/parked/w8f2-s2-wip/{Ctx,CtxLaws,CtxBoot,CtxKeyMint,Wp}.lean.txt` exist;
  `Ctx.lean.txt:284-285 keyAt := (ctxFloor ξ t ∗ chainKey E ξ t) ∨ ∃ h, dirtyIn … ∗ authoredByAt …`, `:705-708 ownCtxAt … ∗
  chainTokAt E cpu ξ W D` ✓ — exactly the relaunch's "re-wire" line; `CtxLaws.lean.txt`: `ctxStamped ξ T V g :39`, `ctxDomAt :45`
  (vector under the dominator's, gate only under a set gate), `ctx_stamp :574`, `ctx_unstamp :627` (takes `vecCertsAt era V g cpu`),
  `ctx_register :753`, `ctx_park :900`, `ctx_resume :937`, `ctx_move :1034` ✓.  (`PROGRESS-W8f2.md` still says
  `claude-notes/w8f2-s2-wip/`, which exists in neither the tip nor `../xv6iris-weak-w2` — [R35.s3].)
- **The three findings are faithfully transcribed** (`PROGRESS-W8f2.md` "Findings" 1–4 ↔ plan `:1816-1823`); finding 1's cites
  `readAU` `WpAtomic.lean:403` (PROGRESS says `:399`; the tip is `:403` — the plan is right), `readAUr` `ReadAUr.lean:26` ✓;
  `exclWriteAUOwn :481`/`exclWriteAURsv :490` ✓; `wp_s_sd_mint :40`/`wp_s_sw_mint :127` (`WpSmodeMint.lean`) ✓; the 18 `Xv6/` files
  / 37 lines naming `kctx_newlock`/`newlock_*` ✓ (grep: 18 / 37); `SpecMain`/`ProofMain`/`MainSecondaryParts`/`StartedInv` exist ✓;
  `wp_s_sd_proc` `WpSmodeProc.lean:108` ✓; `userret` `fence.i` at `KernelImage.lean:17614` (`0x8000609c`) ✓.
- **Q-F2-BOOTGATE's spec paragraph is right about the machine.**  `HRead.coh` is the per-byte FOREIGN-source coherence floor:
  `LoadSrcs.stampAt` (`TsoMem.lean:312-316`: the source's timestamp when foreign, 0 when own), raised by `HRead.afterLoad :356-358`,
  reset by the hart's OWN store (`:361-364`); `gateOk :257` asks exactly "a post-power-on store of the publication byte at or below
  `coh j f`", so a secondary's `lw started` seeing hart 0's store at `r` DOES make `gateOk` σ-true for that hart, and no secondary
  ever stores to `started` (`.pub 0`'s `cpuRegionOk 0`), so the floor never resets — `ChainEnv.ext`'s fourth clause (`:231-235`)
  is the invariant that makes this stable ✓.  The RVWMO reading (`fence rw,rw; sw` / `lw; fence rw,rw`, PPO 4 + rf, total gmo) is
  the right one; Sail/Zifencei/PMAs silent ✓.  `pubCover :244` uses `t < r` (hart 0's entries strictly before its `started`
  store) ✓.  Both new questions carry *Spec (FIRST)* with marks, plain language, a hart/load/store example, definitions, why it
  matters and per-option changes/mark/cost/unblocks/risk — the 2026-10-09 and 2026-10-10 standards are met in FORM; [R35.1]
  corrects (a)'s CONTENT.
- **W8 (f3-rest)** (`:1850-1857`): sizes and feeds named, "all options FAITHFUL" (the spec is silent on how a proof partitions
  the conjuncts) ✓; the three `wp_s_sd_proc` sites and the `userret` image fact are real.
- **Parallel-lane rule** (`:1846-1848`): W-SCO (A)'s files are `Weak/SailCycleOrder*`, `MachOfPf`, `SrvwmoXv6Adequacy`,
  `PfRunUnpinned`; (f2-ctx) edits `Weak/WeakAdequacy.lean` only — no overlap ✓ (unchanged from R34's check).

## REQUIRED changes

- **[R35.1] Q-F2-PIPEHOP option (a) is not implementable as written: its defining predicate is one the plan records as FALSE at
  reachable states, the "registry" it names is pinned to the static list by the merged state interpretation, and the merged hop
  lemma's registry is un-timed and may only grow.**
  *What is wrong (evidence).*  (i) `:4048-4049` defines (a) as "the pure predicate 'word `b` is the lock of a pipe reachable from
  `ftable` as of `t`' … registered at the mint store", and the RELAUNCH `:1834-1835` repeats "(reachable from `ftable` as of `t`)
  registered at `wp_s_sw_mint`".  The plan itself says, three times, that `ftable`-reachability is FALSE in the two windows that
  matter: `:232-233` and `:1942-1943` ("`pipealloc` runs `initlock(&pi->lock)` BEFORE `(*f0)->pipe = pi`, `Xv6/SpecPipealloc.lean:10-12`;
  `fileclose` unlinks BEFORE `pipeclose` reclaims, `SpecFileclose.lean:10-12`") and `:3788-3789` ("FALSE between a pipe lock's birth
  and its publication … and between the unlink and the reclaim").  At the mint store (the plan's registration point) the lock is
  NOT yet reachable, so the side condition cannot be discharged there; and at the LAST `pipeclose` (`SpecFileclose.lean:4-12`:
  `f->type = FD_NONE; release(&ftable.lock); … pipeclose(ff.pipe, …)`) the closer acquires `pi->lock` — a hop from the previous
  releaser, possibly another hart — and then racily reads `pi->readopen`/`pi->writeopen`/`pi->nread`… while NO `ftable` slot points
  at `pi`; with (a)'s predicate that hop word is not a lock as of `t`, the chain fails, and `chainOkAt` is FALSE on every run that
  closes a pipe from a hart other than its last releaser — the very failure mode the question's *Plain language* warns of
  (`:4036-4037`).  (ii) `:4043-4044` *Definitions*: "the registry = the era ghost `rsvName`'s map of reserved regions"; but
  `rsvModelAt` (`Resources.lean:1193-1197`) carries `⌜staticIn rsvStatic reg ∧ rsvExact rsvStatic reg ∧ …⌝` — `rsvName` IS the static
  list, exactly (`RsvMint.lean:3-13`: "Registered from timestamp 0, never released"), so nothing can be "registered" in it
  mid-run without changing `rsvModelAt`.  (iii) The merged hop lemma `memModel_chainHop` (`ChainCert.lean:170-175`) takes `hlk :
  rsvLockByte b` = `lockByteIn rsvStatic b` (`Resources.lean:1166-1167`); `chainEnv σ := chainEnvAt rsvStatic σ` (`:1170`) sets
  `isLk := lockByteIn rs` (`:1056-1057`); `ChainEnv.isLk : PAddr → Prop` is UN-TIMED (`ChainDefs.lean:220-224`) and `ChainEnv.ext`
  requires it to GROW (`:231-233`: `∀ b, X.isLk b → Y.isLk b`; `hopChain_mono :147-152` depends on it).  A pipe lock DIES: the plan's
  own scope note `:3666` ("destroyed at `wp_s_sw_zero_release_cancel`", `WpLock.lean:2491`) and `kfree`'s junk fill of the page
  (`SpecKfree.lean:130`: "memsets the page"), after which the page is reused as anything.  So a σ-derived "live pipe lock" predicate
  is NOT monotone and cannot be `isLk`; and a monotone "once a pipe lock, always a hop byte" `isLk` makes `syncHop :129-131` —
  pure history SHAPE (nonzero, then a 0 by `A`, then a nonzero by `B`) — fire on a reused page's ordinary stores (user or kernel),
  issuing certificates for synchronisation RVWMO does not give: `chainOkAt` would then be TRUE for spurious reasons, which is
  option (b)'s W11 problem (`:4056-4057`) smuggled into (a).  Mark: (a) remains FAITHFUL as an OPTION (restricting claimed chains
  never over-claims); it is its DEFINITION and MECHANISM that are wrong.
  *Exact change (S, text — in §D Q-F2-PIPEHOP (a) and the RELAUNCH's S2b sentence; the question stays OPEN, provisionally (a′)).*
  Replace (a)'s predicate and mechanism by: "**(a′) a TIME-INDEXED σ-readable live window.**  `pipeLockAt σ b t` := some
  `struct file` slot's `f->pipe` word (`ftable`, `FileBoot`) has HELD the address of `b`'s `struct pipe` at some timestamp ≤ `t`
  (the slot's byte history — monotone in the past, so it covers the last `pipeclose`, which runs after the unlink), and `b`'s page
  carries no reclaim entry (the `kfree` junk fill / `wp_s_sw_zero_release_cancel`) between that write and `t`.  Mechanism: the
  merged chain layer's registry becomes time-indexed — `ChainEnv.isLk : PAddr → Nat → Prop` ('`b` is a hop word at `r`'), `ext`
  monotone in the same sense (a past fact never changes), `hopChain`/`valid_hop`/`memModel_chainHop` check `isLk b r` at the
  release's position, `chainEnv σ`'s `isLk b r := lockByteIn rsvStatic b ∨ pipeLockAt σ b r` — a MACHINE-side `MachCSL` predicate
  parametrised by a client-supplied σ-pure `dynLk : MState → PAddr → Nat → Prop` with a monotonicity obligation (so `MachCSL` stays
  kernel-generic [R26.s4]; `Xv6/` supplies `pipeLockAt`); `rsvName` is NOT touched (it stays the static list, `rsvExact`).  The mint
  store's side condition is dropped (the window opens at the `f->pipe` write, `SpecPipealloc.lean:10-11`, not at `initlock`);
  `syncPath` (S4) hops through `isLk b r`.  Amends the MERGED S1 layer: `ChainDefs.lean` (`ChainEnv`, `ext`, `hopChain`,
  `valid_hop`, the `_mono` lemmas), `ChainCert.lean` (`memModel_chainHop`'s `hlk`), `Resources.lean` (`chainEnvAt`, `rsvLockByte`,
  `chainEnv`, `chainEnvAt_congr/_ext_*` gain the `dynLk` monotonicity) — mechanical, ≈ 0.2–0.3k on top of (a)'s 0.5k; the
  `ChainEnv.ext`-stability proofs of `rsvModelAt` re-run.  FAITHFUL (same mark as (a)).  Risk, stated honestly: ANY σ-shape hop
  predicate ((a′) or (b)) can be satisfied by a reused page whose stores happen to alternate like a lock; (a′) bounds this to the
  pipe's live window, (b) does not; the release-site pin W11 adds (`:4056-4057`) is what makes a claimed hop a REAL
  release→acquire pair under either — say so under (a′) too, and add 'W11 pins the release site per hop' to (a′)'s unblocks/risk
  line."  Keep (b) and (c) as they are.  In the RELAUNCH S2b sentence (`:1834-1835`) replace "a σ-readable 'live pipe lock as of
  `t`' (reachable from `ftable` as of `t`) registered at `wp_s_sw_mint`" by "the time-indexed `isLk b r` of Q-F2-PIPEHOP (a′):
  `ChainDefs`/`ChainCert`/`Resources` amended as above (S1 layer, mechanical), `Xv6/` supplies `pipeLockAt` (the `f->pipe` history +
  the reclaim entry)"; add `ChainDefs`, `ChainCert` to the Files list (13 → 15 MachCSL); add "+ ≈ 0.2–0.3k" to the size line.  Also
  fix the *Definitions* sentence `:4043-4044`: "the registry = `rsvName` … now `started`" → "the STATIC registry = `rsvName`
  (= `rsvStatic`, pinned by `rsvExact`, `Resources.lean:1196`); the hop registry `ChainEnv.isLk` is derived from it and, under (a′),
  from `pipeLockAt`".

- **[R35.2] Q-F2-BOOTGATE option (a) names a reserved-store rule that cannot discharge a one-shot word, and omits the files the
  reservation of `started` necessarily moves (`StartedInv`'s cell, the boot carve).**
  *What is wrong (evidence).*  (i) `:1836-1837` / `:4084-4085`: "`main`'s `started = 1` goes through the reserved-store rule".  The
  reserved store rules are `execSpecF_sw_rsv`/`execSpecF_sd_rsv` (`RsvCell.lean:127,163`) over `ctxBytes_writeAURsv :91`, whose
  obligation is `rsvWordOk` (`:33-37`) — HISTORY-FREE by design ("`∀ (m : FlatMem) (t : Nat), 0 < t → regionOk m R → regionOk
  (m.writeBytes …) R`", header `:9-12`: "for `cpus[h]`'s cells, any store by hart `h`").  For `.pub w`, `regionOk` is `cpuRegionOk w m R ∧
  oneShotOk m R` (`Reserved.lean:166`, `oneShotOk :158-159`: all post-power-on entries at ONE timestamp); a store into an `m` that
  already holds a post-power-on entry at another timestamp breaks `oneShotOk`, so `rsvWordOk` is UNPROVABLE for `.pub` — the
  rule as it stands cannot write `started`.  The history-AWARE obligation exists one level down: `rsvStoreOk` (`WpAtomic.lean:432-437`,
  takes the window's histories `Hs`), reached by `rsvWordOk_storeOk` (`RsvCell.lean:40`) — so the fix is a variant of
  `ctxBytes_writeAURsv`/`execSpecF_sw_rsv` stated over `rsvStoreOk` with the half cell's history (the image's, no post-power-on
  entry) — an edit to `MachCSL/RsvCell.lean` (not among the 13 files).  (ii) `started` today is an ORDINARY heap word: `StartedInv.lean:51`
  ("The window is a `WordHist` cell (`wordCell startedAddr 4 0 0 W`)"), `startedArmed :120-121`/`startedUnarmed :125-126` hold
  `wordCell startedAddr 4 …` at full ownership, `started_readAUr :255`, `started_writeAUT :391`; the boot carve hands it out of the
  `.bss` window — `BootCarveProc.lean:800-806 bcpBssWindows` ("`started` is the handover's cell"), `BootShared.lean:223-226
  bcpBssWindowsR` over `rsvErase KernelRsv.static`.  Once `⟨started, .pub 0⟩ ∈ KernelRsv.static` (`KernelRsv.lean:75-76 xv6RsvStatic`,
  with its `decide +kernel` well-formedness checks and `BootRsv.lean`'s `bootRsvHalves` groups `:15`, `bootRan_rsvErase :113`,
  `bootRan_lockHole :207`), `rsvErase` REMOVES those four bytes from the carve and the mint hands the client a HALF at the image
  history (`rsvHalvesC`); `bcpBssWindows`/`bcpBssWindowsR` no longer type-check on the `started` window, and `StartedInv` must be
  restated over the reserved half cell (reads at a fraction are fine; the write is (i)'s rule).  This is β′'s `WpLockInit.lean`
  (315 lines, NEW) pattern for one word: ≈ 0.3–0.5k, four `Xv6/` files + `RsvCell.lean`, absent from (a)'s cost line
  ("≈ 0.5–1k + the 18 creation sites") and from the RELAUNCH's gate sentence (which names only `KernelRsv.static`, `StartedInv`'s
  read, the 18 creation files, `SpecMain`/`ProofMain`/`MainSecondaryParts`).  Mark: (a) is FAITHFUL (an obligation xv6's code
  meets); this is mechanism and size.
  *Exact change (S, text — §D Q-F2-BOOTGATE (a) and the RELAUNCH gate sentence `:1836-1839`).*  Append to (a)'s "what changes":
  "`started` joins `xv6RsvStatic` (`KernelRsv.lean:75`, the `decide` checks re-run); the boot carve's `started` window
  (`BootCarveProc.lean:802 bcpBssWindows`, `BootShared.lean:223 bcpBssWindowsR`) moves to the reserved half (`BootRsv.lean`
  `bootRsvHalves` gains the `.pub` group); `StartedInv` is restated over the half cell (`wordCell … 0 0 W` → the reserved half at
  the image history; `started_readAUr` at the fraction; `started_writeAUT` via a HISTORY-AWARE reserved store — a variant of
  `ctxBytes_writeAURsv`/`execSpecF_sw_rsv` (`RsvCell.lean:91,127`) over `rsvStoreOk` (`WpAtomic.lean:432`), because the history-free
  `rsvWordOk :33` cannot discharge `oneShotOk`); the gate is issued inside that read's atomic step (`memModel_gateIssue
  :129` needs `gateOk (chainEnv σ') j`, true by `HRead.afterLoad`'s foreign stamp, `TsoMem.lean:312-316,356-358`)".  Cost line: "≈
  0.5–1k + the 18 creation sites **+ ≈ 0.3–0.5k for the `started` reservation (`RsvCell`, `KernelRsv`, `BootRsv`, `BootCarveProc`,
  `BootShared`, `StartedInv`)**".  Files list: + `RsvCell` (MachCSL) and the five `Xv6/` files.  One more sentence, for honesty about
  the landed lemma: "`memModel_chainHop :170` takes `gatePassedAt B` for EVERY hop conversion, not only for boot-era coverage
  (`valid_hop :347-350` needs `gateOk X B` in all three arms' bookkeeping); every acquiring hart therefore needs its gate — true in
  xv6 (a secondary acquires nothing before its spin), and the reason the acquirer's own context flag, not only the creator's handle
  flag, must be ≥ 1 at every acquire".

## SUGGESTIONS

- **[R35.s1] Stale cites in rev 38's new text.**  `RsvKind.pub w :120` → `:123` (`Reserved.lean`; `:120` is `| lock`); `CtxId … :432-438`
  → `:432-441` (`gate` is at `:441`); the RESULTS line's `readAU (WpAtomic.lean:403)` is right and `PROGRESS-W8f2.md`'s `:399` is the
  stale one.
- **[R35.s2] The "wiring breaks exactly …" list (`:1829-1832`).**  The tip's `Xv6/` files stating `ctxStamped`/`ownCtx_intro` are
  `BootCarveHart`, `BootShared`, `BootSharedText`, `ForkretRecord`, `IcacheCover`, `IcacheInvRef`, `IcacheTable`, `ProofScheduler`,
  `SchedCtx`, `SpecRelease`, `StartedInv` (11); the plan lists `IcacheRef` (exists, no such statement) and omits `BootCarveHart`,
  `BootSharedText`.  Write "at least" and the grep, not "exactly".
- **[R35.s3] The WIP path.**  `PROGRESS-W8f2.md` says `claude-notes/w8f2-s2-wip/` (neither the tip nor `../xv6iris-weak-w2` has it);
  the plan's `~/dev/weak-orch/parked/w8f2-s2-wip/` is the real one.  One clause in the RELAUNCH: "PROGRESS's `claude-notes/…` path is
  stale; the parked copy is authoritative".
- **[R35.s4] The `lint.sh` drift sentence (`:1845`).**  "`MachCSL.lean:261` already imports `ChainCert` — `lint.sh`'s drift finding closes
  once a root reaches it" reads as if still open; `lint.sh:12-13` defines drift as "imported from the roots lake builds", `MachCSL.lean`
  IS that root, and rev 38's RESULTS already say "audits PASS".  Write "closed by the `MachCSL.lean:261` import".
- **[R35.s5] Name the `coh` receipt gap once.**  There is no persistent ghost for `HRead.coh` (grep `Resources`/`Ctx`/`Wp`: none), so
  the gate and every S3 chain obligation at a racy load must be established INSIDE the load's atomic step (`readAU`/`readAUr`
  continuations see `memModelAt σ'`), never from a post-hoc receipt.  One sentence in S3 saves the worker a detour.
- **[R35.s6] Q-F2-PIPEHOP's *Why it matters*.**  Add the last-`pipeclose` case (`SpecFileclose.lean:4-12`) as the second concrete
  example — it is the one that falsifies the current (a) and the one an xv6 reader will think of first.

## Owner questions the plan is missing

None requiring a NEW ruling.  [R35.1] and [R35.2] correct the TEXT of two questions that are already OPEN and provisionally
adopted; both corrected options stay FAITHFUL (they restrict the chains the proof claims, or add an obligation xv6's code meets;
RVWMO, the Sail model, Zifencei and the PMAs are silent on how a proof partitions or registers hop words, as the questions'
*Spec (FIRST)* paragraphs already say).  The coordinator may apply both as addenda and relaunch; the owner's eventual ruling on
Q-F2-PIPEHOP should be taken over (a′)/(b)/(c), not over the current (a).
