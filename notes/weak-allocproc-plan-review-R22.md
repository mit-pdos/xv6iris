VERDICT: NOT SATISFIED

# Review R22 of `notes/weak-allocproc-plan.md` (rev 25)

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git or jj, no subagents).  Every
cite below was read at the working-copy tip of `../xv6iris-weak`.  Scope per the R22 brief: verify rev 25's
application of R21's four required changes and decide whether W-DISK and the W8-design spike are launchable
as written.  Items (a)/(b) of the standing brief were settled in R1–R21 and are spot-checked, not re-litigated.

**Sign-off.**  NO — three required changes, all S text, one revision.  Two are substantive: **[R22.1]** the
W8-design spike's deliverable list omits the two decisions that fix W8's size and lane (how the ledger is FED,
and how the export reaches a ROOT theorem), so the pin it produces could still mis-size W8 as "one cone rebuild";
**[R22.2]** the W13 (I) `gfDev` criterion the plan writes into §A(†), §C W-DISK (M4)/(iv) and W-DISK-Q2 —
"`(i,k) ∈ gfDev ↔ dvi k ≠ dvo k` with `gisIo → gfDev` (every I/O event moves the fabric) and the used-idx
`LStore` the ONE non-I/O member" — is false on both counts at the tip (an LSR read and the virtio NOTIFY write
leave the fabric unchanged; under the W-DISK MECHANISM three to four `DWriteDev` stores per request change
`dvirtio`), and as written would make `xv6ConfS` unsatisfiable for xv6.  The third, **[R22.3]**, is the plan's
authoritative `Lang.lean` cite-drift line, stale since W-DMA0, which W-DISK's binding MECHANISM text relies on.
W-DISK and W8-design are launchable once these are written; nothing requires an owner ruling (the [R22.2]
delta is a consequence of [OWN.31]+[OWN.32] and should be REPORTED, see the owner-questions section).

## What was checked and holds

- **[R21.1] applied.**  W8 left the parallel launch set (`:1057-1065`, Status `:2249-2251`, D26 `:2915-2917`);
  the W8-design spike (S, read-only) is specified at §C W8 `:2183-2190` with three deliverables (export
  statement = D24, the ledger's file/lane, the (β) coverage question); the W8 ledger is the next serial MachCSL
  item before W-RSV (`:1755-1760`, header `:3-7`); §B(12) `:1025-1026` no longer calls W8 `Xv6/`-only; D24
  `:2908-2911` is marked "PINNED by W8-design"; the stale Deps line is fixed (`:2205-2206`).  Q-W8-lane is
  recorded RULED (α) [OWN.36] (`:2306-2339`) in the 2026-10-10 format.  See [R22.1] for what the spike must
  ALSO pin.
- **[R21.2] applied and consistent with the code.**  §B(10) `:764-768`, §C W11 (iv)b `:2227-2230` and G1-Q
  `:2653` now consume `linCandScaT :757`/`linCandScaTMinus :787` on the NORMALIZED `GD'`, not
  `linCandScaTCatT :780` (which needs `grule14 GT.gtG`, `RvwmoXv6ScaT.lean:780-781`; `grule14` is
  `WeakRvwmoGraph.lean:266-267`).  `normalizeOfAcyclic` (`WeakRvwmoTopo.lean:596-610`) concludes
  `rvwmoMinusDepsConsistent GD' ∧ grule14 GD'.gdG ∧ rowsRel ∧ gdDeps = ∧ wperm`, so TODAY's output already
  feeds `linCandScaTMinus`.  W12 (1) gained the producer `gppoCat6Gmo GD'.gdG` (`:1961-1964`); the file's own
  `linCandScaTMinus` proof uses `gppoCat6Gppo` (`:787-790`: cat's six arms ⊆ `gppo` given load value), which
  confirms the plan's reasoning that a topo order extending `racy`'s `gppo` arm (`WeakRvwmoAcyc.lean:196-198`)
  — or the C-chain's `rsameC` — yields `gppoCat6Gmo` on `GD'`.  Marked unverified, S–M: fine.
- **[R21.3] applied.**  (a) IN zero-length is 1 → 5 at `:1370` and `:1492-1494`, and the five steps are
  real: `serve` is `:521-554` with `setPhase .fetched :526`, `fill`'s `get :489`/`dmaWriteIf r.buf n :491`,
  `setPhase .served :534`, the status `dmaWriteIf :536`; the OUT path is `guard taken :529`, `capture :515-518`
  (`dmaRead :516`, `modify :517-518`), status `:536`, `setPhase .status :537`, gate `:539-541`, `get :542-544`,
  used element `:546-548`, idx `dmaWriteStep … complete :552-554`; `body :558-587` (`get :561`, `get :567`,
  refusal `:568`, pop guard `:576-578`, `fork :579`, drains `:582-586`).  (b) the single-burst invariant is gone
  (`:1359-1362`, `:1586-1591`), restated as "at most one entry belongs to a LIVE task; the rest are zombies or
  finished; `R-dev`'s equality makes them harmless".  (c) F9's scope lists every `SimRel.dev` consumer
  (`:1067-1069`, `:1280-1285`, `:1348-1353`, `:1550-1556`); the cites hold at the tip: `SimRel.dev :315`, `hdev`
  consumed at `MachOfPf.lean:869, 906, 918, 935, 943-958, 989, 1003, 1061`, the MMIO arms `:1007-1038`, `simDev`
  via `devStepOfFdev … hdev.symm` at `:1253, :1266`, `simWire :1301-1354` (`hdev` also at `:1353`, see
  [R22.s1]); `pdiskUart` keeps `dp' = dp` (`WeakEvInst.lean:519-525`).
- **[R21.4] applied.**  W5 CORE is CONDITIONAL on `Hyps.disk`, called plumbing, not registered, with the
  four-discharge acceptance and the "`SimRel` only through `MRun`/`pfObsOf`/`cutOfPristine`" check
  (`:1733-1741`, `:1060-1064`, `:2250-2251`); `MachOfPf.lean`'s header deviation 3 (`:58-60`, "its owner is OPEN")
  is to be corrected to [OWN.35].  `cutOfPristine :1588` indeed takes `SimRel DR c st t g` in `Hyps.cut`'s exact
  shape and uses only `winPristine :1559` + `pow`/`mem`/`auth`; `MRun :131` is `Language.NSteps n`, so
  `Hyps.safe`/`winPristine` are instantiations of `xv6FsAdequacy_closed`/`xv6TextAdequacy_closed`
  (`Xv6/LinkSystemAdequacyClosed.lean:20-26`, `Xv6/LinkTextAdequacy.lean:26-35`) at `g := g0` (`gen = 0`,
  `pow = false`, `diskOf ds = fsImgDisk`) — see [R22.s3].
- **[R21.s1]–[R21.s4] adopted.**  `sailCycleOrder` in label-list form (`:279-281`, `:927-937`, `:349-351`,
  W5 `:1729-1730`); `shStepF` (`TsoShadow.lean:310-318`) sets `fiArm` at `.LInstr`, clears at `.LIFetch`, else
  keeps it — the one-fold derivation of `Hyps.fi :635` is sound as described; W-SCO covers every 2-aligned word of
  the window (`:1747-1751`); the capture-`DRead` 1 → 0 case (`:1342-1343`, `:1543-1544`); the cite/stale-text
  fixes (`:1488`, `:2178`, `:2921-2922`, `:1519-1520`).
- **The W-DISK MECHANISM against `serve`/`body`/`DevLang`.**  `DevM.guard :125`, `dmaWriteIf :157`,
  `dmaWriteStep :163` (`MachCSL/Dev/DevLang.lean`); `devOpStep`'s `dmaWrite` arm (`Lang.lean:570-574`: write iff
  `g s = some s' ∧ ramBytes ∧ ¬ anyReserve`, else the no-op skip `σ' = σ`); `reset :260-262`, `write :291-325`
  (`offQueueNotify → some v`), `completeOk :412-416`, `pushOk :419`, `complete :423-426`, `drain :429-432`,
  `alistSet :233-234`.  The idx node, the used-element `pre` (pre-check → `.status` → `drainAll` → gate with
  `completeOk` verbatim → `get :542-544` fused), the status write's `pre`, `pre₁` on the OUT capture segment and
  the (α) ABORT all match the code.  `pdevOk` (`WeakPromiseFact.lean:613-614`) and today's label-only `pdevEv`
  (`WeakEvInst.lean:544-547`) are as cited; the state-aware form keeps `pdevOk` for `LSilent` abort/skip steps.
- **(a)/(b) spot checks.**  `Xv6.Allocproc` (`Xv6/LinkAllocproc.lean:14-16`) is `allocproc_proof` parametric in
  the six callee interfaces (`ProofAllocproc.lean:3620-3639`); `wp_allocproc_body`'s premises are as listed
  (`SpecAllocproc.lean:204-224`); the baseline (`tools/audit/baseline.json:11-14`) and roots (`roots.txt:6`, `:19`)
  are as cited; `audit.sh --weak` audits a HARDCODED module list (`audit.sh:44`), as §B(12) says.
  `srvwmoConsistent`'s residue table (`WeakAxiomatic3.lean:2062-2084`) is as §0 F1 describes.

## REQUIRED changes

- **[R22.1] W8-design must also pin HOW the ledger is fed and HOW the export reaches a root theorem — the two
  decisions that fix W8's size class.**
  *What is wrong (evidence).*  §C W8-design (`:2183-2190`) pins (1) the export statement, (2) the ledger's
  file/lane, (3) the (β) coverage.  §C W8 then sizes the ledger as "mechanical but wide, one ≈ 0.73M-line
  `Xv6`-cone rebuild" (`:2198-2200`) and §C "FOUR SERIAL items" says "`Xv6/` NAMES neither reservations nor
  `coh`" as the pattern (`:1760-1764`).  Neither claim can be made before two further decisions:
  - **Feeding.**  The `mmOk` idiom is a PURE predicate on `σ` carried as `⌜mmOk σ⌝` inside `memModelAt`
    (`MachCSL/Resources.lean:779-785`, `:951-956`) and re-established by every memory rule GENERICALLY (no
    program knowledge).  W8's (ii) "a protected access under a held lock" is not generically re-establishable: the
    store rule cannot know that the byte it writes is `proc[3].state` and that `proc[3].lock` is held — only the
    `Xv6/` proof (through the lock invariant's points-to, `procHeld`) knows it.  So the ledger must be FED by the
    `Xv6/` proofs, and the brief must say WHERE: (f1) at every protected load/store rule application (an `Xv6/`
    SWEEP of thousands of `swp_*` sites — XL, and NOT "a rebuild"); (f2) at the lock layer only (`acquire`/
    `release` specs hand a holder token to the state interpretation, and the protected cells' points-to are wrapped
    so a store through them records the holder — the number of such wrapper layers is the cost, M–L if `procHeld`
    and its siblings are the only doors); (f3) derived from `σ` alone for (i) ("no foreign writer" is a function of
    `HEnt.tid` over the byte's history given a static ownership map) — the (β) question, already listed.  The
    W-RSV precedent ([R12.1][R13.1]: "NAMES untouched" ≠ "FILES untouched", 12 `Xv6/` files) is exactly the
    mistake to avoid.
  - **Root path.**  The export must appear in a ROOT theorem's conclusion.  Either (r1) it enters `mmOk` (a
    conjunct of the existing invariant: `xv6FsAdequacy_closed`'s TEXT is unchanged — `xv6TracePure cov ls g :=
    fsBootPure … ∧ (g.pow = true → mmOk g.m)`, `Xv6/SystemSlot.lean:135-136` — but its MEANING strengthens, and a
    ghost ledger needs an existential inside `mmOk` or a state-side mirror), or (r2) a SIBLING root as W3 did
    (`xv6TextAdequacy_closed`, with power/boot/system twins: `MachCSL/PowerText.lean` 734, `Xv6/BootSharedText.lean`
    250, `Xv6/SystemBootEraText.lean` 196, `Xv6/SystemAdequacyText.lean` 580, `Xv6/LinkTextAdequacy.lean` 35 — ≈
    1.8k lines, plus `roots.txt`/`baseline.json`/`tcb/expected.json` entries).  (r2)'s cost alone is the size of
    W3.
  *Exact change (§C W8-design `:2183-2190`; §C W8 `:2198-2200`; D24 `:2908-2911`).*  Add deliverables "(4) the
  FEEDING path of each class (i)–(iii): (f1) per-site / (f2) lock-layer / (f3) state-derived, with a COUNT of the
  `Xv6/` sites or wrapper layers each touches — the ledger is 'one cone rebuild' ONLY under (f2)/(f3); (5) the
  ROOT path: into `mmOk`/`xv6TracePure` (statement text unchanged, meaning strengthened — say so in §A(6)) or a
  sibling root on the W3 pattern (≈ 1.8k lines of twins, listed above)".  Make §C W8's "mechanical but wide, one
  cone rebuild" CONDITIONAL on (4) = (f2)/(f3), and record (f1) as the XL outcome that would re-open the lane
  decision ([OWN.36] was ruled on the "one rebuild" cost).  S text.
- **[R22.2] The W13 (I) `gfDev` criterion as written is unsatisfiable for xv6, and "the used-idx `LStore` is the
  ONE non-I/O fabric move" is false under the plan's own MECHANISM.**
  *What is wrong (evidence).*  §A(†) `:359-365`: "`(i, k) ∈ gfDev ↔ dvi k ≠ dvo k` … with `gisIo (i, k) → (i, k)
  ∈ gfDev` (every I/O event moves the fabric) and the used-idx `LStore` of each completed request the ONE non-I/O
  member"; repeated at §C W-DISK (M4) `:1419-1420` ("the ONE RAM store that moves the fabric"), (iv) `:1649-1650`,
  W-DISK-Q2 `:2475-2477`, Status `:2260-2261` and §A(6) `:257` (the trusted-surface sentence "one RAM store per
  completed request is a fabric move").
  - **Non-moving I/O events exist on every path to `allocproc`.**  `pnodeStep`'s MMIO read arm is `devRead d
    req.pa n = some (w, d')` with `l = LDev .rd …` (`WeakEvInst.lean:300-305`); `devRead` routes to
    `(devSig d).read` (`MachCSL/Dev/Fabric.lean:138-141`).  UART `read :109-123`: LSR is `some (lsr u, u)` (`:120`)
    — the state does NOT move (so are IER/LCR/MCR/MSR/SCR; only RBR with a non-empty FIFO and ISR with THRI move).
    Virtio `readN :337-338` returns `(…, v)` with `v` unchanged for EVERY register (`read :268-289` yields a value
    only).  PLIC `read :123-136`: prio/pending/enable/threshold reads return `p` unchanged; only the claim moves.
    Writes too: `Virtio.write :311` answers `offQueueNotify` with `some v` — the NOTIFY the driver issues for
    every disk request moves nothing (the root loop polls the ring).  So for `uartputc_sync`'s LSR polls
    (`0x800009ec`, hart 0's `printf` before `userinit`) and every NOTIFY (`0x80005c92`), `dvo k = dvi k` while
    `gisIo (i,k) = true`.  Under "`gisIo → gfDev` ∧ `gfDev ↔ dvi ≠ dvo`" such a row has no conforming emission:
    `xv6ConfS` is UNSATISFIABLE for xv6 — the same vacuity shape as `emDevfree`'s, one level up.  The landed
    INTERIM clause `gfIoDev :172` (`gisIo ↔ gfDev`, by CLASS) does not have this defect; the planned (I)
    restatement introduces it.
  - **Several non-I/O fabric moves per request, not one.**  Every `DWriteDev` applies its `pre` and `g` to
    `dvirtio` at the write (`:1512-1521`, `:1559-1563`): the status write's `pre` performs `setPhase .fetched :526`
    (+ `taken :529`, capture's `cacheReq ∘ setPhase .served :517-518` for OUT; `setPhase .served :534` for IN), the
    used-element write's `pre` performs `setPhase .status :537`, `drainAll` and the gate's `setPhase .pushed`, the
    idx write's `g` is `complete`; the IN fill's `pre` carries `:526`.  Each changes `inflight`/`cache`/`taken`,
    so `dvi k ≠ dvo k` at three (OUT) or four (IN) `LStore`s per request — all `gfDev` members under the endpoint
    criterion, all realization-necessary under [OWN.32] (a) (each reads the device state through its guard; the
    trace must place it where the pf run did relative to hart MMIO).  An `LSilent` ABORT/skip with `d' ≠ d` is an
    ADMIN step (no `Geid`): its move sits inside `hemitf`'s `admRun true p (dvi k) ls pa da` (`WeakRvwmoFab.lean:
    239-250`), which already threads the fabric — but (I) must not re-impose "admin runs are fabric-constant"
    (`admRunDevfree`, `WeakRvwmoSupply.lean:175`) on device-active disk rows beyond W-DISK's `devQuiet` form.
  *Exact change (§A(†) `:359-365`; §A(6) `:257`; §C W-DISK (M4) `:1419-1420`, (iv) `:1649-1650`; W-DISK-Q2
  `:2475-2477`; Status `:2260-2261`; §C W13 (I) `:2054-2057`).*  "(I)'s clause: `(i, k) ∈ gfDev ↔ (gisIo (i, k)
  = true ∨ dvi k ≠ dvo k)` — every I/O-class event by CLASS (its VALUE depends on the fabric at its position even
  when it moves nothing: LSR, NOTIFY, every virtio register read), plus every non-I/O item whose step moves the
  fabric; at a non-moving member `fab (n+1) = fab n`.  The non-I/O members are the disk row's `DWriteDev` stores
  whose step changes `dvirtio` — under the MECHANISM the status, used-element and used-idx stores of every request
  (phases, cache, latch; `complete` at the idx store), and the IN fill when its `pre` carries `:526`.  (R3) orders
  them against hart MMIO events as the fabric serializes them: STRONGER than the spec's silence by exactly that,
  EQUAL to MachCSL's step structure, realization-necessary under [OWN.32] (a) (each store's guard reads the
  device state).  `LSilent` abort/skip moves are admin-run moves, not `gfDev` members; (I) keeps `hemitf`'s
  threaded fabric through admin runs on the disk row."  Replace the trusted-surface sentence by "the device's
  request-service RAM stores are fabric transactions (each reads the device state at the store and may move it);
  the used-idx store is the one that raises the interrupt".  REPORT the delta of [OWN.31]/[OWN.32] to the owner
  (no gate recommended; see the owner-questions section).  S text; W13 (I)'s size (M on the fabric side)
  unchanged; W-DISK's header must not say "the ONE RAM store that moves the fabric".
- **[R22.3] The plan's authoritative `Lang.lean` cite line is stale since W-DMA0, and W-DISK's binding text
  cites through it.**
  *What is wrong (evidence).*  §A's [R16.s1] line (`:441-446`) declares itself the superseding authority for
  `Lang.lean` cites ("Older `:N` cites … are superseded by this line") and gives `storeDma :171-173`, `dmaView
  :189`, `blockedStep ≈ :402-409`, `hartStep :504-506`, `dmaRead :539`, `anyReserve` guard `:542`, `devBlocked
  :561`, `devStep :575`.  W-DMA0 inserted the `storeDma` docstring and `storeDma_zero`/`storeDma_of_ne`
  (`:176-193`), shifting everything below by ≈ 30 lines.  Tip: `MState.afterLoad :128`, `MState.store :151`,
  `MState.storeDma :181-183` (`storeDma_zero :186`, `storeDma_of_ne :191`), `dmaView :218`, `setDev :222`,
  `bootShape :336`, `blockedStep :431`, `hartStep :533-538` (`.pure` arm `:535`), `devOpStep :560-584` (`dmaRead
  :569`; `dmaWrite` arm `:570-574`: `anyReserve` guard `:572`, the skip disjunct `:574`), `devBlocked :590-598`,
  `devStep :604-616` (`.pure`: root restart `:609`, done-marking `:610-612`; `.op`: step `:614`, blocked `:615`),
  `primStep :632`, `primStep_power_on :715`.  Binding text that cites the OLD numbers: W-DISK MECHANISM
  `Lang.lean:544` (skip arm, `:1466`, `:1523`, `:1530`), `devBlocked :561-563`/`:563`/`:567` (`:1527`, `:1545`),
  `devStep :575-577` (`:1527-1528`, `:1535`), `Lang.lean:569-573` (`:1590`); §C W4 F9 `Lang.lean:586` (`:1359`),
  `devStep :580` (`:1367`), `devStep :581-583` (`:1374`), `Lang.lean:544` (`:1373`); W-RSV `hartStep .pure
  Lang.lean:499-502` (`:1851`), `:500-505`/`:504-506` (`:1848`, `:705`); §A `:1486` already has `:181-193`.
  *Exact change.*  Rewrite the `:441-446` line with the tip numbers above (keeping its "supersedes" sentence) and
  fix the W-DISK MECHANISM and §C W4 F9 cites listed, since those two texts are binding and launch now.  S.

## SUGGESTIONS

- **[R22.s1] Cite drift in `MachOfPf.lean`.**  `simWire` runs to `:1354` (`hdev` is consumed at `:1353`), not
  `:1339`; `Hyps :620` with `tso :622`, `safe :623`, `cut :625`, `fi :635`, `disk :644` — the plan's `:635` for `fi`
  is right, its `Hyps :620-660` should be `:620-657`.
- **[R22.s2] W-DISK's `pdevEv` text.**  The state-aware marker `pdevEv p l p' := lbIsdev l || (p = .PDisk (some
  (DWriteDev ..)))` is stated on `p`; say also that `pdevEvFalse` (`WeakRvwmoSupply.lean:164-166`) is currently
  proved by `cases l`, so its `devQuiet p` restatement is a new proof, not a hypothesis edit (S, already inside
  [R17.3]'s S).
- **[R22.s3] W5 CORE's brief: name the instantiations.**  `Hyps.safe` is `xv6FsAdequacy_closed g0 rfl rfl hdisk n
  κs t g hsteps |>.1` with `g0.pow = false` and `diskOf ds = fsImgDisk` from the premise's `ds`; `winPristine` is
  `xv6TextAdequacy_closed … |>.2` read through `textWin_get` for every `pa ∈ [bcRoLo, bcRoHi)`; `cutOfPristine`'s
  `hlo : ramBase ≤ lo`/`hhi : hi ≤ ramEnd` are `Xv6/BootCarve.lean` facts.  One line each saves the worker a
  search.
- **[R22.s4] W-DISK header wording after [R22.2].**  The "Deviations from MachCSL's `serve`" table should carry a
  column "moves the fabric?" per node (START, POP, fill, status, used element, used idx: yes; `DRead`s, `DFence`,
  `DStall`, `DRet DIdle`: no), since (I) reads the fabric-move set off exactly that.
- **[R22.s5] §B(11) (vi).**  Add the [R22.2] consequence there too: the `dev`-kind pop plus the request's
  fabric-moving RAM stores are the disk row's `gfDev` members; the I/O-class events of hart rows are members by
  class whether or not they move the device.

## Owner questions the plan is missing

- **Q-GFDEV-delta — REPORT level (a delta of [OWN.31]/[OWN.32], no gate recommended): which row items count as
  fabric moves in the published conformance premise.**  Raised by [R22.2].
  - *Spec, per the OWNER RULE (FIRST).*  The RVWMO chapter and riscv.cat have no device-internal events and no
    notion of a device's register state; the Sail model in this tree has no device/DMA model (`MachCSL/Dev/*.lean`
    is the only device text; an MMIO access is an ordinary `mem_read`/`mem_write` routed by `devAddr`,
    `MachCSL/Dev/Fabric.lean:126-141`); Zifencei is silent; the PMAs give strong ordering within one I/O channel
    only.  virtio 1.x says the device reads the ring and descriptors and writes used elements/index; it does not
    say when a device re-reads its registers.  Every option below is STRONGER than this silence (device-model
    text, D45/D49 class) and none changes the published CONCLUSIONS.
  - *Plain language.*  The published premise `xv6ConfS` lists, per row, which events are "fabric transactions" —
    steps at which a device's registers or the device's own bookkeeping are read or changed — in the order the
    devices served them (`gfDev`); the platform assumption (R3) then says the memory order agrees with that order.
    The plan said only I/O accesses and ONE disk-side store (the used-index write) are fabric transactions.  At the
    tip, an I/O READ of a status register changes nothing (so the "changes the fabric" test would miss it, though
    its VALUE depends on where it sits), and the device's status/used-element stores DO change the device's
    bookkeeping (their guards read it, per [OWN.32]'s folding).
  - *Tiny example.*  Hart 0 polls the UART line-status register (reads `LSR`, nothing changes) and then writes a
    byte to `THR`; the disk, serving a request, writes the status byte into RAM — its guard first checks the request
    is still in flight and marks it served.  Outcome under the plan's text: the `LSR` read is an I/O event that
    "must" be a fabric move yet moves nothing — no emission conforms, the whole execution is outside the quantifier
    (vacuity).  Outcome under the fix: the `LSR` read is listed by class (the fabric sequence stutters there), the
    status store is listed because it moved the device's bookkeeping, and (R3) orders both against hart 1's MMIO.
  - *Definitions.*  **Fabric** (`Efab`): the devices' registers, wires and internal state (for virtio: the
    in-flight phases, the write cache, the capture latch).  **`gfDev`**: the list of row items that are fabric
    transactions, in fabric order.  **`gisIo`**: an item is an I/O-class event (a hart MMIO access, a pin
    delivery, a device-thread move, the disk's START/pop).  **`dvi k`/`dvo k`**: the fabric before/after row item
    `k`.  **(R3)**: "I/O events are gmo-ordered as the fabric serializes them" (`GraphFabResidue.lean:84-99`).
    **`DWriteDev`**: W-DISK's disk-side RAM store whose guard reads the device state and may move it.
  - *Why it matters.*  The trusted-surface sentence changes from "one RAM store per completed request is a fabric
    move" to "the device's request-service RAM stores are fabric transactions"; (R3) then couples three to four
    disk-side stores per request (instead of one) to hart MMIO order.  Conclusions are unchanged; the quantifier
    omits executions in which those stores are reordered against unrelated MMIO — executions the one-row device
    model (D51) already excludes in spirit.
  - *Options.*  **(a) RECOMMENDED — `gfDev ↔ gisIo ∨ (dvi ≠ dvo)`; every `DWriteDev` store that moves `dvirtio`
    is a member.**  What changes: §A(†)/(I) text only; (R3) over those stores.  STRONGER than the spec by (R3) on
    them; EQUAL to MachCSL; realization-necessary under [OWN.32] (a).  Cost: S text now, nothing in (I)'s size.
    Unblocks W-DISK/(I) consistently.  Risk: none beyond the honesty line.  **(b) keep only the used-idx store in
    `gfDev`.**  Then the realization cannot place the status/used-element stores relative to hart MMIO although
    their guards read the fabric — the (L) trace existence fails; not available under [OWN.32] (a).  **(c) re-rule
    [OWN.32] to (b): pure device-state reads as `LDev .dev` events, the stores plain.**  FAITHFUL to the same
    executions; the `dev` events carry (R1)–(R3) instead of the stores; cost +S on (I) text and a W-DISK brief
    change before launch; no benefit over (a).  The owner's own folding ruling made (a) the only consistent
    reading, hence REPORT, not a gate.

No other owner question is needed.  [R22.1] and [R22.3] are plan text in the sound direction; the plan's
existing RULED questions carry their "Spec:" lines and meet the 2026-10-10 format.
