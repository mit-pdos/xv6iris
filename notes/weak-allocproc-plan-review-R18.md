VERDICT: NOT SATISFIED

# Review R18 of `notes/weak-allocproc-plan.md` rev 21 (adversarial, evidence-based; 2026-10-11)

Scope (per the R18 brief): rev 21 = rev 20 + R17's four required changes with two -alts + [OWN.33].  Audited: (1) the
four R17 changes and the -alts against the code they cite — `MachCSL/Dev/Virtio.lean` (`serve :521-554`, `body :558-587`,
`completeOk :412-416`, `pushOk :419`, `complete :423-426`, `reset :260-262`, `write :291-295`, `read :268`, `readN :337`,
`VirtioState :209-224`, `cacheView :359-362`), `MachCSL/Dev/DevLang.lean` (`step`/`guard`/`modify`/`dmaWriteIf`/
`dmaWriteStep`, header), `MachCSL/Lang.lean` (`evStep :355-397`, `hartStep :504-508`, `devOpStep`'s `.dmaWrite` arm,
`devBlocked`, `devStep`'s blocked arm, `storeDma :170-172`), `Weak/WeakEvInst.lean` (EVERY `pnodeStep` arm `:280-395`,
`pstepNode :404-412`, `pstepPlic :464-473`, `pdiskProg :485-516`, `pdiskUart :518-526`, `pstepEv`, `pdevEv :544-547`,
`pdiskProgDevFree :1670`, `pdevEvOk :1694`), `Weak/WeakEvPf.lean:220-223`, `Weak/WeakPromiseBridge.lean` (`wpPfStep
:322-345`, `projLbl :530-544`), `Weak/WeakAxRealize.lean:129-133` (`lbAdmin`), `Weak/TsoShadow.lean:552-590`,
`Weak/PfStepTsoView.lean` (`hartRel :127`, `viewRel :135`, `rowFence :722-748`, `rowSfenceMarker :750-758`),
`Weak/PfStepTsoMem.lean:57-66`, `Weak/WeakEvLang.lean` (`erwLabel :404-408`, `sfAnnB :413`, `annLabel :419`, `dvirtio
:899`, `ediskStep :927-961`), `Weak/WeakPromiseFact.lean:611-660` (`pdevOk`, `wpAstepAfree`), `Weak/WeakRobustTrace.lean`
(`mkAev :356`, `ptracesDevOf :616`, `wpBehaviorFulfilOnceDev :1260`), the whole devfree family (`WeakRvwmoSupply.lean:
164-246`, `WeakRvwmoFab.lean` `lbIsdev :119`/`emDev :144`/`isDevBlock :152`/`hblk :285`/`hblkQ :318`/`hemitf :239-262`/
`hemitfStatesQ :347-460`/`hartConffStatesQ :471`/`gfexecConf :524-536`/`supplyOfFconf :689`/`fconfRowsPin`/`fconfSupply
:782-842`, `WeakRvwmoLin2.lean:997-1037`, `WeakRvwmoFabInd.lean:413-447`, `WeakRvwmoCapstone.lean:230-265`),
`Weak/VirtioProg.lean:606-623`, `Weak/WeakEvCapstone.lean:1026-1027,1183`.  (2) the folding rule's closing cases for
F9; (3) the `devQuiet` ripple; (4) strengthening (viii); (5) the launch set.  Advisory only; no proofs or builds (the
"TYPE-CHECKS" of the pinned statement is therefore verified by READING the binders, not by elaboration); no git/jj; no
subagents.  `file:line` cites `../xv6iris-weak`.

**Sign-off.**  NO — four defects in W-DISK's BINDING text, all S text, none touching the published statement.  The
other four launch items are launchable as written.  (i) **[R17.1-alt]'s `pre`** is right that the folded `setPhase`s
must reach the pf fabric, but it still cannot deliver "`R-dev` stays EQUALITY incl. phases": on the OUT path MachCSL's
`modify .fetched :526` and `taken` guard `:529` are program-ordered BEFORE capture's `dmaRead :516`, so the matched
MachCSL run performs them at pf's capture `DRead`, two pf steps before the status `DWriteDev` applies `pre` — equality
fails on that segment; and `pre` re-applies the moves to whatever state it finds, so after a mid-burst reset (`write
:295`: STATUS := 0 → `reset`, `inflight := []`, `taken := none`) pf RESURRECTS the request (`setPhase` on an empty map,
`:248-249`) while MachCSL's twin is a zombie — `R-dev` fails and pf later aborts requests MachCSL completes ([R18.3]).
(ii) **The (M9) START snapshot of `cfg`/`usedIdx`** is NOT what `serve` does: MachCSL re-`get`s at `:522` (fetch
addresses), `:489` (fill's `cacheView`) and `:541-543` (`ui`, `c` for the used element/idx), so on a config write between
START and `:541` MachCSL WRITES the used element at the NEW ring address while pf SKIPS — the plan's Mark "both skip,
SAFETY-EQUAL" is false, and F9 would need a driver fact ("no virtio config write mid-burst") the plan says it does not
need ([R18.4]).  (iii) **The payload path is specified twice, incompatibly**: (M8) "pf commits a write at the used-idx
step; `R-dev` carries pf `disk` = MachCSL `cacheView`" vs the FOLDING RULE (2) "capture's cache move `:518` → the next
fabric step's folded part" ([R18.1]).  (iv) **[R17.3]'s `devQuiet` threading cannot keep `lake build Weak` green
after W-DISK**: `hemitfStatesQ`'s second conjunct (`emDev false (n+k) es = false → dvo = dvi ∧ ∀ d, hblkQ Q d d …`,
`WeakRvwmoFab.lean:347-354`) is FALSE for every `DWriteDev` WRITE block (label `LStore`, no `LDev` → `emDev = false`,
yet `complete` moves `isr`/`usedIdx` → `dvo ≠ dvi`), and `devQuiet` at the ROW start cannot be threaded past the START
block (`.PDisk none → .PDisk (some _)`); `fconfRowsPin`/`supplyOfFconf`/`fconfSupply`/`fconfSupply'`/
`fconfTraceRealize`/`FabInd.fconfRealize`/`xv6RvwmoSafeModuloF :230` then have unsatisfiable obligations for a
device-active disk row.  The fix is an INTERIM clause in `gfexecConf`, not "a hypothesis with no proof change" ([R18.2]).

## What was verified (holds as cited; not to re-litigate)

**[R17.1] / [R17.1-alt] mechanics.**  `DevM.guard g = step (fun s => (g s).map …)` and `modify f = step (fun s => some
(f s, []))` (`DevLang.lean`); `devBlocked d (.step g) σ = ∀ s' os, g … = some (s', os) → ¬ devObsOk …` — vacuous when
`g = none`, so the blocked arm of `devStep` (`m' = m ∧ σ' = σ`) is a self-loop STUTTER the schedule need not take at
all ✓; `devObsOk .virtio _ _ os = (os = [])` (`Fabric.lean:95`), so a virtio `modify`/`guard` that answers never
blocks ✓; `.dmaWrite g`: `g = none ∨ ¬ ramBytes → σ' = σ`, the task CONTINUES ✓ (`Lang.lean`, `devOpStep`); `taken`
guard `:529` sits between `setPhase .fetched :526` and `capture :530`, `pushed` gate `:539-540` between `setPhase
.status :537` and the post-gate `get :541` ✓ — [R17.1-alt]'s observation that the abort must carry those `setPhase`s
is right.  `completeOk` (OUT) = `taken = some h && (wce cfg || !reqCached)` `:412-414`; FLUSH = `cache.isEmpty` `:415`;
`pushOk = inflight.all (!isPushed)` `:419` ✓; `complete` frees `taken` iff `= some h` `:426` ✓.  **[R17.2] /
[R17.2-alt].**  `Pexv6.PHart cpu m rs fn ib` with `fn : Option (Bool × Bool × Bool × Bool)` ✓ (`WeakEvPf.lean:220-222`);
`hartStep`'s match is `.impure (.ok o) k` (`Lang.lean:508`) so the node shape is right; `wpPfStep` takes `pstep pcls`
as section variables (`WeakPromiseBridge.lean:322-330`) ✓; `pfStepFactsT` uses only `fok stamp` of its section
(`TsoShadow.lean:552-556, 576`), so the argument order `pfStepFactsT fok cohSrc st c i l` is right ✓; `rmem c st σ`
(`PfStepTsoMem.lean:62`), `viewRel stamp σ st` (`PfStepTsoView.lean:135`), `evStep cpu o σ v σ'` (`Lang.lean:355`) ✓;
`sfAnnB n w` with `w : BitVec n` ✓ (`WeakEvLang.lean:413`), `rowFence`'s `hfi : b = .Barrier_RISCV_i → fiArm = true`
`:725` and `rowSfenceMarker`'s `fiArm = false` `:753` ✓.  **The five hypotheses are exactly the right exclusions**,
checked against EVERY `pnodeStep` arm: `fn = some _` → parked fire `m' = m` (`:404-409`) ✓ (a); `LSilent` arms:
`regRead` (`v = σ.regs cpu r` forced by `evStep :358`, pf takes `k (rs r)`), `regWrite` with `ERWnone` (`erwLabel`
`:406`), the retry self-loop (`:363-365`, `m' ≠ k v`), `branchAnnounce`/`cacheOp`/`tlbi`/`takeException`/
`returnException`/`translationStart`/`translationEnd`/`cycleCount`/`message` (`m' = k ()`, `evStep` `σ' = σ` — provable
but excluded uniformly), `getCycleCount` (`m' = k 0` ✓ = `evStep`'s `v = 0`), `choose` (`m' = k ch`, any) ✓ (b);
`LDev`: MMIO arms read `d.efDev` (`:305, :341`), `pstepPlic` keeps `m' = m` (`:468`) ✓ (b); the announce arm emits
`annLabel n w` ∈ {`LInstr`, `LFence false×4`} with `m' = k ()` (`:372-374`), the barrier arm `ebarLabel b` with `fn' =
ebarPark b` (`:367-369`) ✓ (c).  No arm is missed; `LRegW`/`LCtrl` (`regWrite`, `m' = k ()`, `evStep` → `setReg`) are
covered by the main theorem since `rmem`/`viewRel` mention only `mem log tv itv hr resv` ✓ (E-M2).  **[R17.3].**
`pdevEvFalse :164`, `pstepEvDevfree :169`, `admRunDevfree :175`, `admRunRefab :186`, `hemitDevfreeConst :202`,
`hemitDevfreeRefab :241` quantify an arbitrary `p : Pexv6` ✓ (false under the state-aware marker, as R17 said);
`devQuietStep` HOLDS: from `.PDisk none` the only `pdiskProg` arm is START (`LDev .dev`, `:488`) and every `pdiskUart`
arm is `LDev .dev` (`:520`) ✓; `epsInit`'s disk entry is `.PDisk none` (`WeakEvCapstone.lean:1027`) ✓; `lbAdmin .LDev =
True` (`WeakAxRealize.lean:131`) and `projLbl .LDev = none` (`:538`) — the START still rides in admin stars today ✓;
the robustness chain is parametric in `pdev` through `pdevOk` only (`WeakPromiseFact.lean:637`, `WeakRobustTrace.lean:
356, 616, 1260`; `WeakRobustAcyc*`/`Retag`/`Ser`/`Graph`/`Main` take `pdevOk pstep pdev` as a hypothesis) — a
dev-flagged `LStore` is simply recorded with `aeDev = some (din, d')` (`mkAev :356`), so `WeakEvCapstone.lean:1183`
stays unchanged in statement ✓.  **[R17.4] / (viii).**  `pdiskProg` holds ONE `Option (DM Dres)`, START only from `none`
(`:488`), `virtioProg` runs one request to `dcomplete` (`VirtioProg.lean:606-623`); MachCSL `fork (.serve h)` per pop
(`Virtio.lean:579`) ✓ — the text of (viii) and W-DISK-Q4 is accurate.  **[OWN.33]** recorded in header, §B(11)
(viii), §C W-DISK acceptance, Status, §D W-DISK-Q4 ✓.  **Suggestions s1–s5, s7** applied ✓ (`VirtioProg` map
`:1376-1387`; `pfDWriteRowMem` dropped from W-DMA0 `:1459-1461`; snapshot wording `:1278, :1285`; `ediskStepLabel`
wildcard `:1265`; F9 rows `:1230-1232`; launch set `:986-996`).  **Owner-question format**: every §D question opens
with "Spec:" and marks options ✓; no OPEN question ✓.  **Cites**: `Virtio.lean` `body` is `:558` (plan `:559`),
capture's `modify` `:517-518` (plan `:518`) — fine.

## REQUIRED changes

- **[R18.1] The payload path is specified twice, incompatibly; `R-dev`'s image clause is wrong under the folding
  rule.**  *What is wrong.*  §C W-DISK (M8) (`:1278-1281`) says "pf commits a write at the used-idx step as MachCSL's
  capture + later drain do" and "`R-dev` carries 'pf `disk` = MachCSL `cacheView`'"; the FOLDING RULE (2) (`:1325-1326`)
  folds "capture's cache move `:518`" (`cacheReq`, `Virtio.lean:496-502, 517-518`) into the status `DWriteDev`'s `pre`.
  Under (2) pf's `cache` holds the payload from the status write on and pf NEVER drains (no root-loop twin), so pf
  `disk` ≠ MachCSL `cacheView` is the NORMAL state (pf `disk` lags by the cached payload) and "pf `disk` = MachCSL
  `cacheView`" is false; under (M8)'s wording `cacheReq` must NOT be folded.  Two further consequences the brief leaves
  open: under (2) `reqCached` is permanently true in pf, and FLUSH's `completeOk` conjunct `cache.isEmpty` (`:415`) is
  permanently false — the brief excludes only `!reqCached` from the folded gate (`:1341-1342`).  *Exact change (choose
  ONE; the reviewer recommends (A), MachCSL's own shape):*  **(A)** keep FOLDING RULE (2) as written (capture's
  `cacheReq ∘ setPhase .served` in the status write's `pre`); pf never drains; `R-dev`'s image clause is
  **`cacheView (dvirtio_pf) = cacheView (dvirtio_M)`** (both preserved by MachCSL's `drain :429-432`, both moved
  identically by `cacheReq`), NOT equality of `disk` or `cache`; pf's folded gate uses **`completeOkPf v r h := if OUT
  then taken = some h else true`** — BOTH drain-dependent conjuncts (`!reqCached`, FLUSH's `cache.isEmpty`) dropped,
  discharged by inserting MachCSL `drain` steps before the gate in the matched run; (M8)'s sentence becomes "pf's
  payload enters `cache` at the status write's `pre` exactly as `capture` does; the DURABLE image `diskOf` is
  MachCSL-only ([R16.s3])".  **(B)** drop `cacheReq` from (2); pf's idx `g := complete ∘ (write the payload into
  `disk`)`; `R-dev`: pf `disk` = MachCSL `cacheView` EXCEPT between MachCSL's capture and the completion, where MachCSL
  `cacheView` = pf `disk` overlaid with the in-flight OUT payload — a phase-dependent clause.  (A) is one clause; (B)
  is two and departs from `serve`.  S, text; W-DISK and F9.
- **[R18.2] [R17.3]'s "`devQuiet` hypothesis, no proof change beyond it" cannot keep `lake build Weak` green after
  W-DISK: `hemitfStatesQ`'s per-block conclusion is FALSE for every `DWriteDev` write block, and the hypothesis cannot
  be threaded past START.**  *Evidence.*  `hemitfStatesQ` (`WeakRvwmoFab.lean:347-354`) concludes, for EVERY block `n`
  of the row, `emDev false (n+k) es = false → dvo (n+k) = dvi (n+k) ∧ ∀ d, hblkQ Q d d … (f n) (f (n+1))`; `emDev`
  (`:144-150`) and `isDevBlock :152` are LABEL-based (`lbIsdev :119`).  After W-DISK a used-idx `DWriteDev` block is
  `eadm [LSilent …] ++ [(LStore …, some k)]` — `emDev = false` — with `dvo = setDvirtio dvi (complete …)` (`isr`,
  `usedIdx` move, `complete :423-426`) ≠ `dvi`; likewise the used-element block whose `pre` sets `.pushed`.  So the
  conclusion is FALSE (not merely unprovable) for any `hemitf` emission containing such a block, and such emissions
  exist (`hemitf :239-262` is just the inductive over `pstepEv`).  The proof's per-block use of `pstepEvDevfree`
  (`:384-387, 431-438`) would need `devQuiet (f n)`; from the row start `.PDisk none` the START block (`LDev`, `emDev =
  true`) moves to `.PDisk (some _)`, so no later block is quiet — `devQuietStep` (`WeakRvwmoSupply`) cannot carry it.
  Consumers that then have unsatisfiable obligations for a device-active disk row: `hartConffStatesQ :471` →
  `fconfRowsPin :786` (the `(i,n) ∉ GF.gfDev → ∀ d, hblkQ … d d …` conjunct, with `gfexecConf`'s `isDevBlock em k ↔ (i,k)
  ∈ gfDev` `:533`) → `supplyOfFconf :689`'s third hypothesis → `fconfSupply :827`, `fconfSupply'` (`Lin2.lean:997`),
  `fconfTraceRealize :1014`, `WeakRvwmoFabInd.fconfRealize :413-447`, `WeakRvwmoCapstone.xv6RvwmoSafeModuloF :230`
  (internal, D39 — must still BUILD).  `admRunDevfree`/`admRunRefab`/`hemitDevfreeConst`/`hemitDevfreeRefab` ARE
  rescued by `devQuiet p` (their hypothesis "no `LDev` in the run/row" keeps the disk at `.PDisk none` throughout) ✓ —
  R17.3 is right for the Supply family and wrong for the Fab family.  *Exact change (§C W-DISK MECHANISM (ii) and the
  file list; the §C W13 (I) brief):*  **(a)** `gfexecConf` (`Fab.lean:524-536`) gains the INTERIM clause **"a `.PDisk`
  row's emission is `LDev`-free: `boot i = .PDisk _ → ∀ kd ba bs, LDev kd ba bs ∉ emLabels em`"** (hart rows keep
  their MMIO blocks — `devQuiet (.PHart ..)` is `True` and `pstepEv` keeps the constructor); **(b)** `hemitfStatesQ`
  and `hartConffStatesQ` take **`devQuiet p ∧ (∀ dp, p = .PDisk dp → ∀ kd ba bs, LDev kd ba bs ∉ es.map Prod.fst)`**
  (the induction then carries it: a `PHart` stays quiet under every step, a `PDisk` under `LDev`-free steps by
  `devQuietStep`), `fconfRowsPin` extracts it from (a); nothing else in the chain changes shape; **(c)** NAME the
  consequence in §C W13 (I) and §B(11): "until (I) replaces `isDevBlock` by the endpoint criterion `(i,k) ∈ gfDev ↔ dvi k
  ≠ dvo k` and deletes clause (a), the INTERNAL fabric bundle `gfexecConf` is vacuous for device-active disk rows — the
  same interim pattern as `ioResidueGwfInterim :184`; the published bundle `xv6ConfS` is (I)'s" — and (I)'s brief lists
  the clause's deletion among its `Fab :318-503` edits; **(d)** correct `:1371-1373` ("no proof change beyond the
  hypothesis; S–M … W-DISK OWNS this minimal restatement") to "the Supply family gains `devQuiet p` (S); the Fab family
  gains the interim disk clause (a)/(b) (S–M); W-DISK owns both" and the header's [R17.3] summary likewise.  The
  alternative — W-DISK absorbs (I)'s endpoint criterion (the M) — is recorded, not recommended (two XL-adjacent items on
  `Fab :318-503`).  S–M.
- **[R18.3] `pre` must begin with the in-flight pre-check, and `R-dev` is equality only UP TO the pending `pre` on the
  OUT capture segment; the abort's F9 row is wrong.**  *What is wrong, against `serve`.*  (i) OUT path order:
  `modify (setPhase .fetched) :526` → `guard taken :529` → `capture :530` = `dmaRead r.buf :516` → `modify (cacheReq ∘
  setPhase .served) :517-518` → `dmaWriteIf status :536`.  pf's order: capture `DRead` (a plain `LLoad`, `pdiskProg
  :491-495`, `d' = d`) → status `DWriteDev` with `pre` = the three moves.  MachCSL program order forces `:526` and `:529`
  BEFORE the `dmaRead`, and the `dmaRead` must be matched to pf's `DRead` (same step, else the `latest`/top values can
  differ), so the matched run performs `modify .fetched` + `guard taken` AT pf's `DRead`: for the two pf steps between,
  MachCSL's fabric is `pre₁ (dvirtio_pf)` (phase `.fetched`, `taken = some h`) while pf's is unmoved — "`R-dev` stays
  EQUALITY on `inflight`/`taken`/…/phases" (`:1330`, `:1219-1220`) is FALSE on that segment.  Rev 20's "coarser phases,
  equal up to phase" was closer; the correct relation is below.  (ii) `pre` as specified re-applies `setPhase`/`taken`
  to whatever state it finds.  After a mid-burst reset (`Virtio.write :295`: STATUS := 0 → `reset :260-262`, `inflight :=
  []`, `taken := none`), pf's status `DWriteDev` would run `setPhase … (.fetched r)` on the EMPTY map (`alistSet`,
  `:248-249`) — RESURRECTING the request — take `taken`, write the status byte (own guard `reqOf = some r` now true),
  pass the folded gate (`taken = some h`), skip the used writes (`cfg0 ≠ c`) and END the burst with `(h, .pushed)` in
  flight and `taken = some h` forever; MachCSL's twin, left at `:517` by the matched run, is a zombie at the reset
  state.  `R-dev` fails, and after any later re-init pf's `pushOk`/`taken` abort every request MachCSL completes — RAM
  diverges.  The case is unreachable under xv6 (STATUS := 0 only in `virtio_disk_init`), but F9 simulates EVERY shaped
  pf run and the plan claims no driver fact is needed.  (MachCSL's own `:517-518` resurrects too; the matched run simply
  never schedules that continuation.)  *Exact change (§C W-DISK FOLDING RULE and §C W4 F9):*  **(a)** `pre`'s FIRST
  folded guard is the in-flight check **`(phase s h).isSome`** (the request MachCSL's task was serving is still in
  flight); failure → ABORT with `d' = d` (nothing re-applied); only then the `setPhase`s/`taken`/`cacheReq` moves and the
  `DevM.guard`s — so pf applies MachCSL's moves exactly when MachCSL's task would still be live, and after a reset pf
  aborts ↔ MachCSL's zombie is never scheduled (`inflight = []`, `taken = none` on both sides).  **(b)** `R-dev` (F9):
  `dvirtio_M = dvirtio_pf`, EXCEPT while pf sits between the capture `DRead` and the status `DWriteDev` of an OUT
  request, where `dvirtio_M = (pre₁ (dvirtio_pf)).1` with `pre₁` = `setPhase .fetched` + the `taken` guard (the moves
  MachCSL performed at the `DRead`); `poolRel` records which (the MachCSL task's position does).  The remaining
  `DWriteDev`s have no `DRead` between the previous fabric step and them (IN: `fill`'s `get :489` is immediately before
  its `dmaWriteIf :491`; the used-element/idx writes follow the gate and `get :541-543` directly), so equality holds
  there.  Non-reset MMIO writes (`write :291-326`: `cfg` fields, `isr` ACK) commute with `pre₁` (disjoint fields) —
  the worker verifies this once.  **(c)** F9 rows: capture `DRead` 1 → 3 (`modify .fetched`, `guard taken`,
  `dmaRead`); the ABORT arm 1 → 0 (the twin is blocked or left unscheduled; `devStep`'s blocked self-loop is never
  needed), replacing "1 → 1 (`devStep`'s blocked arm)" at `:1230-1231` and "matched by the folded `modify` steps +
  `devStep`'s blocked arm" at `:1328`; a `DWriteDev` 1 → k counts the `pre` moves NOT already performed at a `DRead`.
  **(d)** the Mark (`:1349-1353`): with (a) the ONLY reachable abort is a mid-burst device reset (STATUS := 0), where
  pf aborts and MachCSL's task is a zombie — SAFETY-EQUAL, LIVENESS-weaker there only (as now), no driver fact.  S.
- **[R18.4] The (M9) START snapshot of `cfg`/`usedIdx`/`cacheView` is not `serve`'s; under a mid-burst config write
  MachCSL WRITES where pf SKIPS — the Mark's "both skip, SAFETY-EQUAL" is false and F9 would need a driver fact.**
  *Evidence.*  `serve` re-reads the device state THREE times: `let v ← get :522` (so `fetch v.cfg h :523` uses the
  cfg at the serve task's start, not the root loop's `:560`), `fill`'s `let v ← get :489` (`cacheView v` at the fill),
  and `let v ← get :541; ui := v.usedIdx; c := v.cfg :542-543` AFTER the `pushed` gate — the used element goes to
  `usedElemAddr c ui :546` and the idx to `usedIdxAddr c :553` with THAT `c`.  A hart's config write (QUEUE_SEL/
  QUEUE_NUM/the address registers, `write :296-326`) between pf's START and MachCSL's `:541` makes MachCSL write the
  used element/idx into the NEW ring and `complete`, while pf's `g` (`s.cfg = c` with START's `c`, `:1285`) answers
  `none` and SKIPS: MachCSL appends two log entries pf does not — `R-log` fails, F9 cannot close.  The plan's
  "`virtio_disk_init` writes the queue config once, before DRIVER_OK" (`:1350-1351`) is an xv6 fact F9 has no access
  to without a new SC-tree export (the W-DISK-Q1 (a)-style cost the plan rejected).  The simulation's SCHEDULING freedom
  closes it instead: MachCSL device steps that pf performs as ONE step are executed as one block, so no hart step can
  fall between them.  *Exact change (§C W-DISK (M8)/(M9), MECHANISM (i), the Snapshot paragraph, the Mark; §C W4 F9):*
  **(a)** `DM.DWriteDev` takes **state-dependent address and data**: `(pre : VirtioState → VirtioState × Bool) (g :
  VirtioState → Option VirtioState) (pa : VirtioState → PAddr) (bs : VirtioState → List (BitVec 8)) (k : DM Dres)`,
  evaluated at `s := (pre (dvirtio d)).1` in the arm (`l = LStore false (paZ (pa s)) (bs s) [] []`); `DmWf` asks `∀ s,
  (bs s).length = n ∧ n ≠ 0` (the three writes have fixed widths 1/8/2; the fill `r.len`); the used element's `pa s =
  usedElemAddr s.cfg s.usedIdx`, `bs s = usedLen r ++ head`, the idx's `pa s = usedIdxAddr s.cfg`, `bs s = s.usedIdx +
  1`, `g s = if reqOf s h = some r then some (complete s h) else none` — `serve`'s own post-gate `get` folded like the
  `modify`s (`:541-543`), no snapshot; the fill's `bs s = diskRead (cacheView s) (reqOff r) n` — `fill`'s `get :489`
  folded, so (M8)'s "START snapshot equal to the fill-time view because drains preserve `cacheView`" is no longer
  needed (keep the sentence only as the reason `R-dev`'s `cacheView` clause is stable).  **(b)** the POP `LDev .dev`
  step (already fabric-reading, [OWN.32]) RE-SNAPSHOTS `cfg` for the descriptor addresses — `serve`'s `get :522`; the
  matched MachCSL run executes `get; guard; fork; (serve) get` at the POP (1 → 4), so the two `get`s see one state.
  START keeps `live`, avail/ring addresses and `seen` from the root loop's `get :560` (1 → 2 with `choose`).  **(c)**
  the Snapshot paragraph (`:1348`) becomes "snapshots are taken exactly where `serve` does: START (`:560`), POP (`:522`),
  the fill's `pre` (`:489`), the used-element/idx `pre` (`:541-543`)"; the Mark (`:1349-1353`) becomes "after
  [R18.3]/[R18.4] the pf program and `serve` take the same decisions at the same fabric states up to the simulation's
  scheduling; the only divergence is the post-reset abort ([R18.3] (d)); no driver fact"; W-DISK-Q3's text (`:2044-2047`)
  gains "with state-dependent `pa`/`bs`" (within the RULED (a), no re-ruling: the read of `cfg`/`cacheView` is inside
  the fabric-moving write, not a re-read node).  S–M text; W-DISK's size class unchanged.

## SUGGESTIONS

- **[R18.s1] Tie `p'` to `c'` in the pinned statement.**  Hypothesis 1 (`pstepEv (.PHart …) c.pcDev l p' d'`) and
  hypothesis 2 (`wpPfStep …`, whose own `pstep` existential chooses `c'.pcAgs[i].paSt`) are related only through `l`;
  W4 recovers `c'.pcAgs[hartAgent cpu].paSt = p'` by `pstepEv`'s determinism per label on `PHart` nodes (true, but a
  lemma).  Cheaper: add the hypothesis `c.pcAgs[hartAgent cpu]? = some ⟨.PHart cpu (.impure (.ok o) k) rs fn ib, ws,
  prom⟩` and the conclusion `(c'.pcAgs[hartAgent cpu]?).map Wpagent.paSt = some p'`; the "hypotheses may be WEAKENED"
  rule then lets W2 CLOSE drop it if unneeded.  Not blocking.
- **[R18.s2] "TYPE-CHECKS" (`:1082`)** was established by a reviser reading binders, not by `lake`; write "checked by
  reading against …; elaboration is W2 CLOSE's day-one step (`:1121-1122`)".
- **[R18.s3] F9 bookkeeping after [R18.3]/[R18.4]**: START 1 → 2 (`choose`, `get`); avail/ring `DRead` 1 → 1; POP 1 →
  4 (`get`, `guard`, `fork`, serve's `get`) and the row "`fork` 1 → 0" goes; OUT capture `DRead` 1 → 3; each `DWriteDev`
  1 → k (its `pre` moves not already performed) + the `dmaWrite`; the drains 0 → k before the used-element `pre`; ABORT
  1 → 0; own-guard SKIP 1 → 1 (`dmaWrite`'s skip arm).  The `13+k` thread map is then exact.
- **[R18.s4] `pdiskProg`'s terminal node.**  With COMMIT retired the brief never says what follows the idx
  `DWriteDev` (`k`): say "`DRet DIdle` → `dp' = none` (the existing arm `:514`)" so the next START is well-defined, and
  that `DRet DDone`/`vdelta` go with COMMIT.
- **[R18.s5] Cite drift (minor)**: `Virtio.body` is `:558` (plan `:559`); capture's `modify` `:517-518`; `pushOk :419`
  (plan cites `completeOk :412-414` only — the gate also tests `pushOk` and `(phase v h).isSome`, `:539`); `reset
  :260-262`, `write`'s STATUS arm `:294-295` (new cites for [R18.3]).
- **[R18.s6] §C top / Status**: after this round — W-DMA0 ∥ W11 (iv)b ∥ W2 CLOSE ∥ W4 F1–F8 immediately (unchanged);
  W-DISK once [R18.1]–[R18.4] are written into its brief (all S text, one revision).

## Owner questions the plan is missing

None required.  [R18.1]–[R18.4] are pf-internal device-model engineering in the SOUND direction (pf ⊆ MachCSL): they
change neither the published statement nor the trusted surface of §A(6)/§B(11) (the pf disk row's (viii) sequential
service, MachCSL's choices (i)–(vii) and [OWN.30]–[OWN.33] stand); [R18.2]'s interim `gfexecConf` clause restricts an
INTERNAL bundle (D39) until (I), exactly as `ioResidueGwfInterim` already does for `gwf`.  For the record, under the
owner rule: RVWMO, riscv.cat and the Sail model in this tree have no device-internal events (Sail has no device/DMA
model; `MachCSL/Dev/*.lean` is the only device text), Zifencei and the PMAs are silent, and virtio 1.x says nothing
about when a device re-reads its own configuration — so where pf samples `cfg` (START vs `serve`'s `get` points) is a
choice EQUAL to MachCSL after [R18.4] and beyond the spec's silence either way; no option is more or less faithful to
the ISA, and the plan may decide it without a ruling.
