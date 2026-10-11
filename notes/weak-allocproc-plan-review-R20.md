VERDICT: NOT SATISFIED

# Review R20 of `notes/weak-allocproc-plan.md` rev 23 (adversarial, evidence-based; 2026-10-11)

Scope (per the R20 brief): rev 23 = rev 22 + R19's three required changes (all W-DISK binding text) + W2 CLOSE DONE
(the LANDED `pfStepTso` replaces the pinned text) + [OWN.34] + the OPEN owner question Q-FIARM; W11 (iv)b landed AFTER
rev 23 and must be recorded.  Audited against: `MachCSL/Dev/Virtio.lean` (`VirtioState :209-224`, `alistSet :233`,
`setPhase :248`, `reset :260-262`, `write :291-325`, `cacheView :359-362`, `reqSectorLen :371`, `reqCached :374`,
`completeOk :412-416`, `pushOk :419`, `complete :423-426`, `drain :429-432`, `fetch :466-478`, `fill :488-492`,
`cacheReq :496-500`, `capture :515-518`, `serve :521-554`, `body :558-587`), `MachCSL/Dev/DevLang.lean` (`guard :125`,
`dmaWriteIf :157`, `dmaWriteStep :163`), `MachCSL/Dev/Fabric.lean` (`devObsOk :90-95`: virtio = `os = []`),
`MachCSL/Lang.lean` (`storeDma :171-173`, `devOpStep :531-554`, skip arm `:544`, `devBlocked :561-569`, `devStep
:575-586`), `Weak/WeakEvInst.lean` (`pdiskProg :485-514`, `pdevEv :544-547`), `Weak/WeakEvLang.lean` (`DmWildChain
:913-917`, `ediskStep :926-961`, `ediskStepWf :1324-1345`, `eprimStepDiskReducible :1349-1372`), `Weak/VirtioProg.lean`
(`virtioProg :606-623`, `dmWfDreadData :913-917`, `dmWfDwriteData :919-923`, `dmWfDtail :935-943`, `virtioProgWf
:953`), `Weak/PfStepTso.lean` (`pinnedStmt :55`, `proposedStmt :102`, `hsrcOfRhist :191`, **`pfStepTso :301-330`**,
`pfStepTsoProposed :436`, `pfStepTsoStutter :444`, `pfStepTsoSame :499`, `rmemSameMem :514`, `viewRelSameRead :522`,
`pfRunSTAuthors :527`), `../weak-orch/parked/PROGRESS-W2CLOSE.md`, **`Weak/RvwmoXv6ScaT.lean` (792 lines; `Weak.lean:
632`)**, `model/Lean_RV64D/LeanRV64D/Step.lean:331-404`, `MachCSL/UCycleDefs.lean:1-25`, `MachCSL/WpDevDisk.lean:
140-160, 531-554`, `MachCSL/WpDevDma.lean:46, 136-165`, `MachCSL/WpDevDmaStep.lean:125-146`, `Xv6/DiskInv.lean:2164,
2750, 2828, 2855`.  Advisory only: no proofs, no builds, no git/jj, no subagents.  `file:line` cites `../xv6iris-weak`.
Items (a)/(b) of the standing brief were settled in R1–R15 and are not re-litigated.

**Sign-off.**  NO — two S defects in W-DISK's BINDING text and one stale record.  (i) **`R-dev` on the OUT capture
segment is stated unconditionally as `dvirtio_M = (pre₁ dvirtio_pf).1` with `pre₁ = setPhase .fetched (+ latch)`**
(`:1301-1306`, `:1478-1486`): a hart's STATUS := 0 on that segment (`write :294-295` → `reset :260-262`) makes
MachCSL's `dvirtio` the RESET state (`inflight = []`, `taken = none`) while `(pre₁ (reset pf)).1` has `(h, .fetched r)`
in flight (and `taken = some h` in the free case) — the invariant is FALSE from the reset until pf's status `DWriteDev`
aborts; the "non-reset MMIO writes commute" sentence names the gap without closing it ([R20.1]).  (ii) **`DmWf`'s
`n ≠ 0` (`:1458`) contradicts (M5′)'s "`n = 0` arm is pf-`LSilent`, 1 → 1" (`:1438-1441`) at the fill/capture**, whose
width is `r.len.toNat` = the descriptor's `len` read off RAM (`fetch :477`, no driver fact): `virtioProgWf` would be
unprovable for a zero-length chain, or the `n = 0` arm dead — today's program ELIDES the node (`dmWfDreadData :913-917`,
`dmWfDwriteData :919-923`), and the plan must say which ([R20.2]).  (iii) **W11 (iv)b is LANDED** (`Weak/
RvwmoXv6ScaT.lean`, `linCandScaT :757`) but the plan says IN FLIGHT / LAUNCHABLE and lists `linCandScaT` AND `pfStepTso`
among names "NOT in any merged file — workers must not grep for them" (`:349-352`) ([R20.3]).  The running workers
(W-DMA0 (A), W4 F1–F8) are unaffected; W-DISK is launchable once [R20.1]–[R20.2] are written (S text, one revision).

## What was verified (holds as cited; not to re-litigate)

**[R19.1] applied correctly.**  `drainAll v = { v with disk := cacheView v, cache := [] }` IS the result of MachCSL
draining every cached sector: for `a` in sector `s` with entry `bs` (`|bs| = reqSectorLen ≤ 512`, `cacheReq :498`),
`drain :432`'s `diskWrite v.disk (512 s) bs a = bs[a - 512 s]?` or `v.disk a` = `cacheView :359-362` at `a`; a sector's
`diskWrite` never reaches another sector (`|bs| ≤ 512`); keys unique (`alistSet :233-234`) ✓.  The used-element `pre`
= pre-check → `setPhase .status :537` → `drainAll` → gate `:539-541` with `completeOk :412-416` VERBATIM (`:1510-1516`)
✓; after `drainAll`, `!reqCached` (`:374-375`) and `cache.isEmpty` hold ✓; `taken = some h` holds from the status
write's `pre` ✓.  The matched run's drains are root-thread steps (`body :581-586`: `choose`, `get`, `choose`, `modify`,
`.pure` → restart `devStep :580` — 5 per sector ✓; `chooseLt` is `choose` + a pure bind, `DevLang.lean:134-136`) and
may run as one block before the task's `guard :539` (the schedule is existential) ✓.  `R-dev` FULL equality (`:1298`,
`:1388`, `:1478`), the `cache = []` invariant (`:1310`, `:1389`), the Mark (`:1530-1534`), §B(11) (vii)/(ix)
(`:900-918`), the acceptance (`:1631-1633`) ✓.  **[R19.2]**: `DWriteDev … (k : VirtioState → DM Dres)` (`:1454-1458`),
the used-element continuation binds `ui`/`c` (`:1412`), the idx node `serve :552-554` VERBATIM with the conjuncts
(`:1414-1416`; a reset between the two used writes → own-guard SKIP at `:553`, `Lang.lean:544`, then `DRet DIdle` ✓),
`DM.DPop` (`:1423-1427`; refusal `:568` 1 → 2, pop `:567,:576,:579,:522` 1 → 4 ✓) ✓.  **[R19.3]**: `pre₁` conditional
on the latch (`:1302-1306`, `:1480-1486`) ✓ — but see [R20.1].  **[R19.s1]–[R19.s5]** adopted (`:1317-1330`,
`:586` cite, (ix), `wce :1516-1518`, header `:23-26`) ✓.  **`devObsOk .virtio _ _ os = (os = [])`** (`Fabric.lean:95`),
so `complete`'s `isr` move inside `dmaWriteStep` never blocks (`Lang.lean:542`, `devBlocked :567`) ✓ — the fused idx
write is MachCSL-legal.  **W2 CLOSE record**: the plan's signature (`:1149-1177`) is `pfStepTso :301-330` VERBATIM
(hypothesis order, `rest` last) ✓; companions' lines ✓ (`:1188-1197`); the four repairs match `PROGRESS-W2CLOSE.md`
§"Why stopped" ✓; `pinnedStmt :55` kept as a documented non-theorem ✓; [R18.s1] "NOT needed" matches PROGRESS §[R18.s1]
✓.  **Q-FIARM's Spec line**: `run_hart_active` (`Step.lean:331`) is `dispatchInterrupt` (`:332`) → `fetch ()` (`:335`)
→ `instr_announce h` (`:340`, RVC) / `instr_announce w` (`:377`, base) → decode → `execute` (`:368-371` / `:403-405`),
and `execute` contains no instruction fetch (the `ExecuteAs` re-dispatch `:369,:404` re-enters `execute` only) ✓;
`UCycleDefs.lean:17-20` re-states `run_hart_active 0 = ucDispatch >>= … fetch () >>= ucAfterFetch` ✓; the question
meets the owner rule (RVWMO/riscv.cat silent on in-cycle order; Zifencei WHAT not WHEN; Sail file:line; PMAs silent;
every option FAITHFUL) and the 2026-10-10 format (plain language, `itv`/`fiArm`/shadow/marker defined, the
`sw; fence.i; jump` example, per-option what-the-theorem-says/omits/cost/unblocks/risk) ✓.  **[OWN.34] record**
(`:1676-1683`, `:2239-2247`): `LeaseD.dmaWrite` `WpDevDisk.lean:146-153` ✓, `storeDma` rewrites `:531, :544, :554` ✓,
`dmaWriteLease` `WpDevDma.lean:46` ✓ (`pushed Hs t diskAgent w`, `Kb < t`), `Lease.dmaWrite :139-142` ✓,
`lease_dmaWriteIf :158` ✓; the four `Xv6/DiskInv.lean` sites exist: `LeaseL.dmaWriteIf` `:2164, :2750, :2828` and
`LeaseL.dmaWrite` `:2855` (the idx write) ✓ — see [R20.s1] for the layer they come from.  **Cites**: `pdiskProg
:485-514` (START `:488`, DWrite `:497-499`, COMMIT `:505-507`, `DRet DIdle :514`), `pdevEv :544`, `ediskStep :926-961`,
`ediskStepWf :1324`, `eprimStepDiskReducible :1349` (has the `DRet DWild` arm `:1361-1363`) ✓; minor drift:
`pfStepTso`'s (c)/(d) hypotheses are `PfStepTso.lean:322-325` (plan `:2204` says `:325-328`), `virtioProgWf :953`,
`dmWfDcomplete :945`.

## REQUIRED changes

- **[R20.1] `R-dev` on the OUT capture segment must absorb a hart reset: make `pre₁` the status write's `pre`
  TRUNCATED before capture's `modify` (pre-check included, identity on failure), not `setPhase .fetched (+ latch)`.**
  *What is wrong (evidence).*  §C W-DISK `:1478-1486` and §C W4 F9 `:1301-1306` state, for pf between the capture
  `DRead` and the status `DWriteDev`, `dvirtio_M = (pre₁ dvirtio_pf).1` with `pre₁ = setPhase .fetched` AND (iff the
  latch was free) `taken := some h`, and add "non-reset MMIO writes (`write :296-323`) commute with `pre₁` (disjoint
  fields)".  The RESET does not commute and is reachable on the segment (STATUS := 0 is a plain MMIO store any shaped pf
  run may contain; F9's standard is "no driver fact", `:1397`): `write :294-295` → `reset :260-262` sets `inflight :=
  []`, `taken := none`, `cache := []` on BOTH sides (the matched run's MachCSL task has performed `:526` (+ `:529`,
  `:516`) and sits at `:517`, or is blocked at `:529`).  After it, `dvirtio_M` = the reset state, while `(pre₁
  dvirtio_pf).1 = setPhase (reset …) h (.fetched r)` (`alistSet :233-234` on the empty map — the resurrection
  [R18.3] names) with `taken = some h` in the free case: the clause is FALSE at every pf-step boundary from the reset
  until pf's status `DWriteDev`, whose pre-check `(phase s h).isSome` fails → ABORT `d' = d` = MachCSL's reset state
  (consistent at the END, as `:1498-1506` says, but the INVARIANT the worker writes into the header and F9 proves is the
  segment clause).  *Exact change (§C W-DISK `R-dev` `:1478-1486`; §C W4 F9 `:1301-1309`; the header's [R19.3] line
  `:19-20`):*  "`pre₁` := the status `DWriteDev`'s `pre` TRUNCATED before capture's `modify :517-518` — the in-flight
  pre-check (identity when `phase s h = none`: after a reset nothing is re-applied), then `setPhase .fetched :526`,
  then the `taken` guard `:529` (identity when `taken ≠ none`: MachCSL blocked, [R19.3]); `dvirtio_M = (pre₁
  dvirtio_pf).1` on the whole segment, every hart action included — non-reset MMIO writes commute with `pre₁`
  (disjoint fields), and a RESET is absorbed by the pre-check's identity arm (both sides reset; pf's status `DWriteDev`
  then aborts with `d' = d`, 1 → 0)".  The three cases the matched run distinguishes (free / held / reset) are then one
  formula; `poolRel` still records the MachCSL task's position.  S text; W4 F9's `R-dev` unchanged in size.
- **[R20.2] Zero-length data phase: `DmWf`'s `n ≠ 0` and (M5′)'s "`n = 0` arm" contradict each other at the
  fill/capture, whose width is RAM content.  Rule: ELIDE the data node when `r.len.toNat = 0` (today's shape); the
  `n = 0` arm is dropped.**  *What is wrong (evidence).*  MECHANISM (i) `:1458`: "`DmWf` asks `(∀ s, (bs s).length = n
  ∧ n ≠ 0) ∧ ∀ s, DmWf (k s)` — fixed widths 1/8/2, the fill `r.len`"; (M5)/(M5′) `:1436-1441`: "(M5′)'s `n = 0` arm is
  pf-`LSilent`, MachCSL-no-op, 1 → 1", arm `¬ ramBytes ∨ g … = none ∨ n = 0 → LSilent`.  The fill's `n = r.len.toNat`
  (`fill :490`) and the capture's `dmaRead r.buf r.len.toNat` (`:516`) take `len` from descriptor `d1` read off RAM
  (`fetch :471, :477`); `fetch` never tests it, so a shaped pf run may carry `r.len = 0` (a RAM fact F9 cannot see,
  `:1397`).  With `n ≠ 0` in `DmWf`, `virtioProgWf` (the twin of `:953`, consumed by `ediskStepWf :1324`) is unprovable
  for that chain — unless the program never emits the node, in which case the `n = 0` arm is dead text; `DmWf.read`
  likewise demands `0 < n` (`dmWfDreadWord :905-907`), so a capture `DRead pa 0` is ruled out either way.  Today's
  program already ELIDES: `dreadData pa 0 k = k []` and `dwriteData pa [] k = k` (`dmWfDreadData :913-917`,
  `dmWfDwriteData :919-923`).  *Exact change (§C W-DISK (M5)/(M5′) `:1436-1441`, MECHANISM (i) `:1458-1462`, §C W4 F9
  bookkeeping `:1323-1324`, §C W-DMA0 "W-DISK's (M5′) `n = 0` arm" `:1687-1688`):*  "the IN fill `DWriteDev` and the OUT
  capture `DRead` are emitted only when `r.len.toNat ≠ 0` (the continuation branches on the decoded `r`, as
  `dreadData`/`dwriteData` do today); `DmWf` keeps `n ≠ 0` (every emitted width is 1/8/2 or a non-zero `r.len`); for
  `r.len = 0` MachCSL's `dmaRead r.buf 0` (`:516`: `dmaView` vacuous) and `dmaWriteIf r.buf 0` (`:491`: `ramBytes pa 0`
  vacuous, `storeDma pa 0` a no-op AFTER W-DMA0 — the reason F9 waits for it) are matched 0 → 1 inside the next
  `DWriteDev`'s block (the OUT status write then performs `:526`, `:529`, `:516`, `:517`, `:536` — 1 → 5); `cacheReq`
  with `reqSpan r = 0` (`:368, :497`) adds no entry; (M5′)'s arm is `¬ ramBytes (pa s) |bs s| ∨ g s = none → LSilent`
  (the `n = 0` disjunct DROPPED)".  Mark: EQUAL to MachCSL (a zero-length transfer is a no-op on both sides); virtio
  1.x's text on zero-length buffers is not checked in-tree (silent as far as the reviewer knows); no owner ruling.  S
  text.
- **[R20.3] Record W11 (iv)b LANDED and fix the two stale "NOT in any merged file" names.**  *Evidence.*
  `Weak/RvwmoXv6ScaT.lean` (792 lines, imported `Weak.lean:632`): **`linCandScaT :757`** — `gwf G → gppoCat6Gmo G →
  gloadValue G → grule14 G → candScaT cohSrc (linCand G)`; corollaries **`linCandScaTCatT :780`** (from
  `rvwmoCatConsistentT GT` + `grule14 GT.gtG`, via `catTForgetAxioms`) and **`linCandScaTMinus :787`** (from
  `rvwmoMinusConsistent G` + `grule14 G`); pieces `RvwmoXv6ScaT.linScaBytes :110` ((iv)a's `linScaOk` re-proved WITHOUT
  `gpoloc ⊆ gmo` — a forwarded source is the hart's OWN message), `shInv :562` (the (T)/(R)/(C) invariant of the
  header `:15-26`), `loadFloor :483`; header `:35-37`: `gatomicity`/rule 12 unused, `LIo` handled without `gwf`'s
  interim `False` arm (W13 (I)/(M)'s flip does not touch the file).  The plan still says IN FLIGHT / LAUNCHABLE
  (`:1035-1036`, `:1042-1043`, `:2104-2111`, `:2124`, `:2752`) and lists `linCandScaT` (`:351-352`) AND `pfStepTso`
  (`:350-351`: "the two halves exist, their composition does not") among names "NOT in any merged file — workers must
  not grep for them" — the second is stale since W2 CLOSE DONE in the same revision.  *Exact change:*  §A "Names":
  move `pfStepTso` (+ companions, `PfStepTso.lean:301,436,444,499,514,522,527,191`) and `linCandScaT`/`linCandScaTCatT`/
  `linCandScaTMinus` to "LANDED"; keep `linCandDiskLat` ((iv)c) in the NOT list; §C top, §C W11 (iv), Status, D26:
  "(iv)b DONE (`Weak/RvwmoXv6ScaT.lean`, 792)"; §B(10) `:762-770` and §D G1-Q `:2490`: the landed premise set is
  `gppoCat6Gmo` + `grule14` on the linearized graph (rules 2, 4, 5 used; no `ptraceRel ⊇ gmo|W` statement needed —
  `linTvnScaLe :194` of (iv)a carries it), so W11 (v)/W13 (L) consume `linCandScaTCatT` on `GT.gtG`; IN FLIGHT list
  = W-DMA0, W4 F1–F8.  Bookkeeping only; no statement changes.

## SUGGESTIONS

- **[R20.s1] W-DMA0's consumer list misses the lease LAYER the `Xv6/` sites apply** (no brief change — W-DMA0 is
  running; a note for its merge review): the four `Xv6/DiskInv.lean` applications are `DevM.LeaseL.dmaWriteIf`
  (`:2164, :2750, :2828`) and `DevM.LeaseL.dmaWrite` (`:2855`) from **`MachCSL/WpDevDmaStep.lean:127-146`** (and the
  `V` twin `WpDevDmaStepV.lean:121-135`), each with an `hlease : … ⊢ dmaWriteLease pa n w …` obligation; (A)'s `n ≠ 0`
  premise lands on THOSE constructors (and on `LeaseD.dmaWrite`/`Lease.dmaWrite`) or `dmaWriteLease` itself gains the
  `n = 0` case.  Also `MachCSL/WpDevDisk.lean:868, 886, 904, 1153, 1945, 1952` use `dmaWriteLease` directly.
- **[R20.s2] Say where the aligned program's `DFence` sits**: ONE `DFence` immediately before the used-idx `DWriteDev`
  (today's `dtail` shape, `dmWfDtail :935-943`: … write, write, `.fence`, write), `fencePost dws true×4` on the disk's
  `Wstate`, 0 MachCSL steps (E-M3, `:1129`) — §A(†)'s "(R1)'s disk use … ordered by the device-side `DFence` (rule 4)"
  (`:420-421`) depends on it and (M4)'s text (`:1372-1376`) does not name it.
- **[R20.s3] (ix) needs no §A(6) entry — say why**: a drain emits no label (`drain :429-432` is a `modify`; pf's
  `drainAll` is inside the used-element `pre`), so WHEN pf drains changes no graph event and restricts no coverage —
  unlike (viii), whose sequential service excludes graphs with interleaved requests.  One clause in §B(11) (ix).
- **[R20.s4] Q-FIARM option (b): give the premise its FORM in the published statement.**  The realized pf run is
  EXISTENTIAL in T-alloc-RVWMO's conclusion (§A (a)), so "a premise of `machRunOfPfRun`" must enter the published
  theorem as a CLOSED proposition about the Sail hart program (`sailCycleOrder : ∀ cpu run, pfRunST … run → …`, over
  every `try_step` residual), added to the hypothesis list of §A's statement and to §B(11) — the shape `bootImageSealed`
  has, not a per-run side condition; (a′)/(a) then PROVE that closed proposition.  Worth one sentence in the question
  so the owner sees exactly what text the theorem gains.
- **[R20.s5] Cite drift**: `pfStepTso`'s (c)/(d) `PfStepTso.lean:322-325`; `virtioProgWf :953`; `dmWfDcomplete :945`;
  `eprimStepDiskReducible :1349-1372`; `ediskStep :926-961`.

## Owner questions the plan is missing

None required.  [R20.1]–[R20.2] are pf-internal device-model engineering in the SOUND direction (pf ⊆ MachCSL): under
the owner rule, RVWMO, riscv.cat and the Sail model in this tree have no device-internal events (Sail has no device/DMA
model; `MachCSL/Dev/*.lean` is the only device text), Zifencei and the PMAs are silent; virtio 1.x is silent on a
device's reset-time bookkeeping and (unverified in-tree) on zero-length buffers; eliding a zero-length transfer is
EQUAL to MachCSL's `dmaRead pa 0`/`storeDma pa 0` after W-DMA0 (both no-ops), neither more nor less faithful to the ISA.
Q-FIARM stays the one OPEN question; [R20.s4] sharpens it without changing its options or recommendation.
