VERDICT: NOT SATISFIED

# Review R19 of `notes/weak-allocproc-plan.md` rev 22 (adversarial, evidence-based; 2026-10-11)

Scope (per the R19 brief): rev 22 = rev 21 + R18's four required changes, all inside W-DISK's binding text.  Audited
against the code: `MachCSL/Dev/Virtio.lean` (`VirtioState :209-224`, `alistSet :233`, `phase`/`setPhase :247-249`,
`reset :260-262`, `write :291-325`, `cacheView :359-362`, `reqCached :374-375`, `completeOk :412-416`, `pushOk :419`,
`complete :423-426`, `drain :429-432`, `fill :488-492`, `cacheReq :496-500`, `capture :515-518`, `serve :521-554`,
`body :558-587`), `MachCSL/Dev/DevLang.lean` (`step :113`, `modify :119`, `guard :125`, `dmaWriteIf :157`,
`dmaWriteStep :163`), `MachCSL/Lang.lean` (`storeDma :172`, `devOpStep :531-554`, `devBlocked :561-569`, `devStep
:575-586`), `Weak/WeakEvInst.lean` (`pnodeStep :280-401`, `pstepNode :404-413`, `pstepPlic :464-472`, `pdiskProg
:485-514`, `pdiskUart :518-524`, `pstepEv :533-541`, `pdevEv :544-547`, `pdiskProgDevFree :1670`, `pdevEvOk :1694`),
`Weak/WeakEvLang.lean` (`ediskStep :927-961`), `Weak/VirtioProg.lean` (`DM :320-324`, `virtioProg :606-623`),
`Weak/WeakRvwmoSupply.lean:164-250, 310-317`, `Weak/WeakRvwmoFab.lean` (`lbIsdev :119`, `emDev :144`, `isDevBlock
:152`, `hemitf :239-260`, `hblkQ :318`, `hemitfStatesQ :347-355`, `hartConffStatesQ :471-485`, `gfexecConf :524-536`,
`gfexecConfOfQconf :649-662`, `supplyOfFconf :690`, `fconfRowsPin :786-806`, `fconfSupply :827`),
`Weak/WeakRvwmoLin2.lean:997-1016`, `Weak/WeakRvwmoFabInd.lean:413-447`, `Weak/WeakRvwmoCapstone.lean:228-240`,
`Weak/WeakPromiseFact.lean:613-614`, `Weak/WeakEvCapstone.lean:645-665, 1026-1027, 1183`.  Advisory only: no proofs, no
builds, no git/jj, no subagents.  `file:line` cites `../xv6iris-weak`.  Items (a)/(b) of the standing brief (the
`Xv6.Allocproc` statement and the TsoMem = sRVWMO claim) were settled in R1–R15 and are not re-litigated here; R16–R18's
W-DISK findings that this round re-verified are listed under "What was verified".

**Sign-off.**  NO — three defects in W-DISK's BINDING text, all pf-device-model engineering, none touching the published
statement or the four running workers (W-DMA0, W11 (iv)b, W2 CLOSE, W4 F1–F8 are launchable/continuable as written).
(i) **[R18.1] (A)'s `R-dev` clause `cacheView pf = cacheView M` is NOT an invariant of the simulation it is meant to
close**: under (A) pf's `disk` is the boot image forever (nothing in pf writes `disk`), MachCSL's `disk` advances at
every `drain`, and a hart's STATUS := 0 (`write :294-295` → `reset :260-262`, `cache := []` on BOTH sides, `disk`
kept) makes `cacheView` = `disk` on both sides — different as soon as one OUT has been drained; separately,
`cacheReq` on a request whose length is not a sector multiple (`reqSectorLen :371`, partial tail entry; `cacheView
:361` falls back to `v.disk a` past the entry's length) exposes pf's stale image where MachCSL exposes its drained
one.  Both are reachable in a shaped pf run; F9 "simulates EVERY shaped pf run with no driver fact" (rev 22's own
standard, `:1437-1440`), so F9 cannot close on (A) as written ([R19.1]).  (ii) **[R18.4]'s "the idx write's `s.usedIdx
= ui ∧ s.cfg = c` conjuncts are trivially true and disappear" (`:1341-1343`) is false**: `serve` binds `ui`/`c` at
`:542-544` BEFORE the used-element write and re-tests them at the used-INDEX write `:553`, which is a SEPARATE pf step;
a hart's config write between the two pf steps (any `cfg` field, `write :296-323` — even `qsel`/`devfsel`, which do
not move `usedIdxAddr`) makes MachCSL SKIP the idx write (`g = none`, `Lang.lean:544`; the request stays `.pushed`,
`pushOk` false forever) while rev 22's pf idx node WRITES and `complete`s — `R-log` fails ([R19.2]).  (iii) **[R18.3]
(b)'s `pre₁` is stated unconditionally** ("`setPhase .fetched` + the `taken` guard, performed by the matched run at
pf's `DRead`"): when `taken ≠ none` at that point MachCSL's `guard :529` BLOCKS, so the matched run cannot reach the
`dmaRead :516` and performs only `:526`; `R-dev` on the segment is then `setPhase .fetched` alone and pf's `DRead` is
matched 1 → 1, not 1 → 3 ([R19.3], S).  The pf program the worker would build from rev 22 is one F9 cannot simulate;
the fixes are S text, one revision.

## What was verified (holds as cited; not to re-litigate)

**[R18.1] (A) partially.**  `drain :429-432` PRESERVES `cacheView`: for `a` in the drained sector `s` with entry `bs`,
before = `bs[a % 512]?` or `v.disk a`, after = `diskWrite v.disk (512 s) bs a` = `bs[a - 512 s]?` or `v.disk a` — equal
(and unique keys: `alistSet :233-234` dedups, `alistDel :236` removes all) ✓; `drain` leaves `cacheView` unchanged, so
the matched run may insert drains anywhere without moving the fill's data ✓.  The `completeOk :412-416` conjuncts
`!reqCached` (OUT, `wce = false`) and `cache.isEmpty` (FLUSH) ARE drain-dependent ✓, so a verbatim fold without a pf
drain would dead-lock pf's writes ✓ — the DIAGNOSIS of R18.1 stands; its REMEDY (pf never drains, `completeOkPf`,
`cacheView` clause) does not ([R19.1]).  "`cacheReq` moves both `cacheView`s identically" (`:1326-1327`) is TRUE for
sector-multiple lengths and FALSE for a partial tail sector (above).  **[R18.2].**  `hemitfStatesQ :347-355`'s second
conjunct is as R18 described; `emDev :144-150`/`isDevBlock :152` are label-based ✓; the interim clause is satisfiable
by today's only witness: `gfexecConfOfQconf :649-662` builds every row from `gdexecQconfRows` (`Supply.lean:310-317`),
whose emissions are `emDevfree` ✓ — so the clause `boot i = .PDisk _ → LDev ∉ emLabels em` is discharged there for
free, and the chain `fconfRowsPin :786` → `supplyOfFconf :690` → `fconfSupply :827` → `fconfSupply' (Lin2 :997)` →
`fconfTraceRealize :1014` → `FabInd.fconfRealize :413-447` → `xv6RvwmoSafeModuloF :228-240` all take `gfexecConf`
as a HYPOTHESIS and need no proof change beyond (b)'s threading ✓.  (b)'s induction carries: from `.PDisk none` the
only `pdiskProg` arm is START (`LDev`, `:488`) and every `pdiskUart` arm is `LDev` (`:520`), so an `LDev`-free `.PDisk`
emission is EMPTY — "vacuous for device-active disk rows" (`:1480`) is exactly right ✓; `PHart` keeps its constructor
under `pstepEv :535` ✓.  **[R18.3] (a).**  `pre`'s in-flight pre-check: `setPhase` on an empty map RESURRECTS
(`alistSet :233-234` conses) ✓; after `reset` both `inflight = []` and `taken = none` ✓; a zombie MachCSL task is never
scheduled — `devStep :585-586` has no fairness, the blocked arm is a stutter ✓; MachCSL's own `:517-518` would
resurrect too (`setPhase (… ) h (.served r)` unconditionally) ✓.  **[R18.3] (b) order.**  OUT path is `:526` → `:529`
→ `:516` → `:517-518` → `:536` ✓; IN path `:526` → `fill`'s `get :489` → `dmaWriteIf :491` → `:534` → `:536` (no
`DRead` between `:526` and the fill) ✓; FLUSH/other `:526` → `:534` → `:536` ✓; non-reset MMIO writes touch `cfg`/`isr`
only (`write :296-323`), disjoint from `inflight`/`taken` ✓; MMIO reads are pure (`readN :337-340`) ✓.  **[R18.4]
(a)/(b).**  `fill`'s `get :489` immediately precedes its `dmaWriteIf :491` ✓ — folding it into the fill's `pre` is
exact; the used-ELEMENT write's `:546-547` conjuncts are tested in the same matched block as `get :542` and the gate
`:539-541` ✓ — for THAT write "trivially true" is right; `serve`'s `get :522` feeds `fetch v.cfg h` (`descAddr`,
`qnum` bounds, `:466-478`) ✓ so the POP must re-snapshot `cfg`; the root's `get :561` feeds `live`, `availIdxAddr`,
`availRingAddr`, `seen` ✓.  The matched-run block argument (MachCSL device steps that pf performs as one step run
consecutively, `:1434-1435`) is legitimate: the schedule is existential in the MachCSL run ✓.  **State-aware `pdevEv`.**
`pdevOk :613-614` constrains only `pdev = false` steps ✓; `pdevEv p l p' := lbIsdev l || p is .PDisk (some (DWriteDev ..))`
is a Bool of the right type ✓.  **Cites.**  `body :558`, `get :561`, `dma16 :563, :565`, `get :567`, `guard :576-578`,
`fork :579`, drains `:581-586`, `completeOk :412-416`, `pushOk :419`, `complete :423-426`, `reset :260-262`, `write
:294-295` ✓; `WeakEvInst.lean:485-488, :514, :518-526, :544-547, :1670, :1694` ✓; `Fab.lean:347-354, :471, :524-536,
:533, :786, :689/690, :827` ✓; `Supply.lean:164-171, :175, :202, :241` ✓.  Minor drift: `devStep`'s blocked arm is
`:586` (plan `:575-577`, which is the theorem head); `devBlocked :561-569`.

## REQUIRED changes

- **[R19.1] [R18.1] (A)'s `R-dev` image clause is false after a device reset and after a partial-sector write;
  replace "pf never drains" by a pf drain folded into the used-element write's `pre`, keep `completeOk` verbatim, and
  make `R-dev` FULL equality off the `pre₁` segment.**  *What is wrong (evidence).*  (1) Under (A) no pf node writes
  `disk`: `cacheReq :496-500` writes `cache`, `setPhase :248`/`complete :423-426`/the `taken` latch touch other fields,
  `write :291-325` never touches `disk`, `reset :262` keeps it — so pf `disk` = the boot image for the whole run,
  while MachCSL's `disk` advances at every `drain :432`.  A hart's STATUS := 0 (`write :294-295`) applies `reset` on
  BOTH sides: `cache := []`, so `cacheView = disk` on both (`cacheView :359-362`), and these differ as soon as any OUT
  was drained — which every xv6 OUT is, since `wce = false` (`vdi_wce_15`) makes `completeOk :414` require
  `!reqCached`.  A later IN then fills RAM with different bytes on the two sides (`fill :492`), `R-log` fails.  The
  plan's Mark "the ONLY reachable divergence is the post-reset ABORT … SAFETY-EQUAL" (`:1435-1440`) is therefore false:
  the post-reset DATA diverges.  (2) `cacheReq`'s entry for the last sector of a request whose `len` is not a multiple
  of 512 has `reqSectorLen r i < 512` bytes (`:371, :498`); `cacheView :361` answers `v.disk a` for `a % 512 ≥ |bs|` —
  pf's boot image vs MachCSL's drained image, after any earlier drained OUT to that sector.  So "moved identically by
  `cacheReq`" (`:1326-1327`) holds only for sector-multiple lengths — a RAM-content (driver) fact F9 cannot see.  Both
  cases are reachable in a shaped pf run; the plan's standard for F9 is "no driver fact" (`:1439-1440`), and (1) needs
  one even for xv6-shaped traffic (STATUS := 0 is a plain MMIO store any pf run may contain).  *Exact change (§C W-DISK
  (M8), MECHANISM "The folded gate", `R-dev` [R18.3 (b)], the Mark, §B(11) (vii), §C W4 F9 `:1250-1252`, the header's
  [R18.1] summary `:5-9`, W-DISK acceptance `:1532-1534`):*  **(a)** define `drainAll (v : VirtioState) : VirtioState :=
  { v with disk := cacheView v, cache := [] }` (= the result of MachCSL draining every cached sector in any order:
  unique keys by `alistSet :233-234`/`alistDel :236`, and `drain :432`'s `diskWrite` IS `cacheView` on that sector);
  the used-ELEMENT write's `pre` becomes **pre-check `(phase s h).isSome` → `setPhase .status` (`:537`) → `drainAll` →
  the gate `:539-541` with `completeOk` VERBATIM** (`!reqCached` and `cache.isEmpty` are true after `drainAll`;
  `completeOkPf` is WITHDRAWN); the matched MachCSL run inserts `cache.length` root-loop drain iterations (`body :581-586`,
  each `choose`(k=1), `get`, `choose` j, `modify`, restart) immediately before its `guard :539`, in the same block.
  **(b)** `R-dev` (F9) becomes **`dvirtio_M = dvirtio_pf` — ALL fields, `disk` and `cache` included** — EXCEPT on the
  OUT capture segment ([R19.3]); the `cacheView` clause and the "`diskOf` is MachCSL-only" note ([R16.s3], `:1327-1330`,
  §B(11) (vii) `:881-885`) are REPLACED by "pf's durable image advances at the gate, all cached sectors at once; MachCSL's
  one sector per drain step; EQUAL at every pf-step boundary of the matched run, so a future crash-row consumer sees one
  image".  **(c)** the invariant beside `R-dev`: **`cache = []` outside a capture → gate window** (pf: the only `cacheReq`
  is the status write's `pre`, the only drain the gate's; MachCSL: the matched run drains only there) — with it `cacheReq`
  is applied to EQUAL states on both sides at every capture, so partial-sector lengths need no fact; on a gate ABORT
  (`pushOk`/`taken` false) `d' = (pre s).1` includes `drainAll`, matching MachCSL's drained-then-blocked state; on a
  pre-check ABORT `d' = d` with `cache = []` by `reset` on both sides.  **(d)** the Mark: "the only reachable divergence
  is the post-reset LIVENESS gap (pf aborts, MachCSL's task is a zombie); the post-reset DATA is equal (`disk` equal by
  (b))".  **(e)** §B(11) (vii)'s wording: "pf drains at the gate (STRONGER than MachCSL's any-time drain only in WHEN;
  pf ⊆ MachCSL; device-internal, every spec silent)".  Recorded, not recommended: keep (A) and give F9 the two premises
  "no STATUS := 0 after an OUT" and "every OUT `len` is a sector multiple" — RAM-content/driver facts needing an SC-tree
  export (the cost the plan rejected for W-DISK-Q1 (a)).  S text; W-DISK's class unchanged; W4 F9's `R-dev` SIMPLER.
- **[R19.2] [R18.4] (a) drops the used-INDEX write's snapshot conjuncts; they are load-bearing because the two used
  writes are separate pf steps.  Give `DWriteDev` (and the POP node) a STATE-RECEIVING continuation and keep `serve`'s
  `ui`/`c` test at the idx write.**  *What is wrong (evidence).*  `serve :542-544` binds `ui := v.usedIdx`, `c := v.cfg`
  ONCE after the gate; the used-element write `:546-547` AND the used-idx write `:553` test `s.usedIdx = ui ∧ s.cfg = c`.
  Rev 22 (`:1338-1343`) makes both writes read `s.cfg`/`s.usedIdx` at their OWN step and drops the conjuncts.  For the
  used-element write that is exact (same matched block as `get :542`); for the idx write it is not: pf's used-element
  `DWriteDev` and idx `DWriteDev` are two pf steps, so a hart MMIO config write (`write :296-323` — `qsel`, `devfsel`,
  `dfsel`, `shmsel`, `qnum`, `ready`, the ring addresses; `s.cfg = c` compares the WHOLE `VirtioCfg`) may fall between
  them.  MachCSL then answers `g = none` at `:553` and SKIPS (`Lang.lean:544`; the request stays `.pushed`, `pushOk :419`
  false forever, `taken` never freed), while rev 22's pf idx node (`g s = if reqOf s h = some r then complete …`) writes
  `usedIdxAddr s.cfg` and `complete`s — one log entry pf appends and MachCSL does not; `R-log` fails, and no matched
  schedule exists (the config write is a hart step pf's run contains).  Unreachable under xv6 (no `cfg` write after
  `virtio_disk_init`) but F9's standard is no driver fact.  *Exact change (§C W-DISK (M9), MECHANISM (i) the node, the
  file list, §C W4 F9 bookkeeping):*  **(a)** `DM.DWriteDev (pre : VirtioState → VirtioState × Bool) (g : VirtioState →
  Option VirtioState) (pa : VirtioState → PAddr) (bs : VirtioState → List (BitVec 8)) (k : VirtioState → DM Dres)` —
  the continuation RECEIVES `s := (pre (dvirtio d)).1` (the state `serve`'s `get :542` binds; `dp' = some (k s)` on
  both the write and the own-guard SKIP arm) — `serve`'s `let v ← get` fused into the fabric-moving write, inside the
  RULED (a) of [OWN.32] (a read INSIDE a fabric step, not a re-read node); `DmWf` asks `(∀ s, (bs s).length = n ∧ n ≠ 0)
  ∧ ∀ s, DmWf (k s)`.  **(b)** the used-element node binds `ui := s.usedIdx`, `c := s.cfg` in `k`; the idx node is
  `DWriteDev (pre := fun s => (s, true)) (g := fun s => if reqOf s h = some r ∧ s.usedIdx = ui ∧ s.cfg = c then some
  (complete s h) else none) (pa := fun _ => usedIdxAddr c) (bs := fun _ => ui + 1) (k := fun _ => DRet DIdle)` — `:552-554`
  verbatim; it has no folded moves (nothing between `:547` and `:552`), so its `pre` is the identity and a lost request
  is an own-guard SKIP (1 → 1, MachCSL's skip arm) followed by `DRet DIdle` → `dp' = none` (1 → 1, the finished task's
  done-marking `devStep :581-583`), not an ABORT; the used-ELEMENT node keeps [R18.4]'s state-dependent `pa s =
  usedElemAddr s.cfg s.usedIdx` and the sentence "trivially true and disappear" is restricted to IT.  **(c)** the POP
  node is NAMED: `DM.DPop (h : BitVec 16) (k : VirtioState → DM Dres)`, `pdiskProg` arm `l = LDev .dev 0 []`, `(phase s
  h).isSome → dp' = none ∧ d' = d` (MachCSL's refusal `:568`, 1 → 2: `get :567`, restart) else `s' := { setPhase s h
  .popped with seen := s.seen + 1 }`, `d' = setDvirtio d s'`, `dp' = some (k s')` with `k` using `s'.cfg` for `fetch`
  (`serve`'s `get :522` sees exactly `s'`; 1 → 4 as `:1265-1266`).  Rev 22 lists "the POP" among `ediskStep`'s arms
  (`:1501`) without a constructor; the re-snapshot it requires (`:1343-1345`) is the same state-receiving continuation.
  S text; the `WeakEvDisk` per-node rules and `ediskStepWf` take the `∀ s` form.
- **[R19.3] [R18.3] (b)'s `pre₁` is conditional on the `taken` guard answering; state it and the segment's
  bookkeeping that way.**  *Evidence.*  `guard :529` is `DevM.guard`, which BLOCKS when `v.taken ≠ none` (`DevLang.lean:
  125`, `devBlocked :563`); the matched run cannot then perform `dmaRead :516` at pf's capture `DRead`, so it performs
  `modify :526` only (1 → 1), `R-dev` on the segment is `dvirtio_M = setPhase dvirtio_pf h (.fetched r)` (not `pre₁`
  incl. the latch), and pf's status `DWriteDev` fails the same guard in its `pre` (its `taken` equals MachCSL's) →
  ABORT with `d' = setDvirtio d (pre s).1` = MachCSL's blocked state ✓ — consistent, but not what `:1393-1398` and
  `:1251-1254` say ("`pre₁` = `setPhase .fetched` + the `taken` guard … performed by the matched run at pf's `DRead` (1 →
  3)").  *Exact change (§C W-DISK `R-dev` [R18.3 (b)] `:1393-1398`; §C W4 F9 `:1251-1254`, `:1267`):* "`pre₁` =
  `setPhase .fetched` AND, iff `taken = none` at the `DRead`, the latch `taken := some h`; the matched run performs
  `:526` (+ `:529` + `:516` iff the latch is free) at pf's `DRead` — 1 → 3 when free, 1 → 1 when held (MachCSL blocked
  at `:529`, the `dmaRead` never performed; pf's read value is then unused: its status `DWriteDev` aborts on the same
  guard); `poolRel` records which case (the MachCSL task's position does)".  S text.

## SUGGESTIONS

- **[R19.s1] F9 bookkeeping after [R19.1]–[R19.3]**: the drains before the gate are 0 → 5k (per cached sector: `choose`,
  `get`, `choose`, `modify`, root restart `devStep :580`); the root's restart step after a POP (`pure ()` → `.pure` →
  `m' = body`, `:578-580`) is 0 → 1, foldable into the POP (1 → 5) or the next START (1 → 3); the forked task's
  done-marking (`:581-583`, `σ.setRt`) is 0 → 1 at `DRet DIdle` (so "`DRet DIdle` → `dp' = none` 1 → 0" at `:1271`
  becomes 1 → 1 and `poolRel` carries `devrt.done`); a gate ABORT is 1 → 5k (drains, then the blocked guard is never
  taken).
- **[R19.s2] Cite drift**: `devStep`'s blocked arm `Lang.lean:586` (plan `:575-577`), `devBlocked :561-569`; `fetch
  :466-478`; drains `:581-586`.
- **[R19.s3] Name the pf drain in §B(11) (viii)'s neighbourhood as (ix)**: "pf drains every cached sector at the gate
  of each request (MachCSL: any time, one sector per root-loop step) — pf ⊆ MachCSL, device-internal, every spec
  silent; EQUAL durable image at pf-step boundaries".  It replaces (vii)'s crash-row caveat.
- **[R19.s4] `completeOk`'s `wce` branch**: say once that with `wce = true` (a hart negotiating F_FLUSH — not xv6)
  MachCSL need not drain but the matched run still may, so (a)'s block is unconditional.
- **[R19.s5] Header `:5-9`/`:110`**: rewrite the [R18.1] summary as "(A) diagnosed right (drain-dependent gate
  conjuncts), remedied by [R19.1] (pf drains at the gate; `completeOk` verbatim; `R-dev` full equality)".

## Owner questions the plan is missing

None required.  [R19.1]–[R19.3] are pf-internal device-model engineering in the SOUND direction (pf ⊆ MachCSL) and
change neither the published statement nor §A(6)/§B(11)'s trusted surface beyond the one named entry [R19.s3].  For the
record under the owner rule: RVWMO, riscv.cat and the Sail model in this tree have no device-internal events (Sail has no
device/DMA model; `MachCSL/Dev/*.lean` is the only device text); Zifencei and the PMAs are silent; virtio 1.x is silent
on when a device drains a write-back cache and on when it re-reads its configuration, and (the reviewer believes, from
memory, unverified in-tree — no spec text is checked in) requires IN/OUT data lengths to be multiples of 512 — [R19.1]
(c) removes any dependence on that requirement, so no ruling is needed; where pf drains is a choice EQUAL to one of
MachCSL's schedules, neither more nor less faithful to the ISA.
