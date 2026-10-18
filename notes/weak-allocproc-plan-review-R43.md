VERDICT: SATISFIED

# Review R43 of `notes/weak-allocproc-plan.md` (rev 53): REMAINING WORK audit, SCOPE audit, row 6l design

Reviewer: one-off reviewer + design advisor (advisory only: no builds, no proofs, no git/jj, no subagents). Every
`file:line` below was read at the working tree `../xv6iris-weak` on 2026-10-18 AFTER the post-rev-53 merges the
coordinator named (`Weak/CapPcLog.lean` `machRunPc`/`readAtPrimedOf`, `Weak/SilCand.lean`+`SilDep.lean`+`SilReplay.lean`
6b/6c, `Weak/SilClose.lean` kill′, `Weak/SilRegZero.lean` row 6k (A), `Weak/CapFetchProv.lean` row 6i, the census
`notes/W10-6m-census.md`). `Weak.lean:793-794` imports `SilClose`/`SilRegZero`; `CapFetchProv` is not yet wired.

**Scope of the verdict.** The question asked is whether workers may CONTINUE rows 1, 3, 6i and START 6m's census on
this plan. Yes: row 1 (narrow δ1, `../xv6iris-weak-w1/PROGRESS-W11F.md:362-384`, inc 15 with the `xstale : Option Resv`
snapshot refinement — a sound, more faithful variant of the sized rule) is unaffected by anything below; rows 3 and 6i
are DONE at the tip (as redesigned); the 6m census has landed and its findings feed the 6l design below. What the
verdict does NOT cover: rows 6b, 6j, 6n and 7 must not be briefed from rev 53 as written — [R43.1]–[R43.5] change their
content and size. None of the required changes shrinks the remaining work; two of them ([R43.1], [R43.4]) add to it.

## PART 1 — audit of rev 53

### What was verified and holds

- **Header/DONE accounting.** Spot-checked line counts at the tip: `CertZ*` 9,621 ✓, `CapF*` 1,253 ✓, `LockFacts*` 702 ✓,
  CertZ24–34 2,705 ✓ (obsolete, still imported `Weak.lean:775-798`), `GraphFetchBlocks` 801 ✓, `GraphFetchN2` 834 ✓,
  `GraphFetchWalkZ` 936 ✓, `WbPrimed` 707 ✓, `WbPrimedArm` 449 ✓, `PinTrapFrame` 467 ✓. `Sil*` is now 3,447 (3,209 at
  rev 53 + 6b/6c), plus `SilClose` 258 and `SilRegZero` 364 after the merges.
- **SCOPE (1), every cite:** `srvwmoXv6M2` `Weak/SailCycleOrderCycle.lean:179` ✓ (statement lines 179-212 ✓, conclusions
  = the five closed roots + `allocprocAns`); `xv6ConfS` `Weak/GraphFabConf.lean:165` ✓; `NCPU = 8` `MachCSL/TsoMem.lean:59` ✓;
  `xv6DiscAdequacy_closed` `Xv6/LinkDiscAdequacy.lean:44` ✓; `xv6FsAdequacy_closed` `Xv6/LinkSystemAdequacyClosed.lean:20` ✓;
  `unionAdequacyClosed` `Xv6/LinkUInitUnion.lean:163` ✓; the nine export conjuncts `Xv6/AccessDiscipline.lean:761-763` ✓
  (the docstring `:6` still says "EIGHT" — the plan already lists this, row 8); `textPcs` `Weak/KernelSitesDef.lean:244` ✓;
  `imagePinnedb :1869` / `pinsCover :1891` `Weak/KernelPins.lean` ✓ (the 1,689-site census figure was not re-counted);
  `cycleKillOfOrdStepS` is at `Weak/SilOrd.lean:412` (plan says :408 — drift only); `t2linSupplyCZIO`
  `Weak/GraphFetchAncSupply.lean:274` ✓; `CapF1.recRealizedH` `Weak/CapF1.lean:50` ✓; `machRunOfPfRun`
  `Weak/MachOfPf.lean:2950` ✓; `w13Wit` `Weak/W13Wit.lean:310` ✓; `allocprocTraceAns` `Xv6/AllocprocTrace.lean:402` ✓.
- **SCOPE (3)(ii) cites:** `emNoDangle` `Weak/GraphFetchBlocks.lean:87` ✓; `usedElemGateOk` `Weak/GraphFabConf.lean:377` ✓;
  `ioResidueGmo` `Weak/GraphFabResidue.lean:127` ✓; `fetchReplayOk :132` / `fetchLateChained :170` / `fetchProv :183`
  `Weak/G7Fetch.lean` ✓; `frameUnexemptAfter :77` / `frameNoDmaAfter :82` `Weak/PinTrapFrame.lean` ✓; `syncRealized`
  `Weak/RvwmoXv6Adequacy.lean:664` ✓, `segRealized :333`, `readAt :272`, `relSiteWCrel :218` ✓; `xstale` `MachCSL/Lang.lean:119` ✓.
- **Spec marks in SCOPE (3)** are correct and honest as far as they go: P2 STRONGER than the platform (the Svadu
  first-touch race), `usedElemGateOk` a device-model premise, `ioResidueGmo` STRONGER than RVWMO+PMAs (QEMU-true),
  the graph fetch model STRONGER than the Zifencei text (E1′), the tagged cat transcription a trusted surface, W13-wit a
  vacuity caveat not a soundness gap; the user-row `aq`-load side condition correctly marked STRONGER for user code and
  EQUAL for the kernel. The "kernel-wide" claim for conclusion (a) is CORRECT: the quantifier is over every bundle of the
  whole image on 8 harts from `_entry`, the export is a property of every reachable state, the pin table is exhaustive
  over the flat text walk, the kill is stated over every class graph, and the realization is from power-on. Missing
  header items: [R43.6].
- **roots.txt:20** (`Xv6.xv6DiscAdequacy_closed`) indeed omits `relProvAt` (and lists the conjuncts up to `kptMapsExp`
  only) — row 8 is right. `tools/ci/roots-weak.txt` has 13 roots ✓; `tools/audit/baseline-weak.json`, `tools/tcb/expected.json`
  exist ✓.
- **Dependencies in the table** are right where they are stated (6l after 3; 6b after 1/3/4; 6f after 3/4/6a; 6n after
  6a–6k; 7 after everything). B4 `gfDevWIoCZ` (inventory) is correctly absent: closed by `CapF4.gfDevWIoCZOf` from the
  header premise `usedElemGateOk`.

### REQUIRED changes

**[R43.1] Row 4 is CLOSED NEGATIVELY on its second half, and the consequence is missing from rows 6b/6n/7: the kill's
graphs and the twin member carry REGISTERED classes, but `relSiteWCrel` holds only on the Wb-PRIMED re-tag.**
*Evidence.* `CapPcLog.readAtPrimedOf` `Weak/CapPcLog.lean:817-830` concludes `readAt` at `cf′` with `WbPrimed.cfgRel cf cf′`
and its docstring (`:811-816`) says the clause "CANNOT be moved to `cf` itself": on the registered machine the walker's
A/D `LExStore` after `fence rw,w` clears `wRelp`, so the release `sw` is `.WCplain` there. The bundle's rows get their
classes from the REGISTERED classifier: `hemitf` (`Weak/WeakRvwmoFab.lean`, `HFone`/`HFpair`) uses `pstepEv` and
`hlblRealizes`/`lblPost` (→ `pclsEv`); `gcls` reads the label's class (`Weak/WeakRvwmoKillArms.lean:149`); the Sil twin
replays with `pstepEv pclsEv` (`Weak/SilReplay.lean:245,251`, `Weak/SilPfBridge.lean:112,203`, `SilWalk.stepOk`'s
`lblRealizes pclsEv` `Weak/SilWalk.lean:71`). So at the realized twin member `SilAgree.memberS` the release message's
class is the registered one, and (i) `readAt`'s conjunct `relSiteWCrel σ c.pcLog` (`RvwmoXv6Adequacy.lean:274`) is not
available on that log, (ii) CertZ14/18's `np REL` facts (`CertZ18.sp` = `np ∧ ¬failAcq`, `Weak/CertZ18.lean:45`) and
`relCoversS`'s window facts are stated on GF's classes. The plan's row 4 text ("or keep it on `cN′` … then `readAt` is
restated over `cN′`, S") is what happened, but no row absorbs the restatement: 6b (`readAt` step 3 "at the twin member"),
6n (`l2ClaimS` consumes `badSeg`/`wpublished`/`readAt` by class) and 7 are sized as if the member's log were usable as is.
*Exact change.* Mark row 4 DONE (pcLogAgree discharged) with the finding; add to row 6b (or a new row 6b′, Weak, after
rows 1/3/4) ONE of: **(a) re-tag inside the classification** — state `l2ClaimS`/`readAt`/`relCoversS` over the primed
re-tag `retagLog f (logS c)` of the realized member (`WbPrimed.cfgRel`'s log clause `Weak/WbPrimed.lean:333-339`) and
prove the Sil twin's `lblAgreeS` and the transport's `np` facts are class-blind except at release sites where the re-tag
is exactly `.WCrel` (FAITHFUL — proof organisation, [OWN.97]'s instance; ≈ 0.4–0.9k); or **(b) prove on realized runs
that no walker write-back follows the release fence** (the lock word's page is already dirty from the holder's own
swap, D is never cleared, `menvcfg.ADUE` on) — needs the realized Sv39/TLB state at the release store from the
`dataRealized` machinery (FAITHFUL; ≈ 0.5–1k, M−; it would also let `readAt` move back to `cf`). Recommend (a).
Re-size 6b to 0.9–2.4k. Both options keep the spec unchanged (RVWMO's rule 4 orders explicit later stores; Svadu's A/D
update is an implicit access — the primed instance is the faithful reading, [OWN.97]).

**[R43.2] Rows 2, 3, 6i, 6k are DONE at the tip; the table and the Σ must say so, and row 6i's result changes rows 3′/6n/7.**
*Evidence.* 6b/6c merged (`SilCand.depView` `Weak/SilCand.lean:62`, `SilReplay.progOkD :35`, `SilCand.ordOk :51`), kill′
`Weak/SilClose.lean` (`cycleKillS :170`, `cycleKillCZS :228`), 6k (A) `Weak/SilRegZero.lean` (`wprotRegdZ`,
`cycleKillZS`), 6i `Weak/CapFetchProv.lean` (315 l., `../xv6iris-weak-w2/PROGRESS-W11F-6i6m.md`). The 6i worker found
that **`fetchProv` is FALSE at the untrimmed `forgetF GT`**: `xv6ConfS` gives only `emFetchIn` ("rows' fetch edges ⊆
`gtFetch`", `Weak/GraphFetchHullZ.lean:70,94`, `GraphFetchAncSupply.lean:105,120`), so a quantified bundle may store
junk pairs, `gfetchE` (`Weak/WeakRvwmoAcyc.lean:227`: membership ∧ gmo-forward) then has arbitrary gmo-forward edges,
and the class kill `CatLin.cycleKillCZC` (`Weak/GraphFetchHullZ.lean:520`) is FALSE-SUSPECT as quantified (a junk
gmo-forward edge closes a cycle with any gmo-backward racy path); nor is provenance hull-stable. Landed instead: `trimF`
(fragment filtered to row-emission edges, `CapFetchProv.lean:78`), `provAll`, the trimmed kill `CatLin.cycleKillCZT`
(`cycleKillCZC` + `provAll` + IH over TRIMMED hulls) and `t2linSupplyCZT`/`t2linSupplyCZTtagged` (`:206,238`), which give
`t2linSupplyCZIO`'s conclusion for the UNTRIMMED graph via `topoSupplyZIO` at `trimF GF`.
*Soundness of the coordinator's re-route (checked):* trimming only removes `gfetchE` edges, so `racyDIO (trimF GF) ⊆
racyDIO GF`; `confTrim` keeps the bundle (every row emission's edges are provenant, so `emFetchIn` still holds);
`provPair` is existential over emissions of the row, hence a superset of whichever emission the normalization picks;
the normalized candidate's rows are GF's (`rowsRel`), so M2's premises are about the untrimmed GF. The twin kill
(`SilKill.cycleKillOfL2S`, `certSupplyS`'s hull premise, `l2ClaimS`) must be restated at `trimF boot (gfHull GF cs)` with
`provAll` in `l2ClaimS`, and `cutSupplyCZC`'s hull normalization (`cutSupplyOfCycleCZC`, `GraphFetchWalkZ`) must be read at
the trimmed hull — S, ≈ 0.1–0.3k. Other landed consumers of the fragment: `G7Fetch.g7FetchCert`'s `hrep`/`hlate` quantify
over every `gzFetch` item (fake items satisfy `gzFetch`) → use `g7FetchCertP`; `w13Wit` is a concrete bundle, unaffected;
`t2linSupplyCZIO` stays for the concrete-bundle route. SOUND; FAITHFUL (the fragment is proof data, riscv.cat has no
fetch events; nothing in the trusted surface changes).
*Exact change.* Rows 2, 3, 4, 6i, 6k: DONE with one-line results; new row 3′ "retarget the twin kill to `cycleKillCZT`"
(S, 0.1–0.3k, H); row 7 uses `t2linSupplyCZTtagged`; SCOPE (1) bullet "the cycle kill" gains the sentence "stated for
every class graph whose fetch fragment is provenant (`trimF`); the untrimmed `cycleKillCZC` is not provable as quantified";
row 6i's "H, 0.1–0.4k" becomes "DONE as a redesign, 315 l.". Update the header paragraph and the Σ accordingly
([R43.7] for the numbers).

**[R43.3] Row 6k (A) is a correct INTERIM but it moves `protReg`/`protRegZ`'s burden into row 6j, whose sizing does not
contain it (coordinator note #2).** *Evidence.* `SilRegZero.wprotRegdZ` records the zero in the TWIN WP package's
registration ghost (`Weak/SilRegZero.lean` §1-§2; `wpPackageProtZS` replaces `wpPackageProtS + regZeroS`); kill′ still
takes `SilKill.wpPackageS` and `wpPackageProtS/ZS` — Iris-level premises "xv6 is verified in the twin weak logic"
(`Weak/SilKill.lean:115-125`, `SilClose.lean:73-85`). Row 6j's stated purpose is to REPLACE these by export-sourced facts
("no weak-WP premise in the header"). Once the twin WP package is gone, (A)'s ghost is gone with it, and `protRegZ` at
the realized member must come from the export: E1 (twin realization = row 1 inc 19 + a twin CapF1 — needed by 6b
anyway), E2 (classes of realized lock writes — rows 6a/6f, and [R43.1]), E3 (static lock words are 0 in the image —
a Weak census, ≈ 0.1k), E4 (a 10th APPEND-ONLY export conjunct `dynLockWinZAt` pinning the pipe-lock word's value at
the window opening — MachCSL serial lane, ≈ 0.2–0.5k, `../xv6iris-weak-w3/PROGRESS-W10N2p.md` "row 6k" (E4)), plus the
Weak glue `lkFold ↔ altFold` through `rmem` (0.5–1k). So YES: (A) moves the burden into 6j, and 6j's 0.8–1.5k is short by
≈ 0.8–1.6k. *Exact change.* Row 6j: spell out its `protReg`/`protRegZ` sourcing (E1–E4 + glue), re-size to 1.6–3.1k /
10–22 h, dependency "+ row 1 inc 19, + E4 in the MCSL lane after row 1" (put E4 beside row 5 as 5′, 0.2–0.5k, tcb
unchanged, APPEND-ONLY like `kptMapsExp`/`relProvAt`); row 6k: "DONE (A) as INTERIM — the published header must not
carry `wpPackageProtZS`; retired by 6j's export route (B)". Spec: both FAITHFUL (proof organisation; `regZeroAt` is an
xv6 program fact about registration sites); an Iris premise left in the header would be WEAKER — the owner question
Q-6J-PROTREG below exists only in case 6j's export route is judged too expensive.

**[R43.4] Row 6l's design and the new named fact `oneByteS` (coordinator note #1) — see PART 2.** *Exact change.* Replace
row 6l's one-liner by the design's row text (PART 2 §6): "incremental walk with a LOCAL gate; `orderSupplyCZ3`,
`lockDiscCZ3` and GF-level `oneByteS` retired; residual GF-level facts G1 (kernel-row AMO = `acquire+0x1c`'s
`amoswap.w.aq`) and the device-row `diskFabPo`; windowed `lockCoSP`", size 1.4–2.2k (+0.5–1.5k of 6m's pinned reads
inside it, per the census §8), 12–24 h, confidence M. Move `oneByteS` to realized members (`SilOrd.spNfS` is needed only
for the COMPLETE member, where every event is realized and the export gives it). Keep the fallback (orderSupplyCZ3 NAMED,
WEAKER) in the row. Row 6m: "NOT separable from 6l" (census F1–F3) — its order-dependent sites (`holding+0x0` from
`acquire`, `started`, the four `virtio_disk_intr` reads, the eight device reads, the silent window) are inputs of 6l's
gate (PART 2 §4); the census's 2.3–4.7k + 0.5–1.5k replaces 1.5–4k.

**[R43.5] The header premises list in SCOPE (3)(ii) and §B(11) omits three facts the kill′ chain names today.**
*Evidence.* `LockFacts3.diskLockFree :122` / `diskFabPo :127` (device-row facts inside `lockDiscCZ3`'s NF3, needed by
`cycleKillDiscS` and, as `diskFabPo`, by PART 2's design), and — until [R43.3]'s route (B) lands — the twin WP packages
`wpPackageS`/`wpPackageProtZS` (`SilClose.cycleKillS :170` hypotheses 4–5). *Exact change.* Add to SCOPE (3)(ii):
"`diskFabPo` — the device row's fabric RAM stores are gmo-ordered along its program order. Spec: RVWMO is silent on
DMA; the virtio spec requires buffer data visible before the used-ring update — EQUAL to virtio for data→used-idx,
STRONGER for other pairs, equal to the pf disk program [OWN.33]; device-model premise like `usedElemGateOk`"; and
"`diskLockFree` (device DMA never writes a lock word) — device-model, dischargeable from the pf disk program's
descriptor targets (S) once DMA targets are export-chained; or dropped under PART 2's design". State explicitly that the
twin WP packages are INTERIM only.

**[R43.6] The confidence column understates two rows and the Σ is stale.** Row 6i was "H" and turned into a FALSE-finding
plus a 315-line redesign; row 6k was "M" and turned out not export-derivable. Rows 6b (+re-tag), 6j (+protReg) and 6n
(the assembly that now also absorbs `provAll` and the re-tag) should be "M−/L+" with the new sizes. *Exact change.*
Recompute: done since rev 53 ≈ +1.4k (Sil* +238, SilClose 258, SilRegZero 364, CapFetchProv 315, CapPcLog +~110, census
notes not counted); remaining midpoint ≈ 26k − 2.6k (rows 2/3/4/6i/6k) + 0.7k ([R43.1]) + 1.2k ([R43.3]) + 0.3k (6l's
re-size) + 1.0k (6m per census) + 0.2k (3′) ≈ 26.8k → % done by lines ≈ 117.9 ÷ (117.9 + 26.8) ≈ 81.5 % (gross), range
76–87 %. The risk sentence should now name rows 1, 6l(+6m), 6j, 6b′ as the LOW/M− cluster.

**[R43.7] Launch-order line (`:2635`) and §C W10 line (`:5750`) are superseded again.** w3's kill′ and 6k (A) are merged;
w2 is on 6m's census (done) → next per the census; w1 on δ1 inc 15. *Exact change.* Tag `[rev 54] SUPERSEDED` and write
the new order: w1 δ1 inc 15–19 → X1 rest → E4 (5′); w2 row 3′ (kill retarget, S) → 6f/6h → 6b′ (re-tag, needs 1/3/4);
w3 row 6l (PART 2) with 6m's pinned-read table → 6m's taint walker/value lemmas; 6j after 1 (inc 19) and 6f; 6n/7 last.

### SUGGESTIONS

- **[R43.s1]** Retire CertZ23's order route in the docstrings once PART 2 lands: `CertZ23.lean` (`orderSupplyOfDisc3`,
  `lockDiscCZ3`) and `LockFacts3.lean` §4 (`lockDiscGF`, `relSitesGF`, `nf1S`, `nf2S`) join CertZ24–34 as
  obsolete-but-green; the cosmetic cleanup row should list them (≈ 3.4k dead lines then).
- **[R43.s2]** Row 1's PROGRESS has a faithfulness note on inc 16 (`tv ≤ tvn` alone is WEAKER than RVWMO; the simple
  sound bound `rv ≤ tvn` may be TOO STRONG for the twin whose bound is `SilCand.depView`). Record in row 1 that the
  MachCSL rule's bound must be ≤ the twin's (`depView`, 6c) or the twin W4 (inc 19) cannot map stale steps — this is
  row 1's real remaining design risk, not the reservation (now removed by the snapshot refinement).
- **[R43.s3]** SCOPE (1): `xv6ConfS … (NCPU + 1)` — say "8 hart rows + 1 device row" explicitly; readers take "9 harts".
- **[R43.s4]** Row 8: add `Weak.lean` wiring of `CapFetchProv` and the `#print axioms` of `t2linSupplyCZTtagged`
  (propext, Classical.choice, Quot.sound per the worker's acceptance) to the registration checklist.
- **[R43.s5]** Cite drift: `cycleKillOfOrdStepS` is `SilOrd.lean:412`; `relSiteWCrel` is `RvwmoXv6Adequacy.lean:218`
  (`:190` in the §D entries).
- **[R43.s6]** The DONE total's caveat should also exclude `CertZ23`/`CertZ16-17`'s order machinery if PART 2 is taken
  (≈ 0.9k more obsolete lines), so "% done" is not inflated by two generations of the same lemma.

## Row 6l design

### 1. Spec first: what RVWMO / riscv.cat require of a walk order

Nothing. The walk order `L` is a proof device: the member built along it is a promise-free run whose append order IS
the realized MachCSL log order, and the kill needs that member to agree with `GF` on (i) every row's labels up to read
re-indexing (`SilAgree.lblAgreeS`), (ii) coherence among the lock protocol's successful writes (`CertZ18.lockCoSP`,
`Weak/CertZ18.lean:50`), because the transport `csChainedT` (`Weak/GraphFetchN2.lean:392`) reads the holder's acquire
and release in the member's log and concludes gmo facts at `GF` through `coLeR` (`:198`). RVWMO's own global order
`gmo` is NOT a usable walk order: po ⊄ gmo (W→W reordering, load buffering are allowed, [OWN.2]), and an emission can
only be replayed in po. So `L` must be a linear extension of po ∪ fabric order ∪ co_sp. The cross-lock finding
(`../xv6iris-weak-w3/PROGRESS-W10N2p.md:83-91, 235-250, 605-612`) is exactly why cat alone does not give one: xv6's
release is a PLAIN `sw zero` after `fence rw,w` (no `.rl`), so "release lk1 ;po acquire lk2" has NO ppo edge (rule 4
needs a fence AFTER the store, rules 5–7 need `.aq` on the earlier access or RCsc on both), and the cycle
A(rel lk1) →po B(acq lk2) →co C(rel lk2) →po D(acq lk1) →co A closes in gmo only through the paired acquires' `.aq`
(A's own acquire <ppo B, C's own acquire <ppo D) AND mutual exclusion (B co-before C's acquire, D co-before A's acquire).
CertZ23 encodes exactly this: the κ-key (`CertZ23.kapLe :107-170`, `keyLt :190-250`) anchors a release at its own
acquire (NF2a) and needs NF1′ (cross-hart sp writes co-outside a critical section) at the co edge into a release
(`keyLt`'s last case, `hNF1`). NF1′ and NF2a are VALUE / provenance facts about xv6 (mutual exclusion; "a release's lock
is the one this hart acquired") — true in every realized run, but at an arbitrary cat-consistent `GF` they are part of
what the theorem proves (the racy-cyclic `GF` is refuted by the kill that consumes the order). That is the circularity
of `orderSupplyCZ3`/`lockDiscCZ3` (`Weak/SilOrd.lean:14-16`, `LockFacts3.lean` header "Why … stay NAMED").

Marks (vs RVWMO):
- **(A) keep `orderSupplyCZ3` NAMED** (rev 53's fallback): a true but unproved xv6 program fact in the trusted base —
  WEAKER (the theorem is conditional on it). Cost 0.
- **(B) assume acyclicity of po ∪ fabric ∪ co_sp outright** — STRONGER than RVWMO (rejects real executions on other
  programs; on xv6 it happens to be true) — reject, as rev 53 does.
- **(C) the incremental order below** — FAITHFUL: no assumption beyond cat consistency, the bundle, the image and
  facts at REALIZED prefixes; it never uses NF1′/NF2a at `GF`.
- **(D) a smaller NAMED residual** (fallback of (C)): name only `NoStuck` ("at every realized prefix some row is
  enabled") — still a GF-quantified program fact, WEAKER, but one lemma instead of six facts.

### 2. The key observation that removes the circularity

Build the order AS the walk proceeds, with a LOCAL gate, and prove progress from cat consistency plus facts at the
realized prefix. The gate is: **a kernel-mode AMO on a registered lock word may be appended only when, for each of its
bytes, its `GF` rf-source write is the member's LATEST write of that byte** (a successful acquire then reads 0 in the
member exactly as in `GF`); **every other event is appended as soon as it is its row's next event** (releases, plain
stores, loads, fences, I/O; fabric members in fabric order; failed acquires as SILENT steps when the datum gives one).
Why no deadlock: suppose no row is enabled. Every row with events left has a next event that is a gated kernel AMO `e`
whose `GF` source `src` (a 0-write, co-immediately before `e`'s write by atomicity, `gatomicity`
`Weak/WeakRvwmoGraph.lean:309`) is UNREALIZED (a realized-but-not-latest source is contradictory, Lemma 3 below).
`src` sits on a row `h′` that is not done; `h′`'s next event `e′` is po-≤ `src`; `e′ = src` is impossible (a store is
ungated, hence enabled), so `e′ <po src` and `e′` is itself a gated kernel AMO — an `amoswap.w.aq` (G1) — and rule 5
(`acqGmoAfterC` `Weak/CatLin.lean:255`) gives `gpos e′ < gpos src`; co ⊆ gmo (`gwixLtGmo` `Weak/WeakRvwmoLock.lean:100`)
gives `gpos src < gpos e`. Following `e → e′ → …` over finitely many rows yields `gpos e < gpos e` — contradiction. The
fabric row and dev-order waits close the same way (fabric order ⊆ gmo by `ioResidueGmo`'s R3 + `gfDevWIo`; a row's
I/O event that is the next fabric event is enabled; the device row's own order by `diskFabPo`). Mutual exclusion is
never used for unrealized events; it is used only at REALIZED prefixes (Lemma 3), where the export supplies it.
The 6m census's F1–F3 fit the same gate: a PINNED read (`holding+0x0` from `acquire`, `started`, the `virtio_disk_intr`
and device reads) is enabled iff its `GF` source is the member's latest write of the byte, and a failed acquire's
silent step is enabled iff its `GF` source is realized (the datum then has a hold window). The progress argument is
identical (pinned reads are kernel loads/AMOs ordered by rule 5 only when `.aq`; for a plain pinned LOAD the hop uses
rfe ⊆ gmo into it and the fact that the SAME hart's later events are not needed — see §5 R6).

### 3. Statements (Lean-level sketches; new leaf `Weak/SilOrd2.lean`, imports `Weak.SilClose`)

```lean
/-- The gate. `latestW S b` = the member's latest write of byte `b` (gwix in the member / log position);
`srcOf GF e b` = the GF write `e` reads at byte `b` (`CertZ30.evOfWr`-style lookup from `greadsByte`). -/
def SilOrd2.gated (GF : Gfexec) (D : Nat → CertZ7.EmData) (Lb : Int → Prop) (pin : List Int) (x n : Nat) : Prop :=
  (∃ aq base ts rvs wvs k, (GF.gfGd.gdG.gxProg.getD x [])[n]? = some (.LRmw aq false base ts rvs wvs k) ∧
      Lb base ∧ kernelMode ((D x).f n)) ∨
  pinnedRead GF D pin x n            -- 6m §3 route P + §4 device reads, by the emission state's PC / device position

def SilOrd2.enb (GF : Gfexec) (D : Nat → CertZ7.EmData) (Lb : Int → Prop) (pin : List Int) (fab : Nat → Efab)
    (S : SilWalk.St) (cnt : Nat → Nat) (x : Nat) : Prop :=
  cnt x < (GF.gfGd.gdG.gxProg.getD x []).length ∧
  ((x, cnt x) ∈ GF.gfDev → GF.gfDev[devCnt S]? = some (x, cnt x)) ∧          -- fabric order
  (SilOrd2.gated GF D Lb pin x (cnt x) →
     ∀ b t v, greadsByte GF.gfGd.gdG (x, cnt x) b t v →
       ∃ w, srcOf GF (x, cnt x) b = some w ∧ SilOrd2.realizedAt S w ∧ SilOrd2.latestW S b = some w) ∧
  (CertZ24.lblFail Lb lb → ∃ w, srcOf GF (x, cnt x) base = some w ∧ SilOrd2.realizedAt S w)   -- silent slot

/-- Per lock byte and registration window: realized sp writes = a GF-co-prefix, in GF-co order. -/
def SilOrd2.coPrefix (GF : Gfexec) (Lb : Int → Prop) (S : SilWalk.St) : Prop :=
  ∀ b, Lb b → ∀ x y vx vy, gwritesByte GF.gfGd.gdG x b vx → gwritesByte GF.gfGd.gdG y b vy →
    CertZ18.sp GF.gfGd.gdG b x → CertZ18.sp GF.gfGd.gdG b y → sameWin S b x y →
    (gwix GF.gfGd.gdG x < gwix GF.gfGd.gdG y → SilOrd2.realizedAt S y → SilOrd2.realizedAt S x ∧ memPos S x < memPos S y)

/-- The walk invariant: `SilOrd.inv`'s per-hart clauses (unchanged) + counts/fabric (`SilOrd.pref` without `L`) + `coPrefix`. -/
def SilOrd2.inv (GF) (D) (Lb) (Rel) (fab) : SilWalk.St → (Nat → Nat) → Prop := …

/-- NAMED at REALIZED prefixes (same family as `SilKill.acqAqS`): window alternation of lock-word writes in the
member's log (swap ≠ 0 by hart h, then release = 0 by h, …), word-wide, from `lockWordDiscAt`/`lkCpuReadAt`. -/
def SilOrd2.prefixDiscS (boot d0 fab im N P) : Prop :=
  ∀ GF ad S cnt, … → SilWalk.ok d0 S → SilOrd2.inv … S cnt → wlpAltWin (SilAgree.logS S.c) P

/-- THE DATUM, now asked only at ENABLED events (weaker than `SilOrd.hartStepRIS`, which asks it for `L[k]`). -/
def SilOrd2.hartStepRIS2 (d0) (rows) (Lb) (GF D pin fab) (Rel) : Prop :=
  ∀ S x lb … k, SilWalk.ok d0 S → … → SilOrd2.enb GF D Lb pin fab S cnt x → (rows.getD x [])[cnt x]? = some lb →
    ∃ lb' o pa da ls' pC' w', SilWalk.relW Lb lb (lb', o) ∧ SilWalk.stepOk S x lb' o pC pa da ls' pC' d' w' ∧ Rel x (cnt x + 1) pE' pC'

/-- LEMMA 1 (NoStuck): cat + bundle + residue + G1 + diskFabPo + prefixDiscS ⇒ some row is enabled while rows remain. -/
theorem SilOrd2.noStuck … : rvwmoCatAD GF.gfGd ad → gfexecConfZF boot d0 fab GF → ioResidueGmo GF → gfDevWIo GF →
    SilOrd2.kernelAmoAq boot GF → LockFacts3.diskFabPo GF → SilOrd2.inv … S cnt → wlpAltWin (logS S.c) P →
    (∃ x, x < rows.length ∧ cnt x < (rows.getD x []).length) → ∃ x, SilOrd2.enb GF D Lb pin fab S cnt x

/-- LEMMA 2 (policy): `SilWalk.walkPol d0 rows Lb (SilOrd2.inv …)` — `walkPolOfOrdS`'s proof with `noStuck` choosing `x`
and the datum at the enabled event; the fabric clause as in `walkPolOfOrdS` (`hB`), the counting clause without `L`. -/
theorem SilOrd2.walkPolS2 …

/-- LEMMA 3 (sources): at an invariant state, a gated AMO whose GF source is realized but not the member's latest is
impossible (atomicity + `coPrefix` + `wlpAltWin`). -/
theorem SilOrd2.srcLatestOrUnrealized …

/-- LEMMA 4 (CoAgree): at a COMPLETE walk, the trace-derived order `Lof S := S.c.tr.map … ` satisfies `CertZ8.walkOrd`
and `CertZ23.ordCoSP` (windowed) — so `SilOrd.lockCoOfOrdS` is REUSED verbatim to get `lockCoSP` (windowed). -/
theorem SilOrd2.ordOfTrace … : SilOrd2.inv … Sf cntF → done → CertZ8.walkOrd rows GF.gfDev (Lof Sf) ∧ CertZ23.ordCoSPW …

/-- The walk supply and kill′′: `SilOrd.walkSupplyOfOrdStepS` with `orderSupplyCZ3`/`spNfS`/`stepSupplyS` replaced by
`stepSupplyS2` (datum at enabled events), `prefixDiscS`, `kernelAmoAq`, `diskFabPo`; `SilClose.cycleKillS` likewise. -/
theorem CatLin.SilOrd2.walkSupplyS2 … ; theorem CatLin.SilClose.cycleKillS2 …
```

`oneByteS`: `SilOrd.spNfS` is consumed only in `SilOrd.lockCoOfOrdS` (`Weak/SilOrd.lean:243-280`, hypothesis `hnf`) for
writes of the FINISHED member, where every event is realized; restate it as `SilOrd2.oneByteRealS` over `RunDataS`
members (like `acqAqS`) and discharge it from the export at the member (every realized lock-word write is a 4-byte
aligned swap/release/init of ONE word, `struct spinlock` ≥ 24 bytes apart) — rows 6f's machinery; drop
`CatLin.SilClose.oneByteS` (keep `spNfOfOneByte` for the record).

### 4. Why it is not circular, and what remains GF-level

The gate reads only (i) `GF`'s labels, rf and co (given data of the quantified graph), (ii) the REALIZED prefix (the
member's log, its latest writes, its alternation — facts the realization supplies at every prefix, as `acqAqS`/`relCoversS`
already are at complete members; prefixes of a realized twin run are realized), (iii) the emission datum `D`
(`CertZ7.emDataOk` `Weak/CertZ7.lean:44`: program state per item, so kernel/user mode and PC are known). NoStuck uses
NO fact about unrealized events except their LABELS and cat's order axioms. The residual GF-level facts are:
- **G1 `kernelAmoAq`**: every `LRmw` item of a row whose emission state is in S/M mode is `acquire+0x1c`'s
  `amoswap.w.aq` (4 bytes, aligned). Spec: image (`LockFacts.lean`: the image's only AMO) + kernel text identity for
  the fetched bytes (`kFetchText`, `Xv6/KptTextIdent.lean`) — FAITHFUL per pc, no values involved; ≈ 0.1–0.2k. User-mode
  AMOs are NOT gated (if one wrote a kernel lock word in the member, the realized export refutes it), so no fact about
  user rows is needed for the order.
- **`diskFabPo`** (already named, `LockFacts3.lean:127`): device-row events gmo-ordered along the device's program
  order — a device-model premise ([R43.5]); `diskLockFree` is NOT needed (a device 0-write source is handled by the
  device-row hop).
- **cat**: `gatomicity`, `gppoCat6Gmo` (rule 5 via `acqGmoAfterC`, rule 4 via `fenceGmoAfterC`), `gloadValue`
  (`grfeGmo` `Weak/AxGraph.lean:261`), co ⊆ gmo; **bundle**: fabric pins (`CertZ8.devCount`/`quietNotDev`
  `Weak/CertZ8.lean:107,181`), `ioResidueGmo` R3, `gfDevWIo`.
Everything else (`lockDiscCZ3`'s NF1′, NF2a, NF2c, NF3a; `orderSupplyCZ3`; `relSitesGF`, `nf1S`, `nf2S`) is retired.

### 5. Induction measure, reuse, risks

- **Measure**: the remaining-events count `CertZ2.rem` (`SilWalk.walkRun` `Weak/SilWalk2.lean`), unchanged; NoStuck is
  the progress lemma; the deadlock argument inside NoStuck is a pigeonhole over the ≤ `rows.length` rows (iterate the
  "waits-for" successor `rows.length + 1` times and extract a repeat; gpos strictly increases along it).
- **Reuse**: `SilWalk.walkPol`/`walkRun`/`certSupplyOfWalkS` unchanged; `SilOrd.walkPolOfOrdS`'s fabric block `hB` and
  counting lemmas (`CertZ8.ordCount`, `filterSnoc`, `take_S_r`) verbatim with the trace-derived `L`; `SilOrd.lockCoOfOrdS`,
  `CertZ8.ceidOrd`/`memberWixIff`, `CertZ30.evOfWr` verbatim; `CertZ23.ordCoSP` as the final statement (windowed
  variant); `acqGmoAfterC`, `fenceGmoAfterC`, `gwixLtGmo`, `grfeGmo`, `CatLin.acqFoldFreeG`'s source reasoning;
  `SilKill.cycleKillOfL2S` unchanged (only the supply changes).
- **Size**: SilOrd2 ≈ 0.9–1.4k (gate + invariant 0.15k, NoStuck 0.4–0.6k, Lemmas 3–4 0.25–0.4k, policy 0.15k) + G1 0.1–0.2k
  + the windowed `lockCoSP` restatement through `CertZ18.agreeW3`/`GraphFetchN2.agreeW`/`coLeR`/`SilAgree.agreeW4OfRPS`
  0.2–0.4k + glue (`walkSupplyS2`, `cycleKillS2`, `oneByteRealS`) 0.1–0.2k = **1.4–2.2k, 12–24 worker-hours**; plus the
  census's pinned-read table and the silent-window gate **+0.5–1.5k** (6m's part inside 6l). Confidence **M** (was L).
- **Risks**: (R1) windowed vs unwindowed `lockCoSP`: `csChainedT` uses co only inside `inWin` (`GraphFetchN2.lean:244`,
  `coLeR` at `ACQ`/`w′` in the window), so windowed should suffice; if a consumer needs cross-window co (pipe-lock
  re-registration), the alternative is the W11-D chain argument (old life <ob new life's `initlock` through the
  `kmem.lock` hand-off), L — avoid. (R2) `prefixDiscS` must be dischargeable at PREFIXES: same shape as `acqAqS` but
  quantified over `SilWalk.St` with `inv` (as `hartStepRIS` is); needs the twin realization (row 1 inc 19 + twin CapF1)
  for prefixes — the same dependency 6b has. (R3) G1 for S-mode rows after a user program ran: the kernel text is
  pristine (`textPristine`) and `fetchProv`-trimmed fetches of kernel text return image bytes — relies on
  W5d-G's kernel fetch fact; check it is available at `GF` (it is used by the pins). (R4) a failed acquire whose source
  is realized but no silent `q` exists must be impossible — that is 6m's datum (the 6c bound = riscv.cat), now
  restricted to realized sources (strictly easier than today's unconditional `hartStepRIS`). (R5) The device row's
  "next event" when it is not a fabric member (DMA descriptor reads): ungated, enabled — but its value agreement is the
  census's eight device reads (route P): pinned, gated on a realized source; their hop uses rfe ⊆ gmo into the read and
  `diskFabPo` within the device row. (R6) Plain PINNED kernel loads (`holding+0x0`, `started`, `virtio_disk_intr`'s four):
  a stuck pinned load `r` has an unrealized source `w` on row `h′` with `e′ <po w`; `e′` is gated (AMO: rule 5 ✓) or a
  stuck pinned LOAD — then `gpos e′ < gpos w` needs a ppo edge from a plain load to a later store: NOT given by RVWMO in
  general. Census check: the sources of the pinned loads are release stores / `started`'s store / the device's used-ring
  writes, and the stuck-pinned-load → later-store hop on the SAME hart passes a `fence rw,w` (`release+0x16`, `main+0xae`)
  or the device row's program order in every xv6 case — `main+0x16`'s `started` read is followed by `fence r,rw`
  (`PFence +0x18`, census §3.2: rule 4 with pr=1 orders it before every later store ✓); `holding+0x0`'s reader in `acquire`
  reaches its own swap (`.aq`, rule 5 does not help backwards) — but the read's branch (`bnez`) is a CONTROL dependency to
  every later store (rule 11, `gdepsGmo` in `rvwmoCatAD`) ✓; `virtio_disk_intr`'s loads feed `b->disk = 0`'s address (addr
  dependency, rule 9/10 ✓) and branches (rule 11 ✓). So the hop holds via dependencies at `GF` (tagged deps are in
  `rvwmoCatAD`'s `gppo12`), FAITHFUL, but it must be checked per pinned site in the worker's table. If some pinned site
  has neither, the fallback is census F2 (b) (a re-convergent `holding` arm) for that site.
- **Fallbacks**: (D) name `SilOrd2.noStuck`'s conclusion (WEAKER, one GF-level lemma, 0 lines); then (A) as in rev 53.

### 6. Row text proposed for rev 54

| 6l | **the walk ORDER, incremental with a LOCAL gate** (Weak, w3) | Replace the input order by a per-step choice: kernel-mode lock AMOs and the census's pinned reads are appended only when their `GF` rf-source is the member's latest write of the byte, failed acquires when their source is realized, everything else at once; progress from cat (rule 5, co/rfe ⊆ gmo, atomicity) + the realized prefix's window alternation (`prefixDiscS`) — never NF1′/NF2a at `GF`; the order is read off the finished trace and `SilOrd.lockCoOfOrdS` reused (windowed `lockCoSP`); `orderSupplyCZ3`/`lockDiscCZ3`/GF-level `oneByteS` RETIRED; residual GF-level facts G1 (kernel-row AMO = `amoswap.w.aq`, image) and the device-model `diskFabPo`. | rows 3′, 1 (inc 19, for `prefixDiscS` at prefixes) | 1.4–2.2k (+0.5–1.5k 6m's pinned reads) (fallback: name `noStuck`, 0) | 12–24 (+4–12) | M |

### 7. Coordinator notes, answered in one place

- **Note #1 (`oneByteS`)**: move to realized complete members (`SilOrd2.oneByteRealS`); §3 above. It is needed only by
  `lockCoOfOrdS` at the finished member.
- **Note #2 (6k (A) vs 6j)**: yes, (A) moves the burden into 6j; 6j's sizing is short by ≈ 0.8–1.6k and gains a MachCSL
  conjunct (E4) — [R43.3]. (A) is the right interim (reversible, `SilClose` kept intact).
- **Note #3 (6i re-route; census)**: the re-route is sound — [R43.2]; the census's F1–F3 are absorbed by the gate
  (pinned reads + silent window), F2's `holding+0x0` from `acquire` is handled by the gate plus the rule-11 hop (R6),
  F4's PTE custody is a 6m item (recommend (a), from the realized prefix, like `prefixDiscS`), F5's device reads are
  pinned (R5). Answers to §9: Q-6M-ORDER (a); Q-6M-HOLD (a), with (b) as the per-site fallback; Q-6M-PTE (a).

## Owner questions the plan is missing

**Background (plain words).** The final theorem says: every execution of this xv6 binary that the RISC-V weak memory
model (RVWMO, as written in riscv.cat) allows behaves like one of the executions our sequential-style kernel proof
already covers. The proof builds, for each weak execution, an equivalent run of a simpler machine, one step at a time
("the walk"). To build it we must decide in which order to replay the eight harts' steps. The order has to respect each
hart's program order and the order in which the locks were actually taken. Finding such an order from the weak
execution alone needs facts like "two harts never hold the same lock at once" — true for xv6, but it is one of the
things the theorem is proving, so assuming it would be circular.

**Q-6L-ORDER — how do we justify the replay order?**
*Where it sits.* REMAINING WORK row 6l; `Weak/SilOrd.lean:14-16`, `Weak/CertZ23.lean:341-355`.
*Terms.* *Replay order*: the sequence in which the walk appends the harts' steps. *Lock co*: the order in which the
successful lock operations (acquires that got the lock, releases) hit each lock word. *Gate*: a rule saying when a step
may be appended. *Realized prefix*: the part of the run already rebuilt on the simple machine (its memory facts are
known from the kernel proof).
*Tiny example.* Hart 1: `release(a); acquire(b)`. Hart 2: `release(b); acquire(a)`. RVWMO lets each hart's acquire
overtake its earlier release (a plain store after a fence orders nothing after it). If hart 1's acquire of `b` read the
value hart 2's release wrote, and hart 2's acquire of `a` read hart 1's release, no replay order exists that puts every
release before the acquire that read it AND keeps each hart in program order — unless we know each acquire was preceded
(in lock order) by that hart's own earlier acquire, i.e. mutual exclusion. The incremental design never needs that:
it appends an acquire only when the write it read is already the latest in the rebuilt run, and shows from RVWMO's own
rules (an `.aq` acquire comes before everything after it; a write comes before the read that saw it) that some hart can
always move.
*Options.* **(a) incremental gated order (recommended)** — an xv6 expert reads: "the theorem assumes nothing about xv6's
locking beyond what RVWMO and the image give"; FAITHFUL; 1.4–2.2k Lean, 12–24 h (+6m's pinned reads 0.5–1.5k, 4–12 h);
confidence M. **(b) name the order's existence** (rev 53 fallback) — reads: "assuming xv6's lock discipline makes a
replay order exist" — WEAKER (an unproved program fact in the trusted base); cost 0. **(c) assume acyclicity** —
STRONGER than RVWMO; rejected.

**Q-6J-PROTREG — where does "every lock word is zero when registered, then only acquires/releases write it" come from?**
*Where it sits.* Rows 6j/6k; `Weak/SilRegZero.lean`, `Weak/SilClose.lean:105-117`, `PROGRESS-W10N2p.md` "row 6k".
*Terms.* *Registration point*: the position in the memory log from which a lock word is treated as a lock. *Twin WP
package*: a premise saying the kernel is verified in a second ("twin") program logic — the capstone's plan is to have NO
such premise in the final header, deriving everything from the kernel proof's export instead. *Export conjunct*: one of
the nine facts the kernel proof already exports about memory (`Xv6/AccessDiscipline.lean:761-763`).
*Tiny example.* `pipealloc` calls `kalloc` (the page may still hold `kfree`'s 0x01 fill), then `initlock(&pi->lock)`
writes 0, then publishes the pipe. The replay needs "the lock word was 0 right before its first acquire"; the export
today says only that after some point the word's writes are lock-shaped, not what value it had at that point.
*Options.* **(A) interim, landed** — the zero is carried by the twin logic's registration ghost; reads: "the final
theorem would still assume a second program logic's proof of xv6" if it stayed — WEAKER if it remains in the header;
0 more lines. **(B) export route (recommended for the published theorem)** — a 10th append-only export conjunct
`dynLockWinZAt` (pipe-lock word is 0 at its window's opening; `kalloc.c`/`pipe.c` provenance), a static-locks census
(0 in `.bss`), the twin realization, glue; reads: "every lock fact comes from the kernel proof"; FAITHFUL; ≈ 0.2–0.5k
MachCSL (serial lane, tcb unchanged) + 0.8–1.5k Weak, 8–16 h. Recommendation: (B) scheduled in row 6j; (A) stays until
then.

*Informational (no menu).* Row 6i found that a quantified bundle may carry junk "fetch edges" (proof bookkeeping, not
RVWMO content); the kill is now proved on the bundle with those edges filtered to the real ones (`trimF`). Nothing in
the model text or the theorem's statement changes; FAITHFUL.
