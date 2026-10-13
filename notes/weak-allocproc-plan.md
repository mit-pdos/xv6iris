# allocproc on RVWMO: target theorem, gap analysis, roadmap (design advisor, 2026-10-09)

**Status: rev 46 (2026-10-13) = rev 45 + RESULTS (verified at the tip `../xv6iris-weak`: FabInd-S, W13 (W) part 1, W9a increment 1, W5d-G G1, W8 (f2-ctx) S3
wiring MERGED; W13 (K-cat) STOPPED on a computed riscv.cat counterexample; + W8 (f2-ctx) S4 DONE GREEN in w2, merge pending) + rulings [OWN.56] (Q-BATCH-3 = (1)),
[OWN.57] (Q-F2-PTE-WINDOW = (c) ghost freed-page set), [OWN.58] (weekly cap lifted) + NEW ITEMS (no new review since R41 — rev 45 applied it; tags [rev 46]): the W8
(pte-ghost) launch paragraph; F-X decided; the Stage 2 roadmap updated; SIX new owner questions in the owner format (Q-KCAT, Q-W9A, Q-F-RACY, Q-F-DISKTAIL, Q-PTEDISC,
Q-DYNLKDISC — each non-blocking under its provisional option) and ONE informed note (G1's E1′ = the carried-over R1 (a) reading; (H3′) now listed in §B(11); no menu).**
What changed: §C top "WAITS / LAUNCHABLE (rev 46)", "Rev 46 RESULTS", "F-X DECIDED", "W8 (pte-ghost)", "STAGE 2 ROADMAP (rev 46)"; §B(11) (H3′); §A(4) note; §C W8 (f3-rest),
W9a, W11, W14 notes; launch status (rev 46); §D: Q-F2-PTE-WINDOW and Q-BATCH-3 RULED, the six new questions FIRST.  Key facts: (K-cat)'s refined invariant is FALSE under
riscv.cat (ppo rule 2's `\ rsw` exemption + per-byte rf; `WeakRvwmoKillIOC.lean:150,166`) → rerouted provisionally through W11 (Q-KCAT (a), NEW S–M item (K-cat′));
W9a's R-3 is FALSE of Sail (interrupt dispatch before fetch `Step.lean:331-335`, taken branches, `ret`, per-clause dataflow) → provisional (A), increment 2 RUNNING; G1
kept the PINNED `gfexecConfIO` beside the NEW unpinned `gfexecConfZ` (`WeakRvwmoFab.lean:873,888`) — the collapse and `xv6ConfS`'s move to the Zifencei slot are G6
obligations; S4 exports THREE of six (`xv6AccessDisc := chainOkAt ∧ lockWordDiscAt ∧ cpuStaticAt`, w2 `Xv6/AccessDiscipline.lean:219`) — `pteDiscAt` and the pipe-lock
part of `lockWordDiscAt` are not derivable from the state interpretation (Q-PTEDISC, Q-DYNLKDISC → W8 (f3-rest) if ruled in); F-X: the X1/X5 "both greps EMPTY" is NO
LONGER an acceptance item.  History: rev 46 — RESULTS + [OWN.56]–[OWN.58] + (pte-ghost) + F-X + roadmap + 6 owner Qs.
**Rev 45 (2026-10-13) = rev 44 + review R41 (5 required changes, tags [R41.n]; NOT SATISFIED — all S plan text on the THIRD launch set and the two open
owner questions, no redesign, no shrinking; ONE alt: [R41.1-alt] the RUNNING RELAUNCH 5 paragraph is NOT edited — its corrected `.pte` docstring sentence is a launch
ADDENDUM after it; adopted [R41.s1]–[R41.s8]).**  What changed: **[R41.1]** Q-F2-PTE-WINDOW's bound CORRECTED — `freewalk` (`vm.c:265-280`) `kfree`s EVERY interior
page-table page BEFORE clearing the parent slot naming it (`freewalk(child); pagetable[i] = 0`, `kfree(pagetable)` LAST), so the window is every page-table page of the
dying table (≈ 5 for a small process), each from its `kfree`'s `release(&kmem.lock)` to the clear of its pointer — not "the ONE 4 KiB root page"; "exactly `R`'s 4 KiB"
is not a theorem (a new owner may write a V-only pointer-shaped word naming a RAM page); junk target `0x4040404040000` (`ptPtrTo`, `ChainDefs.lean:651-653`); (b″) closes
the interior windows too; `exec` swaps the word first (no window), `fork`'s failure path has the same window; (a) stays SOUND and recommended (§D, Rev 44 RESULTS, the
RELAUNCH 5 addendum).  **[R41.2]** W5d-G is a RE-AUDIT item: `Graph`/`Acyc`/`Topo`/`Conf`/`Supply`/`Hull`/`Lin`/`WeakEvInst`/`WeakEvLang` are in EVERY registered root's
import closure (`roots-weak.txt`: 13 roots, 493 modules) — each increment = full-cone rebuild + `audit.sh --weak --build`, baseline unchanged; G3's `Gdexec.gdFetch` is a
STRUCTURE change (`WeakRvwmoGraph.lean:669-671`; default-`[]` field + literal sweep, or a wrapper — worker's choice, re-count at launch [R41.s5]).  **[R41.3]** FabInd-S ∩
W5d-G G3 = `WeakRvwmoKillIO.lean` (`:423` vs `:86-90/:308`) — FabInd-S LANDS BEFORE G3 STARTS (a gate).  **[R41.4]** W13 (W)'s `gfDevWIo` discharge: the HART half
PROVED ([R40.s2]), the DISK half a NAMED hypothesis `usedElemGateOk` (the run-level virtio gate at the used-ELEMENT `DWriteDev`, `WeakEvInst.lean:519-525`/
`VirtioProg.lean:88-90`) discharged by W14; W13-wit exercises the hart half only [R41.s6].  **[R41.5]** Q-BATCH-3 rewritten in the owner format, with a third option
(W9a + the (W) chain first, W5d-G after) [R41.s7].  Also: cite drift [R41.s2]; (K-cat)'s per-arm closure argument + the image fence census [R41.s3]; the window's timing
[R41.s4]; RESULTS wording [R41.s8]; `IN FLIGHT` updated (RELAUNCH 5 RUNNING, w2).  No new owner question (R41: none missing; `usedElemGateOk` informed under the
non-blocking rule, no menu).  History: rev 45 — R41 (5 req., 1 alt; s1–s8 adopted).
**Rev 44 (2026-10-13) = rev 43 + review R40 (1 required change, tags [R40.n]; NOT SATISFIED — one S plan-text fix on W13 (R3′), APPLIED AT
LAUNCH as option (α): `gfDevWIo` KEPT as the NAMED premise, `gfDevAnc` NOT introduced; adopted [R40.s1]–[R40.s7]) + RESULTS (SIX MERGES 2026-10-13: **W13 (R3′)**
11:39, **W11 (iv)c** 11:41, **D35-fix** 11:47, **W8 (f2-ctx) (a′-r) + S3-a** 11:17 and **S3-b + S3-c0** 12:13, **W13 (K)** 12:30, **W13 (F-dep)** 12:50 — EVERY
Stage 2 first/second-batch item is IN THE TIP) + RULING **[OWN.55]** (the second batch APPROVED 11:16: W11 (iv)c launched w5, (K) launched w4 after (R3′)) + the
THIRD Stage 2 launch set + the W13 (K) open items placed + the W8 (f2-ctx) RELAUNCH 5 paragraph + ONE new owner question (Q-F2-PTE-WINDOW, provisionally (a)).**
What changed: **[R40.1]** (α) — `gfDevGmoOfRes : ioResidueGmo GF → gfDevWIo GF → gfDevGmo GF` (`Lin2.lean:1237`), `fconfTraceRealizeIO :1284` DROPS `gfDevGmo` only
(premises = `rvwmoMinusConsistent`, `grule14`, `ioResidueGmo`, `gdiskRead14`, `gfexecConfIO`, `gfDevWIo`, `length ≤ N` — VERIFIED in the tip), `devOrderOfPtraceExtIO
:1245`/`trDevOrderedOfPtraceIO :1253`/`fconfSupply' :1263` LEFT ALONE (they keep `gfDevGmo` as an explicit premise — the landed DEVIATION, harmless: `gfDevGmoOfRes`
discharges it at every call); the rev-43 motivation was WRONG — a `DRead` is NEVER a fabric member on this program (`WeakEvInst.lean:504-509`, `VirtioProg.lean:68-95`),
the only non-W/I/O `tq`-member is the `DFence` via the used-ELEMENT `DWriteDev`'s SKIP [R40.s6], so `gfDevWIo`/`gfDevAnc` had identical discharge obligations and
`gfDevAnc` would have broken `devOrderOfPtraceExtIO`'s proof (`ptraceRelIO :1079`'s `gisWIo` arm); hart side immediate [R40.s2].  **[R40.s1]** D35-fix launched at
once in w1 (the "(R3′) first" gate was not load-bearing: (R3′)'s files are in no registered root's import closure); **[R40.s3]–[R40.s5]** D35-fix's (5)/(2)/file
counts; **[R40.s7]** cite drift.  **RESULTS** (§C top "Rev 44 RESULTS", all cites re-read at the tip): (R3) = `(gisIo ∧ gisIo ∧ gpo) ∨ (gmem ∧ gmem ∧ gfBefore)`
(`GraphFabResidue.lean:112-124`, the [R39.s4] computed `DWriteDev`-member check `:322-361`); D35-fix `lbRcsc := lbAq || lbRl` (`WeakRvwmoGraph.lean:252`, `grcsc :256`,
`grelAcqGrcsc :272`, `gppo :283`; `grelAcqGmoC` DELETED, `CatFloor.lean:31`; 13 roots re-audited, baseline unchanged; 20 files in the grep); W11 (iv)c
`linCandDiskLat` PROVED (`RvwmoXv6ScaT.lean` §(6) `:806-`, `linCandDiskLatA :837`); W13 (K) `Weak/WeakRvwmoKillIO.lean` (708: `racyDIO :90`, `normalizeOfAcyclicIO :308`
supplies `gdiskRead14`, `fconfRealizeIO :345`, `cycleKillIO :396`, `t2linIO :454`, `hullRunIO :465`, `ioSegPinned :609` with check (i) PROVED for RVWMO⁻
`rsameNoReadEdge :655`; OPEN: check (ii) → W11 (i), check (i) FAILS on the cat chain's `rsameC` rfi arm → **W13 (K-cat)** (NEW S), the cat-side induction needs
`gfexecConfHull` without its UNUSED `gfexecConsistent` premise → **FabInd-S** (NEW S)); W13 (F-dep) (A1) (`AxDeps.lean`: `gtdepsWf :236`, `gtAdFull :265`, `dstepT :631`
MMIO arms, smoke test `ioGtCatT :1449`; roots' premise WEAKER, `roots-weak.txt:13-17`; OPEN: `gdexecQconfT` still requires `emDevfree`, `CatLinChain.lean:330` → the
new edges matter first at W13 (W)); W8 (f2-ctx) S3-b + S3-c0 ((A′): the `.pte` exemption read from MEMORY via `RsvKind.roots` + Sv39 `ptByteAt`, `ChainDefs.lean:670`;
`loadSrcOk` `Resources.lean:1273` etc. STATED, not wired; `Xv6/KernelRsv.lean:70-72`; **WEAKER caveat**: `freeproc`'s `kfree(root)` → `p->pagetable = 0` window
(`proc.c:162-163`; image `0x80001b2c`/`0x80001b30`) keeps a reallocated root page exempt → **Q-F2-PTE-WINDOW** (§D FIRST; provisionally (a) accept as a NAMED
weakening, the window stated in the export; (b″) a one-line kernel reorder behind a sizing pass)).  **THIRD LAUNCH SET** (§C top): recommended **W5d-G G1–G5 (G1
first) ∥ W9a ∥ W13 (W) [FabInd-S → (K-cat) → (W)]** beside W8 (f2-ctx) RELAUNCH 5; W13 (R) after W5d-G; W10 sizing pass first; W14 after (W) + W5d-G; owner's batch
nod needed (Q-BATCH-3).  New owner questions: **Q-F2-PTE-WINDOW** (provisional (a), non-blocking), **Q-BATCH-3** (approval).  History: rev 44 — R40 (1 req., 0 alt;
s1–s7 adopted) + six merges + [OWN.55] + third set + RELAUNCH 5.
**Rev 43 (2026-10-13) = rev 42 + review R39 (3 required changes, tags [R39.n]; NOT SATISFIED — all S plan text on the SECOND Stage 2
launch set: two file-list/disjointness corrections and one trusted-text satisfiability gap in W13 (R3′); no redesign, no shrinking; adopted
[R39.s1]–[R39.s5]) + LAUNCH RECORD (**W13 (F-dep) RELAUNCHED** under (A1) [OWN.52], w3, with [R39.2] handed over as a launch addendum — applied at
launch; **W8 (f2-ctx) RELAUNCH 3 RUNNING**, w2; running briefs unchanged).**  What changed: **[R39.1]** D35-fix's consumer list completed —
`AxGraphCat.grcscGrelAcq :250` (`grcsc → grelAcq`) becomes FALSE under `lbRcsc := lbAq || lbRl` (two `LStore true` in po are `grcsc`, not `grelAcq`)
→ DELETED, `gppoCat6Gppo :264`'s sixth arm becomes the direct `Or.inr (Or.inr (Or.inr h))`, header `:39` + port map `:85` rewritten; `CatLinWit.lean:42`
(`racyChk`, the Bool twin of `racy`, uses `grelAcqB`) widens to `grcscB` or `sbrfiAcyclic :124` stops matching `racyD`; `CatLinHull.lean:94-126`
re-elaborates (the grep `lbRcsc|grcsc|grelAcq` over `Weak/` = 14 files: rev 42's 12 + these two); `lblRenRcsc` MOVES from `CatLinHull.lean:94` to
`WeakRvwmoNorm.lean` beside `lblRenAq`/`lblRenRl :362-363` because `rowsRelGppo` (`WeakRvwmoAcyc.lean:512`) unfolds the arm and `Hull` imports
`Acyc`'s descendants; `Xchg.lean:896` gains `lblTswapRcsc` beside `lblTswapRl :743`; the SEMANTIC consequence is now stated — `racy :197` carries
`gppo` BY NAME, so route (i) WIDENS `racyD :200` and every acyclicity premise over it (`normalizeOfAcyclic :607`, `hullRun`, the kill, W5d-G G3/G4,
(K)'s `racyDIO`) inherits the wider arm with NO text change (empty on kernel graphs — no `W.rl`); `AxDeps.lean` has NO rule-7/RCsc/RCpc mention, so
"not touched" is unconditional.  **[R39.2]** D35-fix ∩ (F-dep) = {`WeakRvwmoAdm.lean`} (D35-fix re-cases `mp2PpoGmo :850`; (F-dep)'s sweep hits
`LDev kd ba bs` at `:696` — disjoint sites, whichever lands second rebases, S); `AxSpinSpike.lean` is a REBUILD on both sides (`cDw :658`/`:749`);
`Weak/CatLinChain.lean` joins (F-dep)'s files (`gdexecQconfTForget :331-338` uses only the `gisW` TARGET fact; after (0b) `forgetDeps :178` filters the
SOURCE too, so it takes `hartConfRowDepsWf`'s `lbIsR` conjunct, `WeakRvwmoConf.lean:837`; S; no other batch item touches the file) — APPLIED AT
LAUNCH as the (F-dep) addendum.  **[R39.3]** W13 (R3′) corrected: rev 42's "every disk-row event is a write, an I/O event or a read" was FALSE —
`DFence` (`VirtioProg.lean:28,91`) emits the row event `LFence true true true true` (`WeakEvInst.lean:511`) and a `DWriteDev` own-guard SKIP/ABORT is
SILENT (`:525-530`) while `pdevEv :604` is `true` at every disk `DWriteDev` node, so a fence label can enter `gfDev` (`WeakRvwmoFab.lean:857`;
`lbIsMem :127` = R ∨ W ∨ Io): `gfDevAncOfConf` has a counter-model and an unrestricted fabric arm `gfBefore → gmoLt` (`gmoLt :137` over `gxGmo`
members; `graphOfCand :276` filters `lbIsMem`) makes the TRUSTED `ioResidueGmo` UNSATISFIABLE there.  Fix: the arm = `gmem x ∧ gmem y ∧ gfBefore GF
x y` (EQUAL strength on every anchor, STRONGER than the silent ISA, EQUAL to MachCSL on events with a memory-order position); `gfDevGmoOfRes :
ioResidueGmo GF → gfDevAnc GF → gfDevGmo GF`; `ioResidueIo :114` → "an I/O endpoint, or both endpoints `gmem` members"; **`gfDevAnc` a NAMED premise
of `fconfTraceRealizeIO`**, discharged by W13 (W)/W14 (disk program shape + xv6's guard invariant, PROVED there; hart side: `pdevEv`-true hart steps
are MMIO); acceptance names the counter-model, re-proves `w13fIoResidueOk :236`, and [R39.s4] adds a COMPUTED satisfiability check on a bundle with
a `DWriteDev` member.  §D Q-L-R3 gains the refinement line (RULED option refined; non-blocking rule, owner informed).  Second launch set KEPT — **W13
(K) [(R3′) first] ∥ D35-fix ∥ W11 (iv)c** — order/disjointness corrected: (R3′) lands BEFORE D35-fix launches so one `audit.sh --weak` covers both
trusted-text changes [R39.s3]; D35-fix after (F-dep) (1) or coordinated on `WeakRvwmoAdm`.  Cites [R39.s1]: `gppoCatT :198`, `gisAnc :1141`,
`linCandScaTMinusA :790`, `forgetDeps :178`/`gtAd :187`; [R39.s2] `AxLitmus.lean:110/119`, `AxGraphCat.lean:142`; [R39.s5] herd's `[M]` wording.
New owner questions: NONE (R39: none missing).  History: rev 43 — R39 (3 req., 0 alt; s1–s5 adopted) + (F-dep) RELAUNCHED (A1) w3 + (f2-ctx)
RELAUNCH 3 RUNNING w2.
**Rev 42 (2026-10-13) = rev 41 + RESULTS (W12 + W12b DONE, MERGED 06:17; W13 (L) DONE, MERGED 05:56; W8 (f2-ctx) S0 + S2 MERGED 07:11,
the (a′-r) receipt work PARKED one error from green, RELAUNCH 3 RUNNING w2 10:19) + RULINGS [OWN.52]–[OWN.54] (Q-FDEP = (A1); Q-L-R3 = (a);
D35-rule7 = (a)) + the SECOND Stage 2 launch set (no review since R38 — rev 41 applied it, nothing re-applied; no shrinking).**  What changed:
**RESULTS** (§C top "Rev 42 RESULTS"): W12's `rvwmoCoreD` restatement (`WeakRvwmoAcyc.lean:207`; `normalizeOfAcyclic` `WeakRvwmoTopo.lean:607`
concluding `gppoCat6Gmo :617` [R21.2]) + `Weak/CatLin.lean` (541; `catADOfCatT :54`), `CatLinHull` (182; `hullCatAD :155` — NO `hren` injectivity
needed), `CatLinChain` (439; `gdexecQconfT :320`, `xv6RvwmoSafeModuloT :403` STATED, not registered), `CatLinWit` (136; `sbrfi` cat ✓, NOT RVWMO⁻),
W12b `CatFloor` (836) + `CatFloorWit` (118) as TWINS (deviation: `Floor`/`Cert3` untouched) with the premises `grelAcqGmoC` (D35) and `noPlainAqC`
(D36); W13 (L)'s anchored rank trace (`WeakRvwmoLin.lean` §6 `:1889-2358`), `WeakRvwmoLin2.lean` §8 (`ptraceExtIO :1083`, `gisAnc :1141`,
`gdiskRead14 :1153`, **`fconfTraceRealizeIO :1271`**, `w13fIoDevOrdered :1403`), `linNwAAnc` (`RvwmoXv6Sca.lean:208`, what W11 (iv)c uses),
`linCandScaTA :748`; deviations D1–D3; the residual premises `gfDevGmo :1219`/`gfDevWIo :1222` → [OWN.53].  **[OWN.52] Q-FDEP = (A1)**: W13 (F-dep)
RELAUNCHES under (A1) DIRECTLY — `gtAdFull`, `gppoCatT` over it, `catTAd` + `catADOfCatT` (now in W12's LANDED `Weak/CatLin.lean:54` and the spike
`CatOfMinusSpike.lean:37` — both (F-dep)'s to edit, W12 is DONE) by `gppo12` monotonicity, `AxScCat.scPpo :168`'s rule-12 case — INSIDE increment
(0), no (A2) interim (§A(3), §C top (F-dep) paragraph, §C (F-dep) (0e), §D).  **[OWN.53] Q-L-R3 = (a)**: (R3)'s fabric arm (`GraphFabResidue.lean:84`)
widened to ALL `gfDev` members — a trusted-surface TEXT change named in §A(6), done as **W13 (R3′)** (S), the FIRST increment of the W13 (K) worker;
`gfDevGmo` becomes a theorem; **`gfDevWIo` is NOT a consequence of (R3)** (it says what the members ARE, not how they are ordered) — (R3′) replaces it
by `gfDevAnc` (members ⊆ the (L) anchors) with its discharge lemma from `gfexecConfIO`'s membership clause (§C top, §D: the ruling's "discharges
`gfDevWIo`" reaches exactly this far).  **[OWN.54] D35-rule7 = (a)**: VERIFIED against herd's `riscv-defs.cat` — `let RCsc = (Acq|Rel|AcqRel) &
(EX|X)`, `r7 = [RCsc];po;[RCsc]`: EVERY aq/rl-annotated LR/SC/AMO is RCsc, so the tree's `lbRcsc := lbAq && lbRl` (`AxGraphCat.lean:143`) is NARROWER
and the tree's cat model is WEAKER than riscv.cat (sound) by the `[W.rl];po;[R.aq]`, `[W.rl];po;[W.rl]` and rl-only-RMW pairs; the fix is **D35-fix**
(M ≈ 0.3–0.6k, ≈ 14 files): `lbRcsc := lbAq || lbRl`, RVWMO⁻'s rule-7 arm (`WeakRvwmoGraph.lean:227-237`) widened IN STEP so `gppoCat6Gppo :257`/
`minusImpliesCat :274` keep their statements, `grelAcqGmoC` DROPPED from `CatFloor` (derived), the registered LB roots' premise `rvwmoCatConsistentT`
STRENGTHENS (text unchanged, meaning = riscv.cat; RE-AUDIT `audit.sh --weak --build`, baseline expected unchanged — the kernel has no `.rl` write,
so no kernel graph changes) — §A(3)/(6), §C top launch text, §D.  **SECOND LAUNCH SET** (§C top): recommended batch **W13 (K) [(R3′) first] ∥
D35-fix ∥ W11 (iv)c**, beside (f2-ctx) RELAUNCH 3 and the (F-dep) RELAUNCH; W5d-G G3/G4 wait for (K)'s `racyDIO` statement commit (file contention)
and G1/G2/G5 for (F-dep) increment (1) (the `LDev` sweep) — W5d-G is the next batch; W9a waits for (F-dep) (2)/(3) (the pin bridge); W10/W14/W13
(R)(W)/W8 (f3-rest) gated as before.  New owner questions: NONE (Q-L-R3 and D35-rule7 arrived RULED; recorded in §D in the owner format).  History:
rev 42 — RESULTS (W12, W12b, W13 (L); (f2-ctx) S0 + S2) + [OWN.52]–[OWN.54] + W13 (R3′) + D35-fix + the second launch set.
**Rev 41 (2026-10-13) = rev 40 + review R38 (6 required changes, tags [R38.n]; NOT SATISFIED — all on W13 (F-dep)'s GRAPH side, ONE
memory-model TEXT change (the tagged well-formedness `gtdepsWf`), no shrinking; adopted [R38.s1]–[R38.s5]) + RULINGS [OWN.48]–[OWN.51] + RESULTS (Stage 2
first batch LAUNCHED; **W13 (F-dep) STOPPED GREEN before any edit**) + Q-FDEP (OPEN, provisionally (A2), (A1) recommended).**  What changed: **[R38.1]** the
W13 (F-dep) worker's STOP finding (`~/dev/weak-orch/parked/PROGRESS-W13Fdep.md`) is CORRECT: §C W13 (F-dep) told the worker to emit D50 (b)'s edges
(`DTdata`/`DTctrl`/`DTtrans`/`DTr13` INTO I/O stores, every edge OUT OF an I/O load) that the PUBLISHED model's `gtdepsWf` (`Weak/AxDeps.lean:168-171`, a
conjunct of `rvwmoCatConsistentT :208-211`) cannot hold — it demands a `lbIsR` source and a `lbIsW` write-tag target, both `false` on `Lbl.LIo`
(`WeakAxiomatic.lean:174-182`, D47 (a)) — so once `rowDepsT ⊆ GT.gtDeps` enters `gdexecQconfT`/`xv6ConfS` the published premise is UNSATISFIABLE on
every row that prints a byte (hart 0's first `printk`: `acquire`'s RAM loads → the never-reset `dtCtl` → `DTctrl` into the THR store `sb a5,0(a3)`
`0x800009fa`) — VACUITY; FIXED by **option A**: (F-dep) gains item **(0)** (the first green increment after the payload sweep) — `gtdepsWf` admits
`lbIsR ∨ lbIsIoRd` sources and `lbIsW ∨ lbIsIoWr` write-tag targets (FAITHFUL to riscv.cat's `R`/`W` under appendix (c1)); `forgetDeps`/`gtAd` filter to
RAM endpoints so `catTAd`, `catTForgetAxioms`, W12's `catADOfCatT` and the registered LB roots keep their STATEMENTS (their premise WEAKENS — a strictly
stronger theorem, no re-registration); `AxSpinGate.gsrcT` filters to `lbIsR` sources; the Bool/SC tier in step; a computed-satisfiability smoke test;
§A(3)/(6)/(†) name the trusted-surface change; **[R38.2]** the UNTAGGED `dstep` (`WeakRvwmoConf.lean:497-499`) stays INERT — only `dstepT` gets the arms
(an untagged `LDev .wr` arm would push W13-wit's own addr edge `ld a5,0(a0)` → `sb zero,1(a5)` into `gfexecConfIO`'s `rowDeps ⊆ gdDeps`, `Fab.lean:857`,
whose `gdepsWf` is RAM-only — the non-vacuity witness would die); `WeakRvwmoConf` leaves (F-dep)'s owner list, `WeakPromise.lean:89` (`Wlabel.LDev`) and
`AxSpinGate.lean` join it; **[R38.3]** the `LDev` payload sweep is an ARITY change — ≈ 180 positional sites in 35 files (grep; R38 177/35, the worker
146/38), not "`Supply` 4, `FabInd` 2" — landed as increment (1) ALONE; (F-dep) re-sized **M–L ≈ 1k, three increments**; **[R38.4]** **Q-FDEP** (rule 12
from an I/O-load source): provisional **(A2)** — `gppoCatT` over the source-filtered `gtAd`, WEAKER than riscv.cat by exactly the
`[IoR];(addr|data);[W];rfi;[R]` instances (sound) — **(A1)** recommended (`gtAdFull` + two one-line monotonicity proofs); **[R38.5]** header, launch
state and the (F-dep)/W12 launch paragraphs rewritten (the batch is APPROVED [OWN.48], not "awaiting"); **[R38.6]** what the RUNNING W12 worker must
know (course note, §C W12 launch paragraph; its brief is not changed here).  **RULINGS 05:18 2026-10-13**: [OWN.48] Stage 2 first batch LAUNCHED — W12
(+W12b) w1 RUNNING, W13 (L) w4 RUNNING, W13 (F-dep) STOPPED GREEN before edits (RELAUNCH when rev 41 is signed off); [OWN.49] Q-F2-PIPEHOP-2 =
(a′-r) (inside W8 (f2-ctx) RELAUNCH 2, RUNNING w2); [OWN.50] F-C = (i); [OWN.51] weekly cap — no new launch at seven_day ≥ 90%, wind down green at
95%.  New owner questions: **Q-FDEP** (§D FIRST; provisionally (A2), (A1) recommended, awaiting ruling).  History: rev 41 — R38 (6 req., 0 alt; s1–s5
adopted) + [OWN.48]–[OWN.51] + RESULTS ((F-dep) STOPPED GREEN) + Q-FDEP.
**Rev 40 (2026-10-13) = rev 39 + review R36 (4 required changes, tags [R36.n]; NOT SATISFIED — all plan TEXT on the W8 (f2-ctx)
lane, no memory-model change, no shrinking; adopted [R36.s1]–[R36.s6]) + RESULTS (**M2 CLOSE DONE**; W8 (f2-ctx) S1′ + S2-pre MERGED, worker
STOPPED GREEN) + RELAUNCH 2 (W8 (f2-ctx)) + Q-F2-PIPEHOP-2 (OPEN, provisionally (a″+shape)).**  What changed: **[R36.1]** rev 39's "W8 (f2-ctx)
continuation RUNNING" was STALE — the worker STOPPED GREEN 2026-10-13 after two increments that are IN THE TIP (`diff -rq` w2 ↔ tip empty):
**S1′** the time-indexed hop registry (`ChainDefs.lean:266 isLk : PAddr → Nat → Prop`, checked at the ACQUIRE position `hopChain :177-183` —
deviation D2) with the DYNAMIC registry = the lock's NAME word (`Reserved.lean:236 nameLockAt` — deviation D1 = (a″)) and the hop/retime
requests inside the AMO's/release's step (`WpAtomic.lean:608-669` — deviation D3); **S2-pre** `started` reserved `.pub 0`
(`Xv6/KernelRsv.lean:52,57`), the gate issued INSIDE the publication read (`ReadAUr.lean:36`, `memModel_rdIssue :121`), `writeAUT`'s RESERVED
arm over `rsvStoreOk` (`WpStoreOrd.lean:45`), `StartedInv` over the half window (deviation D4); findings F-A–F-D; the S2b WIP parked at
`~/dev/weak-orch/parked/w8f2-s2b-wip/` (9 files) — recorded (§C top, RESULTS (rev 40)) with **RELAUNCH 2** deciding F-B (adopted, guard
`j ≠ w`) and F-C (option (i) as rows BEFORE wiring, (ii) the fallback); **[R36.2]** the merged registry's ONE constant is WRONG:
`pipeLockNameStr` (`Xv6/KernelRsv.lean:104`: `KA.«pipealloc» + 0x48 + 0x3000 + 222 = 0x80007730 = KernelStr.«digits»`) names
`"0123456789abcdef"`, not `"pipe"` — the image's `addi a1,a1,-146 # 800075c0` (`KernelImage.lean:13328-13329`) gives `KS.«pipe» = 0x800075c0`
(`:18120`, `:18837`); NO pipe lock is a hop byte until it is fixed (no unsoundness — a registry only RESTRICTS chains) — RELAUNCH 2's FIRST
increment S0 (`pipeLockNameStr := KS.«pipe»` + a `rfl` lemma); **[R36.3]** the MERGED D1/D2 (name-word window, indexed at the acquire) DEPART
from the RULED (a′) text [OWN.46] (`f->pipe` slot window, indexed at the release, client `dynLk`) — recorded as a DEVIATION, FAITHFUL, adopted
PROVISIONALLY as **(a″+shape)** under the non-blocking rule pending **Q-F2-PIPEHOP-2** (§D FIRST): the pure-SHAPE `syncHop :171` admits
`kfree`'s junk byte `1` on the lock word (`memset` low-to-high, `kalloc.c:55`, `string.c:8-10`; `lk->name` still reads `"pipe"`) as an
"acquire" over a GENUINE release, and the `initlock` zero over `kalloc`'s junk `5` as a "release from held" — fixed by WORD-SIZED hop entries
(`wordEntAt`, S ≈ 0.1k) and a WINDOWED `lockRegionOk` for dynamic locks (the whole-history `AccessDiscipline.lean:104` would be FALSE at every
`kfree` of a pipe); the honest limit (a user-forged word alternation + `&"pipe"`) is closed by (a′)'s kernel-only slot history, not by shape —
rev 39's "W11's release-site pin makes a claimed hop real" is WRONG for an existential export and is rewritten; **[R36.4]** F-C's option (i)
is adopted with its rows (C′)/(D′)/(E) stated as Lean invariants BEFORE wiring, sized against the REAL client surface (27 `Xv6/` files
mention `reference γ`/`unitStamp`/`maxStamp`/`slotdHalf`/`slotpHalf`, 60 mentions of the two stamp functions — not ≈ 15), option (ii) sized
as the fallback; (f2-ctx) total ≈ 9–13.5k.  Suggestions: [R36.s1] M2 CLOSE's cosmetic cites (moot — DONE; `baseline-weak.json:3`'s module
list already names both modules), [R36.s2] §B(11)'s stale "premise of … M1, M2 and §A's statement" clause, [R36.s3] the W12 → `AxDeps`
rebuild-only edge + G1's `Fab` site by name (`Gfexec :793`), [R36.s4] `ChainDefs.lean:17-23`'s docstring (RELAUNCH 2 S0), [R36.s5] the
two-register note for `roots-weak.txt:23-24`'s gloss (housekeeping, next `tools/` touch), [R36.s6] the worker writes the PARKED path in
PROGRESS.  **RESULTS: M2 CLOSE DONE** — `Weak.srvwmoXv6M2` REGISTERED (`roots-weak.txt:25`, `baseline-weak.json:163` — EXACTLY M1's entry;
headers `PfRunUnpinned.lean:55` "M2 CLOSED: registered", `SailCycleOrderCycle.lean:177`, `MachOfPf.lean:73-77`/`SrvwmoXv6Adequacy.lean:18-21`
"proved: `sailCycleOrder_holds`"; `audit.sh:49,56` unchanged, the optional core NOT registered) — **both Stage 1 milestones M1 + M2 DONE
(INTERNAL, NOT published [OWN.2]); Stage 1b CLOSED.**  Launch state: W8 (f2-ctx) RELAUNCH 2 LAUNCHABLE (serial MachCSL lane; S0 first);
Stage 2 FIRST LAUNCH SET unchanged — **W12 (+W12b) ∥ W13 (F-dep) ∥ W13 (L)**, [R36.s3]'s edge named — awaiting the owner's batch approval [rev 41: APPROVED and LAUNCHED [OWN.48]].
New owner questions: **Q-F2-PIPEHOP-2** (§D FIRST; provisionally (a″+shape), awaiting ruling; (a′-r) the named S4 follow-up).  History: rev 40
— R36 (4 req., 0 alt; s1–s6 adopted) + RESULTS (M2 CLOSE DONE; (f2-ctx) S1′ + S2-pre MERGED) + RELAUNCH 2 + Q-F2-PIPEHOP-2.
**Rev 39 (2026-10-13) = rev 38 + review R35 (2 required changes, tags [R35.n]; NOT SATISFIED — both S text in Q-F2-PIPEHOP (a) /
Q-F2-BOOTGATE (a) and the W8 (f2-ctx) RELAUNCH paragraph that executes them, no memory-model change; APPLIED AT LAUNCH by the coordinator in
the continuation brief `../weak-orch/allocproc_W8f2_cont_prompt.txt` (w2, RUNNING — the brief is not changed here), recorded; adopted
[R35.s1]–[R35.s6]) + RULINGS [OWN.46][OWN.47] + RESULTS (W-SCO (A) DONE) + the M2 CLOSE launch paragraph + the first Stage 2 launch set.**
What changed: **[R35.1]** Q-F2-PIPEHOP (a) was not implementable as written — "the lock of a pipe reachable from `ftable` as of `t`,
registered at the mint store" is FALSE at the mint store (`initlock` precedes `(*f0)->pipe = pi`, `SpecPipealloc.lean:10-11`) and at the
last `pipeclose` (`fileclose` unlinks first, `SpecFileclose.lean:4-12`), `rsvName` IS the static list (`rsvExact`, `Resources.lean:1196`), and
the merged hop registry `ChainEnv.isLk` is UN-TIMED and only grows (`ChainDefs.lean:220-233`) while a pipe lock DIES — replaced by **(a′) a
TIME-INDEXED hop registry `isLk b r`** (`ChainDefs`/`ChainCert`/`Resources` amended, MachCSL parametrised by a client `dynLk` with a
monotonicity obligation, `Xv6/` supplies `pipeLockAt` from the `f->pipe` slot history + the reclaim entry, W11's release-site pin named as the
guard against shape-only hops; ≈ +0.2–0.3k) — **RULED [OWN.46]**; **[R35.2]** Q-F2-BOOTGATE (a)'s "`started = 1` through the reserved-store
rule" cannot discharge a one-shot word (`rsvWordOk`, `RsvCell.lean:33-37`, is history-free; `.pub`'s `oneShotOk`, `Reserved.lean:158-166`,
needs the window's history) — a HISTORY-AWARE variant over `rsvStoreOk` (`WpAtomic.lean:432`) is added, and reserving `started` moves
`StartedInv`'s `wordCell` and the boot carve (`BootCarveProc.lean:802`, `BootShared.lean:223`, `BootRsv`, `KernelRsv.lean:75`; ≈ +0.3–0.5k,
`RsvCell` + five `Xv6/` files in the Files list) — **RULED [OWN.47]**.  Suggestions: [R35.s1] cites (`pub :123`, `CtxId :432-441`), [R35.s2]
the wiring list is "at least" the 11 files of the grep, [R35.s3] the parked WIP path is authoritative, [R35.s4] the `lint.sh` drift finding is
CLOSED by `MachCSL.lean:261`, [R35.s5] there is no `coh` receipt ghost — gate and chain obligations are issued INSIDE the load's atomic step,
[R35.s6] the last-`pipeclose` example.  **RESULTS: W-SCO (A) DONE and MERGED** (w4; §C top): commit 1 restated `sailCycleOrder` under
`wbootFacts σ0` (`Weak/SrvwmoXv6Adequacy.lean:139`) with `Rboot` (`SailCycleOrderK.lean:238`) pinning `pma_regions = bootPMA` AND
`htif_tohost_base = none` ⇒ **M1/M2 NO LONGER VACUOUS**; 122/122 `execute` clauses + `fence.i` + both fetch arms (16 files
`Weak/SailCycleOrder*.lean`, ≈ 4.1k lines); **`sailCycleOrder_holds` is a THEOREM** (`Weak/SailCycleOrderCycle.lean:137`, from
`cycleOkBoot_holds :128`) — `sailCycleOrder` LEAVES the trusted base (§A(6)), §B(11)'s premise list and the §A statement, remaining only as a
proved lemma; corollaries `srvwmoXv6M1 :148`/`srvwmoXv6M2 :179` = the cores without `hsco`; **`Weak.srvwmoXv6M1` REGISTERED**
(`roots-weak.txt:22`, `baseline-weak.json:148` — entry EXACTLY the core's; `audit.sh:49,56` list `Weak.SailCycleOrderCycle`; 555 `bv_decide`
certificates counted); `srvwmoXv6M2` STATED, its registration = **M2 CLOSE — LAUNCHABLE NOW (§C top) [DONE rev 40]**; every "vacuous until W-SCO commit 1"
annotation is resolved.  **W8 (f2-ctx) continuation RUNNING** (w2) [rev 40: STOPPED GREEN 2026-10-13; S1′ + S2-pre MERGED (tip); RELAUNCH 2, §C top [R36.1]].  **Stage 2**: the FIRST LAUNCH SET (§C top) — recommended batch **W12
(+W12b, same worker) ∥ W13 (F-dep) ∥ W13 (L)**; W5d-G G1–G5 + W13 (K) second (file contention, not deps).  New owner questions: NONE (R35:
none missing; both corrected options FAITHFUL).  History: rev 39 — R35 (2 req., 0 alt, applied at launch; s1–s6 adopted) + [OWN.46][OWN.47]
+ RESULTS (W-SCO (A) DONE; `Weak.srvwmoXv6M1` registered) + M2 CLOSE paragraph + Stage 2 launch set.
**Rev 38 (2026-10-12) = rev 37 + review R34 (3 required changes, tags [R34.n]; NOT SATISFIED — all S text in the W8 (f2-ctx)
launch paragraph, no design or memory-model change; APPLIED AT LAUNCH by the coordinator as the ADDENDUM of
`../weak-orch/allocproc_W8f2_prompt.txt`, recorded here; adopted [R34.s1]–[R34.s6]) + RESULTS (W8 (f2-ctx) S1 MERGED; the worker STOPPED
GREEN with three findings) + Q-F2-PIPEHOP / Q-F2-BOOTGATE adopted PROVISIONALLY (a).**  What changed: **[R34.1]** deliverable (5) of the
launch paragraph enumerates the six conjuncts of `xv6AccessDisc` and lands FOUR OF SIX (`chainOkAt ∧ lockWordDiscAt ∧ pteDiscAt ∧
cpuStaticAt`); `cpuProcDiscAt` and `utextDiscAt` are DEFERRED to the named follow-up **W8 (f3-rest)** (the coordinator's name for the
review's "W8-γ"; the header/`roots.txt:20` comment say "four of six"; §C W8's acceptance sentence and skeleton say so); **[R34.2]** the
brief's BINDING `W8-Rctx.md` §1–§6 carries the carve-out — §0.5/§4/§6/§7's user-table verdict "CHAINED as owned stores" is SUPERSEDED by
[OWN.39] (PTE-KEY for BOTH tables; option (b) UNFAITHFUL), §7 Q-R1 by [OWN.38], §6's lane order by [OWN.41], its cites are rev-29/w3
numbers; **[R34.3]** the per-author vector's ghost plumbing is in the Files list — route (A) (`CtxId` grows `chain : CPU → GName` +
`gate : GName`, `Resources.lean:432-441`, no functor change) LANDED in S1; route (B) (`MachFixedGS`/`bootFixedGS`/`xv6GF` +
`Weak/WeakAdequacy.lean:99`) was the fallback; 13 MachCSL files; NO shared file with W-SCO (A) in either route.  Suggestions: [R34.s1]
stale cites (`WpLock.lean:1255,1461`, `ctxDeposit :156`, `PipeBirth :307`, `cycleKillOfF :668`; `W8-Rctx.md`'s MachCSL cites relocate by
name), [R34.s2] 37 `wp_m_*` carry `[CurCtx]`+`ctxTok` (34 gained), [R34.s3] launch authority named ([OWN.37] + [OWN.41], no batch approval),
[R34.s4] `vtest-lean/Vtest/`, [R34.s5] the 31 consumers = LLB-naming + hook-surface greps (tip: 22 / 16, union 35), [R34.s6] the per-row
CLOSED table in `PROGRESS-W8f2.md` from increment 1 (the worker kept it).  **RESULTS: W8 (f2-ctx) S1 MERGED** (`MachCSL/ChainDefs.lean`,
`MachCSL/ChainCert.lean` NEW — the sync-chain layer over byte histories, the `started` boot hop `pubCover`, the gate, author-reach
certificates, `memModel_chainRetime/chainHop/certIssue/gateIssue`; `chainName` era ghost in `rsvModelAt`; `RsvKind.pub`; `CtxId` grows
`chain`/`gate` (unwired); `MachCSL.lean:261` imports `ChainCert`; `tcb/expected.json` gains `ChainDefs` on 4 roots; every registered root
unchanged in statement); the worker STOPPED GREEN at S2a (`~/dev/weak-orch/parked/PROGRESS-W8f2.md`, WIP `parked/w8f2-s2-wip/`) with three
findings: (1) key-less `readAU`/`readAUr` racy loads need chain obligations too (size only); (2) **Q-F2-PIPEHOP** — `chainOkAt` itself
needs pipe locks as hop words; (3) **Q-F2-BOOTGATE** — the boot hop does not compose with lock hops σ-checkably.  Both in §D (FIRST) in
the owner format, **provisionally (a), awaiting ruling** (non-blocking rule).  W8 (f2-ctx) re-sized 6.5–9.5k + 1–1.5k; a complete
RELAUNCH paragraph (§C top) covers the continuation (lock layer, `CtxBox`, the `started` gate, load obligations, X1–X5 with the 31
consumers, the export, the root).  W-SCO (A) RUNNING in w4, brief unchanged.  New owner questions: Q-F2-PIPEHOP, Q-F2-BOOTGATE (R34 itself
found none missing).  History: rev 38 — R34 (3 req., 0 alt, applied at launch; s1–s6 adopted) + RESULTS (W8 (f2-ctx) S1) + Q-F2-PIPEHOP/
Q-F2-BOOTGATE provisional (a) + RELAUNCH W8 (f2-ctx) + W8 (f3-rest) named.
**Rev 37 (2026-10-12) = rev 36 + review R33 (1 required change, tag [R33.1]; NOT SATISFIED — S: a second register the
`cycleOkBoot` filter must pin; adopted [R33.s2]–[R33.s5]; [R33.s1] was the coordinator's prompt, regenerated at launch) + RESULTS (W13 (I)
DONE, W8-β′ DONE, W-RSV DONE) + [OWN.45] (Q-SCO-PMA RULED (α)).**  What changed: **[R33.1] `cycleOkBoot` with `Rboot` pinning ONLY
`pma_regions` is still FALSE**: after `pmaCheck` passes, `checked_mem_read` (`model/Lean_RV64D/LeanRV64D/Mem.lean:437-446`) routes the
ifetch through `within_mmio_readable` (`Platform.lean:718-728`), whose HTIF arm `within_htif_writable :243-249` READS the register
`htif_tohost_base` (`Option (BitVec 64)`, `Defs.lean:1561`); under an arbitrary `some base` in RAM the fetch is answered by `htif_load`
from the `htif_tohost` register with NO `.memRead` node, so any word (e.g. `0x12000073`) is announced at phase `.instr` and `good`'s
`.instrAnnounce` arm (`SailCycleOrderK.lean:154-156`) fails — [R32.1]'s shape one register further along the same path.  Fix: `Rboot` pins
BOTH `pma_regions = bootPMA` AND `htif_tohost_base = none` (both in `bootPost`, `BootInitModel.lean:39,41`; `hwVal` `HwConfig.lean:48-57`
lists both as frozen at reset; `enable_htif` has no caller), the `regWrite` arm excludes both, the run invariant carries both, "the ONE
place precise about a value" → TWO (the PMA lookup and `within_mmio_readable`) — **APPLIED AT LAUNCH: W-SCO (A) launched 2026-10-12 in w4
with [R33.1] + [R33.s2] in its brief (`../weak-orch/allocproc_WSCO_A_prompt.txt`), RUNNING; its §C-top brief carries the change tagged**.
The run-level restatement stays TRUE (`bootFin_bootProg` → `bootPost` for every landing file); M1/M2's statements, names and the
`baseline-weak.json` entry unchanged.  **[OWN.45] Q-SCO-PMA RULED (α)** (16:56): the fact is stated under `wbootFacts σ0`.  Adopted:
[R33.s2] base lemma `bootFin_bootProg`/`resetRegsRun_of_run` (not `bootRun_bootLand`), [R33.s3] `Rboot` by `match` (no `cast`), [R33.s4]
cites (`tick_clock` is `model/…/Platform.lean:549`; `writeReg pma_regions` also at `model/…/LeanRV64D.lean:265` `sail_model_init`;
`nodeStep :273`'s `regRead` case; `good`'s arms `:145-150`/`:154-156`/`:157`), [R33.s5] `barrier_kind_of_num`'s `Barrier_RISCV_i` fallback
(`PhysMemInterface.lean:262-275`) — `FENCE`'s per-clause lemma cases on the kind.  **RESULTS (all MERGED in the tip)**: **W13 (I) DONE**
(both halves: `gfexecConfIO` with contact membership `gisIo ∨ dvi ≠ dvo ∨ tq k`, the interim `.PDisk` clause GONE, `hblkQ` folding
GENERALIZED, `GraphFabResidue.gfIoDevOfConf`, `GraphFetchSpike.emZifencei`; deviations: `hemitf`/`hartConff` gain `tq`,
`gfexecConfOfQconf`/`cycleKillOfF` take `∀ i, devQuiet (boot i)`; §C top/§C W13 (I)); **W8-β′ DONE** (157 static locks + `cpus[h]`
reserved; `Xv6/AccessDiscipline.lean`, `SystemAdequacyDisc.lean`, `LinkDiscAdequacy.lean`, root `Xv6.xv6DiscAdequacy_closed` REGISTERED
`roots.txt:20`; deviations: four existing roots' `tcb/expected.json` module sets GROW (Reserved/WordHistDefs), `powerInterp_accessDiscβ`
takes `rsvStatic = KernelRsv.static`; §C W8); **W-RSV DONE** (`hartStep` `.pure` arm `σ.dropResv cpu` `Lang.lean:543`; `wpLoop_restart(B/C/O)`
`Wp.lean:2005-2108`; 37 `wp_m_*` carry `[CurCtx]` + `ctxTok` (34 gained [R34.s2]); deviations: S-mode rules unchanged (fragment from `transTok`'s `ctxTok`),
`resvOut :2068` side condition on `sT_*`/`wait_wfi`/`ucStep`, the boundary does NOT clear `hr.acq` [R12.s2], `SPIN` gains `∃ r,
resvFragAny cpu r` (`SpecSpin.lean:40`); 20 MachCSL + 11 `Xv6/` + 2 `Weak/` + 1 `vtest-lean/Vtest/` [R34.s4] files; §C W-RSV).  **W8 (f2-ctx) is LAUNCHABLE
NOW** (deps W8-β′ + W-RSV MERGED; §C top launch paragraph, rebase surface against the tip).  Serial lane: W8-β′ ✓ → W-RSV ✓ → **W8
(f2-ctx)**.  M2 CLOSE now waits ONLY for W-SCO (A).  No new owner question (R33: none missing).  History: rev 37 — R33 (1 req., 0 alt,
applied at launch; s2–s5 adopted) + RESULTS (W13 (I), W8-β′, W-RSV) + [OWN.45]; W8 (f2-ctx) launch paragraph.
**Rev 36 (2026-10-12) = rev 35 + review R32 (4 required changes, tags [R32.n]; NOT SATISFIED — [R32.1] a soundness/vacuity
defect in the named premise, [R32.2]–[R32.4] S text/records; adopted [R32.s1]–[R32.s4], [R32.s6]–[R32.s8]; [R32.s5] is the coordinator's
prompt, not plan text).**  What changed: **[R32.1] `sailCycleOrder` (`Weak/SrvwmoXv6Adequacy.lean:126-137`) is FALSE as stated** — closed
over EVERY `σ0 : WGState` with no boot hypothesis, so `epsInit σ0` seats a hart on an ARBITRARY register file; with `pma_regions` marking an
I/O region executable, an instruction FETCH from a device address is labelled `LDev` by `pnodeStep` (`WeakEvInst.lean:315-321` tests
`devAddr` BEFORE `akIfetch`), leaves no `LIFetch`, and the SFENCE.VMA-announce clause fails (refuting run: the word `0x12000073` =
`sfence.vma` fetched from a PLIC enable register).  Hence `hsco` is REFUTABLE and **`srvwmoXv6M1Core` (registered) and `srvwmoXv6M2Core`
were VACUOUS until W-SCO (A)'s first commit landed (LANDED rev 39 — non-vacuous)**; `cycleOkAll`/`cycleOkK` (`SailCycleOrderK.lean:229-232`) were FALSE as defined (`good`'s
device arm is "any answer", `:146-150`) — the rev-35 brief asked for a proof of a false proposition.  TRUE on THIS platform because the
boot PMA table `bootPMA` (`MachCSL/Platform.lean:199-250`: both I/O regions `executable := false`, RAM `executable := true`; no match ⇒
`pmaCheck` faults, `Mem.lean:265-268`; `override_PMA` never touches `executable`, `Pma.lean:313-319`) is pinned by `wbootFacts σ0`
(`WeakLang.lean:482-490` → `bootPost … pma_regions = pma`, `BootInitModel.lean:41`), which M1 AND M2 already assume and the model never
writes (`writeReg pma_regions` only at `ArchReset.lean:125` and `model/…/LeanRV64D.lean:265` `sail_model_init`, both outside the cycle [R33.s4]).  **Q-SCO-PMA adopted PROVISIONALLY as (α), awaiting ruling (§D, FIRST
item)**: `sailCycleOrder` restated under `wbootFacts σ0` (the shape `sailCycleOrderK :92-93` has), `good` gains a register filter,
`cycleOkBoot` replaces `cycleOkAll` as W-SCO (A)'s deliverable (1) — its FIRST commit; names and the `baseline-weak.json` entry unchanged
(registration by NAME [R21.4]); "FAITHFUL (true of the model by inspection)" → "TRUE of the model FROM THIS PLATFORM'S RESET; FALSE over
arbitrary register files" at §A(6), §B(11), Q-FIARM; every "M1 DONE"/"M2 CORE DONE" site says "vacuous until W-SCO (A)'s first commit" (all RESOLVED at rev 39).
**[R32.2]** `Weak/PfRunUnpinned.lean` and `Weak/SailCycleOrderK.lean` are MERGED in the tip and IMPORTED (`Weak.lean:635-636`; the tip's
`PfRunUnpinned.lean` is byte-identical to w5's), neither registered — every "merge pending"/"once w5 merges"/"not imported"/"coordinator's
step" clause fixed.  **[R32.3]** the W13 (I) rename `emFetchImg → emZifencei` collides with the merged 4-ary `Weak.emZifencei`
(`GraphFetchSpike.lean:312`) — handed to the W13 (I) bundle worker as a LAUNCH ADDENDUM (rename the spike's def to
`GraphFetchSpike.emZifencei`, or defer to G1; worker's choice, said in the header); **the W13 (I) bundle half is LAUNCHED** (w3; its brief
NOT rewritten).  **[R32.4]** §C W-SCO (A)'s brief names the WHOLE cycle decomposition (`tick_clock`, `run_hart_waiting`, the `ExecuteAs`
redirect, hooks, prelude/epilogue) and is REWRITTEN to be launchable (premise restatement first, 122 execute clauses).  Suggestions:
[R32.s1] stale cites refreshed at the live sites (`HypsC.fi :703-715`, `machRunOfPfRun :2928`, `noWriteOfPristine :2982`, `fetchIsImage
:3009`, `cutOfPristine :3028`, `sailCycleOrder :126`, `fiOfSco :176`, `m1Hyps :216-227`, `fiArmLastCyc :148`; rev-31–34 history records keep
their pre-merge numbers); [R32.s2] the "demotes" gloss is `SrvwmoXv6Adequacy.lean:18`/`:80`'s, not `roots-weak.txt:20`'s; [R32.s3]
`blockTouches`' carrier is a third per-item function `tch`; [R32.s4] W-SCO (A) states `srvwmoXv6M2` too; [R32.s6]/[R32.s7] cites; [R32.s8]
`PROGRESS-WSCO.md`'s "ONE closed proposition" section is rewritten first.  W8-β′'s brief UNCHANGED (running).  History: rev 36 — R32
(4 req., 0 alt; s1–s4, s6–s8 adopted; s5 to the coordinator's prompt) + Q-SCO-PMA (provisionally (α)) + W13 (I) bundle half LAUNCHED with
[R32.3] as addendum.
**Rev 35 (2026-10-12) = rev 34 + review R31 (1 required change, tag [R31.1]) + results + [OWN.42][OWN.43].**  What changed:
**[R31.1] APPLIED, not open — by the coordinator's choice of route (i) in W5d's brief, DELIVERED in code**: the M2 instance of
`fcutE` carries the `fiArm` STATE as a second FREE function `fiOf : Nat → Nat → Bool` of `srvwmoXv6M2Premises` beside `itvOf`
(`PfRunUnpinned.fiStep :68`/`fiFold :75`/`itvStep :100`/`fcutEM2 :113`, `../xv6iris-weak-w5/Weak/PfRunUnpinned.lean`); the
replay invariant `itv = itvOf ∧ fiArm = fiOf` holds BY CONSTRUCTION (no Sail fact); `ls` is no longer the carrier of
`emFenceI`'s criterion on the Exec side; **[R31.s1]** (the instance closes over the execution: `fcutEM2 stamp E itvOf fiOf`
reads `E.exTr[k]?`), **[R31.s2]** (`simStep`/`simRun`, `g1NoRunT`/`g2RunT` in the threading commit — delivered as generic
twins), **[R31.s3]** (boot values `∀ i, itvOf 0 i = 0 ∧ fiOf 0 i = false` in `srvwmoXv6M2Premises :594-604`) APPLIED;
[R31.s4]/[R31.s5] need no edit (the generic twins `execProgOk'SC`/`pfRunSTC`/`HypsC` ARE the generic-`fcutE` forms;
`m2Hyps.fi :632` is `fiOfSco` from `sailCycleOrder`) (§B(4)(iii), §C W5d).  **RESULTS**: **W5 CLOSE-OUT DONE → M1 DONE** (VACUOUS until
W-SCO (A)'s first commit landed [R32.1] — LANDED rev 39)
(`Weak.srvwmoXv6M1Core` registered: `tools/ci/roots-weak.txt:20`, `baseline-weak.json`'s entry EXACTLY [R28.1]'s, `audit.sh:47,54`;
INTERNAL milestone, NOT published [OWN.2]; **[R29.s3] CLOSED** — the module list is written ONCE at `audit.sh:47`, the comment
sites say "`Weak.AxSpinT2b,...,Weak.AxSpinT2q4,Weak.SrvwmoXv6Adequacy` (the list in `tools/ci/audit.sh`)", `Audit.lean:93-94`);
**W5d M2 CORE DONE** (VACUOUS until W-SCO (A)'s first commit landed [R32.1] — LANDED rev 39; MERGED in the tip, `Weak.lean:636` [R32.2]) in workspace
`../xv6iris-weak-w5` (`Weak/PfRunUnpinned.lean` 780 lines: `srvwmoXv6M2Premises :594`,
`srvwmoXv6M2PfRun :609`, **`srvwmoXv6M2Core :652`**, `srvwmoXv6M2Satisfiable :758`; the threading landed as GENERIC TWINS
`execProgOk'SC`/`execProgOk'STC`/`pfRunSTC`/`contRC`/`MachOfPf.HypsC` with the plan's names as the TRIVIAL instances — M1's text
UNCHANGED; `fok := fokTriv`; M2Core also returns the replay invariant; NOT registered — M2 closes after W-RSV and [R32.1]; MERGED
[R32.2]); **W-SCO shape (0) + GENERIC half DONE and MERGED** (`Hyps.fi` widened `MachOfPf.lean:677`,
`noWriteOfPristine :2982`, `fetchIsImage :3009` [R32.s1]; `Weak/SailCycleOrderK.lean` 631 lines, not registered, imported `Weak.lean:635` [R32.2]:
`sailCycleOrderK :92`, the SailM residual invariant `good :139` — **[R29.s2] CLOSED** —, `cycleOkK :229`/`cycleOkAll :232`,
`sailCycleOrderKOfCycle :536`, **`sailCycleOrderOfCycle :470 : cycleOkAll → sailCycleOrder`**, `srvwmoXv6M1OfK :593`); its
per-word half AS BRIEFED is BLOCKED (a 4-byte instruction at `pc ≡ 2 (mod 4)` is fetched as TWO separately translated halfwords,
`Fetch.lean:217-226,252-280` — the [R21.s2] word set does not contain the words the cycle announces; `PROGRESS-WSCO.md`) →
**[OWN.42] RULED (A): prove `cycleOkAll` for EVERY instruction** (one lemma per `execute` clause — 122 `def execute_*` in
`InstsEnd.lean` —, `fence.i`/SFENCE.VMA by hand, the instruction-independent cycle), discharging `sailCycleOrder` ITSELF from M1,
M2 and §A — kernel AND user text; ≈ 1.5–3k lines, L (spike `PROGRESS-WSCO-spike.lean.txt`, not merged [OWN.10]); §C W-SCO is a
RELAUNCH brief on route (A); §A, §B(11), Q-FIARM now say "a THEOREM after W-SCO, for all text"; **W13 (I) realization half DONE
and MERGED** (`mstep.MStepIo` `WeakAxiomatic.lean:170`, `projLbl LDev ↦ some LIo` `WeakPromiseBridge.lean:542`, `LDev` out of
`lbAdmin :140`, `LIo` shape arms `True`, `promiseFreeCompleteClean`/`wpPfBridge` carry I/O, the AxSpin release lemmas take
RAM-only anchors; `PROGRESS-W13I.md`); its fabric-bundle half is BLOCKED under [R22.2] (a `pdevEv`-true but NON-moving disk block
is a non-member the supply cannot replay at the global fabric) → **[OWN.43] RULED (a): membership by fabric CONTACT** — `(i,k) ∈
gfDev ↔ gisIo (i,k) ∨ dvi k ≠ dvo k ∨ the block of item k has a pdevEv-true step`; `hblkQ`'s `∀ d` folding GENERALIZED (not
deleted); the interim `.PDisk` clause deletable; supersedes [R22.2] (§A(†), §C W13 (I) RELAUNCH brief); **W8-β′** increment 1
green, increments 2–4 in progress in w2 (`../xv6iris-weak-w2/PROGRESS-W8beta.md`; brief UNCHANGED).  **[R30.s4]** applied ("by
W-SCO" at the two sites).  **Next batch [OWN.44]: W-SCO (A) ∥ W13 (I) bundle half, launched right after this review loop
reaches SATISFIED; W-RSV after W8-β′ merges** (§C top, rev-35 launch paragraphs).  No new owner question (R31: none missing;
[OWN.42]/[OWN.43] RULED and recorded in §D as Q-SCO-words/Q-GFDEV-contact; every option FAITHFUL — RVWMO/Sail/Zifencei/PMAs
silent on replay bookkeeping and on device-model membership).  History: rev 35 — R31 (1 req., 0 alt; applied via route (i);
s1–s3 applied) + RESULTS (M1 DONE; W5d M2 core; W-SCO (0)+generic; W13 (I) realization) + [OWN.42][OWN.43][OWN.44];
[R29.s2][R29.s3][R30.s4] closed.
**Rev 34 (2026-10-12) = rev 33 + review R30 (1 required change, tag [R30.1]; NOT SATISFIED — S text in W5d's first
commit, proof organisation, no design or memory-model change; adopted [R30.s1], [R30.s3], [R30.s6]).**  What changed:
**[R30.1]** rev 33 still put `itvOf` and its recurrence/frame condition into `execProgOk'S` UNGUARDED — `fcutT` sees one `itv`
and cannot guard them, so a fixed `itvOf` at M1 would strengthen M1's premise and an `∃ itvOf` would need an unplanned choice
lemma; now a SECOND per-index parameter `fcutE` (inside `execProgOk'S`'s existential beside `fetchesOk`, `PfRunShape.lean:247-262`)
carries them, `True` at M1, and `itvOf` is a FREE variable of `srvwmoXv6M2Premises`, a parameter of no shared definition (M1's
content unchanged BY CONSTRUCTION; M1 replay lemmas at both trivial instances; §B(4)(iii), §C top, §C W5d).  Adopted: **[R30.s1]**
`PfStepTso.lean` (`pfRunSTAuthors :527-536`) joins W5d's edited files; **[R30.s3]** `sailCycleOrder` is stated AT the trivial
`fcutT` (≡ `∀ fcutT` via `pfRunSTForgetCut`); **[R30.s6]** `pfLoadFactsTNonload` is `:579-581`.  [R30.s2]/[R30.s5] handed to the
W5d worker at launch; [R30.s4] touches W-SCO's running brief — deferred to its merge review.  No new owner question (R30: none
missing; every option FAITHFUL — RVWMO/Sail/Zifencei/PMAs silent on premise threading).  History: rev 34 — R30 (1 req., 0 alt;
s1, s3, s6 adopted; s2, s5 to W5d at launch; s4 to W-SCO merge review).
**Rev 33 (2026-10-12) = rev 32 + review R29 (2 required changes, tags [R29.n]; NOT SATISFIED — both S text, proof
organisation and record-keeping, no design or memory-model change; adopted suggestions [R29.s1], [R29.s5]; [R29.s4] confirmed).**
What changed: **[R29.1]** W5d's carrier for the M2 cut clause as pinned by [R28.4] could not be executed — `Hyps.cut`
(`MachOfPf.lean:664-671`) takes the UN-threaded `pfStepFacts` and never sees a `pfStepFactsT` clause; a non-trivial `.LIFetch` arm
of `pfLoadFactsT` falsifies `pfLoadFactsTNonload` (`TsoShadow.lean:581-583`), through which EVERY fetch of M1's run enters
`pfRunST` (`pfRunSTApp :622-632`); an `execProgOk'S` conjunct strengthens M1's premise.  The cut clause is now carried by ONE new
parameter `fcutT` (shadow `itv` first; `fok` stays 5-ary) as a THIRD fact `pfCutFactsT` of `pfRunST.snoc`, threaded through
`contR`/`simNode`/`Hyps.cut`/`cutOfPristine`/`sailCycleOrder`/`srvwmoXv6M1Core`, **M1 instantiating it with `True`** — M1's
statement TEXT changes, its content, name and `axioms`/`opaques` entry do not (the W5 CLOSE-OUT's registration by NAME stands);
`SrvwmoXv6Adequacy.lean` IS edited (trivial instances); the parameter threading is W5d's FIRST commit (S–M), landing after W-SCO's
`Hyps.fi` widening and before W-SCO states `sailCycleOrderK`/`srvwmoXv6M1` (§B(4)(iii), §C top, §C W5d; W-SCO's brief UNCHANGED
— worker running — a NOTE appended); **[R29.2]** the one stale lane-order sentence in §C's serial-items paragraph now states
W8-β′ → W-RSV → W8 (f2-ctx).  Adopted: **[R29.s1]** W-SCO's `fetchIsImage` two-lemma recipe for a PAST fetch (`pfRunSTFacts` at
the prefix + a `pclsEv` log-prefix lemma; appended as a NOTE, the brief itself unchanged); **[R29.s5]** `rowFetchM2`'s `hq` comes
from `pfCutFactsT`'s witness directly.  **[R29.s2]** (the SailM residual-invariant statement) and **[R29.s3]** (the stale
`AxSpinT2b,AxSpinT2c` lists in `baseline-weak.json:2-6`/`Audit.lean:91-92`; write the module list ONCE) are NOT written into the
running W-SCO/W5 CLOSE-OUT briefs — hand them to those workers at merge review.  No new owner question (R29: none missing; every
option FAITHFUL — RVWMO/Sail/Zifencei/PMAs silent on premise threading and lane order).  History: rev 33 — R29 (2 req., 0 alt;
s1, s5 adopted; s2, s3 deferred to merge review).
**Rev 32 (2026-10-12) = rev 31 + review R28 (5 required changes, tags [R28.n]; NOT SATISFIED — all S text, no design
or memory-model change; adopted suggestions [R28.s1]–[R28.s8]) + [OWN.41] (Q-RSV-order RULED (b), 11:09 2026-10-12).**  What
changed: **[R28.1]** the W5 CLOSE-OUT's `baseline-weak.json` entry is PINNED to the exact JSON the audit accepts (`axioms` =
`propext`/`Classical.choice`/`Quot.sound` ONLY — a listed `bv_decide` certificate is rejected as a stale axiom, `Audit.lean:305-313`;
`opaques` = the two `resv` opaques + `MachCSL.bootImageSealed`, new to THAT FILE but not to the trusted base; `platform_hooks`
unchanged; five comment sites incl. `audit.sh:51`'s `--build` list); **[R28.2]** W-SCO's per-word lemma had no handle on WHICH word
was fetched (`Hyps.fi` quantifies the pf run only; `candKfetch` constrains addresses, not bytes) — `Hyps.fi` is WIDENED to `cut`'s
shape (`MRun` + `SimRel` premises), the fetched word is pinned to the image through `cutOfPristine`'s argument (factored lemma
`fetchIsImage`), ONE line of `SrvwmoXv6Adequacy.lean` adapts (statement unchanged); **[R28.3]** the launch set's "no shared file"
was false in three files (`roots-weak.txt`/`baseline-weak.json`/`audit.sh`, `PfStepTsoView.lean`'s header, `MachOfPf.Hyps`) → a
LANDING ORDER (CLOSE-OUT first, its deviation-(4) wording anticipates W-SCO; W-SCO registers at its CLOSE step; W5d rebases
`m2Hyps` on the widened `Hyps`); **[R28.4]** W5d/§B(4)(iii) said `fok` gains a 6th argument, which would change `candKfetch`'s
type and M1's registered statement — `fok` stays 5-ary, `itvOf`'s lower bound enters through the shadow-threaded layer
(`pfStepFactsT`) and `execProgOk'S`'s per-index conjunct; `rowFetchM2` is `PfStepTsoView.lean:778`; **[R28.5][OWN.41]** the
serial lane is now **W-COH ✓ → W-DMA0 ✓ → W8-β′ (RUNNING) → W-RSV → W8 (f2-ctx)**, recorded at every order site, and W-RSV's
brief gets a **Launch (rev 32)** paragraph (deps = W8-β′ MERGED + M1 ✓; rebase surface ≈ 8 MachCSL files β′ touches; the W4/W2
re-proof — 13 `MachOfPf.lean` guard sites incl. F9's four `hres` — INSIDE W-RSV; acceptance with the REGISTERED root green).
W8-β′'s brief UNCHANGED (running).  No new owner question (R28: none missing).  History: rev 32 — R28 (5 req., 0 alt), [OWN.41].
**Rev 31 (2026-10-12) = rev 30 (SATISFIED by R27: 0 req., 7 sugg. [R27.s1]–[R27.s7] — s1–s3 handed to the W8-β′
worker at launch, s4 the (r2) twin ≈ 0.1–0.3k, s5 `W8-design.md` not re-edited, s6 cites, s7 (f2-ctx)'s MachCSL-side hook exit)
+ W4 F9 DONE + W5 CORE DONE (M1's core theorem LANDED) + the Weak import-hygiene fix + R-ctx DONE (`notes/W8-Rctx.md`) +
[OWN.38]–[OWN.40].**  What changed: **(1) M1's THEOREM IS LANDED — `Weak.srvwmoXv6M1Core` (`Weak/SrvwmoXv6Adequacy.lean:276`,
318 lines; imported at `Weak.lean:634`)**: W4 F9 (`Weak/MachOfPfDisk.lean` NEW, 1290 lines + `MachOfPf.lean` 1659 → 2979;
`MachOfPf.simDisk :2603` PROVES the disk rows; `Hyps :658` is `tso`/`safe`/`cut`/`fi` — the former `disk` field and `SimRel`'s `DR`
parameter are GONE; the device clause is `R-dev` = `diskSide :331` / `MachOfPfDisk.devAgree :429` / `VRel.holds :349`; two
deviations: `cacheWf` (`MachOfPfDisk.lean:105` [R28.s6]) replaces "`cache = []` outside capture → gate", `devrt`/`TaskId` untracked; every `SimRel.dev` consumer
re-proved [R21.3 (c)]) and W5 CORE adapted to it, so **M1's hypotheses are EXACTLY `srvwmoXv6M1Premises σ0 c pst dv` + four `g0`
boot facts (`g0.gen = 0`, `g0.pow = false`, `σ0.wgdev = g0.m.devs.reset`, `diskOf g0.m.devs = fsImgDisk` — always constructible,
`SrvwmoXv6Adequacy.bootStateOf :217`) + the named premise `sailCycleOrder :113` [OWN.35]** — no disk hypothesis and no side
condition ([OWN.40]: the pf disk program STALLS on an OUT capture buffer wrapping past `2^64`, `VirtioProg.outWraps :421`, header
deviation 6 — FAITHFUL to the PMAs, STRONGER than MachCSL, pf ⊆ MachCSL, unreachable for xv6; §B(11) (x), §C W-DISK (d5));
axioms = `xv6FsAdequacy_closed`'s cone + the 4 `bv_decide` certificates of the NI/union/text roots, nothing new; `lake build
MachCSL Xv6 Weak`, lint and `audit.sh --weak` green after the **import-hygiene fix** (`bv_decide`'s auxiliary
`page_based_mem_type.enumToBitVec`/`mem_payload.enumToBitVec` were generated by BOTH `Weak/ExecSC4.lean` and `MachCSL/UTlb.lean`,
so the `Weak.lean` root could not import `SrvwmoXv6Adequacy`; `ExecSC4` now imports `UTlb` and reuses its copies,
`ExecSC4.lean:62-70`; rule recorded `notes/weak-port-protocol.md:91-92,313-317`).  **M1 per the plan's own definition (§A, §C W5):
PROVED, NOT yet CLOSED** — §B(12)/[R21.4] close M1 at REGISTRATION, and the tip registers nothing (`tools/ci/roots-weak.txt` holds
the ten AxSpin roots only; `tools/audit/baseline-weak.json` has no `srvwmo` entry; `XV6_AUDIT_MODULES`, `tools/ci/audit.sh:44`,
lacks `Weak.SrvwmoXv6Adequacy`); what remains is ONE explicit S item, **W5 CLOSE-OUT** (§C W5: the three registrations, the D21
report wording, `PfStepTsoView.lean`'s header deviation (4), the file header's "NOT registered here", status counting).  No premise
is unproved besides `sailCycleOrder`: `candKfetch`/`candScaT`/`candDiskLat` are the candidate RESTRICTIONS M1 is DEFINED by
(D20/D21), satisfiable (`srvwmoXv6M1Satisfiable`).  **(2) R-ctx DONE → W8 (f2-ctx) RE-SIZED and CORRECTED [OWN.38][OWN.39]**
(§C W8 (4)/(6)/Acceptance, §B(2), §C W13 R5 C6, §D Q-R1/Q-R2): **F0** — the scalar chain invariant W8-design pinned ("every
foreign-hart entry `t ≤ bound ξ` has a `syncPath`", `W8-design.md:343-344`) is FALSE at ONE ordinary lock hand-off (a third hart's
unrelated store below the release stamp), so the chain bound is **PER AUTHOR — a vector `chain ξ : CPU → Nat` kept BESIDE the
unchanged scalar TSO floor, joined at each hop, with causal closure** (Q-R1 RULED (a) [OWN.38]); relative to it the 31-row table is
18 CHAINED, 3 DEVICE-KEY, 10 NEEDS-X and **NONE RESISTS — the (f1) fallback list is EMPTY**; five additions the TSO proof never
tracked, **X1–X5** (hooks re-floored from the releaser's OWN vector; a `CtxBox` row "every live key's stamp ≤ `max tp td`"; a
BIRTH key for post-boot locks in `lkFresh`/`isLock`; a DEVICE-only absorb for the virtio watermark; the `ACQUIRE_LLB`/
`ACQUIRESLEEP_*LLB` "cash any `topLb`" surface WITHDRAWN, its consumers re-routed); 4 direct leaky sites OUTSIDE the 21 files
(`IputParts.lean:461`, `ProofAcquiresleep.lean:809`, `StartedInv.lean:198,344`) and 31 consumer files of the hook/llb surfaces;
the `"log"` lock (`ProofInitlog.lean:434`) is a SECOND post-boot lock birth ([R25.3]'s "only" corrected); the `swtch` handoff is
CHAINED with the hop at `lock_pay_intro → lock_pay_take` on `p->lock`, NOT at `wp_swtch` (all 8 `ProofSwtch` transports are
same-hart; `W8-design.md:350` corrected); **[OWN.39]** USER page-table entries go under the `pte-key` arm like the kernel table
(`Cust.pte` and `pteDiscAt` cover BOTH tables — Spec: the privileged spec's A/D update scheme orders updates ASSOCIATED with
fenced accesses, but an A-bit update MAY be speculative and is then ordered by nothing, so a chain would be UNFAITHFUL), hence
`WpPtWalkOwn` joins the MachCSL list; **W8 (f2-ctx) ≈ 6.5–9.5k lines (was ≈ 4–6.5k), 12 MachCSL + ≈ 52 `Xv6/` files + the twin,
3–4 full-cone rebuilds**, still serial — AFTER W-RSV since [OWN.41] [R28.5].  **(3) Launch set (§C top)**: **W8-β′ RUNNING** (brief UNCHANGED); **MAY
LAUNCH NOW** — the **W5 CLOSE-OUT** (S), **W-SCO** (M–L, `Weak/` lane; delivers the `candKfetch`-restricted `sailCycleOrderK` and
the corollary `srvwmoXv6M1` WITHOUT the premise — `srvwmoXv6M1Core` is KEPT and registered as is), **W13 (I)** (graph lane, gate
MET), **W5d** (L, `Weak/` lane — its dep M1 ✓); **W8 (f2-ctx)** waits only for W8-β′ (its R-ctx gate PASSED, no (f1) part);
**W-RSV**: the recorded risk MATERIALISED — M1 closed FIRST, so under D26/[OWN.37]'s order W-RSV waits for W8 (f2-ctx)'s 3–4
rebuilds and M2 waits behind both → **NEW owner question Q-RSV-order (§D, OPEN; recommendation (b) = [OWN.36]'s recorded (α′):
W8-β′ → W-RSV → W8 (f2-ctx))** — **RULED (b) [OWN.41] at rev 32 [R28.5]**.  History: rev 31 — F9 + W5 CORE + R-ctx DONE,
[OWN.38]–[OWN.40], Q-RSV-order OPEN.
**Rev 30 (2026-10-12) = rev 29 + review R26 (2 required changes, tags [R26.n]; one alternative [R26.2-alt]; SATISFIED by R27).**  What
changed — both S text in W8-β′'s brief (§C top; §C W8 (3)/(5)/(6)/Acceptance/Unverified); the W4 F9, W5 CORE and R-ctx briefs are
UNTOUCHED (workers running; R-ctx launchable per R26): **[R26.1]** deliverable (ii)'s registry agreement was stated in the WRONG
direction — "MachCSL registry ⊆ `xv6LockWord σ`" is FALSE at reachable states (`pipealloc` runs `initlock(&pi->lock)` BEFORE
`(*f0)->pipe = pi`, `Xv6/SpecPipealloc.lean:10-12`; `fileclose` unlinks BEFORE `pipeclose` reclaims, `SpecFileclose.lean:10-12`) and
the extraction needs the CONVERSE **registration lemma `xv6LockWord σ b t → b ∈ reg`**; fixed at every site.  **[R26.2]** deliverable
(i) left `reg` homeless and named no STEP at which a byte becomes reserved (the state interpretation opens only inside `swp` step
rules; `newlock_written`/`lock_pay_born` are `|={E}=>`/`|==>` lemmas, `Lock.lean:682-687,488`): pinned — a new era ghost `rsvName`
in `EraGS`/`MachGS` (`Resources.lean:105-135,420-438,470-477`; `MachGS.ofEra` `Power.lean:771-776`; the fourteen-field era tuple at
the PowerOn mint `Power.lean:558-653`, `PowerText.lean:290`; the `MachGS` literals `Xv6/AppUnionPre.lean:88`, `Xv6/AppPreGS.lean:53`,
`Weak/WeakAdequacy.lean:110-128`); **[R26.2-alt]** the reserving step is the `PowerOn` mint ITSELF, for a client-supplied STATIC list
(`KernelRsv.static`, the `KernelMap.static` pattern `Power.lean:558,565`: `cpus[h]`'s three cells + the image spinlocks incl. the
sleeplocks' inner locks), halves held by the interpretation from the mint, `powerBootRes` handing the boot client halves (the
`powerBootResT` split shape, `PowerText.lean:80,113` — NOT W3's trace hook) — because (a) R26's "boot carve" (`BootCarveHart.lean:84`)
is a pure ownership split, not a step, and (b) `riscvPowerAdequacy`'s final hook is `… ⊢ ◇ ⌜phi g' h⌝` (`Adequacy.lean:359-366`: no
fancy update, no invariant), so a registration made by a mid-run step is a GHOST fact the twin's extraction cannot reach unless
membership is PURE in `memModelAt` — true of a static list (`⌜staticIn reg⌝`), false of a pipe lock born at `pipealloc`; so β′'s
provisional `lockWordDiscAt` covers the STATIC lock words (every lock W13 (K) reads on the `allocproc` trace), and pipe locks
(dynamic registration at `wp_s_sw_mint`/`wp_s_sd_mint`, de-registration at `wp_s_sw_zero_release_cancel`, a `tReg ≤ t < tEnd` index)
move to W8 (f2-ctx) with the hook problem recorded as an open design point; β′ re-sized M–L ≈ 1.3–2.3k, ONE cone rebuild; "no PowerOn
hook" → "no PowerOn TRACE hook; the gname and the static halves are minted at PowerOn".  Adopted [R26.s1] (`powerInterp_mmOk`'s
pattern, `Adequacy.lean:481`), [R26.s2] (`pteDiscAt` is a DOCUMENTATION clause — `wtlbResPtTranslateAddrStaleAt` is over `Wmstate`,
`Weak/WeakKptStale.lean:488-502`, no Stage-2 consumer named), [R26.s3] (`.pte` custody anchored MachCSL-side via `kptRootName`),
[R26.s4] ((f2-ctx) needs a MachCSL-generic chain invariant parametrised by the registry), [R26.s5], [R26.s6].  No owner question
(R26: none missing; both changes are proof organisation — RVWMO/Sail/Zifencei/PMAs silent, every option FAITHFUL).  History: rev 30 — R26 (2 req., 1 alt).
**Rev 29 (2026-10-12) = rev 28 + review R25 (3 required changes, tags [R25.n]; no alternatives).**  What changed:
**[R25.1]** `chainOkAt` as pinned was FALSE on kernel page-table-entry bytes — the hardware A/D write-back is an EXCLUSIVE
store by the walking hart (`WpPtWalk.lean:3-7,455-470`) that every other hart's walk PLAIN-reads and `coh`-stamps
(`Lang.lean:373-375,400`, `TsoMem.lean:354-356`) with no sync chain (`KptInv.lean:4-8`; Svadu ON: `menvcfg = ADUE | STCE`,
`SpecStart.lean:29,40`): the export gains `Cust.pte`, `chainOkAt` exempts it, a new clause **`pteDiscAt`** (every post-boot
kernel-PTE entry an A/D variant of the canonical value, `KptInv.pteVariant`) joins `xv6AccessDisc`; R-ctx tables the walker
as a NAMED `pte-key` arm; the W13 census's "`kernel_pagetable` non-racy" line becomes row C6; `:492`'s "`menvcfg = 0`" corrected
(FIOM = 0 still holds).  **[R25.2]** W8-β′'s acceptance is pinned to THREE Lean statements — the MachCSL `reservedOk σ reg`
conjunct beside `⌜mmOk σ⌝`, the `Xv6/` extraction `powerInterp_accessDiscβ` on `powerInterp_textPristine`'s pattern (rev 30: `powerInterp_mmOk`'s [R26.s1]), and
**the (r2) sibling root `xv6DiscAdequacy_closed` NOW at the β′ conjunction** (`xv6AccessDisc` provisionally `lockWordDiscAt ∧
cpuStaticAt`, W8 (f2-ctx) only STRENGTHENS it) — so "unblocks W13 (K)" is true at the root level; β′ re-sized M–L ≈ 1.1–2k.
**[R25.3]** R-ctx's file list is 21 files (+ `Xv6/ProofSwtch.lean`'s `kctx_move_in/out` ×5 = the `swtch` handoff door, +
`Xv6/PipeBirth.lean`'s `lock_pay_born` = the only dynamic lock birth); counts corrected (`ctx_move` 1, `kctx_move_*` 6,
`lock_pay_born` 1); its table gains handoff and walker rows.  Adopted [R25.s1]–[R25.s6] (cites `:502`, NEW `SrvwmoXv6Adequacy`,
`tools/tcb/expected.json`, `lkFresh` 30 files, `Dres :269-273`, the `userret` `fence.i` image fact behind `utextDiscAt`,
Q-HOLDING (c) touches `lk->locked` too).  No owner question (R25: none missing; [R25.1] is FAITHFUL export shape, not a
memory-model choice — Spec line in §C W8).  W4 F9 and W5 CORE briefs UNCHANGED (launchable per R25).  History: rev 29 — R25 (3 req.).
**Rev 28 (2026-10-12) = rev 27 (SATISFIED by R24) + W-DISK DONE + the W8-design results (`notes/W8-design.md`,
`notes/xv6-holding-race.md`) + [OWN.37] (Q-W8-feed RULED (a)).**  What changed: **(1) W-DISK LANDED** (merged at the tip:
`Weak/VirtioProg.lean` REWRITTEN to the aligned program — 672 lines, `DM` = `DRet`/`DRead`/`DFence`/`DWriteDev`/`DPop`,
`virtioProg :438`, `drainAll :323`, `popState :319`, `preCaptureHead :338` (= `pre₁`), `dusedTail :394`, `virtioProgWf :661`;
`WeakEvLang.ediskStep :936` with the ten arms, `ediskStepWf :1360`, `eprimStepDiskReducible :1393`, `setDvirtioSelf :922`;
`WeakEvInst.pdiskProg :499` (ten arms, deviation 10), the STATE-AWARE `pdevEv :604`, `pdiskProgDevFree :1759`/
`pstepDiskDevFree :1781`/`pdevEvOk :1792` re-proved; the `ewpDisk*` rules `WeakEvDisk.lean` — `ewpDiskStart :388`, `ewpDiskRead
:431`, `ewpDiskFence :488`, **`ewpDiskWriteDevStore :524`/`ewpDiskWriteDevSkip :607`/`ewpDiskWriteDevAbort :666`,
`ewpDiskPop :722`/`ewpDiskPopRefused :772`**, `ewpDiskIdle :816`; W2's disk rows `PfStepTsoMem.pfDWriteDevRowMem :698`/
`pfDSkipRowMem :806` and `PfStepTsoView.rowDiskDevMove :808` (+ `rowDiskWrite :796`'s fabric-delta form, the (↓) table rows
`:45-46`); `WeakRvwmoSupply.devQuiet :177`/`devQuietStep :183`, `pdevEvFalse :209`/`pstepEvDevfree :219` RESTATED (new proofs
by cases on `p` [R22.s2]), the Supply family's `devQuiet p` hypothesis; `WeakRvwmoFab.gfexecConf :620`'s INTERIM `LDev`-free
`.PDisk` clause `:633` ("DELETED BY W13 (I)"), `hemitfStatesQ :396`/`hartConffStatesQ :556` with the `devQuiet ∧ LDev`-free
hypothesis, `fconfRowsPin :885`, `fconfSupply :928`; `WeakRvwmoCapstone.epsInitQuiet :232` discharging the boot pool;
`xv6RvwmoSafeModuloF :238` still builds; `WeakEvCapstone.lean:1183` unchanged in statement; NO `DWild` left in `Weak/`
(grep = 0); `MachCSL/Dev/Virtio.lean` and the driver proofs UNTOUCHED.  **Deviations from the rev-27 brief (all pf-internal,
sound direction, no owner question)**: (d1) `Weak/AxOpsem.lean` was EDITED — not on the file list — because
`pstepProgReadCont :622`'s `.PDisk` case destructures every `pdiskProg` arm (`:647-660`, now ten); (d2) the quiet-boot
hypothesis is threaded as **`∀ i, i < N → devQuiet (boot i)`** (`WeakRvwmoFabInd.lean:425,465,537`, `WeakRvwmoLin2.lean:
1007,1024`, `WeakRvwmoCapstone.lean:268`), not per-row inside `gfexecConf`; (d3) the PLAIN `DWrite` node is GONE from `DM`
(every disk store is a `DWriteDev`; `pfDWriteRowMem :672` survives as the store-without-move lemma (13) that (13′) composes);
(d4) Rocq's `ewp_disk_write`/`ewp_disk_commit` are RETIRED (`WeakEvDisk.lean:52-78`, deviation 5), not re-stated.  §0 F1,
§A(†), §B(11)'s pf-drift entry and §C W-DISK are marked RESOLVED where they stand (the binding text is kept as the record);
**W4 F9 is UNBLOCKED.**  **(2) W8 restructured per [OWN.37]** (§C W8, §D Q-W8-feed; the W8-design spike is DONE, read-only,
nothing built): the export is the PURE per-state predicate **`xv6AccessDisc σ`** (`Xv6/AccessDiscipline.lean`, text pinned
from W8-design §1 in §C W8 — `chainOkAt ∧ lockWordDiscAt ∧ pteDiscAt ∧ cpuStaticAt ∧ cpuProcDiscAt ∧ utextDiscAt` [R25.1]; D24 FIXED), reached
through the SIBLING ROOT **(r2) `Xv6.xv6DiscAdequacy_closed`** on the W3 pattern ((r1) is NOT available: the predicate is
xv6-specific and an existential registry inside `mmOk` lets the chain run through a non-lock word); a ledger-free (β) export
covers only the lock-layer words and `cpus[h]` — so W8 is **three items**: **W8-β′** (M, ≈ 0.8–1.5k; `cpuStaticAt` +
`lockWordDiscAt` by a MachCSL "reserved region" + lock registry; 6–8 MachCSL + ≤ 30 `Xv6/` files, ONE cone rebuild, serial
MachCSL, lands FIRST, unblocks W13 (K)), then the read-only **R-ctx** gate (S: re-justify the ≈ 35 TSO-leaky context-law uses
in 19 `Xv6/` files by a sync chain or the device-key arm), then **W8 (f2-ctx)** — chain-carrying context tokens (L–XL ≈
5–8.5k lines, 11 MachCSL + 19–62 `Xv6/` + 5 twin files, 2–4 full-cone rebuilds, serial MachCSL before W-RSV; fallback (f1)
per-site custody PER PART that resists R-ctx — XL ≈ 10–15k, ≥ 320 files).  **(f2)/(f3) feeds do NOT exist** for stacks or
lock-protected bytes (custody is invisible to the memory rules; (f3′) is a valid EXPORT vocabulary — the dynamic owner
`kOwnerAt` = the hart whose `cpus[h].proc` names `&proc[j]` — but not a feed).  Serial lane: W-COH ✓ → W-DMA0 ✓ → W8-β′ → W8
(f2-ctx) → W-RSV, with **M1 NOT in the MachCSL queue**: M1 = W5 CORE + W4 F9 (`Weak/`-only, no W8 fact in its premise set),
so it CLOSES IN PARALLEL with W8; W-RSV waits for BOTH (D26 + file overlap).  **(3) The plan's (iii) was FALSE at `holding+0x12`
(`0x80000c04`, `PResidue`, `KernelPins.lean:255`)**: `acquire` calls `holding()` BEFORE the AMO, so a NON-holder reads
`lk->cpu` — the holder's plain, still-unpublished `sd` (`notes/xv6-holding-race.md`; benign: the reader can never see its OWN
pointer, `lkCpu_read_not_mine`, `MachCSL/Lock.lean:18-22`).  Every claim that the read is lock-protected — [W13c] (K)
precondition (ii) "under its OWN lock", the census's C2 "held" case, §C W8's "(ii) must cover `lk->cpu`" — is corrected: the
export EXEMPTS lock-layer bytes from (iii+) and covers them by `lockWordDiscAt`; W11's `badSeg` refutation and W13 (K)'s
`ioSegPinned` route `lk->cpu` reads through it (REPORT level, §D Q-HOLDING).  **(4) Launch set (§C top)**: W4 F9 ∥ W8-β′
(serial MachCSL) ∥ R-ctx (read-only) ∥ W5 CORE; W13 (I)'s gate is MET (next in the graph lane).  **No OPEN owner question**
(Q-W8-feed RULED (a) [OWN.37]; Q-HOLDING is REPORT level).  History: rev 28 — W-DISK DONE + W8-design + [OWN.37].
**Rev 27 = rev 26 + review R23 (2 required changes, tags [R23.n]; no alternatives; SATISFIED by R24).**  What changed: **[R23.1]**
W8's class (i) has a DYNAMIC owner — process kernel stacks migrate between harts at `swtch` (`stackOwn` travels in the
context payload, `Xv6/ProofSwtch.lean:140`, `Xv6/SpecSwtch.lean:35-58`): (i) = "no foreign writer SINCE THE LAST OWNERSHIP
HANDOFF" (`swtch` under `p->lock`); (f3)/(β) cover only `PPerCpu` and the fixed per-hart stacks; W8-design COUNTS the 1,034
`PStack` sites by context and names the handoff doors as (f2) layers (§C W8-design/W8, §B(9d), D24); **[R23.2]** the
unsatisfiable rev-25 `gfDev` formula purged from W-DISK (ii)(c) and §C W13 (M); every "FABRIC MOVES" gloss of `gfDev`
now reads "fabric TRANSACTIONS (I/O-class events by class, plus fabric-moving stores)"; Q3 (b) carries the disjunction.
Adopted: [R23.s1] `hemitf`'s endpoints bracket the BLOCK (admin run + step), START a member by class, [R23.s2] FLUSH/unknown
type 1 → 3 and the pf-only `DFence` in the deviations line, [R23.s3] cite drift, [R23.s4] the W8 doors, [R23.s5] the
`DWild` acceptance wording.  **No OPEN owner question** (R23: none missing).  History: rev 27 — R23 (2 req.).
**Rev 26 = rev 25 + review R22 (3 required changes, tags [R22.n]; no alternatives).**  What changed: **[R22.1]**
W8-design ALSO pins (4) how the ledger is FED — (f1) per protected `Xv6/` site / (f2) lock layer / (f3) derived from `σ` —
with a COUNT of sites or wrapper layers, and (5) the ROOT path ((r1) into `mmOk`/`xv6TracePure`, text unchanged, meaning
strengthened; (r2) a W3-pattern sibling root, ≈ 1.8k lines of twins); W8's "one cone rebuild" is CONDITIONAL on (f2)/(f3),
(f1) is the XL outcome that re-opens [OWN.36] (§C W8, D24); **[R22.2]** W13 (I)'s clause is `gfDev ↔ gisIo ∨ dvi ≠ dvo` — rev
25's `gisIo → dvi ≠ dvo` was UNSATISFIABLE for xv6 (an LSR read, a virtio NOTIFY, every virtio register read moves nothing)
and "the used-idx `LStore` is the ONE non-I/O fabric move" was FALSE under the MECHANISM (the status, used-element and
used-idx `DWriteDev`s all move `dvirtio`); trusted-surface sentence reworded; the [OWN.31]/[OWN.32] wording delta REPORTED,
no gate (§D Q-GFDEV-delta); **[R22.3]** the `Lang.lean` cite authority re-based on the post-W-DMA0 tip, the binding
W-DISK/F9/W-RSV cites fixed.  Adopted: [R22.s1] `simWire :1295-1354`, [R22.s2] `pdevEvFalse` restated = a NEW proof,
[R22.s3] W5 CORE's instantiations named, [R22.s4] a "moves the fabric?" column, [R22.s5] §B(11) (vi).  **No OPEN owner
question** (Q-GFDEV-delta is REPORT level).  History: rev 26 — R22 (3 req.).
**Rev 25 = rev 24 + R21 (4 req., tags [R21.n]; no alternatives) + [OWN.36] (Q-W8-lane RULED (α)).**  What changed: **[R21.1]+[OWN.36]** W8 leaves the parallel launch set — a read-only **W8-design** spike (S) pins
W8's export statement (= D24), the ledger's file/lane and whether a ledger-free (β) export covers W8 (i)/(iii); then **W8's
ledger in the state interpretation is the next SERIAL MachCSL item, BEFORE W-RSV** (lane W-COH ✓ → W-DMA0 ✓ → W8 ledger
→ M1 → W-RSV; §B(12), §C, D24, D26); **[R21.2]** Stage 2 consumes `linCandScaT`/`linCandScaTMinus` on the NORMALIZED `GD'`
(rule 14 by construction), NOT `linCandScaTCatT` on `GT.gtG` (`grule14` fails on the LB/W→W graphs the quantifier
admits); W12 (1) gains the producer `gppoCat6Gmo GD'.gdG` (unverified); **[R21.3]** zero-length IN is 1 → 5 (`:526`
included); the single-burst invariant DROPPED (stale entries harmless under `R-dev`); F9 re-proves EVERY `SimRel.dev`
consumer and checks `pre₁` against `pdiskUart` moves too; **[R21.4]** W5 CORE is CONDITIONAL on `Hyps.disk`
(UNSATISFIABLE until W-DISK + F9): plumbing, not a milestone, not registered — M1 is registered/reported only at F9.
Adopted: [R21.s1] `sailCycleOrder` in LABEL-LIST form (no shadow in the published premise), [R21.s2] W-SCO covers every
2-aligned 4-byte word of the window, [R21.s3] the capture-`DRead` 1 → 0 case, [R21.s4] cites/stale text.  **No OPEN owner
question.**  History: rev 25 — R21 (4 req.) + [OWN.36].
**Rev 24 = rev 23 + R20 (3 req.) + [OWN.35] (Q-FIARM RULED (b)+(a′)) + W-DMA0 (A), W4 F1–F8 (`Weak/MachOfPf.lean`, 1659),
W11 (iv)b (`Weak/RvwmoXv6ScaT.lean`, 792) DONE:** **[R20.1]** `R-dev` on the OUT capture segment ABSORBS a hart reset —
`pre₁` := the status `DWriteDev`'s `pre` TRUNCATED before capture's `modify :517-518` (in-flight pre-check → `setPhase
.fetched :526` → `taken` guard `:529`, identity arms): ONE formula for free / held / reset (rev 23's `setPhase .fetched (+
latch)` was FALSE after a STATUS := 0); **[R20.2]** the zero-length data node ELIDED (`dreadData`/`dwriteData` shape),
`DmWf` keeps `n ≠ 0`, (M5′)'s `n = 0` disjunct dropped; **[R20.3]** W11 (iv)b landed, Names fixed; **[OWN.35]** ONE named
trusted premise `sailCycleOrder` (§A, §B(11); = `MachOfPf.Hyps.fi :635`), demoted for kernel text by **W-SCO** after M1;
W4's open items `winPristine` → W5, F9 → `R-dev`.  s1–s4 adopted; s5 only `PfStepTso.lean:322-325`.
**Rev 23** = rev 22 + R19 (3 req., all W-DISK binding text) + W2 CLOSE DONE (`pfStepTso` PROVED with the REPAIRED
statement — rev 21's pinned text FALSE at the fetch row and at every `|log|`/`ownPub` row, VACUOUS inside an exclusive
pair) + [OWN.34] (W-DMA0 via (A)) + Q-FIARM raised: **[R19.1]** "pf never drains" WITHDRAWN (`cacheView pf = cacheView M`
not invariant across STATUS := 0 / a partial-sector tail) — pf DRAINS at the gate (`drainAll`, `completeOk` VERBATIM),
`R-dev` FULL equality, `cache = []` outside capture → gate; **[R19.2]** the idx write's `usedIdx = ui ∧ cfg = c` conjuncts
are LOAD-BEARING — state-receiving `DWriteDev` continuation, `DM.DPop` named; **[R19.3]** `pre₁` conditional on the `taken`
guard — SUPERSEDED by [R20.1].  s1–s5 adopted.
Rev 22 = rev 21 + R18 (4 req., W-DISK binding text): **[R18.1]** payload path specified twice → (A), its REMEDY superseded
by [R19.1]; **[R18.2]** `devQuiet` rescues the Supply family only — `gfexecConf` gains the INTERIM "a `.PDisk` row's
emission is `LDev`-free" clause (D39 internal, the `ioResidueGwfInterim` pattern); **[R18.3]** `pre` opens with the in-flight
pre-check (no mid-burst-reset RESURRECTION), `R-dev` up to `pre₁` on the OUT capture segment, ABORT 1 → 0; **[R18.4]**
state-dependent `pa`/`bs`, snapshots where `serve` takes them.  s2–s6 adopted; [R18.s1] decided NOT needed at W2 CLOSE.
No owner question (device-internal, every spec silent).
Rev 21 = rev 20 + R17 (4 req.; [R17.1-alt], [R17.2-alt]) + [OWN.33] (W-DISK-Q4 = (c): sequential pf disk, §B(11) (viii);
concurrent pf disk agent = follow-up after M2): **[R17.1]** FOLDING RULE (own guard → skip; `DevM.guard` → **(α) ABORT**,
the MachCSL task a zombie; single-burst invariant) + [R17.1-alt] the abort carries `pre`'s moves; **[R17.2]** `pfStepTso`
pinned as Lean + [R17.2-alt] five hypotheses (`fn = none`, `l ≠ LSilent`, not `LDev`, the two `fiArm`s); **[R17.3]**
`devQuiet`/`devQuietStep` start-state hypothesis through Supply/Fab/Lin2/FabInd; **[R17.4]** sequential service a named
strengthening.  s1–s5, s7 adopted.
Rev 20 = rev 19 + R16 (6 req., [R16.1-alt]) + [OWN.30]–[OWN.32] (W-DISK-Q1 (b) → serial **W-DMA0**; Q2 (a); Q3 (a)) +
RESULTS (W13 (T)+(M) `GraphFabResidue.lean` 268 l. + `lbIsMem`; W5-pre `SrvwmoXv6Witness.lean` 805 l.; W11 (iv)a
`RvwmoXv6Sca.lean` 327 l.): **[R16.1]** W-DISK's (M4)/(M9) contradicted `pdevOk` (`WeakPromiseFact.lean:613-614`) → the
`DWriteDev`/state-aware-`pdevEv` MECHANISM, no pure re-read node, W13 (I) = M, `DWild` = 21 occurrences; **[R16.1-alt]**
a write's `g = none` SKIPS (`Lang.lean:574`); **[R16.2]** [OWN.30]/[OWN.31] recorded; **[R16.3]** W-DMA0 standalone (folding
it into W-RSV cycled F9 → M1 → W-RSV → (b) → F9); **[R16.4]** W5-pre, W11 (iv)a DONE, W11 (iv)b launchable; **[R16.5]** xv6
CLEARS `F_FLUSH` (FLUSH marks vacuous) and MachCSL's device-model choices are PERMANENT §B(11) entries; **[R16.6]**
`pfStepTso` pinned, item (3) `fiArm` W2 CLOSE's; s1–s6.  (Rev 21's "`cfg`/`usedIdx`/`cacheView` from the START
snapshot" and "`R-dev` EQUALITY incl. phases" are SUPERSEDED by [R18.3]/[R18.4] below.)
Rev 19 = rev 18 (SATISFIED by R15) + Stage-1 RESULTS (W5b′, W-COH, W1b (+ (A)), W5d-G G0, W2a, W2b DONE; W13 (E)
PARTIAL) + [OWN.26]–[OWN.29] + the W4 census (`notes/W4-structural-census.md`, [W4c]) + the W13 I/O census
(`notes/W13-io-census.md`, [W13c]): §0 F1 (iii) LANDED (W-COH), the honesty lists name the pf DISK MODEL's drift until
W-DISK lands; §A(b) = W1b's export (`forkHist` [OWN.28]); §A "Names" moved the landed Stage-1 names; §B(4)(iii) cites the
RE-CREATED `GraphFetchSpike.lean` with [OWN.26]'s `emSlot`; §B(9)/(11)/W13 R5 dropped the STALE `pr.locking`/`panicked`/
"UART LSR racy flag" entries and §B(11) gained the census's per-arm omissions; §B(10) recorded W2a/W2b, `rhist`, the
`LSilent`/`LInstr` correction and the FALSE bound `n ≤ |st|` (dropped); §C gained **W-DISK** (E-D1 RULED (a) [OWN.29]),
W4's census interface (E-S1–E-S3, F1–F8 NOW, F9 after W-DISK), W2 CLOSE, W13 (E)'s re-sequencing [OWN.27], W5d-G G1's
carry-overs.
R14 (rev 18, NOT SATISFIED → rev 18 SATISFIED by R15) fixed three rev-17 worker texts: **[R14.1]** W-COH's file list
gains the MERGED `Weak/TsoOfPf.lean` (`tsoAfterLoadCoh` stated the OLD semantics) and the `Vtest` lib (`vtest-lean/
Vtest/XState.lean`, `HartExec.lean`; NOT a default target, `lakefile.toml:43-49`), neither in the Xv6/MachCSL CI build
(`tools/ci/audit.sh:13-16`) — built explicitly (DONE: `TsoOfPf.lean` 312 lines, `g2TsoSched :251`, `g2OwnLog :272`);
**[R14.2]** W2's instance-INDEPENDENT row is **exload**, NOT exstore — `LExStore` is the SAME `MState.store` as the plain
store (`excl` a parameter), whose `coh` RESET W-COH adds; **[R14.3] + [OWN.24]** W5d-G G1–G5 run AFTER W13 (M).
R10–R13 (revs 14–17; the tags survive in the body): **[R13.1]** W-RSV (i-a)'s census gains the M-MODE lane — 35
`wp_m_*` wrapper STATEMENTS, `ProofEntry`/`ProofStart`/`ProofTimerinit` (68 applications), `SpecSpin`/`ProofSpin`: 12
`Xv6/` files, L–XL unchanged, (i-a) stays RULED, delta REPORTED (no gate) — §C W-RSV, §D W-RSV-Q; **[R13.2]** the hart
`LLoad`/`LStore` rows' Lean waits for W-COH (DONE); W1b RULED-in; **[R12.1]** W-RSV's ghost cost — `wpLoop_restart`
cannot be re-stated over `ctxTok`, so (i-a) threads `resvFragAny` through 16 cycle rules' statements and callers (the
LARGER serial MachCSL item); **[R12.2]** [OWN.21] applied, gates removed, the foreign-only stamp LOAD-BEARING for (9d);
**[R11.1]/[R11.1-alt]** G2-Q's (a′) corrected to RESET + FOREIGN-only (both RULED, now LANDED); **[R11.2]** W-RSV as
boundary clearing, guards stay; **[R11.3]** the trace shadow cannot carry `itv` — W5d's `itvOf`; **[R11.4]** (F-dep)
fills `LIo rd`'s `asrc` as the `LExLoad` arm does; **[R10.1]** G2-Q's original (a) NOT faithful (own-forwarded byte);
**[R10.2]** `linCandScaT` graph-derivable only under (a′)/(a‴); **[R10.3]** the shadow is a function of the step-list
PREFIX — W5b′ threads it (DONE); **[R10.4]** the W5d-G spike file was lost, re-created from `notes/W5dG-spike.md` (DONE,
G0).  **RULED [OWN.17][OWN.18]: G1-Q (e) `candScaT`; G3-Q (a″) `candDiskLat` + (R2′) + anchors; D42–D43 (a); D46 (a);
D47–D49 (a); D50 (b) EXTEND the taggers (W13 (F-dep), in scope); D51–D52 (a).**  Rev 13: the W2 spike
(`notes/W2-spike.md`, `Weak/TsoOfPf.lean`) hit D7's STOP at **G1** `.aq` floor debt / **G2** footprint coherence stamp
(§0 F1 (iii)) / **G3** DMA reads at the top; Layer 2 redesigned around the TsoMem view SHADOW (§B(10)).  Rev 10/R8:
**D38 RULED [OWN.14]: MMIO accesses are I/O-CLASS GRAPH EVENTS**, W13 around `Lbl.LIo` + `ioResidueGmo`.  Every OPEN
or STANDING semantics question opens with a "Spec:" line and marks each option faithful / stronger / weaker (OWNER
RULE 2026-10-09) [R8.1][R9.1][R9.s3].**
**One-liner [R6.s1][R7.2a][OWN.12][OWN.14]: the published quantifier is riscv.cat RVWMO with TAGGED dependencies
(`rvwmoCatConsistentT`) over graphs whose rows CONTAIN the I/O accesses as events, plus an I/O-ordering PLATFORM
assumption (`ioResidueGmo`: BEYOND what ppo gives those events — nothing from FENCE (Sail drops the i/o bits), only
rule 5 and the (c1) dependency edges (D50 (b) [OWN.17]) — a row's RAM accesses po-before an I/O event and its RAM STORES po-after it are
gmo-ordered on that side of it, and I/O events are gmo-ordered as the fabric serializes them — the residue is what
QEMU TCG gives and RVWMO + PMAs do not, AND what the one-row device model requires [R8.2][R8.s2]) and a graph-tier
Zifencei fetch model (`gzFetch`) — two named trusted-base items with no reference model.  Non-vacuity past boot: W14
(D44 (i), RULED).**
History (all 2026-10-09; reviews `notes/weak-allocproc-plan-review-RK.md`): rev 1 survey; rev 2 R1 (11 req.; D8–D13);
rev 3 R2 (5 req., two [R2.n-alt]; D14–D19); rev 4 R3 (4 req.; D20–D23) + [OWN.1–4]; rev 5 R4 (5 req.; D25, D27, D28);
rev 6 R5 (3 req.: quiescence VACUOUS → W13; W3 sibling root; `pairAdjacent`) + [OWN.5–9]; rev 7 R6 (5 req., s1–s4) +
spikes (tagged cat model, W12b, `devAcyclic` REFUTED, T2-1c′ LANDED, W13 = XL, fetches ADMINISTRATIVE; D32–D43); rev 8
R7 (4 req.: `dv → read` arm DROPPED (a′), disk row first-class, user-fetch witness INFEASIBLE; D44–D45); rev 9
[OWN.10–12] (faithful I/O INFEASIBLE §B(11b), (a′) the residue; D44 (i) → W14; D46); rev 10 [OWN.13–15] (D33–D36,
D38–D40 RULED; W13 = I/O-CLASS EVENTS `Lbl.LIo`/`ioResidueGmo`; D47–D50); rev 11 R8 (4 req.: "Spec:" lines on D41,
D45–D50; D51, D52; §B(11b) on the appendix "I/O Ordering"; FIOM clause); rev 12 R9 (SATISFIED; 2 req.: Spec lines on
D7/D19/D20 + `candSca` alignment caveat, five cite paths; s1–s4) + Stage-0 results (W5b/W5c DONE, W1/W3 PARTIAL; W1-Q, Q-W3a);
rev 13 W2 spike D7 STOP (G1–G3 redesign: `tsoShadow`/`candScaT`/`candDiskLat`, (R2′); G1-Q–G3-Q) + W3 DONE + [OWN.16] (W1-Q, Q-W3a, D41, D45 RULED);
rev 14 (2026-10-10) R10 (4 req.: G2-Q (a) mis-specified → (a′)/(a‴); W11 (iv) under (b); W5b′ shadow threading; `GraphFetchSpike` lost; s1–s5) + [OWN.17–19] (G1-Q, G3-Q, D8–D9, D19 (b) → W-RSV, D20, D42–D43, D46–D52 RULED; G2-Q re-presented);
rev 15 (2026-10-10) R11 (4 req.: (a′) + `coh` reset [R11.1] + foreign-only stamp [R11.1-alt]; W-RSV boundary clearing; `itvOf`; (F-dep) `asrc`; s1–s5) + [OWN.20] (G2-Q RULED (a′), applied CORRECTED; W-RSV-Q NEW);
rev 16 (2026-10-10) R12 (2 req.: W-RSV ghost cost → (i-a)/(i-b), census 16 rules / 25 MachCSL + 8 `Xv6/` files, L–XL [R12.1]; [OWN.21] applied, gates removed, foreign-only stamp load-bearing for (9d) [R12.2]; s1–s5) + [OWN.21–23] (G2-Q (a′) BOTH components; W-RSV-Q RULED (i-a); D19 (b) stands; no OPEN question);
rev 17 (2026-10-10) R13 (2 req.: (i-a) census + M-mode lane — 35 `wp_m_*` statements, 12 `Xv6/` files, L–XL unchanged, (i-a) stays RULED, delta recorded [R13.1]; W2's hart `LLoad`/`LStore` rows after W-COH, W1b RULED-in [R13.2]; s1–s5; Stage-1 launch set at §C top);
rev 18 (2026-10-10) R14 (3 req.: W-COH + `Weak/TsoOfPf.lean` + `Vtest`, built explicitly [R14.1]; W2's `LExStore` row after W-COH, exload instance-independent [R14.2]; W5d-G G1–G5 after W13 (M) [R14.3]; s1–s5) + [OWN.24] (Q-W5dG-seq RULED (a)); R15 SATISFIED (0 req., 6 sugg., Q-CI-Weak → [OWN.25] no CI change);
rev 19 (2026-10-11) Stage-1 RESULTS (W5b′ `TsoShadow` 996 l., W-COH, W1b + (A) `AllocprocTrace` 447 l., W5d-G G0 `GraphFetchSpike` 339 l., W2a `PfStepTsoMem` 781 l., W2b `PfStepTsoView` 807 l. DONE; W13 (E) PARTIAL) + [OWN.26] (`emSlot` = real slot tag) + [OWN.27] (W13 (E) re-sequenced (a): `projLbl` flip/`lblRealizes`/`lbAdmin` drop → (I)) + [OWN.28] (W1b pid history (A): fork-only joined history) + [OWN.29] (E-D1 disk = (a): align `virtioProg` to `serve` → **W-DISK**) + the W4 structural census [W4c] (per-KIND thread map, HSafe, `κs`, `n ≤ |st|` FALSE, F1–F8/F9) + the W13 I/O census [W13c] (rule-9 hits NONE, R5 STOP candidates NONE via L-IO, §B(11) omissions and stale names); W-DISK-Q1/Q2 OPEN;
rev 20 (2026-10-11) R16 (6 req.: W-DISK's (M4)/(M9) vs `pdevOk` → the `DWriteDev`/state-aware-`pdevEv` mechanism, W13 (I) = M [R16.1]; [OWN.30]/[OWN.31] recorded [R16.2]; W-DISK-Q1 (b) = standalone **W-DMA0** [R16.3]; W5-pre + W11 (iv)a DONE [R16.4]; F_FLUSH fact + permanent device-model strengthenings [R16.5]; `pfStepTso` signature pinned [R16.6]; s1–s6) + [OWN.30–32] (W-DISK-Q1 (b), Q2 (a), Q3 (a) RULED) + W13 (T)+(M) DONE (`GraphFabResidue.lean`); no OPEN owner question.
rev 21 (2026-10-11) R17 (4 req.: W-DISK FOLDING RULE (α) abort + single-burst invariant [R17.1] (+ [R17.1-alt] `pre`); `pfStepTso` pinned as Lean [R17.2] (+ [R17.2-alt] five hypotheses); `devQuiet` start-state hypothesis through Supply/Fab/Lin2/FabInd [R17.3]; sequential pf disk named §B(11) (viii) [R17.4]; s1–s5, s7) + [OWN.33] (W-DISK-Q4 RULED (c)); no OPEN owner question.
rev 22 (2026-10-11) R18 (4 req., all W-DISK binding text: payload path (A) — `cacheReq` folded, `R-dev` on `cacheView`, `completeOkPf` [R18.1]; interim `gfexecConf` `LDev`-free-disk-row clause, Fab family ≠ Supply family [R18.2]; in-flight pre-check first in `pre`, `R-dev` up to `pre₁` on the OUT capture segment, ABORT 1 → 0 [R18.3]; state-dependent `pa`/`bs`, snapshots where `serve` takes them [R18.4]; s2–s6; s1 deferred to W2 CLOSE); no OPEN owner question.
rev 23 (2026-10-11) R19 (3 req., all W-DISK binding text: pf drains at the gate (`drainAll`), `completeOk` verbatim, `R-dev` FULL equality, `cache = []` outside capture → gate [R19.1]; state-receiving `DWriteDev` continuation, the idx write keeps `ui`/`c`, `DM.DPop` named [R19.2]; `pre₁` conditional on the `taken` guard [R19.3]; s1–s5) + W2 CLOSE DONE (`Weak/PfStepTso.lean`, the REPAIRED statement; item (3) → Q-FIARM) + [OWN.34] (W-DMA0 via option (A)); OPEN: Q-FIARM.
rev 24 (2026-10-11) R20 (3 req.: reset-absorbing `pre₁` [R20.1]; zero-length data node ELIDED, `n ≠ 0` kept [R20.2]; W11 (iv)b LANDED + Names [R20.3]; s1–s5) + [OWN.35] (Q-FIARM RULED (b)+(a′): `sailCycleOrder` + W-SCO) + W-DMA0, W4 F1–F8 (`MachOfPf.lean`), W11 (iv)b (`RvwmoXv6ScaT.lean`) DONE; no OPEN owner question.
rev 25 (2026-10-11) R21 (4 req.: W8 → W8-design spike + lane [R21.1]; Stage-2 `linCandScaT` on the normalized `GD'`, W12 (1) producer [R21.2]; IN 1 → 5, single-burst invariant dropped, F9 re-proves every `SimRel.dev` consumer [R21.3]; W5 CORE plumbing, not registered [R21.4]; s1–s4) + [OWN.36] (Q-W8-lane RULED (α): W8 ledger serial MachCSL before W-RSV); no OPEN owner question.
rev 26 (2026-10-11) R22 (3 req.: W8-design pins feeding (f1)/(f2)/(f3) + root (r1)/(r2) [R22.1]; `gfDev ↔ gisIo ∨ dvi ≠ dvo` [R22.2]; `Lang.lean` cite authority [R22.3]; s1–s5).
rev 27 (2026-10-11) R23 (2 req.: W8 (i) dynamic owner — kernel stacks migrate at `swtch`, handoff under `p->lock` [R23.1]; rev-25 `gfDev` formula + "FABRIC MOVES" purged [R23.2]; s1–s5); SATISFIED by R24 (0 req., 6 sugg. folded into W8-design).
rev 28 (2026-10-12) W-DISK DONE (`VirtioProg.lean` rewritten, ten-arm `pdiskProg`/`ediskStep`, `ewpDisk*` rules, `pfDWriteDevRowMem`/`pfDSkipRowMem`/`rowDiskDevMove`, `devQuiet`/`epsInitQuiet`, interim `gfexecConf` clause; deviations d1–d4) + W8-design DONE (`notes/W8-design.md`: export `xv6AccessDisc` pinned, PStack buckets BOOT 82/PROC 747/BOTH 192/DEAD 13, feeds (f1)/(f2)/(f3′)/(f2-ctx) sized, W8-β′, R-ctx, root (r2), the `holding+0x12` race) + [OWN.37] (Q-W8-feed RULED (a): W8-β′ → R-ctx → W8 (f2-ctx), fallback (f1) per part; root (r2) `xv6DiscAdequacy_closed`); W4 F9 unblocked; Q-HOLDING REPORT; no OPEN owner question.
rev 29 (2026-10-12) R25 (3 req.: `Cust.pte` + `pteDiscAt` + the `chainOkAt` exemption [R25.1]; W8-β′ pinned to three Lean statements incl. the (r2) twin [R25.2]; R-ctx 21 files [R25.3]; s1–s6); rev 30 (2026-10-12) R26 (2 req., both W8-β′ brief text: registration lemma `xv6LockWord σ b t → b ∈ reg`, not its FALSE converse [R26.1]; `reg`'s home `rsvName` + the reserving STEP [R26.2], with [R26.2-alt] static regions registered at the `PowerOn` mint (the hook `◇ ⌜phi⌝` cannot see a mid-run ghost registration), pipe locks → (f2-ctx); s1–s6); no OPEN owner question; SATISFIED by R27 (0 req., 7 sugg.);
rev 31 (2026-10-12) W4 F9 DONE (`Weak/MachOfPfDisk.lean` 1290 + `MachOfPf.lean` 2979: `simDisk`, `R-dev` = `diskSide`/`devAgree`, `cacheWf`, `devrt` untracked, no disk hypothesis) + W5 CORE DONE (`Weak/SrvwmoXv6Adequacy.lean` 318: `srvwmoXv6M1Core` = premises + `g0` boot facts + `sailCycleOrder`; M1 PROVED, registration = the W5 CLOSE-OUT) + the `enumToBitVec` import-hygiene fix + R-ctx DONE (`notes/W8-Rctx.md`: F0 per-author vector bound, 31 rows, none RESISTS, X1–X5, 4 outside sites + 31 consumer files, the `"log"` lock) + [OWN.38] (Q-R1 (a) vector bound; W8 (f2-ctx) ≈ 6.5–9.5k, 12 MachCSL + ≈ 52 `Xv6/`, 3–4 rebuilds) + [OWN.39] (Q-R2 (a) user PTEs under the `pte-key` arm) + [OWN.40] (OUT capture STALLS on a wrapping buffer, §B(11) (x)); OPEN: Q-RSV-order.
rev 32 (2026-10-12) R28 (5 req., all S text: W5 CLOSE-OUT's exact `baseline-weak.json` entry [R28.1]; W-SCO's `Hyps.fi` widened to `cut`'s shape + `fetchIsImage` [R28.2]; shared-file LANDING ORDER CLOSE-OUT → W-SCO → W5d [R28.3]; `fok` stays 5-ary, `itvOf` via `pfStepFactsT` [R28.4]; lane order + W-RSV Launch (rev 32) [R28.5]; s1–s8 adopted) + [OWN.41] (Q-RSV-order RULED (b): W8-β′ → W-RSV → W8 (f2-ctx)).
rev 33 (2026-10-12) R29 (2 req., both S text: W5d's M2 cut clause carried by the new trivially-instantiated parameter `fcutT` as `pfRunST.snoc`'s third fact `pfCutFactsT` — M1's statement TEXT changes, its entry does not; W5d's parameter threading is its FIRST commit, after W-SCO's `Hyps.fi` widening [R29.1]; the stale serial-lane sentence → W8-β′ → W-RSV → W8 (f2-ctx) [R29.2]; s1 (`fetchIsImage` PAST-fetch recipe, NOTE in W-SCO) + s5 adopted; s2/s3 deferred to the running workers' merge review).
rev 34 (2026-10-12) R30 (1 req., S text: `itvOf` free in `srvwmoXv6M2Premises`, its cut/recurrence/frame carried by a second per-index parameter `fcutE`, `True` at M1 — no shared definition gains a non-trivial conjunct [R30.1]; s1/s3/s6 adopted).
rev 35 (2026-10-12) R31 (1 req.: the M2 `fcutE` instance carries the `fiArm` STATE — route (i), a free `fiOf` beside `itvOf`, DELIVERED in W5d's file [R31.1]; s1–s3 applied) + RESULTS (W5 CLOSE-OUT → **M1 DONE**, registered; W5d M2 core `Weak/PfRunUnpinned.lean` in w5; W-SCO shape (0) + generic half `Weak/SailCycleOrderK.lean`, per-word half blocked; W13 (I) realization half, bundle half blocked) + [OWN.42] (W-SCO = (A): `cycleOkAll` for every instruction, `sailCycleOrder` a theorem for all text) + [OWN.43] (W13 (I): `gfDev` membership by fabric CONTACT, `hblkQ` folding generalized) + [OWN.44] (next batch approved); [R29.s2][R29.s3][R30.s4] closed.
rev 36 (2026-10-12) R32 (4 req.: `sailCycleOrder` FALSE over arbitrary `σ0` — restated under `wbootFacts σ0`, `good` gains a register filter, `cycleOkBoot` replaces `cycleOkAll`, M1/M2 VACUOUS until W-SCO (A)'s commit 1 [R32.1] (landed rev 39); w5/W-SCO files MERGED [R32.2]; `emZifencei` collision → launch addendum [R32.3]; W-SCO (A) brief rewritten with the whole cycle [R32.4]; s1–s4, s6–s8) + Q-SCO-PMA (provisionally (α)) + W13 (I) bundle half LAUNCHED.
rev 37 (2026-10-12) R33 (1 req.: `Rboot` ALSO pins `htif_tohost_base = none` — `within_mmio_readable`/`htif_load` answer an ifetch with no `.memRead` node [R33.1], applied at W-SCO (A)'s launch; s2–s5 adopted) + [OWN.45] (Q-SCO-PMA RULED (α)) + RESULTS (W13 (I) DONE, W8-β′ DONE, W-RSV DONE) + W8 (f2-ctx) LAUNCHABLE (§C top); OPEN owner questions: NONE.
rev 38 (2026-10-12) R34 (3 req., all S text in the W8 (f2-ctx) launch paragraph — (5) FOUR of six conjuncts, `cpuProcDiscAt`/`utextDiscAt` → W8 (f3-rest) [R34.1]; `W8-Rctx.md` carve-out for [OWN.39]/[OWN.38]/[OWN.41] [R34.2]; ghost plumbing route (A) in Files, 13 MachCSL [R34.3]; applied at launch; s1–s6 adopted) + RESULTS (W8 (f2-ctx) S1 MERGED: `ChainDefs`/`ChainCert`, worker stopped green with 3 findings) + Q-F2-PIPEHOP/Q-F2-BOOTGATE provisional (a) + RELAUNCH W8 (f2-ctx) + W8 (f3-rest) named; OPEN owner questions: Q-F2-PIPEHOP, Q-F2-BOOTGATE.
rev 40 (2026-10-13) R36 (4 req., all plan text on the (f2-ctx) lane: RESULTS (S1′ + S2-pre MERGED, deviations D1–D4, findings F-A–F-D) + RELAUNCH 2 deciding F-B (guard `j ≠ w`) and F-C ((i) as rows first, (ii) fallback) [R36.1]; `pipeLockNameStr` = `"digits"`, not `"pipe"` → `KS.«pipe»`, S0 [R36.2]; the merged (a″) name-word window is a DEVIATION from RULED (a′), word-shaped hop entries + windowed `lockRegionOk`, provisional pending Q-F2-PIPEHOP-2 [R36.3]; F-C (i) rows before wiring, 27 client files, (ii) sized [R36.4]; s1–s6 adopted) + RESULTS (**M2 CLOSE DONE** — `Weak.srvwmoXv6M2` registered; M1 + M2 DONE, Stage 1b CLOSED); OPEN owner question: Q-F2-PIPEHOP-2 (provisionally (a″+shape)).
rev 39 (2026-10-13) R35 (2 req., both S text: Q-F2-PIPEHOP (a) → (a′) time-indexed `isLk b r` + `pipeLockAt` [R35.1]; Q-F2-BOOTGATE (a) + history-aware reserved store over `rsvStoreOk`, `started`'s cell/carve moved [R35.2]; applied at launch in the (f2-ctx) continuation brief; s1–s6 adopted) + [OWN.46] (Q-F2-PIPEHOP = (a) as amended = (a′)) + [OWN.47] (Q-F2-BOOTGATE = (a) as amended) + RESULTS (W-SCO (A) DONE: `sailCycleOrder_holds` a THEOREM, M1/M2 non-vacuous, `Weak.srvwmoXv6M1` REGISTERED, `srvwmoXv6M2` stated) + M2 CLOSE launch paragraph (LAUNCHABLE) + the first Stage 2 launch set (W12 (+W12b) ∥ W13 (F-dep) ∥ W13 (L)); OPEN owner questions: NONE.
rev 46 (2026-10-13) RESULTS (FabInd-S, W13 (W) part 1, W9a inc. 1, W5d-G G1 (pinned `gfexecConfIO` + `gfexecConfZ` until G6), W8 (f2-ctx) S3 MERGED; W13 (K-cat) STOPPED — riscv.cat counterexample `kcatCex`; S4 DONE in w2 at THREE of six) + [OWN.56] (batch 3) + [OWN.57] (pte window → (c)) + [OWN.58] (weekly cap lifted) + W8 (pte-ghost) launch paragraph + F-X (greps not acceptance) + roadmap (W11 (1)–(5), W14 `usedElemGateOk`, G6, (K-cat′)) + 6 owner Qs (Q-KCAT, Q-W9A, Q-F-RACY, Q-F-DISKTAIL, Q-PTEDISC, Q-DYNLKDISC) + (H3′) in §B(11).
rev 45 (2026-10-13) R41 (5 req., 1 alt: Q-F2-PTE-WINDOW's window = EVERY page-table page of the dying table, each `kfree` → clear of its pointer, bound not a page count, junk target `0x4040404040000`, (b″) closes interior windows too [R41.1] — RELAUNCH 5's running paragraph untouched, docstring correction as an addendum [R41.1-alt]; W5d-G = full-cone rebuild + `audit.sh --weak --build` per increment, `Gdexec.gdFetch` a structure change [R41.2]; FabInd-S before G3 (`KillIO` shared) [R41.3]; (W)'s `gfDevWIo` disk half = named `usedElemGateOk` for W14 [R41.4]; Q-BATCH-3 in the owner format + third option [R41.5]; s1–s8 adopted); OPEN owner questions: Q-F2-PTE-WINDOW (provisionally (a), corrected bound), Q-BATCH-3.
rev 44 (2026-10-13) R40 (1 req., 0 alt: W13 (R3′) keeps `gfDevWIo` as the named premise, option (α), applied at launch [R40.1]; s1–s7 adopted) + RESULTS (W13 (R3′), W11 (iv)c, D35-fix, W13 (K), W13 (F-dep), W8 (f2-ctx) S3-a/S3-b/S3-c0 ALL MERGED) + [OWN.55] (second batch approved) + (K)'s open items placed (W11 (i); NEW W13 (K-cat); NEW FabInd-S) + the THIRD Stage 2 launch set (W5d-G G1–G5 ∥ W9a ∥ W13 (W)) + W8 (f2-ctx) RELAUNCH 5 text; OPEN owner questions: Q-F2-PTE-WINDOW (provisionally (a)), Q-BATCH-3.
rev 43 (2026-10-13) R39 (3 req., 0 alt: D35-fix list — `grcscGrelAcq :250` FALSE/deleted, `CatLinWit`/`CatLinHull` added, `lblRenRcsc` → `Norm`, `lblTswapRcsc`, `racyD`'s meaning widens via `gppo` [R39.1]; D35-fix ∩ (F-dep) = {`WeakRvwmoAdm`}, `CatLinChain` → (F-dep), applied at launch [R39.2]; (R3′) fabric arm over `gmem` members, `gfDevAnc` a NAMED premise, the `DFence`/silent-`DWriteDev` counter-model [R39.3]; s1–s5 adopted) + W13 (F-dep) RELAUNCHED (A1) w3 + (f2-ctx) RELAUNCH 3 RUNNING w2; no new owner question.
rev 42 (2026-10-13) RESULTS (W12 + W12b, W13 (L) DONE/MERGED; (f2-ctx) S0 + S2 MERGED, RELAUNCH 3) + [OWN.52] Q-FDEP (A1) → (F-dep) relaunches under (A1) + [OWN.53] Q-L-R3 (a) → W13 (R3′) (S; `gfDevGmo` a theorem, `gfDevWIo` → `gfDevAnc`) + [OWN.54] D35-rule7 (a) → D35-fix (`lbRcsc := aq || rl`, RVWMO⁻ rule 7 in step, `grelAcqGmoC` dropped, re-audit) + the SECOND Stage 2 launch set ((K)+(R3′) ∥ D35-fix ∥ W11 (iv)c; W5d-G next, G1/G2/G5 after (F-dep) (1), G3/G4 after (K)).
rev 41 (2026-10-13) R38 (6 req., all on W13 (F-dep)'s graph side: option A — `gtdepsWf` admits I/O-read sources / I/O-write targets, `forgetDeps`/`gtAd`/`gsrcT` filter to RAM endpoints so `catTAd`/`catTForgetAxioms`/`catADOfCatT`/the LB roots keep their statements (premise weakens) [R38.1]; the untagged `dstep` STAYS inert, `dstepT` only, `WeakRvwmoConf` not an owner, `WeakPromise.lean:89` + `AxSpinGate.lean` are [R38.2]; the `LDev` payload sweep ≈ 180 sites / 35 files as increment (1) alone, (F-dep) M–L ≈ 1k [R38.3]; Q-FDEP provisional (A2), (A1) recommended [R38.4]; header/launch text [R38.5]; the W12 course note [R38.6]; s1–s5 adopted) + [OWN.48]–[OWN.51] (batch LAUNCHED; Q-F2-PIPEHOP-2 = (a′-r); F-C = (i); weekly cap) + RESULTS (W13 (F-dep) STOPPED GREEN before any edit, `PROGRESS-W13Fdep.md`); OPEN owner question: Q-FDEP.

**The kernel [OWN.4][R1.9]: xv6-riscv `b72cbac1`, branch `verified`** (`notes/STATUS.md:8-11`, `README.md:89-90`)
= upstream plus (a) a per-process root (`p->root`, `sys_chroot`, `igetroot`, root-aware `dirlookup`/walk) and
(b) upstream's post-`ded23f2` allocpid — bounded counter `PIDMAX = 1000` (`Xv6/ProcGeom.lean:80`) with a 64-slot
liveness scan, inlined by gcc into `allocproc+0x38..+0x94` (`claude-notes/kernel-defects.md:224-231`) — not the
textbook monotone `nextpid`.  Image `Xv6/KernelImage.lean` by `tools/dump_kernel.py`.

Advisory only; read-only survey of `../xv6iris-weak` (`Weak/`, `Xv6/`, `MachCSL/`, `notes/weak-memory-*.md`,
`claude-notes/{completed,design}/*weak*`).  Sizes: S ≤ 300 lines, M ≤ 800, L ≤ 2k, XL = multi-week / many files.
Unconfirmed claims are **unverified**.  Spike scratch files (build, no `sorry`): `Weak/CatOfMinusSpike.lean` (399),
`Weak/W13Spike.lean` (145), **`Weak/TsoOfPf.lean` (312 after W-COH, MERGED, `Weak.lean:624`; `propext, Classical.choice,
Quot.sound`) — the W2 spike's Lean: `g1Run`/`g1Shape`/`g1Tso`/`tsoAqPairTv`/`tsoExclRv` (G1), `g2Run`/`g2Shape`/
`g2Tso`/`tsoAfterLoadCoh :179` (RESTATED for the foreign-only stamp), `g2TsoSched :251`, the own-store counterexample
`m0 :270`/`g2OwnLog :272` (W-COH's acceptance), `fenceRow :303`, `histOf :62` (`R`-hist) [W2s]**, **`Weak/
GraphFetchSpike.lean` (339 lines) — RE-CREATED by W5d-G G0 from `notes/W5dG-spike.md` (the 2026-10-09 original was lost
unsnapshotted [R10.4][OWN.18]); its re-creation record R1–R10 lives in the file header, reviewed `notes/W5dG-G0-review.md`
(OK, carry-overs in §C W5d-G G1); every `GraphFetchSpike.lean:N` cite below is now to THIS file**; `W13Spike.lean` §3 is
SUPERSEDED (§A(†)).  Stage-1 files (merged 2026-10-11): `Weak/TsoShadow.lean` (996), `Weak/PfStepTsoMem.lean` (781),
`Weak/PfStepTsoView.lean` (807), `Xv6/AllocprocTrace.lean` (447), [R16.4] `Weak/SrvwmoXv6Witness.lean` (805 after
W5-pre), `Weak/RvwmoXv6Sca.lean` (327, W11 (iv)a), `Weak/GraphFabResidue.lean` (268, W13 (T); `Weak.lean:629-630`);
censuses `notes/W4-structural-census.md` [W4c] and `notes/W13-io-census.md` [W13c] (read-only, not plan amendments —
folded in HERE).

## 0. The two findings that reshape the question

**F1. allocproc is ALREADY fully verified in this tree — on a weak-memory machine, not on SC.**
`Xv6.Allocproc : ALLOCPROC` (`Xv6/LinkAllocproc.lean:14-16`, proof `Xv6/ProofAllocproc.lean:3623-3639`, 3.6k
lines; spec `Xv6/SpecAllocproc.lean:118` `allocprocPost`, `:204` `wp_allocproc_body`) covers the whole function on
the real image (0x80001b72..0x80001c72): the `proc[]` scan with `acquire`/`release` per slot (interrupts may be ON,
migrating hart via `wpNext`), the inlined allocpid under `pid_lock` with the 64-word collision scan (Löb-closed,
`PidLock.pidLedger`/`pidTie`, `Xv6/PidLock.lean:88,113`), `kalloc`, `proc_pagetable` with PTE writes into fresh OWNED
pages (`pptPost`), `memset`, `ra = forkret`, `sp = kstack + PGSIZE`, both failure tails through `freeproc`,
`p->pid`/`p->state` as `p->lock`-protected cells (`procHeld`).  Callees verified too (≈ 10.7k lines).  In the cone
of the audited roots (`tools/ci/roots.txt:6` `xv6FsAdequacy_closed`, via `Xv6/LinkSyscall.lean:84`/`LinkMain.lean:53`),
baseline (`tools/audit/baseline.json:11-14`) axioms `propext`/`Classical.choice`/`Quot.sound` + exactly three opaques
`LeanRV64D.Functions.xv6_resv_is_valid`, `…xv6_resv_matches`, `MachCSL.bootImageSealed` [R7.s6].

The memory model under all of that is `MachCSL.TsoMem` (`MachCSL/TsoMem.lean:1-40`; `relaxed-rr.md`): one total
store order with per-byte write histories, per-hart view FLOORS (load–load reordering), store forwarding by author,
store buffering, `fencePost` (`:489`; `fence rw,w`/`w,w`/`r,w` are NO-OPS, `fenceDrains`/`fenceAcq :500-505` [R16.s1]), `.aq` AMOs, LR/SC
reservations, a non-coherent i-cache view `itv` + `fence.i`.  **What it forbids that RVWMO allows** [R1.7]: (i)
store–store reordering and load buffering (stores never early) — the weak tier's sRVWMO residue (rule 14,
`Weak/WeakAxiomatic3.lean:2050-2071`; litmus divergences LB and reader-fence-only MP, `Weak/WeakSrvwmoLitmus.lean:
1663-1695`), checked by reading: nothing relates TsoMem to `srvwmoConsistent`, and §B(10) does not need it [R2.s2];
(ii) **reservation serialisation — GONE (W-RSV DONE 2026-10-12, rev 37: the reservation is cleared at the instruction boundary,
`Lang.lean:543`; record)**: a foreign store or exclusive read overlapping a held reservation is BLOCKED
(`blockedStep`, `MachCSL/Lang.lean:366-378,395-403`; DMA `anyReserve`, `:539,562`); the reservation persists until the
holder's next store of ANY address (`:147-153`) or a blocked exclusive read, surviving fences (`:155-163`); RVWMO's
atomicity axiom constrains only SUCCESSFUL pairs (D19 Spec); the kernel uses only `amoswap.w.aq` (`Xv6/ProofAcquire.
lean:5`), USER code may `lr`/`sc`.  What the reservation does NOT do [R11.s2]: it never decides an SC's success — the
opaque `xv6_resv_is_valid` does (`UWait.lean:21-26`, `Xv6/UserMemLrsc.lean:9-13`; `MState.store` never reads
`σ.resv cpu`, `Lang.lean:147-153,372-378`), so TODAY's LR/SC is already WEAKER than Zalrsc (an SC may succeed over an
intervening store; sound) and W-RSV removes only the blocking.  **D19 RULED (b) [OWN.19], form (i-a) RULED [OWN.22][OWN.23]: (ii) is
PLANNED OUT — once §C W-RSV lands, `σ.resv cpu` is CLEARED at the hart's instruction boundary (`hartStep .pure`,
`Lang.lean:535`; the pf twin ALREADY does this: `instrPost … wRes := none`, `Weak/WeakMem.lean:720-721`), so a
reservation blocks only within its issuing instruction (= the AMO's atomicity, FAITHFUL; Zalrsc permits invalidation
at any time); the blocking ARMS stay (firing only against in-flight reservations [R12.s4]); the ghost side threads the
hart's reservation fragment through the cycle rules and their callers — L–XL, with W8 (f2-ctx) [OWN.37] the largest
serial MachCSL items [R12.1]; this list then reads "(i) + (iii)" and the "Honestly" line below drops "reservation serialisation"**;
**(iii) [W2s] FOOTPRINT coherence stamping — LANDED OUT by W-COH (2026-10-11): `HRead.afterLoad` now stamps a byte's
`coh` with its source timestamp ONLY for a FOREIGN-authored source (`Hist.readEnt`/`Hist.readSrc`, `MachCSL/TsoMem.
lean:127-136`; `FlatMem.loadSrcs :320`; `HRead.afterLoad :354`), and `MState.store` RESETS its footprint
(`HRead.resetCoh :361`, `Lang.lean:156`) — exactly riscv.cat rule 2 with both exemptions; the record below is what
TsoMem WAS**.  THREE components beyond riscv.cat rule 2 (`gppo2`, `Weak/AxGraphCat.
lean:151-156`: same-byte reads of DIFFERENT sources with NO same-hart write to the byte po-between) [R11.1][R11.1-alt]:
(1) a plain load stamps EVERY byte of its footprint with the load's view (`HRead.afterLoad`, `MachCSL/TsoMem.lean:268`;
the `cohOk` premise, `Lang.lean:365`), so two overlapping loads of DIFFERENT footprints are ordered even when the
shared byte reads the SAME write — witness `TsoOfPf.g2Run`/`g2Tso` (cat-consistent BY INSPECTION, `W2-spike.md:36-38`,
not in Lean [R10.s3]; no TsoMem schedule), mixed-size (N10-adjacent); (2) the stamp SURVIVES the hart's own store to
the byte (`MState.store` touches `hr` only by `clearAcq`, `Lang.lean:152`, `TsoMem.lean:277`) — rule 2's
`po-loc-no-w` exemption has no twin; (3) a byte read from the hart's OWN store is stamped too (own stores are visible
at any view, `HEnt.visible :116-118`, and cat puts no gmo constraint on them).  Hence G2-Q — RULED (a′) [OWN.20] in
the form correcting all three, BOTH components CONFIRMED/RULED [OWN.21][OWN.23] (§D).  NOT strengthenings, recorded against the spike:
**G1** (TsoMem's `.aq` floor = the AMO WRITE's position, `Lang.lean:136,151`; WeakMem's `max(wVrNew, t)` = the READ's
source, `WeakMem.lean:608-626,834`) is an ENCODING/realizability gap of the position-preserving log identification —
rule 5 (`gacqPo`, `WeakRvwmoGraph.lean:214`) puts the AMO gmo-before every later access of the hart, so once the log
is gmo-ordered (Stage 2, `ptraceRel ⊇ gmo|W`) "floor = AMO position" is cat-FAITHFUL (§D G1-Q); **G3** (DMA reads at
the TOP, `dmaView`, `Lang.lean:189`) is the DEVICE MODEL's strengthening over the appendix's DEVICE sentence (§B(11b)
F6, already named), a realizability gap on the pf DISK ROW (`DRead` = `LLoad aq false`, `WeakEvInst.lean:491-494` [R23.s3]).
**RESOLVED — W-DISK DONE 2026-10-12 (rev 28; the paragraph is the RECORD of what the pf program WAS).  The pf DISK PROGRAM
[W4c] (the pre-W-DISK `virtioProg :606`, a Rocq-literal port RECORDED as drift
from MachCSL's `Virtio.body`/`serve`, header deviation 2 `:99-112`) deviates from the device model of record in FOUR
unconditional ways — the used element as TWO 4-byte writes with `len = r.len` (MachCSL: ONE 8-byte write, `usedLen` =
bytes written, `Virtio.lean:382,546-548`; virtio 1.x: "the number of bytes written into the device-writable portion" —
MachCSL FAITHFUL, pf UNFAITHFUL), status UNSUPP for FLUSH (`vstatus :557`; MachCSL `statusOf :377` OK — [R16.5] xv6's
driver CLEARS `F_FLUSH` (`Xv6/SpecVirtioDiskInit.lean:10`; `ProofVirtioDiskInit.lean:935` DRIVER_FEATURES := 0), so a
FLUSH would be UN-negotiated and the device's answer is spec-UNSPECIFIED: both are model choices, vacuous — xv6 never
issues FLUSH), `DWild` writes anywhere on a malformed chain (MachCSL `stall`; spec: driver MUST
NOT, device behaviour unspecified), and the ISR/`usedIdx` move at a separate COMMIT after the used-idx write (MachCSL:
fused into that write, `Virtio.lean:552-555`) — plus five conditional ones ((M5)–(M9), §C W-DISK).  E-D1 RULED (a)
[OWN.29]: §C **W-DISK** ALIGNED `virtioProg` to `serve` (LANDED: `Weak/VirtioProg.lean:438`, the (M1)–(M9) table with
marks and the "moves the fabric?" column in its header), so there is now ONE device model (MachCSL's) and these deviations
have LEFT the honesty lists; §B(11)'s "Machine-model choices" keep MachCSL's own device-model strengthenings PERMANENTLY
[R16.5].**
Dependency order (ppo 9–13) is absent in TsoMem — the sound direction.  Honestly (today, after W-COH, W-DISK and W-RSV [rev 37]): "xv6 on
sRVWMO" (reservation serialisation GONE — W-RSV DONE 2026-10-12) — the pf disk program's drift is GONE (W-DISK DONE 2026-10-12); **[rev 31] and
this sentence is now a THEOREM for kernel-only, pinned candidates — M1's `srvwmoXv6M1Core` (`Weak/SrvwmoXv6Adequacy.lean:276`,
§A), under the candidate restrictions `candKfetch`/`candScaT`/`candDiskLat` — and, since rev 39, WITHOUT the Sail-cycle premise:
`Weak.srvwmoXv6M1` (`SailCycleOrderCycle.lean:148`, REGISTERED), `sailCycleOrder` being a THEOREM (`sailCycleOrder_holds`)**.  **Under [OWN.2] this is an INPUT,
not the result**: the published theorem is at RVWMO proper, by robustness (§B(9)).

**F2. The AxSL tier cannot reach allocproc** [OWN.1: retired].  Theorem 2 (`allocpidOpen2`,
`Weak/AxSpinT2b2.lean:325`) covers ≈ 230 dynamic instructions at ≥ 57k lines [R1.s1]; allocproc's footprint is
≈ 120k with four more lock protocols, the freelist, private page-table pages.  Theorem 2 stays an audited
riscv.cat-tier validation of the handle-based lock protocol; do NOT extend it.

## A. The target theorem

**What "credible for xv6" requires** (an xv6/weak-memory expert's checklist):
1. the real kernel binary, named above [OWN.4]; every callee real, failure paths included.  The caller discharges
   `wp_allocproc_body`'s premises (`Xv6/SpecAllocproc.lean:204-224`: `k.tier = KTier.kpt`, `allocprocSlots (= 48)
   ≤ k.avail`, `k.noff + 2 < 2^31`, `"kmem"/"nextpid"/"proc" ∉ k.locks`, `procsInv`, the two `isLock`s,
   `kallocAvail γk on`, `procsAvailAt Γ pav tk`, `□ (killCred -∗ Q (-1))`, `actLend`) — kernel-state facts only;
2. harts [R1.1]: **exactly `NCPU = 8`, all booted** (`MachCSL/TsoMem.lean:57`; `hartAgent`/`diskAgent`/`ifetchAgent :62-64` [R16.s1]; `PowerOn` forks `cpus =
   List.finRange NCPU`, `MachCSL/Lang.lean:315-320`; `riscvPowerAdequacy`, `MachCSL/Adequacy.lean:383`) — fewer
   harts NOT covered (D8).  The other harts run ARBITRARY xv6 kernel/user code, interrupts on where xv6 allows
   them, devices as modelled (2 UARTs, PLIC, virtio with DMA as a store-order agent) — on route (M); at the graph
   tier the rows are `xN σ0 = (epsInit σ0).length = NCPU + 1` (`Capstone.lean:94`): 8 harts PLUS the disk agent's
   row `.PDisk none` (`WeakEvCapstone.lean:1027`, booted by `xboot`, `Capstone.lean:90-91`) [R7.3][R5.s5][R5.1];
3. memory [OWN.2]: **RVWMO as the ISA defines it — the TAGGED cat model `rvwmoCatConsistentT GT` over `GdexecT`
   (`Weak/AxDeps.lean:208-211`: `gwf ∧ gppoCatTGmo ∧ gloadValue ∧ gatomicity ∧ gtdepsWf ∧ gtdepsGmo`, rule 12 over
   `gtAd` = the addr/data edges only — **[OWN.52] RULED (A1), rev 42: `gppoCatT` ranges over `gtAdFull` (the addr/data edges into RAM writes from
   ANY read, I/O loads included — FAITHFUL to riscv.cat's `r12`; W13 (F-dep) (0)); the chain's projections `forget`/`gtAd` keep RAM sources**
   (rev 41's provisional (A2) — the `[IoR];(addr|data);[W];rfi;[R]` instances omitted — is RETIRED before any code took it); rules 1–5, 7, 12;
   omits 6, 8; **rule 7 = riscv.cat's `[RCsc];po;[RCsc]` with RCsc = EVERY aq/rl-annotated LR/SC/AMO (herd `riscv-defs.cat`: `RCsc = (Acq|Rel|AcqRel)
   & (EX|X)`) — [OWN.54] rev 42: the tree's `lbRcsc` (both bits, `AxGraphCat.lean:143`) is NARROWER, fixed by D35-fix (§C top)**; fidelity by litmus,
   `Weak/AxLitmus.lean:29`)** [R6.1].  **NOT the untagged `rvwmoCatConsistent` (`Weak/AxGraphCat.lean:191-194`)**:
   its `gppo12` ranges over the untagged `gdDeps` and so also orders `ctrl;[W];rfi;[R]`, which riscv.cat does NOT —
   the tree calls it "UNSOUND for safety" (`AxDeps.lean:12-18`), machine-checked by `twCatT :876` with
   `twNotCatForget :883`; `catTOfCat` goes cat→tagged, the converse fails (`:22-27`).  The chain runs on `forget GT`
   (W12 spike F1; D33 RULED (a) [OWN.13]).  **I/O accesses are events of the rows** [OWN.14]: `gmem` (hence gmo,
   `gwf`'s membership clause, `Graph.lean:169-171`) includes the new `Lbl.LIo` labels; ppo applies to them as
   riscv.cat is written (§B(11)) **and [R38.1] the tagged well-formedness `gtdepsWf` ADMITS I/O-read sources and I/O-write targets**
   ((F-dep) (0a): `lbIsR ∨ lbIsIoRd` / `lbIsW ∨ lbIsIoWr`; `.dev` events in neither — until it lands, the D50 (b) edges make the premise
   unsatisfiable on I/O rows); their values are device-supplied (no `lbRd`, so `gloadValue`/`grf`/`gfr` are vacuous
   for them BY CONSTRUCTION — the appendix "I/O Ordering": "For I/O, the load value axiom and atomicity axiom in
   general do not apply" [R8.s1]).  W→W reordering and load buffering ALLOWED; every strengthening NAMED;
4. page tables live: shared kernel table with concurrent hardware A/D write-back (`MachCSL/KptInv.lean:39,85`;
   TLB `MachCSL/UTlb.lean`; in W8's export it lands as `pteDiscAt`, §C W8 [R25.1]; **[rev 46] S4 did NOT land it — not derivable from the state interpretation, Q-PTEDISC**), fresh user table private until published;
5. the conclusion is functional AND safety [R1.2][R1.9]: returned slot `&proc[j]`, `j < NPROC`, `p->lock` held,
   `state = USED`, `pid ∈ [1, PIDMAX]` distinct from every live pid, fresh trapframe page (`kalloc`'s fill of
   `5`, `Xv6/SpecKalloc.lean:69`, via `procPrivNocwd`, `SpecAllocproc.lean:131`), fresh user table with
   trampoline + trapframe, context `[forkret, kstack+PGSIZE, 0×12]`; or `0` with the lock released and everything
   freed; **no hart ever stuck** (`Reducible`); all kernel invariants preserved — i.e. exactly `allocprocPost`.
   **Panics are NOT excluded** (`panic` is a bare `wpLoop`, `Xv6/SpecPanic.lean:11-14`), **nor the two reducible
   spin arms** [R2.4]: `blockedStep` and the weak retry self-loop of a lost exclusive pair
   (`Weak/WeakEvInst.lean:360-364`) — BOTH remain under W-RSV (`blockedStep`'s arms stay, firing only against
   IN-FLIGHT reservations; the caveat must not be read as "blocking is gone") [R12.s4].  "never panics" = "no `panic:` bytes in the UART trace" (`uartSentSub`,
   `Xv6/UartTrace.lean:182`), M–L, new work — D9.  **Caveat until W14 lands (D44 RULED (i) [OWN.11])** [R7.4b]: the
   header says "non-vacuity certified to the first UART store / disk COMMIT" (W13-wit); REACHING `allocproc` is W14;
6. axioms `propext`/`Classical.choice`/`Quot.sound` + `bv_decide` certificates + the three opaques
   (`tools/audit/baseline.json:11-14`), no `sorry`; trusted base named: Sail model (its cycle-order fact `sailCycleOrder` was a NAMED PREMISE
   [OWN.35] §B(11) — **[OWN.42][rev 35] W-SCO (A) PROVES it for every instruction (`SailCycleOrderK.sailCycleOrderOfCycle`
   from `cycleOkBoot` [R32.1]), after which it is a THEOREM and NOT a trusted item; [R32.1] it is TRUE of the model FROM THIS
   PLATFORM'S RESET (the boot PMA table forbids instruction fetch from I/O regions and the HTIF window is disabled [R33.1]) and FALSE over arbitrary register files, so it is
   STATED under `wbootFacts σ0` (Q-SCO-PMA (α), RULED [OWN.45]) — [rev 39] DONE: `sailCycleOrder_holds` (`Weak/SailCycleOrderCycle.lean:137`, from `cycleOkBoot_holds :128`, 122/122
   clauses) IS that theorem, so `sailCycleOrder` is NOT a trusted item and `srvwmoXv6M1Core`/`srvwmoXv6M2Core` are non-vacuous**), image dump, the TAGGED cat
   transcription and its tagged conformance text `gdexecQconfT` (new trusted-SURFACE text — covering I/O items' sources
   under D50 (b), W13 (F-dep) — **[R38.1] and `rvwmoCatConsistentT`'s TEXT changes in ONE definition, `gtdepsWf` (I/O-read sources /
   I/O-write targets admitted; (F-dep) (0a)), a trusted-SURFACE change: the registered LB roots (`allocpidOpen`, `AxSpinT2b.lean:251`,
   premise `HconsT : rvwmoCatConsistentT GT`; the 13 `Hcons := catTAd GT HconsT` files) keep their TEXT and their PREMISE WEAKENS (admits
   I/O-endpoint deps) — a strictly stronger theorem, no re-registration, noted in `tools/ci/roots-weak.txt:13-18`'s gloss** — **[rev 42] two more
   trusted-surface TEXT changes: [OWN.53] (R3)'s fabric arm (`GraphFabResidue.lean:84`) orders ALL `gfDev` members that have a memory-order
   position (`gmem`: the disk's fabric-moving `DWriteDev` RAM stores included; the disk row's `DFence` `LFence` block excluded — [R39.3], else the
   trusted item is unsatisfiable on bundles holding such a member) — STRONGER than the silent ISA, EQUAL to MachCSL on those events (W13 (R3′) — LANDED rev 44, `GraphFabResidue.lean:112-124`; `gfDevWIo` stays the NAMED premise of `fconfTraceRealizeIO`, [R40.1] (α)); [OWN.54] `lbRcsc := lbAq || lbRl` (riscv.cat's
   RCsc) — the registered LB roots' premise `rvwmoCatConsistentT` STRENGTHENS (more ppo edges; text unchanged, meaning now EQUAL to riscv.cat; the
   roots cover exactly riscv.cat's graphs, FEWER than before), so D35-fix RE-AUDITS (`audit.sh --weak --build`; baseline entries expected
   unchanged, certificates recomputed; no kernel graph changes — the image has no `.rl` write)** —, and [OWN.31][R22.2] the sentence "the device's request-service RAM stores are fabric
   transactions (each reads the device state at the store and may move it); the used-idx store is the one that raises the
   interrupt" —
   reviewed against `rowDepsT`'s correction (5), `AxDeps.lean:56-60`) [R6.1], **[R22.1][OWN.37] W8's root is (r2) — the SIBLING root
   `Xv6.xv6DiscAdequacy_closed` on the W3 pattern (W8-design §5; `xv6TracePure`'s TEXT `Xv6/SystemSlot.lean:135-136` and
   `mmOk` UNCHANGED; a root is a theorem, not a trusted item, so NOTHING is recorded here; W8-design's option (T) —
   `xv6AccessDisc` as a trusted premise — was NOT taken)**, the graph-tier fetch model (W5d-G
   `gzFetch`, §B(4)(iii); RULED [OWN.6]), the DEVICE-MODEL choices of §B(11) (MachCSL's fused completion, stall, one
   16-byte descriptor read, FLUSH OK, reads at the top; D51) [R16.5] and the pf disk row's SEQUENTIAL one-request-per-burst
   service (§B(11) (viii) [R17.4][OWN.33]), the graph-tier I/O-ordering PLATFORM assumption
   (W13 `ioResidueGmo`, LANDED `Weak/GraphFabResidue.lean:99`: the (a′) arms of D32
   [OWN.12] restated over I/O-class EVENTS [OWN.14] as (R1)–(R3), §A(†) — the residue over what ppo gives I/O
   events, §B(11)) [R4.2][R5.1][R6.3][R7.1][R7.2].

**Legitimately out of scope:** liveness/fairness, timing, mixed-size fidelity of the cat model (N10), MMIO
ordering beyond the modelled devices, hardware outside the Sail model, power cycles (SINGLE ERA [R2.2]).

**The statement to aim for — three layers.**  *T-alloc* (exists): `Xv6.Allocproc` on MachCSL.  *M1/M2 (internal,
NOT published [OWN.2])*: the composed sRVWMO theorem, pinned/kernel-only (M1) then unpinned (M2), below.
*T-alloc-RVWMO (THE published claim)* [OWN.2][OWN.3][R3.1][R3.2][R3.4][R4.2][R4.4][R5.1][R6.1][R6.3]:
```
∀ (σ0 : WGState) (GT : GfexecT),             -- NEW: the fabric bundle (Weak/WeakRvwmoFab.lean:516) over GdexecT
  wbootFacts σ0 ∧ σ0.wggen = 0 ∧ (∃ ds, σ0.wgdev = ds.reset ∧ diskOf ds = fsImgDisk) ∧        -- the boot [R2.2]
  rvwmoCatConsistentT GT.gfGd ∧        -- riscv.cat, TAGGED deps (AxDeps.lean:208) [R6.1]; rows contain `LIo` events
  ioResidueGmo (forgetF GT) ∧          -- I/O-ordering platform assumption over I/O EVENTS: (R1)–(R3) ⊆ gmo, §A(†)
                                       -- (the (a′) arms of D32 [OWN.12], re-encoded per D38 [OWN.14])
  xv6ConfS (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) GT                             -- xv6 is the program (†)
  -- (∧ sailCycleOrder)                -- [OWN.35][R21.s1] the pf hart rows' LABEL-LIST cycle fact (fetch → announce →
                                       -- execute, Step.lean:331-404), §B(11); [OWN.42][rev 39] a THEOREM — W-SCO (A) DONE:
                                       -- `sailCycleOrder_holds` (`Weak/SailCycleOrderCycle.lean:137`, EVERY instruction, under
                                       -- `wbootFacts σ0` [OWN.45]) — DISCHARGED and DROPPED from the statement (kernel AND user
                                       -- text); `srvwmoXv6M1`/`srvwmoXv6M2` are M1/M2 without it; a premise only at revs 24–38
  →
  (a) the realizing MachCSL run (robustness W9–W11 → sRVWMO cand → T1 → pf run → W4, PREFIXED by PowerOn from
      the given disk) satisfies xv6FsAdequacy_closed's conclusions for ITS ONE ERA: Reducible (panics, two spin
      arms not excluded), xv6TracePure (fs purity + mmOk), xv6NiPhi / unionAdequacyClosed [R3.s2]; the realized
      pf run never enters the retry arm [R2.3]; and
  (b) the allocproc shadow tied to κs (W1b DONE, via xv6NiPhi [R3.s1]; `allocprocTraceAns`, `Xv6/AllocprocTrace.
      lean:402`): at every filed fork round's citation ι of era k the answer is `usysForkAns ι`, `-1` or ∈ [1, PIDMAX];
      `pidPick PIDMAX ι.pev ∈ [1, PIDMAX]` and `nextOf PIDMAX ι.pev ≤ PIDMAX`; on success the pick is not live at
      `ι.pev`; `pidHistWf PIDMAX ι.pev`, its live multiset (`liveList`) duplicate-free and = `liveOf`; `ι.kNull →
      poolEmpty ι.kev.dropLast`, `ι.kOk → ¬ poolEmpty …`; the filing's chain `niChain F (niHist F)` with `niBelow ι
      (niHist F k)`; and ([OWN.28] (A)) per era k the FORK history `AllocprocTrace.forkHist F k :318` (the `niLonger`
      join of the pid prefixes era k's fork rounds cite) is a prefix of `(niHist F k).pev`, `pidHistWf`, `liveList`
      duplicate-free — "live pids pairwise distinct" ACROSS the era's forks.  NOT stated for the joined history
      `(niHist F k).pev` itself (only fork rounds file `pidHistWf`; the other citing rows never read `ι.pev`) nor for
      pid-ledger events after the era's last fork citation (`notes/W1b-done.md`).
```
**Names** [R7.s2].  **LANDED by Stage 0 (merged; grep them)**: `execProgOk'S`/`pairAdjacent`/`candSca`/`candKfetch`/
`scaOk`/`admRunG`/`pfRunS` (`Weak/PfRunShape.lean:242,95,85,53,72,224,273`), `srvwmoXv6M1Premises`/
`srvwmoXv6M1PfRun`/`srvwmoXv6M1Satisfiable`/`esilAdmRun`/`execProgOk'SNil`/`execProgOk'SSnoc` ([R16.4] after W5-pre:
`Weak/SrvwmoXv6Witness.lean:599,624,733,169,272,280`; `SrvwmoXv6Witness.m1PremisesS :611` recovers W5c's conjuncts),
`textPristine`/`textRo`/`powerInterp_textPristine` (`Xv6/TextPristine.lean:38,88,123`), `pidPick_range`/
`allocprocTraceAns` (`Xv6/AllocprocTrace.lean:152,402` — W1b moved them; `pidHistWf_nextOf :129`, `pidHistWf_nodup
:209`, `forkCite :260`, `forkStep :269`, `forkHist :318`, `forkHist_spec :367`, `forkPev_comparable :437`).  **LANDED by
Stage 1 (merged 2026-10-11)**: W5b′ `Weak/TsoShadow.lean` — `CohStamp :98`, `cohFoot :104`/`cohSrc :114`/`cohOff :128`,
`ShSt :160`/`ShFull :292` (memory fields + `itv` + `fiArm`), `shTvn :190`, `tsoRun :326`, `tsoShadow :500`, `shadowOf
:508`, `scaOkT :513`, `diskLatOk :523`, `execScaT`/`execDiskLat :527,534`, `candScaT :540`, `candDiskLat :542`,
`execProgOk'ST :559`, `pfStepFactsT :576`, `pfRunST :584`, `execPrefixPfRunProgShapedT :660` (+ the projection lemma
`memOf (tsoRun st) = shadowRun (E.exTr.take n)`), `execWfPfRunProgShapedT :789`, `execWfPfRunPinShapedT :808`, the
spot checks `g1NotScaT :879`/`g1NoRunT :890`/`g2ScaTSrc :925`/`g2RunT :953`/`itvFenceI :990`/`itvSfence :992`; W-COH
`MachCSL/TsoMem.lean` — `Hist.readEnt :127`, `Hist.readSrc :136`, `FlatMem.loadSrcs :320`, `HRead.afterLoad :354`
(per-byte `LoadSrcs` input), `HRead.resetCoh :361`; `Lang.lean` `MState.afterLoad :128`, `store :156`; W2a `Weak/
PfStepTsoMem.lean` — `midPair :46`, `logAuthor :52`, `rhist :57`, **`rmem :62`** (`R-log`/`R-img`/`R-hist`/`R-resv`),
`histOfSnoc :207`/`histOfFind :250`/`histOfTop :330`/`histOfWriteBytes :400`, `rmemBoot :424`, `resvOthersNone :464`,
the memory rows `pfLoadRowMem :540`/`pfStoreRowMem :571`/`pfExLoadRowMem :599`/`pfDReadRowMem :645`/`pfDWriteRowMem
:669`/`pfFetchRowMemM1 :693`/`pfFetchRowMemCut :724`/`pfFrameRowMem :762`; W2b `Weak/PfStepTsoView.lean` — `hartRel
:127`, **`viewRel :135`** (`R-view` = equality through `tsoShadow`), `sameRead :139`, `StampOk :293` (`cohSrcOk :301`),
`shLoadSrcs :338`, `minView :517`, `minViewLeSca :524`, the view rows `rowLoad :603`/`rowStore :676`/`rowExStore :688`/
`rowExLoad :700`/`rowFence :723`/`rowSfenceMarker :752`/`rowFetchM1 :764`/`rowFetchM2 :777`/`rowDiskRead :790`/
`rowDiskWrite :797`, and the (↓) TABLE with its faithful/stronger/weaker column (file header — W2's acceptance [R9.s4]
DELIVERED); W5d-G G0 `Weak/GraphFetchSpike.lean` — `gwlog :100`, `gfcut :104`, `fetchCutOk :114`, `fetchCutPrefix :146`,
`fetchCutEdge :161`, `fetchRelOk :183`, `fetchRelCut :215`, `gzFetchCut :264`, `gzContrib :272`, `gzFetch :278`,
**`GraphFetchSpike.emSlot :293`** ([OWN.26]), `emZifencei :312`, `fetchPinCutOk :322`; W13 (E) — `IoKind`
(`Weak/WeakMem.lean:110`), `Lbl.LIo kind base vs` (`WeakAxiomatic.lean:96`), `lbIsIo`, `Wlabel.LDev kind base vs`
(`WeakPromise.lean:89`), `unprojLbl (.LIo ..) = .LDev ..` (`WeakPromiseBridge.lean:962`), `execStepNotIo`
(`WeakAxiomatic.lean:320`, `lbIsIo :184`); **[R16.4] W11 (iv)a `Weak/RvwmoXv6Sca.lean` (327; `Weak.lean:629`)** — `tvnSca
:50`, `gwixLeTvnSca :116`, `tvnScaMono :133`, `linGmoEmitBefore :144`, `linLogEmitted :172`, `linTvnScaLe :194`, `linScaOk
:241`, **`linCandSca :314`** (`rvwmoMinusConsistent G → grule14 G → candSca (linCand G)`; no exhaustive `Lbl`/`Wlabel`
match); **[R20.3] W11 (iv)b `Weak/RvwmoXv6ScaT.lean` (792; `Weak.lean:632`)** — **`linCandScaT :757`** (`gwf G →
gppoCat6Gmo G → gloadValue G → grule14 G → candScaT cohSrc (linCand G)`), `linCandScaTCatT :780` (from
`rvwmoCatConsistentT GT`, on `GT.gtG`), `linCandScaTMinus :787`, `RvwmoXv6ScaT.linScaBytes :110`/`loadFloor :483`/`shInv
:562`; **W2 CLOSE `Weak/PfStepTso.lean`** — **`pfStepTso :301`**, `pfStepTsoProposed :436`, `pfStepTsoStutter :444`,
`pfStepTsoSame :499`, `rmemSameMem :514`, `viewRelSameRead :522`, `pfRunSTAuthors :527`, `PfStepTso.hsrcOfRhist :191`;
**W4 F1–F8 `Weak/MachOfPf.lean` (1659; `Weak.lean:633`)** — `MachOfPf.pfStepTsoStmt :95`, `poolOf :162`, `thrOf :194`,
`SimRel :305`, `contR :475`/`contROfRun :500`, `pfObsOf :557`, `Hyps :620` (`tso`/`safe`/`cut`/`fi`/`disk`), `simStep
:1456`, `simRun :1497`, **`machRunOfPfRun :1535`**, `winPristine :1559`, `cutOfPristine :1588` (**[rev 31] after W4 F9 the file is
2979 lines: `diskSide :331`, `SimRel :342` (no `DR`), `Hyps :658` (`tso`/`safe`/`cut`/`fi` — NO `disk`), `smallNoWrap :1653`,
`caseStall :1994`, `simDisk :2603`, `machRunOfPfRun :2854`, `winPristine :2878`, `cutOfPristine :2907`; NEW `Weak/MachOfPfDisk.lean`
(1290): `cacheWf :105`, `VRel :343`/`VRel.holds :349`, `devAgree :429` (+ `devAgreeRead/Write/Level/Fdev :464-558`), `outWraps0 :883`,
`FC :921`, `PosRel :965`; `VirtioProg.outWraps :421` in `dcomplete :424`); **W5 CORE `Weak/SrvwmoXv6Adequacy.lean` (318;
`Weak.lean:634`)** — `SrvwmoXv6Adequacy.lbCyc :96`, `lastCyc :104`, **`sailCycleOrder :113`** (top-level `Weak.sailCycleOrder`),
`fiOf :127`, `fiArmLastCyc :135` (the one-fold lemma), `fiOfSco :163`, `winOfText :187`, `bcRoHiLe :198`, `m1Hyps :203`,
`bootStateOf :217`, `allocprocAns :230`, `xv6Concl :252`, **`srvwmoXv6M1Core :276`** (top-level); **W-DMA0** —
`MState.storeDma` (`MachCSL/Lang.lean:181`, the `n = 0` no-op), `storeDma_zero :186`/`storeDma_of_ne :191`, the lease
constructors' `hzero` (`WpDevDisk.lean:156`, `WpDevDmaStep.lean:139,157`, `WpDevDmaStepV.lean:126,143`); **W13 (T)+(M) `Weak/GraphFabResidue.lean` (268; `Weak.lean:630`)** — `gisIo :67`, `gisR :73`, `gfBefore :79`,
`ioResidue :84` ((R1)(R2)(R2′)(R3)), **`ioResidueGmo :99`**, `ioResidueNodev :119`, `ioResidueAcyclic :148`, `gfIoDev :172`
(the INTERIM clause `gisIo (i,k) ↔ (i,k) ∈ gfDev`; (I) restates it per [OWN.31], below), `w13fIoResidueOk :236`/
`w13fIoRevExcluded :261` ((T)'s acceptance); (M) `lbIsMem := lbIsR || lbIsW || lbIsIo` (`WeakRvwmoGraph.lean:126`),
`WeakRvwmoGraph.gwfNoIo :739`/`gwfMemRW :747` (the ~10 I/O case sites of the chain closed by `gwf`'s `False` `LIo` shape
arm — exactly the sites (I) re-opens), `fenceGob` stated on `lbIsR || lbIsW` (`AxSpinProt3.lean:393-395`).  **NOT in any
merged file — workers must not grep for them**:
`GfexecT`, `GT.gfGd`, `forgetF`, `xv6ConfS`, `gfexecConfIO`, `gdexecQconfT`, `Gdexec.gdFetch`,
`emFenceI`, `rvwmoCoreD`/`rvwmoCatAD` (scratch only), `ptraceRelIO`/`gnxa`/`racyDIO`/`cycleKillIO` ((K)/(L)) [rev 35:
`mstep.MStepIo` LANDED by W13 (I)'s realization half, `WeakAxiomatic.lean:170`; `wpstep.WPIo` is NOT a name — the pf
I/O arm is the existing `wpstep.WPDev`/`wpPfStep.PFDev`; **`projLbl .LDev … = some (.LIo …)` LANDED,
`WeakPromiseBridge.lean:542`**; `LDev` out of `lbAdmin`, `WeakAxRealize.lean:140` — `PROGRESS-W13I.md`], `pfLoadRow` (SUBSUMED by `pfLoadRowMem` + `rowLoad`), `linCandDiskLat` ((iv)c), `itvOf`/`itvStep` (W5d
[R11.3]), `poolRel`/`HSafe` (plan words: W4 landed them as `SimRel`/`poolOf` and `Hyps.safe`), [rev 31: `sailCycleOrder` is
LANDED — `Weak/SrvwmoXv6Adequacy.lean:113`, label-list form, `Hyps.fi` derived by `fiArmLastCyc :135`/`fiOfSco :163` — and
`MachOfPf.Hyps.disk`/`DR`/`diskRows` NO LONGER EXIST (W4 F9)], `Ioev`/`ioOrd`/`ioObAcyclic` (scratch,
SUPERSEDED), `execProgOkA`/`gfexecConfA` (RETIRED by D38), `ioOrdF`/`emIoFence` (D46 (b) only), `badSeg`,
`xv6RvwmoSafeModuloT`, `Weak/ExistWitness.lean`, `DGet` (WITHDRAWN [R16.1][OWN.32]), and W8's names
`xv6AccessDisc`/`chainOkAt`/`syncPath`/`lockWordDiscAt`/`cpuStaticAt`/`cpuProcDiscAt`/`utextDiscAt`/`kOwnerAt`/`lkHolderAt`/
`custAt`/`xv6DiscAdequacy_closed` (§C W8; grep-checked FREE by W8-design).  **[rev 28] LANDED by W-DISK (merged 2026-10-12)**:
`DM.DWriteDev`/`DM.DPop`/`Dres.DStall` (`Weak/VirtioProg.lean:263,266,273`), `virtioProg :438`, `drainAll :323`, `popState
:319`, `preCaptureHead :338` (the plan's `pre₁`), `dusedTail :394`, `runVirtioProg :524`, `virtioProgWf :661`;
`WeakEvLang.ediskStep :936`/`ediskStepWf :1360`/`eprimStepDiskReducible :1393`/`setDvirtioSelf :922`; `WeakEvInst.pdiskProg
:499` (ten arms), the state-aware `pdevEv :604`, `pdiskProgDevFree :1759`, `pstepDiskDevFree :1781`, `pdevEvOk :1792`,
`WeakEvInst.pdiskProgLabel`; `WeakEvDisk.ewpDiskStart :388`/`ewpDiskRead :431`/`ewpDiskFence :488`/`ewpDiskWriteDevStore
:524`/`ewpDiskWriteDevSkip :607`/`ewpDiskWriteDevAbort :666`/`ewpDiskPop :722`/`ewpDiskPopRefused :772`/`ewpDiskIdle :816`;
`PfStepTsoMem.pfDWriteDevRowMem :698`/`pfDSkipRowMem :806`; `PfStepTsoView.rowDiskDevMove :808`; `WeakRvwmoSupply.devQuiet
:177`/`devQuietStep :183`/`pdevEvFalse :209`/`pstepEvDevfree :219`; `WeakRvwmoCapstone.epsInitQuiet :232`;
`WeakRvwmoFab.gfexecConf :620` (interim clause `:633`).  [R20.3] `pfStepTso`, `linCandScaT`,
`machRunOfPfRun`/`thrOf`/`pfObsOf`, `Weak/MachOfPf.lean`, W-DMA0's `n = 0` case and the W3 root `xv6TextAdequacy_closed`
(`Xv6/LinkTextAdequacy.lean:26`) moved to LANDED.
(†) `xv6ConfS` is the SHAPED, UNPINNED, FABRIC-ORDERED, TAGGED conformance bundle [R5.1][R6.1][R6.3][R6.4][OWN.14]:
`gfexecConfIO` (W13 (I)/(W): per-row `hartConff` emissions with TWO fabric endpoints, `Fab.lean:262-263`/`hemitf
:239-260`; an I/O access is a TAGGED row item `(l, some k)` whose `pstepEv` has fabric endpoints `dvi k → dvo k` (possibly equal); **[OWN.31]
[R16.1 (iv)] `gfDev : List Geid` (`Gfexec :517`/`gfDev :520` [R23.s3], type unchanged) lists the fabric TRANSACTIONS (I/O-class events by class, plus fabric-moving stores) [R23.2] in fabric order — `(i, k) ∈
gfDev ↔ (gisIo (i, k) = true ∨ dvi k ≠ dvo k ∨ the BLOCK of item k has a `pdevEv`-true step)` **[OWN.43][rev 35] — membership
by fabric CONTACT, superseding [R22.2]'s two-disjunct form: a block that READS the fabric without moving it is a member, so every
NON-member block is `pdevEv`-quiet, hence fabric-preserving AND blind (`pdevEvOk`, `WeakEvInst.lean:1792`), which is what
`supplyOfFconf`'s replay at the global fabric `fab ∘ dcnt` needs; EQUAL to [R22.2] on every xv6 run, STRONGER as generic
trusted text only by unreachable non-moving fabric-touching blocks, which (R3) then orders (`PROGRESS-W13I.md`; §D
Q-GFDEV-contact)** — every I/O-class event by CLASS (its VALUE depends on the fabric
at its position even when it moves nothing: a UART LSR read `Uart.lean:120`, the virtio NOTIFY write `Virtio.lean:310`, every
virtio register read `readN :337-338`, PLIC prio/pending/enable/threshold reads `Plic.lean:123-136`; at such a member `fab
(n+1) = fab n` unless its ADMIN BLOCK moved [R23.s1]) PLUS every non-I/O item whose BLOCK (admin run + tagged step, `HFone`/`HFpair`
`Fab.lean:242-259`) moves the fabric [R23.s1], read off `hartConff`'s endpoints (`:239-262`), NOT off
the label-based `isDevBlock em k ↔ (i, k) ∈ gfDev` (`:533`; `lbIsdev :119`/`emDev :144`/`isDevBlock :152` are label
functions and cannot see W-DISK's `DWriteDev` `LStore`s).  Rev 25's "`gisIo → gfDev` ∧ `gfDev ↔ dvi ≠ dvo`" was
UNSATISFIABLE for xv6 (hart 0's LSR polls and every NOTIFY move nothing — no conforming emission, the `emDevfree` vacuity
one level up) and "the used-idx `LStore` is the ONE non-I/O member" was FALSE: under the MECHANISM the status, used-element
and used-idx `DWriteDev`s of EVERY request (and the IN fill when its `pre` carries `setPhase .fetched :526`) each change
`dvirtio` (phases, cache, latch; `complete` at the idx store) — three (OUT) or four (IN) non-I/O members per request, (R3)
ordering them against hart MMIO as the fabric serializes them: STRONGER than the spec's silence by exactly that, EQUAL to
MachCSL's step structure, realization-necessary under [OWN.32] (a) (each store's guard reads the device state).  `LSilent`
abort/skip moves are ADMIN-run moves (inside `hemitf`'s `admRun … (dvi k)`, `Fab.lean:239-250`), not `gfDev` members; (I)
keeps the threaded fabric through admin runs on the disk row and does not re-impose `admRunDevfree` (`Supply.lean:175`)
there beyond W-DISK's `devQuiet` form.  The landed (M) clause `gfIoDev` (`GraphFabResidue.lean:172`, `gisIo ↔ gfDev`) is the
INTERIM form (I) restates; admin stars carry NO `gfDev` member), `fab 0 = efInit
σ0.wgdev`, `rowDepsT` tags in `GT.gtDeps` (`gdexecQconfT`-style — [R38.6] stated against the GENERALIZED `gtdepsWf`, NO RAM-endpoint
filter, and only after (F-dep) (0) merges; `rowDepsSubT`, `AxDeps.lean:690`, gives the untagged
bundle back through the inclusion untagged ⊆ tagged [R38.2]), the fetch clause `emZifencei` (W5d-G, replacing `emFetchImg`, `Fab.lean:534`/`Supply.lean:277-278`)
with `F_em ⊆ GT.gdFetch`, exclusive pairs FUSED (the `execProgOk'S` shape of [R3.2], LANDED by W5b [R6.4]) — NOT
today's quiescent `gdexecQconf` (`Weak/WeakRvwmoSupply.lean:292`), whose `emDevfree` (`:284` [R16.s1]) forbids every
`LDev`.  **Quiescence is VACUOUS for allocproc** (W13 spike CONFIRMS): the event LTS emits `LDev` for EVERY MMIO
access (`Weak/WeakEvInst.lean:300-303,335-338`) and the disk row's START/COMMIT (`:484,502`); hart 0's `main` runs
`consoleinit` FIRST (`Xv6/SpecMain.lean:7-10`) = `uartinitone`'s seven `WriteReg`s (`Xv6/SpecUartinitone.lean:6-13`),
so `userinit → allocproc` is unreachable in EVERY quiescent `GD` (route-b: "HONEST MILESTONE",
`claude-notes/design/weak-memory-route-b.md:1009-1020` [R9.2]); no `LDev`-emitting witness exists (`gfexecConfOfQconf`, `Fab.lean:648`).
**THE I/O ITEM (D38 RULED [OWN.14]; D32 (a′), D37 (a) [OWN.12] carried over)** [R6.3][R7.1][R7.3a]: [OWN.8]'s literal
axiom IS `gfexecConsistent'` (`Weak/WeakRvwmoLin2.lean:761-762`) — it forbids LB and W→W even at an EMPTY fabric
(`lbExcluded`, `Weak/W13Spike.lean:35`): a robustness ASSUMPTION, not a hardware model; and every block-level dev
condition (`gdevAdj ⊆ gmo`, `Fab.lean:539-544`) excludes SC (`scDevExcluded`/`scDevUnrealizable`, `W13Spike.lean:55,66`)
because `execProgOk'` (`WeakAxRealize.lean:373-386`) folds the `LDev` admin block into the NEXT tagged event.  **Rev 10
removes the cause: an I/O access is its OWN graph event `Lbl.LIo kind base vs`** (D47; `IoKind = rd | wr | dev`), a
`gmem` event with its own gmo position, in EVERY row `i < xN σ0 = NCPU + 1`: a hart's MMIO reads/writes (`pnodeStep`,
`WeakEvInst.lean:300-303,335-338`, today `LDev` without payload), the PLIC pin delivery to a hart (`pstepPlic
:464-470`), the disk agent's START/COMMIT (`pdiskProg :485-516`, arms `:488,506`; **W-DISK DONE (2026-10-12) [OWN.29]: COMMIT is
RETIRED — the used-idx `DWriteDev` carries the completion's fabric move (W-DISK-Q2 RULED (a) [OWN.31]) and the ring POP
(`seen+1`) is ONE `LDev .dev 0 []` event per request right after the ring `DRead` (W-DISK-Q3 RULED (a) [OWN.32]; MachCSL's
guard-pop is a separate step, `Virtio.lean:576-578`)**) AND the device threads' fabric
moves at the disk agent (`pdiskUart :518-524` — UART tx/rx, PLIC gateway) — all kind `dev` [R7.3a][D49].  `lbRd`/`lbWr` are `none` on `LIo`, so rf, co, fr, load-value,
atomicity and the log message `gmsg` (`Lin.lean:463`) ignore I/O events BY CONSTRUCTION (device-supplied values,
[OWN.14]); `lbIsR`/`lbIsW` stay RAM-only, so rule 4 (`gfenceCovers`, `Graph.lean:204-209`) and rule 7 skip them ([R38.1] the tagged
dependency well-formedness `gtdepsWf` no longer keys on them ALONE: `lbIsR ∨ lbIsIoRd` sources, `lbIsW ∨ lbIsIoWr` write-tag targets) —
Sail's `execute_FENCE` keys on `extractLsb pred 1 0` only (`InstsEnd.lean:18299-18313`), after `effective_fence_set`
(`BaseInsts.lean:568-573`), which with FIOM = 1 ORs the i/o bits INTO the memory bits and never the reverse — so the
i/o bits produce NO I/O ordering in Sail unconditionally, and never reach `LFence` at all because xv6 powers on with
`menvcfg = 0` (`BootBoard.lean:30`) and `start()` sets `menvcfg = ADUE | STCE` (`Xv6/SpecStart.lean:29,40`; FIOM = 0, so
the i/o bits still never reach `LFence`) [R8.3d][R25.1 (e)]; the graph can give I/O events NO fence edge
(D48); rules 1–3 give none (`gaccesses` is byte-footprint based); rule 5 `gacqPo`'s `gmem e2` (`:214-215`) DOES
order an acquire read before a later I/O event — a strengthening the appendix's condition (c1) EXCLUDES (quoted in
§B(11b)), subsumed by (R1), vacuous as a trusted use — D52 RULED (a) [OWN.18]; **dependency edges through `LIo` are
ON — D50 RULED (b) [OWN.17]; graph side = (F-dep) (0) [R38.1]**: the TAGGED tagger `dstepT` (NOT `dstep` [R38.2]) gets the (c1) edges (addr/data/ctrl → I/O store, addr → I/O load, provenance
OUT of an I/O load; NO ctrl → I/O load), W13 (F-dep), §C — in-edges are subsumed by (R1) (RAM source) / (R3) (I/O
source), out-edges into RAM STORES by (R2); the ONE edge class beyond (R1)–(R3) is I/O-load →addr→ RAM LOAD (rule 9),
expected absent in xv6 (MMIO values flow to ctrl, to RAM/I/O stores as data — **unverified** census).  **The trusted item
is an INCLUSION, not an acyclicity over an extended order** — gmo is already total over `gmem`: `ioResidueGmo GF :=
∀ x y, ioResidue GF x y → gmoLt GF.gfGd.gdG x y` with **(R1)** `gpo x y ∧ gmem x ∧ ¬ gisIo x ∧ gisIo y` (a row's RAM
accesses po-before an I/O event, READS included); **(R2)** `gpo x y ∧ gisIo x ∧ gisW y` (an I/O event po-before a
row's RAM WRITE — `grule14`'s shape, `Graph.lean:257-258`, with `gmem` covering I/O; reads po-after stay UNORDERED,
the (a′) point [R7.1]); **(R3)** `gisIo x ∧ gisIo y ∧ (gpo x y ∨ gfBefore GF x y)` (same-row issue order — ISA-given
only within ONE channel (F2), cross-channel residue — and fabric order, stated on the ORDER `gfBefore`, not `gdevAdj`,
so hulls that cut I/O events out keep it); **(R2′) [W2s; G3-Q RULED (a″) [OWN.17]]** `gpo x y ∧ gisIo x ∧ gisR y ∧ y.1 = NCPU`
(an I/O event po-before a DISK-ROW RAM read — the device model's "reads after the MMIO see everything before it", the
DEVICE sentence's direction; hart rows keep reads po-after I/O UNORDERED).  Free when no row has an I/O event (`ioResidueNodev`, the
`ioObAcyclicNodev :109` rank proof re-done — LANDED: `ioResidueNodev`/`ioResidueAcyclic`, `GraphFabResidue.lean:119,148`)
so LB and W→W stay in the quantifier; admits the SC case (`w13f` re-encoded: gmo `MMIO₀ < MMIO₁ < st < ld` is now a
GRAPH — W13 (T)'s acceptance DELIVERED: `w13fIoResidueOk :236`, and the reversed fabric order is EXCLUDED,
`w13fIoRevExcluded :261`); does NOT assume `racyD` acyclicity — the kill carries that.  **The item is LANDED as
`GraphFabResidue.ioResidueGmo :99` over the four arms `ioResidue :84` (W13 (T) DONE 2026-10-11); until (I) flips `gwf`'s
`LIo` arm no `gwf` graph carries an I/O event and it holds for free (`ioResidueGwfInterim :184`).**  (R1)/(R2) are REALIZATION-NECESSARY and ISA-given at three
xv6 sites only (§B(11b)); no read arm (`elabOk σ c LDev = True`, `WeakEvInst.lean:558`; TsoMem's MMIO arms touch only
`devs`, `MachCSL/Lang.lean:356-358,372-375`) and nothing needs one (reads have no cross-hart OUT-edge in `ptraceRel`,
`Lin2.lean:124`).  For the disk row (R1) says "DMA writes (plain `LStore`s, drained by `LFence true true true true`,
`:497-498`) are gmo-before COMMIT" — device-MODEL semantics, the one place (T) carries disk correctness [R7.3] (and,
via the one-row model, DMA accesses around UART/PLIC moves — D51); **after W-DISK (DONE 2026-10-12) the sentence reads "… gmo-before
the used-idx write", which is then a RAM store ordered by the device-side `DFence` (rule 4) and the single order — (R1)'s
disk use SHRINKS to the START event, the POP event ([OWN.32]: DMA reads of the avail index/ring po-before it) and the
UART/PLIC moves (W-DISK-Q2 RULED (a) [OWN.31])**.  `candSca` is NOT a premise here: a `Cand`
predicate, ill-typed on `GD`, DERIVED at Stage 2 from `gloadValue` (`linCandSca`, W11) [R4.4].  The conformance
premise is genuine: the graph side alone yields only `execWf`-style facts; the program half is realized by
`execWfPfRunProg` (`Weak/WeakAxRealize.lean:802-808`) [R1.5].  **The pin fixes WHAT a fetch answers, not WHERE it
fetches** [R3.1]: at M1 the premise is `pstepPin` + `candKfetch` (every `LIFetch` footprint in W3's pristine window
`[bcRoLo, bcRoHi)`, §B(4) [R5.2]) — what makes M1 kernel-only; M2 replaces both by CUT-form Zifencei admissibility
on the pf side; the target needs the graph-side twin `gzFetch` (W5d-G).  Boot premises: `xv6FsAdequacy_closed`'s
(`Xv6/LinkSystemAdequacyClosed.lean:20-26`) transposed through `PowerOn` (`MachCSL/Lang.lean:294-304`) to
`wbootFacts` (`Weak/WeakLang.lean:482-490`); `diskOf ds.reset = diskOf ds` from `Xv6/BootSharedDev.lean:283` [R3.s4][R9.2].
(b) is the trace-observable shadow of `allocprocPost` in the NI idiom (`xv6NiPhi`, `Xv6/NiAdequacy.lean:91-92`) [R1.4].
*M1/M2 (internal)*: **M1's premise set IS the DEFINITION `srvwmoXv6M1Premises σ0 c pst dv`** ([R16.4] W5-pre DONE,
`Weak/SrvwmoXv6Witness.lean:599-607`: `wbootFacts σ0 ∧ σ0.wggen = 0 ∧ (∃ ds, σ0.wgdev = ds.reset ∧ diskOf ds = fsImgDisk)
∧ srvwmoConsistent c ∧ c.cdImg = imgZ σ0.wgimg ∧ pst 0 = epsInit σ0 ∧ dv 0 = efInit σ0.wgdev ∧ execProgOk'ST (pstepPin
(imgZ σ0.wgimg) pstepEv) pclsEv (candKfetch bcRoLo bcRoHi) TsoShadow.cohSrc pst dv (candExec c) ∧ candScaT cohSrc c ∧
candDiskLat c` — STRONGER than W5c's set; `m1PremisesS :611` recovers `execProgOk'S … ∧ candSca c`; `srvwmoXv6M1PfRun
:624-633` returns a `pfRunST … cohSrc` run PLUS the projection `∀ i, (tsoShadow cohSrc st i).mem = shadowOf cohSrc c.cdTr
i`; `srvwmoXv6M1Satisfiable :733`) — W5 states M1 THROUGH it, never by re-listing; M2 = `execProgOk'ST pstepEv pclsEv
fok_cut cohSrc …` with the cut-form fetch clause as `fok` `∧ candScaT cohSrc c ∧ candDiskLat c`.  **[rev 31] M1 IS LANDED as
`Weak.srvwmoXv6M1Core` (`Weak/SrvwmoXv6Adequacy.lean:276`, W5 CORE + W4 F9, 2026-10-12)**: from `srvwmoXv6M1Premises σ0 c pst dv`,
a MachCSL machine-off `g0` (`g0.gen = 0`, `g0.pow = false`, `σ0.wgdev = g0.m.devs.reset`, `diskOf g0.m.devs = fsImgDisk` — one
always exists, `bootStateOf :217`) and `sailCycleOrder` [OWN.35], it concludes the shaped `pfRunST … (candKfetch bcRoLo bcRoHi)
cohSrc` run with `pairAdjacent` and the projection lemma, its record `r` (`contR`, `recLabels r = st`), the MachCSL run `MRun n
([power], g0) (powerOn :: pfObsOf r) (t, g)` related by `SimRel` (opaque — its device clause `R-dev` is never unfolded), and at that
run `Reducible` (panics, two spin arms not excluded), `xv6TracePure`, `xv6NiPhi`, `unionPhiSync`, `textPristine g` and the
allocproc shadow `allocprocAns :230` (= `allocprocTraceAns`'s conclusion, verbatim) — i.e. §A (a)+(b) at the sRVWMO/kernel-only
tier.  NO disk hypothesis remains (F9's `simDisk`; [OWN.40]).  Axioms: `xv6FsAdequacy_closed`'s cone + the 4 `bv_decide`
certificates of the NI/union/text roots; `#print axioms` at the file's end.  Header: INTERNAL milestone (D21 wording), NOT
registered by the worker — the **W5 CLOSE-OUT** (§C W5) registers it.  W-SCO then adds `srvwmoXv6M1` (the premise discharged for
kernel text); M2 restates the whole over the cut-form `fok` (W5d).  [R16.s1][R22.3] Cite drift after W-COH and W-DMA0, for
readers of §0/§A/§B (workers grep NAMES): `MachCSL/Lang.lean` (tip after W-DMA0) `MState.afterLoad :128`, `MState.store :151`,
`MState.fence :161`, `MState.storeDma :181-183` (`storeDma_zero :186`, `storeDma_of_ne :191`), `anyReserve :212`, `dmaView
:218`, `setDev :222`, `bootShape :336`, `blockedStep :431` (arms `:433-436`), `hartStep :533-538` (`.pure` arm `:535`),
`devOpStep :560-584` (`dmaRead :568`; `dmaWrite` arm `:569-574` [R23.s3]: `anyReserve` guard `:572`, the skip disjunct `:574`),
`devBlocked :590-598` (`.step` arm `:592`), `devStep :604-616` (`.pure`: root restart `:609`, done-marking `:610-612`; `.op`:
step `:614`, blocked `:615`), `primStep :632`, `primStep_power_on :715`; `TsoMem.lean` `Hist.read :122-123`, `HRead :288`, `HRead.zero :293`;
`WeakRvwmoSupply.emDevfree :284`, `emFetchImg :288`, `gdexecQconf :292`; `WeakRvwmoFab.Gfexec :517`/`gfDev :520` [R23.s3], `isDevBlock ↔
gfDev :533`, `emFetchImg :537`, `gfexecConfOfQconf :649`, `hemitfStatesQ :347`, `supplyOfFconf :690`; `MachOfPf.simDev :1193`; `WeakAxiomatic3.srvwmoRealizable :2088`.  **[rev 28] After W-DISK**: `WeakRvwmoFab.emDev :158`,
`isDevBlock :166`, `hemitfStatesQ :396`, `hartConffStatesQ :556`, `gfexecConf :620` (interim clause `:633`), `supplyOfFconf
:789`, `fconfRowsPin :885`, `fconfRows :908`, `fconfSupply :928`; `WeakRvwmoLin2.fconfTraceRealize :1019` (quiet-boot
hypothesis `:1007,1024`); `WeakRvwmoFabInd.fconfRealize :419` (`:425,465,537`); `WeakRvwmoCapstone.xv6RvwmoSafeModulo :191`,
`xv6RvwmoSafeModuloF :238`, `epsInitQuiet :232`; `WeakEvInst.pdiskProg :499`, `pdevEv :604`; `WeakEvLang.ediskStep :936`;
`VirtioProg.virtioProg :438` (the `:606-623`/`:485-516`/`:488` cites below are pre-W-DISK).  Older `:N` cites to
these names in the body are to the pre-W-COH/pre-W-DMA0 file and are superseded by this line (the binding W-DISK
MECHANISM, §C W4 F9 and W-RSV texts were re-based in rev 26 [R22.3]).
sRVWMO ("RVWMO, stores never early") results stay milestones only [OWN.2]; `xv6RvwmoSafeModuloF` is RETIRED (D39).

## B. Gap analysis

Legend: *need* = needed for T-alloc-RVWMO; *route* = (M) machine tier / (A) AxSL tier (retired [OWN.1]).

**(1) AxSL tier not composed with the machine tier.**  Route (A) only (retired): XL; Theorem 2 = validation (D6).
**(2) Page tables.**  Route (M): CLOSED — kernel table a live shared invariant with A/D variants (`KptInv.pteVariant`),
`utlbOk` "up to A/D" (`MachCSL/UTlb.lean:17-21`) [R1.s3]; user-table pages fresh owned memory (`pptPost`), published
at `satp` + `sfence.vma`; Svadu write-back named in §B(11) and carried by W8's `pteDiscAt` (§C W8 [R25.1]) — **for the USER
tables too [OWN.39] (rev 31)**: `swp_update_and_write_pte_own` (`MachCSL/WpPtWalkOwn.lean:501-515`) writes owned `ctxBytes` and
stamps a dirty key at the running context, which a `p->lock` migration would carry as a chain — but the privileged spec's A/D
update scheme (supervisor.adoc) orders the update only when it is ASSOCIATED with a fenced access, while an A-bit update MAY be
speculative and is then ordered by nothing; so the chain reading is UNFAITHFUL and user PTE bytes take the `pte-key` arm
(`Cust.pte`, `pteDiscAt`) like the kernel table's — FAITHFUL, STRONGER only in documentation.  S.  **(3) SIE = 0, 3 harts, no devices/DMA.**  Route (M):
CLOSED (`KCtx.sie`, `wpNext`, `NCPU = 8`, DMA at the store order).  Graph tier: OPEN — the quiescent bundle has NO
devices; the fabric bundle is W13 (§A(†)) [R5.1].

**(4) Text never written / fetch pinned** [R1.8][R2.1][R2.1-alt][R3.1][R4.2].  The fetch-view premise is carried
by both weak capstones (`xv6SrvwmoSafe` (b'), `Weak/WeakSrvwmoCapstone.lean:88-89`; `xv6RvwmoSafeModulo`,
`Weak/WeakRvwmoCapstone.lean:195`: `∀ ρ, rtc epfRun … → efetchItvOk ρ.1 ρ.2`, `Weak/WeakEvCapstone.lean:681-685`)
because the lift `wpPfRtcEpfRtc` (`:1008-1011`) needs it (`Hcov`, `WeakSrvwmoCapstone.lean:118-120` [R3.s4]); not
dischargeable weak-side on route (M).  Treatment: (i) W5 does NOT go through `epfRun`; it starts from
`execWfPfRunProg`'s `rtc (wpPfRun pstepEv pclsEv) …` (`WeakAxRealize.lean:802-808`, via `wpPfRunPinSub :225`), and
W4 projects `wpPfRun` runs.  (ii) W2's (↓) `LIFetch` row carries the content: the pf fetch is admissible at floor 0
(`PFIFetch`, `Weak/WeakPromiseBridge.lean:441-449`) while TsoMem fetches as the i-cache agent at `σ.itv cpu ≤ tvn ≤
top` (`MachCSL/Lang.lean:360-362`); the row closes iff no log write hits the fetched bytes between the version read
and `itv`.  THE TsoMem-side mechanism [R5.s4][R5.2]: kernel text is held as `imgByte a v := ∃ tid, a ↦ₕ□ [⟨0, tid,
v⟩]`, a DISCARDED-fraction singleton HISTORY (`MachCSL/Ctx.lean:433-436`), assembled into `kernelText`
(`Xv6/KernelText.lean:25-30`) from `bootRo … bcRoLo bcRoHi` (`Xv6/BootCarve.lean:582`; window `[ramBase, _data)` ⊇
text + rodata); against the auth heap it reads the image byte at EVERY view (`MachCSL/Wp.lean:1478,1490`) and a DMA
write needs `DFrac.own 1` (`MachCSL/WpDma.lean:142-145`) — so `candKfetch` (every `LIFetch` footprint ⊆ `[bcRoLo,
bcRoHi)` ⊇ `[text, etext = 0x80007000)`, `Xv6/KernelImage.lean:771`) is dischargeable for kernel text (W3), NOT for
user pages (`own 1` cells).  **[R3.1] The pin does not make a candidate kernel-only**: a pinned fetch is pf-admissible
AT ANY LOG (`fetchPinIfetchOk`, `WeakAxRealize.lean:167-176`; `WeakPromise.lean:228-231`), the program LTS constrains
the fetched value only through memory (`pstepEv`'s i-cache arm, `WeakEvInst.lean:306-312`), and the boot image is
ZERO past the ELF (`bootByte_zero`, `MachCSL/BootImage.lean:31` [R6.5a]) — a conformant pinned candidate can run
`userinit → scheduler → userret (fence.i) → sret` and fetch zeros at the user page while TsoMem's `itv` has passed
`uvmfirst`'s writes: W4's `LIFetch` row has no TsoMem step.  Fix: M1 carries `candKfetch` inside the shaped predicate.
(iii) **The unpinned supply is TWO items** [R4.2], SHAPED by the W5d-G spike (DONE) and RE-CREATED as `Weak/
GraphFetchSpike.lean` (W5d-G G0 DONE 2026-10-11, 339 lines; every `GraphFetchSpike.lean:N` below is that file) [R6.4b].  **W5d** (M2, L; in the
target [OWN.3]) is the pf half: `execWfPfRunProgF`, the replay at `pstepEv` with a Zifencei side condition in place
of `fetchPin`.  **Fix now (spike §3.4): the M2 fetch clause is the CUT form `∃ q, itv ≤ q ≤ |log| ∧ ifetchOk img log
q base tvs`** (`fetchCutOk`, `GraphFetchSpike.lean:114` — with an explicit bound `cut` and the [W2s] per-byte `t ≤ q` conjunct, header
R1; `fetchCutOkLit :123` recovers the report's literal; `ifetchOk` DEFINED `Weak/WeakPromise.lean:222-224`, used
`WeakEvInst.lean:564` [R9.2]; `itvPostMachCSL`,
`Weak/WeakInterp.lean:378-384`), NOT per-byte `ifetchOk … itv` — per-byte fetches tear ([R3.4]; `ifetchByteOk`,
`WeakPromise.lean:222-231`) and the cut form is what W5d-G produces; W4's (↓) `LIFetch` row then holds for user text
(TsoMem reads at `tvn := q`) and W2's `R` carries `itv ≤ q`.  **[W2s] Two corrections**: (i) `ifetchByteOk … q` admits
a byte source `t > q` (its window `(t, max t q]` is EMPTY, `WeakPromise.lean:222-224`), which TsoMem at `tvn := q`
cannot read — the cut form adds `t ≤ q` PER BYTE (W5d; W5d-G's G5 `gzFetchCut` must produce it, or a torn fetch slips
through); (ii) the pf machine has no `itv`: the clause's `itv` is the SHADOW's (`tsoShadow`, §B(10): `fence.i` →
`max itv (fencePost true false tv rv pub)`, `Lang.lean:155-163`), so `R-itv` is `itv_T = itv_S ≤ q` — **carried by
W5d's `itvOf`, NOT by the Exec-trace shadow [R11.3]**: `fence.i` and the Q7 `sfence.vma` marker are the SAME label
`LFence false false false false` (`ebarLabel`, `WeakEvInst.lean:272-275`; `ebarNow .Barrier_RISCV_i = none`,
`WeakEvLang.lean:745`; `annLabel :418-419`), `projLbl` keeps it (`WeakPromiseBridge.lean:536`) and `lbAdmin` excludes
it (`WeakAxRealize.lean:129-133`), so both reach `E.exTr` as indistinguishable `Estep`s; `emFenceI`'s criterion needs
the admin block `ls`, which is existential PER INDEX inside `execProgOk'S` (`PfRunShape.lean:242-262`), and `fok` has
no `itv` argument (`fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop`, `:232,242`).  W5d therefore
defines a per-row, per-step `itvOf : Nat → Nat → Nat` as a FREE variable of M2's premise set `srvwmoXv6M2Premises` — NOT a
parameter of `execProgOk'S`/`execProgOk'ST`/`pfRunST` [R30.1] — DRIVEN by the index's REALIZING label (`s.esLb = LFence false×4`
on the left arm) and constrained in M2's INSTANCE of `fcutE` (below), per index, where `ls` IS in scope (`fetchesOk … ls`,
`PfRunShape.lean:232-234`) — **[R31.1] `ls` is NOT the carrier of `emFenceI`'s criterion on the Exec side**: the raise at a `LFence false×4` step is
decided by the step-list shadow's `fiArm` STATE (`shStepF`, `TsoShadow.lean:310-319`: set by `LInstr`, cleared by `LIFetch`,
else CARRIED), which this index's `ls` determines only when `ls` contains a cycle label — at a fence step whose star is
cycle-free the replay invariant would need the Sail-cycle fact (W-SCO's, not W5d's).  APPLIED by route (i) (the coordinator's
choice; DELIVERED, `../xv6iris-weak-w5/Weak/PfRunUnpinned.lean:68-123`): a companion FREE bit `fiOf : Nat → Nat → Bool` bound
in `srvwmoXv6M2Premises` beside `itvOf`; `fiOf (k+1) ag = fiFold (fiOf k ag) ls` (`fiStep`: `LInstr ↦ true`, `LIFetch ↦ false`,
else keep); `itvOf (k+1) ag = itvStep stamp E k ag (itvOf k ag) (fiFold (fiOf k ag) ls)` — raises iff `E.exTr[k]?`'s realizing
label is `LFence false×4` (`lbFenceZeroL`) AND the fold is armed, to `max itv (fencePost true false tv rv (ownPub ag au))` at the
trace shadow's `tv`/`rv` (`shadowRun stamp ag (E.exTr.take k)`) and the log's authors (MachCSL's `fence.i` arm,
`Lang.lean:155-163`); frame `∀ i ≠ ag, fiOf (k+1) i = fiOf k i ∧ itvOf (k+1) i = itvOf k i`; boot `∀ i, itvOf 0 i = 0 ∧ fiOf 0 i =
false` (= `ShFull.zero`, `TsoShadow.lean:299`) [R31.s3]; the instance CLOSES over the execution — `fcutEM2 stamp E itvOf fiOf k ag
ls σ` [R31.s1] — so `fcutE`'s arity stays `Nat → Nat → List Wlabel → Mstate → Prop` (route (ii), reading the realizing node `pa`
under `sailCycleOrder`, NOT taken).  The replay invariant is `∀ i, (tsoShadow stamp st i).itv = itvOf n i ∧ (tsoShadow stamp st
i).fiArm = fiOf n i`, BY CONSTRUCTION (no Sail fact); `fiOf`, like `itvOf`, is a parameter of NO shared definition and `fcutE`
stays `True` at M1 — the bold sentence of [R30.1] unchanged.  [Rev 34's wording, SUPERSEDED: "`ls` serves ONLY to tell `fence.i`
from the `sfence.vma` marker by `emFenceI`'s criterion (the marker's star ends in `LIFetch`, `fence.i`'s in `LInstr`,
`W5dG-spike.md:115-117`): `itvOf (k+1) s.esAg = itvStep (itvOf k s.esAg) (tv, rv) pub ls` (`itvPostMachCSL`,
`WeakInterp.lean:378-384`), frame at every non-fence step [R12.s1]".]; **[R28.4] `fok`'s type is UNCHANGED (5 arguments)** — `fok` is the ONE parameter
threaded through `execProgOk'S` (`PfRunShape.lean:242`), `pfStepFacts :265-269`, `execProgOk'ST`/`pfRunST` (`TsoShadow.lean:
555-590`), `MachOfPf.Hyps :658`, `sailCycleOrder :114`, `srvwmoXv6M1Premises` (`SrvwmoXv6Witness.lean:599-607`, where
`candKfetch` IS the `fok`) and `srvwmoXv6M1Core :284`, so a 6th argument would change `candKfetch`'s type and M1's REGISTERED
statement.  **[R29.1] The M2 cut clause is carried by ONE new, trivially-instantiable PARAMETER `fcutT : Nat → Image → List Wmsg
→ Nat → Int → List (Nat × BitVec 8) → Prop`** (the shadow's `itv` first; `fok` keeps its role as the un-threaded fetch clause).
R28's carrier ("a `.LIFetch` arm of `pfLoadFactsT`, `itvOf k i ≤ q` a conjunct of `execProgOk'S`") does not work: (1) `Hyps.cut`
(`MachOfPf.lean:664-671`) takes the UN-threaded `pfStepFacts fok` and must conclude `(tsoShadow cohSrc st i).itv ≤ q` for the SAME
`q` as `ifetchOk` — not derivable from a 5-ary `fok_cut`, and `max q itv` does not repair it (`ifetchByteOk … (max t itv')`,
`WeakPromise.lean:220-222`, is STRONGER at a larger `itv'`); (2) `pfLoadFactsT`'s fetch arm is `| _ => True` (`TsoShadow.lean:
568-573`) and EVERY fetch of M1's run enters `pfRunST` through `pfRunSTApp :622-632` via `pfLoadFactsTNonload :579-581`
(fetches are admin-star labels, `lbIsLoad = false`), so a non-trivial arm breaks `execWfPfRunPinShapedT :808` and
`srvwmoXv6M1PfRun` unless proved pf-side — impossible for an `itv`-aware clause (its content is `textPristine`, pf-visible only
through `SimRel`, [R28.2]); (3) a conjunct of `execProgOk'S` STRENGTHENS M1's premise and re-proves `srvwmoXv6M1Satisfiable
:733`.  So: `pfRunST.snoc` gains a THIRD fact `pfCutFactsT fcutT stamp st c i l := ∀ base tvs, l = .LIFetch base tvs → fcutT
(tsoShadow stamp st i).itv c.pcImg c.pcLog i base tvs` beside `pfStepFacts`/`pfLoadFactsT` (`TsoShadow.lean:584-590`),
**[R30.1] the Exec-level twin is a SECOND parameter `fcutE : Nat → Nat → List Wlabel → Mstate → Prop`, per INDEX** — one conjunct
`fcutE k s.esAg ls (stt E k)` INSIDE `execProgOk'S`'s per-index existential beside `fetchesOk fok (stt E k) s.esAg ls`
(`PfRunShape.lean:247-262`, sharing that index's `ls`; `fcutT` sees ONE `itv` and cannot guard the recurrence); M1: `fcutE :=
fun _ _ _ _ => True`; M2 (as DELIVERED [R31.1 (i)][R31.s1], `PfRunUnpinned.lean:113-121`): `fcutEM2 cohSrc (candExec c) itvOf fiOf k ag ls σ :=
(∀ base tvs, .LIFetch base tvs ∈ ls → fcutM2 (itvOf k ag) σ.msImg σ.msLog ag base tvs) ∧ fiOf (k+1) ag = fiFold (fiOf k ag) ls ∧
itvOf (k+1) ag = itvStep cohSrc (candExec c) k ag (itvOf k ag) (fiFold (fiOf k ag) ls) ∧ ∀ i ≠ ag, fiOf (k+1) i = fiOf k i ∧
itvOf (k+1) i = itvOf k i`, `itvOf`/`fiOf` bound in `srvwmoXv6M2Premises :594` with their boot values [R31.s3].  **Every new conjunct of a SHARED definition (`execProgOk'S`, `execProgOk'ST`,
`pfRunST.snoc`, `contR.cons`, `Hyps`) is a parameter instance that is `True` at M1 — `itvOf`, its recurrence and frame condition
included — so M1's content is unchanged BY CONSTRUCTION (no choice lemma `execProgOk'S → ∃ itvOf, …`), and `itvOf` is a parameter
of NO shared definition** (a fixed `itvOf` at M1 would FALSIFY the recurrence after an own store + `fence.i`, `Lang.lean:161-166`,
shrinking M1's candidate set; the worker may pick another guard shape iff the bold sentence holds).  The M1 replay lemmas
(`execPrefixPfRunProgShapedT :660`, `execWfPfRunProgShapedT :789`, `execWfPfRunPinShapedT :808`) are stated at BOTH trivial
instances (`pfRunSTApp`'s step discharges `pfCutFactsT` by `trivial`); the M2 replay `execWfPfRunProgF` (W5d's new file) turns
`fcutE`'s instance into `pfCutFactsT`'s per-fetch fact with `∀ i, (tsoShadow cohSrc st i).itv = itvOf n i ∧ (tsoShadow cohSrc st i).fiArm = fiOf n i` a replay invariant
[R31.1] (DELIVERED: `execPrefixPfRunProgF :342`/`execWfPfRunProgF :558`, `PfRunUnpinned.lean`)
beside the `.mem` projection;
`contR.cons` (`MachOfPf.lean:518-522`) and `simNode` (beside `hfT :886`) carry `pfCutFactsT`, `MachOfPf.Hyps` is parametrised by `fcutT`
and `cut` receives `pfCutFactsT fcutT cohSrc st c (hartAgent cpu) (.LIFetch base tvs)` (passed at `:1043`).  **M1 instantiates
`fcutT := fun _ _ _ _ _ _ => True`** — `pfLoadFactsTNonload`, `pfRunSTApp`, `execWfPfRunPinShapedT`, `srvwmoXv6M1PfRun`,
`srvwmoXv6M1Satisfiable`, `cutOfPristine`, `machRunOfPfRun`, `sailCycleOrder :113` (STATED AT the trivial instance [R30.s3] — equivalent to `∀ fcutT` via a one-line `pfRunSTForgetCut`,
twin of `pfRunSTForget :591-597`; text closest to today's, W-SCO's `sailCycleOrderK` adapts by that lemma alone) and
`srvwmoXv6M1Core` gain the trivial instance: **M1's statement TEXT changes; its content, name, `axioms`/`opaques` entry do not**
(both parameters; `itvOf` appears in no shared definition [R30.1]).
M2: `fcutT itv img log i base tvs := ∃ q, itv ≤ q ∧ q ≤ |log| ∧ ifetchOk img log q base tvs ∧ ∀ byte, t ≤ q`; `Hyps.cut` at M2
is the step's `pfCutFactsT` verbatim; the `itv = itvOf` replay invariant (above) is the M2-side lemma.  FAITHFUL
(proof organisation; the published quantifier, trusted base and conclusions unchanged).  Over-approximating (every `LFence false×4` raises `itv`) is not derivable at Stage 2 (`gzFetch` uses the
EMISSION's `fence.i` sites); under-approximating (`itv = 0`) breaks W4's `LIFetch` row (TsoMem fetches at `itv ≤ tvn`,
`Lang.lean:360-362`).  M1's `candKfetch` is unaffected.
**W5d-G** (Stage 2, **L** ≈ 1.8–2.2k + ONE XL risk; was
"L–XL unverified"; **[rev 44] LAUNCHABLE — the THIRD Stage 2 batch, §C top: deps (F-dep) ✓ and (K) ✓; G3 builds on (K)'s parametric `racyDX` (`Acyc`) / `normalizeOfAcyclicX` (`Topo`)**) is the graph half.  **Verdict: keep the fetch an ADMINISTRATIVE emission item** (`hemit`'s `eadm`,
`Weak/WeakRvwmoConf.lean:712-722`; `lbAdmin`, `WeakAxRealize.lean:130-134`) and add a RELATIONAL Zifencei condition
plus a "fetch fragment" of ordering edges stored as graph data, as `gdDeps` stores the store-dep fragment — NOT a
graph event ([R4.s1]'s `IF`-event shape gives the same edges at much higher cost); semantically it IS the `IF` event
at a gmo position, encoded as an EXISTENTIAL cut.  **The trusted-base item
`gzFetch G C i k base tvs`** (`GraphFetchSpike.lean:278`), per fetched byte `(t, v)`: (Z1) value — `logByte img (gwlog
G) t (base+j) = some v` (tag `t` = a gmo write index, `0` = image); (Z2) not from the future — the source is `gmoLt`
the hart's next own write `gnxw G (i,k)`; (Z3) fresh past `fence.i` — every write `w'` to the byte co-after the
source is gmo-after every contributor `c ∈ C` (own writes po-before a `fence.i` site before the slot and rf-sources
of the hart's reads po-before it: `gzContrib :272`) AND after every other byte's source (one fill instant per label).
`emZifencei G C i em` (`:312`) is `xv6ConfS`'s fetch clause: every `(LIFetch base tvs, none)` admin item satisfies
`gzFetch` at its row slot — **the slot is `GraphFetchSpike.emSlot em.emItems n :293`, the tag of the FIRST row item at
or after `n` (RULED [OWN.26]), NOT the report's "#row items before `n`": `hemit`'s `HEpair` emits TWO row items `(l1,
some k)`, `(l2, some k)` for ONE slot (`WeakRvwmoConf.lean:703-714`), so the count mis-numbers after an exclusive pair
(WEAKER on (Z2): checked against a later own write, against (H3); STRONGER on (Z3): `fence.i` sites in `[k, k+p)`
counted as contributors); `emSlotAdm :297` proves it is `k` throughout slot `k`'s admin block (G0 review item 1)**.
**(Z2) as written is WEAKER than its own reading (H3)** (G0 review item 4 — copied from the report, not a re-creation
defect): it bounds the source only by the FIRST own write at/after the slot (`gnxw`), but under RVWMO a LATER own store
`w` to a different address may be gmo-before `nxw`, so `gzFetch` admits a fetch reading the hart's own later store —
a single-hart cycle `w →E1 nxw →gpo w` that RVWMO alone cannot kill; G1 states (Z2) as (H3) reads (EVERY own write
at/after `k` is gmo-after the source) or adopts R1 (a)'s E1′ below, listing it in §B(11) as the stronger reading.
Hardware readings, NAMED in §B(11): (H1) a no-forwarding I$ with one fill instant per
label; (H2) `fence.i` completes the hart's earlier stores and reads before later fetches (for own stores = TsoMem's
`itv ≥ ownPub` drain, already beyond the spec text); (H3) stores are non-speculative relative to fetch.  [G0 review
item 6, for §B(11):] Sail's `fetch` (`LeanRV64D/Fetch.lean:253-288`) does ONE 4-byte read at a 4-aligned pc when
`Ext_Ziccif` is on (`PlatformConfig.lean:2157`), so (Z3)'s "one fill instant per label" FOLLOWS from Sail + Ziccif;
only (H1)'s no-forwarding half is a stronger hardware reading.  `fence.i`
sites come from the EMISSION, not the graph: `fence.i` and the Q7 `sfence.vma` marker share the label `LFence false
false false false` (`WeakEvInst.lean:272-275`; `WeakEvLang.lean:418-419,745`), so `emFenceI em f` := the row item at
`f` is that fence AND the latest `LInstr`/`LIFetch` in the admin block before it is `LInstr` (`emFenceISound`, M;
D40).  Scratch — RE-CREATED (G0 DONE; `propext, Quot.sound`; review `notes/W5dG-G0-review.md` OK): PROVED
`fetchCutPrefix :146` (cut form = the pf/W5d check at the realizing prefix, ONE view), `fetchCutEdge :161` (+
`fetchCutRel :248`), `fetchRelCut :215` (the relational form `fetchRelOk :183` gives the cut form at `itv := lmax cs`),
`fetchPinCutOk :322` (kernel-text instance); STATED `gzFetch :278`, `gzFetchCut :264`, `emZifencei :312`, `gfcut :104`,
`gwlog :100`, `gzContrib :272`.  **Kernel-text instance**: tag 0, image bytes, no write ⇒ (Z1)–(Z3) vacuous;
`candKfetch` + W3's `textPristine` discharge `gzFetch`; kernel-only executions get an EMPTY fetch fragment.
Consumption (`W5dG-spike.md`): edges E1 src→nxw, E2 c→w', E3 src_l→w'_j, `gmoLt` on `GD` by (Z2)/(Z3), stored as
`Gdexec.gdFetch` (D42), `F_em ⊆ GD.gdFetch` in `xv6ConfS`; retime via `L ⊇ racyD ∪ F` (the contributor SET is rf/po-
defined, retime-invariant; `normalizeOfAcyclic` renames write indices NON-monotonically, `Topo.lean:594-607`); realize
by replaying the fetch before `(i,k)`'s step at log `gwlog.take gfcut` (`linPrefixLog`, `fetchCutPrefix`).
Measured sites: `pstepPin` 19 files/121, `emFetchImg` 10/41, `gdexecQconf` 18/124, `gdDeps` 31/133, `wlblRen` 3/41.
Sizes: W3 DONE (≈ 1.9k incl. twins) [R5.2]; W5d L; W5d-G L (G1–G5; G6 shared with W11 (iii); G7 L in W11/W8); **XL risk R1 — hull
closure**: `hullOk` is rf-closed only (`WeakRvwmoHull.lean:557-560`) and knows nothing of fetch sources — a kept
fetch whose next own write was cut away loses its source; fix (a, recommended): anchor sources to EVERY po-later
memory access (E1′, stronger but gmo-true (H3)), then "kept fetch ⇒ source kept" follows from racyD-closure (M if the
cut selection is racyD-driven, XL if `t2linAux` must be re-proved); (b) keep E1 and let hulls cut each hart only
directly after a memory event (re-check `t2linAux`'s cut selection).
**(5)–(8) Segment coverage, scope pins, store-value rows, stack/cpu privacy.**  Route (M): CLOSED (F1; the pid
ledger handles wrap/collision retries, `Xv6/ProofAllocproc.lean:16-24`; text facts by `rfl`/`decide`; real
`stackOwn`/`kctx` resources).

**(9) THE gap: TsoMem is sRVWMO (+ reservation serialisation until W-RSV — GONE, rev 37); the target is RVWMO proper** [R1.7][OWN.2].
*Inventory of weaker models in the Lean tree.*  (α) `WeakMem` pf machine = sRVWMO operational (T1
`srvwmoRealizable`, `Weak/WeakAxiomatic3.lean:2088` [R16.s1]; T2 `t2Ev`, `Weak/WeakEvInst.lean:2046`) — TsoMem's strength
class; (β) `WeakPromise*` (`Weak/WeakPromise.lean:1-16`) — LB reachable, RVWMO fidelity BY INSPECTION only; (γ) PSO
two-log machine: NOTHING in Lean; (δ) graphs: the tagged cat model (§A(3)), the untagged `rvwmoCatConsistent`,
`rvwmoMinusDepsConsistent` (`WeakRvwmoGraph.lean:628`).
**`minusImpliesCat` (`Weak/AxGraphCat.lean:274`) runs the WRONG way for us**: RVWMO⁻ renders rules 1–3 as all of
`gpoloc` (`WeakRvwmoGraph.lean:224-228`), ordering a write before its own po-later same-byte read — it FORBIDS
store-buffer forwarding (N11, `AxGraphCat.lean:10-16`), so a theorem over RVWMO⁻ misses cat-consistent executions.
The whole Tier-2 chain (`rule14Linearization`, `Weak/WeakRvwmoLin.lean:1846`; `racyD`, `Acyc.lean:200`;
`t2linOfL2'''`, `Walk3.lean:77`; `xv6RvwmoSafeModulo`, `Capstone.lean:187`; 45 files, 33k lines) starts at RVWMO⁻(+deps).
**Where the cat gap lives — THREE gates, not two** [R4.5][R4.s2][R6.2] (W12 spike, DONE: 26 files in the
capstone/Walk3 closure use `rvwmoMinus*`/`gppoGmo`, classified by projection).  Survive as is (core `gwf ∧
gloadValue ∧ gatomicity ∧ gdepsWf`, never ppo): `normalizeOfAcyclic`/`topoExists`/`topoLinearizes`/`racyDMem`
(`Topo.lean:188-193,558,585,594`), `topoSupply`, `hullRealizable*`, `hullRun`; `segPinGmo` (`Glue.lean:233-240`,
rules 4, 5, deps); `cyBackwardNotAq` (rule 5).  Untouched: `rule14Linearization`/`WeakRvwmoLin` (47 `hppo`)/`Lin2`/
`Norm`/`PreNorm*`/`Xchg` — on the NORMALIZED `GD'`, RVWMO⁻ + rule 14 BY CONSTRUCTION.  **Gate 1 (rfi)**: `racyDSplit`
(`Glue.lean:101-110`) sends EVERY rf arm to `gcross`, whose `grfGmo` (`Acyc.lean:218-233`) maps the FORWARDING case
through `gpoloc`'s W→R edge — the edge cat lacks; CLOSED in the scratch (`racyDSplitC`: rfi → `rsameC`, `gcrossE` =
rfe ∪ co ∪ fr from `gwf` + lv only; §C W12 (2)).  **Gate 2 (lock kit)**: `csChained` (`KillArms.lean:499`) and the
`acq*` lemmas use rules 1, 4, 5 only (`Lock.lean:120,125,200,235`) — CLOSED, re-proved verbatim as `*C`.
**Gate 3 (the certification walk's floor kit — W10's toolkit) BREAKS, needs a REDESIGN**: `gvisUb G r n` = "every
write of index ≤ n is gmo-before r" (`Weak/WeakRvwmoFloor.lean:100-101`) is FALSE under cat for an own store forwarded
to a po-later read (it may be gmo-AFTER); `greadSrcUb` (`:442-453`) closes its po case with `gpolocGmo` W→R,
`finvStep` (`:605-619`) uses it for the coh hook; consumers `cinvReplay`/`floorOfCgraph`/`certFloorOk`/`cpolRead`
(`Cert3.lean:311,391,428,468`) via `wblkPolAt` (`Walk.lean:700-731`).  The FLOOR itself holds (`t = gwix w`;
co-maximality covers po-visible writes) but needs a per-byte coherence invariant (rules 1/2) in place of `gvisUb` —
Floor §4–§6 and Cert3 §2–§3, ≈ 0.5–1k (M–L) = **W12b** (D34).  Two smaller mismatches, VACUOUS for kernel rows
(release = `fence rw,w; sw`, `Xv6/ProofRelease.lean:83-86`; acquire = `amoswap.w.aq`), OPEN for user rows [OWN.3]: the
`wVRel` hook consumes rule 7 RCpc (`Floor.lean:21`), which `grcsc` (`AxGraphCat.lean:163`) lacks (D35 — [OWN.54] rev 42: a tree-side NARROWING of riscv.cat's RCsc, closed by D35-fix); WeakMem's
forwarded ACQUIRE load (`fwdView ws true a t = t`, `WeakMem.lean:585-591`) is stricter than cat (D36).  **So the gap is
CONFINED to the kill AND the walk floor** — not the 33k lines.  Witnesses need NO re-proof (`catADOfMinus` ∘
`minusImpliesCat`; corrects [R5.s1]).  Residual premises `l2ClaimAt`/`cutSupply`/`certSupply`/`walkSupply`/
`walkPolicy` are re-hypothesised; their discharges (W8–W11) must handle FORWARDING graphs (TsoMem forwards — fine).
*Why plain DRF does not apply.*  xv6 races by design.  The Lean pin census at THIS image [R4.1]
(`Weak/KernelPins.lean:22-23`, by `tools/gen_weak_pins.py` at `b72cbac1`): **1689 load sites: 1034 `PStack`, 3
`PPerCpu`, 289 `PCtrl`, 1 `PFence`, 180 `PDep`, 63 `PCall`, 119 `PResidue`; 58 certifying witnesses need the
sp-frame assumption `own = true`** (`KernelPinsDef.lean:447-465`).  Racy flag reads (`started` — the image's ONE racy
RAM flag, written `0x80000f7e` after `fence rw,w`, read `0x80000ee4` before `fence r,rw` [W13c b.4]; virtio
`used->idx`/`used->ring[].id`/`info[].status` — DMA-written; `ticks`, `p->killed`, `p->state`) are pinned by
branch/fence/lock.  [W13c] STALE in rev ≤ 18: `panicked` and `pr.locking` do NOT exist in this image (`pr` is one
`struct spinlock`, size `0x18`; `panic` self-jumps at `0x8000085e` and writes no flag), and the UART LSR reads
(`0x80000976`, `0x800009ec`, `0x80000a3a`, `0x80000a5c`) are MMIO (`LDev .rd`), NOT RAM flags — `KernelPins` lists
those pcs as `PCtrl` load sites only because `gen_weak_pins.py` does not separate MMIO loads (a generator fact, harmless:
MMIO loads are not `segPin` entries at the graph tier).  The applicable theorem is
ROBUSTNESS UNDER A PER-SITE DISCIPLINE (L2′ = `l2Claim`, `Weak/WeakRvwmoGlue.lean:449`: per cycle segment `segPin ∨
csHyps ∨ Bad`, `:229,400,440`) — DRF generalised: every cross-hart read is pinned by ppo before the hart's next store,
or is lock-protected (`protRead`/`wprotAt`, `Weak/WeakGhost.lean:3408,1040`), or observes an owned-unpublished message
(`Bad`).  The discipline must be established on the STRONG model's executions; the only verified source is the TsoMem
Iris proofs — which today export `mmOk` only (`MachCSL/Resources.lean:779-785`), nothing per access.
*The routes, sized candidly* [R6.s3, RULED]: **(9a)** re-verify xv6 on a weaker MachCSL instance (none exists; Xv6
cone ≈ 0.65M lines over 77k of `MachCSL`; PSO alone "2–4 weeks is the floor" in Rocq, LB has no design; linking to cat
needs a Promising≡RVWMO-grade theorem) — **XL × 2, rejected**.  **(9b)** PSO two-log machine W6 (L–XL; "RVWMO minus LB
minus deps"; LB robustness still needs the per-site discipline) — off the path, optional de-risk of W8's export (D4).
**(9c)** promise-machine robustness W7-P (`robustMain`, `Weak/WeakRobustMain.lean:1520`; fidelity EXTERNAL) — **fails [OWN.2]**, D2′ fallback only.
- **(9d) *Graph-tier robustness re-sourced from TsoMem (RECOMMENDED — the cheapest SOUND route: the T2-LIN
  induction `cycleKill`, `Weak/WeakRvwmoLinInd.lean:155`, realizes each proper hull as an sRVWMO candidate,
  `hullRun`, `Glue.lean:272-290`, W4 turns that into a TsoMem run on which the SC tree's facts hold — robustness by
  minimal violation, reusing the 33k-line chain).*  Residue of `xv6RvwmoSafeModulo` today (`Capstone.lean:187-215`):
  (R-1) `l2Claim`; (R-2) `walkSupply` (`Weak/WeakRvwmoGlue2.lean:453`), reduced to the per-state datum
  `wsegSupply`/`walkPolicy` (`WeakRvwmoWalk2.lean:453`, `Walk.lean:897`; `t2linOfL2'''`, `Walk3.lean:77`; its witness
  a hand-built LB cycle, `Weak/WeakRvwmoCycWit.lean:1-30`); `wpPackage` (`Glue.lean:338-346`: an EWP proof of ALL of
  xv6 on the weak event language — xv6 does not have it; `weakSystemAdequacyPhi`, `Weak/WeakAdequacy.lean:194`);
  `efetchItvOk` (W3/W5d); **(R-3)** the pin bridge's residual: "that a `pstepEv` run's items ARE grouped as the
  checker's pc walk assumes" (`Weak/WeakRvwmoPinBridge2.lean:28-29`) [R4.1].  **What EXISTS for W9** [R4.1]:
  `Weak/KernelPins.lean` (1,901 lines, the witness table), `KernelPinsDef.lean` (639, the checker),
  `tools/gen_weak_pins.py` (1,004; `--check`); `imagePinnedb`/`pinsCover` (`KernelPins.lean:1817-1860`); `pinSegPin`
  (PDep ⇒ `rowDeps` ⇒ `gdDeps` ⇒ `segPin`, `WeakRvwmoPinBridge.lean:284-330`), `pinSegPin'` with `checkerTaintSubProv`
  DISCHARGED for the oracle `psites` (`PinBridge2.lean:530-553`); the callee-summary table is an unread audit artifact
  (`claude-notes/design/weak-memory-route-b.md:1456-1460` [R9.2]).  **W9b**: the non-certifying classes are W8's INPUT, not `segPin` — `PStack`/`PPerCpu`
  (1,037) and the 58 `own = true` witnesses = W8's ownership (i) — no foreign writer SINCE THE LAST OWNERSHIP HANDOFF (process
  `PStack` migrates at `swtch` under `p->lock`; only `PPerCpu`/fixed per-hart stacks are static) [R23.1]; `PCall` 63 + `PResidue` 119 = 182 sites = W8's
  (ii)/(iii) (D28 RULED (a) [OWN.7]).  W8–W13 are specified in §C Stage 2.  Sizes (✓ = spike-confirmed): W8 L–XL,
  W9a L ✓, W9b in W8, W10 M–L (**unverified**; L if it absorbs W12b), W11 L [R4.3], **W12 M–L ≈ 1.2–1.8k ✓**, **W12b
  M–L ≈ 0.5–1k ✓**, **W5d-G L ≈ 1.8–2.2k ✓ + XL risk R1**, **W13 XL ✓ ≈ 7–10k lines / ~70 files (+ ≈ 0.5k under
  G3-Q (a″): (R2′), disk-read anchors [W2s])**, **W2 L + W5b′ S–M ✓ (spike-sized)**, **W4 L** ((E) wide and
  shallow; (R) the bulk).  **Total: XL** — multi-week; W13 the bulk, W5d-G's hull closure the open risk, W14 = non-vacuity.
*Recommended:* (9d), staged after M2; the three spikes are DONE and CONFIRM D25 (a) [OWN.5], SHAPE D27 (a)
[OWN.6], and REFUTE the literal [OWN.8] (D32); (9b) only if W8 wants a smaller model (D4); (9c) as D2′ fallback.

**(10) The machine-tier composition — a simulation over REALIZED, SHAPED runs** [R1.6][R2.2][R2.3][R2.3-alt]
[R3.2][R3.4].  The SC tree's conclusions are trace properties over MachCSL runs (`riscvPowerAdequacy`,
`MachCSL/Adequacy.lean:266`; `xv6FsAdequacy`, `Xv6/SystemAdequacy.lean:543`: `Reducible` + `xv6TracePure` =
`fsBootPure ∧ (pow → mmOk)`, `Xv6/SystemSlot.lean:135-136`).  The pf machine's program half is literally shared
(`MachCSL.riscvStep`, `Weak/WeakEvInst.lean:286`), so the theorem is a SIMULATION: every `wpPfStep`
(`Weak/WeakPromiseBridge.lean:339`) of the realized run is a `MachCSL.primStep` (`MachCSL/Lang.lean:599`) with the
same hart expression and observations.
*(↓) is REFUTED on arbitrary pf runs* [R2.3]: the event instance SPLITS exclusives into `LExLoad`/`LExStore`
(`Weak/WeakEvInst.lean:323-331,350-359`); a foreign store between the halves is ENABLED in WeakMem (`PFStore`,
`WeakPromiseBridge.lean:355-366`) while TsoMem BLOCKS it (`othersReserve`, `MachCSL/Lang.lean:377`).  Saved by
realized FUSED `LRmw` pairs (`lblRealizesPair`, `Weak/WeakAxRealize.lean:305-313`).  **[R2.3-alt]** a STANDALONE
`LExLoad` is realizable as a plain `LLoad` (`lbNobarex`, `:97-103`; `projLbl`'s `LExLoad → LLoad` arm,
`WeakPromiseBridge.lean:541` — [R9.2-alt]: R9 wrote `:543`, which is the `LIFetch` arm; `:537` `LDev`) while TsoMem's dangling
reservation blocks foreign stores and its exclusive read takes `topBytes` (`Lang.lean:147-153,368-371`) — (↓) fails.
**[R3.2] the shape cannot be a separate conjunct on `(c, pst)`**: the realizing `l` and the stars are existential per
index inside `execProgOk'` (`WeakAxRealize.lean:373-386`; `admStar = rtc admStep`, `:343-344`), so the premise is ONE
shaped conformance predicate **`execProgOk'S pstep pcls pst dv E`** := `execProgOk'` with (i) the left disjunct's `l`
not an `LExLoad` (re-imposing `lbFused` on the left arm only, cf. `lblRealizesUnproj :245-247`), (ii) the stars as
label-carrying `admRun`s (`Weak/WeakRvwmoConf.lean:374-381`) whose every `LIFetch` is in kernel text (M1,
`candKfetch`) / cut-form Zifencei-admissible (M2), (iii) every `LLoad` single-copy-atomic (`candSca`, below).
**LANDED (W5b DONE): `execProgOk'S pstep pcls fok pst dv E` (`Weak/PfRunShape.lean:242`, ARITY 6 — the fetch clause
`fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop` is a PARAMETER: M1 `candKfetch bcRoLo bcRoHi`, M2
the cut form; (ii) checks `fok` on the LEADING star only — the intra-pair star is `lbAdmin false`, fetch-free; (iii)
per index) and `pairAdjacent :95`** [R6.4c] over the STEP LIST; under D38 RULED [OWN.14] the I/O step is an ORDINARY left-arm realizing step (`l = LDev kind base
data …`, `projLbl … = some (.LIo …)`), so the shape clauses need only an `LDev` case (rev 9's `execProgOkA` co-design
is gone).  **`pairAdjacent`** (NEW, coined by R2; ONE text for W2 and W5b [R5.3]): *in a shaped run every
realized exclusive pair's halves `l1 = LExLoad …`, `l2 = LExStore …` (`lblRealizesPair`, `:305-313`) are consecutive
steps of the SAME hart up to its own `LInstr`-free star `admStar pstep false pm dm pm2 dm2` (`execProgOk'`'s right
arm, `:380-386`, one exec index); no other agent's step — no foreign store — lies between them*, plus the fetch/SCA
facts along the run (`pfRunS`/`pfStepFacts :273,265`); W5c PRODUCES it (`execProgOk'SNil`/`execProgOk'SSnoc`,
`SrvwmoXv6Witness.lean:260,268`, the S-variants of `Cert.lean:413`).  At Stage 2 `RunData`/`cstOk`/`segStep`/`topoSupply`/`t2linSupply` (plain
`execProgOk'` today) produce the S-variant — W11 (iii) [R4.3], one pass with W5d-G's G6 (`pstepPin` → `execProgOk'S`,
19 files / 121 sites: AxRealize 26, Supply 14, Cert 9, Cert2 8, Fab 7, Cert3 7, SrvwmoCapstone 6, CycWit 6, Cert4 6,
AxAdequacy 6, Cert3b 5, LinInd/Lin2/FabInd 4, Capstone 3, Glue/ConfWit2 2, Glue2/AxRunGV 1 — the one list; §C cites it).
**[R3.4] (↓) fails on PLAIN LOADS even on shaped runs — tearing.**  WeakMem's `readable` is per byte
(`Weak/WeakMem.lean:400-402`; `readOkD`, `WeakPromise.lean:183-188`; `rdOk`, `WeakAxiomatic.lean:122-130`), no axiom
joins one label's bytes (N10); TsoMem reads every byte at ONE `tvn` (`Lang.lean:363-367`) — a floor-0 load with `ts =
[4,4,6,6]` over two word stores is sRVWMO-consistent, never TsoMem's.  RMWs exempt (`rmwLatest`,
`WeakAxiomatic.lean:134`); fetches have the cut form (§B(4)(iii)) as their SCA.
The ISA guarantees single-copy atomicity for NATURALLY ALIGNED accesses ≤ XLEN only, so the premise is **ISA-faithful
for naturally aligned accesses; a misaligned user load is covered by N10's out-of-scope note** (D20 Spec) [R9.1] — NAMED
**`candSca c`** (LANDED `PfRunShape.lean:85`; `scaOk :72`: `∃ tvn ≤ |log|, ∀ j, ts[j]` is the latest write to byte `j`
visible at `tvn` — `≤ tvn` or the hart's own, `scaVis :61`, TsoMem's `Hist.read`; NO floor normalisation: `tvn` is not
tied to the hart's view, so `R` carries it per load, §B(10) `R`).  W2's "plain load" row is (↓) iff `candSca`;
alternative = an atomicity axiom in sRVWMO (re-opens T1, XL) — D20.  **At Stage 2 `candSca` is DERIVED**
[R4.4]: `gloadValue` (`Weak/WeakRvwmoGraph.lean:238-243`) puts ONE gmo position per LOAD EVENT — each byte's source
`gvisible` (`:236`) and co-MAXIMAL among visible same-byte writes — so a torn read is already inconsistent;
`topoSupply` linearizes the NORMALIZED `GD'` and `linCand` (`WeakRvwmoLin.lean:471`) copies labels, so `linCandSca :
rvwmoMinusConsistent G' → grule14 G' → candSca (linCand G')` (S, W11) feeds W5b's replay; `fetchCutPrefix` (W5d-G)
plays the same role for fetches.
*(↑) receptiveness is NOT available on route (M)* [R2.3(iv)]: weak-side `Reducible` would need the weak WP package;
(a) is stated for the realizing MachCSL run, the free weak-side sentence is "the realized pf run never enters the
retry arm" (D15).  *Single era* [R2.2]: `epowerFork` forks no power thread (`Weak/WeakEvLang.lean:201-204`), so
multi-era conclusions are NOT transported; W4's run is prefixed by the `PowerOn` step (D14).
*Layer 2 after the W2 spike [W2s] (D7 STOP → RESOLVED-BY-REDESIGN; G1-Q–G3-Q in §D).*  **The per-label (↓) table**
(`W2-spike.md`; its faithful/stronger/weaker column [R9.s4] is MISSING — D7's marks stand in; W2's ACCEPTANCE
requires it [R10.s5]; DELIVERED by W2b — `Weak/PfStepTsoView.lean` header): ✓ `LSilent` (0 TsoMem MEMORY changes;
**[W4c B6 correction] 1 `primStep` with `σ' = σ` — `regRead`, `branchAnnounce`, `cacheOp`, `tlbi`, `translation*`,
exceptions, `cycleCount`, `message`, `getCycleCount`, `choose` each have an `evStep` arm (`Lang.lean:358,386-399`); ONLY
the lost-SC RETRY self-loop `LSilent` (`WeakEvInst.lean:363-365`; TsoMem's `blockedStep` needs `othersReserve`, false
under `pairAdjacent`) and the parked-fence FIRE (`pstepNode :409-412`; TsoMem applied the whole barrier at the node) are
0 `primStep`s — W4 is a stuttering simulation in exactly those two rows**), `LInstr` (0 memory changes, 1 `primStep`:
the BOUNDARY `LInstr` is `hartStep .pure` (`Lang.lean:533-535`; under W-RSV the arm that clears `resv`, matching
`instrPost`'s `wRes := none`, `WeakMem.lean:720-721` [R12.s5]), the ANNOUNCE `LInstr` and the `sfence.vma` marker
`LFence false×4` are `evStep .instrAnnounce`, `σ' = σ` (`:396`))/`LRegW`/`LCtrl` (`setReg`, `:359`), `LIFetch` M1
(pristine text, `Wp.lean:1478, 1490`), hart `LStore` (`¬ othersReserve` from
`pairAdjacent`; the acceptance table's `LStore` row records BOTH shadow effects — the (a′) `coh` RESET [R11.1] and
`resv := none` (unchanged, `Lang.lean:152`) — `R-view` stays equality [R11.s4][R12.s5]), disk `DWrite` (`storeDma`, `¬ anyReserve`), `LFence`
non-`fence.i` (**`fenceRow`, PROVED**), `fence.i` (identity vs `itv`), the parked `fence rw,w` (0 steps; `wRelp`/`wPub`
inert — suspect CLOSED), `LExStore` (its row records the SAME two effects — reset + `resv := none` — plus the `excl &&
acq` floor move to `top + 1`, `Lang.lean:150`; the reset half after W-COH [R14.2]), `LDev`; **conditional**: `LIFetch` M2 (§B(4)(iii) (i)–(ii)); hart `LLoad` iff (★);
`LExLoad aq` bytes ✓ (`exclOkTs` + `pairAdjacent` make `t` = `topBytes`), views ✗ (G1/G1′); **✗** disk `DRead` (G3).
Suspects: fence-clears-reservation VACUOUS on shaped runs; tearing CLOSED by `candSca`; parked release CLOSED; the `.aq`
off-by-one REFUTED as sized — it is G1, off by `top − t`.  **Rev 13–18: only `fenceRow` was in Lean.  Rev 19: EVERY
row is in Lean, in two halves** — the MEMORY half W2a (`Weak/PfStepTsoMem.lean`: `rmem` = `R-log`/`R-img`/`R-hist`/
`R-resv`, field equations on `.mem`/`.log`/`.resv`; `pfLoadRowMem` = the FlatMem ↔ `histOf` bulk, `histOfFind :250`
being TsoMem's `find? (HEnt.visible i tvn)` = the SCA source in entry form) and the VIEW half W2b (`PfStepTsoView.lean`:
`viewRel` = `R-view` EQUALITY per hart with `tsoShadow cohSrc`; `rowLoad` at `minView` = the shadow's `shTvn` with
`tsoLoadOk` (`tv ≤ tvn ≤ top`, `cohOk`) and `minViewLeSca :524` (`tvn ≤` every `scaOkT` witness); instance-independent
rows for ANY `CohStamp`).  What W2 still OWES (§C W2 CLOSE): the ONE theorem `pfStepTso` composing the halves.
**The gaps.**  **G1**: after `amoswap.aq` reading the lock word at `t` (write at `top+1`) TsoMem's floor is `top` at
the read and `top+1` after the pair (`Lang.lean:136,151`; `tsoAqPairTv`), WeakMem's `wVrNew` is `max(wVrNew, t)`
(`exloadPostRunD`, `WeakMem.lean:834`; `loadPostAt :608` aq arm): a later plain load of a byte written in `(t, top]`
reads stale in WeakMem (`g1Run`; cat-consistent: gmo = AMO, `ld x`, `x := 1`), TsoMem cannot.  The image's `acquire`
is `amoswap.w.aq; sext.w; bnez; jal mycpu; sd a0,16(s1); ld …` (`KernelImage.lean:2265-2290`) — NO fence after the
swap, the whole critical section sits in the window; `release` = `fence rw,w; sw zero` (`:2361`), `sr = false`, leaves
`wVrNew` alone.  [Correction: NO fence closes the window — fences raise `wVrNew` only to `wVrOld`/`wVwOld`
(`WeakMem.lean:674-688`), neither need reach `top+1`; the debt persists until the hart's view passes it otherwise.]
**G1′**: `rv := top` at ANY exclusive read (`afterExcl`, `tsoExclRv`); a later `fence r,*` lifts the floor there.
**G2**: §0 F1 (iii).  **G3**: `dmaView` reads the TOP (`Lang.lean:189,535`); the disk row's `DRead` is `LLoad aq false`
at the disk agent's floor.  [Correction: `dreadAvailIdx` is an ACQUIRE read (`VirtioProg.lean:375-376`, `aq = true`),
the ring/descriptor/data reads plain (`:378-386,606-619`): the MP pattern HOLDS in WeakMem — descriptor reads see every
write log-before the avail index the device observed; the gap is staleness w.r.t. the TOP (an older avail index →
`DIdle` where TsoMem's device serves the request; a descriptor/buffer byte re-written in `(t, top]`), not "no fence after START".]
**The redesign — ONE mechanism for G1/G1′, the `coh` side of (★) and the M2 cut: the TsoMem view SHADOW.**
`tsoShadow st i : (tv, rv, coh, acq, itv)` is TsoMem's per-hart read side REPLAYED deterministically over the pf step
list (`Lang.lean:134-163` per label; `pub` from the log; a plain load at the MINIMAL legal view `tvn := max(F, max_{foreign j}
t_j)`, `F := max(tv, coh over the footprint)`).  Then **`R-view` is EQUALITY** `tv_T = tv_S`, `hr_T = hr_S`, `itv_T =
itv_S` — no debt bookkeeping; `R-log/position/author` (`σ.log[k]` = `(pcLog[k]).wmTid` as an agent; hart `i` =
`hartAgent i`, the disk row = `diskAgent`), `R-hist` (LANDED as `PfStepTsoMem.rhist :57` — `∀ pa, inRam pa 1 → σ.mem[pa]?
= some (histOf img log (paZ pa))` and `none` off RAM; [W4c E-M7] the spike's `σ.mem[pa]? = histOf …` did not type-check
(`imgFlat_get?` is an `Option Hist`, `TsoMem.lean:201-205`; `histOf` a `Hist`) — W2a's `some`/`none` form is the one W4
consumes; timestamp = position + 1), `R-img` (`pcImg = imgZ bootImage`), `R-resv` (`none` unless `midPair :46`) are the
spike's, in `rmem :62`.  [Correction, reason fixed by [R10.s1]: the spike's `tvn :=
max(tvn_sca, F_T)` is too LARGE — not because `rv` would break `R` (moot under EQUALITY) but because `rv` feeds `tv` at
the next `fence r,*` (`Lang.lean:155-160`, `fencePost TsoMem.lean:345`) and Stage-2 derivability needs every
contributor to `F` to be ≤ the gmo position of a later load, which rule 4 gives for the EARLIER load's gmo position =
its `tvn_sca`, not for an arbitrary larger view; take the minimal view.]  **The shadow is a function of the step-list
PREFIX, not of the configuration** [R10.3]: a `Wpcfg` holds the log (writes only), the WeakMem `Wstate`s and program
states (`WeakPromise.lean:135-139`); fences, plain loads and aq pairs move `tv/rv/coh/acq/itv` (`Lang.lean:127-163`)
and leave no trace in `pcLog` — so W5b′ threads the shadow (§C).  [R10.s2] Under equality-`R` every POSITIVE row
reduces to "a TsoMem step EXISTS at the shadow's view with the pf bytes" (TsoMem's fence step always exists and the
shadow IS its view; `fenceRow`'s inequality is the spike's record, no longer the row's content).
**`candScaT` — G1-Q RULED (e) [OWN.17]** := `scaOk` plus `F ≤ tvn`.  **Why it discharges (★) ALONE** [R10.1]
(recorded so W2/W4 do not re-derive it): hart load `r` at the shadow's minimal view `tvn := max(F, max_{foreign j}
t_j)`: `tv_S ≤ tvn`, `cohOk`, `tvn ≤ top` hold by construction (`t_j ≤ |log|`); `Hist.read` at `tvn` returns `t_j` per
byte iff no visible later write to byte `j` — own later writes are excluded by `scaByte` (visible = own), foreign
ones in `(t_j, tvn] ⊆ (t_j, tvn_sca]` by `scaByte` at `tvn_sca` once `F ≤ tvn_sca` (foreign `t_j ≤ tvn_sca` by
`scaVis`).  G2-Q does NOT enter (★): it decides whether `candScaT` is TRUE/DERIVABLE, i.e. which `coh` stamp the
shadow replays.  **Stage-2 derivation (W11 (iv) `linCandScaT`) — LANDED [R20.3]** (`Weak/RvwmoXv6ScaT.lean:757`; premise
set `gwf ∧ gppoCat6Gmo ∧ gloadValue ∧ grule14` on the linearized graph — rules 2, 4, 5 used, `gatomicity`/rule 12 not; NO
separate `ptraceRel ⊇ gmo|W` statement: (iv)a's `linTvnScaLe :194` carries it; **[R21.2] W11 (v)/W13 (L) consume
`linCandScaT :757` (or `linCandScaTMinus :787`) on the NORMALIZED hull graph `GD'` from `normalizeOfAcyclic` (rule 14 by
construction, `WeakRvwmoTopo.lean:596-605`); `linCandScaTCatT :780` is a statement about the INPUT graph and is NOT on
the Stage-2 path — its `grule14 GT.gtG` (`WeakRvwmoGraph.lean:266-267`) fails on every LB/W→W graph §A(3) admits; the
premise `gppoCat6Gmo GD'.gdG` is W12 (1)'s new deliverable**): `tv` part — the SCA witness `tvn_sca := #writes
gmo-before r` is a legal `scaOk` witness (`tvn_sca ≤ |log|` at `r`'s trace position: every `w <gmo r` has `w <gmo
nxw(r)` by rule 14 on `GD'`, so `gwix w < gwix (nxw r)` and `w` sits in an earlier `rblocks` block, `Lin.lean:316,440`;
bytes co-maximal by `gloadValue`); `tv_S` after an aq pair `= gwix(LRmw)` and `LRmw <gmo r` by rule 5 (`gacqPo`,
`LRmw` is `lbIsR ∧ lbAq`); `tv_S` raised by `fence r,*`/`rw,*` to `rv`/`pub`: every contributor (an earlier load's
minimal view ≤ its `tvn_sca`; `top` at an exclusive read `= gwix(LRmw) − 1`; `ownPub = gwix` of the last own store)
is the gmo position of an event rule 4 puts gmo-before `r` — G1 and G1′.  **`coh` part — the G2-Q case split**
[R10.1][R10.2][R11.1][R11.1-alt][OWN.23]: under the ruled (a′), BOTH components (`afterLoad` stamps `coh a := max (coh a) t_a` ONLY for a
FOREIGN source — `e.tid ≠ hartAgent cpu`, hence `t_a ≤ tvn` automatically; own-sourced bytes, forwarded or below the
view, UNSTAMPED; `MState.store` RESETS `coh a := 0` on its footprint) `coh a` at `r` is the max of the foreign-source
stamps of the loads of byte `a` po-after the hart's LAST own store to `a`; for each such `r_prev` with source `w'`:
same source → `w' <gmo r` by `gloadValue` (`w'` foreign); different source (foreign `w''` or an own `m` po-before
`r_prev`) → no own write to `a` po-between, so rule 2 (`gppo2`) gives `r_prev <gmo r`, and `w' <gmo r_prev` by
`gloadValue`; own write `m` to `a` po-between → the stamp was RESET, later stamps recurse — THREE cases, GRAPH-ONLY,
each giving `gwix w' ≤ tvn_sca(r)`.  Why FOREIGN and not "`t_a ≤ tvn`" [R11.1-alt]: an own store `m0` BELOW the view
(`m0`'s position ≤ `tvn_min(r_prev)` because another byte of `r_prev` has a later foreign source) would be stamped at
`gwix m0`, yet cat lets a later same-source read `r` sit gmo-BEFORE `m0` (own stores are visible by po, no `W;po;R`
ppo, same source ⇒ no rule 2): hart A `sb a` = `m0`, `lh (a,d)` = `r_prev` (a from `m0`, d from foreign `w_d`), `lh
(a,c)` = `r` (a from `m0`, c from foreign `w_c`); hart B `w_c`, `w_c'` (both to c), `w_d`; gmo `w_c <gmo r <gmo w_c'
<gmo m0 <gmo w_d <gmo r_prev` is cat-consistent (ppo on A empty; load-value ✓), but with the stamp `coh a = gwix m0 >
gwix w_c'` TsoMem reads `w_c'` for byte c — `candScaT` FALSE.  **Hence the foreign-only component is LOAD-BEARING for
(9d), not cosmetic [R12.2][OWN.23]**: under the reset ALONE that candidate is cat-consistent yet has NO TsoMem
schedule, so at Stage 2 `cycleKill`'s realization of a proper hull as a TsoMem run (§B(9d), `hullRun`, W4) FAILS on it
and the robustness theorem is UNPROVABLE — a hole in (9d), not merely "W11 (iv) harder"; the only repairs are the
component itself (RULED) or a W8 census excluding the shape (a (b)-style TRANSPORTED fact, M, **unverified**) — MOOT.
Under (a‴) (no coherence floor) `F = tv_S` and the part VANISHES; under (b) (TsoMem keeps the footprint stamp) it is NOT graph-derivable — the
plan's own `g2Run`/`g2Tso` (`TsoOfPf.lean:160-199`) is cat-consistent with `F = coh b = 2 > tvn_sca = 0` — and comes
only from W8's census (vi) TRANSPORTED through `R`'s log identification (po-induction: every load's `F` ≤ the gmo
position of every later load sharing a footprint byte).  At M1/M2 `candScaT` is a PREMISE (restricts the candidate's
log order to a gmo-extension — internal milestones only).  **`candDiskLat` — G3-Q RULED (a″) [OWN.17]** :=
every disk-row `LLoad` is `latest` per byte — the `lat = true` CONDITION of `readOkD` (`WeakPromise.lean:183-188`) as a
SHAPE clause, NOT a label change (`latFree`, `WeakPromiseFact.lean:61`, consumed in 16 files incl. `lblRealizes`,
`AxRealize.lean:241`, and `pstepEvLatFreeProg`, `WeakEvCapstone.lean:1052`, stays TRUE): the `DRead` row then matches
`dmaView`.  Stage-2 derivation: disk-row reads become rule-14 ANCHORS of (L) (`gnxa` ∋ disk reads: the trace respects
gmo between a disk read and EVERY write) — consistent because the disk row's po is gmo-ordered by (R1) (DMA writes →
COMMIT), (R3) (COMMIT → next START), (R2′) (START → reads) and rule 14 (a request's reads precede its writes,
`VirtioProg.lean:606-619`); `normalizeOfAcyclic` keeps the anchors as it keeps I/O positions.  **G2**: NO shape clause
closes it against TsoMem AS IS (`g2Tso`: every legal `tvn₁ ≥ 2` stamps `coh b`; the minimal view does not help) — the
shadow is PARAMETRIC in the stamp pair and G2-Q picks the instance (RULED (a′), BOTH components [OWN.20][OWN.23][R11.1]).  **(★) for a plain load of hart `i`**: no write by
another agent to byte `base+j` in `(t_j, F]` — a LOG-LEVEL fact about ONE load, DISCHARGED by `candScaT` alone
[R10.1]; what W8 may still owe is NOT (★) but the census (vi) feeding `linCandScaT` under G2-Q (b) [R10.2] (§C W8).
**Log identification** (W8/W11 vocabulary): pf message `k` = the TsoMem store at timestamp `k+1`, same author/
footprint/bytes; classes stay pf-side (`wmAk` has no TsoMem image; `protReg`/`badSeg` read the pf log).  W14's SC run
is unaffected (every load at the top, so the corrected (a′)'s stamps are ≤ top and its resets harmless [R11.s5]).  (↑) NOT claimed.  **D19 RULED (b) [OWN.19], form (i-a) RULED [OWN.22][OWN.23]** (reservations cleared at the instruction
boundary, §C W-RSV [R11.2][R12.1]) changes three rows' ARGUMENTS, not the mechanism: hart `LStore`/disk `DWrite` need
`¬ othersReserve`/`¬ anyReserve` only against IN-FLIGHT (intra-instruction) reservations, which `pairAdjacent` gives
without clause (i); `LExStore` needs NOTHING of the own reservation (TsoMem never reads `σ.resv cpu` for its own
store, `Lang.lean:147-153,372-378` [R11.2]); `R-resv` becomes EXACT (`resv_T c = snapshot of wRes_c`, both `none` at
every boundary — `instrPost`, `WeakMem.lean:721-722`).  Size: W2 L — DONE as W2a (781) + W2b (807), the CLOSE S–M
(§C W2) + **W5b′ DONE** (`Weak/TsoShadow.lean`, 996: `tsoShadow` over the step list with `itv` + `fiArm` in `ShFull`
(the verify's blocking fix: the step-list shadow carries `itv`, the trace shadow `shadowOf` is memory-only [R11.3]),
`CohStamp` PAIR with the three instances, `scaOkT`/`candScaT`, `diskLatOk`/`candDiskLat`, `execProgOk'ST`/`pfRunST`
BESIDE the landed names (`PfRunShape.lean` untouched — deviation 2; W5-pre re-points `srvwmoXv6M1Premises`), the
re-proved replay `execPrefixPfRunProgShapedT` with the projection lemma [R10.3]) + W4 (L: structural half F1–F8 M–L
DONE (`MachOfPf.lean`, 1659), disk rows F9 L — UNBLOCKED by W-DISK [W4c][R16.3]) + W-DISK (DONE 2026-10-12) + W-DMA0 (DONE) + M (W5; W5-pre DONE
[R16.4]) + M–L (W5c ✓) + L (W5d).
It lifts the WHOLE system theorem; (9d) reuses it both ways; **the log identification carries `protReg` and `¬ badSeg`**
(W11).  [W4c B6] The plan's stuttering BOUND `n ≤ |st|` was FALSE once disk rows are included (MachCSL's virtio needs
internal `choose`/`get`/guard/`fork`/`modify`/restart steps with no pf counterpart, `Virtio.lean:522-552,559-579`); no
consumer cites it and adequacy quantifies over every `n` (`Adequacy.lean:118,386`) — DROPPED (E-S6).

**(11) Model fidelity and named assumptions (trusted base, list in the header)** [R1.1][R1.7][R2.4][R3.1][R3.2]
[R3.4][R4.2][R4.4][R6.1][R6.2][R6.3].  Candidate/conformance premises: `execProgOk'S` (fused exclusive pairs — "a
dangling LR or failing SC is outside the theorem", D19; M1 only: `candKfetch`, D21); `candSca` (ISA-faithful for
naturally aligned loads, D20 [R9.1]; **M1/M2 ONLY** — derived at Stage 2); cut-form Zifencei admissibility (M2); **the published model is the
TAGGED cat transcription** `rvwmoCatConsistentT` + the tagged conformance text `gdexecQconfT` (NEW trusted-surface
text; the untagged model's rule 12 is a strengthening of riscv.cat the tree marks UNSOUND — D33); **the graph-tier
fetch model** (W5d-G `gzFetch`/`emZifencei`, readings (H1)–(H3), §B(4)(iii) — NO reference model, RVWMO has no
instruction-fetch model; D27 RULED (a) [OWN.6]; **[rev 46] + (H3′), G1's E1′ form of (Z2)** (`GraphFetchSpike.lean:292-312`; R1 (a) of §B(4)(iii), G0 carry-over (4)): a fetch's source write is gmo-before EVERY memory access — load or store — of the same hart at or after the fetched slot ((H3) extended from own stores to own loads); Spec: RVWMO has no fetch model, Zifencei only makes prior stores visible to later fetches after `fence.i` (silent on fetch vs later data accesses), Sail fetches each instruction before executing it, per hart sequentially (`Step.lean:335`), PMAs silent — STRONGER than the spec text, true of Sail's per-hart order and of in-order-fetch hardware); **the graph-tier I/O-ordering PLATFORM assumption** (W13
`ioResidueGmo`, LANDED `Weak/GraphFabResidue.lean:99`: (R1)–(R3) of §A(†) over every row's I/O events — hart MMIO, PLIC
pin deliveries, the disk agent's START/COMMIT (W-DISK DONE: START and the ring POP [OWN.32], COMMIT retired), the device threads'
fabric moves; D32 RULED (a′), D37 RULED (a) [OWN.12], D38 RULED [OWN.14]; no reference model [R7.1b][R7.3a]).  **Stated as a RESIDUE** [OWN.12], split EXACTLY: the GRAPH MODEL gives I/O events
rule 5 (acquire read → later I/O; a strengthening of (c1), D52) and NOTHING else — no rule 4 (the i/o bits die in
Sail's decoder, FIOM = 0, §A(†) [R8.3d]; `LFence` is `pr pw sr sw`, `WeakAxiomatic.lean:90`), no rules 1–3 (no byte
footprint), and — D50 RULED (b) [OWN.17] — the (c1) DEPENDENCY edges (W13 (F-dep): the graph-stated (F3)) — while
the ISA PROSE additionally gives (F1), (F2), (F4)–(F6) (§B(11b)), expressible only via the rest of D46 (b) (RULED (a)
[OWN.17]: prose); the ASSUMPTION is the rest — each I/O access acts as a ONE-WAY FENCE for the issuing
row's RAM accesses, and I/O accesses serialize as the fabric does.  "PMA strong ordering" is NOT a justification (it
orders I/O accesses within one channel, never against main memory; D37(c) dropped) [R6.3ii][R7.2b].  The platform is
D37 (a)'s (QEMU TCG), host-dependent.  **Trusted USES, per arm** [R6.s4][R7.2c][R7.3d][OWN.12][R8.2b], list in the
header (CROSS-CHECKED against the image by the W13 I/O census [W13c] §(c): every entry below is confirmed; the
census's OMISSIONS are added, marked [W13c]): (R1) for RAM STORES before an I/O event — `plicinithart`/`plicinit`,
`uartinitone`'s seven `WriteReg`s (`0x800008a0 … 8d4`), the lock's store half and prior stores before
`uartputc_sync`'s LSR read (`0x800009ec`) AND [W13c] before `uartwrite`'s LSR `0x80000976`/THR `0x80000988` (same
shape: `acquire(tx)` at `0x8000096e`), `virtio_disk_intr`'s STATUS read (`0x80005d4a`), [W13c] `virtio_disk_init`'s
FENCE-FREE init sequence (ring-pointer stores `0x800059f6-0x80005a04` and `kalloc`'s three `memset`s before QUEUE_NUM/
the address registers/QUEUE_READY `0x80005a42-0x80005a76`; `free[0..7] = 1` before DRIVER_OK `0x80005a9c`; `initlock`
before MAGIC; `kalloc`'s lock stores), EVERY RAM store po-before a PLIC pin delivery (`pstepPlic`, `devintr` entry on all
harts — (F5) orders pre-trap LOADS only) AND [W13c] the stores BETWEEN the delivery and the claim `0x80005886`
(`kernelvec`'s saves `0x800057c2-0x800057e2`, `uservec`'s trapframe saves `0x8000600c-0x8000607a` — physically RAM,
`usertrap`'s `epc` store `0x800026de`, the prologue saves `0x80002654`) AND [W13c] handler-body stores before
`plic_complete` `0x800058aa` or `uartintr`'s next-iteration LSR `0x80000a5c` (`cons` stores `0x8000032e`/`0x80000338`,
`b->disk := 0` `0x80005d92`, `used_idx` `0x80005da4`, release stores `0x80000cfa`), the device row's DMA accesses
before a UART/PLIC move (D51); (R2) for every device STORE not followed by a PO-fence — THR, NOTIFY (`0x80005c92`),
`plic_complete`, `plicinithart` (only the ACK at `0x80005d52` is fence-covered, `0x80005d54`, and under D48 (a) even
that is a GRAPH-tier use), [W13c] `plicinit`'s `0x8000582c/2e/30`, `uartinitone`'s seven stores (followed by
`initlock`'s RAM stores), `virtio_disk_init`'s MMIO stores (followed by `kalloc`/`memset`/`free[]` stores), the device
row's DMA writes after a UART/PLIC move (D51); [W13c] (R2) for I/O LOADS is a presentation gap only — under (F-dep)
every branched-on load ctrl-pins all later stores (rule 11, `dtCtl` never reset); STATUS `0x80005d4a` is subsumed
through ACK, ISR `0x80000a36` is a DEAD value; (R3) cross-channel issue order — "UART then PLIC in `main`"
(`0x80000f10` → `0x80000f54`) AND [W13c] PLIC → virtio in `main` (`0x80000f58` → `0x80000f68`), UART1 → PLIC on harts ≥ 1
(`printk` `0x80000efc` → `plicinithart` `0x80000f08`), inside every handler PLIC claim → UART (ISR/LSR/RHR, the echo THR,
the unexpected-irq `printk` THR) or virtio (STATUS/ACK) → PLIC complete (the irq → complete and RHR → echo pairs are
dependency-pinned graph facts under (F-dep)), process-context UART0 THR (`consolewrite`) and virtio NOTIFY in one row —
and the unlocked cross-hart PLIC claim/complete races (no lock in `0x80005870-0x800058b4`).  NOT uses in the ISA-prose
sense (GRAPH-tier uses — the fence/trap ones for good, D46 RULED (a); the dependency ones become graph FACTS under D50 (b)): the pre-NOTIFY direction (two `fence iorw,iorw`), the post-ACK loads (the third
fence), loads before a handler's claim (precise traps), dependency-pinned sources of a device store; not uses at all:
the disk row's DMA-before-COMMIT (device model), the racy flag `started` (stale reads stay in the quantifier) — [W13c]
rev ≤ 18's "`pr.locking`/`panicked`" named flags that DO NOT EXIST in this image (§B(9)); `uartstart` likewise does not
exist (transmit is synchronous: `uartwrite` writes THR under `tx_lock` and sleeps on a busy LSR, no tx ring).
**User-row gaps under [OWN.3]** [R6.2] (D35/D36 RULED (a) [OWN.13]): rule 7's single-bit pairs (CLOSED by D35-fix [OWN.54], rev 42) and forwarded plain `LLoad aq`, both
vacuous for kernel rows.  Strengthenings carried INTERNALLY by TsoMem/sRVWMO (gone once (9d) lands): "stores never
early"; reservation serialisation — GONE (W-RSV DONE 2026-10-12, rev 37; D19 RULED (b) [OWN.19]); footprint coherence
stamping — GONE (W-COH landed 2026-10-11, §0 F1 (iii)).  **RESOLVED (W-DISK DONE 2026-10-12, rev 28) — the pf DISK PROGRAM's drift
from the device model of record (E-D1 RULED (a) [OWN.29]; §0 F1, §C W-DISK), kept as the RECORD of what the program WAS**: `virtioProg` reports the used element's `len` as
the DATA length (`r.len`; virtio 1.x: bytes written = data + status for IN, 1 for OUT — UNFAITHFUL, MachCSL's `usedLen`
FAITHFUL), answers UNSUPP to FLUSH (MachCSL OK — [R16.5] xv6 clears `F_FLUSH`, so BOTH are model choices on spec-UNSPECIFIED
behaviour; xv6 never issues FLUSH — vacuous), writes
ANYWHERE on a malformed chain (`DWild`; MachCSL stalls; spec: unspecified, the driver MUST NOT publish such chains —
unreachable under the verified driver), reads each descriptor as FOUR reads (a torn descriptor is pf-legal even under
`candDiskLat`; MachCSL ONE 16-byte read — spec silent on burst granularity), and moves `isr`/`usedIdx` at a separate
COMMIT after the used-idx write (MachCSL fuses them — STRONGER than the spec's "device MAY then notify", MachCSL's named
choice).  W-DISK has LANDED: the ONE device model is MachCSL's; this entry stays as the resolved record (rev 28 did not delete
it), the model-of-record choices it names survive in the next list [R16.5], and the aligned program's own marks are the
(M1)–(M9) table in `Weak/VirtioProg.lean`'s header.  Machine-model choices:
exactly 8 harts booted (D8 RULED (a) [OWN.19]); **ONE sequential device row** (`i =
NCPU`) for the disk program, the UART threads AND the PLIC gateway (`pstepDisk = pdiskProg ∨ pdiskUart`,
`WeakEvInst.lean:518-526`; Rocq deviation 5) — so (R1)/(R2) order the disk's DMA accesses against UNRELATED UART/PLIC
moves: a model artifact, STRONGER than any spec text, named as D51 [R8.2a]; **[R16.5] the virtio DEVICE MODEL of record
(`MachCSL/Dev/Virtio.lean`, to which W-DISK aligns the pf program): (i) the used-idx write FUSED with the completion
(`isr` raised, `usedIdx+1`, in-flight removal — `complete :423-427`, `serve :552-555`): STRONGER than virtio 1.x's "the
device MAY then notify" (a delayed notification is spec-legal, excluded); (ii) STALL on a malformed descriptor chain
(`stall :457`, `serve :524`): a choice on spec-UNSPECIFIED behaviour (the driver MUST NOT publish one; unreachable under
the verified driver); (iii) ONE 16-byte descriptor read per descriptor (`fetch :466-481`): spec silent on burst
granularity — a choice; (iv) FLUSH answered OK regardless of negotiation (`statusOf :377-379`; xv6 clears `F_FLUSH` —
`SpecVirtioDiskInit.lean:10`, `ProofVirtioDiskInit.lean:935`, `vdi_wce_15 :559`): a choice on UNSPECIFIED behaviour,
vacuous for xv6; (v) DMA READS at the TOP of the store order (`dmaView`, `Lang.lean:189`; F6, G3-Q): STRONGER than the
appendix's DEVICE sentence; (vi) [OWN.32] the ring POP as a device-internal `dev` event under (R1)–(R3) (D49 (a)/D51
class: STRONGER than the spec's silence by the row's coupling of the pop to its DMA accesses; EQUAL to MachCSL's step
structure; **[R22.s5][R22.2]** the disk row's `gfDev` members are this `dev`-kind pop plus the request's fabric-moving RAM
stores — status, used element, used idx, the IN fill when its `pre` moves a phase — while hart rows' I/O-class events are
members by CLASS whether or not they move the device, §A(†)); (vii) [R16.s3] write-through durability under `wce = false` (`completeOk :412-414` needs `!reqCached`, so a
WRITE completes only after the root loop DRAINS it, `body :581-586`) — the pf program lays the payload into its `cache`
at the status write exactly as `capture` does and DRAINS every cached sector at the request's completion gate ([R19.1]
(e): STRONGER than MachCSL's any-time, one-sector-per-step drain only in WHEN; pf ⊆ MachCSL; device-internal, every spec
silent); `R-dev` is FULL equality of `dvirtio` (`disk` and `cache` included) at every pf-step boundary of the matched run,
so a future crash-row consumer sees ONE durable image (rev 22's "`diskOf` is MachCSL-only" caveat is WITHDRAWN); [R18.2]
until W13 (I) the INTERNAL fabric bundle
`gfexecConf` (D39) is vacuous for a device-active disk row (interim `LDev`-free-disk-row clause, the
`ioResidueGwfInterim` pattern; LANDED `WeakRvwmoFab.lean:633`, with `hemitfStatesQ :396`/`hartConffStatesQ :556`'s `devQuiet ∧
LDev`-free hypothesis and the quiet-boot hypothesis `∀ i, i < N → devQuiet (boot i)` discharged by `epsInitQuiet`) — the
published bundle `xv6ConfS` is (I)'s; (viii) [R17.4][OWN.33] the pf disk program serves ONE
request per burst, in available-ring order, to completion before the next pop (`pdiskProg`'s single residual program,
START only from `none`, `WeakEvInst.lean:499-503` after W-DISK; `virtioProg` `VirtioProg.lean:438`) — STRONGER than virtio 1.x
(the device may process requests in any order and complete them out of order) and than MachCSL (one forked `serve` task
per request, `Virtio.lean:579`, run concurrently); excluded executions: two requests' DMA accesses interleaved, a later
request completing first; the SOUND direction for W4 (pf ⊆ MachCSL); xv6's correctness does not depend on completion
order (`virtio_disk_intr` dispatches on `used->ring[].id`); W-DISK-Q4 RULED (c): kept and named now, a concurrent pf disk
agent is the named follow-up after M2; W13 (W)/W14's disk witness is unaffected; (ix) [R19.1][R19.s3] pf drains every
cached sector at the GATE of each request (MachCSL: any time, one sector per root-loop step, `body :581-586`) — pf ⊆
MachCSL, device-internal, every spec silent; EQUAL durable image at pf-step boundaries (replaces (vii)'s crash-row
caveat); NO §A(6) entry needed [R20.s3]: a drain emits no label (`drain :429-432` is a `modify`; `drainAll` sits inside
the used-element `pre`), so WHEN pf drains changes no graph event and excludes no graph — unlike (viii); **(x) [OWN.40][rev 31]
the pf disk program STALLS an OUT request whose capture buffer would wrap past `2^64`** (`VirtioProg.outWraps :421` in
`dcomplete :424`: `buf + len > 2^64` → `DRet DStall`; header deviation 6) — MachCSL's `dmaRead` WRAPS its `PAddr` and reads the
top of DRAM while the pf load reads `Int` addresses where `imgZ` aliases the boot image, so the two sides would capture different
bytes; the stall is FAITHFUL to the PMAs (no physical memory exists past the top of the address space), STRONGER than MachCSL's
`serve` (which performs the wrapped read), the SOUND direction pf ⊆ MachCSL (the MachCSL task is simply never scheduled again,
`PosRel.stall`/`caseStall :1994`, 1 → 0); UNREACHABLE for xv6 (1 KiB buffers in DRAM); F9's former interim `Hyps.noWrap` is
discharged INSIDE F9 (the capture read's no-wrap bound from `outWraps r = false`, every other disk read ≤ 16 bytes,
`smallNoWrap :1653`); MachCSL and `Xv6/` UNTOUCHED; like (ix) it emits no label (a stall is the `LSilent` self-loop), so no §A(6)
entry**; Svadu A/D write-back as a plain
view-neutral LR/SC; DMA as a store-order agent; TsoMem's instruction-fetch model (`MachCSL/TsoMem.lean:34-39`,
`Lang.lean:360-362,155-163`) — beyond RVWMO's text (Zifencei); **[OWN.35] the ISA-model fact `sailCycleOrder` — a THEOREM since rev 39 (`sailCycleOrder_holds`), formerly the named
premise** — a closed proposition about the pf HART ROWS (Sail's cycle as the event instance labels it)
[R20.s4][R21.s1]: along every `pfRunST` run from `wpInit … (epsInit σ0)` (any `fok`, any `σ0`), at each own `.barrier
Barrier_RISCV_i` node the latest own `LInstr`/`LIFetch` step is `LInstr`, and at each own sfence-marker announce it is
`LIFetch` — stated on the label list, NOT through `tsoShadow`'s internal `fiArm` bit (W5 derives `MachOfPf.Hyps.fi :635`
from it by a one-fold lemma over `shStepF`, `TsoShadow.lean:310-318`), i.e. "the Sail cycle fetches, then announces,
then executes, and fetches nothing while executing" (`Step.lean:331-404`); **[R32.1] TRUE of the model FROM THIS PLATFORM'S RESET
(the boot PMA table `bootPMA` `Platform.lean:199-250` forbids instruction fetch from I/O regions, `pmaCheck` `Mem.lean:263-274`, and the HTIF window is disabled — `htif_tohost_base = none`,
`within_mmio_readable` `Mem.lean:437-446` [R33.1]); FALSE
over arbitrary register files — a fetch from a device address is an `LDev` step (`pnodeStep` `WeakEvInst.lean:315-321`), not an
`LIFetch`, so the SFENCE.VMA clause fails; R21's grep (no `execute_*` uses `InstructionFetch`) looked at `execute`, never at `fetch` to a
device — hence the premise is STATED under `wbootFacts σ0` (Q-SCO-PMA (α), RULED [OWN.45]); its rev-35 text (`:126-137`, every `σ0`) was
REFUTABLE; **[rev 39] restated (`SrvwmoXv6Adequacy.lean:139`) and PROVED — `sailCycleOrder_holds`, `Weak/SailCycleOrderCycle.lean:137` — M1/M2 non-vacuous**; RVWMO/riscv.cat/Zifencei silent on in-cycle order, the PMAs put
EXECUTABILITY in the platform's table; [R36.s2] a hypothesis of `machRunOfPfRun` (`Hyps.fi`) and of the CORES `srvwmoXv6M1Core`/`M2Core`,
discharged in `srvwmoXv6M1`/`M2` — GONE from §A (the shape `bootImageSealed` has it never regains); **[OWN.42][rev 35] option (a) IS TAKEN: W-SCO (A) proves
`SailCycleOrderK.cycleOkBoot` ([R32.1]: `cycleOkAll` is FALSE — fetch from MMIO; `cycleOkBoot` adds the register filter `Rboot`,
`pma_regions = bootPMA`) (every `execute` clause — 122 `def execute_*` in `InstsEnd.lean` —, `fence.i`/SFENCE.VMA by hand,
the instruction-independent cycle) and the reduction `sailCycleOrderOfCycle : cycleOkBoot → sailCycleOrder` (restated under
`wbootFacts σ0` [R32.1]; `cycleOkAll` DELETED, `cycleOkK` kept under `Rboot`, `SailCycleOrderK.lean:251-261`)
makes `sailCycleOrder` a THEOREM for kernel AND user text — it has left M1, M2 and §A's
statement and is NOT a trusted item; **DONE rev 39: `sailCycleOrder_holds` (`Weak/SailCycleOrderCycle.lean:137`), 122/122 `execute` clauses, 16 files `Weak/SailCycleOrder*.lean` ≈ 4.1k lines** (rev 24–34: W-SCO was to prove it for
kernel text only, user rows keeping it — SUPERSEDED: the kernel-text per-word route does not cover the words the cycle can
announce — two separately translated halfwords at `pc ≡ 2 (mod 4)`, `Fetch.lean:217-226,252-280`; `PROGRESS-WSCO.md`, §D
Q-SCO-words); the SC-failure model (`Xv6/UserMemLrsc.lean:7-12`;
D17); single era.  Fidelity: the cat transcription omits rules 6, 7-RCpc, 8 (sound direction for THOSE),
litmus-checked only; the published quantifier IS cat (tagged) — D25 (a) RULED [OWN.5], spike-CONFIRMED, W12 on the
critical path, no RVWMO⁻ fallback; Sail fork `070832a1` with `-D SYMBOLIC`; the image dump.  Keep, list.
**(11b) Faithful RVWMO I/O, evaluated [OWN.12] — verdict: INFEASIBLE as the realization's ordering source; (a′)
RULED, restated as the residue; optional audit D46.**  Read-only evaluation; every claim about the ISA text is a
reading of PROSE: the RVWMO chapter says I/O memory, instruction fetch and `sfence.vma` are "not (yet) formalized" and
gmo is over "the primitive load and store operations generated by memory instructions"; riscv.cat has NO I/O events —
a faithful I/O model is itself a NEW trusted-surface transcription.  **The ONLY ISA text saying which ppo rules apply
to I/O is the explanatory appendix's "I/O Ordering" subsection** (`riscv-isa-manual` `src/unpriv/mm-explanatory.adoc`,
fetched by R8, not in this tree) [R8.3a]: load-value/atomicity "in general do not apply"; ppo "still generally
applies" when one access is I/O and one of FIVE conditions holds — **(c1)** ppo as in the RVWMO chapter,
"with the exception that acquire and release ordering annotations apply only from one memory operation to another
memory operation and from one I/O operation to another I/O operation, but not from a memory operation to an I/O nor
vice versa"; **(c2)** overlapping addresses in an I/O region; **(c3)** the same strongly-ordered I/O region; **(c4)**
either in a channel-1 region; **(c5)** the same channel other than 0; then **the FENCE sentence** "To enforce ordering
between I/O operations and main memory operations, code must use a FENCE with PI, PO, SI, and/or SO, plus PR, PW, SR,
and/or SW" (also the normative pointer the privileged "Memory Ordering PMAs" section defers to — quote THAT section
verbatim once fetched [R8.s5]), and **the DEVICE sentence** "implementations must assume that the device may attempt
to access memory immediately after receiving the MMIO signal, and subsequent memory accesses from that device to
memory must observe the effects of all accesses ordered prior to that MMIO operation".
*What the ISA gives (`ioOrdF`, the faithful hart arms), against those conditions:* **(F1)** FENCE with i/o bits (the
FENCE sentence; Unpriv. FENCE: "the EEI will define which memory addresses … will be treated and ordered as device
input and device output operations") — `fence iorw,iorw` orders every prior RAM and device access before every later
one; **(F2)** (c2)–(c5): po-loc among I/O accesses and a hart's accesses to ONE strongly-ordered channel in program
order among themselves (faithful minimum: one channel per device — UART0/UART1, PLIC, virtio; the CLINT never reaches
the language, `MachCSL/Dev/Fabric.lean:10`, `timerinit` is Sstc CSR-only) — the platform declares NO channels (`bootPMA`,
`MachCSL/Platform.lean:199-239`: one `IOMemory`, non-idempotent window `[0x2000000, 0x12000000)`; Sail's `PMA`
structure has no ordering/channel attribute, `LeanRV64D/Defs.lean:549-566`), so CROSS-channel order is not given;
same-address rules are vacuous RAM↔MMIO; **(F3)** (c1) dependencies: addr/data/ctrl into a device STORE (ppo 9–11;
herd's `ctrl` reaches every po-later store after the dependent branch), addr into a device load; ctrl into a device
LOAD is NOT ppo — the only basis is the PMA non-idempotency text ("no speculative access to a non-idempotent region"),
a reading to be NAMED; **(F4)** aq/rl: (c1)'s exception verbatim — they do NOT order memory↔I/O (so `gacqPo` over I/O
is a NAMED strengthening, D52, not "a reading"); **(F5)** precise traps: earlier instructions COMPLETE before a trap
is taken, so a load/AMO po-before an interrupt handler has its value before the handler's MMIO, a STORE need not be
performed; **(F6)** the device rows' own order (virtio DRead/DWrite/DFence/COMMIT, `pdiskProg`) and the fabric
sequence `fab` are the device MODELS' — already trusted, not platform — with ONE ISA-prose anchor [R8.3b]: the DEVICE
sentence says that after the MMIO the device's memory accesses observe everything ordered before it — the ISA reading
of the pre-NOTIFY `fence iorw,iorw` → device-reads-the-descriptors path; the device MODEL (DMA reads at the TOP of the
store order, `MachCSL/Dev/DevLang.lean:20-21` [R9.2], `dmaView`, `Lang.lean:189,535`) is the STRONGER "reads at the top" form.
*What the realization needs (model-independent):* TsoMem and the pf machine run each row sequentially — an I/O step
sits at its po position, a store enters the log at its step, a load never reads from the future — so the realized
trace is a linear extension of `po ∪ rf ∪ gmo'|W ∪ gmo|IO` (Lin2's `ptraceRel` + (L)); hence (R1) (any `gmem` x) and
(R2) are REALIZATION-NECESSARY on every row [R7.1iii].  *(1) Paths and dependence.*  allocproc's own footprint touches
MMIO only through `panic`/`printf` (`uartputc_sync`: LSR loads, THR store) and, with interrupts on during the `proc[]`
scan (`wpNext`), through `devintr`'s PLIC claim/complete, `uartintr`, `virtio_disk_intr`; reaching it needs
`consoleinit`/`uartinit`, `plicinit(hart)`, `virtio_disk_init`, and `fork → allocproc` needs `exec("/init")`'s disk
I/O.  The published CONCLUSIONS depend on NO memory↔MMIO ordering: TsoMem's MMIO arms move no view (`Lang.lean:
356-358,372-375`), the Xv6 proofs read `fence iorw,iorw` as the MEMORY floor rule (`ProofVirtioDiskIntr.lean:92-99`),
DMA correctness is (F6), no conclusion names the UART wire order (`uartSentSub` is D9; `xv6NiPhi` counts accepted
bytes, `NiTrace.lean:198-203`); only the REALIZATION of `GT`'s fabric sequence depends on it.  *Decoder evidence:*
§A(†) (Sail drops PI/PO; FIOM = 0; `fenceDrains`/`fenceAcq` `TsoMem.lean:356-364`, `ebarNow` `WeakEvLang.lean:733-745`,
`ebarLabel` `WeakEvInst.lean:272-275` never see i/o bits); the bits survive ONLY in the instruction word (D48),
recoverable as `emFenceI` recovers `fence.i`: `emIoFence` — S–M, a fence FRAGMENT as graph data (D46 (b)).  *Per-path audit:*
`virtio_disk_rw`: desc `sh` → `fence` (`0x80005c7a`) → avail `sh` → `fence` (`:5c8a`) → NOTIFY `sw zero,80(a5)`
(`:5c92`, `0x10001050`) — `x →po dv` faithful (F1) ✓, and the DEVICE sentence gives the device's reads after NOTIFY;
after NOTIFY `lw a5,4(s3)` (`b->disk`), `sleep`'s stores, no fence — `dv →po w` ✗.  `virtio_disk_intr`: `acquire` →
STATUS `lw a5,96(a5)` → ACK `sw a5,100(a4)` (`:5d52`) → `fence` (`:5d54`) → loads — `dv →po w` after ACK ✓ (F1); the
acquire's store half and frame stores before STATUS ✗ ((F4)/(c1): aq does not reach I/O).  `uartputc_sync`: LSR loads
→ THR store: ctrl ✓ (F3; same channel (F2)); prior stores and the lock's store half → LSR ✗; THR → `release` (`fence
rw,w; sw`) ✗ (no PO bit).  PLIC: pre-trap loads → claim ✓ (F5), pre-trap stores ✗; claim → handler stores ✓ (F3
ctrl), claim → `plic_complete` ✓ (data); `plicinithart`/`plicinit` boot stores → device stores ✗.  **So `dv(store)
→po w` is ISA-given at exactly ONE xv6 site (the ACK) and `st →po dv` at exactly TWO (the pre-NOTIFY fences); every
other arm instance is the residue.**
*(2)/(3) Can the gap be closed without an assumption?*  No — the executions it admits are GENUINE RVWMO + I/O
behaviours of the verified code, so no kill can refute them: **(X1)** `printf` under `pr.lock`: hart B's last THR
store →po `release` →rf hart A's `acquire` →po A's THR store, with A's THR FABRIC-BEFORE B's — consistent with
`ioOrdF` (no PO-fence after THR), unrealizable by any sequential trace (THR_B < rel_B < acq_A < THR_A vs `fab`);
**(X2)** the same shape on the virtio channel, NOTIFY_A →po `release(vdisk_lock)` →rf `acquire`_B →(fence)→ NOTIFY_B
→fab NOTIFY_A — the four virtio fences do not close it; **(X3)** a pre-trap store buffered past the handler's claim
IS closed (lock-protected, released before the trap; the AMO read is trap-ordered (F5)) — PLIC claim cycles are
killable, `plicinithart`'s boot stores are not (no reader, no fence).  Dropping `fab` from what the realization
reproduces needs each device's answers invariant under the reorderings `ioOrdF` permits — the UART's LSR depends on
the tx FIFO (`MachCSL/Dev/Uart.lean:88,132,184`), the PLIC's claim CLEARS pending (`MachCSL/Dev/Plic.lean:85-93`
[R9.2]): a per-device commutation argument over `fab` (xv6- and device-specific, XL) that also changes what the theorem
says about devices; posted-MMIO arms in TsoMem re-open the driver proofs ((9a), XL×2).  Stating (L)/(K)/W2 with the
faithful edges alone is syntactically possible (`ioOrdF ⊆ ioResidue`) but (L)'s existence FAILS at (X1)/(X2) — a
faithful (L) needs the residue as a premise anyway.  **Hence (a′) stays [OWN.12], re-encoded as (R1)–(R3) [OWN.14];
D46 RULED (a) [OWN.17] keeps the fence fragment `emIoFence` (S–M), the trap-boundary edges (S) and `ioOrdF ⊆
ioResidue` (S) as PROSE (header-only value); D50 RULED (b) [OWN.17] puts the DEPENDENCY part IN SCOPE — W13 (F-dep),
M–L [R38.3]: the taggers `dstep` (`WeakRvwmoConf.lean:497-499` — STAYS inert [R38.2]) / `dstepT` (`AxDeps.lean:461-463` — gets the arms) are
inert on `LDev`, the graph's `gtdepsWf` must FIRST admit I/O endpoints ((F-dep) (0) [R38.1]), and the
MMIO arms of `pnodeStep` emit `LDev` with NO source fields (`WeakEvInst.lean:316-320,351-356` [R38.s3]; rev 10's "`oib = none`
discard" was a misnomer [R11.s1] — in `pnodeStep` `oib = none` means "`ib` UNCHANGED" (`.pure → some ibNone`, `regRead →
some (ibRd ib r)`, every other arm `none`, `:284-296`), the RAM store arm has it too; what the MMIO arms lack is the
read set `depsOfIb ib.ibBits` ON THE LABEL, as `LExLoad`/`LStore`/`LExStore` carry `asrc`/`vsrc`, `:329-331,344-355`),
§C W13 (F-dep).**
**(12) Audit coverage and file layout** [R1.10].  `Xv6/` never imports `Weak/` (`lakefile.toml:2,27-41`).  Composition
files live in `Weak/`, registered in `tools/ci/roots-weak.txt` + `tools/audit/baseline-weak.json` + `XV6_AUDIT_MODULES`
(`tools/ci/audit.sh:44`), built by `--weak` CI over the whole `Xv6` cone (D13); pure-`Xv6/` roots (W3; W8's export `Xv6/AccessDiscipline.lean` and its
(r2) sibling root `xv6DiscAdequacy_closed` [OWN.37] — W8-β′ and W8 (f2-ctx) are serial MachCSL items, NOT `Xv6/`-only
[R21.1][OWN.36][OWN.37], §C) go to `roots.txt`/`baseline.json`/`tools/tcb/expected.json` [R25.s2] (`tools/ci/lint.sh` checks agreement).  [R14.1] A MachCSL change whose cone build is green
can still break `Weak/` (`audit.sh:13-16`: "Weak/ is not in the Xv6/MachCSL build CI audits") and the `Vtest` lib
(`lakefile.toml:43-49`, NOT a default target; `tools/ci/vtest.sh check`) — W-COH's, W8-β′'s, W8 (f2-ctx)'s and W-RSV's briefs REQUIRE `lake
build Weak.TsoOfPf Vtest` (or the `--weak` lane + `vtest.sh check`) in their acceptance.  S.

## C. Roadmap

Each stage ends in a theorem; "∥" = parallel (one Opus worker, one file each).  Stages 0–1b are INTERNAL
milestones on the critical path of the target; Stage 2 is the target [OWN.2].

**Stage-1 RESULTS (2026-10-11) and the rev-19 launch set.**  DONE and MERGED: **W5b′** (`Weak/TsoShadow.lean`, 996;
adversarial verify's one blocking item — the step-list shadow lacked `itv` — FIXED: `ShFull` = `ShSt` + `itv` + `fiArm`),
**W-COH** (G2-Q (a′) BOTH components; `TsoOfPf.lean` restated, `Vtest` twins built; acceptance's three facts
`tsoAfterLoadCoh :179`/`g2TsoSched :251`/the `m0` counterexample `:270-272` present), **W1b + follow-up + (A)**
(`Xv6/AllocprocTrace.lean` 447; [OWN.28]), **W5d-G G0** (`Weak/GraphFetchSpike.lean` 339; review OK, carry-overs → G1;
[OWN.26]), **W2a** (`Weak/PfStepTsoMem.lean` 781, the MEMORY half) and **W2b** (`Weak/PfStepTsoView.lean` 807, the VIEW
half with the (↓) table's marks column); **W13 (E) PARTIAL** (the alphabet merged; `projLbl` flip/`lblRealizes*`/`lbAdmin`
drop RE-SEQUENCED into (I) — [OWN.27] (a)); censuses W4 [W4c] and W13 I/O [W13c] landed (read-only).  **Wave 2 DONE
(2026-10-11) [R16.4]**: **W13 (T)+(M)** (`Weak/GraphFabResidue.lean` 268 — `gisIo`/`gisR`/`gfBefore`/`ioResidue`
(R1)(R2)(R2′)(R3)/`ioResidueGmo`/`ioResidueNodev`/`ioResidueAcyclic`/`w13fIoResidueOk`/`w13fIoRevExcluded`/`gfIoDev`;
(M) `lbIsMem := lbIsR || lbIsW || lbIsIo`, `gwfNoIo`/`gwfMemRW`, the ~10 I/O case sites closed by the `False` `LIo` shape
arm, `fenceGob` on `lbIsR || lbIsW`; NOT done — `gdexecQconfT`/`xv6ConfS` do not exist yet, the clause is stated as
`gfIoDev` for W12/W13 (I)/(W); `emDevfree`'s retirement deferred to (I)/(R) per [OWN.27]), **W5-pre**
(`srvwmoXv6M1Premises :599` re-pointed to `execProgOk'ST`/`candScaT`/`candDiskLat`, `srvwmoXv6M1PfRun :624` a `pfRunST`
run + projection lemma, `srvwmoXv6M1Satisfiable :733`; W4 census D1/R5 "the premise set still says `candSca`" CLOSED),
**W11 (iv)a `linCandSca :314`/`tvnSca :50`** (`Weak/RvwmoXv6Sca.lean`, 327), **W2 CLOSE** (`Weak/PfStepTso.lean`,
items (1), (2), (4); item (3) `fiArm` → [OWN.35] `sailCycleOrder`, §D), **[R20.3] W11 (iv)b `linCandScaT :757`**
(`Weak/RvwmoXv6ScaT.lean`, 792; + `linCandScaTCatT :780`/`linCandScaTMinus :787`), **W-DMA0** (option (A) [OWN.34]; §C
W-DMA0 records the landed form), **W4 F1–F8** (`Weak/MachOfPf.lean`, 1659 — `machRunOfPfRun :1535`; §C W4 records what it
leaves OPEN).  **Rev 28 RESULTS (2026-10-12)**: **W-DISK DONE** (merged at the tip — `Weak/VirtioProg.lean` rewritten to the aligned
program, 672 lines; the ten-arm `pdiskProg :499`/`ediskStep :936`; the `ewpDisk*` rules incl. `ewpDiskWriteDevStore`/`Skip`/
`Abort`, `ewpDiskPop`/`PopRefused`; W2's rows `pfDWriteDevRowMem`/`pfDSkipRowMem`/`rowDiskDevMove`; `devQuiet`/`devQuietStep`/
`epsInitQuiet`; the interim `gfexecConf` clause `Fab.lean:633`; `pdevEvOk` re-proved against the state-aware `pdevEv`;
`xv6RvwmoSafeModuloF` builds; no `DWild`; `Dev/Virtio.lean` and the driver proofs untouched; deviations d1–d4 in the header
— §C W-DISK records them) and **W8-design DONE** (read-only; `notes/W8-design.md`, `notes/xv6-holding-race.md`; §C W8).
IN FLIGHT: none on this plan's lanes (rev 28).
**Rev 35 RESULTS (2026-10-12) and the rev-35 launch set [OWN.42]–[OWN.44] (rev-36 corrections tagged).**  DONE and MERGED: **W5 CLOSE-OUT
→ M1 DONE** (**[R32.1] LANDED rev 39 — non-vacuous**; was: `hsco` refutable: a fetch from MMIO of an SFENCE.VMA word under an arbitrary
`pma_regions`; the registered entry (axioms/opaques) is unaffected, the theorem's content is restored by W-SCO (A)'s first commit)
(`Weak.srvwmoXv6M1Core` registered — `tools/ci/roots-weak.txt:20`, `tools/audit/baseline-weak.json` (the [R28.1] entry), `audit.sh:47,54`;
`Weak/SrvwmoXv6Adequacy.lean` 331 lines, `srvwmoXv6M1Core :289`; INTERNAL, not published [OWN.2]; §C W5), **W-SCO shape (0) +
generic half** (`MachOfPf.lean`: `HypsC.fi :703-715` widened (`HypsC :686`, `Hyps :716`), `noWriteOfPristine :2982`, `fetchIsImage :3009`,
`cutOfPristine :3028` [R32.s1]; `Weak/SailCycleOrderK.lean` 631, not registered, IMPORTED `Weak.lean:635` [R32.2] — `sailCycleOrderOfCycle
:470 : cycleOkAll → sailCycleOrder` (sound; its premise FALSE [R32.1]);
§C W-SCO), **W13 (I) realization half** (`MStepIo` `WeakAxiomatic.lean:170`, `projLbl` flip `WeakPromiseBridge.lean:542`, `lbAdmin
:140`, shape arms `True`, release lemmas on RAM-only anchors; §C W13 (I)).  **W5d M2 CORE** — MERGED in the tip (`Weak.lean:636`,
byte-identical to w5's; NOT registered — M2 closes after W-RSV and [R32.1]) [R32.2] (`Weak/PfRunUnpinned.lean` 780 — `srvwmoXv6M2Core
:652`, [R32.1] LANDED rev 39 — non-vacuous; the threading as generic twins, M1's text unchanged; §C W5d).
IN FLIGHT (rev 36): **W8-β′** (serial MachCSL; increment 1 green, 2–4 in progress, `../xv6iris-weak-w2/PROGRESS-W8beta.md`; brief UNCHANGED)
— **DONE and MERGED 2026-10-12 [rev 37] (§C W8 Deps records the landed form)**.
BLOCKED → RULED: W-SCO's per-word half ([OWN.42] (A)), W13 (I)'s bundle half ([OWN.43] (a)).  **NEXT BATCH — APPROVED [OWN.44],
launched right after this review loop reaches SATISFIED, in PARALLEL (no shared file)**:
**W-SCO (A) — DONE and MERGED 2026-10-12 (w4) [rev 39].**  Landed: **commit 1** — `sailCycleOrder` restated under `wbootFacts σ0`
(`Weak/SrvwmoXv6Adequacy.lean:139`); `good`'s register filter `Rboot` (`SailCycleOrderK.lean:238`, `match` form [R33.s3]) pinning
`pma_regions = bootPMA` AND `htif_tohost_base = none` [R33.1]; `cycleOkBoot :251` REPLACES `cycleOkAll` (DELETED; `cycleOkK :261` kept,
`cycleOkKOfBoot`); `rbootInit` from `wbootFacts` via `bootFin_bootProg` [R33.s2] ⇒ **M1/M2 NO LONGER VACUOUS**; **(1) `cycleOkBoot_holds`**
(`Weak/SailCycleOrderCycle.lean:128`): the footprint kit (`SailCycleOrderGood` 530, `Fp` 1150, `FpReg`, `Stretch`, `ExecG`), the fetch
(`SailCycleOrderFetch` 207 — BOTH arms, the two separately translated halfwords, each an ifetch RAM read under `Rboot`), decode/CSR/memory
(`AllDecode`/`AllCsr`/`AllMem`), **122/122 `execute_*` clauses** (`AllExec`, `AllExec1–4`), `fence.i`'s ONE `Barrier_RISCV_i` and SFENCE.VMA
by hand, the instruction-independent cycle (`ucPrelude`/`ucDispatch`/`run_hart_waiting`/`ucFinish`/`ucEpilogue`/`tick_clock`) — 16 files
`Weak/SailCycleOrder*.lean`, ≈ 4.1k lines, imported `Weak.lean:635-639` (the rest transitively); **(2) `sailCycleOrder_holds :137` — a
THEOREM** (`sailCycleOrderOfCycle cycleOkBoot_holds`; axioms = the three standard + counted certificates): `sailCycleOrder` LEAVES the
trusted base (§A(6)), §B(11)'s premise list and the §A statement — it remains a proved lemma; **(3)** `srvwmoXv6M1 :148` / `srvwmoXv6M2 :179`
= the cores without `hsco`, by DIRECT application [R32.s4] (the (i′) detour `sailCycleOrderK`/`srvwmoXv6M1OfK` KEPT as a record); **(4)
`Weak.srvwmoXv6M1` REGISTERED** (`tools/ci/roots-weak.txt:22`, `baseline-weak.json:148` — entry EXACTLY the core's [R28.1]; `audit.sh:49,56`
list `Weak.SailCycleOrderCycle`; 555 `bv_decide` certificates COUNTED — the coordinator's `audit.json` figure); `srvwmoXv6M2` STATED, NOT
registered — **M2 CLOSE (below) — DONE rev 40**; the headers carry the 122-clause census, the two-halfword note and the [R32.1]/[R33.1] platform note.
Build/lint/`audit.sh --weak` green; every other registered root unchanged in statement.  *(rev 36 brief — the RECORD)*  RELAUNCH [OWN.42];
brief REWRITTEN at rev 36 [R32.1][R32.4] (L ≈ 1.7–3.3k; `Weak/` lane; the worker RESUMES from
`../weak-orch/parked/PROGRESS-WSCO.md` and the spike `PROGRESS-WSCO-spike.lean.txt` — NOT merged [OWN.10], re-created in the workspace;
**LAUNCHED 2026-10-12 in w4 — DONE [rev 39]**: `../weak-orch/allocproc_WSCO_A_prompt.txt` names this paragraph + [OWN.45] + the
addenda [R33.1] (second pinned register, below) and [R33.s2] (base lemma) [R33.s1]; the brief is NOT changed while the worker runs — the
rev-37 edits below are tagged and are what the addendum says).**  *Deps*: W-SCO (0) + generic half MERGED; M1 DONE (non-vacuous since
commit 1 below LANDED, rev 39); `SailCycleOrderK.lean`/`PfRunUnpinned.lean` imported (`Weak.lean:635-636`), neither registered [R32.2].
**COMMIT 1 — THE PREMISE RESTATEMENT [R32.1] (S–M ≈ 200–400 lines; `SrvwmoXv6Adequacy.lean`, `SailCycleOrderK.lean`, `PfRunUnpinned.lean`,
`MachOfPf.lean` header text).**  *Why*: `sailCycleOrder :126-137` is closed over EVERY `σ0` with no boot hypothesis — `epsInit σ0`
(`WeakEvCapstone.lean:1026`) seats each hart on `σ0.wgregs c`, an ARBITRARY register file — and `pnodeStep` labels a read at a device
address `LDev` whatever its kind (`WeakEvInst.lean:315-321`, `devAddr` tested BEFORE `akIfetch`); so under a `pma_regions` marking the PLIC
executable the cycle FETCHES an SFENCE.VMA word `0x12000073` from a PLIC enable register (M-mode, `pmpcfg = 0`, `pmaCheck` answers
`executable = true`, `Mem.lean:274`), announces it with `lastCyc = some .LInstr`, and the second clause (`:136-137`) is FALSE.  The same
tree path refutes `cycleOkAll`/`cycleOkK` (`good`'s `.memRead` arm `:145-150`, device conjunct `:149-150`, is "any answer, same phase";
`.regRead :157` is "any answer" [R33.s4]);
`sailCycleOrderOfCycle :470`/`sailCycleOrderKOfCycle :536` are sound with FALSE premises.  Rewrite `PROGRESS-WSCO.md`'s "What remains is
ONE closed proposition … `cycleOkK`" section FIRST [R32.s8].  *(i) Restate under the boot hypothesis — option (α), PROVISIONAL (§D
Q-SCO-PMA)*: `sailCycleOrder := ∀ fok σ0, wbootFacts σ0 → ∀ st c, pfRunST … → …` (the shape `sailCycleOrderK :92-93` has); `fiOfSco :176`
takes `hb : wbootFacts σ0`; `m1Hyps :216-227`, `m2Hyps` (`PfRunUnpinned.lean:632`), `fiOfScoK :554`, `m1HypsK :578` take `hb` (M1/M2 carry
it in their premise sets, `SrvwmoXv6Witness.lean:599`, `PfRunUnpinned.lean:596`); `srvwmoXv6M1Core :289`'s and `srvwmoXv6M2Core :652`'s
`hsco` becomes the restated premise — statement TEXT changes, NAME and `baseline-weak.json` entry do not (registration by NAME
[R21.4]/§B(12); the premise got WEAKER, the theorems STRONGER and non-vacuous).  (β) `∀ c, (σ0.wgregs c) pma_regions = bootPMA` alone still
needs the never-written invariant and saves nothing; (γ) refusing `akIfetch` in `pnodeStep`'s device arm is the recorded alternative, not
taken.  *(ii) Give `good` a register filter*: `good A R Q ph m`, `R : ∀ r : Register, RegisterType r → Prop`; `.regRead r, k ↦ ∀ v, R r v →
good … (k v)`; `.regWrite r v, k ↦ r ≠ pma_regions ∧ r ≠ htif_tohost_base ∧ ∀ u, good … (k u)` **[R33.1]** (the walk PROVES the model never writes
either: the only `writeReg pma_regions` are init — `MachCSL/ArchReset.lean:125`, `model/…/LeanRV64D.lean:265` `sail_model_init` [R33.s4] —
and `enable_htif` (`Platform.lean:217-218`) has NO caller in `model/` or `MachCSL/`; `Register` derives `DecidableEq`, `Defs.lean:1542`);
**`Rboot : ∀ r, RegisterType r → Prop | .pma_regions, v => v = bootPMA | .htif_tohost_base, v => v = none | _, _ => True` [R33.1][R33.s3]**
(the `match` form avoids the `cast` a `r = pma_regions → v = bootPMA` statement needs at `RegisterType pma_regions = List PMA_Region`,
`Defs.lean:1553` / `RegisterType htif_tohost_base = Option (BitVec 64)`, `:1561`, and lets `simp` close the `_` arms); **`cycleOkBoot := ∀ tick,
good (fun _ _ => True) Rboot (fun _ _ => True) .instr (riscvStep tick)` REPLACES `cycleOkAll` as deliverable (1)** (`cycleOkAll`/`cycleOkK` deleted, or kept with the header note "FALSE —
fetch from MMIO; superseded"); the run invariant `inv :264` gains "every hart's `rs pma_regions = bootPMA ∧ rs htif_tohost_base = none`" [R33.1] (base: `wbootFacts
σ0` (`WeakLang.lean:488`: `bootRun (bootProg (bootHid c) bootPMA) f₀ = some ((), σ0.wgregs c)`) → **`bootFin_bootProg` (`BootReset.lean:62-70`)
through the `resetRegsRun_of_run` pattern (`:107-115`: rewrite the `BootFin` witness with the equation) [R33.s2]** — `bootRun_bootLand :118`
only names the landing file and carries no `bootPost` — → `bootPost … htif_tohost_base = none ∧ … pma_regions = pma`,
`BootInitModel.lean:39,41`; step: `pnodeStep`'s `regWrite` arm `rs.set r v` (`WeakEvInst.lean:313`) with the two `≠` from `good`, and the
PLIC wire `pinSet` (`:473,:486`) touches `sig_meip`/`sig_seip` only — the ONLY two sites with `ors = some _`, `pstepEv :594-600`);
`nodeStep :273`'s `regRead` case (`:335-338`, called by `invStep :359` [R33.s4]) instantiates `v := rs r`; `invRun :430`,
`scoOfInv :450`, `sailCycleOrderOfCycle :470 : cycleOkBoot → sailCycleOrder` (restated), `sailCycleOrderKOfCycle :536` adapt; `goodBind
:174`/`goodMono :196` thread `R`.  *(iii) The PMA lemma the cycle needs* (S; `decide`/`bv_decide` over the literal table):
`matching_pma_region bootPMA pa w = some r → r.attributes.executable = true → 0x80000000 ≤ pa.toNat` (`bootPMA` `Platform.lean:199-250`:
`[0x1000, 0x2000)` and `[0x0200_0000, 0x1200_0000)` IOMemory `executable := false`, `[0x8000_0000, 0x8800_0000)` MainMemory `executable :=
true`) and `… = none → pmaCheck throws` (`Mem.lean:265-268`); `override_PMA` (`Pma.lean:313-319`) never changes `executable`, so the `pbmt`
override is immaterial; hence under `Rboot` every `InstructionFetch` `.memRead` node of `fetch_bytes` (`Fetch.lean:217-226`, BOTH halfwords)
has `devAddr = false` and `good`'s FIRST arm (`:145-150` [R33.s4]) applies — the device arm is never reached by an ifetch.  **[R33.1] TWO
places where the footprint walk must be PRECISE about a VALUE, not just about event kinds: (1) the PMA lookup (`matching_pma_region bootPMA
… = some r ∧ r.executable ⇒ 0x8000_0000 ≤ pa`, so the ifetch `.memRead` has `devAddr = false`); (2) `within_mmio_readable` on that `pa`
(`Mem.lean:437-446`, BETWEEN the PMA check and `read_ram`; `Platform.lean:718-728`): `within_clint :221-229`/`within_sig :232-240` false by
constant arithmetic (`plat_clint_base = 0x0200_0000`/`plat_clint_size = 0xC0000`, `plat_have_sig = false`, `PlatformConfig.lean:4476-4486`),
`within_htif_readable :252` = `within_htif_writable :243-249` false by `htif_tohost_base = none` — the `uma_within_mmio_readable_ram` shape
(`MachCSL/UMemPhys.lean:169-171`, used `UMemRam.lean:86,113`; `WeakFetch2.lean:323` carries the same `hhtif`) — so the fetch reaches
`read_ram rk paddr …` (`PhysMemInterface.lean:338`, the `.memRead` node) and NOT `htif_load` (`:598-620`, register reads only, no node).
Without (2) the path `some 0x8000_1000` answers the fetch from the `htif_tohost` register and announces any word at phase `.instr`:
`cycleOkBoot` refutable.  The spike's `nctPmaCheck` is a footprint lemma and gives neither.**  Everything else in the walk is footprint-only.  *(iv) Text*: `SrvwmoXv6Adequacy.lean`'s header (`:18`, `:80`) and `MachOfPf.lean`'s `fi` docstring (`:5-6`, `:679-680`)
say "TRUE of the model from this platform's reset (the boot PMA table forbids instruction fetch from I/O regions and the HTIF window is
disabled [R33.1]); FALSE over arbitrary register files; stated under `wbootFacts σ0`"; `PfStepTsoView.lean:67`'s `sailCycleOrderK_holds` → `sailCycleOrder_holds` [R32.s2].
**THEN (1) `SailCycleOrderK.cycleOkBoot_holds : cycleOkBoot`** via the spike's CPS kit (`gPure`/`gBind`/`gRBind`/`gIte`/`gDite`/`gCatch`/…,
the "no cycle event" footprint `ncG`/`ncT` — RAM reads non-ifetch, no announce, no `Barrier_RISCV_i`, no `pma_regions` write —, the
`nct_auto` dispatcher; spike sizing `maxHeartbeats` 1M for `nctPmpCheck`/`nctPmaCheck`, 2M for `nctJal`): (a) footprint lemmas for the
SHARED pieces — `pmpCheck` (in the spike), `pmaCheck` PRECISE per (iii), `translateAddr`/`pt_walk` and `untilFuelM.go` (RECURSIVE —
`nct_step` flags them; fuel induction, `ncTRUntilFuelM`), `mem_read`/`mem_write` for non-ifetch kinds, CSR read/write, the trap/exception
handlers, `lpad`/`checkPC`, interrupt dispatch, `tick_clock`, `run_hart_waiting`, the hooks; (b) ONE lemma per `execute_*` clause — **122
`def execute_*` in `model/Lean_RV64D/LeanRV64D/InstsEnd.lean` = the 122 arms of the dispatcher `def execute` (`:18769`); no F/D/V (present:
Zicond, Zba/Zbb/Zbs, Zimop/Zcmop, Zicbo*, shadow-stack `SS*`, `C_*`); 124 is WRONG [R32.s5]** — symbolic in operands; `FENCEI`
(`:18295-18297`, `sail_barrier Barrier_RISCV_i; RETIRE_SUCCESS`) proves "exactly one `Barrier_RISCV_i`, no fetch/announce" (the barrier
clause needs phase `.instr`, which the cycle's announce established) — **[R33.s5] NOT "no other clause emits one": `barrier_kind_of_num`
(`PhysMemInterface.lean:262-275`) falls back to `| _ => Barrier_RISCV_i`, so `execute_FENCE`'s lemma CASES on the kind (harmless for `good`:
its barrier arm needs only phase `.instr`) rather than assuming `≠ Barrier_RISCV_i`**; `SFENCE_VMA` (`:18009`, `flush_TLB`, no barrier) by hand — its
announce IS the `sfAnnB` marker and comes from the cycle at phase `.fetch`; the 46 `ExecuteAs` sites (the compressed `C_*` clauses) are
one-liners reducing to the base clause; **(c) the instruction-independent cycle [R32.4]**: `riscvStep tick = try_step 0 false >>= λ _, (if
tick then tick_clock () else pure ())` (`MachCSL/Lang.lean:241-243`); `try_step` (`Step.lean:416-440`) = `ext_pre_step_hook`,
`minstret_increment := should_inc_minstret …`, then `run_hart_waiting` (`Step.lean:230-242`; the WFI-parked body `ucBody` dispatches to,
`UCycleDefs.lean:61`) or `run_hart_active` = `ucDispatch` (`dispatchInterrupt`) → `fetch ()` (one or two `fetch_bytes`,
`Fetch.lean:217-226,252-280`; each ifetch read continues at phase `.fetch` by (iii), the second halfword's `translateAddr` reads are
ordinary PTW `LLoad`s) → `ucAfterFetch` (`UCycleDefs.lean:169-210`: `instr_announce` (phase `.instr`, or `.fetch` kept at the SFENCE
marker), pure decode, `is_landing_pad_expected`/`trap`, `nextPC`, `uxaExecAs` = `execute` + ONE `ExecuteAs` redirect
(`UExecAluGpr.lean:281-284`) — the ∀-clause lemma is applied TWICE per cycle) → `ucFinish`'s arms (interrupt trap `handle_interrupt`, fetch
fault `handle_exception`/`ext_handle_fetch_check_error`, execute trap `exception_handler`/`set_next_pc`, illegal, wait `assert`, retire) →
`ucEpilogue` (`tick_pc`, `minstret` bump; `UCycleDefs.lean:123-130`, `ucPrelude :55-59`) → `ext_post_step_hook`; then `tick_clock`
(`model/Lean_RV64D/LeanRV64D/Platform.lean:549-554` [R33.s4] — NOT `MachCSL/Platform.lean`, `bootPMA`'s file: `mcycle`/`mtime` bumps,
`clint_dispatch false` — register-only, a footprint lemma nonetheless); the equations
`uc_tryStep_eq`/`uc_runHartActive_eq` (`UCycleDefs.lean:11-17`) cut the cycle into these stretches.  Footprint lemmas for ALL of these.
(2) `theorem sailCycleOrder_holds : sailCycleOrder := sailCycleOrderOfCycle cycleOkBoot_holds`; (3) the corollaries **`srvwmoXv6M1`** =
`srvwmoXv6M1Core … sailCycleOrder_holds` (M1's statement WITHOUT `hsco`, by DIRECT application — the (i′)/(iv) detour `sailCycleOrderK`/
`srvwmoXv6M1OfK` is REDUNDANT; delete at the CLOSE if it shortens the build, else keep as a record) **and `srvwmoXv6M2 : <srvwmoXv6M2Core
without hsco>` (`PfRunUnpinned.lean:652`) [R32.s4]** — stated here; REGISTERED at M2 CLOSE (rev 40; after W-RSV's W4 re-proof, D26);
(4) CLOSE/registration: `Weak.srvwmoXv6M1` in `roots-weak.txt`/`baseline-weak.json` (entry = the core's [R28.1]; `decide`/`bv_decide`
certificates COUNTED, not listed; NO new opaque), its module in `audit.sh:47,54`; `roots-weak.txt:20` gains "(THEOREM after W-SCO (A))"
(the "demotes it for kernel text" gloss is `SrvwmoXv6Adequacy.lean:18`'s, fixed in (iv)) [R32.s2]; `PROGRESS-WSCO.md` updated.  *Files*:
`Weak/SailCycleOrderK.lean`, `Weak/SrvwmoXv6Adequacy.lean`, `Weak/PfRunUnpinned.lean` (commit 1) + NEW `Weak/SailCycleOrderAll*.lean` (the
per-clause lemmas, SPLIT per opcode family to bound elaboration), `tools/ci/roots-weak.txt`, `tools/audit/baseline-weak.json`,
`tools/ci/audit.sh`, three headers.  *Rebase surface*: NONE with W13 (I)'s bundle half (`WeakRvwmoFab`/`Supply`/`Lin2`/`FabInd`/`Capstone`/
`GraphFabResidue`, w3); W5d: MERGED, no surface [R32.2]; with W8-β′ (w2: `MachCSL/`, `Xv6/`, `WeakAdequacy.lean`): none; with W-RSV: rebuild
only (no reservation guard in these files).  *Acceptance*: `lake build MachCSL Xv6 Weak`, lint, `audit.sh --weak` green with
`Weak.srvwmoXv6M1` registered and `srvwmoXv6M1Core`'s entry UNCHANGED; `#print axioms sailCycleOrder_holds` = `propext`/`Classical.choice`/
`Quot.sound` (+ counted certificates), no `sorry`, no new opaque; `cycleOkBoot_holds` CLOSED — no hypothesis beyond the restated premise's
`wbootFacts σ0`, no restriction on the fetched word (option (a) of §B(11); TRUE of the Sail model from this platform's reset); the file
header carries the 122-clause census, the two-halfword fetch note and the [R32.1]/[R33.1] platform note (TWO pinned registers); `PROGRESS-WSCO.md` updated.  *Risks*:
elaboration budget (split files); the recursive walkers (fuel induction); the breadth of the trap/finish handlers; threading `R` through
the kit; a clause that RESISTS cannot be excluded by a candidate restriction (the cycle executes any word) — report it, the owner re-rules;
**[R33.1] a THIRD configuration register on the ifetch path would be found by the walk as a `.regRead` whose answer the proof needs — pin it
from `hwVal` (`HwConfig.lean:48-57`: `misa`, `mseccfg`, `pma_regions`, `htif_tohost_base`, `elp`, `senvcfg`, `mstateen0`, `sstateen0`) in
`Rboot` the same way; do NOT weaken `good`**.
**W13 (I) bundle half — DONE and MERGED 2026-10-12 (w3; `../weak-orch/parked/PROGRESS-W13I.md`) [rev 37]**: `gfexecConfIO` (replaces
`gfexecConf`, deleted; `WeakRvwmoFab.lean`) = `fab 0 = d0` ∧ Nodup ∧ bounds ∧ per row `∃ em dvi dvo tq, hartConff … ∧ (∀ k < |row|, (i,k) ∈
gfDev ↔ gisIo (i,k) ∨ dvi k ≠ dvo k ∨ tq k) ∧ pins ∧ emZifencei img em ∧ deps` — the contact bit `tq : Nat → Bool` is [R32.s3]'s third
per-item function (named `tq`, not `tch`; each admin run is `WeakRvwmoFab.admRunT`, returning "some step is `pdevEv`-true"); the interim
`.PDisk` clause GONE; `hemitfStatesQ`/`hartConffStatesQ` have NO start-state hypothesis (`tq k = false → dvo k = dvi k ∧ lbIsIo = false ∧
∀ d, hblkQ … d d …` — the folding GENERALIZED from `pdevEvOk`); `fconfRowsPin`/`fconfRows`/`fconfSupply` lose the quiet-boot hypothesis,
`supplyOfFconf` unchanged; `GraphFabResidue.gfIoDev` restated to the graph-visible half `gisIo (i,k) → (i,k) ∈ gfDev`, derived by
`gfIoDevOfConf :187`; `gisIo` moved to `WeakRvwmoFab`; `emZifencei` = the slot with content `emFetchImg` [R28.s5], the spike's def renamed
`GraphFetchSpike.emZifencei` [R32.3]; `xv6RvwmoSafeModuloF` builds on `gfexecConfIO`; `epsInitQuiet` deleted.  **Deviations**: `hemitf`/
`hartConff` gain `tq` (`hemitHemitf`/`hartConfHemitf` give `∃ tq`); `gfexecConfOfQconf` and `FabInd.cycleKillOfF :668` [R34.s1] take `∀ i, devQuiet
(boot i)` (a quiescent boot pool; discharged at xv6's boot); `WeakRvwmoFabInd` O1/O2 take `tq`, `gfexecConfRen`/`gfexecConfHull` transport
the contact clause.  Build/lint/`audit.sh --weak` green, no new axiom/opaque; registered Weak roots unchanged in statement.  W5d-G G1–G5's
gate (the `Fab`/`Supply` text) is MET.  The launch brief follows as the RECORD.**  *(rev 36 brief)* RELAUNCH [OWN.43] — LAUNCHED at rev 36 in
`../xv6iris-weak-w3` with [R32.3] as a LAUNCH ADDENDUM (`../weak-orch/allocproc_W13I_bundle_prompt.txt`; M on the fabric side; graph lane).  *Deps*: (I)'s realization half MERGED; W-DISK ✓ (`pdevEv :604`, `pdevEvOk :1792`, `devQuiet`
`WeakRvwmoSupply.lean:177`).  *Deliverables*: (1) `gfexecConfIO` = `gfexecConf` (`WeakRvwmoFab.lean:620`) with the `isDevBlock` clause
REPLACED by the CONTACT criterion `(i,k) ∈ GF.gfDev ↔ (gisIo (i,k) = true ∨ dvi k ≠ dvo k ∨ blockTouches em k)`, `blockTouches em k` :=
the BLOCK of item k (admin run + tagged step, `hemitf` `HFone`/`HFpair` `:253-275`) contains a `pstepEv p d l p' d'` step with `pdevEv p l
p' = true` — recorded per item by `hemitf` — **[R32.s3] the ONE viable carrier: a third per-item function `tch : Nat → Bool` beside `dvi dvo` in
`hemitf`/`hartConff` (`:253,:278`), fixed by `HFone`/`HFpair`'s premises (`har`'s admin run + `hre`/`hst`) and existentially quantified in
`gfexecConfIO` like `dvi dvo` (`emItems` holds labels only, `WeakRvwmoConf.lean:721`, and `pdevEv` is STATE-aware, `WeakEvInst.lean:608-610`,
so nothing can be read off the items)**; (2) the interim `.PDisk` `LDev`-free clause (`:633-634`; its docstring `:614-619` [R32.s6]) DELETED and the `devQuiet ∧ LDev-free` hypotheses of `hemitfStatesQ :396`/
`hartConffStatesQ :556` replaced by per-item quietness; (3) `supplyOfFconf :789`'s block folding `hblkQ :332` GENERALIZED, not deleted:
a NON-member block is quiet ⇒ fabric-preserving AND blind (`pdevEvOk`), so `∀ d, hblkQ Q d d …` holds for it and the supply fabric
`fab ∘ dcnt` replays it at the global fabric; `fconfRowsPin :885,917`'s `(i,n) ∉ gfDev → ∀ d, hblk d d …` conjunct is DERIVED from
quietness; (4) consumers rebuilt: `fconfSupply`, `WeakRvwmoLin2.fconfTraceRealize`, `WeakRvwmoFabInd.fconfRealize`,
`WeakRvwmoCapstone.xv6RvwmoSafeModuloF` (must BUILD; D39, internal), `WeakRvwmoFabInd.gfexecConfRen :290`/`gfexecConfHull :332` (they
transport the per-row clauses) [R32.s3], `GraphFabResidue.gfIoDev :176` [R32.s6] restated to the contact form; (5) the slot rename
`emFetchImg → emZifencei` [R28.s5] — **[R32.3] ALSO renames the G0 spike's 4-ary `Weak.emZifencei` (`GraphFetchSpike.lean:312`, imported
`Weak.lean:626`, kept per [OWN.10]) to `GraphFetchSpike.emZifencei` in the same commit (else a duplicate `Weak.emZifencei`), so W5d-G G1
later REPLACES the 2-ary slot's content with the spike's definition; alternatively keep `emFetchImg` and leave the rename to G1 —
worker's choice, said in the header (handed as the launch addendum)**; (6) the §A(†) trusted-surface sentence (rev 35's) in the bundle's header;
`PROGRESS-W13I.md` updated.  *Files*: `WeakRvwmoFab.lean`, `WeakRvwmoSupply.lean` (`pdevEvFalse :209`/`pstepEvDevfree :219`/
`admRunDevfree :239`; `emDevfree :360` stays inert — (R) retires it [OWN.27]), `WeakRvwmoLin2.lean`, `WeakRvwmoFabInd.lean`,
`WeakRvwmoCapstone.lean`, `GraphFabResidue.lean`; `WeakEvInst.lean` only if a per-step quietness lemma is missing.  *Rebase surface*:
NONE with W-SCO (A) (W5d: MERGED, no surface [R32.2]); W5d-G G1–G5 WAIT for this item's `Fab`/`Supply` text (D26).  *Acceptance*: `lake build MachCSL Xv6 Weak`
green, `audit.sh --weak` unchanged (no new axiom/opaque), `xv6RvwmoSafeModuloF` builds, `gfexecConfIO` NAMED with a header deviation note
("membership by fabric contact [OWN.43]; non-members are `pdevEv`-quiet, hence blind — `pdevEvOk`"), the `.PDisk` interim clause GONE,
`hblkQ`'s folding present in GENERALIZED form; marks in the header: FAITHFUL to RVWMO (no ISA order added), EQUAL to [R22.2] on every
xv6 run, STRONGER as generic trusted text only by unreachable non-moving fabric-touching blocks ((R3) orders them).
**W-RSV — DONE and MERGED 2026-10-12 (w2) [rev 37]** (D19 (b), form (i-a) [OWN.22][OWN.23]): `hartStep`'s `.pure` arm is `σ' = σ.dropResv
cpu` (`MachCSL/Lang.lean:543`; `dropResv :144` = `resv := updCpu σ.resv cpu none`); the boundary rules `wpLoop_restartB/_restart/_restartC/
_restartO` (`Wp.lean:2005-2108`; `memModel_dropResv :1240`, `hartViews_dropResv :1235`) and `wpLoop_restartT` (`WpSmodeCycleBase.lean:61`);
37 `wp_m_*` statements carry `[CurCtx]` + `ctxTok` (34 gained; the M-mode lane, re-censused at the tip [R34.s2]); `ctxTok_cases :406-407` yields `∃ r, resvFragAny cpu r`.
**Deviations**: S-mode rules UNCHANGED in statement (the fragment comes from `transTok`'s `ctxTok`); a `resvOut` side condition (`Wp.lean:2068`:
the lent resource holds no reservation fragment) on `sT_*`/`wait_wfi`/`ucStep` (`wpLoop_ucStep`, `resvOut_uFr`, `UCycleSwp.lean:362-404`);
the boundary does NOT clear `hr.acq` ([R12.s2]'s alternative — `pairAdjacent` pairs every `LExStore` with its own `LExLoad`; `clearAcq` stays
the store's, `Lang.lean:157`); `SPIN` gains `∃ r, resvFragAny cpu r` (`Xv6/SpecSpin.lean:17,40`).  20 MachCSL + 11 `Xv6/` (incl. `ProofSpin`,
`SpecSpin`, `UserretEntryPt`, `ProofStart`'s `ctxTok cpu curCtx` threading) + 2 `Weak/` (`MachOfPf.lean` guard sites — 7 `othersReserve`/
`anyReserve` lines remain, supplied by `pairAdjacent`; `WeakLang.lean:52`) + 1 `vtest-lean/Vtest/` (`XState.lean:262 dropResv`, `abs_dropResv :265` [R34.s4]) file;
`TsoMem.lean:33-34` says "within the issuing instruction" [R11.s2].  Build `MachCSL Xv6 Weak Vtest`, lint, audit, `--weak`, tcb green;
registered roots (incl. `Weak.srvwmoXv6M1Core`) unchanged in statement.  §0 F1 (ii), the "Honestly" line and §B(11)'s internal list now
say "reservation serialisation GONE"; D19's mark: FAITHFUL for AMOs / WEAKER for user LR/SC (as today).  The rev-36 launch paragraph
follows as the RECORD.**  *(rev 36)* W-RSV [OWN.41] — launches when W8-β′ MERGES (serial MachCSL; brief = §C W-RSV "Launch (rev 32)" — deps, the ≈ 8-file rebase
surface, the W4/W2 re-proof inside, acceptance — PLUS the rev-35 delta: M1 is REGISTERED, so the acceptance's "REGISTERED root(s)
green" is live for `Weak.srvwmoXv6M1Core` (and `Weak.srvwmoXv6M1` if W-SCO (A) has closed); the `Weak/` rebuild adds
`Weak/SailCycleOrderK.lean` (no reservation guard; rebuild only) and `Weak/PfRunUnpinned.lean` (MERGED [R32.2]; its rows rest on
`HypsC.cut`; the guard sites are the SAME — grep `othersReserve`/`anyReserve`/`resv` in `MachOfPf.lean`: 16 lines in the tip after the
twins, the listed 13 predate W5d/W-SCO [R32.s7])).
**W8 (f2-ctx) — LAUNCHED 2026-10-12 (w2) [rev 37]; S1 MERGED, worker STOPPED GREEN; RELAUNCH below [rev 38]; S1′ + S2-pre MERGED, worker
STOPPED GREEN 2026-10-13, RELAUNCH 2 below [rev 40] [R36.1] [OWN.37][OWN.38][OWN.39][OWN.41];
launch authority [OWN.37] + [OWN.41] (lane slot after W-RSV) — no further batch approval, unlike W5d-G [R34.s3]** (the serial MachCSL
lane's next and last planned item; L–XL ≈ 6.5–9.5k **+ 1–1.5k (findings 2–3, rev 38) + ≈ 2–3.5k (F-C, rev 40 [R36.4]) → ≈ 9–13.5k**, 3–4
full-cone rebuilds, green increments; brief =
§C W8 (4)/(6)/Acceptance + `notes/W8-Rctx.md` §1–§6 (BINDING over `notes/W8-design.md` §4/§5/§8, which state the superseded scalar design
[R28.s8]; **within `W8-Rctx.md` itself three things are SUPERSEDED [R34.2]: §0 item 5 / §4 / §6's user-table verdict "CHAINED as owned
stores, `WpPtWalkOwn` only if Q-R2" → PTE-KEY for BOTH tables, `WpPtWalkOwn` IN the file list [OWN.39] (option (b) there is UNFAITHFUL —
rejected); §7 Q-R1 → RULED (a) [OWN.38], the vector IS the design; §6's "serial before W-RSV" → after W-RSV [OWN.41]; its `plan :NNNN`
cites are rev-29 numbers and its MachCSL cites are at the pre-β′ w3 tip — relocate by name [R34.s1]**) + this paragraph; **[R34.1]–[R34.3]
APPLIED AT LAUNCH** as the ADDENDUM of `../weak-orch/allocproc_W8f2_prompt.txt`, recorded here).  *Deps — ALL MET*: W8-β′ MERGED
(`Xv6/AccessDiscipline.lean` 197: `Cust :53`, provisional `custAt :89` (ignores `σ`/`t`), `xv6LockWord :98`, `lockWordDiscAt :104`,
`cpuStaticAt :109`, `xv6AccessDisc :115`, `xv6LockWord_registered :153`, `powerInterp_accessDiscβ :186`; `SystemAdequacyDisc.lean:35`; root
`LinkDiscAdequacy.lean:26` REGISTERED `roots.txt:20`/`baseline.json:67`/`tcb/expected.json:2323`); W-RSV MERGED (above); R-ctx PASSED ((f1)
list EMPTY); M1 ✓.  *Deliverables*: (1) the PER-AUTHOR chain vector `chain ξ : CPU → Nat` + causal closure BESIDE the unchanged scalar floor
(`ctxFloor` `Ctx.lean:179`, `keyAt :187`), maintained at `ctx_absorb :480`/`ctx_stamp :520`/`ctx_unstamp :552` (join the releaser's vector at
the release → acquire hop)/`ctxStamped_raise :577`/`ctx_park :760`/`ctx_resume :788`/`ctx_move :848` (`CtxLaws.lean`), `kctx_floor_of_view`
(`KCtxMove.lean:303`); (2) `CtxBox.lean` (2,131 lines) stamps/registers lifted to join-vectors + row X2 (`boxRows :1117-1121`; `ctxDeposit
:156`, uses `:1489`, `:1824` [R34.s1]) — **[R36.4] X2 as written is SCALAR (finding F-C): the vector rows (C′)/(D′)/(E) of option (i) are
STATED as Lean invariants in `CtxBox.lean` BEFORE any wiring, (ii) is the sized fallback — RELAUNCH 2 (§C top) — **RULED (i) [OWN.50] 05:18 2026-10-13**; (3) X1 — hooks re-floored from the releaser's own vector (`lockHook_llb` `Lock.lean:597`,
`WpLock.lean:1255,1461` absorb at the stamp `T` — `:1141` is now β′'s `lkRsvIn` split [R34.s1]; rows 13–18, 24–25), X3 — a birth key for a
lock born after boot in `lkFresh :1115`/`isLock :861` (`lock_pay_take :541`, `lock_pay_born :660`; `LockBornHook`, `PipeBirth` (`:307`),
`ProofInitlog`'s `"log"` lock), X4 — the device-only absorb (`ProofVirtioDiskIntr`, `DiskInvDefs`), X5 — `ACQUIRE_LLB` (`SpecAcquire.lean:123`)/
`ACQUIRESLEEP_LLB` (`SpecAcquiresleep.lean:170`) withdrawn, the 31 consumer files of `W8-Rctx.md` §5 re-routed through X1/X2; (4) the load
rule establishing a MachCSL-generic, registry-parametrised chain invariant, `chainOkAt` derived `Xv6/`-side [R26.s4]; `WpPtWalkOwn`'s
user-table A/D write-back under the `pte` arm [OWN.39]; **(5) [R34.1] the export's six conjuncts are `chainOkAt ∧ lockWordDiscAt ∧
pteDiscAt ∧ cpuStaticAt ∧ cpuProcDiscAt ∧ utextDiscAt` (§C W8 skeleton); (f2-ctx) lands FOUR OF SIX** — `chainOkAt` (with the `.pte`
exemption for BOTH tables), `lockWordDiscAt` σ-readable (`custAt`/`xv6LockWord` — β′'s deviation 6 — incl. the PIPE part), `pteDiscAt`,
`cpuStaticAt` — exported by the SAME root `xv6DiscAdequacy_closed` (statement strengthened, registration by NAME unchanged;
`tcb/expected.json` module sets may grow as β′'s did — say so in the report); **`cpuProcDiscAt` and `utextDiscAt` are DEFERRED to the named
follow-up W8 (f3-rest)** (below; the file header `AccessDiscipline.lean:4-7` and `roots.txt:20`'s comment say "four of six" so the root
never over-claims; both NAMED in the root's docstring and the report).  The PIPE part — of `lockWordDiscAt` AND, per finding 2, of
`chainOkAt` itself (dynamic registration at `wp_s_sw_mint`/`wp_s_sd_mint`, `WpSmodeMint.lean:127/:40`) — follows **Q-F2-PIPEHOP (§D,
RULED (a′) [OWN.46] = (a) as amended by [R35.1]: the TIME-INDEXED hop registry `isLk b r` + `Xv6/`'s `pipeLockAt`) — MERGED as (a″), the
NAME-WORD window indexed at the acquire (`nameLockAt`), a DEVIATION from (a′) adopted provisionally as (a″+shape) pending Q-F2-PIPEHOP-2
[R36.3]**: REPORT the tie, do not custody silently.
*Files*: **13 MachCSL [R34.3] + `ChainDefs`, `ChainCert` [R35.1] + `RsvCell` [R35.2] = 16** (`Ctx`, `CtxLaws`, `CtxBox`, `Lock`, `WpLock`, `SwtchCtx`, `KCtxMove`, `LockBornHook`, `WpDma`, `WpDmaCtx`,
`WpSmodeLwKey`, `WpPtWalkOwn` + `Resources` for the vector's ghost plumbing — **route (A), LANDED in S1: `CtxId` grows `chain : CPU → GName`
+ `gate : GName` (`Resources.lean:432-441`), per-CPU `MonoNat` on `xv6GF` slot 8 (`Xv6GF.lean:226`), no functor change**; route (B) — a new
`MachFixedGS :202`/`MachGpreS :159` field, `Adequacy.lean:160 bootFixedGS`, `Xv6/Xv6GF.lean:70,390`, `Weak/WeakAdequacy.lean:99` (β′'s
precedent) and `tcb/expected.json` growth — was the fallback, not needed; S1 also touched `ChainDefs`/`ChainCert` (NEW), `Reserved`, `Wp`,
`WpAtomic`, `WpDma`, `WpSmodeFenceFloor`, `Power`, `PowerText`, `CtxBoot`, `RsvMint`, and `Weak/WeakAdequacy.lean:130` for the ERA name only)
+ ≈ 52 `Xv6/` (the 21 of `W8-Rctx.md` §2 + the 31 of §5 — **LLB-naming (`ACQUIRE_LLB`/`ACQUIRESLEEP_LLB`/`*_llb_*`) + hook-surface
(`wp_release_hook_body`/`slBody_hook`/`newlockAt_llb`) consumers: R34 counted 18 + 13, the tip greps 22 / 16 (union 35); X5 is complete when
both greps are EMPTY [R34.s5]** + `IputParts:461`/`ProofAcquiresleep:809`/`StartedInv:198,344`'s outside sites) **+ the gate's 18
lock-creation files (`kctx_newlock`/`newlock_*`, ≈ 37 lines) and `SpecMain`/`ProofMain`/`MainSecondaryParts` (gate threading) [rev 38]** +
`Xv6/AccessDiscipline.lean`/`SystemAdequacyDisc.lean`.  *Rebase surface (the tip at rev 37)*: W8-β′'s — `Lock.lean` (1,239: `lockRsvW`,
`lockBodyM`, `lkRsvIn`, `isLock :861`, `newlock_written :1002`, `lkFresh :1115`), `WpLock.lean` (3,531: reserved-mode AUs with the companion
word), `KCtx.lean` (`cpuCell`), `LockBornHook`, `WpLockInit.lean` (NEW), `Resources.lean` (`rsvModelAt` in `memModelAt`); W-RSV's —
`Ctx.lean` (`ctxTokAt :299`, `ctxTok :320`, `ctxTok_cases :406-407` yields `∃ r, resvFragAny cpu r`: the thread (f2-ctx) rebases on),
`Wp.lean` (`wpLoop_restart*` `:2005-2108`, `resvOut :2068`), `WpPtWalkOwn`, `WpStoreOrd`, `WpDma` guard sites, the 37 `wp_m_*`
`[CurCtx]`+`ctxTok` statements [R34.s2], `Xv6/SpecSpin.lean:40`; with W-SCO (A) (w4: `Weak/SailCycleOrder*.lean`, appends to
`MachOfPf`/`SrvwmoXv6Adequacy`/`PfRunUnpinned`): **NO shared file in either route (`WeakAdequacy.lean` is not W-SCO's) [R34.3]** — but every
MachCSL merge rebuilds `Weak/`, so (f2-ctx)'s 3–4 cone rebuilds land between W-SCO (A)'s green increments (rebuild only, no edit, for W-SCO;
(f2-ctx) EDITS `Weak/WeakAdequacy.lean` only — merge MachCSL-first, W-SCO rebases by rebuild).  *Acceptance*: `lake build MachCSL Xv6 Weak
Vtest` ([R14.1]; `Vtest` = `vtest-lean/Vtest/` [R34.s4]), `tools/ci/lint.sh`, `audit.sh`, `audit.sh --weak`, `tcb.sh` green;
`xv6DiscAdequacy_closed` registered with the FOUR-of-six `xv6AccessDisc` [R34.1], axiom set = `xv6FsAdequacy_closed`'s; every registered root
unchanged in statement; the file headers name F0's vector + causal closure, X1–X5, the (f1) list EMPTY; `W8-Rctx.md`'s 31 rows closed
CHAINED/DEVICE-KEY/PTE-KEY — a row that RESISTS during the proof is REPORTED (spec-first options: FAITHFUL/STRONGER/WEAKER), not custodied;
`PROGRESS-W8f2.md` with a **per-row CLOSED table (the 31 rows + the 4 outside sites + the walker row) kept from increment 1 [R34.s6]**.
*Size*: L–XL ≈ 6.5–9.5k + 1–1.5k, 3–4 rebuilds (order: F0 vector + `CtxBox` first, one rebuild; X1/X3/X4 second; X5 + the 31 consumers
last).  *Risks*: the vector's maintenance proofs (`ctx_unstamp`'s join, X1's "the releaser's own vector covers the hook stamp", X2's
invariance under parks/deposits/mints), `CtxBox`'s elaboration, the pipe-lock registry's σ-expressibility (Q-F2-PIPEHOP), the gate's
threading through `main` (Q-F2-BOOTGATE); the `Xv6` cone (≈ 0.66M lines) per rebuild.
**W8 (f2-ctx) RESULTS (rev 38) — S1 MERGED in the tip; the worker STOPPED GREEN at S2a with three findings** (`~/dev/weak-orch/parked/
PROGRESS-W8f2.md`; the unwired S2a WIP `~/dev/weak-orch/parked/w8f2-s2-wip/{Ctx,CtxLaws,CtxBoot,CtxKeyMint,Wp}.lean.txt` COMPILED against
the tip, not wired).  Landed: `MachCSL/ChainDefs.lean` (NEW, 369: `memExt`, `lockByteIn`, `syncHop :129`, `hopChain`, `ChainEnv`, the boot
hop `pubCover :244`, `gateOk :257`, `pubOneShot :339`, `ChainCert :271` with `valid` = own ∨ chain ∨ boot hop and `_mono/_le/_retime/_hop`),
`MachCSL/ChainCert.lean` (NEW, 202: `memModel_certIssue :122`, `memModel_gateIssue :129`, `memModel_chainRetime :141` — the release's
record, `memModel_chainHop :170` — the acquire's extension given the acquirer's gate; imported by `MachCSL.lean:261`), `Reserved.lean`
`RsvKind.pub w :123` [R35.s1] (a one-shot publication word written only by `w`, `oneShotOk`), `Resources.lean` (era ghost `chainName`, `chainEnvAt`/
`certsOk`/`chainModelAt` inside `rsvModelAt`; `CtxId` 4 fields `:432-441` [R35.s1], route A), `Ctx.lean` (`chainCertAt :80`, `gatePassedAt :92`,
`vecAt :271`, `chainTokAt :614` — defined and proved, NOT yet in `keyAt`/`ownCtxAt`), plumbing in `Wp`/`WpAtomic`/`WpDma`/
`WpSmodeFenceFloor`/`Power`/`PowerText`/`CtxBoot`/`RsvMint`, `Xv6/BootRsv`/`AppPreGS`/`AppUnionPre`/`KernelRsv` (`.pub` arm `:173`)/
`ForkretRecord` (4-field `CtxId`), `Weak/WeakAdequacy.lean:130 chainName := 0`; `tcb/expected.json` gains `MachCSL.ChainDefs` on 4 roots
(module growth only); every registered root unchanged in statement; audits PASS.  **Findings** (spec-first; all FAITHFUL unless marked):
(1) the load-side surface is wider than "the load rule from the key it consumes" — every RACY load goes through the key-less `readAU`
(`WpAtomic.lean:403`)/`readAUr` (`ReadAUr.lean:26`): 26 + 12 `Xv6/` mentions (+ 12 `readAU_locked`; `iget`/`idup` ref reads,
`virtio_disk_intr`'s used ring, `main`'s `started` spin) plus MachCSL's lock-word and page-walk reads; each needs a chain obligation or a
named exemption arm in S3 — size only; (2) **Q-F2-PIPEHOP** — `chainOkAt` ITSELF needs pipe locks as hop words (data under `pi->lock`
written by one hart and read by another is chained only through a `pi->lock` hop), not only `lockWordDiscAt`'s pipe part; (3)
**Q-F2-BOOTGATE** — the boot hop does not compose with lock hops σ-checkably (`MState` records no read positions), so a payload carrying
hart-0 boot-era coverage can be taken only by a hart that has itself passed the `started` gate — R-ctx row 27 holds but the mechanism is
NEW.  Both are in §D in the owner format, **adopted PROVISIONALLY (a) (coordinator, non-blocking rule), awaiting ruling**.  (4) size +
≈ 1–1.5k; no row RESISTS; the (f1) list stays EMPTY.
**W8 (f2-ctx) RESULTS (rev 40) — S1′ + S2-pre MERGED in the tip; the worker STOPPED GREEN 2026-10-13 at S2b with four findings [R36.1]**
(`~/dev/weak-orch/parked/PROGRESS-W8f2.md`; `diff -rq` of `MachCSL/`, `Xv6/`, `Weak/` w2 ↔ tip EMPTY).  **S1′** = the time-indexed registry
[R35.1]: `ChainDefs.lean` (413 lines) `ChainEnv.isLk : PAddr → Nat → Prop` (`:266`), `ext` keeps past registrations (`:274-276`), `hopChain`
checks `isLk b a` at the ACQUIRE position (`:177-183` — **deviation D2**), `syncHop :171`, `pubCover :288`, `gateOk :301`, `valid :350`,
`valid_hop :392`, `memGrow`/`memGrow_writeBytes :116-158`; the DYNAMIC registry is the lock's NAME word — `Reserved.lean` `latestAt :224`,
`nameLockAt :236` ("`b + 8` holds, as of `a ≤ top`, a registered name"), `nameLockAt_mono :240`, `KernelRsv.names :258`, `MachFixedGS.rsvNames
:406`, `Adequacy.lean:229 rsvNames := KernelRsv.names`, `Resources.lean:1062 chainEnvAt rs names σ` with `isLk b a := lockByteIn rs b ∨
nameLockAt names σ.mem σ.top b a`, `Xv6/KernelRsv.lean:111 names := [pipeLockNameStr]` (**deviation D1 = (a″)**, finding F-A — a DEPARTURE from
RULED (a′) [OWN.46], [R36.3] and §D Q-F2-PIPEHOP-2; **the constant is WRONG, [R36.2]**); the hop request inside the AMO's step
(`WpAtomic.lean:608-669`: `hopHead`, `hopRegAt :613` static/dynamic, `HopData :620`, `hopIn :623`/`hopOut :630`, `exclWriteAU`'s optional
request `:657-669`, `memModel_hopIssue` over `ChainCert.memModel_chainHopL :230`; `memModel_chainHop :173` takes `hlk : (chainEnv σ).isLk b a`,
`ha : σ.top = a`) and the release's retime request (`rtIn :453`/`rtOut :458`, `memModel_rtIssue :550`, `memModel_chainRetimeL :205`) —
**deviation D3** = the plan's "new continuation field", on `exclWriteAU`/`writeAU`/`readAUr`/`writeAUT`; existing users pass `none`.
**S2-pre** = `started` reserved `.pub 0` (`Xv6/KernelRsv.lean:52 xv6StartedR`, in `xv6PreLockRegions :57`; `rsvCpuIdx` 7 → 8), the
publication-read issue request (`ReadAUr.lean:36 RdIssue`, `rdIn :42`/`rdOut :50`, `memModel_rdIssue :121`, run by `WpSmodeFenceFloor.lean:259`
— the gate is issued INSIDE the load's step [R35.s5]), `writeAUT`'s RESERVED arm over `rsvStoreOk` (`WpStoreOrd.lean:45` — the [R35.2]
history-aware store landed THERE, not as a `RsvCell` variant), `StartedInv` restated over the half window (`startedWin :152`, `startedCell
:184` with `⌜rsvStatic = KernelRsv.static⌝` — **deviation D4**; `xv6Pub_only :120`; `startedSeen` carries `gatePassed cpu` `:269`),
`BootRsv.bootPreHalves`, `BootShared`/`BootSharedText`/`MainSecondaryParts`/`DiskAcc` adapted.  Builds + `lint`/`audit`/`audit --weak`/`tcb`
PASS per the worker (not re-run by R36); no root statement changed; `tcb/expected.json` unchanged.  **The S2b WIP** (the lock layer:
`Lock.lean.txt:546 lockRec`, `:560 lockPay`, `:625 lockRec_hopReq`, `lock_pay_born(_hook)`; `WpLock.lean.txt`'s AMO hop + release retime;
`LockPayIff`/`LockBornHook` re-proved; 9 files, 10,130 lines) is parked at **`~/dev/weak-orch/parked/w8f2-s2b-wip/`** — AUTHORITATIVE;
PROGRESS's `claude-notes/w8f2-s2b-wip/` path is STALE again (present in neither tree) [R36.s6].  **Findings** (spec-first; all FAITHFUL):
**F-A** (= D1) (a′)'s `pipeLockAt` cannot be discharged by the generic acquire — the lock layer holds the lock words, not `ftable`'s slots,
and there is no persistent history-entry receipt; **F-B** the boot hop must compose AFTER lock hops: `started_absorb` needs the reader's
certificates for the deposit record's whole vector; "a chain `h → 0` ending before hart 0's `started` store, then `j`'s read" IS σ-checkable —
generalise `pubCover` to `(h = w ∧ t < r) ∨ ∃ a < r, hopChain X.m X.isLk h t w a` (SOUND under RVWMO: `h`'s store → `fence rw,w` → release →
hops (`rf` + `.aq`/fence) → hart 0's acquire at `a` → `fence rw,rw` → the `started` store at `r > a` → `rf` → `j`'s load → `j`'s fence: PPO 4–7
+ `rf` compose in the total gmo; Sail/Zifencei/PMAs silent; monotone under `ext` by `hopChain_mono :191` + the coherence clause `:276`;
`valid_hop`/`_retime`/`_le` unchanged in shape; ≈ 0.1k) — **ADOPTED with ONE guard: the generalised `pubCover` requires `j ≠ w` (the
publication's WRITER, for which `ext :276` states the coherence clause), not today's `h ≠ j` (`:289`)**; **F-C** `CtxBox` X2 does not lift to
the per-author vector (blocks S2): `boxRows :1117-1121`'s rows (C)/(D) cover the box's scalar STAMP `T`; `boxRefDecr :1617` raises `td` by a
TSO visibility move with no vector analogue (`idup`/`iput` never check out); `ctxDeposit :156-162` stamps at `max T (max K W)`, so two deposits
can share a stamp and `(id, stamp)` cannot name an epoch — RULED (i) per [R36.4] (RELAUNCH 2); **F-D** (info) `ACQUIRE_LLB`-style laws stay
provable (scalar floors are TSO visibility); X5 is needed only where a KEY is built from a floor (`CtxBox`'s absorb, `IcacheInvRef`'s key →
`topLb`) — X5's consumer set narrows.  Per-row table: rows 1–31 + the 4 outside sites + the walker OPEN; row 27's absorb waits on F-B
(adopted), rows 13–18, 22 on F-C (ruled); none RESISTS.  Size: + ≈ 2–3.5k (F-C).
**RELAUNCH 2 — W8 (f2-ctx) continuation (rev 40; serial MachCSL lane; w2 or a fresh workspace on the tip) — LAUNCHABLE [R36.1].**  Brief =
the rev-38 RELAUNCH text below as amended by [R36.2]–[R36.4] + `PROGRESS-W8f2.md` (its "Design", S1′ and S2-pre sections BINDING; the worker
writes the PARKED path there from now on [R36.s6]) + the parked S2b WIP (`~/dev/weak-orch/parked/w8f2-s2b-wip/`, AUTHORITATIVE).  Order
(green increments): **S0 — two fixes, ONE `MachCSL` + `Xv6/` increment, no cone rebuild beyond `KernelRsv`'s**: (i) **[R36.2]
`pipeLockNameStr := KS.«pipe»`** (`KernelImage.lean:18837`, `= 0x800075c0`; the hand-computed `KA.«pipealloc» + 0x48 + 0x3000 + 222` at
`KernelRsv.lean:104` evaluates to `KernelStr.«digits» = 0x80007730` — the `addi` immediate is −146, `KernelImage.lean:13328-13329`; nothing in
the tree tied the constant to the image), `theorem pipeLockNameStr_eq : pipeLockNameStr = KS.«pipe» := rfl`, and a `decide`/`rfl` fact that
the image bytes at `KS.«pipe»` are `"pipe\0"` (documentation; the `pipealloc` proof computes the same value from `auipc`/`addi`); (ii) **[R36.3]
the hop SHAPE: `syncHop` requires its three entries to be WORD-sized** — `wordEntAt m b t := ∀ i < 4, ∃ e ∈ m[b+i], e.t = t` (same agent) for
`a`, `r` and the held entry (every lock-protocol write to a lock word is a 4-byte store at ONE timestamp — `amoswap.w.aq`, the release's
`amoswap.w zero`/`sw zero`, `initlock`'s `sw zero`; `σ.store` pushes four entries with the same `t`, `memGrow_writeBytes :156` — while
`memset`'s junk, `kfree`'s 1 AND `kalloc`'s 5, is one byte per timestamp) — `syncHop_mono`/`hopChain_*`/`memModel_chainHop(L)`'s `hb` gain
the hypothesis, discharged at the AMO from the lock invariant's `WordHist 4` (S ≈ 0.1k); the `ChainDefs.lean:17-23` docstring says "the region
discipline lets only the lock rules write the byte — or, for a dynamic lock, the word shape + the name window" [R36.s4].  **S2b** the lock
layer from the WIP, with **F-B**: `pubCover` gains the chain arm, guard `j ≠ w`; `started_absorb` closes row 27.  **S2 `CtxBox` — F-C RULED
by the coordinator (non-blocking, both FAITHFUL — proof-internal, the spec is silent): option (i), stated as rows BEFORE wiring [R36.4].**
The FIRST S2 deliverable is the new `boxRows` as Lean definitions in `CtxBox.lean` (no proofs yet): (Σ) and (I) unchanged; **(C′)** the parked
vector `V ≤ vp` when a park has happened since the current deposit, else `V ≤ vd` (the `lastL1` bit); **(D′)** at refcount 0, `V ≤ vd` —
maintained by `vd ⊔= vp` at the `refDecr` of the party holding the CURRENT park token (ONE token per park event; the next park takes it over —
the rows say so explicitly); **(E)** every live reference's epoch token names the current deposit index, the persistent snapshot `epoch e ↦
vd_e` is minted at the deposit, and the token is FRACTIONAL (it splits under the icache's M-5 shares, `mscale`/`reference_split`/
`reference_join` — the same camera shape as the `(id, stamp)`-keyed stamps map); the taker's obligations per transition: `boxWithdrawL1` (D′);
`boxCheckout` the epoch's `vd_e` by L1-lock lineage (the token proves the reference was minted after the deposit) + `vp` by the `lk->lk` hop
from the last park; `boxL1ToL2` its own vector; `boxRefIncr`/`boxRefDecr` token/snapshot bookkeeping.  If the rows do not close on paper
within the first increment, switch to **(ii)** — re-key the stamps map by deposit INDEX (the `(id, stamp)` key is already a per-reference epoch
witness except for stamp collisions, `ctxDeposit :162`), client churn bounded by the 27 files below — and REPORT the choice.  **S3**, **S4** as
in the rev-38 text, S4 with **windowed `lockRegionOk` for dynamic locks** [R36.3] (`lockWordDiscAt`'s dynamic arm states `lockRegionOk` on the
sub-history from the `initlock` zero — the first word-sized entry inside the name window — to the last word-sized entry before the name
overwrite; the whole-history form, `AccessDiscipline.lean:104` over `Reserved.lean:108`, would be FALSE at every `kfree` of a pipe) and the
acceptance item "`PipeBirth` establishes `nameLockAt … (pi.lock) a` from the `initlock` name store" [R36.2].  Rules unchanged (stop green on a
wrong clause; spec-first options; per-row table current).  Files: the rev-38 list + `CtxBox`'s rows; F-C's client surface = the **27 `Xv6/`
files** mentioning `reference γ`/`unitStamp`/`maxStamp`/`slotdHalf`/`slotpHalf` (60 mentions of the two stamp functions: `BcacheInv`,
`BioInit`, `BufEscrow`, `FileDefs`, `FilePay`, `FileOffProto`, `Fileread*`, `Filewrite*`, `IcacheBox`, `IcacheBoxSites`, `IcacheCover`,
`IcacheRef`, `IlockCheckout`, `IlockMain`, `IputEntry`, `IputEntryGhost`, `IputLockedC`, `IputStages`, `OffBox`, `ProofBrelse`, `ProofBwrite`,
`ProofIput`, `SysOpenParts`, …).  Size: remaining ≈ 5–8k of the rev-38 total **+ ≈ 2–3.5k (F-C: MachCSL ≈ +1–1.5k, `Xv6/` ≈ +1–2k over 27
files)**; (f2-ctx) total ≈ 9–13.5k; 3 cone rebuilds.  Parallel-lane rule: W-SCO (A) is DONE — the rev-38 "do NOT edit `Weak/SailCycleOrder*`
…" clause is VOID; keep "`Weak/WeakAdequacy.lean` is the only `Weak/` file (f2-ctx) may edit" (M2 CLOSE — DONE — and the Stage 2 set never
touch `MachCSL/`/`Xv6/`).  **W8 (f3-rest)** still after (f2-ctx).
**RELAUNCH — W8 (f2-ctx) continuation (rev 38; serial MachCSL lane; w2 or a fresh workspace on the tip) — LAUNCHED 2026-10-12 in w2,
RUNNING [rev 39]; **STOPPED GREEN 2026-10-13, S1′ + S2-pre MERGED (tip) — the BASE TEXT of RELAUNCH 2 above [rev 40] [R36.1]**: `../weak-orch/allocproc_W8f2_cont_prompt.txt` names this paragraph with [R35.1]/[R35.2] APPLIED AT LAUNCH and
[R35.s1]–[R35.s6]; the brief is NOT changed while the worker runs — the rev-39 edits below are tagged and are what the brief says;
[OWN.46]/[OWN.47] (23:25) RULE the two provisional options exactly as the brief implements them.**  Brief = the launch paragraph
above with [R34.1]–[R34.3] + §C W8 + `W8-Rctx.md` §1–§6 (carve-outs above) + `PROGRESS-W8f2.md` (its "Design" section is BINDING for
S2–S4) + the S2a WIP (`~/dev/weak-orch/parked/w8f2-s2-wip/` is AUTHORITATIVE — `PROGRESS-W8f2.md`'s `claude-notes/w8f2-s2-wip/` path is STALE,
present in neither the tip nor w2 [R35.s3]).  Resume: re-wire `Ctx.lean.txt`/`CtxLaws.lean.txt`/`CtxBoot.lean.txt`/`CtxKeyMint.lean.txt`/`Wp.lean.txt` onto the tip
(`keyAt = (ctxFloor ∗ chainKey) ∨ dirty`, `ownCtxAt … ∗ chainTokAt`; every `CtxLaws` law re-proved there); the wiring breaks AT LEAST `Lock`,
`CtxBox`, `WpPtWalkOwn` (one pattern), then `WpLock`, `LockBornHook`, `KCtxMove`, `SwtchCtx`, `WpLockInit` and the 11 `Xv6/` files stating
`ctxStamped`/`ownCtx_intro` (the tip's grep [R35.s2]: `BootCarveHart`, `BootShared`, `BootSharedText`, `ForkretRecord`, `IcacheCover`,
`IcacheInvRef`, `IcacheTable`, `ProofScheduler`, `SchedCtx`, `SpecRelease`, `StartedInv` — NOT `IcacheRef`, which has no such statement).  Remaining, in order (green increments; one cone rebuild each for S2, S3, S4): **S2b the lock
layer** — free arm = `ctxStamped ξL T V g` + the release record `chainLb h (V h) A r` (per `h`; `A`/`r` the head release of the lock byte) or
the BIRTH arm (X3: the handle carries `vecFloors curCtx Vb`); the release store re-dates the releaser's certificates (`memModel_chainRetime`),
the winning AMO converts the record for the acquirer (`memModel_chainHop`) — `exclWriteAURsv`/`exclWriteAUOwn` (`WpAtomic.lean:490/:481`)
hand the client the conversion inside the atomic step (a new continuation field); the DYNAMIC pipe-lock hop registry per Q-F2-PIPEHOP (a′) [R35.1][OWN.46] —
the TIME-INDEXED `isLk b r` of §D: `ChainDefs` (`ChainEnv.isLk : PAddr → Nat → Prop`, `ext`, `hopChain`, `valid_hop`, the `_mono` lemmas),
`ChainCert` (`memModel_chainHop`'s `hlk` at the release's position), `Resources` (`chainEnvAt`/`rsvLockByte`/`chainEnv` parametrised by a
client `dynLk : MState → PAddr → Nat → Prop` with a monotonicity obligation; `rsvName` UNTOUCHED) amended — the merged S1 layer, mechanical;
`Xv6/` supplies `pipeLockAt` (the `f->pipe` slot history + the reclaim entry); the mint store carries NO side condition; `syncPath` (S4) hops
through `isLk b r`; **`CtxBox`** (X2: join-vectors +
gate); **the `started` gate** per Q-F2-BOOTGATE (a) as amended by [R35.2] [OWN.47] — `started` joins `xv6RsvStatic` (`KernelRsv.lean:75`, the
`decide` checks re-run) as `.pub 0`; its boot-carve window (`BootCarveProc.lean:802 bcpBssWindows`, `BootShared.lean:223 bcpBssWindowsR`)
moves to the reserved half (`BootRsv.lean` `bootRsvHalves :15` gains the `.pub` group); `StartedInv` restated over the half cell at the image
history (`started_readAUr :255` at the fraction; `started_writeAUT :391` via a HISTORY-AWARE reserved store — a variant of
`ctxBytes_writeAURsv`/`execSpecF_sw_rsv` (`RsvCell.lean:91,127`) over `rsvStoreOk` (`WpAtomic.lean:432`), because the history-free
`rsvWordOk :33` cannot discharge `.pub`'s `oneShotOk`); the gate issued INSIDE that read's atomic step (`memModel_gateIssue :129` needs
`gateOk (chainEnv σ') j`, true by `HRead.afterLoad`'s foreign stamp, `TsoMem.lean:312-316,356-358` — no persistent `coh` receipt ghost
exists [R35.s5]); lock HANDLES carry `gateFloor curCtx` (the 18 creation
files; `SpecMain`/`ProofMain`/`MainSecondaryParts` thread a persistent `gateFloor` premise; hart 0 passes as the writer; `memModel_chainHop
:170` takes `gatePassedAt B` for EVERY hop conversion, so every acquiring hart needs its own gate — true in xv6, a secondary acquires nothing
before its spin); **S3 the load
obligations** — context loads consume keys; `readAU`/`readAUr`/`readAU_locked` racy loads get a chain obligation or a NAMED exemption arm
(device-key, `.pte`, the `started` spin as the gate's issue point), MachCSL's lock-word and page-walk reads included — every such obligation is established INSIDE the load's atomic step (`readAU`/`readAUr`
continuations see `memModelAt σ'`), never from a post-hoc receipt [R35.s5]; X1 (hooks re-floored
from the releaser's own vector, `WpLock.lean:1255,1461`), X4 (device-only absorb), X5 (`ACQUIRE_LLB`/`ACQUIRESLEEP_LLB` withdrawn; the 31
consumers — both greps EMPTY [R34.s5]); **S4 the export** — `Xv6/AccessDiscipline.lean`: σ-readable `custAt`/`xv6LockWord` (static + the
live-pipe arm — **windowed `lockRegionOk` for dynamic locks [R36.3]**)/`syncPath`/`chainOkAt`/`pteDiscAt`, `xv6AccessDisc := chainOkAt ∧ lockWordDiscAt ∧ pteDiscAt ∧ cpuStaticAt` (FOUR of six;
header `:4-7` and `roots.txt:20`'s comment rewritten to say so, `cpuProcDiscAt`/`utextDiscAt` named as W8 (f3-rest)'s [R34.1]),
`SystemAdequacyDisc`/`LinkDiscAdequacy` re-proved, root `xv6DiscAdequacy_closed` by NAME; **the root**: the `lint.sh` drift finding the S1 worker reported is
CLOSED by the `MachCSL.lean:261` import (`lint.sh:12-13` defines drift from the roots' build) [R35.s4].  Rules: a wrong plan clause → stop green, report spec-first options
(FAITHFUL/STRONGER/WEAKER w.r.t. RVWMO/Sail/Zifencei/PMAs); a RESISTING row is reported, not custodied; keep the per-row CLOSED table
[R34.s6] current (rows 1–11, 31 are carried by the S2a laws; row 27 needs the gate); the two §D questions are RULED [OWN.46][OWN.47] exactly as the brief
implements them (rulings 23:25, after launch — no change).  Acceptance as above; remaining ≈ 5.5–8.5k of the 6.5–9.5k + 1–1.5k **+ ≈ 0.2–0.3k
([R35.1] the time index) + ≈ 0.3–0.5k ([R35.2] the `started` reservation: `RsvCell`, `KernelRsv`, `BootRsv`, `BootCarveProc`, `BootShared`,
`StartedInv`)**; parallel
W-SCO (A) in w4 (do NOT edit `Weak/SailCycleOrder*`, `MachOfPf`, `SrvwmoXv6Adequacy`, `PfRunUnpinned`) — **VOID at rev 40: W-SCO (A) DONE
[R36.1]**; `Weak/WeakAdequacy.lean` is the
only `Weak/` file (f2-ctx) may edit; `PROGRESS-W8f2.md` on every stop.
**W8 (f3-rest) — NAMED follow-up [R34.1] (rev 38; after (f2-ctx); not launchable yet)**: the two deferred conjuncts — `cpuProcDiscAt`, fed at
the three `wp_s_sd_proc` sites (`WpSmodeProc.lean:108`; `myproc+0x1e`, `sched+0x2a`, `sched+0x54`, §C W8 (3)) by the holder fold of
`p_j->lock`, a lock-holder fact β′'s cpu-cell rule does not take (S–M ≈ 0.2–0.4k; `Xv6/`-only if the cpu-cell rule suffices, else ONE serial
MachCSL rule edit — the brief says which), and `utextDiscAt`, needing custody of USER pages (unsettled, §C W8 *Unverified points*) plus the
`userret` `fence.i` image fact (`KernelImage.lean:17614`; unsized); exported by the SAME root ("four of six" → "six of six" in the header
and `roots.txt:20`); gates W5d-G G7 (`utextDiscAt`) and W11 (ii)'s `kOwnerAt` uniqueness (`cpuProcDiscAt`); nothing consumes either before
W13 (XL).  All options FAITHFUL (the conjuncts are facts about xv6's code; the spec is silent on how a proof partitions them).
**[rev 46] (f3-rest) now carries** `cpuProcDiscAt`, `utextDiscAt` AND whichever the owner rules in of Q-PTEDISC's (P-a)/(P-b) (`pteDiscAt`: kernel-table leaves registered at the seal in `reservedOk`, ≈ 1–2k; user tables per publication epoch, ≈ 1–2k), Q-DYNLKDISC's (L-a) (pipe locks registered at `lock_pay_born`, windowed `lockRegionOk` birth → `kfree` reclaim, ≈ 0.8–1.5k: `Reserved`, `Resources`, `WpLock`, `PipeBirth`) and Q-F-DISKTAIL's (G) (boot-gate certificate arm, S–M) — S4 landed THREE of six, so the header goes "three of six" → up to "six of six"; AFTER W8 (pte-ghost); sized per ruling at launch.
**WAITS / LAUNCHABLE (rev 46) [OWN.56]–[OWN.58]**: **[OWN.56]** approved the third batch (Q-BATCH-3 = (1), 14:11; all three launched); **[OWN.57]**
Q-F2-PTE-WINDOW = (c) (→ W8 (pte-ghost), below); **[OWN.58]** the weekly cap is LIFTED for this account (run to 100%; the coordinator winds workers down green at
~97%; [OWN.51] superseded).  **MERGED since rev 45**: FabInd-S, W13 (W) part 1, the W13 (K-cat) STOP record (counterexample), W9a increment 1, W5d-G G1, W8 (f2-ctx)
S3 wiring.  **DONE, merge pending**: W8 (f2-ctx) S4 (w2).  **IN FLIGHT** (briefs unchanged): W5d-G G2–G5 (w1), W13 (W) rest = W13-wit + Bool twin (w3), W9a increment 2
= branch case (w5).  **LAUNCHABLE**: **W8 (pte-ghost)** after the S4 merge (serial lane; paragraph below); **(K-cat′)** under Q-KCAT's provisional (a) (graph lane,
S–M; the w3 lane after (W), or any free graph worker — `WeakRvwmoKillIOC.lean` only).  **Gated**: W8 (f3-rest) on (pte-ghost) (+ the Q-PTEDISC/Q-DYNLKDISC/Q-F-DISKTAIL
rulings for its optional parts); W11 on the S4 merge + (K-cat′) (+ Q-DYNLKDISC for pipe locks); W13 (R) on W5d-G; W14 on W13 (W) + W5d-G; W10 on its sizing pass.
**Rev 46 RESULTS (2026-10-13; every cite re-read at the tip unless marked w2).**  **FabInd-S DONE, MERGED** (w3): `gfexecConfHull` (`WeakRvwmoFabInd.lean:385`) takes only
`dclosed cs GF.gfDev` + `gfexecConfIO` — BOTH `gfexecConsistent` and `hullOk` dropped (the proof discarded both); in-file callers `:541`, `:576`; the ONE external call
`WeakRvwmoKillIO.lean:424`; header deviation 5 (`FabInd.lean:56`); `gfexecConsistentOfRes` kept, unused; the G3 gate [R41.3] is MET.  **W13 (W) part 1 DONE, MERGED**
(w3): NEW `Weak/GraphFabConf.lean` (369; `Weak.lean:648`): `GfexecT :63`, `forgetF :70`, `gfexecConfIOT :76` (dependency clause TAGGED, NO `emDevfree`; fetch clause
`emFetchImg` — the PINNED clause after the G1 merge fix, `:87`), **`xv6ConfS :92`** (deviation: `fab` existential), `xv6ConfSForget :150` (the `gdexecQconfTForget`
projection kept), **`usedElemGateOk :310`** (every disk-row fabric member `gisWIo` — the NAMED disk half [R41.4]), **`gfDevWIoOfXv6 :315`** (hart half PROVED via
`hemitfHartIo :239`), `fconfTraceRealizeIOXv6 :353` (premises left: RVWMO⁻, rule 14, `ioResidueGmo`, `gdiskRead14`, conformance, rows ≤ NCPU+1, `usedElemGateOk`);
W13-wit + the Bool twin NOT yet (RUNNING); stale header text `:11-12`/`:38-40` ("slot `emZifencei`") — fix in (W)'s next increment.  **W13 (K-cat) STOPPED GREEN — the plan
clause is FALSE** (w3; NEW `Weak/WeakRvwmoKillIOC.lean` 192, `Weak.lean:647`): the refined invariant `afterIo :63` is NOT closed under `CatLin.rsameC` even with NO fence
(`noPrSrFenceInSeg :71` holds, `kcatCexNoFence :143`) — riscv.cat's ppo rule 2 is `([R];po-loc-no-w;[R]) \ rsw` (same-source same-address loads unordered) and rf is per
BYTE; COMPUTED counter-model `kcatCex :87` (H0: MMIO `x`; `sb [1]←1` `w`; `lh [0]` `u`, byte 1 forwarded from `w`; `lb [0]` `v`, byte 0 = image = `u`'s source; H1: `sb
[0]←1` `w2`; MMIO `y`; gmo `[u; v; w2; y; x; w]`): `kcatCexCatT :90` (tagged model holds), `kcatCexResidue :106`, `kcatCexAfterIoV :150` (`v` fails), `kcatCexRacyDIOCycle
:166` (`racyDIO` cyclic; the segment `x→w→u→v` exits gmo-before `x`, no `CertC`).  `ioSegPinnedC`/`rsameCAfterIo` NOT delivered; [R41.s3]'s per-arm argument is sound for
the forwarded BYTE only — "the ONLY break is a `PR∧SR∧¬PW` fence" was WRONG → **Q-KCAT** (§D; provisional (a) → (K-cat′)).  **W9a increment 1 DONE, MERGED; STOPPED GREEN**
(w5; NEW `Weak/WeakRvwmoPinBridge3.lean` 276, `Weak.lean:649`): `segPinCOfSegPin :51`, `pinSegPinC' :56` (PDep), `pinSegPinCtrlC' :76`, `pinSegPinFenceC :95`,
`pctrlRowDepsSup :110`/`pinSegPinCtrlSupC' :149` (the REAL control label `LCtrl (erwSrcs dec rds)` — `pctrlRowDeps` never matches a real emission), `pdepRowDepsT :198`
(PDep TAGGED), `pdepSegPinCForward :243` (rule 12 across an rfi); every theorem keeps `psites`/`reaches` as a premise; **R-3 is FALSE of Sail as stated**: (1) a pending
enabled interrupt is dispatched BEFORE the fetch (`model/Lean_RV64D/LeanRV64D/Step.lean:331-335`, → `stvec` `:424`); (2) taken branches (the walk follows `wstep`'s
fall-through); (3) `ret` in descended callees (needs the frame's `ra` unchanged — W8 stack ownership); (4) per-instruction DEC-7 dataflow (a per-`execute` walk like
W-SCO's); (5) announced word = `kword pc` (fetch-from-image) → **Q-W9A** (§D; provisional (A)); increment 2 = the branch case (RUNNING).  **W5d-G G1 DONE, MERGED** (w1;
G2–G5 RUNNING): NEW `Weak/GraphFetch.lean` (290, `Weak.lean:650`): `emSlotShift :58`/`emSlotShiftHemit :116` (carry-over 2), **`emFenceI :175` + `emFenceISound
:195`** (D40), `emFenceIOfLast :215`, `emZif :247` (slot content), kernel-text instance `gzFetchOfPin :255`/`emZifOfPin :277`/`emZifOfPinC :286`; `GraphFetchSpike.gzFetch
:306`'s (Z2) STRENGTHENED to E1′ (`:311-312`; docstring `:292-301` names it (H3′) — §B(11), §D informed note); `WeakRvwmoFab.lean:844` `emZifencei G i em :=
GraphFetch.emZif G i em`; NEW **`gfexecConfZ :888`** (+ `gfexecConfZOfIO`/`OfText`/`OfNoWrite`).  **DEVIATION (accepted, rev 46)**: `gfexecConfIO :873` KEEPS the pinned
`emFetchImg` — replacing it now breaks the pinned supply (`fconfRowsPin`/`supplyOfFconf`; W13's chain in `FabInd`/`Lin2`/`KillIO`; D43 (a) keeps `pstepPin` until G6)
and `gfexecConfRen`/`Hull` cannot transport the Zifencei clause before G2–G4/R1 — so **G6 collapses `gfexecConfIO` into `gfexecConfZ` and moves `xv6ConfS`
(`GraphFabConf.gfexecConfIOT :87`) to the Zifencei slot**; until then `xv6ConfS` is the PINNED (kernel-text) conformance and [OWN.3]'s user-text coverage waits for G6
(recorded); `gdexecQconf` untouched (its twin is G5's `supplyOfQconf`); G3's mechanism = `Gdexec.gdFetch` a DEFAULTED field (23 structure-syntax sites unaffected,
≈ 22 anonymous literals to sweep); G1's `audit.sh --weak --build` NOT run (its files are OUT of the registered closure, [R41.2]) — G2 runs it; stale docstring
`WeakRvwmoFabInd.lean:36-37` (2-ary slot) → fixed in G2/G3.  **W8 (f2-ctx) S3 WIRED, MERGED** (w2): S3-c1 `chainModelAt` (`Resources.lean:1415`) carries `loadsChained`;
S3-c2 `memModel_load(_rv)` take `loadSrcOk :1273`; S3-c3 the `readAU`/`readAUr` sweep — companions `RdComps` (`WpAtomic.lean:465`) + `readCertsAt :516` (per entry
`srcCertAt :410` or `exCertAt :502`); receipt arm (a) dynamic lock words (`Lock.lkDynRegW`; 12 `WpLock` reads + 9 writes), arm (b) kernel PT (`KptInv` restructured:
leaves `pteCell … S`, pointer/empty entries FROZEN, `KptInv.leaf_ptByteAt` `MachCSL/KptInv.lean:328`); Xv6 builders (`StartedInv`, `IcachePinwObl`, `DiskAcc`, …).
The exemption is FACTORED ([OWN.57]): `chainExAt` (`ChainDefs.lean:699-702`) = `lockPubByteIn ∨ dynLkAt ∨ ptByteAt ∨ racyByteIn ∨ devPageIn` — NEW footprint-free
registry kinds `RsvKind.racy` (`Reserved.lean:144`; `racyByteIn :682`; `xv6IrefRacyR = ⟨itable+32, .racy 50 136 4⟩`, `KernelRsv.lean:79`) and `RsvKind.devPtr` (`:151`;
`devPageIn :688`; `xv6UsedPtrR = ⟨disk+16, .devPtr 1 8⟩`, `:85`).  Findings: **F-RACY** (`ilock`/`iunlock`'s lock-free guard `ip->ref < 1`, `kernel/fs.c:300,325` — a
REAL race; the plan's "chain lower bounds from `itable.lock`'s release record" is FALSE there) → **Q-F-RACY**; **F-DISKTAIL** (`used->idx`, `virtio_disk.c:318`, may
return hart 0's zero fill `:128` with only a visibility key) → **Q-F-DISKTAIL**; **F-X** → decided below.  **W8 (f2-ctx) S4 DONE GREEN in w2 (merge PENDING; cites to
`../xv6iris-weak-w2`)**: `Xv6/AccessDiscipline.lean` — `Cust :100` gains `pub`/`racy`/`dev`; `custAt :152` (CLASSICAL `if`, exempt classes first in `chainExAt`'s
order); `syncPath :174` = `hopChain` ∨ `pubCover` (the boot hop as implemented [R36.1], not "`t ≤ bootEnd`"); `chainOkAt :183` (five exemption hypotheses, proved by
`chainOkAt_of` from `loadsChained` + `mmOk`); `lockWordDiscAt :208` (STATIC locks only = β′); `cpuStaticAt :212` (custody-free, every cell byte); **`xv6AccessDisc :=
chainOkAt ∧ lockWordDiscAt ∧ cpuStaticAt` (`:219`) — THREE of six, not four**; `powerInterp_accessDisc :333`; root `Xv6.xv6DiscAdequacy_closed` TEXT unchanged, export
strengthened; `tools/tcb/expected.json` that root only (`MachCSL.ChainDefs`, `MachCSL.Resources`, `Classical.choice` enter its statement's base; precedent
`unionAdequacyClosed`); `baseline.json` unchanged; `lake build MachCSL Xv6 Weak Vtest` (3864 jobs), lint, audit, `--weak`, tcb PASS; X1/X5 greps left (31 hits in 18
`Xv6/` files, 0 in `MachCSL/`).  NOT derivable from `powerInterp` (`mmOk`/`reservedOk`/`chainModelAt` say nothing of them): **`pteDiscAt`** (lives only in `KptInv`/
`pptPost`) → **Q-PTEDISC**; **the pipe-lock part of `lockWordDiscAt`** (the windowed `lockRegionOk` [R36.3]; a pipe lock's discipline is its Iris invariant
`Lock.lkDynRegW`, the registry is static-only `rsvExact`) → **Q-DYNLKDISC**; both → W8 (f3-rest) if ruled in.  The S4 docstrings name the `.pte` window as CLOSED by W8
(pte-ghost) [OWN.57] and F-RACY/F-DISKTAIL as weakenings pending the owner.
**F-X DECIDED (rev 46): the X1/X5 "both greps EMPTY" is NO LONGER an acceptance item** of (f2-ctx) or any later item.  Verified reason: the load-side invariant is PROVED
without them — every key is `keyAt` (clean ⇒ chain key), every racy read pays `readCertsAt`, `chainOkAt` is derived from `loadsChained` + `mmOk` (`chainOkAt_of`, w2);
the `ACQUIRE_LLB`/`ACQUIRESLEEP_LLB` surfaces (`Xv6/ProofAcquire.lean:242`, `Xv6/LinkAcquire.lean:18`; 0 hits in `MachCSL/`) mint only TSO floors/visibility — TRUE of
TsoMem, consumed by NO certificate, and absent from the export (the only thing W11 transports to RVWMO), so they cannot leak a TSO-only fact into the published theorem;
X5's [R34.s5] purpose (hooks re-floored from the releaser's vector) was a route to chains that S3's certificates now supply.  Replacement check (automatic): the (r2)
root's statement names no LLB surface (tcb) and `grep -E 'ACQUIRE_LLB|ACQUIRESLEEP_LLB' MachCSL/` stays EMPTY.  Removing the 31 `Xv6/` hits = optional hygiene, any lane,
never a gate.  The RELAUNCH 5 paragraph's "both greps EMPTY" and its addendum's "the TARGET" (below) are SUPERSEDED by this.
**W8 (pte-ghost) — [OWN.57] option (c): close the `.pte` window (rev 46; serial MachCSL lane; AFTER the S4 merge, BEFORE W8 (f3-rest); L ≈ 1.0–1.6k; one cone
rebuild + the (r2) root's tcb check).**  *Goal*: the export's `.pte` class contains NO page another owner can hold — no freed page-table page of a dying table is exempt
(the [R41.1] window: `freewalk` `kfree`s each interior page before `pagetable[i] = 0`, `vm.c:273-274`; `freeproc` frees the root before `p->pagetable = 0`,
`proc.c:162-163`).  *The ghost freed-page set, and why it is read off memory*: the export is a PURE predicate of `σ` (W8-design (1)), so a ghost set can strengthen it
only through a σ-readable image — and xv6 writes one: every page enters the free list at `kfree`'s push `kmem.freelist = r` (`kalloc.c:61`, BEFORE `release(&kmem.lock)`
`:62`), recorded in the head word's byte history (`HEnt` = position, author, value; `TsoMem.lean:76-80`).  *Definitions* (`MachCSL/ChainDefs.lean`, beside `ptByteAt
:670`): NEW footprint-free registry kind `RsvKind.freeHead cnt stride` (`Reserved.lean`, like `.roots`/`.devPtr`; xv6 `xv6FreeHeadR := ⟨kmemFreelistAddr, .freeHead 1 8⟩`,
`KallocDefs.lean:67`, in `xv6RsvStatic`); `ptFreedSince rs m t0 t p` := a registered head word held `p` as of some position in `(t0, t]` (`wordAsOf :646`);
`ptRootLiveAt`/`ptPageLiveAt` = `ptRootAt :664`/`ptPageAt :660` where EVERY hop — root word → root, each slot → child — names a page NOT `ptFreedSince` the position at
which that naming word took its current value; **`ptByteLiveAt`** := `ptByteAt` over the live walk, + `ptByteLiveAt_grow` (as `ptByteAt_grow`: entries above the top
change nothing as of `t ≤ top`); `chainExAt`'s third disjunct (`:702`) and `custAt`'s `.pte` arm use it.  Every hop is restricted, so a freed root/level-1/level-0 page is
not walked through and pointer-shaped words a NEW owner writes into it lead nowhere (the [R41.1] pointer-word caveat disappears with the window).  Residual (docstring):
a dying page-table page stays exempt from `kfree`'s entry to its push (`kalloc.c:55-61`), while the freeing hart holds it EXCLUSIVELY (no hart can obtain it before
`release`) — no foreign read exists there.  *The second bridge (B2) `kmemHeadOk`* (the first is S4's `custAt_notEx`: σ-custody ↔ `loadsChained`'s exemption): every
entry of the head word's history after boot names `0` or a page held FREE-SIDE at that position — in `kmemRes`'s `chainAt` (`KallocDefs.lean:143-146`; a pop writes
`r->next`) or in `kfree`'s precondition (a push writes `r`); kept in `kmemRes` (`:330`) as a pure history fact plus a ghost freed-page LOG (page, position) — extending the
NI ledger's `Kev` (`KallocEv.lean:45-52`; today `KFree` names the ACTOR, not the page) or a sibling mono-list at `γk.pend` (worker's choice).  With `KptInv`'s FROZEN
pointer/empty cells (persistent — exclusive with the own-1 first word a free-side holder has) it yields **`kptNeverFreed`**: no kernel-table page on a leaf path is
named by a head entry after its link — the ONLY consumer of the strengthening, `KptInv.leaf_ptByteAt :328` → `leaf_ptByteLiveAt` (its receipt lends the head word's
history beside the root word and the two frozen pointers).  User tables need no receipt (their reads are owned context loads, [OWN.39]); every load that LOSES the
exemption (bytes of a freed-window page: `kalloc`'s `r->next` under `kmem.lock`, the new owner's own loads, foreign readers of its data) already pays through its
lock/key/certificate arm — the build CONFIRMS that no proof used the `.pte` arm for them (report any that did).  *Files*: `MachCSL/Reserved.lean`, `MachCSL/ChainDefs.lean`,
`MachCSL/KptInv.lean`, `MachCSL/WpAtomic.lean` (only if `exCertAt`'s receipt shape changes), `Xv6/KernelRsv.lean`, `Xv6/KallocDefs.lean`/`KallocEv.lean`/
`KmemGhost.lean`, `Xv6/ProofKfree.lean`/`ProofKalloc.lean`/`ProofKinit.lean` (+ `freerange`'s boot pushes), `Xv6/AccessDiscipline.lean` (`.pte` arm + docstring),
`tools/tcb/expected.json` if the root's base moves; NO `Weak/` file.  *Spec*: RVWMO/riscv.cat/Sail/Zifencei/PMAs SILENT (custody is not an ISA notion; no hart walks the
dying table — §D Q-F2-PTE-WINDOW); FAITHFUL; the export becomes EQUAL to the intended "bytes of pages in use as page-table pages".  *Acceptance*: `ptByteLiveAt` +
`_grow`; `xv6FreeHeadR` registered; `kmemHeadOk` maintained by `kinit`/`kfree`/`kalloc`; `kptNeverFreed`; `KptInv.leaf_ptByteLiveAt`; `chainExAt`/`custAt` over
`ptByteLiveAt`; the WINDOW-CLOSED lemma `ptByteLiveAt_freed` (a page pushed after its naming word's write is not exempt through that word; freeproc/freewalk as its
instance); the export's `.pte` docstring and §A say "no window" (the [R41.1-alt] addendum sentence RETIRED); `lake build MachCSL Xv6 Weak Vtest`, `lint.sh`, `audit.sh`,
`audit.sh --weak`, `tcb.sh` (report `expected.json`); the root's text unchanged, its export STRONGER.  Rules as RELAUNCH 5 (stop green on a wrong clause; spec-first
options; `PROGRESS-W8pte.md` on every stop).  Parallel: the graph lane only.
**STAGE 2 ROADMAP — REMAINING (rev 46; today's findings placed).**  *Running*: S4 (DONE, merge pending), W5d-G G2–G5 (w1), W13 (W) rest (w3), W9a increment 2 (w5).
*Serial MachCSL*: S4 merge → **W8 (pte-ghost)** → **W8 (f3-rest)** (`cpuProcDiscAt`, `utextDiscAt` + the ruled-in parts of Q-PTEDISC/Q-DYNLKDISC/Q-F-DISKTAIL).
*Graph*: **(K-cat′)** (NEW, S–M, `WeakRvwmoKillIOC.lean`, under Q-KCAT (a)): `ioSegPinnedC` under the NAMED per-step condition `ioStepCloses` — the closing arms: write
targets by (R2), I/O targets by (R3), `grfi`, the cat-ordered arms (`gppoCat6`/deps/rule 12) out of a gmo-after-`x` event, `pw` fences out of forwarded reads, `gpoloc`
ON the forwarded byte — its `w13f` instance, and `kcatCex` kept as the permanent counter-model; **W5d-G G6** (with W11 (iii)) ALSO collapses `gfexecConfIO` into
`gfexecConfZ` and moves `xv6ConfS` to the Zifencei slot; **W13 (R)** after W5d-G; **W10** sizing pass first.  **W11 — NEW obligations (rev 46)**: (1) [Q-KCAT (a)]
I/O-entered segments whose exit is reached by a NON-closing `rsameC` step (same-source R→R `gpoloc`, off-byte forwarding — `kcatCex`'s shape) are certified by the
CS-chained route: the outgoing cross edge (`fr v w2`) is a race on `v`'s byte, which `chainOkAt` excludes — a new shape in the certificate census (S–M); W11's gate is
(K-cat′), not (K-cat); (2) **the lock-word check** — (K)'s check (ii): `lockWordDiscAt` is the precondition of the C1/C2 certificates of racy lock-layer reads
(`holding`'s `lk->cpu`, `lkCpu_read_not_mine`); S4 exports it for STATIC locks only, so the pipe-lock C1/C2 (`acquire(&pi->lock)`'s `holding` read by a non-holder)
need **Q-DYNLKDISC (L-a)** — under (L-b) a NAMED premise of W11; (3) [Q-F-RACY (a)] an AUDITED-RACY `badSeg` arm for `ip->ref` (`racyByteIn`): the value only feeds
`ip->ref < 1` → `panic`, which never fires (the reader's own reference keeps every coherence-readable entry ≥ 1) — S, on the `lkCpu_read_not_mine` pattern; (4)
[Q-F-DISKTAIL (a)] the used-ring page (`devPageIn`): its only hart-authored entries are hart 0's boot fill, chained to harts ≥ 1 by `started` (`pubCover`) — S, VOID
under (G); (5) PTE bytes: still NO arm [R25.1 (b)] — Q-PTEDISC costs W11 nothing.  **W14 — NEW obligation (rev 46): DISCHARGE `usedElemGateOk`**
(`GraphFabConf.lean:310`): (i) shape-to-gate — on `pdiskProg`'s node order a non-`gisWIo` disk-row member arises ONLY from the used-ELEMENT `DWriteDev`'s own-guard SKIP
(`WeakEvInst.lean:519-525`), a reachability invariant of `virtioProg` (S–M; prose-only in `GraphFabConf`'s header today); (ii) run-level — on an xv6 run the gate `phase ∧
completeOk ∧ pushOk` (`VirtioProg.lean:88-90`) holds with a RAM target, from the disk invariant (`virtio_disk_rw`'s descriptor/avail discipline); (iii) the computed Bool
twin on W14's device-active witness (W13-wit's disk half is vacuous [R41.s6]); else `usedElemGateOk` stays a NAMED device-model premise (EQUAL to MachCSL's disk step on
xv6 runs).  The rev-44/45 record follows.
**WAITS / LAUNCHABLE (rev 44–45) [R40.1][OWN.55][R41.n]**: **DONE and MERGED since rev 43 (2026-10-13)** — **W13 (R3′)** (w4, 11:39; [R40.1] (α) applied at
launch), **W11 (iv)c** (w5, 11:41), **D35-fix** (w1, 11:47; [R40.s1]: launched at once, 13 roots re-audited, baseline unchanged), **W8 (f2-ctx) (a′-r) + S3-a**
(w2, 11:17) and **S3-b + S3-c0** (w2, 12:13; worker STOPPED GREEN), **W13 (K)** (w4, 12:30), **W13 (F-dep)** (w3, 12:50) — the whole Stage 2 FIRST and SECOND
batches are IN THE TIP (`Weak.lean:646 import Weak.WeakRvwmoKillIO`).  **IN FLIGHT: W8 (f2-ctx) RELAUNCH 5** (w2, RUNNING — rev 45; its paragraph below is binding and UNCHANGED, plus the [R41.1-alt] addendum after it).
**LAUNCHABLE: the THIRD Stage 2 batch** below (owner's batch nod — Q-BATCH-3) and **W8 (f2-ctx) RELAUNCH 5** (serial MachCSL lane; the paragraph below; proceeds under
Q-F2-PTE-WINDOW's provisional (a), non-blocking).  **Gated**: W13 (R) on W5d-G (shared `Supply`/`Lin`/`Glue`/`Walk*`); W14 on W13 (W) + W5d-G; W10 on its sizing
pass; W11 on W8's export (S4) + W13 (K-cat); W8 (f3-rest) on (f2-ctx).  Weekly cap [OWN.51] stands.  The rev-42 record follows after the RESULTS, the THIRD SET and
RELAUNCH 5.
**Rev 44 RESULTS (2026-10-13; every cite re-read at the tip).**  **W13 (R3′) DONE, MERGED 11:39** (w4; `../weak-orch/allocproc_R3p_prompt.txt` carried [R40.1]
(α)): `GraphFabResidue.lean:112-124` — `ioResidue`'s (R3) = `(gisIo x ∧ gisIo y ∧ gpo x y) ∨ (gmem x ∧ gmem y ∧ gfBefore GF x y)`; `ioResidueIo :149` restated
("an I/O endpoint, or both endpoints `gmem` fabric members"); `ioResidueNodev :161`; the header `:23-44` names the trusted-surface change AND the `DFence`
counter-model; **§5 `:322-361` = the [R39.s4] COMPUTED check**: `ioResidueGmo` SATISFIABLE on `GraphFabResidue.diskFab`, a bundle with the disk row's used-idx
`DWriteDev` RAM store as a member (`:331`), beside `w13fIoResidueOk :286`.  `WeakRvwmoLin2.lean` §8.3: `gfDevGmo :1222` stays the Prop (`gfDevWIo :1225` the premise); `gfDevGmoOfRes :1237 :
ioResidueGmo GF → gfDevWIo GF → gfDevGmo GF` PROVES it [R41.s8] (via `WeakRvwmoLin2.wioGmem`; replaces `gfDevGmoOfIo`); **`fconfTraceRealizeIO :1284` premises = `rvwmoMinusConsistent`,
`grule14`, `ioResidueGmo`, `gdiskRead14`, `gfexecConfIO`, `gfDevWIo`, `gxProg.length ≤ N`** — EXACTLY [R40.1] (α)'s acceptance; `w13fIoDevOrdered` re-proved (`:1427`
uses `gfDevGmoOfRes w13fIo w13fIoResidueOk`).  **DEVIATION (recorded, harmless)**: the three ARBITRARY-trace lemmas `devOrderOfPtraceExtIO :1245`,
`trDevOrderedOfPtraceIO :1253`, `fconfSupply' :1263` KEEP `gfDevGmo` as an explicit premise beside `gfDevWIo` — their callers discharge it by `gfDevGmoOfRes`
(`:1305`); nothing downstream weakens.  `WeakRvwmoFabInd.lean` docstring; `Lin2.lean:50-70` header says "(R3′) ([OWN.53], [R40.1] (α))".  `audit.sh --weak` PASS
(3436 jobs; the item's files are in no registered root's closure [R40.s1]).  **W11 (iv)c DONE, MERGED 11:41** (w5): `RvwmoXv6ScaT.lean` §(6) `:806-`:
`linCandDiskLatA :837` (any admissible anchor class containing the disk-row reads: `gwf`, `gloadValue`, `ancOk` → `candDiskLat (linCandA G anc)`),
`linCandDiskLat` (on `linCandIO`, via `ancOkIO`: rule 14, `ioResidueGmo`, `gdiskRead14`), `linCandDiskLatMinus` (from RVWMO⁻); `linCandScaT`'s premise list
UNCHANGED (header `:42-49`); M1's `candDiskLat` premise is now DERIVABLE on RVWMO given `gdiskRead14` — which (K)'s normalization supplies.  **D35-fix DONE,
MERGED 11:47** (w1; `audit.sh --weak --build` PASS, **13 roots re-audited, `baseline-weak.json` UNCHANGED** — no certificate verdict flipped, as predicted (no
`W.rl` in the image)): `WeakRvwmoGraph.lean:252 lbRcsc := lbAq || lbRl`, `grcsc :256` (defined HERE, `AxGraphCat` uses it — [R40.s4]'s move done), `lbRcscMem
:262` (was `lbRcscBits`), `grelAcqGrcsc :272` (the converse `grcsc → grelAcq`, Rocq's `grcsc_grel_acq`, DELETED as FALSE — two `LStore true` in po), `gppo
:283`'s rule-7 arm `grcsc`, header `:64-67/:85-86` (deviation 7 + the Rocq-arm note); `AxGraphCat.lean:38-42/:81-88` header + port map; `CatFloor.lean:31`
`grelAcqGmoC` DELETED — the twins are stated over `rvwmoCatAD` + `noPlainAqC :58` only; `roots-weak.txt:18-23` glosses gain "model rule 7 = riscv.cat's RCsc
[OWN.54]"; the grep `lbRcsc|grcsc|grelAcq` is now 20 files (the planned 14 + `WeakRvwmoLin`, `ProbeK1`, `ProbeRestr`, `CycWit`, `Adm`, `Norm` — the extra edits
are re-cased witnesses/probes and the `lblRenRcsc` home); `Restr` touched for the same reason.  The registered LB roots' TEXT unchanged, PREMISE = riscv.cat.
**W13 (K) DONE, MERGED 12:30** (w4; `Weak.lean:646`; 3437 jobs): NEW leaf **`Weak/WeakRvwmoKillIO.lean` (708)** — §1 `gmoIo :77`, `gdiskRd :82`, `ioExtra :86`
(= residue ∪ `gmoIo` ∪ `gdiskRd`), **`racyDIO :90 := racyDX GF.gfGd (ioExtra GF)`** (`racyDIODec`); §2 `ioExtraGmem :130`, `ioExtraGmo :144` (every extra arm
gmo-forward in the ORIGINAL graph — "(T) directly"); §3 transport: `ioResidueRen :178`, `gfDevWIoRen :194`, `ioResidueHull :242`, `ioResidueGmoHull :279`,
`gdiskRead14Hull :286`, `gfDevWIoHull :295`; §4 **`normalizeOfAcyclicIO :308`** (a `racyDIO`-acyclic core graph re-times via `Topo.normalizeOfAcyclicX` to RVWMO⁻ +
rule 14 KEEPING `ioResidueGmo`, `gmoIo` and `gdiskRead14` — exactly `fconfTraceRealizeIO`'s premises, so **(K) SUPPLIES `gdiskRead14`**), `fconfRealizeIO :345`
(the normalized graph's `glinEidsIO` realizes along the fabric); §5 `cycleKillIO :396`, `t2linAuxIO :429`/`t2linIO :454`, **`hullRunIO :465`** (Glue's `hullRun`
at the fabric, `fab ∘ dcnt`), `hullRunOfKillIO :494`, `t2linRealizeIO :516`; §6 `ioCross :540 := gcrossE ∪ ioExtra`, `racyDIOSplit :543`, `cycleSegmentsIO :560`,
`cycleKillIOC :566` (the cat kill at `X := ioCross`), `ioEntryRelGmo :574`; §7 **`ioSegPinned :609`** (Claim L-IO as a lemma: `entry <gmo exit` from (R1)/(R3) + (R2)
+ check (i) `noReadEdgeOutsideGmo :584`), **check (i) PROVED for RVWMO⁻'s `rsame`: `rsameNoReadEdge :655`, `ioSegPinnedMinus :664`**; §8 non-vacuity
`w13fIoRacyDIOAcyclic :693` (the NON-EMPTY `w13f` fabric is `racyDIO`-acyclic), `w13fIoRevRacyDIOCycle :701` (fabric reversed against gmo ⇒ a 2-cycle: the relation
bites).  Deviations (header `:47-61`): (1) FILES — `racyDIO` cannot live at `Acyc.lean:200` (its arms name `Gfexec`); `Acyc` gained the PARAMETRIC `racyDX`, `Topo`
`topoExistsX`/`normalizeOfAcyclicX`, `hullRunIO` is here, not in `Glue`; (2) `gdHull` UNCHANGED (it already keeps the cut rows' I/O events; `gfHull` filters `gfDev`);
(3) the same-row residue arms + disk-read pairs join the CROSS order `ioCross`, not the segment relation — `CatLin`'s kit reused as is; (4) the induction is over
RVWMO⁻ because `gfexecConfHull` (`FabInd.lean:377`) takes `gfexecConsistent`, which a cat graph lacks.  No new trusted text (`racyDIO` is a proof device).  **OPEN
(placed, rev 44)**: (ii) `lockWordDiscAt` is NOT a precondition of the graph lemma — it is the precondition of the CERTIFICATES of the window's racy lock-layer
reads (C1/C2) → **W11 (i)** (§C W11); check (i) is FALSE for the cat chain's `CatLin.rsameC :114` (its rfi arm forwards a read from a po-earlier write WITHOUT gmo)
→ **W13 (K-cat)** (NEW S–M, below); the cat-side induction needs `gfexecConfHull` without `gfexecConsistent` → **FabInd-S** (NEW S, below).  **W13 (F-dep) DONE,
MERGED 12:50** (w3; (A1) [OWN.52]; 3437 jobs; one `roots-weak.txt` header conflict resolved keeping both notes): `AxDeps.lean` — `lbIsIoRd :203`/`lbIsIoWr :208`/
`lbIsRT :216`/`lbIsWT :218`, **`gtdepsWf :236`** (I/O endpoints admitted), **`gtAdFull :265`** (addr/data edges into RAM writes from ANY read; `gppo12T` over it;
`gtAdSubFull`, `gppo12AdFull`, `gppoCatAdFull`), `dstepT :631` with the `LDev` arms `:637` (an MMIO load is a READ and joins `dtLd`, an MMIO store a WRITE; `.dev`
inert; the untagged `dstep` STAYS inert, `WeakRvwmoConf.lean:499`), **the PERMANENT smoke test `ioGtCatT :1449 : rvwmoCatConsistentT ioGt`** (the tagged model
SATISFIED on an I/O-active graph carrying the new edges, by computation) + `ioGtDepsWfB`/`ioGtForgetDeps`; header `:20-47/:93-110` names the deviation; the registered
roots' TEXT unchanged, PREMISE WEAKER (`roots-weak.txt:13-17`).  **OPEN**: `gdexecQconfT` (`CatLinChain.lean:324-330`) still requires `emDevfree`, so the new edges
have NO consumer yet — they first matter at W13 (W)'s `xv6ConfS` (the device-active bundle); recorded in (W)'s launch text below.  **W8 (f2-ctx): (a′-r) + S3-a
MERGED 11:17** (RELAUNCH 3; `ProofPipealloc` `kmapId` fix; `ChainDefs` `memAbove`/`loadsChained` + step laws; `Resources.loadsChained_store/_dma/_load` STATED), then
**RELAUNCH 4 → S3-b + S3-c0 MERGED 12:13** (w2; 3859 jobs; lint/audit/`--weak`/tcb PASS, `expected.json` UNCHANGED; `PROGRESS-W8f2.md` RELAUNCH 4 section): **S3
DESIGN = (A′)** (both options FAITHFUL — custody-spec text, the ISA is silent): the `.pte` exemption is read off MEMORY — the pages a Sv39 walk reaches, AS OF the
entry's position `t`, from REGISTERED ROOT WORDS: `MachCSL/Reserved.lean` `RsvKind.roots cnt stride` (footprint-free registry entry); `ChainDefs.lean` `entAsOf`,
`wordAsOf`, `ptPtrTo`, `ptChildAt`, `ptPageAt`, `ptRootAt`, **`ptByteAt :670`**, `lockPubByteIn`, `lockWordsByte`, `chainExAt` + the `_grow` lemmas (a step at top `T`
adds entries above `T` only, so the exemption at `t ≤ T` never changes — the step laws' `hex` at positions `≤ top`); `Xv6/KernelRsv.lean:70-72` `xv6KptRootR =
⟨KA.kernel_pagetable, .roots 1 8⟩`, `xv6ProcRootsR = ⟨KA.proc + 80, .roots 64 376⟩` (in `xv6PostLockRegions :106`; `BootRsv`/`rsvLocksLow` cases) — xv6 registers ONE
mechanism's two instances, covering [OWN.39]'s user tables from the store of their root into `p->pagetable` until `freeproc`'s clear; **S3-c0**: `Resources.lean`
`byteSrcOk`, **`loadSrcOk :1273`** (the load's obligation, NAMED), `chainEx σ`, `loadsChained_load :1288` restated over it [R41.s2]; `Ctx` `ownCtx_key_chain`; `Wp`
`ctxByte_srcOk`/`ctxBytes_srcOk` (a plain load of owned context bytes PAYS its obligation); `WpAtomic` `srcCertAt`/`readCertsAt`/`memModel_readCerts` — all STATED,
NOT WIRED.  Why not (A) literal (kernel root only — user roots are run-time values) or (B) a ghost PT-page set (the export is a PURE predicate of `σ`, W8-design (1):
a ghost set needs a second bridge and must SHRINK at `freewalk`).  **CAVEAT (WEAKER, named by the worker; `PROGRESS-W8f2.md` "Precision note"; bound CORRECTED [R41.1])**: in `freeproc`
(`kernel/proc.c:156-163`; image `0x80001b2c jal proc_freepagetable`, `0x80001b30 sd zero,80(s1)`) the root page is `kfree`d (`freewalk`'s last `kfree(pagetable)`,
`vm.c:279`) BEFORE `p->pagetable = 0`; and `freewalk` (`vm.c:265-280`) `kfree`s EVERY interior page-table page (`freewalk(child)`, level-0 then level-1) BEFORE
clearing the parent slot naming it (`pagetable[i] = 0`, `:274`) — under (A′) each such page stays `ptPageAt`-reachable (`ChainDefs.lean:660-662`, depth ≤ 2) from the
still-stored root word between its `kfree`'s `release(&kmem.lock)` (`kalloc.c:62`, the page becomes allocatable) and the clear; a page another hart's `kalloc` takes in
such a window is exempt until the clear — the export claims LESS there (sound).  Leaf DATA pages are unaffected (`uvmunmap` frees them before `*pte = 0`, but leaves
have RWX ≠ 0 and `ptChildAt` follows `ptPtrTo` pointers only).  Assessment → **Q-F2-PTE-WINDOW** (§D FIRST; recommended (a): accept as a NAMED weakening, the WINDOWS
stated in the export's `.pte` arm — every page-table page of the dying table (≈ 5 for a small process), each from its `kfree`'s release to the clear of its pointer;
the junk fills themselves reach no RAM page — `kfree`'s `memset(pa, 1, PGSIZE)` (`kalloc.c:55`) is a V-only pointer PTE to `0x4040404040000` (`ptPtrTo :651-653`),
outside RAM, `kalloc`'s `memset(5)` (`:80`) has RWX ≠ 0 and the walk stops — but a NEW owner that writes a V-only pointer-shaped word before the clear extends the
exemption to whatever RAM page that word names, so the honest bound is the WINDOW, not a page count).  Remaining: S3 wiring (the conjunct, the load rules, the `readAU` client sweep coupled to
X1/X5 with TWO receipt arms), X1/X4/X5, S4 → RELAUNCH 5 below.
**STAGE 2 — THE THIRD LAUNCH SET (rev 44).**  Ground: EVERYTHING of the first two batches is in the tip — W12 (+W12b) ✓, W13 (L) ✓, (F-dep) ✓, (R3′) ✓, (K) ✓,
D35-fix ✓, W11 (iv)c ✓; the serial MachCSL lane is FREE until W8 (f2-ctx) RELAUNCH 5 (w2: `MachCSL/`, `Xv6/`, `Weak/WeakAdequacy.lean` — no graph item touches
these; each of its cone merges REBUILDS `Weak/`).  Per item — deps / files / parallel-safety / size / acceptance.  **W5d-G G1–G5** (§C W5d-G; the second batch's
"W5d-G next"): deps MET — (F-dep) (1) ✓ (the `LDev` sweep of `Supply`/`Fab`/`WeakEvInst` is landed, G1/G2/G5's files have ONE owner again), (K) ✓ (`racyD`'s owner
is free; (K) left the PARAMETRIC `racyDX` in `Acyc` and `topoExistsX`/`normalizeOfAcyclicX` in `Topo` — G3's fetch fragment enters as a further parameter arm
beside `ioExtra`, NOT as a second redefinition: the combined instance `racyDX GD (ioExtra ∪ fetchE)` lives in `WeakRvwmoKillIO.lean` beside `racyDIO :90`, or
`racyDIO`'s `ioExtra` gains the arm — the worker says which; `normalizeOfAcyclicIO :308` then re-proves over it), W12 ✓, W12b ✓ (`Floor` single-writer: the twins left
`Floor` alone), (L) ✓ (`Lin`).  Files (re-cite at launch — the (F-dep) sweep moved `Supply`/`Fab`/`WeakEvInst` lines): G1 `WeakRvwmoSupply.lean` (`emFetchImg :367` today,
was `:277-352` [R41.s2]), `WeakRvwmoFab.lean` (the `Gfexec` bundle's fetch-clause SLOT `:816` — `emZifencei` replaces `emFetchImg` there), `WeakEvInst`/`WeakEvLang` (lemma),
`GraphFetchSpike` (the slot content); G2 `WeakRvwmoConf.lean:57-66,147`; G3 `WeakRvwmoGraph.lean` (`Gdexec.gdFetch` — a STRUCTURE change to `structure Gdexec where gdG; gdDeps`
`:669-671`: either a field with default `[]` + a sweep of the anonymous-constructor literals (RE-COUNT at launch: ≥ 23 structure-syntax `gdDeps :=` sites + the literals
added by (K)/(F-dep)/(R3′), e.g. `KillIO.lean:701 ⟨⟨w13fIoG, []⟩, …⟩`, `GraphFabResidue.diskFab :339`, `AxDeps.ioGt :1441`), or a wrapper `GdexecF := ⟨GD, gdFetch⟩`
consumed by `xv6ConfS`/`racyDX` only — the worker says which in its FIRST report; `forget : GdexecT → Gdexec` fills it [R41.2][R41.s5]), `Acyc` (`racyDX` instance),
`Glue.lean:205-223`, `Hull.lean:716`, `Topo` (parametric), `KillIO` (the combined instance); G4 `Topo`; G5 `Lin`, `Floor`, `Supply` (`:743-883` region).  Parallel-safe vs (f2-ctx) ✓, vs
W9a ✓ (`PinBridge3` NEW), vs W13 (W) — (W) CONSUMES the `Gfexec` bundle whose fetch clause G1 rewrites: ONE S rebase of (W)'s `xv6ConfS` statement when G1 lands
(G1 is W5d-G's FIRST increment, M ≈ 350–450 — land it early); vs FabInd-S: SHARED `WeakRvwmoKillIO.lean` (FabInd-S fixes the `:423` call; G3 adds the combined
instance beside `racyDIO :86-90` and re-proves `normalizeOfAcyclicIO :308`) — **FabInd-S LANDS BEFORE G3 STARTS** (a gate, not a preference; G1/G2 precede G3, so it
costs nothing), else G3 rebases the one-line `:423` call [R41.3]; vs (K-cat) ✓ (NEW leaf file).  Order inside the item: G1 →
G2 → G3 → G4 → G5 (G1 first for (W); G3/G4 on (K)'s parametric forms).  Size L ≈ 1.8–2.2k (+ XL risk R1, §C W5d-G: hull closure — R1 (a) E1′ recommended) + a FULL-CONE rebuild per increment (minutes, not lines [R41.2]).
Acceptance (§C W5d-G): `emFenceI` + `emFenceISound`; the `emZifencei` content in the `Gfexec` slot at the real slot tag [OWN.26]; the six G0 carry-overs;
`Gdexec.gdFetch` [OWN.18]; `retimeZifencei`; `supplyOfQconf` producing the M2 cut clause; `normalizeOfAcyclicIO` re-proved over the combined relation (I/O positions,
disk-read anchors AND the fetch fragment kept); hull closure per §B(4)(iii) R1 (a); **every increment: `lake build` of the registered cone + `audit.sh --weak --build` — 13 roots, `baseline-weak.json` UNCHANGED,
the roots' STATEMENTS unchanged (report; M1/M2's premises are candidate-level and the AxSpin roots are over `GdexecT`/`forget`, so a default-valued field or a
`forget`-side fill keeps them — only the audit shows it) [R41.2]**: `Graph`/`Acyc`/`Topo`/`Conf`/`Supply`/`Hull`/`Lin`/`WeakEvInst`/`WeakEvLang` (and `AxDeps`, `Adm`,
`AxSpinSpike`, `SrvwmoXv6Witness`, `VirtioProg`, `WeakAdequacy`) are in EVERY registered root's import closure (`roots-weak.txt`: 13 roots, 493 modules); OUT are only
`Fab`/`GraphFetchSpike`/`Glue`/`Floor` and all of `KillIO`/`CatLin*`/`Lin2`/`FabInd`/`GraphFabResidue`/`PinBridge*` — W5d-G is a RE-AUDIT item like D35-fix.
**W9a `Weak/WeakRvwmoPinBridge3.lean`** (§C W9a): deps MET — W12's `segPinC` ✓ (`CatLin.lean`), **(F-dep) (2)/(3) ✓** (the pin bridge `pinSegPin`/`pinSegPin'`/
`checkerTaintSubProv` RE-PROVED under the tagged `dstepT` MMIO arms — the rev-43 gate).  Files: NEW `PinBridge3.lean` (reads `PinBridge.lean` 360, `PinBridge2.lean`
601 — `reaches`/`psites`, §8 — and `CatLin`'s `segPinC`/`segPinCForward`; an S lemma edit to `PinBridge2` is allowed — no other item touches it).  Parallel-safe vs
everything ✓.  Size L (M–L + M [R6.1], ≈ 0.8–1.2k).  Acceptance: `pinSegPin'` applied at every certifying site of the REAL `pstepEv` run targeting `segPinC`
(`pinStepOfSegPinArm`; PDep entries across an rfi via `segPinCForward`); no generator work (§B(9)); build/`audit.sh --weak` unchanged (automatic — `PinBridge*`/`CatLin`
are OUT of the roots' closure [R41.2]).  **FabInd-S** (NEW rev 44;
S ≈ 10–40 lines; `Weak/WeakRvwmoFabInd.lean` only): `gfexecConfHull :377-383` takes `gfexecConsistent GF` and `hullOk GF.gfGd.gdG cs` and its proof DISCARDS both
(`rintro _ hdc _ ⟨…⟩` `:384`) — drop the unused `gfexecConsistent` (and `hullOk`, if the worker confirms no caller needs the arity) and fix the 2 in-file uses
(`:535`, `:570`) + 4 docstring mentions (`:17,:37,:51,:61`) + the def [R41.s1], and the ONE external caller `WeakRvwmoKillIO.lean:423` (which then no longer needs `WeakRvwmoKillIO.gfexecConsistentOfRes`); `gfexecConfRen`
unchanged.  Spec: no trusted text (a hull transport lemma).  Why: (K)'s deviation (4) — the cat-side induction (`cycleKillIOC`/`t2linIO` over `rvwmoCatAD` graphs)
cannot supply `gfexecConsistent`; `hullRunIO`/`fconfRealizeIO` take only `rvwmoCoreD` + the hull's conformance, so this is the last cat-side gap in (K)'s chain.
Acceptance: build green; `gfexecConfHull`'s statement shorter, every caller re-proved; `audit.sh --weak` unchanged (automatic — `FabInd`/`KillIO` are OUT of the
closure).  Parallel-safe vs all ✓ EXCEPT `WeakRvwmoKillIO.lean`, shared with W5d-G G3 — FabInd-S lands BEFORE G3 starts [R41.3].  **W13 (K-cat)** (NEW rev
44; S–M ≈ 150–300 lines; NEW leaf `Weak/WeakRvwmoKillIOC.lean` importing `WeakRvwmoKillIO` + `CatLin`): the cat twin of `ioSegPinned :609` on `CatLin.rsameC :114`,
whose rfi arm (`grfi :80`) forwards a read from a po-earlier same-hart write WITHOUT a gmo edge, so check (i) `noReadEdgeOutsideGmo :584` FAILS; the refined
invariant of §C W13 R5 (plan `:4074-4076`): after the I/O event `x`, every event of the segment is "gmo-after `x`, OR a read FORWARDED (`grfi`) from a write gmo-after
`x`", closed under every `gpow`/`gppo`/deps/rfi step EXCEPT a `PR∧SR∧¬PW` fence (a fence ordering prior reads before later reads but not prior writes — the forwarded
read's source write may still be gmo-before `x`'s successor chain) — per arm [R41.s3], so the worker neither widens the side condition to `PR∧¬PW` nor misses an arm:
`deps` target writes are ordered after `x` by (R2) (`gdepsWf`, `WeakRvwmoGraph.lean:675-677`: targets are `lbIsW`); `gpoloc :279-280`'s R→R same-address arm keeps the
later read "forwarded from a po-later write, or coherence-after"; `gacqPo`/`grcsc` need an `aq`/`rl` label a forwarded plain load lacks; `grfi :80` is the invariant's
own second disjunct; the ONLY break is `gfenceCovers :228-232` with `pr ∧ sr ∧ ¬ pw`; deliverables `WeakRvwmoKillIOC.afterIo` (the invariant), `ioSegPinnedC` (with the NAMED side
condition `noPrSrFenceInSeg` — no `PR∧SR∧¬PW` fence label in the segment's hart row between `x` and the exit), `rsameCAfterIo` (closure).  Discharge of the side
condition is an IMAGE fact for W11/W14 (its INPUT is the image fence census — opcode `0x0f`/funct3 0: 4 × `fence iorw,iorw`, 2 × `fence rw,w`, 1 × `fence r,rw`
[R41.s3]): the image's only such fence is `fence r,rw` `0x80000ee6` (`KernelImage.lean:2748` `0x0230000f`; `WkStartedLoad.lean:22`; harts ≥ 1's `started` spin,
reached BEFORE their first I/O event — `timerinit` is sstc CSR-only, `start.c:56-65`; hart 0 skips it) — user-mode code after `sret` UNVERIFIED for that sub-case (already noted at §C W13 R5).  Spec: no trusted text (proof device; riscv.cat's rfi
forwarding is exactly what makes the RVWMO⁻ check (i) fail — the cat chain is FAITHFUL, the RVWMO⁻ one STRONGER).  Acceptance: `ioSegPinnedC` proved; the
`w13f` instance (no fence in row 0 after the UART store) checked; build/`audit.sh --weak` unchanged.  Parallel-safe vs all ✓ (new file; reads `KillIO`/`CatLin`).
**W13 (W)** (§C W13 (W); `xv6ConfS` on `gfexecConfIO` + W13-wit; M–L ≈ 0.6–1k): deps MET — (K) ✓, (F-dep) ✓, (L) ✓, (I) ✓, (R3′) ✓ (D26's order).  Content: the
SHAPED, UNPINNED, FABRIC-ORDERED, TAGGED bundle `xv6ConfS` (§A(†)) = `gdexecQconfT` (`CatLinChain.lean:324`) at the device-ACTIVE bundle — i.e. WITHOUT `emDevfree`
(`:330`; this is where (F-dep)'s I/O-endpoint edges first MATTER: state the tagged conformance over `gfexecConfIO`'s rows and keep `gdexecQconfTForget :337`'s
projection), `gfexecConfIO` (`Fab`), the fetch-clause slot (`Fab.lean:816`; `emZifencei` once G1 lands — until then the slot's current content, ONE S rebase), and
**the discharge of `gfDevWIo`** (the (R3′) named premise) **[R41.4]: `gfDevWIoOfXv6` takes a NAMED disk-side hypothesis `usedElemGateOk` (or the worker's name) —
on an xv6 run the used-ELEMENT `DWriteDev`'s gate `phase ∧ completeOk ∧ pushOk` (`VirtioProg.lean:88-90`) holds and its target `pa s` is RAM, equivalently no own-guard
SKIP at that node (`WeakEvInst.lean:519-525`: the SKIP arm fires on `g s = none ∨ ¬ ramBytes (pa s) …`) [R40.s6]; the HART half is PROVED here by [R40.s2]'s three cites
(`lbAdmin` never `LDev`; hart arms keep `d' = d`; `LDev` projects to `LIo`); the DISK half is a RUN-LEVEL virtio fact — a property of the state `virtio_disk_rw`'s
descriptor/avail discipline produces, NOT of `pdiskProg`'s shape (`VirtioProg.lean:68-95`), and not available in (W)'s consumer files — DISCHARGED by W14's
device-active witness / the disk invariant, or it stays a named premise.  Spec: RVWMO/riscv.cat/Sail/Zifencei/PMAs are SILENT on device programs; `usedElemGateOk` is
device-model text EQUAL to MachCSL's disk step on xv6 runs (owner informed, no menu)**; + **W13-wit**: hart 0's run `_entry → … →
uartinitone` to its first UART store `sb zero,1(a5)` `0x800008a0` (`LIo .wr 0x10000001 [0]` in row 0 — the first candidate with a NON-EMPTY `gfDev`, D31), by kernel
evaluation on W5c's `esilAdmRun` — it exercises `gfDevWIo`'s HART half only (no disk activity before the UART store: the disk half is VACUOUS on it and the Bool twin
cannot catch a wrong guess; the disk half's computed check belongs to W14's device-active witness [R41.s6]); **[R38.s1] the COMPUTED satisfiability check of every conformance text** — `xv6ConfS`'s Bool twin `true` on W13-wit's bundle (the
check that caught (F-dep)'s vacuity); gate 2 (a device-ACTIVE disk witness) → W14 as before.  Files: NEW `Weak/GraphFabConf.lean` (or the worker's name; `xv6ConfS`
exists today only in docstrings — `Fab.lean:816`, `GraphFetchSpike.lean:89,314`) + `W13Wit.lean`; consumer-only of `Fab`/`CatLinChain`/`Lin2`/`KillIO`.
Parallel-safe vs (f2-ctx) ✓, vs W9a ✓, vs W5d-G: ONE S rebase on G1 (above); vs FabInd-S/(K-cat) ✓ — RECOMMENDED as the SAME worker's increments: **FabInd-S →
(K-cat) → (W)** (S, S–M, M–L; each green).  Acceptance: `xv6ConfS` STATED over the device-active tagged text with `gdexecQconfT`'s projection kept; `gfDevWIo`
discharged (`gfDevWIoOfXv6`: hart half PROVED, disk half the NAMED `usedElemGateOk`) — `fconfTraceRealizeIO`'s premise list then closes on xv6 runs except
`gdiskRead14` (supplied by (K)), the trusted `ioResidueGmo`, and the named `usedElemGateOk` (W14) [R41.4]; W13-wit builds with a non-empty `gfDev`; the Bool twin
evaluates `true` (hart half); build/`audit.sh --weak` unchanged (automatic — new consumer files, OUT of the closure).  **W13 (R)** (the re-thread of the
constant-fabric chain onto `gfexecConfIO`: 8.6k lines / 14 files — `Supply`, `LinInd`, `Cert4`, `Glue`, `Glue2`, `Walk*`, `Progress`, `PreNorm*`, `Capstone`; L–XL): deps
MET but it SHARES `Supply`/`Lin`/`Glue` with W5d-G G1/G3/G5 — **after W5d-G** (the fourth set).  **W10**: D35-fix ✓ (the `CatFloor` twins over `rvwmoCatAD` +
`noPlainAqC`), but its design is one line (§C W10, "unverified") — a **SIZING PASS first** (S, read-only, any lane: `wsegSupply`/`walkPolicy` on the D35-fixed twins,
whether W10 absorbs `Floor`/`Cert3`'s originals; by the reviser or a spike worker), NOT a batch slot.  **W14**: after W13 (W) + W5d-G — NOT NOW.  **W11**: after W8's
export (S4) + (K-cat) — NOT NOW ((iv)c ✓).  **W8 (f3-rest)**: after (f2-ctx).  **RECOMMENDED BATCH (≤ 3, parallel, pairwise file-disjoint up to the ONE named S
rebase): W5d-G G1–G5 (G1 FIRST) ∥ W9a ∥ W13 (W) [FabInd-S → (K-cat) → (W)]** — graph lane, three workers, beside W8 (f2-ctx) RELAUNCH 5 (w2, serial lane; four
workers in all); the owner's batch nod is needed ([OWN.55] covered the second batch) — **Q-BATCH-3** (§D).  Disjointness: W5d-G's files ∩ W9a = ∅ (`PinBridge*` are in
none of G1–G5); ∩ (W)/(K-cat) = ∅ except the `Gfexec` CONSUMER rebase (S); ∩ FabInd-S = `WeakRvwmoKillIO.lean` (`:423` vs `:86-90/:308`) — FabInd-S before G3
[R41.3]; W9a ∩ (W) = ∅; (f2-ctx) ∩ the graph items = ∅ (`MachCSL/`, `Xv6/`, `WeakAdequacy`).
Landing order: FabInd-S first (S; frees (K)'s cat-side induction, and the GATE for G3's `KillIO` edit [R41.3]), G1 early (so (W) rebases once), the rest any order.  Usage: [OWN.51].
**RELAUNCH 5 — W8 (f2-ctx): S3 WIRING → S4 (rev 44; serial MachCSL lane; w2 on the tip; after the 15:10 five-hour reset).**  Binding text: RELAUNCH 2's paragraph
below (with [OWN.49] (a′-r), [OWN.50] F-C (i)) as executed by RELAUNCH 3/4 (briefs `../weak-orch/allocproc_W8f2_cont3/cont4_prompt.txt`), the worker's
`PROGRESS-W8f2.md` RELAUNCH 4 section "Next (S3 wiring → S4)" (BINDING step list; it found NO plan clause wrong), §C W8, and THIS paragraph.  **STATE**: S0, S1/S1′,
S2-pre, S2, (a′-r), S3-a, S3-b, S3-c0 MERGED; the design choice (A′) RECORDED (Rev 44 RESULTS); the caveat is **Q-F2-PTE-WINDOW**, provisionally **(a)** — PROCEED: S4's
`.pte` arm is `ptByteAt` as designed; its docstring and `pteDiscAt`'s STATE THE WINDOW ("bytes of pages reachable from a registered root word as of the access,
including a root page already freed by `proc_freepagetable` until `freeproc` clears `p->pagetable`, `0x80001b30`"); nothing else is parked on the ruling (option (b″)
would be a SEPARATE serial item after S4).  **Increments, in order (green each; one cone rebuild for S3, one for S4)**: **S3-c1 the conjunct** — `chainModelAt E σ :=
⌜loadsChained (chainEnv σ) (chainEx σ)⌝ ∗ ∃ Z, …` (the 7 destructuring sites: `ChainCert` ×4, `Wp.rsvModel_mono`, `Power:723`, `PowerText:473`, `Adequacy:508`,
`WpAtomic:938`, `Wp:1679`); `rsvModel_mono` gains `hlc`; stores by `loadsChained_store` + `chainExAt_grow` (`memGrow_writeBytes`, `memAbove_writeBytes`, top + 1;
`coh ≤ top` from `hmm`); DMA likewise; exclusive read/fence/`dropResv` by `rsvModelAt_congr` (`chainEx` reads `mem`/`top` only); `setRt` `rfl`; power-on
`loadsChained_zero`.  **S3-c2 the loads** — `memModel_load`/`memModel_load_rv` take `hsrc : loadSrcOk (chainEnv σ) (chainEx σ) σ.mem cpu pa n tvn` (`chainEx
(σ.afterLoad …) = chainEx σ` by `rfl`); callers: `Wp.swp_sail_mem_read_plain_ctx` ← `ctxBytes_srcOk` (landed), `WpAtomic.swp_sail_mem_read_aur` ← `readAU`'s opened
tuple gains `readCertsAt cpu pa n K Hs` beside `histBytes`, discharged by `memModel_readCerts` (landed); `readAUr` likewise (its two loads, `ReadAUr.lean`,
`WpSmodeFenceFloor:252`); `UIcache:245` (user loads: keys, as the ctx load).  **S3-c3 the `readAU` CLIENT SWEEP (the bulk; coupled to X1/X5)** — `srcCertAt` has arms
boot / device / own / static-lock-or-pub / chain; TWO more σ-dependent arms as RECEIPTS the rule converts with `histsAt`: **(a) a live DYNAMIC lock word** (`dynLkAt`
at `e.t`: the lock invariant's `lkDynReg` receipts + its `WordHist`) — `WpLock`'s pipe-lock reads (`holding`); **(b) a KERNEL-TABLE post-seal A/D entry** (`ptByteAt`
at `e.t`): `kptOn` gains the persisted root word (`Xv6.kptRoot_persist` already gives `↦₈□`), `kptBody` the pure fact "every discipline position `fl i j` ≤ every `W`
entry" (the seal precedes every walk), and a lemma `PTree.wf` + canonical pointer values ⇒ `ptPageAt`.  Clients: `KptInv` (1), `WpLock` (12 `unfold readAU` sites:
static ⇒ pub/lock arm, dynamic ⇒ (a)), `WpSmodeLwKey` builders, `Xv6/` `StartedInv`/`MainSecondaryParts` (pub arm), `DiskAcc`/`DiskInvDefs` (device arm; hart-0 init
entries by key or gate), `IcachePinwObl`/`IcachePinwLw`/`IdupCore`/`ProofIdup`/`IgetScan`/`IcacheTable` (`ip->ref` under `itable.lock`: chain lower bounds from the
lock's release record — **X1/X5's re-route**: hooks re-floored from the releaser's own vector, `WpLock.lean:1255,1461`; `ACQUIRE_LLB`/`ACQUIRESLEEP_LLB` withdrawn
for the 31 consumers — both greps EMPTY [R34.s5]; X4 device-only absorb).  **S4 the export** — `Xv6/AccessDiscipline.lean`: σ-readable `custAt` with **`.pte :=
ptByteAt`** (the window documented per (a)) and `.lockw` from `lockPubByteIn`/`dynLkAt` + the WINDOWED `lockRegionOk` for dynamic locks [R36.3]; `chainOkAt` from
`loadsChained` (the `started` byte by the export's boot-hop arm, `t ≤ bootEnd`); `pteDiscAt`; `xv6AccessDisc := chainOkAt ∧ lockWordDiscAt ∧ pteDiscAt ∧
cpuStaticAt` (FOUR of six; header `:4-7` and `roots.txt:20` say so; `cpuProcDiscAt`/`utextDiscAt` → W8 (f3-rest) [R34.1]); `SystemAdequacyDisc`/`LinkDiscAdequacy`
re-proved; root `xv6DiscAdequacy_closed` by NAME.  Rules unchanged (stop green on a wrong clause; spec-first options; the per-row table — rows 1–31, the 4 outside
sites, the walker — current; none RESISTS so far).  Parallel: the third graph batch is `Weak/`-only — do not edit `Weak/` except `WeakAdequacy.lean`; do not edit
root files.  Size: remaining ≈ 3–5k (S3 wiring ≈ 2–3.5k over the clients above, S4 ≈ 0.5–1k); 2 cone rebuilds.  Acceptance: `lake build MachCSL Xv6 Weak Vtest`
green, `lint.sh`, `audit.sh`, `audit.sh --weak`, `tcb.sh` (`expected.json` unchanged unless the export's modules change — report); registered roots unchanged in
statement except the (r2) root's export as stated; the export's `.pte` docstring names the window.  **W8 (f3-rest)** after it.
**RELAUNCH 5 ADDENDUM (rev 45; the RUNNING paragraph above is binding and UNCHANGED — the coordinator relays this to w2 as a launch addendum) [R41.1-alt]**: R41's
required docstring correction ([R41.1] (2)) is applied HERE rather than in the binding text because the running brief must not be edited; it changes no step. S4's `.pte`
docstring and `pteDiscAt` state the CORRECTED window: "bytes of pages reachable from a registered root word as of the access, including a page-table page already
freed by `freewalk`/`proc_freepagetable` until the pointer naming it is cleared (its parent's slot, `pagetable[i] = 0`, `vm.c:274`; for the root, `freeproc`'s
`p->pagetable = 0`, `0x80001b30`)" — §D Q-F2-PTE-WINDOW (a), §A's export sentence likewise.  Cite drift, re-cite at launch [R41.s2]: `Adequacy:508`/`WpAtomic:938`/
`Wp:1679` are pre-S3-c0 lines; `loadsChained_load` is `Resources.lean:1288`.  The X1/X5 "both greps EMPTY" is the TARGET: today `ACQUIRE_LLB|ACQUIRESLEEP_LLB` = 31 hits
in `Xv6/`; after X1/X5 both greps EMPTY.
**WAITS / LAUNCHABLE (rev 42) [OWN.52]–[OWN.54]**: **DONE and MERGED since rev 41 — W12 (+W12b)** (w1, 06:17), **W13 (L)** (w4, 05:56), **W8 (f2-ctx)
S0 + S2** (07:11, 109 files; the (a′-r) receipt work PARKED one error from green at `~/dev/weak-orch/parked/w8f2-aprime-r-wip/`, 22 files —
`Xv6/ProofPipealloc.lean` ~681, the rule's `kmapId` premise unmatched before address normalisation).  **IN FLIGHT: W8 (f2-ctx) RELAUNCH 3** (w2,
10:19; `../weak-orch/allocproc_W8f2_cont3_prompt.txt`; brief unchanged here).  **W13 (F-dep) RELAUNCHED under (A1)** (w3, 2026-10-13; the rev-41
paragraph below as amended by [OWN.52] — no (A2) interim; [R39.2]'s `CatLinChain` + `Adm` notes sent as a LAUNCH ADDENDUM, applied at launch; brief
otherwise unchanged) [rev 43]; **LAUNCHABLE: the SECOND Stage 2 batch** below (after [R39.1]–[R39.3], applied in rev 43).  Weekly cap [OWN.51] stands.
The rev-41 record follows.
**Rev 42 RESULTS (2026-10-13).**  **W12 + W12b DONE, MERGED** (`../weak-orch/parked/PROGRESS-W12.md`; `Weak.lean:640-645`): increment 1 = the
STATEMENT edits — `rvwmoCoreD GD := gwf ∧ gloadValue ∧ gatomicity ∧ gdepsWf` (`WeakRvwmoAcyc.lean:207`; `coreOfMinus`, the coercion
`coeCoreOfMinus :216` so RVWMO⁻ callers keep their text), `topoExists`/`normalizeOfAcyclic` (`WeakRvwmoTopo.lean:607`, LAST conjunct `gppoCat6Gmo
GD'.gdG :617` [R21.2]), `normalizeOfAcyclic'` (`Dec`), `topoSupply` (`Supply`), `topoLinearizesF` (`Fab`), `hullRealizableOfAcyclic` (`LinInd`),
`hullRealizableRowsG` (`Cert4`), `hullRun` (`Glue`), `hullCoreD` (`Hull`, no statement change); increment 2 = `Weak/CatLin.lean` (541; kill/cert/raw
chain PARAMETERISED by the cross order `X`; `catADOfCatT :54`), `CatLinHull.lean` (182; `hullCatAD :155` — transport hull → G, NO `hren`
injectivity: the believed risk did not materialise), `CatLinChain.lean` (439; `gdexecQconfT :320`, `gdexecQconfTForget`, `t2linOfL2'''C :291`,
**`xv6RvwmoSafeModuloT :403` STATED, not registered**), `CatLinWit.lean` (136; `sbrfi :90` — `rvwmoCatConsistentT` ✓ `:95`, `rvwmoCatAD` ✓ `:101`,
NOT RVWMO⁻ `:110`, `racyD`-acyclic `:124`, normalised `:128` — the [R6.s2] gate); increment 3 = W12b `Weak/CatFloor.lean` (836; per-byte coherence
invariant `finvC` with `cohUbA`, the forward bank `fwdOk`/`fwdHit`; `finvCStep :329` … `cpolReadCatAD :823`) + `CatFloorWit.lean` (118;
`sbrfiOldFinvFails`/`sbrfiNewFinv`/`sbrfiCertified` — the [R7.s5] gate) as **TWINS** (deviation: `Floor`/`Cert3` originals UNTOUCHED, so `Walk*`
compile and `Floor` stays single-writer for W5d-G G5); two premises beyond `rvwmoCatAD`: `grelAcqGmoC :60` (D35 — DROPPED by D35-fix [OWN.54]) and
`noPlainAqC :63` (D36 (a); kernel-true — the only plain `aq` read in any row is the DISK row's `DRead avail idx (aq)`, `VirtioProg.lean:74`, never a
hart reader's row).  Axioms: `propext`/`Classical.choice`/`Quot.sound` only.  **W13 (L) DONE, MERGED** (`PROGRESS-W13L.md`, ≈ +950 lines):
`WeakRvwmoLin.lean` §6 `:1889-2358` — the ANCHORED rank trace over any class `anc` (`gnxa`, `gancs`, `gaix`, `grankA`, `glinEidsA`, `linCandA`,
`linNwA`; admissibility `granc14`/`ancOk :1922-1926`; the write instance is DEFINITIONAL — `glinEidsAW`/`linCandAW` are `rfl` `:1931-1933`;
`glinAGmoAnc :2259`, `glinAAncIff :2288`); `WeakRvwmoLin2.lean` §8 `:1079-1415` — `ptraceRelIO`/`ptraceExtIO :1079-1083` (D7 arm gmo|(W ∪ IO)),
`gtraceLinearizationMinIO :1091`, the (L) anchors `gisAnc :1141` (writes, I/O events, disk-row reads), `gdiskRead14 :1153` (a NAMED premise, not
trusted: W13 (K)'s normalisation keeps it, (W)'s disk program supplies it), `ancOkIO :1166`, `rule14LinearizationIO :1203`, `gfDevGmo :1219`/
`gfDevWIo :1222`/`gfDevGmoOfIo :1225`, `devOrderOfPtraceExtIO :1233`, `trDevOrderedOfPtraceIO :1241`, **`fconfSupply' :1251` RESTATED without the
`before L` premise**, **`fconfTraceRealizeIO :1271`** (THE deliverable), non-vacuity at a NON-EMPTY fabric `w13fIoDevOrdered :1403` with the contrast
`w13fLinNotDevOrdered :1385` (the write-anchored trace REVERSES the two MMIO events); `RvwmoXv6Sca.lean` `linNwAAnc :208` (the prefix log at an
anchor = the writes gmo-before it — what W11 (iv)c `linCandDiskLat` uses), `linCandScaA :339`; `RvwmoXv6ScaT.lean` `linCandScaTA :748`,
`linCandScaTMinusA :790` (the old statements are the write instances, unchanged); `WeakRvwmoFabInd.lean:464-465` docstring.  Deviations D1–D3 (the
report).  **Residue of (L)**: `fconfTraceRealizeIO` carries `gfDevGmo` + `gfDevWIo` because the landed (R3) orders I/O PAIRS only — **Q-L-R3 RULED
(a) [OWN.53] → W13 (R3′) below**.
**W13 (R3′) — the [OWN.53] text change (S ≈ 0.1–0.2k; NEW rev 42; `Weak/` only; the W13 (K) worker's FIRST green increment) — DONE and MERGED 2026-10-13 11:39 (w4) [rev 44], with [R40.1] (α) APPLIED AT LAUNCH (`../weak-orch/allocproc_R3p_prompt.txt`): `gfDevWIo :1225` KEPT as the NAMED premise ([R41.s2]: `:1222` is `gfDevGmo`), `gfDevAnc` NOT introduced, `fconfTraceRealizeIO` drops `gfDevGmo` ONLY — the landed form is in Rev 44 RESULTS; rev 43's `gfDevAnc` sentences below are corrected in place.**  *Spec (FIRST)*:
RVWMO/riscv.cat/Sail have no device events; Zifencei and the PMAs are silent; `gfDev` and (R1)–(R3) are device-model/trusted-surface text (D45/D49).
*What changes*: `ioResidue`'s (R3) (`GraphFabResidue.lean:84`) becomes `(gisIo x ∧ gisIo y ∧ gpo x y) ∨ (gmem x ∧ gmem y ∧ gfBefore GF x y)` —
the fabric arm ranges over the members that HAVE a memory-order position **[R39.3]** (EQUAL in strength to "all members" on every anchor — anchors
are `gmem`; STRONGER than the silent ISA, EQUAL to MachCSL, where the disk's used-idx/status `DWriteDev` stores and the harts' MMIO are ONE fabric
order, on the events gmo places; an UNRESTRICTED arm would be FALSE-making: `gmoLt :137` needs `gxGmo` members and `graphOfCand :276` filters
`lbIsMem`, so on a bundle whose `gfDev` holds a non-`gmem` label — the counter-model below — the TRUSTED `ioResidueGmo` would be UNSATISFIABLE,
R38's vacuity class on trusted text); the file header's trusted-surface sentence and §A(6) say so.  Consumers: `ioResidueIo :114` ("every arm has
an I/O endpoint") loses the fabric case — restate as "… or both endpoints are `gmem` fabric members"; `ioResidueNodev :121` gains `GF.gfDev = []` (or "every member is I/O");
`lbIoOk :127` is stated at `dev := []` (the LB graph has no fabric); `w13fIoResidueOk :236`/`w13fIoRevExcluded :261` re-checked (members ARE I/O
there — truth unchanged); `WeakRvwmoLin2.lean` §8.3: `gfDevGmo` becomes a THEOREM **`gfDevGmoOfRes : ioResidueGmo GF → gfDevWIo GF → gfDevGmo GF` [R40.1] (α)** (`gisWIo ⇒ gmem`, so
the arm fires on every `gfBefore` pair of members; replacing `gfDevGmoOfIo :1225`); `fconfTraceRealizeIO :1271` DROPS `gfDevGmo` only; `devOrderOfPtraceExtIO :1233`/`trDevOrderedOfPtraceIO :1241`/`fconfSupply' :1251` are LEFT ALONE (so "§8.3 only" is TRUE); **`gfDevWIo` is NOT a consequence
of (R3)** (it says what the members ARE, not how they are ordered) and STAYS the NAMED premise — rev 43's `gfDevAnc GF := ∀ e ∈ GF.gfDev, gisAnc GF.gfGd.gdG e = true` (members ⊆ the (L) anchors `gisAnc :1141`) is NOT taken [R40.1]: (b) `devOrderOfPtraceExtIO :1233` is proved through `ptraceRelIO :1079`'s SECOND arm `gisWIo x ∧ gisWIo y ∧ gmoLt x y`, so under `gfDevAnc` it is NOT provable as stated (a disk-row READ member is not `gisWIo`; `ptraceRelIO`'s arm would have to widen to `gisAnc` and `glinIOPtraceExtIO :1195` be re-proved — §8 preamble + §8.2, not "§8.3 only"); (c) the motivating case does not exist on this program: a `DRead` block's own step is `pdevEv`-false (`WeakEvInst.lean:504-509`: `d' = d`, not I/O), the only `pdevEv`-true SILENT steps are the `DWriteDev` SKIP/ABORT (`:519-531`), and the row item FOLLOWING each (`VirtioProg.lean:68-95`) is a `DWriteDev` (W), the `DFence` (the counter-model), a `DRet` → START (`LDev`, I/O) or START after ABORT — a `DRead` is NEVER a member, so `gfDevWIo` and `gfDevAnc` have IDENTICAL discharge obligations on xv6 runs ("the used-element store's guard never skips").  `gfDevWIo` is a NAMED premise of
`fconfTraceRealizeIO`, NOT provable from the membership clause (`WeakRvwmoFab.lean:857`, `… ∨ tq k = true`) for a generic bundle (the W13 (L)
worker said the same of `gfDevWIo`): COUNTER-MODEL — the disk program has ONE `DFence` (`VirtioProg.lean:28,91`, before the used-idx write) emitted as
the ROW event `LFence true true true true` (`WeakEvInst.lean:511`), and a `DWriteDev` own-guard SKIP or ABORT is SILENT (`:519-531`, `l = LSilent`, no
row item; `LSilent` is an ADMIN label, `WeakAxRealize.lean:140-144`, folded into the NEXT row item's block by `admRunT`, `WeakRvwmoFab.lean:285-292`) while `pdevEv :605-611` [R40.s7] is `true` at EVERY disk `DWriteDev` node — **only the SKIP at the used-ELEMENT `DWriteDev` folds into the `DFence`'s block** (program order `VirtioProg.lean:68-95`: fill → status → used-element → `DFence` → used-idx; an ABORT ends the burst, `dp' = none`, and the next row item START is `LDev`) [R40.s6], so then the contact bit `tq k` of
that block is `true` and `(NCPU, k) ∈ gfDev` with a label that is neither `gisAnc` nor `gmem` (`lbIsMem :127` = R ∨ W ∨ Io) — rev 42's "every
disk-row event is a write, an I/O event or a read" was FALSE (the `DFence` row item is a fence).  Discharge of `gfDevWIo` belongs to W13 (W)/W14 — ONE guard: disk side from
the disk program's SHAPE plus xv6's guard invariant (no own-guard SKIP at the used-ELEMENT `DWriteDev` on an xv6 run — (I)'s analysis, to be PROVED
there, not assumed); hart side IMMEDIATE [R40.s2]: a hart block is a member only via an `LDev` row item — admin labels are `LSilent`/`LRegW`/`LCtrl` (+ `LInstr`/`LIFetch` under `instr`; `lbAdmin`, `WeakAxRealize.lean:140-144`), never `LDev`, so `pdevEv` is false on every hart admin step (the `.PDisk` match fails for harts, `WeakEvInst.lean:605-611`); hart RAM/fetch arms keep `d' = d` (`:316-360`), so `dvi k ≠ dvo k` also needs an `LDev` step; `LDev` projects to `LIo` (`WeakPromiseBridge.lean:542`), hence `gisIo` — a member by class = the hart half of `gfDevWIo` (not proved inside (R3′); (W)'s).  Files: `GraphFabResidue.lean`, `WeakRvwmoLin2.lean` (§8.3 only), `WeakRvwmoFabInd.lean:464-465` (docstring).
Parallel-safe vs (f2-ctx) ✓, vs (F-dep) ✓ (no `LDev` site in the three files), vs D35-fix ✓, vs W11 (iv)c ✓ (`RvwmoXv6Sca*`).  Acceptance: `lake
build Weak` green; `fconfTraceRealizeIO`'s premises = `rvwmoMinusConsistent`, `grule14`, `ioResidueGmo`, `gdiskRead14`, `gfexecConfIO`, **`gfDevWIo`
(NAMED; [R40.1] (α) — was rev 43's `gfDevAnc`)**, `gxProg.length ≤ N` — LANDED EXACTLY SO (`Lin2.lean:1284-1290`); `w13fIoDevOrdered` re-proved; `w13fIoResidueOk :236` re-proved (its members are I/O ⇒ `gmem`); the
`GraphFabResidue` header STATES the counter-model (why the arm is over `gmem` members); **[R39.s4] a COMPUTED check that `ioResidueGmo` is
SATISFIABLE on a bundle with a `DWriteDev` member** (the disk row's used-idx store beside a hart MMIO event — the (R3′) analogue of [R38.s1]; today
only `w13fIo`'s two MMIO events exist) — LANDED `GraphFabResidue.lean:322-361` (`diskFab`); `audit.sh --weak` unchanged; header + §A(6) sentence in place.  [R40.s7] after the (F-dep) merge every `WeakEvInst`/`VirtioProg`/`Fab` line above has drifted — the cites are rev-43's, the landed ones are in Rev 44 RESULTS.
**D35-fix — the [OWN.54] model-text correction (M ≈ 0.3–0.6k; [R40.s5] grep `lbRcsc|grcsc|grelAcq` = 14 files, EDITS = 17 (+ `Norm`, `ConfWit2`, `Adm` beyond the grep) + 1 rebuild (`AxSpinSpike`); NEW rev 42; `Weak/` only; one worker, any lane; RE-AUDIT) — DONE and MERGED 2026-10-13 11:47 (w1) [rev 44]; launched 11:14 AT ONCE in its own workspace per [R40.s1] (the "(R3′) lands first" gate was NOT load-bearing: (R3′)'s files are in no registered root's import closure, so its `audit.sh --weak` is a no-op — the audits that matter are this item's and (F-dep) (0)'s, both PASS: 13 roots re-audited, baseline unchanged); landed form in Rev 44 RESULTS (the grep is now 20 files).**  *Spec
(FIRST)*: riscv.cat (herd `riscv-defs.cat`): `let AQ = (Acq|AcqRel) and RL = (Rel|AcqRel)`, **`let RCsc = (Acq|Rel|AcqRel) & (EX|X)`**, `r5 =
[AQ];po;[M]`, `r6 = [M];po;[RL]`, `r7 = [RCsc];po;[RCsc]` — EVERY aq- or rl-annotated LR/SC/AMO is RCsc; the ISA prose agrees (RVWMO "Memory Model
Primitives": aq/rl on LR/SC/AMO are RCsc annotations; RCpc only under Ztso); Sail is silent (single-hart operational model, the annotations are
access-kind bits); Zifencei/PMAs silent.  The tree: `lbRcsc := lbAq && lbRl` (`AxGraphCat.lean:143`), `grcsc :163` — only a fused `LRmw` with both
bits qualifies (`lbRcscBits :245`), so `gppoCat6 :169` LACKS riscv.cat's `[W.rl];po;[R.aq]`, `[W.rl];po;[W.rl]` and rl-only-RMW pairs (`[R.aq];po;[_]`
is rule 5 anyway): the tree's cat model is WEAKER than riscv.cat there (sound for the theorem, but `rvwmoCatConsistentT` is then NOT riscv.cat, and
W12b had to ASSUME `grelAcqGmoC`); the header's "rule 7's RCpc part OMITTED" (`:37-43`) misnames those pairs — under riscv.cat they are RCsc.  *Why
reading the bits as RCsc is safe*: a hart's plain load carries `aq := akSync` of the Sail access kind (`WeakEvInst.lean:336`), set only by LR/AMO
kinds; `projLbl` (`WeakPromiseBridge.lean:537-547`) maps `LExLoad aq`/`LExStore rl`/`LRmw` to `LLoad aq`/`LStore rl`/`LRmw`; the only other `aq` is
the disk row's `DRead avail idx (aq)` (`VirtioProg.lean:74`; `WeakEvInst.lean:507`) — the model-artifact row (D51) where rule 5 already orders every
later access, so widening adds no disk-row edge.  Kernel census: the image's only annotated atomic is `acquire`'s `amoswap.w.aq` (no `.rl`, no
LR/SC; release = `fence rw,w; sw`, `Xv6/ProofRelease.lean`), so on KERNEL graphs the widened rule 7 adds NO edge (every new pair needs a `W.rl`);
the gap closed is [OWN.3]'s USER-row gap (§B).  *What changes*: **(1)** `lbRcsc := lbAq || lbRl` (`AxGraphCat.lean:143`; docstring: riscv.cat's
`(Acq|Rel|AcqRel) & (EX|X)` — the alphabet carries bits only on atomics); `lbRcscBits :245` → `lbRcscMem` (an RCsc label is a memory label), **DELETE `grcscGrelAcq :250` — FALSE under
the new bit (two `LStore true` in po are `grcsc` but not `grelAcq`) [R39.1]**, NEW `grelAcqGrcsc : grelAcq G e1 e2 → grcsc G e1 e2`; `gppoCat6Gppo
:264`'s sixth arm becomes the direct `Or.inr (Or.inr (Or.inr h))` once `gppo`'s arm is `grcsc`; header `:39` and the port-map line `:85`
(`grcsc_grel_acq`) rewritten; `lbRcsc`'s docstring `:142` ("both annotation bits") [R39.s2]; **(2)** RVWMO⁻'s rule-7 arm IN STEP: `gppo :237`'s `grelAcq` disjunct (`WeakRvwmoGraph.lean:227-
237`) becomes `grcsc`-wide (`grcsc` defined there, `AxGraphCat` re-exporting; `grelAcq` kept as a lemma-level name; [R40.s4] `lbRcsc` MOVES with it — today `AxGraphCat.lean:143`; `lbAq` `WeakAxiomatic.lean:184` and `lbRl` `WeakAxiomatic2.lean:434` are already below `Graph`, as `grelAcq :227-229` shows — plus a `Decidable (grcsc …)` instance beside `grelAcqDec` (`Dec.lean:244`) for `gppo`'s decidability; LANDED `WeakRvwmoGraph.lean:252/:256`), so `gppoCat6Gppo :257` and
`minusImpliesCat :274` keep their STATEMENTS — route (i); route (ii), leaving RVWMO⁻ alone and weakening `gppoCat6Gppo`, breaks `normalizeOfAcyclic
:617`'s `gppoCat6Gmo` conclusion unless `racyD` gains a rule-7 arm (W13 (K)/W5d-G G3 territory) — NOT taken; consumers of the arm re-proved:
`WeakRvwmoKill.lean:87` `gviolNoRelacq` → `gviolNoRcsc` (+ `:162,192,221`), `WeakRvwmoDec.lean:244` (decidability), `WeakRvwmoXchg.lean:896` (swap
invariance, label-based; NEW `lblTswapRcsc` beside `lblTswapRl :743` [R39.1]), `WeakRvwmoAcyc.lean:510-519` `rowsRelGppo` [R40.s7] (unfolds `grelAcq`, rewrites with
`lblRenAq`/`lblRenRl`, `WeakRvwmoNorm.lean:362-363` — with the arm `grcsc` it needs **`lblRenRcsc` BELOW `Acyc`: MOVE it from `CatLinHull.lean:94` to
`WeakRvwmoNorm.lean` beside `lblRenAq`/`lblRenRl` [R39.1]**, `Hull` imports `Acyc`'s descendants), `WeakRvwmoFloor.lean:431` `grelacqGmo` (via `grelAcqGrcsc`), the witnesses
`WeakRvwmoConfWit2.lean:324`/`WeakRvwmoAdm.lean:850` (`gppoGmo` by `decide`/`absurd`, recomputed), `AxLitmus.lean` (`grelAcqB :111`, its spec `:115`, `grcscB`'s cat use `:316` [R40.s7], `gppoCatNo2B
:314`; the litmus VERDICTS re-checked against herd), `AxGraphDec.lean:419-433` (`grcscB` text unchanged, spec proofs re-elaborated),
`AxProtLock3.lean:163` `lbRcscIsR` (FALSE for `LStore rl`) → `lbRcscIsMem`, `gppoCat6Gmem1 :167` re-cased, `AxSpinSpike.lean:749` (Bool twin, text
unchanged — a REBUILD, not an edit; the file is also in (F-dep)'s list via `cDw :658` [R39.2]), **`CatLinWit.lean:42` (`racyChk`, the Bool twin of
`racy` — `gacqB || grelAcqB || decide (∈ gdDeps)` — MUST widen to `grcscB` or `sbrfiAcyclic :124`'s `racyD`-acyclicity no longer matches `racyD`; its
spec `racyChkOf :44` re-proved) and `CatLinHull.lean:94-126` (`lblRenRcsc` leaves for `Norm`; the hull `grcsc` transport `:123-126` re-elaborates)
[R39.1]** — [R40.s5] the grep `lbRcsc|grcsc|grelAcq` over `Weak/` is 14 files; the EDITS are 17 (+ `Norm`, `ConfWit2`, `Adm` beyond the grep) + 1 rebuild; **(3)** `CatFloor.lean`: `grelAcqGmoC :60` DELETED, `finvCStep :329` … `cpolReadCatAD :823` take it from `gppoCat6Gmo` through
`grelAcqGrcsc` (the `h7` argument removed), `CatFloorWit.sbrfiRel7 :35` deleted, header `:29-34` rewritten (D35 CLOSED); **(4)** headers:
`AxGraphCat.lean:37-43` ("rule 7's RCpc part" → "rule 7 = riscv.cat's RCsc; omitted: rules 6, 8"), the rule-7 docstrings, `AxLitmus.lean:110`'s docstring ("Rule 7's RCpc
arm") and `gppoMinusB :119` (the Bool `gppo` twin — widen with `grelAcqB :115`) [R39.s2], `WeakRvwmoGraph.lean`'s header (the Rocq DEVIATION: Rocq's
RVWMO⁻ `gppo` has `grelAcq`, here `grcsc`-wide) [R39.1]; `AxDeps.lean` is NOT touched — it has NO rule-7/RCsc/RCpc mention (grep EMPTY), so the
(F-dep) ∩ D35-fix claim below rests on fact [R39.1]; **SEMANTIC CONSEQUENCE (state it in the header) [R39.1]**: `racy :197` carries `gppo` BY
NAME, so route (i) WIDENS `racyD :200` — the acyclicity premise of `normalizeOfAcyclic :607`, `hullRun`, the kill, W5d-G G3/G4 and (K)'s `racyDIO :=
racyD ∪ …` inherit the wider arm with NO text change ((K) is textually unaffected; the kill must exclude rule-7-wide cycles — EMPTY on xv6 graphs,
no `W.rl`); `linGppo` (`Topo.lean:333`) and `linwGppo` (`PreNorm2.lean:387`) prove `gppoGmo` of the retimed graph THROUGH `rowsRelGppo` and
`racy`'s `gppo` arm — automatic after the `lblRenRcsc` move; **(5) RE-AUDIT** [R40.s3]: all 13 registered roots REBUILD (the ten audited modules import `WeakRvwmoGraph`/`AxGraphCat`); M1/M2 (`srvwmoXv6M1Core`/`M1`/`M2`, `roots-weak.txt:28-30`) have CANDIDATE-level premises (`srvwmoConsistent c`, `SrvwmoXv6Witness.lean:599-607`, `PfRunUnpinned.lean:594-598`) — statement AND meaning unchanged, rebuild only; the registered LB roots (`allocpidOpen`, `AxSpinT2b.lean:255/436`, `AxSpinT2b2.lean:329/510`, premise
`HconsT : rvwmoCatConsistentT GT`; the 13 `Hcons := catTAd GT HconsT` files) keep their TEXT, their PREMISE STRENGTHENS (equal to riscv.cat; the
theorems cover exactly riscv.cat's graphs — FEWER than before): run `tools/ci/audit.sh --weak --build` and `lint.sh`; `baseline-weak.json` entries
EXPECTED UNCHANGED (axioms `propext`/`Classical.choice`/`Quot.sound`, certificates counted); the certificates `allocpidOpenCert`/`allocpidOpen2Cert`/
`…RaceCert`/`…PrefixCert` (concrete graphs: `amoswap.w.aq` acquires, plain releases — no `W.rl`, no new edge) re-elaborate by `decide`/`bv_decide`
— a changed verdict is a STOP (it would mean a concrete graph has an rl write); `roots-weak.txt:13-18`'s gloss gains "rule 7 = riscv.cat's RCsc
[OWN.54]"; §A(3)/(6) name the change (done here).  Parallel-safe vs (f2-ctx) ✓ (`Weak/` only), vs (F-dep): **∩ = {`WeakRvwmoAdm.lean`} [R39.2]** (D35-fix re-cases
`mp2PpoGmo :850`, `rcases h with hloc | hf | hacq | hrel`; (F-dep)'s sweep hits the positional `LDev kd ba bs` at `:696` and lists `Adm` among its
witness files — DISJOINT sites, whichever lands second rebases, S; `AxSpinSpike` is a rebuild on both sides, not an edit); `AxGraphCat`/
`WeakRvwmoGraph`/`Norm`/`Kill`/`Dec`/`Xchg`/`Acyc`/`Floor`/`CatFloor*`/`CatLinWit`/`CatLinHull`/`AxLitmus`/`AxGraphDec`/`AxProtLock3` ∩ (F-dep)'s owner
+ sweep files = ∅; `AxDeps` is NOT touched (no rule-7 mention; `gppoCatT :198` is `gppoCat6 ∨ gppo12T` by name, `:202`), vs W13 (K)+(R3′) (rebase S if both touch `Acyc` — `:512` is inside a lemma, not `racyD :200`), vs W11
(iv)c ✓ (`gppoCat6Gppo`'s statement is kept, so `RvwmoXv6ScaT`/`Topo` are untouched); **both D35-fix and (F-dep) (0) change `rvwmoCatConsistentT`'s
meaning — ONE combined `audit.sh --weak` after both merge**.  Acceptance: `lake build Weak` green; `grelAcqGmoC` gone; **`grcscGrelAcq` gone, `CatLinWit.sbrfi*` recomputed, the `racyD`-widening sentence in
`WeakRvwmoGraph`'s header [R39.1]**; `CatFloor`'s twins stated over `rvwmoCatAD` + `noPlainAqC` only; `gppoCat6Gppo`/`minusImpliesCat` statements unchanged; `sbrfi`/`isw`/`epc`/litmus verdicts unchanged (reported
per test); `audit.sh --weak` PASS, baseline unchanged; `#print axioms allocpidOpen` unchanged.
**STAGE 2 — THE SECOND LAUNCH SET (rev 42) — ALL DONE and MERGED 2026-10-13 [rev 44] ([OWN.55] approved the batch 11:16; (R3′) 11:39, W11 (iv)c 11:41, D35-fix 11:47, (K) 12:30, + (F-dep) 12:50; Rev 44 RESULTS; the record follows).**  Ground: first batch — W12 (+W12b) ✓, W13 (L) ✓, **W13 (F-dep) RELAUNCHED under (A1) [OWN.52] (w3, 2026-10-13;
its files `AxDeps`, `WeakEvInst`, `WeakPromise`, `AxSpinGate`, `PinBridge*`, `CatLinChain` [R39.2], the `LDev` sweep — `LDev` mentions `WeakEvInst` 52 / `WeakRvwmoFab` 31 /
`WeakRvwmoSupply` 27, positional sites per [R38.3]; [R39.2] handed to it as a LAUNCH ADDENDUM — applied at launch)**; the serial MachCSL lane BUSY with W8 (f2-ctx) RELAUNCH 3 (w2: `MachCSL/`, `Xv6/`,
`Weak/WeakAdequacy.lean`).  Per item — deps / files / parallel-safety / size / acceptance: **W13 (K)** (§C W13 (K); + (R3′) FIRST): deps MET —
(T) ✓, W12's statement commit ✓ (`racyD :200`/`normalizeOfAcyclic :607` have ONE owner again, W12 is DONE), W8-β′ ✓ (`lockWordDiscAt` for
`ioSegPinned`'s precondition (ii)), (L) ✓ (`gdiskRead14 :1153` is the disk-read-anchor disjunct (K) must keep).  Files: `WeakRvwmoAcyc.lean:200`
(`racyDIO := racyD ∪ ioResidue ∪ gmo|IO ∪` the `gdiskRead14` pairs), `WeakRvwmoTopo.lean:607` (`normalizeOfAcyclic` over `racyDIO`; I/O positions
and disk-read anchors kept, `gppoCat6Gmo` [R21.2] kept), `WeakRvwmoHull.lean:718` (`gdHull` keeps I/O events, filters `gfDev`),
`WeakRvwmoKillArms.lean:499` (`csChained` generalised), `WeakRvwmoGlue.lean` (`hullRun` → `cycleKillIO`), `GraphFabResidue.lean` (via (R3′)); the cat
side is already parameterised by the cross order (`CatLin.lean`, W12) — `cycleKillIOC` instantiates `X := gmo|IO`.  Parallel-safe vs (f2-ctx) ✓, vs
(F-dep) ✓ (no `LDev` site in `Acyc`/`Topo`/`Hull`/`Glue`/`KillArms`), vs D35-fix (S rebase at `Acyc` at most — `:512` `rowsRelGppo`, not `racyD
:200`; `racyDIO`'s MEANING widens with `gppo` under D35-fix, textually unaffected [R39.1]), vs W11 (iv)c ✓; **CONFLICTS with W5d-G
G3/G4** (`racyD`, `Acyc.lean:200`, `Hull.lean:714`, `Topo`) — G3/G4 follow (K)'s `racyDIO` statement commit.  Size M–L ≈ 0.8–1.2k (+ (R3′) S) — LANDED 708 lines as the NEW leaf `Weak/WeakRvwmoKillIO.lean` (deviation (1): `racyDIO` cannot live at `Acyc.lean:200`, its arms name `Gfexec`; `Acyc` gained the parametric `racyDX`, `Topo` `topoExistsX`/`normalizeOfAcyclicX`; `gdHull` UNCHANGED; Rev 44 RESULTS).
Acceptance: `cycleKillIO` through `hullRun`; `ioSegPinned` STATED with its two checks (§C W13 R5: (i) no same-row edge INTO a read outside gmo, (ii)
`lockWordDiscAt`); the normalised graph's `glinEidsIO` realises it (a corollary of `rule14LinearizationIO :1203`); build/`audit.sh --weak` unchanged.
**D35-fix** (above): deps MET (W12b ✓ supplies the premise to drop); files/size/acceptance above.  **W11 (iv)c `linCandDiskLat`** (§C W11 (iv)c):
deps MET ((L) ✓ — `linNwAAnc :208`, the disk-row read anchors `gisAnc :1141`; W-COH ✓, W5b′ ✓).  Files: `Weak/RvwmoXv6Sca.lean`/`RvwmoXv6ScaT.lean`
(new theorems beside `linCandScaTA :748`: on `linCandIO G` a disk-row load reads the LATEST write to its bytes at its trace position — from
`gdiskRead14` + `gloadValue`'s co-maximality + `linNwAAnc`); the pf consumer `candDiskLat` named in §B(10).  Parallel-safe vs everything in the
batch ✓.  Size S–M ≈ 0.2–0.4k.  Acceptance: `linCandDiskLat` proved on `linCandIO`; `linCandScaT`'s premise list unchanged.  **W5d-G G1–G5** (§C
W5d-G): gate W13 (M) ✓, W12 ✓ (the restated `Topo`/`Acyc`); **G1/G2/G5 MUST WAIT for (F-dep) increment (1)** (G1 `WeakRvwmoSupply.lean:277-352` +
`WeakRvwmoFab.lean` `Gfexec :799`/`gfexecConfIO :844` + the `WeakEvInst` lemma — all in the sweep; G5 `Supply.lean:743-883` likewise; G2
`WeakRvwmoConf.lean:57-66,147` is no longer (F-dep)'s file [R38.2] — 3 inert `LDev` mentions — but G2 is idle before G1); **G3/G4 MUST WAIT for
(K)'s `racyDIO` commit** (`Acyc.lean:200`, `Hull.lean:714`, `Topo.lean:120-129,594-607`): W5d-G is therefore the FIRST item of the THIRD batch (or
the (K) worker's continuation G3 → G4 → G1 → G2 → G5 once (F-dep) (1) has merged); L ≈ 1.8–2.2k + XL risk R1.  **W9a**: W12's `segPinC` ✓, but
(F-dep) (2)/(3) RE-PROVES the pin bridge (`pinSegPin`/`pinSegPin'`/`checkerTaintSubProv`, `PinBridge`/`PinBridge2`) that W9a's `PinBridge3` builds on
— after (F-dep).  **W10**: W12b's floor kit ✓, but its design is one line (§C W10, "unverified") and it should consume the D35-fixed `CatFloor` —
after D35-fix, sizing pass first.  **W13 (R)/(W)**: after (K) + (F-dep) (D26).  **W14**: after W13 (W) + W5d-G.  **W8 (f3-rest)**: after (f2-ctx).
**RECOMMENDED BATCH (≤ 3, parallel, pairwise file-disjoint up to the named S rebases): W13 (K) [(R3′) first] ∥ D35-fix ∥ W11 (iv)c** — graph lane,
three workers, beside (f2-ctx) RELAUNCH 3 and the (F-dep) RELAUNCH (w3; four graph workers in all — the owner's batch nod covers the three NEW items;
(F-dep) was approved by [OWN.48]); landing order **[R39.2][R39.s3]** — AS EXECUTED [R40.s1]: (R3′) first for (K) only (S; (K) consumes `ioResidue`); the "(R3′) lands BEFORE D35-fix launches" gate DROPPED as not load-bearing — `GraphFabResidue`/`Fab`/`Lin2`/`CatLin` are in NO registered root's import closure (computed over `import Weak.*` lines for `AxSpinT2b/T2b2/T2c/T2e3/T2q1-4`, `SrvwmoXv6Adequacy`, `SailCycleOrderCycle`), so (R3′)'s `audit.sh --weak` cannot change; D35-fix launched 11:14 in w1 beside (R3′) in w4; (iv)c any time (∩ everything = ∅); D35-fix AFTER (F-dep) increment (1) has
merged, or coordinated with the (F-dep) worker on `WeakRvwmoAdm.lean` (the one shared file, disjoint sites `:696`/`:850` — whichever lands second
rebases, S); `AxSpinSpike` rebuilds on both sides; ONE combined `audit.sh --weak` once D35-fix and (F-dep) (0) are both in.  Disjointness VERIFIED
[R39.2]: (K)/(R3′) ∩ (F-dep) = ∅ (`LDev` in none of `Acyc`/`Topo`/`Hull`/`Glue`/`KillArms`/`GraphFabResidue`/`Lin2`/`FabInd`); W11 (iv)c ∩ everything
= ∅; (f2-ctx) (w2: `MachCSL/`, `Xv6/`, `WeakAdequacy` — no `LDev`, no rule-7 name) ∩ the four graph items = ∅.  Usage: [OWN.51].
**WAITS / LAUNCHABLE (rev 41) [R38.5][OWN.48]–[OWN.51]**: **Stage 2 FIRST BATCH LAUNCHED 05:18 2026-10-13 [OWN.48]** — **W12 (+W12b) RUNNING** (w1,
`allocproc_S2_w1_prompt.txt`; brief unchanged — the coordinator sends [R38.6]'s course note), **W13 (L) RUNNING** (w4; brief unchanged), **W13 (F-dep)
STOPPED GREEN before any edit** (`~/dev/weak-orch/parked/PROGRESS-W13Fdep.md`; the tree is the launch tip): §C's clause was incomplete and WRONG on the
graph side — FIXED by [R38.1]–[R38.4]; **RELAUNCH when rev 41 is signed off**, under option (A) with the (A2) shape (the (F-dep) paragraph below);
**W8 (f2-ctx) RELAUNCH 2 RUNNING** (w2; Q-F2-PIPEHOP-2 RULED (a′-r) [OWN.49] and F-C = (i) [OWN.50] inside it; brief unchanged); **W8 (f3-rest)** after
it.  **Weekly cap [OWN.51]**: no new launch at seven_day ≥ 90%, workers wound down green at 95% — the (F-dep) relaunch is the only pending launch and
obeys it.  The rev-40 record follows.
**WAITS / LAUNCHABLE (rev 40)**: **M2 CLOSE — DONE 2026-10-13** (below; Stage 1b CLOSED, M1 + M2 DONE — INTERNAL, NOT published [OWN.2]);
**W8 (f2-ctx) RELAUNCH 2 — LAUNCHABLE** (serial MachCSL lane; S0 the `pipeLockNameStr` + hop-shape fix first [R36.2][R36.3]; launch authority
[OWN.37] + [OWN.41] as before; Q-F2-PIPEHOP-2 provisional, non-blocking); **W8 (f3-rest)** after it; **Stage 2** the FIRST LAUNCH SET below —
**W12 (+W12b) ∥ W13 (F-dep) ∥ W13 (L)** with the W12 → `AxDeps` rebuild-only edge named [R36.s3] — awaiting the owner's batch approval
([OWN.44] covered three other items; M2 CLOSE needed no nod — bookkeeping of items already RULED [OWN.3]/W5d/[OWN.42] [R36.s1]).  The rev-39
record follows.
**WAITS / LAUNCHABLE (rev 39)**: **M2 CLOSE — LAUNCHABLE NOW** (every dep MET: W-SCO (A) ✓ `sailCycleOrder_holds`, W-RSV ✓ with the W4
re-proof inside, `srvwmoXv6M2` STATED `SailCycleOrderCycle.lean:179`; the paragraph below); **W8 (f2-ctx) continuation RUNNING** (w2; the
RELAUNCH above with [R35.1]/[R35.2]; [OWN.46]/[OWN.47] confirm its options — rev 40: STOPPED GREEN, S1′ + S2-pre MERGED, RELAUNCH 2 [R36.1]); **W8 (f3-rest)** after it (gates W5d-G G7, W11 (ii)); **Stage 2**:
the FIRST LAUNCH SET below — recommended batch **W12 (+W12b) ∥ W13 (F-dep) ∥ W13 (L)**, then W5d-G G1–G5 + W13 (K); the owner's batch
approval is needed ([OWN.44] covered W-SCO (A), W13 (I), W-RSV only); W14 for W13 (W) + W5d-G; W11 (iv)c for W13 (L).
**M2 CLOSE — DONE and MERGED 2026-10-13 (rev 40).**  `Weak.srvwmoXv6M2` REGISTERED: `tools/ci/roots-weak.txt:25` (gloss as below; the header
comment `:9-12` says "M1 and M2"), `tools/audit/baseline-weak.json:163` — EXACTLY `Weak.srvwmoXv6M1`'s entry (`propext`/`Classical.choice`/
`Quot.sound`; the two `resv` opaques + `MachCSL.bootImageSealed`), `comment :12-13` added, the module list `:3` names BOTH
`Weak.SrvwmoXv6Adequacy` and `Weak.SailCycleOrderCycle` [R36.s1]; `audit.sh:49,56` UNCHANGED (the optional `srvwmoXv6M2Core` registration NOT
taken); headers: `PfRunUnpinned.lean:55` "M2 CLOSED: registered as `Weak.srvwmoXv6M2`", `SailCycleOrderCycle.lean:176-178` "registered (M2
CLOSE …)", `MachOfPf.lean:73-77` and `SrvwmoXv6Adequacy.lean:18-21` "proved: `sailCycleOrder_holds`, `SailCycleOrderCycle.lean:137`".  **Both
Stage 1 milestones M1 + M2 DONE (INTERNAL, NOT published [OWN.2]); Stage 1b CLOSED; what is left is Stage 2.**  Housekeeping left [R36.s5]:
`roots-weak.txt:23-24`'s gloss "THEOREM after W-SCO (A)" should add "(under `wbootFacts σ0`: `pma_regions = bootPMA`, `htif_tohost_base =
none`)" so the registered line states the platform premise — one line, any lane, with the next `tools/` touch.  *(The rev-39 launch paragraph
— the RECORD; its (4) quoted a `PfRunUnpinned.lean` header sentence that did not exist and cited `MachOfPf.lean:66-67` for `:73-77` [R36.s1].)*
**M2 CLOSE — the registration of M2 (S; NEW rev 39; `tools/` + four file headers, NO theorem change; LAUNCHABLE NOW, any lane).**  *Deps —
ALL MET*: W-SCO (A) ✓ (`sailCycleOrder_holds`), W-RSV ✓ (the W4 re-proof, D26), W5d M2 core ✓ (`srvwmoXv6M2Core`, `PfRunUnpinned.lean:652`);
the corollary **`Weak.srvwmoXv6M2`** is STATED at `Weak/SailCycleOrderCycle.lean:179` = `srvwmoXv6M2Core … sailCycleOrder_holds`, i.e. M2's
statement WITHOUT `hsco` (premises `srvwmoXv6M2Premises` + the four `g0` boot facts; conclusions = M1's + the replay invariant).  *What
remains*, on the W5 CLOSE-OUT's pattern (§C W5): (1) `tools/ci/roots-weak.txt` gains `Weak.srvwmoXv6M2` after `Weak.srvwmoXv6M1` with the gloss
"M2 (INTERNAL milestone, NOT published [OWN.2]): the UNPINNED fork-path composition — every M2-premised cut-form pf run (`pstepEv` itself,
`fcutEM2` at `itvOf`/`fiOf`, boot values) is realized by a MachCSL run from the machine off on which the closed xv6 theorems and
`allocprocAns` conclude, plus the replay invariant; premises `srvwmoXv6M2Premises` + `g0` boot facts only (SailCycleOrderCycle)"; the header
comment (`:1-10`) says "M1 and M2"; (2) `tools/audit/baseline-weak.json` gains `{ "name": "Weak.srvwmoXv6M2", "axioms": ["propext",
"Classical.choice", "Quot.sound"], "opaques": [the two `resv` opaques, "MachCSL.bootImageSealed"] }` — EXACTLY `Weak.srvwmoXv6M1`'s entry
[R28.1] (certificates counted, never listed; `platform_hooks` unchanged) plus a `comment` line (and fix the `comment`'s stale module list
"…,Weak.SrvwmoXv6Adequacy" → "…,Weak.SailCycleOrderCycle"); (3) `audit.sh:49,56` UNCHANGED — `Weak.SailCycleOrderCycle` is already in both
lists (the theorem lives there); OPTIONAL, worker's choice said in the report: register `Weak.srvwmoXv6M2Core` too (symmetric with M1; adds
`Weak.PfRunUnpinned` to both `audit.sh` lists) — the milestone is the corollary; (4) headers: `PfRunUnpinned.lean` ("NOT registered — M2
closes after W-RSV and [R32.1]" → "M2 CLOSED: registered as `Weak.srvwmoXv6M2`"), `SailCycleOrderCycle.lean:176-178` ("NOT registered (M2
CLOSE registers it)" → registered), `SrvwmoXv6Adequacy.lean:18-20,81-89` and `MachOfPf.lean:66-67` ("W-SCO (A) proves it" → "proved:
`sailCycleOrder_holds`, `SailCycleOrderCycle.lean:137`"); (5) status counting: M2 counts from this item on ([R21.4]); the §A `∧
sailCycleOrder` conjunct is GONE at M1, M2 and the published statement.  *Files*: `tools/ci/roots-weak.txt`, `tools/audit/baseline-weak.json`
(+ `tools/ci/audit.sh` only with the optional core), the four headers.  *Lane / parallel-safety*: any lane; NO shared file with W8 (f2-ctx)
(w2: `MachCSL/`, `Xv6/`, `Weak/WeakAdequacy.lean`) nor with any Stage 2 item; a `Weak/` rebuild only.  *Size*: S (≈ 20–40 lines, hours).
*Acceptance*: `lake build Weak` (or `audit.sh --weak --build`), `tools/ci/lint.sh` (roots ↔ baseline agreement), `audit.sh --weak` green with
`Weak.srvwmoXv6M2` registered and its entry EXACTLY `Weak.srvwmoXv6M1`'s; `#print axioms srvwmoXv6M2` = `propext`/`Classical.choice`/
`Quot.sound` (+ counted certificates), no `sorry`, no new opaque; every other registered root unchanged in statement; the status line quotes
`audit.json`'s `bv_decide_certificates` for `Weak.srvwmoXv6M2`.  Non-vacuity: `srvwmoXv6M2Satisfiable :758` (QUIESCENT, D22/D44 — W14
certifies at `allocproc`).  **Stage 1b then CLOSES**; what is left is Stage 2.
**STAGE 2 — THE FIRST LAUNCH SET (rev 39).**  Ground: M1 ✓ (`srvwmoXv6M1`), M2 ✓ at CLOSE, W13 (E)/(T)/(M)/(I) ✓, W-DISK ✓, W-RSV ✓, W-SCO ✓,
W8-β′ ✓ (root (r2) at `lockWordDiscAt ∧ cpuStaticAt`); the serial MachCSL lane is BUSY with W8 (f2-ctx) (w2: `MachCSL/`, `Xv6/`,
`Weak/WeakAdequacy.lean` — NO Stage 2 item touches these; each of its 3–4 cone merges REBUILDS `Weak/`, rebuild only, so graph workers time
their green increments around them).  D26's order (§D): `{W12 ∥ W12b ∥ W5d-G G1–G5 ∥ W13 (L)(K)(F-dep)} → W13 (R)(W) → W9a/W10 → W11; W14
after W13 (W) + W5d-G`; the FILE map below refines it (contention, not deps).  Per item — deps / files / parallel-safety / size / acceptance:
**W12** (§C W12; **DONE rev 42**): deps MET (D25 (a) [OWN.5]; the spike `Weak/CatOfMinusSpike.lean` MERGED [OWN.10]: `rvwmoCatAD :31`, `segPinC :163`; W13 (T) ✓
for the I/O arms; W13 (K)'s `racyDIO` NOT needed — the cat arms are written ONCE, parameterised by the cross order).  Files: NEW
`Weak/CatLin*.lean` + S statement edits at `WeakRvwmoTopo.lean` (`topoLinearizes :436`, `topoExists :583`, `normalizeOfAcyclic :598`),
`WeakRvwmoDec.lean:378` (`normalizeOfAcyclic'`), `WeakRvwmoSupply.lean:954` (`topoSupply`), `WeakRvwmoGlue.lean:282` (`hullRun`),
`WeakRvwmoFab.lean:909` (`topoLinearizesF`), `WeakRvwmoAcyc.lean:200` (`racyD`, `racyDMem`); `Lin*`/`Norm`/`PreNorm` untouched.  Parallel-safe
vs (f2-ctx) ✓, vs W13 (L) ✓ (no shared file), vs W13 (F-dep) — `Supply`/`Fab` shared at different sites (rebase S) **and W12 DEPENDS on
`AxDeps` (`CatOfMinusSpike.lean:20 import Weak.AxDeps`; `catADOfCatT :37` over `rvwmoCatConsistentT`/`gtAd`), which (F-dep) EDITS — rebuild/
re-elaboration after each (F-dep) merge, not a file conflict [R36.s3] — **[R38.6] no longer exact: (F-dep) increment (0) CHANGES `gtdepsWf`,
`forgetDeps`, `gtAd`, `rvwmoCatConsistentT` (course note for the RUNNING worker, sent by the coordinator): (i) `catADOfCatT :37`'s STATEMENT survives;
its proof survives under (A2) and needs ONE line under (A1) (`gppo12` monotonicity over `gtAd ⊆ gtAdFull`, lemma exported by (F-dep)); (ii) W12 (5)'s
`gdexecQconfT` is stated as `rowDepsT em ⊆ GT.gtDeps` against the GENERALIZED `gtdepsWf` — NO RAM-endpoint filter (that is D50 (a), contrary to
[OWN.17]) — and NOT before increment (0) has merged (until then `rvwmoCatConsistentT ∧ gdexecQconfT` is unsatisfiable on I/O rows); (iii) `rvwmoCoreD`
over the UNTAGGED `gdepsWf` is unaffected (option A leaves the untagged world alone); (iv) new W12 lemmas take `lbIsR`/`lbIsW` of a tagged edge's
endpoints from `forget GT`/`gtAd`'s `gdepsWf`, never from `gtdepsWf`; (v) rebase ONCE after increment (1)'s `Supply`/`Fab` sweep (`LDev` sites,
disjoint from `topoSupply :954`/`topoLinearizesF :909`)**; NOT vs W5d-G G3/G4 and
W13 (K) (the same `Topo`/`Acyc`/`Glue`/`Hull` statements) — those follow W12's FIRST commit (the statement edits over `rvwmoCoreD`, S, landing
first).  Size M–L ≈ 1.2–1.8k.  Acceptance: build/lint/`audit.sh --weak` unchanged (no new axiom/opaque); the forwarding witness (SB+rfi-pos)
through `rvwmoCatAD`, cat-consistent and NOT RVWMO⁻ [R6.s2]; `hullCatAD`; `xv6RvwmoSafeModuloT` STATED (its premises are W11's — not
registered); the restated `normalizeOfAcyclic` concludes `gppoCat6Gmo GD'.gdG` [R21.2].  **W12b** (§C W12b; **DONE rev 42**): deps = W12's `rvwmoCatAD` (the
spike's exists — a start against it re-points once W12 (1)–(2) land); files NEW `Weak/CatFloor*.lean` + `Floor`/`Cert3` restatements;
conflicts with W5d-G G5 (`Floor`).  Size M–L ≈ 0.5–1k.  Acceptance: the `finvStep` coh-hook forwarding read certified [R7.s5].  RECOMMENDED as
the W12 worker's second increment (one lane, `Floor` single-writer).  **W13 (F-dep) — RELAUNCH (rev 41) [R38.5]** (§C W13 (F-dep); STOPPED GREEN before any edit, `PROGRESS-W13Fdep.md`): deps MET ((E) ✓;
D50 (b) [OWN.17]; census [W13c]: rule-9 graph hits NONE); proceeds under **option (A)** in the **(A1) shape — RULED [OWN.52], rev 42: `gtAdFull`, `gppoCatT` over it, the two
monotonicity lines (`catTAd`; `catADOfCatT` in `Weak/CatLin.lean:54` AND `CatOfMinusSpike.lean:37` — both (F-dep)'s now, W12 is DONE), `AxScCat.scPpo
:168`'s rule-12 case — INSIDE increment (0), no (A2) interim** (the (0e) text is the spec).  **Increments, in this order** — **(1)** the `LDev` payload sweep ALONE: the arity change `Wlabel.LDev kind
base vs` → `+ asrc` (rd) / `+ asrc vsrc` (wr) at `WeakPromise.lean:89`, ≈ 180 positional sites in 35 files [R38.3] (`WeakEvInst` 35, `WeakRvwmoSupply`
18, `WeakEvCapstone` 16, `WeakRvwmoFab` 12, `WeakRvwmoCert3b` 10, `AxOpsem` 10, `WeakEvPf`/`MachOfPf`/`AxRunGV2` 7, `WeakPromiseBridge` 6, `PfStepTso` 5,
`WeakRvwmoWalkb`/`AxPair`/`AxFetch1` 4, `WeakAxRealize` 3, …; `LDev ..` wildcards need nothing) + the per-row fill in `pnodeStep` (`LDev .rd`
`WeakEvInst.lean:319` with `asrc := depsAsrc (depsOfIb ib.ibBits)` as the `LExLoad` arm `:345-346`, NOT the plain `LLoad` arm `:336`; `LDev .wr` `:355`
as the `LStore` arm) — mechanical, ONE build, so W12 (`Supply.lean:954`, `Fab.lean:909`) and (L) (`FabInd`) rebase on it ONCE; **(0)** the model text in
the (A2) shape (§C (0a)–(0d): `gtdepsWf` generalized, `forgetDeps`/`gtAd` source-filtered, `gtdepsRdOk` widened, `AxSpinGate.gsrcT` filtered +
`gsrcTSrc`/`gsrcTSrcPo` restated, the Bool/SC tier, the `AxDeps` header deviation, the computed-satisfiability smoke test); **(2)/(3)** `dstepT` arms
ONLY (`dstep` inert, deviation in the `AxDeps` header), `dstepTState` as the erasure/inclusion lemma, `rowDepsSubT`/`rowDepsTSub`/`rowDepsTAddr`
restated, the pin bridge `pinSegPin`/`pinSegPin'`/`checkerTaintSubProv` re-proved; **(0e)** RULED (A1) [OWN.52], folded into (0) — (A1): `gtAdFull`, `gppoCatT` re-pointed,
two monotonicity lines (`catTAd`; `catADOfCatT` in W12's file after W12's statement commit, or by W12) and `AxScCat.scPpo`'s rule-12 case; (A2):
nothing.  **NEVER merge (1)+(2) without (0)** — that is exactly the Gap-1 vacuity for W12's `gdexecQconfT`.  Files: owners `Weak/AxDeps.lean`,
`Weak/WeakEvInst.lean`, `Weak/WeakPromise.lean`, `Weak/AxSpinGate.lean` ((0c) only — the registered roots' TEXT must not change; audit line "registered
roots unchanged in statement") + the sweep list + `PinBridge`/`PinBridge2`, **`Weak/CatLinChain.lean` [R39.2]** (`gdexecQconfTForget :331-338` proves `forget GT`
membership from `elemOfForgetDeps` with the `gisW` TARGET fact only; after (0b) `forgetDeps :178` filters the SOURCE too, so the proof takes
`hartConfRowDepsWf`'s source conjunct `lbIsR`, `WeakRvwmoConf.lean:837` — S; no other batch item touches the file), the witness files (`ConfWit2`,
`CycWit`, `Adm` — `LDev`-free rows, trivial; **`Adm` is ALSO D35-fix's file (`mp2PpoGmo :850`), disjoint from the sweep site `:696` — rebase S by
whichever lands second [R39.2]**),
the retired `Ax*` tier (`AxGate`, `AxScRun`, `AxScCat`, `AxFetch5`, `AxSpinSpike.cDw`); `Weak/WeakRvwmoConf.lean` is NOT an owner file [R38.2].
Parallel-safe vs (f2-ctx) ✓, vs W12 (rebase S at `Supply`/`Fab`, disjoint sites; W12 rebuilds after each (F-dep) merge [R38.6]), vs W13 (L)
(`FabInd`/`Supply`, rebase S); vs W5d-G G1/G2 only the `WeakEvInst` lemma remains (the `WeakRvwmoConf.lean:57-66,147` half of that conflict
disappears [R38.2]) — G1/G2 rebase on it.  Size **M–L ≈ 1k, three increments** [R38.3].  Acceptance: build green per increment; **`gtdepsWfB` over
`rowDepsT` of W13-wit's row (or `tw` + one `LDev` item) evaluates `true` — a PERMANENT smoke test beside `catTConsistentBSound` [R38.1]**; `LIo rd`'s
`asrc` as the `LExLoad` arm, `LIo wr`'s as `LStore`'s [R11.4]; the row lemmas and the pin bridge re-proved; `catTAd`/`catTForgetAxioms`/`catADOfCatT`
statements UNCHANGED; registered roots unchanged in statement; the `Ax*` tier builds; `gdexecQconfT`'s trusted-surface text covers I/O items (header,
§A(6)); no `gen_weak_pins.py` change.  Q-FDEP RULED (A1) [OWN.52] (rev 42).  Relaunch-brief corrections
[R38.s2] (not plan facts): W13-wit's `ld a5,0(a0)` → `sb zero,1(a5)` is an ADDRESS edge (`dtagW DTaddr = false`, target clause `gmem`) — representable
in the tagged model TODAY, dying only on the untagged route; the tagged vacuity comes from `DTdata`/`DTctrl`/`DTr13` → I/O store and from every
I/O-load-sourced edge (first instance: the first `printk`'s THR store `0x800009fa`); `uartstart` does not exist in this image (census `:314`) — the data
example is `uartwrite`'s THR `0x80000988`.  **W13 (L)** (§C W13; **DONE rev 42**): deps MET ((T) ✓; (I) ✓ `gfexecConfIO`/`gfDev`; G3-Q (a″)
[OWN.17]).  Files: `Weak/WeakRvwmoLin2.lean` (`ptraceRel :130` → `ptraceRelIO`, `gtraceLinearizationMin :634`, `fconfSupply' :1006`),
`Weak/WeakRvwmoLin.lean` (`gnxw :440` → `gnxa`, `glinEids`/`linCand :471`), `Weak/WeakRvwmoFabInd.lean` (`trDevOrdered :464`, discharged
from `ptraceExtIO`), `RvwmoXv6Sca*.lean` (only `linGmoEmitBefore :144`/`linLogEmitted :172` re-proved).  Parallel-safe vs (f2-ctx) ✓, vs W12
✓, vs (F-dep) (rebase S); NOT vs W5d-G G5 (`Lin`).  Size M–L (+ M for the disk-row read anchors [W2s]).  Acceptance: `ptraceExtIO` (fab order =
the trace's I/O order = gmo|IO by (R3)); `fconfSupply'`'s `before L` premise and FabInd's `trDevOrdered` DISCHARGED; `linCandScaT` re-proved
on the anchors; unblocks W11 (iv)c `linCandDiskLat`.  **W5d-G G1–G5** (§C W5d-G): gate MET (W13 (M) ✓; (I)'s `Fab`/`Supply` text landed; G0
`GraphFetchSpike.lean` 344 merged [OWN.10]) — this paragraph + §C W5d-G is its brief base; owner's batch approval needed.  Files: G1
`WeakRvwmoSupply.lean:277-352`, `WeakRvwmoFab.lean` at the `Gfexec` bundle (`structure Gfexec :793`, `gfexecConfIO :844` — by name; `:516` is a
theorem body [R36.s3]), `WeakEvInst`/`WeakEvLang` (lemma), `GraphFetchSpike` (the slot content
`emZifencei` [R32.3]); G2 `WeakRvwmoConf.lean:57-66,147`; G3 `WeakRvwmoGraph.lean:613`, `Acyc.lean:200`, `Glue.lean:205-223`,
`Hull.lean:714`, `Topo.lean:120-129,594-607` (~31 literal sites); G4 `Topo` (L ≈ 600); G5 `Lin`, `Floor`, `Supply.lean:743-883`.
Parallel-safe vs (f2-ctx) ✓; CONFLICTS with W12 (`Topo`/`Acyc`/`Glue`/`Hull`), (F-dep) (`WeakEvInst`/`Conf`), (L) (`Lin`), W12b (`Floor`),
(K) (`racyD`) — the most file-contended item: launch when W12's first commit and (F-dep) have merged, G5 after (L).  Size L ≈ 1.8–2.2k (+ XL
risk R1).  Acceptance: `emFenceI` + `emFenceISound`, the `emZifencei` content in `xv6ConfS`/`gdexecQconf` at the real slot [OWN.26], the six
G0 carry-overs, `Gdexec.gdFetch` [OWN.18], `retimeZifencei`, `supplyOfQconf` producing the M2 cut clause; hull closure per §B(4)(iii) R1 (a);
build/`audit.sh --weak` unchanged.  **W13 (K)**: deps (T) ✓, but it REDEFINES the racy relation (`racyDIO` over `racyD :200`,
`normalizeOfAcyclic`, `gdHull :718`, `csChained` `KillArms.lean:499`) — serialize AFTER W12's statement commit (one `racyD` owner) and with
G3; size M–L; acceptance `cycleKillIO` through `hullRun`, `ioSegPinned` with its two checks (§C W13 R5).  NOT in the first batch.  **W13
(R)**, **(W)**: after (L)(K)(F-dep) (D26; (R) re-threads 8.6k/14 files onto `gfexecConfIO`; (W) states `xv6ConfS` over (F-dep)'s
`gdexecQconfT` text + W13-wit) — NOT NOW.  **W14**: deps W13 (W) + W5d-G — NOT NOW.  **W9a**: targets W12's `segPinC` — after W12.  **W10**:
on W12b's floor kit — after W12b.  **W11**: W8's export ((f2-ctx) RELAUNCH 2, rev 40) + W12 + W13 (K) — NOT NOW; (iv)c after (L).  **W8 (f3-rest)**:
after (f2-ctx) (serial lane).  **RECOMMENDED BATCH (≤ 3, parallel, pairwise file-disjoint up to the named S rebases): W12 (then W12b, same
worker) ∥ W13 (F-dep) ∥ W13 (L)** — graph lane, three workers, no owner gate beyond the batch approval (GIVEN [OWN.48], rev 41 — LAUNCHED); landing order inside the batch: W12's
statement edits FIRST (S), then any order; **W5d-G G1–G5 + W13 (K) are the SECOND batch** (G3/G4/(K) on W12's restated `Topo`/`Acyc`; G1/G2
on (F-dep); G5 on (L)).  **M2 CLOSE (S) launches beside them at once** (not counted among the three) — **DONE rev 40**.  The rev-31 record follows.
**Rev 31 RESULTS (2026-10-12) and the rev-31 launch set.**  DONE and MERGED: **W4 F9** (`Weak/MachOfPfDisk.lean` NEW 1290 lines +
`Weak/MachOfPf.lean` 1659 → 2979 — `simDisk :2603` proves the disk rows; `SimRel :342` lost its `DR` parameter, its device clause is
`R-dev` (`diskSide :331` / `MachOfPfDisk.devAgree :429` / `VRel.holds :349`: every device but the disk EQUAL, the disk EQUAL (all
fields) off the OUT capture segment and `(pre₁ pf).1` on it in its three task positions zombie / free / held) and EVERY consumer
of the old clause is re-proved — the `simNode` posts, the MMIO arms (`diskSideRead/Write :812,820`), `simDev` (`diskSideFdev :828`),
`simWire` [R21.3 (c)]; `machRunOfPfRun :2854` takes NO disk hypothesis; `Hyps :658` = `tso`/`safe`/`cut`/`fi`; deviations (file
headers): `cacheWf :105` (distinct keys, each entry ≤ one sector — holds at EVERY state and survives a pre-check abort) replaces
the plan's "`cache = []` outside a capture → gate window" [R19.1 (c)], `devrt`/`TaskId` are NOT tracked (the idx write's `DRet DIdle`
is 1 → 0, a refused POP 1 → 1, the root's restart folded into the next START = 1 → 3; the `13+k` thread is the task's position in
the pool), the interim `Hyps.noWrap` discharged inside F9 via [OWN.40] (`§B(11) (x)`); axioms `propext`/`Classical.choice`/
`Quot.sound`; `MachOfPf.lean` header deviation 3 now cites [OWN.35]), **W5 CORE adapted = M1's CORE** (`Weak/SrvwmoXv6Adequacy.lean`
318 lines, `Weak.lean:634`: `srvwmoXv6M1Core :276` — hypotheses = `srvwmoXv6M1Premises` + the four `g0` boot facts + `sailCycleOrder
:113`; `m1Hyps :203` discharges `tso` by `pfStepTsoProposed`, `safe` by `xv6FsAdequacy_closed`'s `Reducible`, `cut` by `cutOfPristine`
from `winOfText :187` (W3's root through `textWin_get`), `fi` by `fiOfSco :163` from the one-fold lemma `fiArmLastCyc :135`; the
conclusions `xv6Concl :252` + `allocprocAns :230`; `SimRel` used only through `MRun`/`pfObsOf`/`cutOfPristine`'s three fields and
`SimRel.pow`, its device clause never unfolded — the rev-25 acceptance met; axioms = `xv6FsAdequacy_closed`'s cone + 4 NI/union/text
`bv_decide` certificates), the **import-hygiene fix** (`ExecSC4.lean:62-70` imports `MachCSL.UTlb` so `bv_decide`'s
`enumToBitVec` auxiliaries are generated once; `Weak.lean` imports `SrvwmoXv6Adequacy`; build/lint/`--weak` audit green), **R-ctx**
(read-only, `notes/W8-Rctx.md`: §C W8 (4)).  **M1: PROVED, NOT CLOSED** — [R21.4]/§B(12) make REGISTRATION the close, and
`roots-weak.txt`/`baseline-weak.json`/`XV6_AUDIT_MODULES` do not name it yet; the **W5 CLOSE-OUT** (§C W5, S) does.  **IN FLIGHT:
W8-β′** (serial MachCSL; launched 2026-10-12 10:26 on the rev-30 brief below + [R27.s1]–[R27.s3] at launch — **UNCHANGED here**).
**MAY LAUNCH NOW (rev 31; no owner gate)**: **W5 CLOSE-OUT** (S; `tools/` + two file headers, no theorem change; §C W5) ∥ **W-SCO**
(M–L, `Weak/` lane, NEW file; the `candKfetch`-restricted `sailCycleOrderK` + `fiOfScoK` + the corollary `srvwmoXv6M1` without the
premise, `srvwmoXv6M1Core` untouched by W-SCO [R30.s4]; §C W-SCO) ∥ **W13 (I)** (M on the fabric side, graph lane; gate MET since rev 28 — the first
item of the Stage-2 graph lane, D26) ∥ **W5d** (L, `Weak/` lane; dep W5 ✓ — `Weak/PfRunUnpinned.lean`, the cut-form replay with
`itvOf`; §C W5d) — four lanes, one worker each; **[R28.3] shared files, in LANDING ORDER** (W5d's restated M1 is a new theorem
`srvwmoXv6M2Core` in its own file): the **W5 CLOSE-OUT lands FIRST** (S, hours) and its deviation-(4) wording already anticipates
W-SCO ("the named premise `sailCycleOrder` [OWN.35]; `sailCycleOrderK_holds` (W-SCO) proves it for kernel text"), so W-SCO does
NOT touch `PfStepTsoView.lean`'s header; **W-SCO's registration** (`roots-weak.txt`/`baseline-weak.json`/`audit.sh:44,51`; entry =
the core's with the per-word lemma's certificates counted) is its CLOSE step, rebased on the merged CLOSE-OUT; **W-SCO's `Hyps.fi`
widening [R28.2]** is its FIRST commit (`MachOfPf.lean` + ONE line of `SrvwmoXv6Adequacy.lean:213`); **[R29.1] W5d's `fcutT`
(+ per-index `fcutE` [R30.1], both `True` at M1) parameter threading (§B(4)(iii); S–M, ≈ 150–300 lines of signatures and trivial instances) is W5d's FIRST commit**, rebased on
the widening, landing BEFORE W-SCO states `sailCycleOrderK`/`srvwmoXv6M1` (W-SCO then states them over the parametrised
`pfRunST` at M1's trivial instance; if W5d's commit is late, W-SCO states them over the current type and W5d adapts — S either
way); the W5 CLOSE-OUT is unaffected (registration by NAME; M1's statement TEXT changes, its entry does not).  **WAITS**: **W-RSV** for W8-β′'s MERGE **[OWN.41][R28.5]** (Q-RSV-order RULED
(b): W8-β′ → W-RSV → W8 (f2-ctx); M1 ✓, D26; §C W-RSV "Launch (rev 32)"); **W8 (f2-ctx)** for W-RSV (rebases on its `resvFragAny`
thread at `ctxTok`, `Ctx.lean:298-299`; R-ctx PASSED — no (f1) part; brief = §C W8 (4)/(6)/Acceptance as re-sized by
[OWN.38][OWN.39]); **M2** for W5d + W-RSV's W4 re-proof (inside W-RSV, [R28.5]); W5d-G G1–G5 for W13 (I)'s `Fab`/`Supply` text; W14 for
W13 (I)/(W) + W5d-G; W11 (iv)c for W13 (L).
**MAY LAUNCH NOW (rev 28; no owner gate) — RECORD of the rev-28 set (W4 F9, R-ctx, W5 CORE DONE; W8-β′'s brief is the RUNNING
worker's text)**: **W4 F9** (disk rows, L ≈ 0.8–1.5k; UNBLOCKED by W-DISK — loosens `SimRel`'s
device clause to `R-dev` = full `dvirtio` equality off the OUT capture segment, `(preCaptureHead h r).1` on it, `cache = []`
outside capture → gate; re-proves EVERY `SimRel.dev` consumer [R21.3 (c)]; §C W4) ∥ **W8-β′** (M–L ≈ 1.3–2.3k [R26.2], SERIAL MachCSL —
the first item of the lane since W-DMA0: a MachCSL "reserved region" (the state interpretation holds half of each reserved
byte's points-to, so a generic rule's own-1 cell cannot name one) for `cpus[h]` and the lock layer's own words.  **[R26.2]
`reg`'s HOME and the reserving STEP** (rev 29 named neither; the interpretation is opened only by `swp` step rules, and
`newlock_written`/`lock_pay_born` are `|={E}=>`/`|==>` lemmas, `Lock.lean:682-687,488` — `lkFresh :727` is what they CONSUME
[R26.s6]): (a) a new era ghost `rsvName : GName` in `EraGS`/`MachGS` (`Resources.lean:105-135,420-438`, the `MachGS.era` tuple
`:470-477`, `MachGS.ofEra` `Power.lean:771-776`; the only existing lock ghost `lockSetName` is a per-hart set of HELD lock NAMES,
`Ctx.lean:96-101`), an auth map `PAddr ↦ RsvKind` (`cpu h` / `lockw` / `lockcpu`, fragments persistent) allocated with the era's
other ghosts at the `PowerOn` mint (the fourteen-field tuple, `Power.lean:558-653`, `PowerText.lean:290`); `memModelAt E σ`
(`Resources.lean:951-956`) gains `(E.rsvName ↪●MAP reg) ∗ ([∗map] a ↦ _ ∈ reg, ∃ H, pointsTo (G := E.mem) a (DFrac.own ½) H) ∗
⌜staticIn reg ∧ reservedOk σ reg⌝` (an equivalent camera is the worker's call, recorded in the file header); (b) **[R26.2-alt]
the reserving step is the `PowerOn` mint itself, for a client-supplied STATIC list `KernelRsv.static`** (a MachCSL class the
`Xv6/` client instantiates — the `KernelMap.static` pattern, `KMap.lean:120`, `Xv6/KernelMap.lean:156`, allocated and persisted
as the kernel mapping is, `Power.lean:558,565`): `cpus[h]`'s three cells (`cpuCells`, `KCtx.lean:556-560`) and every image
spinlock's two words incl. the sleeplocks' inner locks; `powerBootRes` (`Power.lean:336`) hands the boot client HALVES of those
words (the `powerBootResT` split shape, `PowerText.lean:80,113`, with NO `HtextRec`-style trace hook); registered from `t = 0`
(matching `cpuStaticAt`'s `e.t ≠ 0`), no time index, no de-registration.  Why not R26's "at `initlock`'s stores and at the boot
carve": the carve (`BootCarveHart.lean:84`) is a pure ownership split, not a step; and `riscvPowerAdequacy`'s final hook is
`… ⊢ ◇ ⌜phi g' h⌝` (`Adequacy.lean:359-366`: no fancy update, no invariant), so a registration performed by a mid-run step is a
GHOST fact the extraction (ii) can use only if membership is PURE in `memModelAt` — true of a static list (`⌜staticIn reg⌝`),
false of a pipe lock born at `pipealloc`.  Hence pipe locks are W8 (f2-ctx)'s (dynamic registration at `wp_s_sw_mint`/
`wp_s_sd_mint`, `WpSmodeMint.lean:126,40` — `initlock`'s two stores ALREADY use these dedicated rules, `ProofInitlock.lean:56,68`;
de-registration at the destroying free store `wp_s_sw_zero_release_cancel`, `WpLock.lean:2028`; `reservedOk` indexed `tReg ≤ t <
tEnd`, the reclaimed interval not exported; the hook problem under *Unverified points*, §C W8).  Consequences: `cpuCells`' three
`own 1` cells become halves (≈ 11 cpu-cell rule uses re-proved, `WpSmodeRules.lean:966,1076,1159`, `WpSmodeProc.lean:107`);
`wordCell` (`WordHist.lean:293`; `histBytes` already takes a fraction map), hence `lockBody :590-597`, `newlock_written`,
`lkFresh`, `wp_initlock_body` (`SpecInitlock.lean:36`) and the `WpLock.lean` rules become fraction-parametric (own 1 for an
unregistered pipe lock, half + fragment for a static one) — the "`lkFresh`'s modality changes" case already priced at ≤ 30 `Xv6/`
files.  **[R25.2] THREE Lean deliverables**: (i) the MachCSL conjunct `⌜staticIn reg ∧ reservedOk σ reg⌝` beside `⌜mmOk σ⌝` in
`memModelAt` — per registered region every entry with `e.t ≠ 0` is by the region's structural author (`cpu h`: `hartAgent h`; a
lock's words: the `lockWordAt`/`lkCpuAt` shape, `Lock.lean:53-56,18-22`), re-established by the dedicated rules ONLY; (ii) the
`Xv6/` extraction `powerInterp_accessDiscβ : powerInterp g ⊢ ⌜g.pow = true → lockWordDiscAt g.m ∧ cpuStaticAt g.m⌝` on
**`powerInterp_mmOk`'s pattern (`MachCSL/Adequacy.lean:481`; `TextPristine.lean:120` calls it the parent) [R26.s1]** — NOT
`powerInterp_textPristine`'s, which needs `eraRegistered` + the persisted window —, where **[R26.1]** `lockWordDiscAt σ := ∀ b t,
xv6LockWord σ b t → ⟨the `lockWordAt`/`lkCpuAt` discipline on `b`'s and `b+16`'s histories up to `t`⟩` is obtained from
`reservedOk g.m reg` through the `Xv6/`-side **registration lemma `xv6LockWord σ b t → b ∈ reg`** (every σ-visible lock word IS
registered) — NOT rev 29's converse "registry ⊆ `xv6LockWord σ`", FALSE at reachable states (`pipealloc` runs `initlock(&pi->lock)`
BEFORE `(*f0)->pipe = pi`, `Xv6/SpecPipealloc.lean:10-12`; `fileclose` unlinks the end BEFORE `pipeclose` reclaims,
`SpecFileclose.lean:10-12`) and anyway W8 (f2-ctx)/W11's concern via `custAt .lockw`, if needed at all; in β′ the lemma is the
decidable list-membership fact for xv6's `KernelRsv.static` instance, and the PROVISIONAL `lockWordDiscAt` quantifies over the
STATIC lock words — every lock W13 (K) reads on the `allocproc` trace (`proc[j].lock`, `pid_lock`, `wait_lock`) is one; pipe locks
join at (f2-ctx); (iii) **the (r2) sibling root `xv6DiscAdequacy_closed` NOW**, with `xv6AccessDisc` provisionally `:= lockWordDiscAt ∧
cpuStaticAt` (registered in `roots.txt`/`baseline.json`/`tools/tcb/expected.json` per §B(12); W8 (f2-ctx) only STRENGTHENS
the conjunction) — so W13 (K)'s `lk->cpu` precondition is unblocked at the ROOT level, not just as a statement; files [R26.2 (d)]:
MachCSL `Resources`, `Power` (mint, `MachGS.ofEra`, `powerBootRes`), `PowerText` (the W3 twin's tuple, `powerBootResT`), `WordHist`,
`Lock`, `WpLock`, `WpSmodeMint`, `LockBornHook`, `KCtx` (+ the `KernelRsv` class), `WpSmodeRules`/`WpSmodeProc` (≈ 11 files;
`Adequacy.lean` spells no era tuple — likely untouched); `Xv6/`: the `KernelRsv` instance, `BootCarveHart` (halves), `SpecInitlock`/
`ProofInitlock`, ≤ 30 `lkFresh` files, the `MachGS` LITERALS `AppUnionPre.lean:88`/`AppPreGS.lean:53` (one field each; the 15
`MachGS.ofEra` CALLERS pass an `E : EraGS` and need no edit — R26's "nine" is neither the count nor the touch) + the twin;
`Weak/WeakAdequacy.lean:110-128` (a `MachGS` literal; `lake build Weak` is already in the acceptance); `Vtest` builds no `MachGS`;
M–L ≈ 1.3–2.3k; ONE cone rebuild; §C W8) ∥ **R-ctx** (**DONE 2026-10-12 — `notes/W8-Rctx.md`; results in §C W8 (4) [rev 31]**; the brief: S, READ-ONLY, no build: the gate of W8 (f2-ctx) — re-justify each of the
≈ 35 TSO-leaky context-law uses in the **21** `Xv6/` files of W8-design §3.4 + `Xv6/ProofSwtch.lean` + `Xv6/PipeBirth.lean`
[R25.3] (`ctx_absorb` 6 uses/3 files, `ownCtx_floor_view` 8/4, `ctxStamped_raise` 5/2, `lockHook_llb` 13/10, `ownCtx_key_vis`
3/2; transports `ctx_unstamp` 1, `ctx_park` 3, `ctx_move` 1 (`ProofForkretPark.lean:250`), `kctx_move_in/out` 6
(`ProofSwtch.lean:251,253,268,270,274` — the `swtch` payload transport, the (f2-ctx) `p->lock` hop site — + `ProofScheduler.lean:
1000`), `lock_pay_born` 1 (`PipeBirth.lean:303` — the only post-boot lock birth [rev 31: ONE OF TWO — the `"log"` lock,
`ProofInitlog.lean:434` via `kctx_newlockAt`, sealed in the first `forkret`'s `fsinit`, is the other; R-ctx Q-R3], β′'s cancellable-lock/reclaim case)) by a
sync chain, the device-key arm, or the **`pte-key` arm** [R25.1 (c)] (the A/D write-back `WpPtWalk.lean:455-470`/`Xv6/TransPt.lean`
and the walk's plain PTE read are EXEMPT from the chain invariant, covered by `pteDiscAt` — tabled as such, NOT as RESISTS) —
the bcache/icache/sleeplock floors (`SpecRelease.lean:164-169`, `BcacheLock.lean:132`, `SpecAcquire.lean:96-103`) and the
virtio completion floors (`DiskInvDefs`, `ProofVirtioDiskIntr`); output: per use CHAINED / DEVICE-KEY / PTE-KEY / RESISTS
(→ (f1) for that part), plus a row for the `swtch` handoff (CHAINED via the `p->lock` hop or RESISTS) and one for the walker;
§C W8) ∥ **W5 CORE** (§C W5: M1's
statement and every discharge EXCEPT `Hyps.disk` — HSafe, the fetch cut via `cutOfPristine` + `winPristine` from
`powerInterp_textPristine`, `Hyps.tso` by `pfStepTsoProposed`, the boot bridge, `sailCycleOrder` as the named premise —
with F9's `Hyps.disk` an explicit hypothesis; M; [R21.4] PLUMBING — conditional on `Hyps.disk`, UNSATISFIABLE until F9
(W-DISK ✓): not a milestone, not registered).  **W13 (I)**: gate MET (W-DISK DONE — the fused `DWriteDev` and the
state-aware `pdevEv` are in the tree, [R16.1 (iv)]; (M) landed); launchable in the GRAPH lane as soon as a worker is free (not
in the four-item set above — usage; its brief then fixes the `Fab`/`Supply` text that W5d-G G1–G5 wait for, D26).
WAITS (rev 28 text — RECORD; the rev-31 state is above: F9 ✓, W5 CORE ✓, R-ctx ✓ with an EMPTY (f1) list, M1 PROVED): **W8 (f2-ctx)** for W8-β′ (lands first, same lane) AND the R-ctx check (its gate; a use that RESISTS falls back to
(f1) for that part only — [OWN.37]); **W4 F9** — no longer waits (W-DISK ✓, W-DMA0 ✓) — but F9 must still loosen `SimRel`'s device clause (`efDev =
σ.devs`, `MachOfPf.lean` header deviation 6) to `R-dev` (equality off the OUT capture segment, the [R20.1] `pre₁` form on
it) and re-prove EVERY consumer of `SimRel.dev` [R21.3 (c)] (§C W4 OPEN (b)); **M1 CLOSES** when F9 lands (W5 CORE instantiates `Hyps.disk`) — NO
disk-free M1 variant: M1's premise set IS `srvwmoXv6M1Premises` (§A), whose `srvwmoXv6M1PfRun` runs contain disk-agent
program steps (START is unguarded from `.PDisk none`, `WeakEvInst.lean:502` [R25.s1]), so a "no disk step" premise would be a NEW candidate
restriction, underivable at Stage 2 and dropped at M2 — not worth a second statement; **M1 does NOT wait for W8 — EXACTLY**: M1 CLOSE = W5 CORE's theorem with `Hyps.disk` discharged by W4 F9; its files are
`Weak/`-only (`Weak/SrvwmoXv6Adequacy.lean` — NEW, created by W5 CORE [R25.s2] —, `Weak/MachOfPf.lean`); its inputs are `machRunOfPfRun` ✓, `pfStepTso` ✓, the SC
roots `xv6FsAdequacy_closed`/`xv6TextAdequacy_closed` (whose STATEMENTS W8-β′/W8 do not change — they edit the state
interpretation and the context layer, `MState`/`Lang.lean` untouched, W8-design §0 item 2) and W-DISK ✓; `srvwmoXv6M1Premises`
names NO access discipline, and W8's export is consumed only by W11 (i)/(ii) and W13 (K) at Stage 2.  So M1 closes IN
PARALLEL with W8-β′/W8 (f2-ctx); the only coupling is BUILD order (a MachCSL merge rebuilds the `Xv6` cone and `Weak/`,
so the two lanes merge in sequence, never in logic).  Rev 25–27's lane picture "W8 ledger → M1 → W-RSV" placed M1 in the
MachCSL queue only as W-RSV's gate marker — kept in that role below; **W-RSV** for M1 (D26) AND W8 (f2-ctx) (file
overlap: `Resources.lean`, the load rules, `WpLock.lean`; if W8's 2–4 rebuilds outlast F9 + W5 CORE, W-RSV waits — the
recorded risk); **W-SCO**
(the [OWN.35] demotion) for M1; **W5d/M2** for M1; **W5d-G G1–G5** — their gate W13 (M) is MET (Q-W5dG-seq (a) [OWN.24]), but they edit the chain files
beside W13 (I)/(K): launch after (I)'s brief fixes the `Fab`/`Supply` text (D26); **W11 (iv)c `linCandDiskLat`** for
W13 (L)'s anchors; **W14** for W13 (I)/(W) + W5d-G (W2 CLOSE ✓).

**Stage 0 — RESULTS (2026-10-09): W3, W5b, W5c DONE; W1 interim DONE (W1-Q RULED (c)); W2 spike DONE → D7 STOP,
redesigned (§B(10)); spikes DONE** [R2.s4][R4.2][R5.1][R6.4a][OWN.16][W2s].  Files: `../weak-orch/parked/PROGRESS-W1.md`,
`PROGRESS-W3.md`, `../weak-orch/W5b-API.md`, `notes/W2-spike.md`.
- **W3 — DONE (option A; Q-W3a RULED (A) [OWN.16])** [R1.8][R2.1][R3.1][R5.2][OWN.9].  `Xv6/TextPristine.lean`
  (`textWin :34`, `textPristine g :38` — every byte of `[bcRoLo, bcRoHi)` has history `[⟨0, 0, img a⟩]`;
  `textPristine_read/_readBytes :60,72` — every agent at EVERY `tvn` reads the image bytes, `Wp.lean:1478,1490`;
  `textRo E :88`; `powerInterp_textPristine :123`) + the power-thread twins `MachCSL/PowerText.lean` (`wp_powerT`/
  `riscvPowerAdequacyT`/`powerBootResT`, hook `HtextRec`, persisting the window AFTER era allocation — rev 11's
  slot-stash was UNSOUND: `Hphi` receives only `powerInterp g'`, the era's cells are `Hboot`'s, run LAST, PROGRESS-W3),
  `Xv6/BootSharedText.lean`, `Xv6/SystemBootEraText.lean`, `Xv6/SystemAdequacyText.lean` (≈ 1.76k lines of twins) and
  the **sibling root `Xv6.xv6TextAdequacy_closed`** (`Xv6/LinkTextAdequacy.lean:26`; `roots.txt:19`,
  `baseline.json:63`, `tcb/expected.json` per [R6.5c]; axiom set = `xv6FsAdequacy_closed`'s, no new opaque); existing
  statements and the baseline UNTOUCHED.  Dependents (W2's `LIFetch` row, M1's `candKfetch`, M2's `gzFetch` kernel half,
  W4's `LIFetch` row, W5) are UNBLOCKED.
- **W1 → W1b `Xv6/AllocprocTrace.lean` — DONE (447 lines; W1-Q RULED (c) [OWN.16]; pid history (A) RULED [OWN.28])**
  [R3.s1][R6.5d-alt]; D23, D10.  Landed (line map `notes/W1b-done.md`): `pidPick_range :152` (the `nextOf` tie now
  DISCHARGED: `pidHistWf_nextOf :129`), `pidPick_range_of_wf :161`, `pidPick_badHist :179`/`badWord :184` (the interim's
  fallback word — now EXCLUDED by `pidHistWf`), `pidHistWf_nodup :209` (live pids distinct), `forkCite :260`, `forkStep
  :269`, **`allocprocTraceAns :402`** (§A (b) is its export: answer/`pidPick`/`nextOf ≤ PIDMAX`/`pidHistWf`/`liveList`/
  `poolEmpty` at `KNull`/`¬ poolEmpty` at `KOk`/the chain `niChain F (niHist F)` — the follow-up's fix: rev-18's
  version DISCARDED the chain, so each round's facts held only within its own cited prefix), `forkPev_comparable :437`;
  **(A) [OWN.28]**: `forkHist :318` (the `niLonger` join of era k's fork citations), `foldLonger_spec :324`,
  `forkCite_facts :343`, `forkHist_spec :367` — the fork-only joined history is `pidHistWf`, a prefix of `(niHist F
  k).pev`, contains every fork citation ⇒ live pids distinct ACROSS the era's forks.  Through `NiLedger` (`niForkTie
  :230`, `niEntryOk`'s fork-tie row `:329`, `UsysDet.usysForkTie :321`; `SyscallArmsFork.syscArmFork_ev :137`/`_evNeg
  :211`).  Not stated: `pidHistWf` of the FULL joined history (the non-fork citing rows never read `ι.pev` — not
  derivable from the NI conclusion), pid-ledger events after the era's last fork citation.  Axioms = `xv6NiAdequacy`'s.
- **W2 — SPIKE DONE (D7 STOP, redesigned §B(10)); W2a + W2b DONE (2026-10-11); the CLOSE remains** [R1.11][R2.3]
  [R3.4][R6.4b][W2s].  **W2a `Weak/PfStepTsoMem.lean` (781) — the MEMORY half**: `rmem c st σ :62` = `R-log` (`c.pcLog.
  map wmTid = σ.log.map some`, authors ≤ NCPU) ∧ `R-img` ∧ `rhist :57` ∧ `R-resv` (`σ.resv cpu = none ∨ midPair st
  (hartAgent cpu)`); the history algebra (`histOfSnoc`, `histOfWriteBytes`, `histOfFind` = TsoMem's `find? (HEnt.visible
  i tvn)` is the SCA source, `histOfTop` = `latest`), `rmemBoot :424`, `midPairOther`/`resvOthersNone` (the exclusive-pair
  bookkeeping gives `¬ othersReserve`/`¬ anyReserve` from `pairAdjacent`), the rows `pfLoadRowMem` (TsoMem `readBytes`
  at any `tvn ≤ tvn₀` keeping the bytes visible), `pfStoreRowMem` (`LStore`/`LExStore`, ONE lemma, `excl` a parameter
  [R14.2]), `pfExLoadRowMem` (top bytes + reservation), `pfDReadRowMem` (`candDiskLat`'s `latest`), `pfDWriteRowMem`,
  `pfFetchRowMemM1`/`Cut`, `pfFrameRowMem`.  Deviations (each an address/log hypothesis without which the statement is
  false): `histOfWriteBytes` takes `σ.log.length = log.length`; `pfDReadRowMem` the no-wrap bound `pa.toNat + n ≤ 2^64`
  (`noWrapOfRam` derives it from `ramBytes`; [rev 31] F9 supplies it from `smallNoWrap :1653` for every ≤ 16-byte disk read and
  from `outWraps r = false` for the OUT capture read — [OWN.40], §B(11) (x)); bytes match `w` as `data[j]? = some (nthByte w j)`.  **W2b `Weak/
  PfStepTsoView.lean` (807) — the VIEW half**: `viewRel stamp σ st :135` (`hartRel`: `tv`/`rv`/`coh`/`acq`/`itv` of hart
  `cpu` = `tsoShadow stamp st (hartAgent cpu)`), `StampOk :293` (`cohSrcOk`, `cohFootOk`, `cohOffOk`), `minView :517` =
  the shadow's `shTvn`, `minViewLeSca :524`; the rows against the COMPILED functions: `rowLoad :603` (`cohSrc`; `tsoLoadOk`
  ∧ `viewRel (σ.afterLoad …)`), `rowStore :676`/`rowExStore :688` (`cohSrc`, the reset), `rowExLoad :700`, `rowFence
  :723` (any stamp; `fence.i` raises `itv` iff the shadow's `fiArm`), `rowSfenceMarker :752`, `rowFetchM1 :764`/`M2 :777`,
  `rowDiskRead :790`/`rowDiskWrite :797` (`viewRelForeign`: `diskAgent ≠ hartAgent`); **the (↓) TABLE WITH its faithful/
  stronger/weaker column — W2's acceptance [R9.s4][R10.s5][R11.s4] DELIVERED (file header)**.  Deviations: `R-log`
  (`σ.log = stAuthors st`) is a HYPOTHESIS of the rows reading the top/`ownPub` (W2a's half); a plain load's per-byte
  source agreement is the hypothesis `hsrc` (`σ.mem.loadSrcs … (minView …) pa n = shLoadSrcs (stAuthors st) tvs` — the
  SEAM with W2a, discharged from `R-hist`); `rowFence` needs `fiArm = true` exactly at `fence.i` and `rowSfenceMarker`
  `fiArm = false` — facts of the step list's INSTRUCTION STRUCTURE (`emFenceI`'s criterion), **W2 CLOSE's item (3) to
  supply [R16.6]** (the file header's "W4's to supply" is to be corrected by W2 CLOSE; W4 F5 consumes the lemma); `LDev`
  by a WILDCARD arm (`lbInert`), so (E)/(I) payload changes join without a rebase.
  **W2 CLOSE — DONE except item (3) (`Weak/PfStepTso.lean`, NEW, merged 2026-10-11; `lake build Weak` green, axioms
  `propext, Classical.choice, Quot.sound`, lint = expected drift; `../weak-orch/parked/PROGRESS-W2CLOSE.md`)** — what W2
  CLOSE delivered: (1) **`pfStepTso`**, the ONE
  theorem W4 consumes, composing `rmem ∧ viewRel cohSrc` as `R_mem` and the two halves per label: from an `R_mem`-related
  pair under `pairAdjacent` + `pfRunST`'s facts (`scaOkT` at the prefix shadow, `diskLatOk`), a TsoMem post-state exists
  with `R_mem` re-established; (2) the **`hsrc` hand-off** W2a → W2b — `rhist` + `histOfFind` give `loadSrcs` at the
  minimal view = `shLoadSrcs` (the `Hist.readSrc`/`shSrc` agreement W-COH's input list was NAMED for, [R13.s3]); (3)
  **`fiArm` from instruction structure — NOT DONE, and NOT a step-list fact (W2 CLOSE's day-one finding → Q-FIARM, §D,
  RULED (b)+(a′) [OWN.35]: the named premise `sailCycleOrder`, demoted for kernel text by W-SCO)**: rev 22 called it "a `pfRunST` step-list fact" (the own `LFence false×4` whose latest own
  `LInstr`/`LIFetch` is `LInstr` is the `fence.i` barrier node, the marker's is the announce) — but `st` has no monad and
  the pf state's `Ibch` records the announce, not later fetches; what is needed is the Sail model's IN-CYCLE event order
  (`run_hart_active`, `model/Lean_RV64D/LeanRV64D/Step.lean:331-404`: `fetch () :335` → `instr_announce :340/:377` →
  `execute :370/:404`, no instruction fetch inside `execute`; the cycle is already cut by equations in
  `MachCSL/UCycleDefs.lean:11-17`); `PfStepTsoView.lean`'s header deviation (4) is corrected by W-SCO (or W5) to name `sailCycleOrder`;
  (4) **the census's granularity requirements [W4c E-M1–E-M4]**: state `pfStepTso` PER HART EVENT — the
  `Outcome` node `o` the hart's `m` sits at plus the label emitted there (base `paZ req.pa`, `|tvs| = n`, data `wbytes n
  v`) — concluding `evStep cpu o σ v σ'` (`Lang.lean:355`) for THE answer `v` the pf continuation consumed (`.Ok (w,
  none)` with `nthByte w j = tvs[j].2`), not "some TsoMem step with the same bytes" (E-M1; a `hartStep` form with `m`
  fixed also serves); `R_mem` mentions ONLY `MState`'s memory fields (`mem log tv itv hr resv`), invariant under
  `setReg`/`setDev`/`setRt`, and constrains the pf `Wstate`'s dependency fields no further than the shadow reads (E-M2 —
  else W4 cannot move registers/devices/forks independently); `R_mem` preserved with `σ` UNCHANGED across the 0-step rows
  (retry `LSilent`, parked fire, disk `DFence`) and the `σ' = σ` rows (E-M3); `pfStepTso` TAKES `ramBytes req.pa n` as a
  hypothesis — the structural half supplies it from HSafe (E-M4; `pfLoadRowMem`/`pfStoreRowMem` already do).  Disk rows
  (E-M5) are stated at `MState` level with no cpu (`dmaView`/`storeDma`) — they move to W-DISK's aligned program; a disk
  `DWrite`'s `ramBytes` is NOT available from HSafe (`dmaWrite`'s no-op arm is always enabled, `Lang.lean:574`) —
  W-DISK mirrors that no-op arm on the pf side (§C W-DISK (M5′)), so no driver fact is needed.
  **[R16.6][R17.2] THE STATEMENT — LANDED as `Weak.pfStepTso` (`Weak/PfStepTso.lean:301`), the REPAIRED shape adopted by
  the coordinator on day one; W4 F1–F8 take it FROM THE FILE (rev 21's pinned text is kept there as `PfStepTso.pinnedStmt
  :55`, a documented NON-theorem; `pfStepTsoProposed :436 : proposedStmt fok`).  `R_mem := fun c st σ => rmem c st σ ∧
  viewRel TsoShadow.cohSrc σ st`.  Why the pinned text could not be proved (`PROGRESS-W2CLOSE.md`): FALSE at the fetch
  row (`PFIFetch` checks `ifetchOk … 0`, ANY timestamp, while TsoMem fetches at `tvn ≥ σ.itv` — a stale fetch after a
  `fence.i` that raised `itv` past an own store; `fok` cannot see `itv`); FALSE at every row reading `|log|`/`ownPub`
  (nothing tied `stAuthors st` to `c.pcLog`: `st = []`, a one-message own log, `fence rw,rw` — TsoMem `tv = 1`, shadow `tv
  = 0`); VACUOUS inside an exclusive pair (`pairAdjacent (st ++ [x])` unsatisfiable mid-pair, `pairAdjacentSnocExLoad`);
  and `LExLoad` needs exclusivity (`PFExLoad` checks `readOk … 0` only, TsoMem reads the TOP).  Each repair is a
  HYPOTHESIS change; the conclusion and the pinned explicit-parameter order are unchanged, `rest` appended last.  Marks:
  (1a) the fetch cut is FAITHFUL (the bare `ifetchOk … 0` is WEAKER than Zifencei; the cut is TsoMem's fetch arm exactly;
  M1 pristine text: any `q ∈ [itv, |log|]`, M2: W5d's cut); (2a) the `R-log` link is bookkeeping (`pfRunSTAuthors`);
  (3a) `rest` is a WEAKENING (`rest = []` is the pinned form); (4a) `ownCoh ∧ exclOkTs` is FAITHFUL (RVWMO's atomicity
  axiom: a paired read sees the coherence-latest value = TsoMem's top read).  The landed signature:**
  ```
  theorem pfStepTso (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
      (c c' : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (σ : MState) (cpu : CPU)
      (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (rs : RegFile)
      (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (l : Wlabel) (p' : Pexv6) (d' : Efab)
      (rest : List (Nat × Wlabel)) :
      pstepEv (.PHart cpu (.impure (.ok o) k) rs fn ib) c.pcDev l p' d' →      -- the node IS `o` (E-M1)
      wpPfStep pstepEv pclsEv (hartAgent cpu) l c c' →
      pairAdjacent (st ++ (hartAgent cpu, l) :: rest) →                        -- (1) the `rest` binder
      pfStepFactsT fok TsoShadow.cohSrc st c (hartAgent cpu) l →
      (∀ n va req, o = .memRead n va req → ramBytes req.pa n) →                 -- E-M4, from HSafe
      (∀ n va req, o = .memWrite n va req → ramBytes req.pa n) →
      rmem c st σ → viewRel TsoShadow.cohSrc σ st →
      c.pcLog.map Wmsg.wmTid = (stAuthors st).map some →                       -- (2) the `R-log` link
      (∀ base tvs, l = .LIFetch base tvs →                                     -- (3) the fetch cut `q`
         ∃ q, (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).itv ≤ q ∧ q ≤ c.pcLog.length ∧
           ifetchOk c.pcImg c.pcLog q base tvs ∧
           ∀ (j t : Nat) (v : BitVec 8), tvs[j]? = some (t, v) → t ≤ q) →
      (∀ aq base tvs asrc, l = .LExLoad aq base tvs asrc →                     -- (4) exclusivity
         ownCoh c ∧ exclOkTs c.pcLog (hartAgent cpu) base (tvs.map Prod.fst) (c.pcLog.length + 1)) →
      fn = none →                                                               -- [R17.2-alt] (a)
      l ≠ .LSilent → (∀ kd ba bs, l ≠ .LDev kd ba bs) →                         -- [R17.2-alt] (b)
      (o = .barrier .Barrier_RISCV_i →                                          -- [R17.2-alt] (c): Q-FIARM
         (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).fiArm = true) →
      (∀ n w, o = .instrAnnounce n w → sfAnnB n w = true →                      -- [R17.2-alt] (d): Q-FIARM
         (tsoShadow TsoShadow.cohSrc st (hartAgent cpu)).fiArm = false) →
      ∃ (v : o.ret) (σ' : MState),
        evStep cpu o σ v σ' ∧                                                     -- Lang.lean:355
        (∃ rs' fn' ib', p' = .PHart cpu (k v) rs' fn' ib') ∧                     -- `v` IS what the pf continuation took
        rmem c' (st ++ [(hartAgent cpu, l)]) σ' ∧ viewRel TsoShadow.cohSrc σ' (st ++ [(hartAgent cpu, l)])
  ```
  **[R17.2-alt] — why the five hypotheses** (adding hypotheses WEAKENS the theorem, which R17.2's own rule "hypotheses may
  be WEAKENED by the prover" does not cover, so they are pinned here): without them the statement is FALSE at arms its
  hypotheses cannot relate — (a) `fn = some _`: `pstepNode`'s parked fire keeps `m' = m` (`WeakEvInst.lean:404-412`), so
  `p' = .PHart cpu (k v) …` fails; (b) `LSilent`: at `.regRead r` `evStep` forces `v = σ.regs cpu r` (`Lang.lean:358`)
  while pf continues with `k (rs r)` and `R_mem` has NO register clause (E-M2, by design); the retry self-loop keeps `m' =
  .impure (.ok (.memWrite …)) k` (`:363-365`); `LDev`: MMIO `devRead`/`devWrite` read `c.pcDev`'s `efDev`, which `R_mem`
  does not relate to `σ.devs`, and `pstepPlic` keeps `m' = m` (`:464-473`); (c) `rowFence` NEEDS `fiArm = true` at
  `fence.i` and `rowSfenceMarker` `fiArm = false` (`PfStepTsoView.lean:725,753`), facts of the step list's instruction
  structure that `st` alone (no run hypothesis) does not give — W4 F5 discharges them from `Hyps.fi` (= `sailCycleOrder`,
  [OWN.35]) at its call site.  **Companion lemmas — LANDED** (`Weak/PfStepTso.lean`; W4 takes the signatures from the file):
  **`pfStepTsoStutter :444`** — `fn ≠ none ∨ ((∃ n va req, o = .memWrite n va req) ∧ l = .LSilent)` (parked-fence fire /
  PLIC wire / lost-SC retry), with the EXTRA hypothesis `∀ f, fn = some f → ∃ b, ebarPark b = some f` (without it FALSE: an
  arbitrary parked `fn = some (_, _, true, _)` would move the shadow's `tv`; `pnodeStep` sets no other `fn'`); concludes
  `p' = .PHart cpu (.impure (.ok o) k) …` (monad kept) ∧ `rmem c' (st ++ …) σ ∧ viewRel … σ (st ++ …)` (E-M3, 0 MachCSL
  steps); **`pfStepTsoSame :499`** — GENERIC in `P`/`D`/agent, no `pstepEv`, `l = .LSilent ∨ ∃ kd ba bs, l = .LDev kd ba
  bs`; same conclusion (W4 moves `regs`/`devs`/the PLIC pin by `setReg`/`{σ with devs}`, under which `R_mem` is invariant,
  E-M2); **`rmemSameMem :514`** (`rmem` reads `mem log resv` only), **`viewRelSameRead :522`** (`viewRel` reads `tv hr
  itv` only), **`PfStepTso.hsrcOfRhist :191`** (item (2), the `hsrc` hand-off), **`pfRunSTAuthors :527`** (hypothesis (2)
  along any `pfRunST` from `c0.pcLog = []`).  `R_mem` restricted to `mem log tv itv hr resv` (E-M2).
- **W5b `Weak/PfRunShape.lean` — DONE** (625 lines, green; API `../weak-orch/W5b-API.md`) [R2.3(iii)][R3.2][R3.4]
  [R5.3][R6.4c].  Landed: `candKfetch :53`, `scaVis/scaByte/scaOk :61-72`, `execSca :78`, `candSca :85`, `pairAdjacent
  :95` (+ `Nil/App/Fused/Blk`), `admRunG :224`, `fetchesOk :232`, **`execProgOk'S :242`**, `pfStepFacts :265`, `pfRunS
  :273`, the replay **`execPrefixPfRunProgShaped :512`** / `execWfPfRunProgShaped :594` / `execWfPfRunPinShaped :608`
  — PROVED: `pclsEqr pcls → pstepPinned (exImg E) pstep → execWf E → execProgOk'S … → n ≤ |trace| → ∃ c st, pfRunS … st
  c ∧ pairAdjacent st ∧ states/fabric match ∧ cfgMatchd c (stt E n)`; helpers `execProgOk'SForget/SSca`, `pfRunSRtc/
  PinSub/Trans/One`, `mstepWpPfStepPairS`.  **Deviations from rev 11**: (i) ARITY 6 — `fok` explicit (the left arm is
  `lbFused l ∧ lblRealizes …`, no constructor list: W13 (E)'s payload `LDev` joins unchanged); (ii) the replay is
  PINNED/M1 ONLY (`pstepPinned` hypothesis) — W5d's M2 replay drops it; (iii) `scaOk` has NO floor normalisation
  (`tvn ≤ |log|` only; TsoMem's `Hist.read` via `scaVis`) — W2's `R` carries `tvn`; (iv) [R10.3] `pfStepFacts c i l`
  reads the PRE-CONFIGURATION only (`:265-269`; `pfRunS.snoc … pfStepFacts fok c1 i l`, `:273-277`), so rev 13's
  "`pfStepFacts` carries `candScaT`, the replay threads it unchanged" was FALSE — true for `diskLatOk` (log-only), not
  for the shadow.  **W5b′ — DONE (`Weak/TsoShadow.lean`, 996 lines) [W2s][R10.3][R11.1][R11.3]**: `tsoShadow stamp st i
  : ShFull :500` over the STEP LIST, indexed by the AGENT (`hartAgent c`; the disk row's shadow exists, unused —
  deviation 1), `ShFull` = memory fields `ShSt` (`tv rv coh acq`) + `itv` + `fiArm` (the bookkeeping bit of `emFenceI`'s
  criterion: `itv` moves only at an own `LFence false×4` whose latest own `LInstr`/`LIFetch` step is `LInstr`;
  `itvFenceI`/`itvSfence` check it); the `coh` stamp is the PAIR `CohStamp :98` (load stamp over a per-byte `List
  (Option (Agent × Nat))` mirrored from the pf log — the SAME input W-COH's `FlatMem.loadSrcs` builds — × store effect)
  with `cohFoot`/`cohSrc`/`cohOff`; the TRACE shadow `shadowOf :508` is MEMORY-ONLY (`itv` via W5d's `itvOf`); `scaOkT
  :513` = `scaOk ∧ F ≤ tvn`, `diskLatOk :523`; `execProgOk'ST :559` = `execProgOk'S ∧ execScaT ∧ execDiskLat` BESIDE the
  landed names with forgetful maps (`PfRunShape.lean` NOT edited — deviation 2; W5-pre re-pointed `srvwmoXv6M1Premises`,
  DONE [R16.4]); `pfStepFactsT`/`pfRunST :576,584`; the re-proved replay `execPrefixPfRunProgShapedT :660` returning the
  PROJECTION LEMMA `memOf (tsoRun st) = shadowRun (E.exTr.take n)` (admin steps inert, a fused `LRmw` block = the pair),
  whole-trace `:789` and pinned/M1 `:808` forms; `scaOkT` is required of EVERY plain load, the disk row's included
  (deviation 3; there it follows from `latest`).  Spot checks: `g1NotScaT`/`g1NoRunT` (G1 under every stamp),
  `g2ScaTSrc`/`g2NotScaTFoot`/`g2RunT` (G2: `scaOkT` under (a′), NOT under today's footprint stamp).  [R14.s2] `LDev` is
  matched by a wildcard arm, so W13 (E)'s payload joined without a rebase (confirmed at the 09:23 combined merge).
- **W5c `Weak/SrvwmoXv6Witness.lean` — DONE; W5-pre DONE (805 lines after it, header `:17-24`) [R3.3][R16.4]**; D22.
  Landed: **the DEFINITION `srvwmoXv6M1Premises σ0 c pst dv :599-607`** (§A; W5 states M1 through it — NOW over
  `execProgOk'ST … cohSrc`, `candScaT cohSrc c`, `candDiskLat c`; `m1PremisesS :611` recovers W5c's `execProgOk'S ∧
  candSca`), `srvwmoXv6M1PfRun :624-633` (every M1 premise set feeds W5b′'s shadow-threaded replay
  `execWfPfRunPinShapedT`: a `pfRunST pstepEv pclsEv (candKfetch bcRoLo bcRoHi) cohSrc (wpInit …) st cf` with
  `pairAdjacent st`, matched to the candidate's last state, PLUS `∀ i, (tsoShadow cohSrc st i).mem = shadowOf cohSrc
  c.cdTr i`), **`srvwmoXv6M1Satisfiable :733`** (`∃ σ0 c pst dv, srvwmoXv6M1Premises ∧ c.cdTr = [⟨0, LLoad false
  0x8000a3e8 ts8 (vs8 wl)⟩] ∧ ∀ k, dv k = efInit σ0.wgdev`; the new clauses hold trivially — the ONE load is hart 0's
  first step at floor 0, `execScaTOne`), the **`esil → admRun` bridge `esilAdmRun :169`** (+ `esilNodePstep`,
  `fetchPstep`, `loadPstep`, `entryRun`: the two `_entry` fetches then the GOT load, 106 evaluation steps),
  `execProgOk'SNil/SSnoc :272,280`, a concrete `sigma0` with `wbootFacts` and `diskOf ds = fsImgDisk`, `candConsistent
  :718`.  As designed: `_entry`'s FIRST memory
  instruction, `ld sp,1000(sp)` at `0x80000004` (`Xv6/KernelImage.lean:14-17`; GOT word `0x8000a3e8`, `t = 0`), hart 0
  alone, `candKfetch` ✓ (`roLo/roHi :490-491`), NOT the `sw &started` block (`WeakEvStarted.evX2`, `Weak/WeakEvStarted.
  lean:668` [R9.s2], mid-instruction, EMPTY admin run, `ConfWit.lean:11-22`).  Certifies satisfiability ONLY —
  QUIESCENT, not reaching `allocproc` (D44), nothing about W13's bundle [R5.s3]; W13-wit (D31) can start on the bridge once
  W13 (I) flips `projLbl` (its end event is an `LIo .wr` GRAPH event — (E) alone left `projLbl .LDev = none` [OWN.27]).
- **The three spikes — DONE** (reports `notes/W12-spike.md`, `W13-spike.md`, `W5dG-spike.md`).  W12 (D33–D36): gates
  1–2 closed, gate 3 = W12b.  W13 (D32, D37–D39): vacuity CONFIRMED, T2-1c′ LANDED (`Lin2.lean:623,836,944,995,1012`),
  [OWN.8]'s literal and the folded `gdevAdj ⊆ gmo` REFUTED.  W5d-G (D40–D43): fetch ADMINISTRATIVE, `gzFetch`, cut form.

**Stage 1 — M1, the composed sRVWMO theorem, pinned/kernel-only (internal).**
- **W4 `Weak/MachOfPf.lean`** (L; **STRUCTURAL half F1–F8 DONE 2026-10-11** — 1659 lines, `Weak.lean:633`; **DISK rows F9
  DONE 2026-10-12 [rev 31]**) [R2.1][R2.2][R2.3][R3.1][W2s][W4c].  **F9 RESULT (rev 31; `../weak-orch/parked/PROGRESS-W4F9.md`)**:
  `Weak/MachOfPfDisk.lean` (NEW, 1290 lines — the virtio half: the `DevStates` algebra, `cacheWf :105`, `pre1Eq` (`pre₁` moves only
  `inflight`/`taken`), the MMIO-commutes-with-`pre₁` lemmas (`writeOther`/`writeNCases`/`readNIT` — the plan's "verified once by the
  worker" [R20.1]; a RESET is absorbed by the pre-check), **`R-dev` = `VRel :343`/`VRel.holds :349` + `devAgree :429`** with its
  stability under hart MMIO (`devAgreeRead/Write :464,513`), PLIC sampling (`devAgreeLevel :447`) and the UART/PLIC programs
  (`devAgreeFdev :558`), MachCSL's residual programs and their one-step shapes, the position relation `FC :921`/`PosRel :965`) and
  `MachOfPf.lean` (1659 → 2979: `diskSide :331` instantiates the former `DR`, `SimRel :342` without it, **`simDisk :2603`**, the
  step-count bookkeeping of §C W4 realised, `smallNoWrap :1653`, `caseStall :1994`; `machRunOfPfRun :2854` with `Hyps :658` =
  `tso`/`safe`/`cut`/`fi`).  OPEN items (a)/(b) below are CLOSED: (a) `winPristine :2878` is discharged by W5 CORE (`winOfText`); (b)
  every `SimRel.dev` consumer re-proved.  Deviations (header 6/7 + `MachOfPfDisk` 1/2): `cacheWf` in place of "`cache = []` outside
  capture → gate" (weaker, holds at every state, survives a pre-check abort at the gate where "`cache = []`" would need "a reset
  request is no longer in flight"); `devrt`/`TaskId` untracked (`fork` hands out `devrt.next` whatever it is; a finished/aborted task
  is never scheduled again, so neither `TaskId` nor `done` is read — the idx write's `DRet DIdle` 1 → 0, a refused POP 1 → 1, the
  root restart folded into the next START 1 → 3); **the wrap issue → [OWN.40]** (MachCSL's DMA read wraps its `PAddr`, the pf load
  reads `Int` addresses where `imgZ` aliases the image past `2^64`: an OUT capture buffer wrapping past `2^64` would capture
  different bytes — RULED (a′): the pf program STALLS it, `VirtioProg.outWraps`, header deviation 6, §B(11) (x); the interim
  `Hyps.noWrap` is gone, the capture read's bound comes from `outWraps r = false`, every other disk read ≤ 16 bytes).  Axioms
  `propext`/`Classical.choice`/`Quot.sound`; `lake build MachCSL Xv6 Weak`, lint, `audit.sh --weak` green.  The §C W-DISK
  record's "`cache = []` outside capture → gate" [R19.1 (c)] is thereby SUPERSEDED by `cacheWf` (the binding text is kept as the
  record; F9's deviation is in the sound direction — a weaker side invariant that still makes `cacheReq` act on EQUAL states, since
  the cache is equal by `R-dev` itself).  **RESULT (rev 24)**: `machRunOfPfRun :1535` — a `pfRunST` run
  (any `fok`, stamp `cohSrc`) from `srvwmoXv6M1PfRun`'s start with `pairAdjacent` has a run RECORD `r` (`contR :475`,
  `recLabels r = st`) and a MachCSL run `PowerOn :: pfObsOf r` ending in `SimRel :305` (pool by step KIND `thrOf :194`,
  registers/devices EQUAL, `rmem ∧ viewRel cohSrc`, `R-log` link, `ownCoh`, `fnOk`); 0 or 1 MachCSL steps per non-disk pf
  step.  Parameters `Hyps :620`: `tso` = `pfStepTsoStmt :95` (VERBATIM `PfStepTso.proposedStmt`), `safe` = HSafe, `cut`
  = the fetch cut, `fi` = the `fiArm` facts (= `sailCycleOrder`, [OWN.35]), `disk` = F9's rows over `DR`.  Deviations
  (file header): W4 proves the stutter/same rows ITSELF (`memFrame`, `viewRelPark`; incl. rows the companions' prose
  missed — the boundary `LInstr`, an `LSilent` register write, the PLIC wire at a parked fence/boundary, the disk agent's
  UART/PLIC moves), so `pfStepTsoStutter`/`pfStepTsoSame` are not parameters; `κs` is a function of the RECORD (a disk
  `LDev .dev 0 []` does not say which device moved).  **OPEN from W4**: (a) **`winPristine :1559`** (the kernel text window
  pristine in EVERY reachable powered MachCSL state) is the second hypothesis of M1's `cutOfPristine :1588` — assigned to
  **W5**, via `Xv6.powerInterp_textPristine` (`Xv6/TextPristine.lean:123`) on the W3 twin root; (b) **F9 must loosen
  `SimRel`'s device clause** (`efDev = σ.devs`, header deviation 6) to `R-dev` ([R18.3]/[R20.1]) (+ the `isr`/`cfg`/`cap`
  agreement every reader needs) and **re-prove EVERY consumer of `SimRel.dev` [R21.3 (c)]**: all `simNode` posts
  `c'.pcDev.efDev = σ'.devs` (`MachOfPf.lean:869,906,918,935,943-958,989,1003,1061`), the MMIO arms (`:1007-1038`), `simDev`
  (UART/PLIC gateway via `simDev :1193`'s `devStepOfFdev … hdev.symm`, `:1253,1266` [R23.s3], incl. moves taken ON the capture segment — `dp' = dp`,
  `WeakEvInst.lean:519-525`) and `simWire` (`:1295-1354` [R22.s1]) — S–M of re-proof in `MachOfPf.lean`.  `machRunOfPfRun`: a shaped `pfRunST` run from `wpInit (imgZ bootImage) (efInit
  ds.reset) (epsInit σ0)` (= `srvwmoXv6M1PfRun`'s configuration by `wbootFacts.2.1`; W5-pre re-points the premise set
  to `pfRunST` [W4c D1]), PREFIXED by ONE `PowerOn` step, is a `-<κs>->ₜₚ^[n]` MachCSL run — a forward simulation BY
  INDUCTION ON THE SHADOW-CARRYING STEP LIST (`pfRunST` is snoc-built, `TsoShadow.lean:584`; `R_mem`'s view part is
  stated against the prefix fold `tsoRun`, so the invariant carries the prefix `st` — E-M6), relation `poolRel ∧ R_mem`
  with **`R_mem` THE PARAMETER** over `MState`'s memory fields and the prefix shadow (instantiated by W2's `rmem ∧
  viewRel cohSrc`) and **`poolRel`** holding the MachCSL thread pool, hart expressions/register files, the UART/PLIC
  programs and device states.  **The census's interface [W4c] (binding for the worker):** (E-S2) the thread map is
  PER STEP KIND, not per agent — after `PowerOn` the pool is `[power] ++ cpus.map (Loop 0) ++ DevId.all.map (DevLoop
  0)` (iris `Step.atomic` appends forks at the END; `DevId.all = [uart0, uart1, plic, virtio]`), i.e. thread `0` power
  (stepped once, never again; `gen = 0 ∧ pow = true` invariant), `1+c` hart `c`, `9/10` the UARTs, `11` the PLIC, `12`
  the virtio root, `13+k` the forked `serve` tasks; hart agent `c`'s step goes to thread `1+c` (`pstepNode`) or `11`
  (`pstepPlic`, the pin delivery — MachCSL runs `devOpStep .setPin` on the PLIC thread), agent `NCPU`'s step to `9`,
  `10`, `11`, `12` or `13+k` by which `pstepDisk` disjunct it takes — so `thrOf : step witness → thread index`; the
  UART/PLIC programs are FABRIC (`Efab.efU i`/`efPlic`), not agents, matched 1-to-1 on one thread each (`fdevStep` ↔
  `devStep`'s `.pure`/`.step`/`.get`/`.choose`/`.sample` + blocked; `uartBodyPlain`/`plicBodyPlain`); the one-row model
  D51 only REMOVES interleavings MachCSL admits (C3).  (E-S1) **HSafe** — W4 takes "every thread of every MachCSL run
  from `([power], g0)` is `Reducible`" as a HYPOTHESIS and W5 discharges it from `xv6FsAdequacy_closed`'s first
  conjunct (`Xv6/LinkSystemAdequacyClosed.lean:20-24`): it supplies the BUS DECODE the pf machine lacks — pf branches
  on `devAddr req.pa` (START address only; WeakMem is `Int`-keyed and unbounded) while MachCSL needs `devBytes`/
  `ramBytes` over the whole footprint (`Lang.lean:361-382`), so a pf RAM label at or past `ramEnd` has NO MachCSL arm;
  at the matched hart (same `m`) `Reducible` gives `devBytes ∨ ramBytes ∨ othersReserve` and `othersReserve` is false
  under `pairAdjacent`.  FAITHFUL (imports the SC proof's own safety fact; Sail checks the PMAs before issuing a memory
  event, MachCSL's decode is PMA-faithful, the pf arm is WEAKER — it admits labels Sail never emits).  This is NOT the
  (↑) §B(10) declines: HSafe is MachCSL-side, a conclusion of the SC tree, and holds for ANY run from boot — so §B(9d)'s
  `hullRun` use of W4 has it too.  The alternative (a Sail-level PMA lemma over the residual monad) is XL, not taken.
  (E-S3) **`κs` is a FUNCTION of the pf run**: pf has NO observations (`weakEvLang`'s `Obs = Empty`, `WeakEvLang.lean:
  1007`); MachCSL's `hartObsM c m σ` is nonempty only at a `cur_privilege` write crossing User and reads `σ.regs c` =
  pf's `rs` under `R-regs`, a UART step's `os` is determined by the guard on pf's pre-fabric; so W4 EXPORTS `κs :=
  .powerOn :: pfObsOf run` and "same observations" is DEFINITIONAL.  (E-S6) the bound `n ≤ |st|` is DROPPED (§B(10)).
  Stuttering [W4c B6]: 0 `primStep`s ONLY at the retry `LSilent` and the parked-fence fire; every other hart label is
  exactly 1 `primStep` (silent ops/announce/marker with `σ' = σ`, `regWrite` → `setReg`, barrier node → `MState.fence`
  for the WHOLE `fence.tso` (Sail emits one barrier event, pf splits `ebarNow` + `ebarPark` — the park is the shadow's
  identity, `ShSt.fenceNoSucc`), RAM nodes through `pfStepTso`, MMIO/PLIC through `pfStepTsoSame` [R17.2-alt]).  Boot bridge [W4c D]: `g0 := { m := ⟨σ0.wgregs,
  imgFlat bootImage, [], 0, 0, HRead.zero, none, ds, DevRt.init⟩, gen := 0, pow := false }` (any `m` works —
  `riscvPowerAdequacy` has no premise on initial memory), `g1` with `devs := ds.reset`, `pow := true`; `bootShape g0
  g1`, `bootFacts g1.m`'s register clause IS `wbootFacts`' verbatim (`WeakLang.lean:487` vs `Lang.lean:301`); the step is
  `primStep_power_on` (`Lang.lean:686-688`); `R_mem` at boot through `rmemBoot`.  **File plan [W4c F]** — parametric in
  `R_mem`, `pfStepTso`, HSafe; F1–F8 depend on W2 only through the parameter INTERFACE (E-M1/E-M2), so they start NOW:
  F1 `thrOf` + `poolRel` (the disk part an abstract parameter until W-DISK; S ≈ 150); F2 an `NSteps` snoc/append helper
  (iris `Language.lean` has none; S ≈ 40); F3 the boot bridge (S–M ≈ 150); F4 hart non-memory nodes (~20 `Outcome`
  arms, mostly `rfl`-shaped; M ≈ 300); F5 hart RAM/MMIO nodes through the LANDED `pfStepTso`/`pfStepTsoStutter`/`pfStepTsoSame` (`Weak/PfStepTso.lean`) +
  the HSafe decode; F5 discharges the REPAIRED hypotheses — (2) the `R-log` link by `pfRunSTAuthors` from `wpInit`, (3)
  the fetch cut (M1: any `q ∈ [itv, |log|]` from `candKfetch`'s pristine text; M2: W5d's `itvOf` cut), (4) `ownCoh` by
  `ownCohStep` and `exclOkTs` from the pair's own `PFExStore`, `rest` = the pair's tail, `pfStepTsoStutter`'s "a parked
  fence is an `ebarPark`" from `pnodeStep` — and the two `fiArm` hypotheses from `Hyps.fi` (= `sailCycleOrder`, Q-FIARM
  RULED [OWN.35]) [R17.2-alt] (M ≈ 250–300); F6
  `fdevStep` ↔ `devStep` (5 arms + blocked), `pstepPlic` ↔ `setPin` (M ≈ 200); F7 `pfObsOf` + the `κs` lemma (S ≈ 100);
  F8 the main induction `machRunOfPfRun` over `pfRunST` (M ≈ 200) — **subtotal ≈ 1.3–1.5k, M–L**; **F9 DISK ROWS
  (L ≈ 0.8–1.5k, unverified) — UNBLOCKED (W-DISK DONE 2026-10-12: the aligned `virtioProg :438`, the `DWriteDev`/`DPop` arms
  of `pdiskProg :499`, `preCaptureHead :338` = `pre₁`, W2's rows `pfDWriteDevRowMem :698`/`pfDSkipRowMem :806`/`rowDiskDevMove
  :808`; W-DMA0 DONE [R16.3]: `storeDma pa 0` appends nothing); the `DR` parameter of `SimRel :305` is F9's to instantiate**: after (a), **`R-dev` [R18.3 (b)][R19.1
  (b)]** is **`dvirtio_M = dvirtio_pf` — ALL fields, `disk` and `cache` included** (pf's durable image advances at the
  gate, all cached sectors at once; MachCSL's one sector per drain step; EQUAL at every pf-step boundary of the matched
  run) EXCEPT while pf sits between an OUT request's capture `DRead` and its status `DWriteDev`, where `dvirtio_M = (pre₁
  dvirtio_pf).1`, **`pre₁` := the status `DWriteDev`'s `pre` TRUNCATED before capture's `modify :517-518` [R20.1]** — the
  in-flight pre-check (IDENTITY when `phase s h = none`: after a reset nothing is re-applied), then `setPhase .fetched
  :526`, then the `taken` guard `:529` (IDENTITY when `taken ≠ none`: MachCSL blocked, [R19.3]) — the moves MachCSL's
  program order forces BEFORE the `dmaRead` (`Virtio.lean:526,529,516`): the matched run
  performs `:526` (+ `:529` + `:516` iff the latch is free) at pf's `DRead` — 1 → 3 when free, 1 → 0 when the request is
  no longer in flight (a reset between the POP and the `DRead`: `pre₁` the identity; `:526` would resurrect) [R21.s3], 1 → 1 when held (MachCSL
  BLOCKED at `guard :529`, `DevLang.lean:125`/`devBlocked :592`; the `dmaRead` is never performed and pf's read value is
  unused — its status `DWriteDev` aborts on the same guard); `poolRel` records which case (the MachCSL task's position
  does); the other `DWriteDev`s have no `DRead` between the previous fabric step and them (IN: `fill`'s `get :489` is
  right before its `dmaWriteIf :491`; the used writes follow the gate and `get :542-544`), so equality holds there;
  the clause holds on the WHOLE segment, every hart action AND every disk-agent `pdiskUart` move included [R20.1][R21.3
  (c)]: non-reset MMIO writes (`write :296-323`: `cfg` fields, `isr` ACK) commute with `pre₁` (disjoint fields — verified
  once by the worker), UART/PLIC moves touch no `dvirtio` field and the PLIC gateway samples virtio's `irq` = `isr`, which
  `pre₁` leaves untouched (rows close, but are RE-PROVED), and a RESET (`write
  :294-295` → `reset :260-262`, BOTH sides) is absorbed by the pre-check's identity arm (pf's status `DWriteDev` then
  aborts with `d' = d`, 1 → 0) — free / held / reset are ONE formula (rev 23's `setPhase .fetched (+ latch)` was FALSE
  from the reset until that abort: `alistSet :233-234` on the empty map resurrects).  Beside `R-dev` [R19.1 (c)]: **`cache = []` outside a capture → gate window** (pf: the only `cacheReq` is
  the status write's `pre`, the only drain the gate's; MachCSL: the matched run drains only there) — so `cacheReq` is
  applied to EQUAL states on both sides at every capture and partial-sector lengths need no fact.  Under [R17.1]'s FOLDING
  RULE (α) the folded `modify`s/`guard`s run inside the next fabric step's `pre`; a failed folded guard ABORTS the burst,
  the MachCSL task left a never-again-scheduled zombie (or blocked), matched **1 → 0** [R18.3 (c)] — `devStep`'s blocked
  arm (`Lang.lean:615` [R19.s2]; `devBlocked :590-598`; a stutter the schedule need not take) is never needed; **NO
  single-burst invariant [R21.3 (b)]** (rev 21's "at most one in-flight entry during a burst, none outside one" is false
  without a driver fact — an idx own-guard SKIP or an (α) ABORT leaves stale entries; `R-dev`'s equality makes them
  harmless, §C W-DISK); the multi-step expansions, `devrt.next`/TaskId/pool-append bookkeeping (13+k).  **Bookkeeping after
  [R19.1]–[R19.3] [R18.s3][R19.s1]** (supersedes [R16.s5]/[R17.s5]; the census's "1 → 4 + a NEW THREAD" row
  `W4-structural-census.md:250`): START `LDev` 1 → 2 (`chooseLt 3` = 0, `get :561`); avail-idx `DRead` 1 → 1 (`dma16`);
  ring `DRead` 1 → 1 (`dma16`); POP `DPop` 1 → 4 (`get :567`, `guard :576`, `fork :579`, `serve`'s `get :522` — the two
  `get`s see one state, so the POP's `cfg` re-snapshot is `serve`'s) or 1 → 2 on refusal (`get :567`, restart); the root's
  restart after a POP (`pure ()` → `.pure` → `m' = body`, `:578-580`) is 0 → 1, folded into the POP (1 → 5) or the next
  START (1 → 3); OUT capture `DRead` 1 → 3 / 1 → 1 [R19.3]; each `DWriteDev` 1 → k (the `dmaWriteIf`/`dmaWriteStep` plus
  the `pre` moves NOT already performed at a `DRead`, k ≤ 5 — [R20.2] for `r.len = 0` the status write absorbs the
  elided data phase: OUT 1 → 5, IN 1 → 5 (`:526`, `:489`, `:491`, `:534`, `:536`) [R21.3 (a)], §C W-DISK (M5); a FLUSH/unknown-type request has NO
  data node at any `r.len` (`pure ()`, `Virtio.lean:531-534`): status 1 → 3 (`:526`, `:534`, `:536`), `completeOk`'s FLUSH arm
  true after `drainAll` — xv6 never issues one, listed by F9's no-driver-fact standard [R23.s2]); **the drains 0 → 5k root-loop steps** (per cached sector:
  `choose`(k = 1), `get`, `choose` j, `modify`, root restart `devStep :609`) INSERTED immediately before the used-element
  `pre`'s `guard :539` in the SAME block, so `completeOk` VERBATIM passes [R19.1 (a)]; a gate ABORT is 1 → 5k (the drains,
  then the blocked guard is never taken); a pre-check ABORT 1 → 0; own-guard SKIP 1 → 1 (`dmaWrite`'s skip arm
  `Lang.lean:574`, `σ` unchanged); the idx `DWriteDev`'s continuation `DRet DIdle` → `dp' = none` 1 → 1 (the forked task's
  done-marking `devStep :610-612`, `σ.setRt`; `poolRel` carries `devrt.done`) [R18.s4][R19.s1]; snapshots exactly where
  `serve` takes them (§C W-DISK Snapshot [R18.4][R19.2]) — the `13+k` thread map is then exact.  Other rows: hart loads at the shadow's minimal view, the `LIFetch` row UNDER `candKfetch` (M1)
  / the cut form at `itvOf` (M2) [R11.3].  Risks [W4c]: R1 (blocking, F9 only) the disk drift → W-DISK; R2 the HSafe
  interface; R3 `pfStepTso` at another granularity (E-M1) — CLOSED by the LANDED statement (E-M1's shape kept, the
  hypotheses repaired, §C W2 CLOSE) [R16.6]; R5 `pfRunS` vs
  `pfRunST` — CLOSED (W5-pre DONE [R16.4]); R6 the W-RSV re-check (E-M9: `R-resv` then says `resv = none` at every
  boundary — ONE structural row changes); R7 elaboration cost of the ~30-arm `Outcome` match (local macros, as
  `WeakEvInst`'s header deviation 9).  Deps: F1–F8 — W5b′ ✓, W-COH ✓ (the shadow INSTANCE `cohSrc` is the actual
  `MachCSL.TsoMem`), W3 ✓, W5-pre ✓, W2 CLOSE ✓ (W4 instantiates `Weak.pfStepTso`'s LANDED signature; its `fiArm`
  hypotheses = `Hyps.fi` = `sailCycleOrder` [OWN.35]) — F1–F8 DONE; F9 — W-DISK ✓ (W-DMA0 ✓), LAUNCHABLE;
  W-RSV (L–XL) lands AFTER W4/M1 (D26) and W4 re-checks three rows (`LStore`, `DWrite`, `LExLoad`; S) [R11.2][R12.1].
- **W-DISK `Weak/VirtioProg.lean` + the `WeakEv*` disk arms — DONE (merged 2026-10-12, rev 28).  E-D1 RULED (a) [OWN.29]:
  ALIGN the weak-side `virtioProg` to MachCSL's `Virtio.body`/`serve` (L–XL; NEW rev 19; rev 20 added the (M4)/(M9) MECHANISM
  [R16.1] and recorded W-DISK-Q1/Q2/Q3 RULED [OWN.30]–[OWN.32]).**  **LANDED — the record** (the binding text below is KEPT as
  what the worker built against): `Weak/VirtioProg.lean` 672 lines (was 979) — `DM` = `DRet`/`DRead`/`DFence`/**`DWriteDev pre
  g pa bs k`**/**`DPop h k`** (`:257-266`), `Dres` = `DIdle`/`DStall` (`:269-273` [R25.s5]), `DmWf :279` (`∀ s, (bs s).length = n ∧ n ≠ 0`,
  `pop`'s `∀ s, DmWf (k s)`), `popState :319`, **`drainAll :323`**, **`preCaptureHead :338`** (= the plan's `pre₁`: pre-check →
  `.fetched` → `taken` guard, truncated before the cache move), `dusedTail :394` (… `DFence` → used-idx `DWriteDev` with
  `serve`'s guard VERBATIM), **`virtioProg :438`**, `runVirtioProg :524` (re-stated as the flat-run shape lemma), `virtioProgWf
  :661`; the header carries the Spec-first text, THE FOLDING RULE, the (M1)–(M9) table with marks, the "moves the fabric?"
  column (START by class, POP, IN fill, status, used element, used idx: YES; `DRead`s, `DFence`, `DStall`, `DRet DIdle`: no)
  and the `R-dev` clause for F9.  `Weak/WeakEvLang.lean` — `ediskStep :936` (ten arms), `ediskStepWf :1360`,
  `eprimStepDiskReducible :1393`, `setDvirtioSelf :922` (the abort's `d' = d` on a pre-check failure); `Weak/WeakEvInst.lean` —
  `pdiskProg :499` (deviation 10: START, `DRead`, `DFence`, `DWriteDev` STORE / own-guard SKIP / ABORT, `DPop` refused /
  moved, `DStall`, `DRet DIdle`), `WeakEvInst.pdiskProgLabel` (five label shapes), **the state-aware `pdevEv :604`**
  (`LDev` label OR `.PDisk (some (DWriteDev ..))`), `pdiskProgDevFree :1759`/`pstepDiskDevFree :1781` (extra hypothesis "not
  at a `DWriteDev`"), `pdevEvOk :1792`; `Weak/WeakEvDisk.lean` (850) — `ewpDiskStart :388`, `ewpDiskRead :431`, `ewpDiskFence
  :488`, **`ewpDiskWriteDevStore :524`** (the log append of Rocq's `ewp_disk_write` AND the fabric move of `ewp_disk_commit`
  in one step), **`ewpDiskWriteDevSkip :607`**, **`ewpDiskWriteDevAbort :666`**, **`ewpDiskPop :722`**, **`ewpDiskPopRefused
  :772`**, `ewpDiskIdle :816`; `Weak/PfStepTsoMem.lean` — **`pfDWriteDevRowMem :698`** (13′: `storeDma` + the device's own
  move) beside `pfDWriteRowMem :672` (13, the store without its move), **`pfDSkipRowMem :806`** (16′: skip/abort, `σ`'s memory
  unchanged); `Weak/PfStepTsoView.lean` — `rowDiskWrite :796` (fabric-delta form), **`rowDiskDevMove :808`** (skip/abort/`DPop`
  = `viewRelForeign`), the (↓) table rows `:45-46`; `Weak/WeakRvwmoSupply.lean` — **`devQuiet :177`**, **`devQuietStep :183`**,
  `pdevEvFalse :209`/`pstepEvDevfree :219` RESTATED with `devQuiet p` (new proofs by cases on `p` [R22.s2]), `admRunQuiet`, the
  Supply family's `devQuiet p` hypothesis; `Weak/WeakRvwmoFab.lean` — `hemitfStatesQ :396`/`hartConffStatesQ :556` with
  `devQuiet p ∧ (∀ dp, p = .PDisk dp → ∀ kd ba bs, LDev kd ba bs ∉ …)` [R18.2 (b)], **`gfexecConf :620`'s INTERIM clause `:633`**
  ("a disk row's emission is `LDev`-free", commented "DELETED BY W13 (I)") [R18.2 (a)], `fconfRowsPin :885` extracting it,
  `fconfSupply :928`; `Weak/WeakRvwmoLin2.lean:1007,1024`, `Weak/WeakRvwmoFabInd.lean:425,465,537` — the quiet-boot hypothesis;
  `Weak/WeakRvwmoCapstone.lean` — **`epsInitQuiet :232`** discharging it at `epsInit` (`:268`), `xv6RvwmoSafeModuloF :238`
  STILL BUILDS; `Weak/WeakEvCapstone.lean:1183` UNCHANGED in statement.  **Deviations from this text (all pf-internal, sound
  direction; no owner question — pf ⊆ MachCSL)**: (d1) `Weak/AxOpsem.lean` EDITED (not on the file list): `pstepProgReadCont
  :622`'s `.PDisk` case destructures every `pdiskProg` arm (`:647-660`), so the ten-arm shape reached it; (d2) the quiet-boot
  hypothesis is **`∀ i, i < N → devQuiet (boot i)`** on `fconfSupply`/`fconfTraceRealize`/`fconfRealize` (discharged by
  `epsInitQuiet`), not a per-row conjunct of `gfexecConf`; (d3) the PLAIN `DWrite` node is REMOVED from `DM` — every disk
  store is a `DWriteDev` (the (M1) used element, the status byte, the IN fill, the used idx), `pfDWriteRowMem` surviving as
  the composable store-only lemma; (d4) Rocq's `ewp_disk_write`/`ewp_disk_commit` RETIRED, not re-stated (`WeakEvDisk.lean:
  52-78`, deviation 5: their nodes no longer exist); **(d5) [rev 31][OWN.40] (W4 F9, `VirtioProg.lean` header deviation 6; §B(11)
  (x))**: `dcomplete :424` STALLS an OUT request when `VirtioProg.outWraps r :421` (`buf + len > 2^64`) — `DRet DStall` instead of
  the capture `DRead`; FAITHFUL to the PMAs (no physical memory past the address-space top), STRONGER than MachCSL's `serve` (whose
  `dmaRead` wraps its `PAddr`), the sound direction pf ⊆ MachCSL (F9 matches it 1 → 0, the MachCSL task never scheduled again);
  unreachable under xv6; the "moves the fabric?" table gains the OUT stall row (`:79`, no); MachCSL and `Xv6/` untouched.
  **Acceptance met**: `lake build MachCSL Xv6 Weak` green, lint, `--weak`
  audit, axioms ⊆ baseline; no `DWild`; `pdevEvOk` re-proved; `devQuiet` named and discharged; the interim clause named with
  its deletion comment; `drainAll`/`completeOk` verbatim, `R-dev` full equality, `pre₁` reset-absorbing, zero-length node
  elided — all in the header.  **Unblocks**: W4 F9 (launch set), W13 (I) (gate met), W14's disk rows; §0 F1 and §B(11)'s
  drift entry are RESOLVED, the one device model is MachCSL's [R16.5].  *Spec (virtio 1.x,
  stated first; RVWMO/riscv.cat/Sail/PMAs are SILENT on device threads):* the device reads the available index, then
  the ring entry and the 16-byte descriptors of the chain; the used element's `len` is "the number of bytes written into
  the device-writable portion of the buffer described by the descriptor chain"; a driver MUST NOT issue FLUSH unless
  `VIRTIO_BLK_F_FLUSH` is negotiated, so the device's answer to an UN-negotiated FLUSH is UNSPECIFIED — [R16.5] MachCSL's
  `deviceFeatures` offers bit 9 (`Virtio.lean:100`) but THIS image's driver CLEARS it (`Xv6/SpecVirtioDiskInit.lean:10`;
  `ProofVirtioDiskInit.lean:935` "DRIVER_FEATURES := 0"; `vdi_wce_15 :559`), so MachCSL's `statusOf` OK and pf's UNSUPP
  are BOTH model choices, vacuous (xv6 issues IN/OUT only); the driver MUST NOT publish a malformed chain and the
  device's behaviour on one is unspecified; after writing the used index the device MAY send a used-buffer notification
  (ISR bit); it says nothing about when the device re-reads its own configuration registers.  RVWMO/riscv.cat/Sail have
  NO device-internal events (Sail has no device/DMA model: `MachCSL/Dev/*.lean` is the only device text); Zifencei/PMAs
  silent — every device-internal step below is model text (D45/D49).  *The two programs today [W4c C4]:* pf `virtioProg`
  (`VirtioProg.lean:606-625`, the Rocq `VirtioModel` port, header deviation 2 = RECORDED drift) vs MachCSL `serve`
  (`MachCSL/Dev/Virtio.lean:521-556`: `fetch :465-481` = three 16-byte `dmaRead`s + `ty`/`sec`, `fill :488-492` from
  `cacheView`, `capture :515-518`, status `dmaWriteIf … statusOf`, the `pushed` guard, ONE 8-byte used-element
  `dmaWriteIf (usedLen r ++ head)`, `dmaWriteStep … complete` = the used-idx write FUSED with `isr`/`usedIdx`/in-flight
  removal; `body :558-587` [R18.s5]: `chooseLt 3`, `get :561`, avail-idx `dma16`, ring `dma16`, `get :567`, guard-pop with
  `seen+1` `:576`, `fork (.serve h) :579`, drain `:582-586`; `serve` re-`get`s at `:522` (fetch addresses), `fill :489`
  and `:542-544` (`ui`, `c` after the `pushed` gate `:539-541`) — the snapshot points [R18.4]; `reset :260-262` on
  STATUS := 0, `write :294-295`; `pushOk :419`).  **What (a) changes in the pf program, mismatch by mismatch (mark = the ALIGNED pf against the spec):**
  (M1) used element = ONE 8-byte `DWrite` of `usedLen r ++ head` (FAITHFUL; was 2 writes with `len = r.len`, UNFAITHFUL
  — for xv6's 1024-byte block IN writes 1025 vs 1024, OUT 1 vs 1024 — and the 2 → 1 log-message count broke the
  position-preserving log identification); (M2) `len` as above; (M3) `DRet DWild` → a STALL node (`Dres.DStall`, a
  self-loop `LSilent` arm mirroring `stall = await false`): the `DWild` constructor, `DmWildChain`/`dmWildChainWf`
  (`WeakEvLang.lean:914-919`), `ediskStep`'s DWild arm (`:956-958`), `ediskStepWf`'s case (`:1359`), `pdiskProg`'s arm
  (`WeakEvInst.lean:509-511`), `WeakEvDisk`'s header (D) go, and `WeakEvPf.ediskStepLabel` (no textual `DWild` arm — a wildcard covers it; verify the exhaustive match still closes [R17.s4]) — [R16.1] **21
  occurrences in 4 files** (`VirtioProg` 14, `WeakEvLang` 3 incl. the `eprimStepDiskReducible` arm `:1347-1370`,
  `WeakEvDisk` 2, `WeakEvInst` 2); mark: both STALL and `DWild` are model
  choices on spec-UNSPECIFIED behaviour (stall STRONGER than "anything", `DWild` admits more); the node is UNREACHABLE
  under the verified driver, so no xv6 execution changes — uniformity with the model of record only; (M4) the
  completion FOLDED into the used-idx write — **W-DISK-Q2 RULED (a) [OWN.31]**: the used-idx write is a `DWriteDev` node
  (MECHANISM below) whose fabric delta is `complete` (`isr`, `usedIdx+1`, in-flight removal in the SAME pf step — the RAM store
  that RAISES the interrupt; **[R22.2]** NOT the only fabric-moving store: the status and used-element `DWriteDev`s move
  `dvirtio` too, so all are `gfDev` members, §A(†)) and the separate COMMIT `LDev .dev` is RETIRED (so is `vdelta`'s START-snapshot
  arithmetic); [R20.s2] ONE `DFence` sits immediately before the used-idx `DWriteDev` (today's `dtail` shape, `dmWfDtail
  :934-942`: … write, write, `.fence`, write) — `fencePost dws true×4` on the disk's `Wstate`, 0 MachCSL steps (E-M3);
  §A(†)'s "(R1)'s disk use … ordered by the device-side `DFence` (rule 4)" rests on it — mark: EQUAL to MachCSL, STRONGER than the spec's "MAY then notify" (MachCSL's named choice, §B(11));
  W13 (I)'s `gfDev` lists the fabric TRANSACTIONS (I/O-class events by class, plus fabric-moving stores) [R23.2], this `LStore` among them (§A(†)); (M6) descriptor = ONE 16-byte `DRead` decoded by
  `descOf` (FAITHFUL to the 16-byte structure; the four-read tearing disappears — `dreadDesc :381-386` → one `dreadWord
  16`; `runDreadDesc`'s `rfl` conversion is lost, a `descOf`/`viewWord` lemma replaces it); (M7) status = `statusOf r`
  ([R16.5] a model choice on UNSPECIFIED behaviour — xv6 clears `F_FLUSH` and never issues FLUSH; vacuous); (M8) data from
  the CACHE-OVERLAID view — **[R18.1] (A) as REPAIRED by [R19.1]: MachCSL's own shape; rev 21 specified the payload path
  twice, incompatibly; rev 22's remedy "pf NEVER drains, `R-dev` on `cacheView`" was NOT an invariant**: pf's OUT payload
  enters its `cache` at the status write's `pre` exactly as `capture :515-518` does (`cacheReq ∘ setPhase .served`); pf
  DRAINS at the request's completion gate — **`drainAll (v : VirtioState) : VirtioState := { v with disk := cacheView v,
  cache := [] }`** (= MachCSL draining every cached sector in any order: unique keys by `alistSet :233-234`/`alistDel
  :236`, and `drain :432`'s `diskWrite` IS `cacheView` on that sector) inside the used-element write's `pre`; the IN fill's
  data is `diskRead (cacheView s) (reqOff r) n` evaluated at the write's own `pre`-state `s` — `fill`'s `get :489` folded
  [R18.4], no START snapshot (a fill-time re-read NODE is what [OWN.32] forbids; a read INSIDE the fabric-moving write is
  not one); `R-dev` is **FULL equality `dvirtio_M = dvirtio_pf`, `disk` and `cache` included** (off the OUT capture
  segment, [R18.3 (b)][R19.3]) with the invariant **`cache = []` outside a capture → gate window** [R19.1 (c)].  Why rev
  22's clause failed [R19.1]: under (A) nothing in pf wrote `disk` (`cacheReq :496-500` writes `cache`; `write :291-325`,
  `setPhase :248`, `complete :423-426`, `reset :262` never touch `disk`), so pf's `disk` was the boot image while MachCSL's
  advanced at every `drain :432`; a hart's STATUS := 0 (`write :294-295` → `reset :260-262`, `cache := []` on BOTH sides)
  then made `cacheView = disk` on both — DIFFERENT once any OUT had been drained (every xv6 OUT is: `wce = false`,
  `completeOk :414` needs `!reqCached`), and a later IN filled RAM differently (`fill :492`) — `R-log` fails: the
  post-reset DATA diverged, not only liveness; separately `cacheReq`'s tail entry for a request whose `len` is not a sector
  multiple (`reqSectorLen :371`, `:498`) has `|bs| < 512`, and `cacheView :359` (arm `:361`) answers `v.disk a` past it [R23.s3] — pf's boot
  image vs MachCSL's drained image.  Both reachable in a shaped pf run; F9's standard is "no driver fact".  With `drainAll`
  and `cache = []` at every capture, `cacheReq` is applied to EQUAL states on both sides and partial-sector lengths need
  no fact; `diskOf` is EQUAL at every pf-step boundary (rev 22's "`diskOf` is MachCSL-only" header note is WITHDRAWN,
  §B(11) (vii)/(ix)).  Recorded, not recommended: keep rev 22's (A) and give F9 the premises "no STATUS := 0 after an
  OUT" and "every OUT `len` is a sector multiple" — RAM-content/driver facts needing an SC-tree export, the cost W-DISK-Q1
  (a) rejected.  (Also recorded, not taken: (B) drop `cacheReq` from (2), the idx `g := complete ∘
  write-the-payload-into-disk`, `R-dev` phase-dependent — two clauses and a departure from `serve`.)  (M9) — **RE-SPECIFIED [R16.1 (iii)]; W-DISK-Q3 RULED (a) [OWN.32]: NO fabric-reading `LSilent`
  node (`DGet` is WITHDRAWN — it violated `pdevOk`'s second conjunct, MECHANISM below); [R18.4] NO START snapshot of
  `cfg`/`usedIdx`/`cacheView` either — `serve` re-`get`s THREE times (`:522` for the descriptor addresses, `fill :489`,
  `:542-544` for `ui`/`c` AFTER the `pushed` gate), so a hart's config write between START and `:542` makes MachCSL write
  the used element/idx into the NEW ring and `complete` while a snapshot-bound pf SKIPS (two log entries MachCSL appends
  and pf does not — `R-log` fails, and rev 21's "both skip, SAFETY-EQUAL" needed the driver fact "no config write
  mid-burst", which F9 cannot see)**: every `DWriteDev`'s `pa`/`bs` is STATE-DEPENDENT, evaluated at `s := (pre
  (dvirtio d)).1` — the used element's `pa s = usedElemAddr s.cfg s.usedIdx`, `bs s = usedLen r ++ head`, `g s = if reqOf
  s h = some r then some s else none` (move-free; its `pre` carries the gate, `drainAll` and `setPhase .pushed`), and its
  continuation `k s` BINDS `ui := s.usedIdx`, `c := s.cfg` — `serve`'s `get :542-544` fused into the fabric-moving write
  (for THIS write the `:546-547` conjuncts are trivially true and disappear: same matched block as `get :542`) [R18.4]
  [R19.2 (b)]; **the idx node is `DWriteDev (pre := fun s => (s, true)) (g := fun s => if reqOf s h = some r ∧ s.usedIdx =
  ui ∧ s.cfg = c then some (complete s h) else none) (pa := fun _ => usedIdxAddr c) (bs := fun _ => ui + 1) (k := fun _ =>
  DRet DIdle)` — `serve :552-554` VERBATIM, conjuncts KEPT [R19.2]**: the two used writes are two pf steps, so a hart's
  config write between them (`write :296-323` — any `cfg` field, `qsel`/`devfsel` included; `s.cfg = c` compares the
  WHOLE `VirtioCfg`) makes MachCSL answer `g = none` at `:553` and SKIP (`Lang.lean:574`; the request stays `.pushed`,
  `pushOk :419` false forever) — rev 22's state-reading idx node WROTE and `complete`d there, one log entry MachCSL does
  not append, `R-log` unmatched (unreachable under xv6, no `cfg` write after `virtio_disk_init`, but F9's standard is no
  driver fact); the idx node has no folded moves (nothing between `:547` and `:552`), so its `pre` is the identity and a
  lost request is an own-guard SKIP (1 → 1) followed by `DRet DIdle` (1 → 1), not an ABORT; the fill's `bs s` as in (M8);
  **the POP is the NAMED node `DM.DPop (h : BitVec 16) (k : VirtioState → DM Dres)` [R19.2 (c)]** (`pdiskProg` arm `l =
  LDev .dev 0 []`; `(phase s h).isSome → dp' = none ∧ d' = d` — MachCSL's refusal `:568`, 1 → 2: `get :567`, restart; else
  `s' := { setPhase s h .popped with seen := s.seen + 1 }`, `d' = setDvirtio d s'`, `dp' = some (k s')` with `k` using
  `s'.cfg` for `fetch :466-478`'s descriptor addresses — `serve`'s `get :522` sees exactly `s'`; the matched run executes
  `get :567; guard :576; fork :579; get :522`, 1 → 4; rev 22 listed "the POP" among `ediskStep`'s arms without a
  constructor); START keeps `live`, the avail/ring
  addresses and `seen` from the root loop's `get :561` — every fabric-dependent decision is a GUARD or a read INSIDE a
  FABRIC step; the `seen+1` POP as its OWN `LDev .dev 0 []` step right after the ring `DRead` (MachCSL's guard-pop IS a
  separate step, `:576-578`) — one more `dev`-kind event per request in the disk row, NAMED in §B(11) (vi) (D49 (a)/D51
  class: STRONGER than the spec's silence by (R1)–(R3)'s coupling of the pop to the row's DMA accesses; EQUAL to MachCSL's
  step structure); the status byte (`reqOf s h = some r`, `:536`) likewise a `DWriteDev` with a MOVE-FREE `g` (`g s = some
  s` when the guard holds; its `pre` carries the folded moves) — the plan's choice (EQUAL to MachCSL; the alternative
  "plain `DWrite` + START snapshot, guard only at the idx write" is WEAKER on a mid-burst config write and would leave
  two write shapes); **(M5) the 0-length DMA log
  entry — W-DISK-Q1 RULED (b) [OWN.30] → the standalone serial item W-DMA0 [R16.3]** (MachCSL's `storeDma pa 0` APPENDED a
  log entry while pf emits none — `DmWf`'s `bs ≠ []`; W-DMA0 DONE: `n = 0` appends nothing, `Lang.lean:181-193`);
  **[R20.2] the zero-length DATA PHASE is ELIDED** (today's shape: `dreadData pa 0 k = k []`, `dwriteData pa [] k = k`,
  `VirtioProg.lean:358-366`; `:913-923` are their `DmWf` lemmas [R21.s4]): the IN fill `DWriteDev` and the OUT capture `DRead` are EMITTED only when `r.len.toNat ≠ 0`
  (the continuation branches on the decoded `r`; `r.len` is RAM content — `fetch :471,:477` never tests it — so the
  branch is needed, not a driver fact); MachCSL's zero-width ops are matched INSIDE the next `DWriteDev`'s block — OUT:
  `:526, :529, :516` (`dmaRead r.buf 0`, `dmaView` vacuous), `:517` (`cacheReq` with `reqSpan r = 0` adds no entry,
  `:368, :497`), `:536` — 1 → 5; IN: `:526` (the FOLDING RULE puts it in the fill's `pre`; with the fill elided it moves
  here, and `R-dev`'s equality off the capture segment forbids performing it earlier), `get :489`, `dmaWriteIf r.buf 0
  :491` (`ramBytes pa 0` vacuous, `storeDma pa 0` a no-op AFTER W-DMA0), `:534`, `:536` — 1 → 5 [R21.3 (a)] (rev 24: 1 → 4); FLUSH/unknown type: `:526`, `:534`, `:536` — 1 → 3 at any `r.len` [R23.s2]; mark
  EQUAL to MachCSL (a zero-length transfer is a no-op on both sides; virtio 1.x's text on zero-length buffers not checked
  in-tree); **(M5′) the `ramBytes` seam E-M5**: `pdiskProg`'s write arms mirror `dmaWrite`'s no-op arm (`ramBytes pa n ∧
  g … = some s' → LStore` / `¬ ramBytes (pa s) |bs s| ∨ g s = none → LSilent`, `dp' = some k`; the `n = 0` disjunct
  DROPPED [R20.2] — no emitted node has width 0), FAITHFUL to the model of record, so F9 needs NO driver fact for DMA
  footprints.
  **(M4)/(M9) MECHANISM [R16.1] — binding for the worker.**  *The invariant.*  `WeakPromiseFact.pdevOk pstep pdev`
  (`:613-614`): for EVERY step with `pdev p l p' = false`, `d' = d` (the fabric does not move) AND `∀ d0, pstep p d0 l p'
  d0` (the step does not DEPEND on the fabric).  The instance marker `pdevEv _ l _ := l is LDev` (`WeakEvInst.lean:544-547`,
  "a function of the LABEL alone"; header convention `:30-33`: "every arm that READS OR MOVES the device fabric carries
  `LDev`" — START is `LDev .dev` precisely because it reads `dvirtio d`, `:488`); `pdevEvOk : pdevOk pstepEv pdevEv`
  (`:1694`) is proved from `pdiskProgDevFree :1670-1684` ("`l ≠ LDev → d' = d ∧ ∀ d0, pdiskProg dp d0 l dp' d0`") and
  `pstepDiskDevFree :1686`.  Consumers ON THE PATH: `WeakEvCapstone.lean:1183` (`wpBehaviorFulfilOnceDev pstepEv pdevEv …
  pdevEvOk`, inside the T2 event capstone) and `WeakRvwmoSupply.pstepEvDevfree :169-171` (via `pdevEvFalse :164`: "`l ≠
  LDev → pdevEv = false`") → `admRunDevfree :175`, `hemitDevfreeConst :202`, `hemitDevfreeRefab :241` — the realization's
  fabric blindness, which `WeakRvwmoFab.lean:17,47` names as its only route to the device semantics.  Rev 19's (M4) — a
  `DWrite` (label `LStore`, arm `:499-503`) with `d' = setDvirtio d (complete …) ≠ d` — made `pdiskProgDevFree` and
  `pdevEvOk` FALSE as stated; rev 19's (M9) `DGet` (`LSilent`, `dp' = some (k (dvirtio d))`) violated the SECOND
  conjunct.  *The fix.*  (i) a NEW node **`DM.DWriteDev (pre : VirtioState → VirtioState × Bool) (g : VirtioState →
  Option VirtioState) (pa : VirtioState → PAddr) (bs : VirtioState → List (BitVec 8)) (k : VirtioState → DM Dres)`** (`pre`
  = the folded part, FOLDING RULE below [R17.1-alt][R18.3]; `pa`/`bs` STATE-DEPENDENT [R18.4], evaluated at `s := (pre
  (dvirtio d)).1`; **the continuation RECEIVES `s` [R19.2 (a)]** — a read INSIDE the fabric step, within [OWN.32]'s ruling
  (a), not a re-read node; `DmWf` asks `(∀ s, (bs s).length = n ∧ n ≠ 0) ∧ ∀ s, DmWf (k s)` — fixed widths 1/8/2, the fill
  a NON-ZERO `r.len` ([R20.2]: the node is emitted only then)) — the pf twin of `DevM.dmaWriteStep` (`MachCSL/Dev/DevLang.lean:163-167`): `pdiskProg`'s arm reads the CURRENT
  fabric at the write — `(pre (dvirtio d)).2 = true ∧ g s = some s' ∧ ramBytes (pa s) |bs s| ∧ bs s ≠ [] → l = LStore false
  (paZ (pa s)) (bs s) [] [] ∧ dp' = some (k s) ∧ d' = setDvirtio d s'` (`bs s ≠ []` is redundant under `DmWf`'s `n ≠ 0`,
  hence no `bs s = []` skip disjunct — harmless [R21.s4]); **[R16.1-alt]** `g s = none ∨ ¬ ramBytes → l =
  LSilent ∧ dp' = some (k s) ∧ d' = setDvirtio d s`
  (the own-guard SKIP keeps `pre`'s moves) — R16 wrote "the stall self-loop" for the `none` case, but MachCSL's `dmaWrite` with
  `g = none` SKIPS the write and CONTINUES (`Lang.lean:574`: `(g = none ∨ ¬ ramBytes pa n) ∧ σ' = σ`; DevLang's docstring
  "blocks nothing and writes nothing"), so the 1 → 1 twin is the (M5′) skip arm.  **FOLDING RULE [R17.1] — binding; the plan chooses (α) ABORT.**  Rev
  20 folded BOTH kinds of guard into one skip arm, and a skipped `DevM.guard` did not propagate: an OUT request whose
  `taken` latch (`Virtio.lean:529`) is held would skip the status write, then perform the used-element/used-idx writes
  (their own guards hold) and `complete`, while MachCSL's task sits BLOCKED at `:529` (`devBlocked :592`, `devStep :615`) — `R-log`/`R-dev` unmatched, F9 unclosable; likewise a failed `pushed` gate.  *Per MachCSL construct:* (1)
  a `dmaWriteIf`/`dmaWriteStep`'s OWN guard (`reqOf s h = some r` `:536`; `… ∧ usedIdx = ui ∧ cfg = c` `:546-547,553`) →
  the SAME node's `g`, failure = SKIP (`LSilent`, `dp' = some k`; 1 → 1, `Lang.lean:574`); (2) a `DevM.guard` (`taken
  :529`, `pushed :539-541`) and the `DevM.modify`s since the previous fabric step (`setPhase .fetched :526`, `.served
  :534`, `.status :537`, capture's cache move `:517-518`) → the NEXT fabric step's folded part `pre`, failure = **(α)
  ABORT**: `l = LSilent ∧ dp' = none` — the burst ends with the request IN FLIGHT exactly as MachCSL's blocked task leaves
  it (phase set, `taken` held, `complete` not run), matched **1 → 0** [R18.3 (c)] (the twin is blocked or simply left
  unscheduled; `devStep`'s blocked arm `Lang.lean:615` is a self-loop STUTTER the schedule never needs — `devBlocked`
  is vacuous for `g = none`); that task is a ZOMBIE the matching schedule never steps again (MachCSL imposes no fairness);
  pf's next START ↔ MachCSL's root-loop pop.  **`R-dev` [R18.3 (b)][R19.1 (b)]** = **`dvirtio_M = dvirtio_pf`, ALL fields
  (`disk` and `cache` included)** EXCEPT on the OUT CAPTURE SEGMENT (pf between the capture `DRead` and the status
  `DWriteDev`), where `dvirtio_M = (pre₁ dvirtio_pf).1` with **`pre₁` := the status `DWriteDev`'s `pre` TRUNCATED before
  capture's `modify :517-518` [R20.1]** (pre-check, identity when `phase s h = none` → `setPhase .fetched :526` → `taken`
  guard `:529`, identity when `taken ≠ none` [R19.3]): MachCSL's program order puts `:526` and `:529` BEFORE the `dmaRead :516`,
  and the `dmaRead` must be matched to pf's `DRead` (same step, else `latest`/top values differ), so the matched run
  performs `:526` (+ `:529` + `:516` iff the latch is free) AT pf's `DRead` — 1 → 3 when free, 1 → 0 when no longer in
  flight [R21.s3], 1 → 1 when held: `guard
  :529` is `DevM.guard`, which BLOCKS when `taken ≠ none` (`DevLang.lean:125`; `devBlocked :592`), the `dmaRead` is never
  performed, pf's read value is unused and its status `DWriteDev` ABORTS on the same guard in its `pre` with `d' =
  setDvirtio d (pre s).1` = MachCSL's blocked state; `poolRel` records which case (the MachCSL task's position does).  No
  other `DWriteDev` has a `DRead` between the previous fabric step and it (IN: `fill`'s `get :489` is immediately before
  its `dmaWriteIf :491`; the used writes follow the gate and `get :542-544` directly), so equality holds there.  The
  clause holds on the WHOLE segment, every hart action and disk-agent `pdiskUart` move included [R20.1][R21.3 (c)]:
  non-reset MMIO writes (`write :296-323`: `cfg` fields, `isr` ACK) commute with `pre₁` (disjoint fields — the worker
  verifies this once), UART/PLIC moves leave `dvirtio` alone and sample `isr`, which `pre₁` does not touch, and a RESET (STATUS := 0,
  `write :294-295` → `reset :260-262` on BOTH sides; the matched MachCSL task sits at `:517` or blocked at `:529`) is
  absorbed by the pre-check's identity arm — pf's status `DWriteDev` then aborts with `d' = d`, 1 → 0; free / held /
  reset are ONE formula, `poolRel` still records the MachCSL task's position (rev 23's `setPhase .fetched (+ latch)`
  resurrected `(h, .fetched r)` on the reset map, `alistSet :233-234`, FALSE until the abort).  (Rev 21's "EQUALITY incl. phases"
  was false on that segment; rev 20's "equal up to phase" was closer but too coarse.)  **[R17.1-alt]** R17.1's (α) wrote
  the abort as `d' = d`; but `setPhase .fetched` (`:526`) runs BEFORE the `taken` guard and `setPhase .status` (`:537`)
  BEFORE the `pushed` gate, so the abort must carry those moves — hence `pre`.  **`pre` [R18.3 (a)] — binding order**:
  its FIRST folded guard is the IN-FLIGHT PRE-CHECK **`(phase s h).isSome`** (the request MachCSL's task was serving is
  still in flight); failure → ABORT with **`d' = d`** (NOTHING re-applied); only then the `setPhase`s/`taken`/`cacheReq`
  moves and the `DevM.guard`s, and `(pre s).2 = false` on a later guard → ABORT with `d' = setDvirtio d (pre s).1`; else
  `g` is applied to `(pre s).1` — write (`d' = setDvirtio d s'`) or own-guard SKIP (`d' = setDvirtio d (pre s).1`, `dp' =
  some k`).  Why the pre-check: `pre` re-applies MachCSL's moves to whatever state it finds, and after a MID-BURST RESET
  (`write :294-295`: STATUS := 0 → `reset :260-262`, `inflight := []`, `taken := none`) a `pre` without it would run
  `setPhase … (.fetched r)` on the EMPTY map (`alistSet :233`) — RESURRECTING the request — take `taken`, write the
  status byte, pass the gate, skip the used writes (`cfg0 ≠ c`) and end the burst with `(h, .pushed)` in flight and
  `taken = some h` forever, while MachCSL's twin (left at `:517` by the matched run) is a zombie at the reset state: `R-
  dev` fails and after any re-init pf's `pushOk`/`taken` abort every request MachCSL completes.  With the pre-check pf
  applies MachCSL's moves exactly when MachCSL's task would still be live, and after a reset pf aborts ↔ MachCSL's zombie
  is never scheduled (`inflight = []`, `taken = none` on both sides; MachCSL's own `:517-518` would resurrect too — the
  matched run simply never schedules that continuation).  Every `DWriteDev` arm is fabric-touching under the state-aware
  `pdevEv` (ii), so an `LSilent` step with `d' ≠ d` respects `pdevOk`.  Capture's `dmaRead`s precede the node as
  `DRead`s; on an abort they match 1 → 0 (a read moves neither `σ` nor the log).  (β) — SKIP with PROPAGATION (exact
  phases, every `g` requires its predecessor's phase, F9 obligation `g_j = none → g_{j+1} = none`) — is recorded, not
  taken: same exact phases plus an extra obligation.  **The folded gate [R18.1][R19.1 (a)]**: the used-ELEMENT write's `pre`
  is **pre-check `(phase s h).isSome` → `setPhase .status` (`:537`) → `drainAll` → the gate `:539-541` with `completeOk
  :412-416` VERBATIM** (`!reqCached` and `cache.isEmpty` are TRUE after `drainAll`; rev 22's `completeOkPf` is WITHDRAWN);
  the matched MachCSL run inserts `cache.length` root-loop drain iterations (`body :581-586`, each `choose`(k = 1), `get`,
  `choose` j, `modify`, restart — 0 → 5k) immediately before its `guard :539`, in the same block, so `completeOk` passes on
  both sides; on a gate ABORT (`pushOk`/`taken` false) `d' = setDvirtio d (pre s).1` INCLUDES `drainAll`, matching
  MachCSL's drained-then-blocked state; on a pre-check ABORT `d' = d` with `cache = []` by `reset` on both sides.  [R19.s4]
  `completeOk`'s `wce` branch: with `wce = true` (a hart negotiating F_FLUSH — not xv6) MachCSL need not drain, but the
  matched run still MAY, so the block above is unconditional.  (Rev 22's warning stands in the other direction: folding
  `completeOk` verbatim WITHOUT a pf drain would skip every OUT request's used writes and xv6's `virtio_disk_rw` would
  sleep forever on `b->disk` — a safe, write-dead disk.)  **In-flight entries [R21.3 (b)] (NO invariant needed)**:
  `pdiskProg` holds ONE residual program and STARTs only from `none` (`WeakEvInst.lean:485-488`), so at most one
  `inflight` entry belongs to a LIVE MachCSL task (the current burst's); every other entry's task is a never-scheduled
  zombie (an (α) ABORT) or has FINISHED (an idx own-guard SKIP leaves `(h, .pushed)` while the task completes,
  `Virtio.lean:552-554`, `Lang.lean:569-574` [R23.s3]); `R-dev`'s equality makes such stale entries harmless (`pushOk`/`taken`/the
  pop guard read the same map, both sides refuse/abort alike); under the verified driver none exists.  **Snapshot [R18.4 (c)][R19.2]**: taken exactly where `serve` does — START
  (root loop's `get :561`: `live`, avail/ring addresses, `seen`), POP (`serve`'s `get :522`: `cfg` for the descriptor
  addresses, via `DPop`'s continuation), the fill's `pre` (`get :489`: `cacheView`), the used-element `pre` (`get
  :542-544`: `usedIdx`, `cfg`, HANDED to the continuation and re-tested at the idx write); the simulation's SCHEDULING
  freedom closes a config write that falls INSIDE one pf step (MachCSL device steps that pf performs as ONE step run as
  one block, so no hart step falls between them); one that falls BETWEEN the two used writes is closed by the idx write's
  KEPT conjuncts (both sides skip).  **Mark [R18.3 (d)][R18.4 (c)][R19.1 (d)]**: after [R18.3]/[R18.4]/[R19.1]–[R19.3] the
  pf program and `serve` take the same decisions at the same fabric states up to the simulation's scheduling; the ONLY
  reachable divergence is the post-reset LIVENESS gap (STATUS := 0 mid-burst, `virtio_disk_init` only: pf aborts,
  MachCSL's task is a zombie that may later unblock, the aborted pf burst cannot resume) — the post-reset DATA is EQUAL
  (`disk` equal by `R-dev`'s full equality); irrelevant to the published safety conclusions, NAMED here; NO driver fact
  needed (rev 21's "both skip on a mid-burst config write" is withdrawn — MachCSL writes into the new ring, and so now
  does pf).  `ediskStep`
  sets BOTH `ewgLog` and `ewgDev` (`edlabApply` already takes `d'`, so `ediskStepFactor` and `WeakEvCapstone :650-664`
  adapt).  **Terminal node [R18.s4][R19.s1]**: the idx `DWriteDev`'s continuation is `k := fun _ => DRet DIdle` → `dp' =
  none` (the existing arm `WeakEvInst.lean:514`; 1 → 1 against the forked task's done-marking `devStep :610-612`), so the
  next START is well-defined; `DRet DDone`/`vdelta` retire with COMMIT.  (ii) **`pdevEv`
  becomes STATE-AWARE**: `pdevEv p l p' := lbIsdev l || (match p with | .PDisk (some (DWriteDev ..)) => true | _ =>
  false)` — the signature `P → Wlabel → P → Bool` already allows it and `pdevOk` is parametric in `pdev`; `pdevEvOk`
  re-proved.  **[R17.3] The devfree lemmas are FALSE as stated** under the state-aware marker: `admRunDevfree`,
  `hemitDevfreeConst :202`, `hemitDevfreeRefab :241` (`WeakRvwmoSupply.lean`) and `hemitfStatesQ :344-460`/
  `hartConffStatesQ :469-503` (`WeakRvwmoFab.lean`) quantify over an ARBITRARY start `p : Pexv6`, and from `p = .PDisk
  (some (DWriteDev ..))` an `LDev`-free `LStore` moves the fabric.  The fix is a START-STATE hypothesis: define
  **`devQuiet : Pexv6 → Prop`** (`.PDisk (some _) → False | _ → True`); prove **`devQuietStep : pstepEv p d l p' d' →
  (∀ kd ba bs, l ≠ LDev kd ba bs) → devQuiet p → devQuiet p'`** (no START ⇒ no burst: every arm out of `.PDisk none` —
  START, the UART/PLIC moves — is `LDev`, `WeakEvInst.lean:488,518-526`); restate `pdevEvFalse : devQuiet p → (∀ …, l ≠
  LDev …) → pdevEv p l p' = false` (**[R22.s2]** today's proof is `cases l` on the label alone, `WeakRvwmoSupply.lean:164-167`
  — the restatement is a NEW proof by cases on `p`, not a hypothesis edit) and `pstepEvDevfree` likewise, and give `admRunDevfree`/`admRunRefab`/
  `hemitDevfreeConst`/`hemitDevfreeRefab` a `devQuiet p` hypothesis (S); thread it through `hemitfStatesQ`'s induction
  (`WeakRvwmoFab.lean:384-387, 431-438` call `admRunDevfree`/`pstepEvDevfree`/`admRunRefab`), `hartConffStatesQ` (gets
  `devQuiet p0`), `supplyOfFconf :690`/`fconfSupply :782-842`, `fconfSupply'` (`WeakRvwmoLin2.lean:997-1037`) and
  `WeakRvwmoFabInd.lean:443`, whose `boot : Nat → Pexv6` receives `∀ i, devQuiet (boot i)` — discharged at `xboot σ0` =
  `epsInit` (`WeakRvwmoCapstone.lean:90-91`, `WeakEvCapstone.lean:1026-1027`: harts `.PHart`, the disk `.PDisk none`).
  `emDevfree` stays LABEL-based; the lemmas gain a start-state hypothesis discharged at `epsInit` (rev 20's "keep
  `emDevfree` via ONE new lemma" could not rescue lemmas stated for all `p`).  **[R18.2] `devQuiet` rescues the SUPPLY
  family only** (`admRunDevfree`/`admRunRefab`/`hemitDevfreeConst`/`hemitDevfreeRefab`: their hypothesis "no `LDev` in
  the run/row" keeps the disk at `.PDisk none` throughout, by `devQuietStep`); **the FAB family is FALSE, not merely
  unprovable, under W-DISK**: `hemitfStatesQ` (`WeakRvwmoFab.lean:347-354`) concludes for EVERY block `n` of the row
  `emDev false (n+k) es = false → dvo (n+k) = dvi (n+k) ∧ ∀ d, hblkQ Q d d …`, and `emDev :144-150`/`isDevBlock :152`
  are LABEL-based (`lbIsdev :119`) — a used-idx `DWriteDev` block `eadm [LSilent …] ++ [(LStore …, some k)]` has `emDev =
  false` yet `dvo = setDvirtio dvi (complete …) ≠ dvi` (`isr`, `usedIdx` move), likewise the used-element block whose
  `pre` sets `.pushed`; and from the row start `.PDisk none` the START block (`LDev`, `emDev = true`) moves to `.PDisk
  (some _)`, so no later block is quiet — `devQuiet` cannot be threaded past START.  Consumers with unsatisfiable
  obligations for a device-active disk row: `hartConffStatesQ :471` → `fconfRowsPin :786` (the `(i,n) ∉ gfDev → ∀ d,
  hblkQ … d d …` conjunct, via `gfexecConf`'s `isDevBlock em k ↔ (i,k) ∈ gfDev` `:533`) → `supplyOfFconf :690`'s third
  hypothesis → `fconfSupply :827`, `fconfSupply'` (`Lin2.lean:997`), `fconfTraceRealize :1014`,
  `WeakRvwmoFabInd.fconfRealize :413-447`, `WeakRvwmoCapstone.xv6RvwmoSafeModuloF :228` (internal, D39 — must still
  BUILD).  *The fix (binding; W-DISK owns it):* **(a)** `gfexecConf` (`Fab.lean:524-536`) gains the INTERIM clause **"a
  `.PDisk` row's emission is `LDev`-free: `boot i = .PDisk _ → ∀ kd ba bs, LDev kd ba bs ∉ emLabels em`"** (hart rows keep
  their MMIO blocks — `devQuiet (.PHart ..)` is `True` and `pstepEv` keeps the constructor); **(b)** `hemitfStatesQ` and
  `hartConffStatesQ` take **`devQuiet p ∧ (∀ dp, p = .PDisk dp → ∀ kd ba bs, LDev kd ba bs ∉ es.map Prod.fst)`** (the
  induction carries it: a `PHart` stays quiet under every step, a `PDisk` under `LDev`-free steps by `devQuietStep`);
  `fconfRowsPin` extracts it from (a); nothing else in the chain changes shape; **(c)** CONSEQUENCE, named in §B(11)
  (vii) and §C W13 (I): until (I) replaces `isDevBlock` by the endpoint criterion `(i,k) ∈ gfDev ↔ (gisIo (i,k) = true ∨ dvi k ≠ dvo k)` (§A(†))
  [R23.2] and DELETES clause (a), the INTERNAL fabric bundle `gfexecConf` is VACUOUS for device-active disk rows — the same interim
  pattern as `ioResidueGwfInterim :184`; the published bundle `xv6ConfS` is (I)'s.  Recorded, not recommended: W-DISK
  absorbs (I)'s endpoint criterion (two XL-adjacent items on `Fab :318-503`).  So `lake build Weak` stays green with: the
  Supply family gaining `devQuiet p` (S); the Fab family gaining the interim disk clause (a)/(b) (S–M); W-DISK owns BOTH
  — not W13 (I) (rev 21's "no proof change beyond the hypothesis" is withdrawn [R18.2 (d)]).  (iii) = (M9) above.  (iv)
  **W13 (I)'s text [R22.2]**: `(i,k) ∈ gfDev ↔ (gisIo (i,k) = true ∨ dvi k ≠ dvo k)`, the endpoints from `hartConff`
  (`WeakRvwmoFab.lean:239-262`), NOT from `isDevBlock` (rev 25's `gisIo → dvi ≠ dvo` was unsatisfiable — non-moving MMIO
  exists — and every fabric-moving `DWriteDev` is a member, §A(†)); (I) deletes clause (a) [R18.2 (c)]; the (I) delta is **M**,
  not "S–M text": the `isDevBlock` clause `:533` and its `hblkQ` consumers `:318-503` change shape, and the ~10 chain
  sites (M) closed by `gwfNoIo` re-open.  **`VirtioProg.lean` map [R17.s1]** (rev 20's "RETIRE
  `:803-952`" and "KEEP `virtioProgWf :952`, `runVirtioProg :664`" contradicted each other): **RETIRE `:211-317`** (§0b,
  the ported `VirtioModel` fragment: `writeByteList :224`, `virtioUsedWrites :279`, `virtioComplete :286`, `virtioReqStep
  :305`) **and `:729-895`** (`virtioCompleteState/Writes`, `vmodelVprogPerm :779`, `virtioCompletePair :792`, §8
  `virtioProgDisj :800`, `virtioProgReqStep :803`, `Stalled :836`, `Idle :850`, `Trichotomy :860`, `ReqStepState :869`,
  `DoneStep :884`) — they tie the program to the Rocq ATOMIC step (no Lean counterpart; `r.len`, UNSUPP FLUSH, `vdelta`
  are what (a) abandons) and nothing in `Weak/` consumes them (grep: `virtioProg` is consumed by `WeakEvLang.ediskStep
  :930`, `WeakEvDisk` §5's per-node rules `:372-600`, `WeakEvInst.pdiskProg :488`, `WeakEvCapstone :645-664,936`);
  **RE-STATE `runVirtioProg :664-728`** over the aligned program as the flat-run SHAPE lemma (three shapes → done / idle /
  stall — it is stated against `virtioPending`/`chainAt`/`reqAt`/`vdelta`, the Rocq model, so "keep" means re-state);
  **KEEP §9 `:897-979`** (`DmWf`, `dmWfDwriteData :919`, `dmWfDcomplete :944`, `virtioProgWf :952` — [R20.s5]'s :945/:953 NOT
  adopted, the tip has :944/:952; consumed by
  `ediskStepWf :1331`); the `dmWritesMap*` algebra (`:417-552`) only where a consumer survives.  **Files**: `Weak/VirtioProg.lean` (979 →
  the program ≈ 400–600 + algebra; ≈ 250 retired), `Weak/WeakEvLang.lean` (`DmWildChain :914-919`, `ediskStep :927-961`
  arms — `DWriteDev` (write / own-guard SKIP / ABORT, the `∀ s` continuation form), `DStall`, `DPop` [R19.2 (c)];
  `ediskStepWf :1324-1346` (the `∀ s, DmWf (k s)` form), [R16.1 (v)] `eprimStepDiskReducible
  :1347-1370` — a `DWild` arm rev 19 did not list), `Weak/WeakEvDisk.lean` (per-node rules §5, header), **`Weak/WeakEvInst.
  lean`** (`pdiskProg :485-516`; **`pdevEv :544`, `pdevEvOk :1694`, `pdiskProgDevFree :1670`, `pstepDiskDevFree :1686`**,
  `pdiskProgLatFree :1400`, `pdiskProgTsLoad :1423`, the `ediskStep ↔ pdiskProg` factorization `:1180-1186`),
  **`Weak/WeakRvwmoSupply.lean:164-171`** (`pdevEvFalse`/`pstepEvDevfree` restated; `devQuiet`/`devQuietStep`, the `devQuiet p`
  hypothesis on `admRunDevfree :175`/`admRunRefab`/`hemitDevfreeConst :202`/`hemitDevfreeRefab :241` [R17.3]),
  **`Weak/WeakRvwmoFab.lean`** (`hemitfStatesQ :344-460`, `hartConffStatesQ :469-503` — the `devQuiet ∧ LDev`-free-disk-
  row hypothesis [R18.2 (b)]; **`gfexecConf :524-536` — the interim `LDev`-free `.PDisk` row clause [R18.2 (a)]**;
  `fconfRowsPin :786` extracts it; `supplyOfFconf :690`, `fconfSupply :782-842` unchanged in shape),
  **`Weak/WeakRvwmoLin2.lean:997-1037`**, **`Weak/WeakRvwmoFabInd.lean:443`** — the Supply family gains `devQuiet p` (S),
  the Fab family the interim clause (S–M) [R17.3][R18.2], **`Weak/WeakEvCapstone.lean`**
  (`:645-664`, `:936`, **`:1183`** `wpBehaviorFulfilOnceDev … pdevEvOk`), `Weak/WeakEvPf.lean` (`ediskStepLabel :711`,
  `ediskStepEra :423`), `Weak/PfStepTsoMem.lean`/`PfStepTsoView.lean` (`pfDWriteRowMem :669`/`rowDiskWrite :797` gain the
  fabric-delta variant and the `LSilent` skip arm, S), `Weak/TsoShadow.lean` (`diskLatOk`/`candDiskLat` UNCHANGED in text
  — the disk row's loads are now one 16-byte `LLoad` per descriptor), W13 (T)'s (R2′)/disk-row anchors (LANDED
  `GraphFabResidue.lean:84`, UNCHANGED in text: they range over disk-row READS; (R1)'s disk sentence in §A(†) becomes
  "DMA writes are gmo-before the used-idx write", the COMMIT event being gone), W13 (I)'s `gfDev` text ([OWN.31];
  mechanism (iv)).  **Size L–XL** (owner's class; **unverified**: ≈ 1.8–2.8k touched — rev 19's 1.5–2.5k + the
  `pdevEv`/devfree re-proofs S–M [R16.1] + the `devQuiet` threading S–M [R17.3] + R18's four and R19's three corrections
  — all S text on the brief, the `gfexecConf` interim clause S–M [R18.2]; class unchanged; W4 F9's `R-dev` SIMPLER).  **Deps**: W13 (E) ✓ (payload `LDev`), W13 (T)+(M) ✓ (MERGED — (T) reads
  `pdiskProg` only through (R2′)'s text; (M)'s `gmem` sweep is landed, so no live conflict on `WeakEvInst`/
  `WeakEvCapstone`/`WeakRvwmoSupply :164-175` [R16.s4], nor on `WeakRvwmoFab.lean :344-503, 689-842`/`WeakRvwmoLin2.lean
  :997-1037`/`WeakRvwmoFabInd.lean :443` [R17.3] — a REBASE on the merged tip, not a merge serialization; W13 (I), which
  later edits `Fab :318-503`, rebases on W-DISK's `devQuiet` restatement), W5b′ ✓;
  NOT W2 CLOSE (the disk rows of W2a/W2b are re-stated by W-DISK itself); NOT W-DMA0 (DONE; the pf side ELIDES the
  zero-length node [R20.2]).  **Sequencing**: BEFORE W4's F9 and BEFORE W13 (I) (the fabric-move
  interface and the state-aware `pdevEv` are (I)'s inputs); beside W4 F1–F8 (F1's disk part is an abstract parameter),
  W2 CLOSE, W11 (iv)b, W-DMA0 (different lanes).  **Acceptance**: `lake build Weak` green, `--weak` audit unchanged (no
  new axiom), no `DWild` constructor, arm or lemma left in `Weak/` and its header prose rewritten (`WeakEvInst.lean:33`,
  `VirtioProg.lean:48,76,148` mention it in comments, so a bare `grep DWild` would fail) [R23.s5], **`pdevEvOk` re-proved against the state-aware `pdevEv` and
  `WeakEvCapstone.lean:1183` unchanged in statement**, `devQuiet`/`devQuietStep` NAMED and discharged at `epsInit`
  [R17.3], **`gfexecConf`'s interim `LDev`-free `.PDisk` clause NAMED with a "deleted by W13 (I)" comment and
  `xv6RvwmoSafeModuloF :228` still building [R18.2]**, `DWriteDev`'s `pre` opening with the in-flight pre-check and
  `pa`/`bs` state-dependent [R18.3][R18.4], **`drainAll` in the used-element `pre` with `completeOk` VERBATIM (no
  `completeOkPf`), `R-dev` as FULL `dvirtio` equality + `cache = []` outside capture → gate, `DWriteDev`'s state-receiving
  continuation with the idx write's `ui`/`c` conjuncts KEPT, `DPop` named, `pre₁` conditional — all written into the header
  [R19.1]–[R19.3]; `pre₁` = the truncated status `pre` (reset-absorbing) [R20.1]; the zero-length data node elided,
  `DmWf`'s `n ≠ 0` kept, no `n = 0` disjunct in (M5′) [R20.2]**, the header's "Deviations from Rocq" rewritten as **"Deviations from MachCSL's `serve`: the DM encoding, the
  folded guards ([R17.1]'s FOLDING RULE: own guard → skip, `DevM.guard` → abort), and SEQUENTIAL single-request service
  (no `fork`; §B(11) (viii)); ONE pf-only node: the `DFence` before the used-idx write (`dusedTail`, `VirtioProg.lean:586-589`;
  0 MachCSL steps — `serve` goes `:546` → `:552` directly), on which §A(†)'s rule-4 ordering of (R1)'s disk use rests"**
  [R17.4][R23.s2] with the (M1)–(M9) table and marks, **plus a "moves the fabric?" column per node
  [R22.s4]** (START — a `gfDev` member by CLASS, its own step keeps `d' = d` (`WeakEvInst.lean:488`) [R23.s1] —, POP, IN fill (its `pre` carries `:526`), status, used element, used idx: YES; the `DRead`s, `DFence`,
  `DStall`, `DRet DIdle`: no — W13 (I)'s `gfDev` set is read off exactly this column, §A(†)) (incl. the gate-time drain note
  [R16.s3][R19.1]: pf's durable image equals MachCSL's at every pf-step boundary); `notes/weak-port-architecture.md` row
  `VirtioProg` closed.
  **Mark of the whole**: MORE FAITHFUL to virtio than today's pf (used `len`, FLUSH, no wild writes); the verified SC
  driver proofs UNTOUCHED ([OWN.29]'s stated merit); the ONE device model is then MachCSL's, §0 F1/§B(11)'s pf-drift
  entry is deleted and MachCSL's own device-model choices stay listed in §B(11) [R16.5]; the one NEW device-internal
  graph event per request (the pop) is named [OWN.32].
- **W5 `Weak/SrvwmoXv6Adequacy.lean`** (M) [R1.5][R2.1][R3.1][R3.s2].  **M1 is STATED THROUGH `srvwmoXv6M1Premises
  σ0 c pst dv`** (never a re-listed premise set; satisfiable by `srvwmoXv6M1Satisfiable`): **W5-pre — DONE [R16.4]
  (`Weak/SrvwmoXv6Witness.lean` only, 805 lines)**: the DEFINITION `:599-607` is over W5b′'s clauses (`execProgOk'ST`
  with `cohSrc`, `candScaT`, `candDiskLat`; the shadow-threaded replay `execWfPfRunPinShapedT`), `srvwmoXv6M1PfRun
  :624-633` is a `pfRunST` run with the projection lemma, `srvwmoXv6M1Satisfiable :733` (the `_entry` GOT load at `t =
  0`, one hart: `candScaT`/`candDiskLat` trivially, `execScaTOne`) [W4c D1, R5 CLOSED]; then W5 proper:
  `srvwmoXv6M1PfRun` gives the shaped run; W4 projects (W5 DISCHARGES W4's HSafe from
  `xv6FsAdequacy_closed`'s `Reducible` conjunct, E-S1, and the boot bridge's `g0`/`g1` from the premise's `ds`);
  `xv6FsAdequacy_closed`, `xv6NiAdequacy`, `unionAdequacyClosed` (`Xv6/LinkUInitUnion.lean:163-164`), W3's root
  `xv6TextAdequacy_closed` ✓ and W1b (`allocprocTraceAns :402`, DONE) conclude; `κs` is W4's `pfObsOf` (E-S3).  Header:
  internal milestone, kernel-only by PREMISE (D21), loads SCA at or above the TsoMem floor by premise `candScaT`,
  `sailCycleOrder` a named premise [OWN.35] (removed from M1 by W-SCO).  Registered per §B(12) ONLY at M1's CLOSE
  [R21.4].  **Rev 24 split — W5
  CORE launchable NOW, M1 CLOSES after F9**: W5 CORE instantiates `MachOfPf.Hyps` (`MachOfPf.lean:620`) for `fok =
  candKfetch bcRoLo bcRoHi`: `tso` by `pfStepTsoProposed`, `safe` (HSafe) from `xv6FsAdequacy_closed`'s `Reducible`,
  `cut` by `cutOfPristine :1588` whose `winPristine :1559` hypothesis it proves for every reachable powered state from
  `Xv6.powerInterp_textPristine` (`Xv6/TextPristine.lean:123`, through the W3 twin `riscvPowerAdequacyT`) — W4's OPEN
  item (a); **[R22.s3] instantiations**: `safe` = `(xv6FsAdequacy_closed g0 rfl rfl hdisk n κs t g hsteps).1` with `g0.gen =
  0`, `g0.pow = false`, `diskOf g0.m.devs = fsImgDisk` from the premise's `ds` (`Xv6/LinkSystemAdequacyClosed.lean:20-26`);
  `winPristine` from `(xv6TextAdequacy_closed …).2 : g.pow = true → textPristine g` (`Xv6/LinkTextAdequacy.lean:26-35`) read
  through `textWin_get` (`Xv6/TextPristine.lean:42`) for every `pa ∈ [bcRoLo, bcRoHi)`; `cutOfPristine :1588`'s `hlo : ramBase
  ≤ lo`/`hhi : hi ≤ ramEnd` from `bcRoLo := ramBase`/`bcRoHi := _data` (`Xv6/BootCarve.lean:143-144, 153`); `fi` from the DEFINITION `sailCycleOrder` (W5 states it in the label-list form of §B(11) and derives
  `Hyps.fi` by a one-fold lemma over `shStepF` [R20.s4][R21.s1]); `disk` an
  EXPLICIT hypothesis of the CORE theorem (F9's interface), so W5 CORE must consume `machRunOfPfRun` only through
  `MRun`/`pfObsOf` and NOT unfold `SimRel`'s device clause (F9 changes it).  NO disk-free M1 variant (§C top: M1's runs
  contain disk-program steps).  **[R21.4] W5 CORE's theorem is CONDITIONAL on `Hyps.disk`, which is UNSATISFIABLE until F9
  lands (W-DISK DONE 2026-10-12 removed the first obstacle — the aligned program's used element is ONE 8-byte `DWriteDev`,
  `VirtioProg.lean:394` `dusedTail`, matching MachCSL's `dmaWriteIf`, `Virtio.lean:546-548`; what remains is F9's `R-dev` —
  full `SimRel.dev` equality fails on the OUT capture segment, [R20.1], `preCaptureHead :338`).  It is PLUMBING, NOT a milestone: NOT registered in
  `roots-weak.txt`/`baseline-weak.json`, not counted in status %; its acceptance = the four discharges (`tso` by
  `pfStepTsoProposed`, HSafe and `winPristine` from `xv6TextAdequacy_closed`, `cut` by `cutOfPristine`) + the statement
  checked to use `SimRel` only through `MRun`/`pfObsOf`/`cutOfPristine`'s three fields (`pow`/`mem`/`auth`).  M1 is
  registered and reported only when F9 discharges `Hyps.disk`.  W5 CORE also corrects `MachOfPf.lean`'s header deviation 3
  ("its owner is OPEN", `:58-60`) to [OWN.35].**  Deps: W1b ✓, W3 ✓, W4 F1–F8 ✓, W5b ✓ + W5b′ ✓ + W5-pre ✓, W5c ✓, W-DMA0 ✓; the CLOSE:
  F9 (W-DISK).
  **[rev 31] W5 CORE DONE and ADAPTED to F9 (merged 2026-10-12 10:47) — `Weak/SrvwmoXv6Adequacy.lean` (318 lines, `Weak.lean:634`
  after the import-hygiene fix).**  The theorem **`srvwmoXv6M1Core :276`** (§A M1 paragraph): hypotheses `srvwmoXv6M1Premises σ0 c
  pst dv`, `g0` with `g0.gen = 0`/`g0.pow = false`/`σ0.wgdev = g0.m.devs.reset`/`diskOf g0.m.devs = fsImgDisk` (`bootStateOf :217`
  builds one from the premises' `ds` — never vacuous), `sailCycleOrder :113`; conclusions = the shaped `pfRunST` run + `pairAdjacent`
  + the W5-pre projections, `contR`/`recLabels`, the MachCSL `MRun` and `SimRel`, and `xv6Concl :252` (`Reducible`, `xv6TracePure`,
  `xv6NiPhi`, `unionPhiSync`, `textPristine g` via `SimRel.pow`, `allocprocAns :230`).  Discharges (`m1Hyps :203`): `tso` =
  `pfStepTsoProposed`; `safe` = `(xv6FsAdequacy_closed g0 …).1`; `cut` = `cutOfPristine bcRoLo bcRoHi` with `winOfText :187`
  (`(xv6TextAdequacy_closed …).2` read through `textWin_get`) and `bcRoHiLe :198` (`_data ≤ ramEnd` by `decide`); `fi` =
  `fiOfSco :163` from the one-fold lemma `fiArmLastCyc :135` (`(tsoShadow stamp st i).fiArm = fiOf (lastCyc i st)` under every
  stamp) — the [R21.s1] label-list form, `lastCyc :104`/`lbCyc :96`; the disk rows are F9's `simDisk`, no longer a parameter.
  Deviations (header): (1) `MachOfPf.lean`'s deviation 3 was corrected by F9, not W5 (`PfStepTsoView.lean`'s deviation (4) is left to
  the CLOSE-OUT); (2) `diskRows`/`DR`/`m1Hyps.disk` DELETED; (3) `allocprocAns` is a COPY of `allocprocTraceAns`'s conclusion
  (proved by `exact`).  Axioms = `xv6FsAdequacy_closed`'s (its cone + the 4 `bv_decide` certificates of the NI/union/text roots),
  printed at the file's end; `lake build MachCSL Xv6 Weak`, lint, `audit.sh --weak` green.  **M1's status against this plan's
  definition** (§A "M1 = the composed sRVWMO theorem, pinned/kernel-only"; §C top "M1 CLOSE = W5 CORE's theorem with `Hyps.disk`
  discharged by W4 F9"; [R21.4] "registered and reported only at F9"; §B(12)): the THEOREM is exactly M1 — PROVED; it is NOT yet
  CLOSED because nothing registers it: `tools/ci/roots-weak.txt` lists the ten AxSpin roots only, `tools/audit/baseline-weak.json`
  has no `srvwmo` entry, `XV6_AUDIT_MODULES` (`tools/ci/audit.sh:44`) lacks `Weak.SrvwmoXv6Adequacy`, and the file header says "NOT
  registered as a root here; the orchestrator registers M1".  No premise is unproved besides `sailCycleOrder`: the `g0` facts are
  constructible, the premise set is satisfiable (`srvwmoXv6M1Satisfiable`), and `candKfetch`/`candScaT`/`candDiskLat` are the
  candidate RESTRICTIONS that DEFINE M1 (D20/D21 — kernel-only and SCA/latest BY PREMISE; derived or replaced at Stage 2/M2), not
  facts awaiting proof.
- **W5 CLOSE-OUT — the registration of M1 (S; NEW rev 31; `tools/` + two file headers, NO theorem change; launch NOW, any lane —
  it touches no Lean statement).**  (1) `tools/ci/roots-weak.txt` gains `Weak.srvwmoXv6M1Core` with the one-line gloss "M1 (INTERNAL
  milestone, NOT published [OWN.2]): the sRVWMO/kernel-only composition — every M1-premised shaped pf run is realized by a MachCSL
  run from the machine off on which `xv6FsAdequacy_closed`/NI/union/text/`allocprocTraceAns` conclude; premises `srvwmoXv6M1Premises`
  + `g0` boot facts + `sailCycleOrder` [OWN.35] (SrvwmoXv6Adequacy)"; (2) **[R28.1]** `tools/audit/baseline-weak.json` gains the
  entry `{ "name": "Weak.srvwmoXv6M1Core", "axioms": ["propext", "Classical.choice", "Quot.sound"], "opaques":
  ["LeanRV64D.Functions.xv6_resv_is_valid", "LeanRV64D.Functions.xv6_resv_matches", "MachCSL.bootImageSealed"] }` — EXACTLY
  `Xv6.xv6FsAdequacy_closed`'s `baseline.json` entry under the new name.  The `bv_decide` certificates are NOT listed: the `axioms`
  field is the exact set OUTSIDE the `<decl>._native.bv_decide.ax_*` family, which the audit counts and shape-checks
  (`Audit.lean:28-34,119-138`) and whose members it REJECTS as stale baseline axioms if listed (`plain := axs.filter (!isBvCertName ·)`,
  `Audit.lean:305-313`); `#print axioms` cannot see `opaque`s (`Audit.lean:41-53`), so the `opaques` list is required and
  `MachCSL.bootImageSealed` — in NO current `baseline-weak.json` entry (all ten list the two `resv` opaques only) — is new to THIS
  FILE but not to the trusted base (`baseline.json`, §0 F1): no deviation; `platform_hooks` (identical in both baselines: `realised` 6,
  `parameters` 2) unchanged; (3) `XV6_AUDIT_MODULES` (`tools/ci/audit.sh:44`) gains `Weak.SrvwmoXv6Adequacy`, and so does the
  `--build` module list (`audit.sh:51` — else a fresh `--weak --build` never builds it); COMMENT sites updated to match:
  `audit.sh:13-18` (header), `roots-weak.txt:1-7`, `baseline-weak.json`'s `comment`, `Audit.lean:85-95`; `tools/ci/lint.sh`
  (roots ↔ baseline agreement) and `tools/ci/audit.sh --weak` pass; (4) the D21 report
  wording, in `Weak/SrvwmoXv6Adequacy.lean`'s header ("NOT registered as a root here" → "registered in `roots-weak.txt`") and in
  the status report: **"M1 — composition milestone, INTERNAL (not published [OWN.2]): kernel-only by premise `candKfetch`, loads
  single-copy-atomic at or above the TsoMem floor by premise `candScaT`, disk-row loads latest by premise `candDiskLat`, under the
  named ISA-model premise `sailCycleOrder` [OWN.35] (W-SCO demotes it for kernel text); the disk rows PROVED (W4 F9), no side
  condition; the realizing MachCSL run satisfies `xv6FsAdequacy_closed`'s conclusions, `xv6NiPhi`, `unionPhiSync`, `textPristine`
  and the allocproc shadow; axioms = the SC roots' + 4 certificates; non-vacuity: `srvwmoXv6M1Satisfiable` (QUIESCENT, D22/D44)"**;
  (5) `Weak/PfStepTsoView.lean` header deviation (4) (`:64-66`: "both facts of the step list's instruction structure, W4's to
  supply") → "facts of the Sail cycle's event order, the named premise `sailCycleOrder` [OWN.35] (`Weak/SrvwmoXv6Adequacy.lean`,
  derived for the shadow by `fiOfSco`); `sailCycleOrderK_holds` (W-SCO, `Weak/SailCycleOrderK.lean`) proves it for kernel text" —
  **[R28.3] this wording ANTICIPATES W-SCO, which does not touch the header again**; (6) status counting: M1 counts from this item
  on ([R21.4]).  Acceptance: `lake build MachCSL Xv6 Weak`, lint, `audit.sh --weak` green with the new root; the two headers edited;
  no statement changed; **[R28.1][R28.s1]** the status line quotes `audit.json`'s `bv_decide_certificates` count for
  `Weak.srvwmoXv6M1Core` (`Audit.lean:393`: the 4 NI/union/text certificates + the SC cone's own — not literally 4) in place of
  "+ 4 certificates".  Deps: none; **lands FIRST of the four lanes [R28.3]**.  **W-SCO** then registers its corollary `srvwmoXv6M1`
  beside it as its CLOSE step (both stay: the core keeps the general premise, the corollary is the kernel-text instance).
  **[rev 35] DONE → M1 DONE (2026-10-12) — [R32.1] was VACUOUS until W-SCO (A)'s first commit — LANDED rev 39, non-vacuous (`hsco` was refutable: a fetch from MMIO
  of an SFENCE.VMA word under an arbitrary `pma_regions`; the registered entry — axioms/opaques — is unaffected; the content is restored by
  the restatement under `wbootFacts σ0`, §C W-SCO (A) commit 1).**  `tools/ci/roots-weak.txt:20` (`Weak.srvwmoXv6M1Core`, the gloss above), `tools/audit/
  baseline-weak.json` (entry EXACTLY [R28.1]'s: 3 axioms, opaques = the two `resv` + `MachCSL.bootImageSealed`; `platform_hooks`
  unchanged), `tools/ci/audit.sh:47` (`XV6_AUDIT_MODULES` ends in `Weak.SrvwmoXv6Adequacy`) and `:54` (the `--build` list); comment
  sites `roots-weak.txt:1-9`, `baseline-weak.json`'s `comment`, `Audit.lean:85-98` — **[R29.s3] CLOSED**: the module list is written
  ONCE (`audit.sh:47`), the comments say "`Weak.AxSpinT2b,...,Weak.AxSpinT2q4,Weak.SrvwmoXv6Adequacy` (the list in `tools/ci/audit.sh`)";
  `Weak/SrvwmoXv6Adequacy.lean` header: "registered in `roots-weak.txt`" (`:8`); `PfStepTsoView.lean:66-67` deviation (4) names
  `sailCycleOrder` and `sailCycleOrderK_holds` (W-SCO (A) renames the latter to `sailCycleOrder_holds` at its CLOSE [OWN.42]);
  `SrvwmoXv6Adequacy.lean` is now 331 lines (`sailCycleOrder :126`, `fiArmLastCyc :148`, `fiOfSco :176`, `m1Hyps :216` — its `fi :226`
  adapted to W-SCO (0)'s widened shape —, `srvwmoXv6M1Core :289`); status counting: M1 counts from here.  Under [OWN.42] the corollary
  `srvwmoXv6M1` is M1 WITHOUT `hsco` for ALL text (not "the kernel-text instance"); the core keeps `hsco` and its registration.

- **W-SCO — `sailCycleOrder` PROVED for xv6's kernel text (NEW rev 24, Q-FIARM RULED (b)+(a′) [OWN.35]; AFTER M1 — **M1's core
  LANDED 2026-10-12, so LAUNCHABLE NOW [rev 31]** on the `Weak/` lane; M–L, unverified).**  **Shape (rev 32, binding)**: a NEW file
  (`Weak/SailCycleOrderK.lean`) + `Weak/MachOfPf.lean` (one field, one application site, one factored lemma) + ONE line of
  `SrvwmoXv6Adequacy.lean` (its root `srvwmoXv6M1Core` keeps the general premise, its STATEMENT and its registration): **(0) [R28.2]
  `MachOfPf.Hyps.fi` is WIDENED to the `cut` shape** — it gains `∀ t g n κ, MRun n ([Expr.power], g0) κ (t, g) → SimRel c st t g →`
  before the node quantifier (`MachOfPf.lean:672-680`; today `fi` quantifies the pf run and the node ONLY, unlike `cut :664-671`); the
  single application `:1035` passes `hreach hR0`, both in hand (`:1043` already passes them to `cut`); `m1Hyps.fi`
  (`SrvwmoXv6Adequacy.lean:213`) becomes `fun st c _ _ _ _ hrun _ _ => fiOfSco hsco _ σ0 st c hrun` — the ONLY edit to that file (a
  one-line adaptation; `srvwmoXv6M1Core`'s statement unchanged by W-SCO [R30.s4] — and, as W5d DELIVERED its threading through
  generic twins, unchanged in TEXT by W5d too, §C W5d [rev 35]).  WHY: as briefed at rev 31 the per-word lemma had no handle on WHICH
  word was fetched — `candKfetch lo hi _img _log _i base tvs := ∀ j < |tvs|, lo ≤ base + j < hi` (`PfRunShape.lean:53-55`)
  constrains the ADDRESSES only, while the pf fetch's bytes are `ifetchOk (imgZ σ.wgimg) σ.wglog (σ.wgitv c) base tvs`
  (`WeakEvInst.lean:631`; `WeakPromise.lean:225`) — image bytes at `t = 0` OR log bytes of any pf store into the window; "no pf store
  ever hits `[bcRoLo, bcRoHi)`" is the SC tree's `textPristine`, which reaches the pf side only through `SimRel`; and the restriction
  is load-bearing for (a′) — the barrier clause needs "`execute (decode w)` emits no fetch before its `Barrier_RISCV_i`" for the
  ACTUAL `w` (generically over all `w` is option (a), L–XL, §B(11), not taken).  (i′) `sailCycleOrderK : Prop` := `sailCycleOrder
  :113`'s body RESTRICTED to runs `pfRunST pstepEv pclsEv (candKfetch bcRoLo bcRoHi) cohSrc (wpInit (imgZ σ0.wgimg) …)` with
  `wbootFacts σ0`, stated WITH the `MRun`/`SimRel` premises (`g0` as in `m1Hyps`, `winPristine bcRoLo bcRoHi g` from `winOfText
  :187`) — the general `sailCycleOrder` quantifies over EVERY `fok`, hence over user text, NOT what W-SCO can prove; (ii)
  `theorem sailCycleOrderK_holds : sailCycleOrderK` — the per-word lemma over EVERY 2-aligned 4-byte word of `[bcRoLo, bcRoHi)`
  [R21.s2] below, CONNECTED to the node through **`cutOfPristine`'s argument** (`MachOfPf.lean:2925-2950`: `SimRel.mem`'s history
  link `hR.mem.2.2.1.1` + `winPristine` + `histNoWrite` ⇒ every fetched byte has `t = 0`, hence the announced word is `imgZ
  σ0.wgimg`'s word at `base` = the image word by `wbootFacts` (`WeakLang.lean:483`, `wgimg = bootImage`)) — factor that step out of
  `cutOfPristine` as a lemma **`fetchIsImage`** (S) both use; **[R28.s2]** the per-word lemma is word-INDEPENDENT except at the
  barrier clause: the sfence.vma clause ("latest own cycle label is `LIFetch` at the announce") holds for ANY word (fetch → announce
  with nothing between, `UCycleDefs.lean:11-17`), only the barrier clause needs the decoded instruction — split the SailM residual
  invariant (the risk below) into a GENERIC half and the per-word half; the generic half is what the general `sailCycleOrder`
  still covers for user text (W5d-G/M2); **[R28.s3]** window size: `[ramBase, _data)` holds `.text`, `.rodata` and `.eh_frame`, ≈
  (`_data − 0x80000000`)/2 word instances — two orders of magnitude beyond the precedent (`AxSpinTextCerts.lean`, 245 lines, 92
  conjuncts by `decide +kernel` over the literal image), so the brief's choice is a **per-instruction-CLASS lemma over `decode`**
  (one lemma per opcode family that can appear; a GENERATED table proves class membership only), the all-words `decide` table the
  recorded fallback; (iii) `fiOfScoK` := `fiOfSco :163` restated from `sailCycleOrderK` for `fok = candKfetch …` under the widened
  `fi` shape (S; `m1HypsK` needs no `hsco`); (iv) **the corollary `srvwmoXv6M1`** = `srvwmoXv6M1Core`'s statement WITHOUT `hsco`,
  proved by re-running the composition with `m1HypsK` (not by `srvwmoXv6M1Core hsco` — the general premise is not available).
  **Landing order [R28.3]**: the `Hyps.fi` widening (0) is W-SCO's FIRST commit (independent of the per-word work) so W5d's `m2Hyps`
  builds on the new shape from the start (W5d's `fi` discharge from the general `sailCycleOrder` ignores the extra premises); the
  registration — `roots-weak.txt`/`baseline-weak.json`/`audit.sh:44,51` gain `Weak.srvwmoXv6M1`/`Weak.SailCycleOrderK` beside the
  core (same `axioms`/`opaques` entry as the core's [R28.1]; the per-word lemma's `bv_decide` certificates are COUNTED, not listed;
  NO new opaque) — is W-SCO's CLOSE step, rebased on the merged W5 CLOSE-OUT; W-SCO does NOT edit `PfStepTsoView.lean`'s header (the
  CLOSE-OUT's wording already names `sailCycleOrderK_holds`).  Q-FIARM's (a′): the cycle is `ucDispatch` → `fetch ()` → `ucAfterFetch fr` by equations
  (`MachCSL/UCycleDefs.lean:11-17`, `uc_runHartActive_eq`), whose first event after the fetch is the announce
  (`Step.lean:340/:377`); the "no fetch during execute" half per decoded instruction, for the words M1's runs can execute
  — **[R21.s2] EVERY 2-aligned 4-byte word of `[bcRoLo, bcRoHi)`**, which includes `.rodata`/`.eh_frame`
  (`Xv6/LinkTextAdequacy.lean:8-9`): HSafe does not confine the pc to `.text`, so data decoded as instructions is in scope;
  the plan's choice is this whole-window per-word lemma (precedent: Q22's 2-aligned `textAt4S`, `AxSpinTextCerts`), NOT a
  new pc-in-`.text` export from the SC tree (recorded alternative).  Delivers `sailCycleOrder` restricted to
  `candKfetch` runs as a THEOREM, M1 loses the premise; M2 and §A's statement KEEP it for user text (any instruction)
  unless option (a) (all of `execute`, L–XL) is later taken — §B(11).  `PfStepTsoView.lean`'s header deviation (4) is
  corrected by the W5 CLOSE-OUT's wording [R28.3].  Risk: a `SailM` residual invariant between the announce and the barrier
  node (new machinery; generic/per-word split per [R28.s2]).  **NOTE (rev 33, added while running; the brief above is unchanged)
  [R29.s1]** `fetchIsImage` is about a PAST step: `cutOfPristine`'s `hnw`/`ht0` argument (`MachOfPf.lean:2922-2956`) is at the
  CURRENT step's pre-configuration, while the barrier clause needs the latest own `LIFetch base tvs` INSIDE `st` at a later node.
  Recipe: (a) `pfRunSTFacts` (`TsoShadow.lean:599-620`) on `st = st0 ++ (hartAgent cpu, .LIFetch base tvs) :: rest` gives `c1` and
  the fetch's `wpPfStep` (hence `ifetchOk c1.pcImg c1.pcLog _ base tvs`, the `PFIFetch` arm) at the prefix; (b) a `pclsEv` log
  lemma "`pfRunST pstepEv pclsEv … c1 st' c → c1.pcLog <+: c.pcLog ∧ c1.pcImg = c.pcImg`" (S; `pfRunSLogK :845` needs a CONSTANT
  class function and `pclsEv` is not one, `pclsEvEqr` — induct on `wpPfStep` directly, or read it off `SimRel.auth`/`stAuthors`);
  then `hnw` at the final `c` (`SimRel.mem` + `winPristine`) transfers to the prefix log and `ht0` gives `t = 0` per byte, so
  `tvs`'s bytes are `logByte img _ 0` = the image's.  State `fetchIsImage` once over "a fetch label at any position of `st`" so
  `cutOfPristine` is its `rest = []` instance.  **[R29.1]** landing order: W5d's `fcutT` parameter threading (§B(4)(iii), §C top)
  lands after the `Hyps.fi` widening and before `sailCycleOrderK`/`srvwmoXv6M1` are stated; if late, state them over the current
  `pfRunST` type and W5d adapts (S).
  **[rev 35] RESULT + RELAUNCH on route (A) [OWN.42] (`../weak-orch/parked/PROGRESS-WSCO.md`).**  Shape (0) DONE and MERGED:
  `Hyps.fi` widened to `cut`'s shape (`HypsC.fi :703-715` after W5d's merge [R32.s1]; the one application site passes `hreach hR0`, `:1102`),
  `fetchIsImage :3009` factored out of `cutOfPristine :3028` plus `noWriteOfPristine :2982` (`SimRel` + `winPristine` ⇒ no log message writes a window byte),
  `m1Hyps.fi` the one-line adaptation (`SrvwmoXv6Adequacy.lean:226`), `srvwmoXv6M1Core`'s statement unchanged; `lake build`, lint,
  `audit.sh --weak` green.  GENERIC half DONE and MERGED — `Weak/SailCycleOrderK.lean` (631 lines, not registered, imported `Weak.lean:635` [R32.2]):
  `sailCycleOrderK :92` ((i′) exactly as briefed, over the current `pfRunST` type), **[R29.s2] CLOSED** — the SailM residual invariant is
  `SailCycleOrderK.good A Q ph m :139` (an all-paths predicate on a Sail tree started at cycle PHASE `ph` = the latest own `LInstr`/`LIFetch`,
  mirroring `pnodeStep`'s dispatch: an ifetch RAM read continues at `.fetch` for answers the fetch filter `A` admits, any other read at the
  same phase, a `Barrier_RISCV_i` REQUIRES `.instr`, an SFENCE.VMA announce REQUIRES `.fetch`, any other announce continues at `.instr`;
  kit `goodBind :174`/`goodMono :196`), `cycleOk :219`/`kWin :224`/`cycleOkK :229`/`cycleOkAll :232`, the run invariant `inv :264`/
  `invStep :359`/`invRun :430` (all `pnodeStep` arms, parked fence, PLIC wire, other agents) and `scoOfInv :450`; **the reductions**
  `sailCycleOrderKOfCycle :536 : cycleOkK → sailCycleOrderK` ([R29.s1]'s recipe landed as `stepLogPrefix :478`/`cleanK :496`/`fetchK :515`:
  the final log is clean by `noWriteOfPristine`, logs only grow, `fetchIsImage` gives timestamp 0) and **`sailCycleOrderOfCycle :470 :
  cycleOkAll → sailCycleOrder`** (the GENERAL premise from the tree fact for every word); (iii)/(iv) `fiOfScoK :554`, `m1HypsK :578`,
  `srvwmoXv6M1OfK :593`.  **The per-word half (ii) AS BRIEFED is WITHDRAWN.**  *Spec first.*  Sail `Fetch.lean:252-280`: with `Ext_Ziccif`
  (`Extensions.lean:528`) a 4-aligned pc is ONE 4-byte read, but at `pc ≡ 2 (mod 4)` the cycle fetches the low halfword at `pc` and — if
  not compressed — the high halfword by a SEPARATE `fetch_bytes pc (pc+2) 2` (`:217-226`, its own `translateAddr`), announcing `ihi +++
  ilo`; in the pf model each translation's PTW reads are ordinary `LLoad`s and `candKfetch` (`PfRunShape.lean:53-55`) constrains ADDRESSES
  only, so the announced word is `image[pa'..pa'+2) ++ image[pa..pa+2)` for two independently translated 2-aligned window addresses
  (`pa' = pa + 2` NOT implied: page crossing at `0x80003ffe`/`0x80009ffe`, a TLB miss reading a different PTE value); RVWMO/Zifencei/PMAs
  silent; the ISA agrees (a page-crossing instruction may fault on either page).  Consequences: "every fetched byte has `t = 0`, hence the
  announced word is the image's word at `base`" is FALSE on that arm (two `LIFetch` labels, two bases); the [R21.s2] set misses the words
  the cycle can announce (`lo` ∈ the 5154 window halfwords with low bits `11`, `hi` ∈ ANY window halfword — millions of pairs, 31 of 32
  major opcodes), so per-class coverage ≈ every 32-bit `execute` clause anyway; "execute emits no announce" is a per-word obligation too
  (an `instrAnnounce` inside `execute` would violate the sfence.vma clause).  *Options (marks vs RVWMO/Sail/Zifencei/PMAs)*: **(A) prove
  `cycleOkAll` for EVERY instruction** — FAITHFUL (the Sail fact, no restriction), STRONGER than W-SCO as briefed: discharges
  `sailCycleOrder` itself (`sailCycleOrderOfCycle`), M2 and §A lose the premise too; L ≈ 1.5–3k (spike `PROGRESS-WSCO-spike.lean.txt`:
  the `good` CPS kit, the `ncT` footprint, `nct_auto` walking `pmpCheck`/`pmaCheck`/`execute_JAL`); **(B)** per-class over the TRUE word
  set — FAITHFUL, no cheaper than (A), proves less; **(C)** pin the second halfword to `pa + 2` by a TLB-register residual invariant —
  FAITHFUL, L+, fragile (the fill policy, every `translate` outcome), the two page-crossing positions still need (B); **(D)** a candidate
  restriction "the two halves of a split fetch are adjacent" beside `candKfetch` — WEAKER than Sail (excludes runs the model has), M1's
  statement changes; not recommended.  **[OWN.42] RULED (A)** (13:59 2026-10-12; §D Q-SCO-words).  **[R32.1] (rev 36): `cycleOkAll` and `cycleOkK` are FALSE as defined and
  `sailCycleOrder :126-137` FALSE as stated** — an instruction fetch from a device address is an `LDev` step under an arbitrary
  `pma_regions` (`pnodeStep` `WeakEvInst.lean:315-321`), so a hart can announce `sfence.vma` with `lastCyc = some .LInstr`;
  `sailCycleOrderOfCycle`/`sailCycleOrderKOfCycle` were sound with FALSE premises; M1/M2 VACUOUS until the restatement under `wbootFacts σ0`
  (Q-SCO-PMA (α), RULED [OWN.45]) landed as W-SCO (A)'s FIRST commit — **LANDED rev 39**.  **Remaining work = the rev-36 launch paragraph at §C top — LAUNCHED 2026-10-12 (w4) — DONE and MERGED 2026-10-12 [rev 39] (the landed form is recorded there: `cycleOkBoot_holds`, `sailCycleOrder_holds`, `srvwmoXv6M1` REGISTERED, `srvwmoXv6M2` stated)** (commit 1 =
  the restatement, `good`'s register filter `Rboot` pinning `pma_regions = bootPMA` AND `htif_tohost_base = none` [R33.1], the `bootPMA`
  executability lemma and the `within_mmio_readable`-false-on-RAM lemma; deliverables (1) `cycleOkBoot_holds` — shared-piece
  footprints incl. `tick_clock`/`run_hart_waiting`/the `ExecuteAs` redirect [R32.4], 122 `execute_*` lemmas, `fence.i`/SFENCE.VMA by hand,
  the instruction-independent cycle —, (2) `sailCycleOrder_holds`, (3) `srvwmoXv6M1` and `srvwmoXv6M2` [R32.s4] by direct application,
  (4) registration; files, rebase surface, acceptance, risks); `sailCycleOrderK`/`srvwmoXv6M1OfK` become REDUNDANT (worker's choice at the CLOSE).
  Consequences recorded in §A (statement + (6)), §B(11) and Q-FIARM: `sailCycleOrder` IS a THEOREM for kernel AND user
  text (rev 39); `srvwmoXv6M2` = `srvwmoXv6M2Core … sailCycleOrder_holds` is stated, REGISTERED at M2 CLOSE (rev 40, §C top).  Everything above the ruling (shape (0), the
  generic half, the reductions) is option-independent and LANDED.
- **The SERIAL MachCSL items — all RULED, no gate left [OWN.21]–[OWN.23][OWN.30][OWN.36][OWN.37] (one worker at a time;
  one `Xv6`-cone rebuild each, W8 (f2-ctx) 3–4): **W-COH ✓ → W-DMA0 ✓ → W8-β′ ✓ → W-RSV ✓ → W8 (f2-ctx) (LAUNCHABLE, rev 37) [OWN.41][R28.5]**
  (M1 — W-RSV's gate marker, NOT a MachCSL item — closed in parallel, §C top; W8 (f2-ctx) waits for W-RSV and rebases on its
  `resvFragAny` thread at `ctxTok`, `Ctx.lean:298-299`) [R16.3][R21.1][OWN.37].**  **W8-β′** (M–L ≈ 1.3–2.3k [R26.2]; the
  reserved-region change — the era ghost `rsvName` + the static list `KernelRsv.static` registered at the `PowerOn` mint
  [R26.2-alt] — in `Resources.lean`/`Power.lean`/`PowerText.lean`/`WordHist.lean`/`Lock.lean`/`WpLock.lean`/`WpSmodeMint.lean`/
  `LockBornHook.lean`/`KCtx.lean` + the cpu-cell rule files, the `⌜staticIn reg ∧ reservedOk σ reg⌝` conjunct, the
  `powerInterp_accessDiscβ` extraction (the registration lemma [R26.1]) AND the (r2) twin
  `xv6DiscAdequacy_closed` at the provisional conjunction (the twin paid ONCE; ≈ +0.3–0.5k — its rebuild then buys a
  ROOT-level fact); ≤ 30 `Xv6/` files as `lkFresh`/`wordCell` become fraction-parametric (30 files [R25.s3]), ≈ 11 cpu-cell rule
  uses, the two `MachGS` literals and `Weak/WeakAdequacy.lean`'s; ONE rebuild;
  launches NOW — **RUNNING since 2026-10-12 10:26 [rev 31]; DONE and MERGED 2026-10-12 [rev 37]**) then **W8 (f2-ctx)** (**[rev 31][OWN.38][OWN.39] L–XL ≈ 6.5–9.5k** (was ≈ 4–6.5k after β′ takes the twin [R25.2]; [OWN.36]'s one-rebuild sizing SUPERSEDED by [OWN.37]): refines the CLEAN
  context key so it carries a sync chain — **a PER-AUTHOR vector bound `chain ξ : CPU → Nat` beside the unchanged scalar TSO floor,
  joined at each hop (F0, R-ctx §1; the scalar "every foreign entry `t ≤ bound ξ` is chained" is FALSE at one lock hand-off)** — in
  `Ctx.lean`, `CtxLaws.lean` (`ctx_unstamp :552`, `ctx_move :848`, `ctx_park`/
  `ctx_resume :760,788`, `ctx_stamp :520`, `ctx_absorb :479`, `ctxStamped_raise :577`), `Lock.lean`, `WpLock.lean`,
  `SwtchCtx`, `KCtxMove`, `CtxBox`, `LockBornHook`, `WpDma`, `WpDmaCtx`, `WpSmodeLwKey` + **`WpPtWalkOwn` ([OWN.39]: the user-table
  A/D write-back's dirty key becomes `pte`-exempt)** + the load rules' internals — **12** MachCSL files; **≈ 52 `Xv6/` files** = the 21
  that use the TSO-leaky/transport laws directly (incl. `ProofSwtch`, `PipeBirth` [R25.3]) + the 31 consumers of the hook/llb surfaces
  (R-ctx §5) + the 4 direct leaky sites outside the 21 (`IputParts.lean:461`, `ProofAcquiresleep.lean:809`, `StartedInv.lean:198,344`
  — in files already counted), the "up to 43 more through `ctxFloor`" (108 uses) now OVERLAPPING these and unchanged in meaning
  (the scalar floor keeps its semantics — beside-the-scalar form); **3–4 full-cone rebuilds**; gate R-ctx PASSED — (f1) list EMPTY,
  additions X1–X5 (§C W8 (4)); §C W8): the files W-RSV rewrites (`Resources.lean`, the load rules,
  `WpLock.lean`), so BOTH land before W-RSV, which rebases on them; neither shares a file with F9/W5 CORE (`Weak/`-only) —
  `MState`/`Lang.lean` are unchanged (W8-design §0 item 2), so W4's `SimRel` and W2a's `rmem` are untouched; if W8 is not
  done when M1 closes, W-RSV WAITS (recorded risk: the critical path moves — the more likely now, at 2–4 rebuilds).  **[rev 31] The
  risk MATERIALISED: M1's core landed 2026-10-12 while W8-β′ had just started** — under this order W-RSV (one rebuild) waits for
  β′ + (f2-ctx)'s 3–4 rebuilds, and M2 waits behind W-RSV; [OWN.36]'s recorded (α′) ("the same, after W-RSV: no collision; delays
  W8 by W-RSV's length — matters only if W8 becomes the bottleneck") is now the cheaper order for M2 → **Q-RSV-order (§D) — RULED
  (b) [OWN.41] 11:09 2026-10-12 [R28.5]: the lane is W8-β′ → W-RSV → W8 (f2-ctx)**; W-RSV launches when β′ MERGES (§C W-RSV
  "Launch (rev 32)"), (f2-ctx) rebases on W-RSV.  `Xv6/` NAMES neither reservations nor `coh` (census:
  `Xv6/*.lean` has no `othersReserve`/`blockedStep`/`resvMap`/`snapOf`/`cohOk`, only `SystemSlot.lean:64`'s comment on
  `mmOk`'s `resv_ok`) — true of NAMES, not of the FILES a statement change touches: W-RSV (i-a) changes the cycle rules'
  AND the 35 `wp_m_*` wrappers' statements and so edits 12 `Xv6/` files (8 apply a cycle rule directly, 3 apply
  `wp_m_*`, `SpecSpin`) [R12.1][R13.1].  Order: **W-COH first — DONE (merged 2026-10-11 09:23, build 3814 jobs,
  lint/audit/tcb ok)**, **W-DMA0 — DONE 2026-10-11** (option (A)), **W8-β′** (RUNNING), then **W-RSV** (when β′ merges; M1 ✓
  per D26; L–XL [R12.1]), then **W8 (f2-ctx)** rebasing on W-RSV — [OWN.41][R28.5][R29.2]; [OWN.37]'s earlier order superseded.  Rev 19's "(b) best folded into W-RSV's brief" is WITHDRAWN [R16.3]: W-RSV waits
  for M1 (D26), M1 = W5 needs W4 F9, F9 needs the `storeDma` change to prove `R-log` across a 0-length DMA write — so
  folding (b) into W-RSV puts F9 → M1 → W-RSV → (b) → F9 in a CYCLE.
  **W-DMA0 — `MState.storeDma pa 0 w` is a NO-OP (S, serial MachCSL — DONE 2026-10-11 via option (A) [OWN.34]; W-DISK-Q1
  RULED (b) [OWN.30]) [R16.3].**  *Landed:* `MState.storeDma` (`MachCSL/Lang.lean:181`, the case split inside the two
  moving fields) + `storeDma_zero :186`/`storeDma_of_ne :191`; `memModel_storeDma`/`machInterp_storeDma` (`WpDma.lean:69,
  149`) take `hn : n ≠ 0` — DEVIATION: the plan expected an `n = 0` case in them; (A)'s premise landed as a receipt-free
  frame obligation **`hzero : n = 0 → …`** (last argument, auto-filled at a non-zero numeral by `Nat.ble` + `rfl`, `omega`
  fallback) on `DevM.LeaseD.dmaWrite` (`WpDevDisk.lean:156`; zero-byte branch in the proof `:542`), `LeaseL.dmaWrite` +
  the `dmaWriteIf` helper (`WpDevDmaStep.lean:139,157`) and their `V` twins (`WpDevDmaStepV.lean:126,143`) — exactly the
  layer [R20.s1] named (the `Xv6/DiskInv.lean` sites apply `LeaseL`); the `Vtest` twin (`XState.lean:314-320`); NO `Xv6/`
  and NO `Dev/Virtio.lean` change.  The design record follows.  *Spec (owner rule, FIRST):* RVWMO's gmo is over "the primitive load and store operations generated by
  memory instructions" — a zero-byte access generates NONE; Sail has NO DMA model, and its own `mem_read`/
  `mem_write_value` take `width : Nat` with the Sail-source bound `0 < width` ERASED in the Lean export (the docstring
  keeps it: `model/Lean_RV64D/LeanRV64D/Mem.lean:494-496,612-614`); Zifencei/PMAs silent — (b) is FAITHFUL, the removal
  of a MODEL ARTIFACT (today's empty entry is "stronger" only as an extra empty timestamp).  *Change:* `MState.storeDma`
  (`Lang.lean:171-173`, an `abbrev`) or the `dmaWrite` arm (`:570-574`) gains the `n = 0 → σ' = σ.setDev d s'` case (no
  log entry, no history change); `Dev/Virtio.lean` and the driver proofs UNTOUCHED (the device still CALLS `dmaWriteIf`;
  only the memory model drops the empty append).  *Consumers to re-prove:* `Resources.mmOk_storeDma :862`; `WpDma.lean`
  (19 sites: `hartViews_storeDma :55`, `memModel_storeDma :64` — its `top`/`log` rewrites `:80-82` get an `n = 0` case,
  `machInterp_of_storeDma :118`, `machInterp_storeDma :142`); **`WpDevDisk.lean` — not "3 sites" but the DMA LEASE RULE
  itself [OWN.34]: `LeaseD.dmaWrite` (`:146-153`; proof `:522-560`, `storeDma` rewrites `:531, :544, :554`) promises that
  the footprint's histories GROW (`dmaWriteLease`, `WpDevDma.lean:46`: `pushed Hs t diskAgent w`, `authoredBy t`, `Kb <
  t`), which a no-op `storeDma pa 0` cannot deliver; likewise `WpDevDma.lean`'s `Lease.dmaWrite :139-142` /
  `lease_dmaWriteIf :158-162`.  RULED (A) [OWN.34]: those constructors gain the premise `n ≠ 0`, auto-discharged
  (`decide`/`omega`) at xv6's call sites (widths 1/8/2); fallback (A′) where a site's `n` is not syntactically non-zero —
  the 4 `Xv6/DiskInv.lean` constructor applications `:2164, :2750, :2828, :2855` (the fill's width is `(Chain.req
  c).len.toNat`, `:2172`, non-zero only through the chain's `len` fact — **unverified**)**; the `Vtest` twins (`vtest-lean/Vtest/
  XState.lean:315-320` `storeDma`/`abs_storeDma`, `DevExec.lean:77` — `tools/ci/vtest.sh check`); on the weak side
  `Weak/PfStepTsoView.lean` (6 sites: `sameReadStoreDma :155`, `rowDiskWrite :797-800`) ONLY — [R17.s2]
  `PfStepTsoMem.pfDWriteRowMem :669` is NOT a consumer (no `storeDma` in the file; its log clause is a hypothesis on `σ'`,
  `:678-680`, and its `LStore` needs `data ≠ []`, `elabOk` `WeakEvInst.lean:556`, so `n = 0` never arises); W-DISK
  ELIDES the zero-length data node [R20.2] (no pf `n = 0` arm; MachCSL's no-op matched inside the next `DWriteDev`).  *Acceptance:*
  `lake build Xv6 MachCSL Weak Vtest` ([R14.1] pattern — `Weak/` and `Vtest` are NOT in the cone build, `audit.sh:
  13-16`), `--weak` audit unchanged, `tools/ci/vtest.sh check`; `Lang.lean`'s docstring and `relaxed-rr.md` name the
  no-op.  *Unblocks:* W4 F9 (with W-DISK).  *Risk:* the one `Xv6`-cone rebuild on the serial lane (shared with nothing
  — W-RSV is weeks away).
  **W-COH — DONE.  G2-Q RULED (a′) with BOTH components [OWN.20][OWN.21][OWN.23] (was S–M)**.  Landed: `Hist.readEnt
  :127`/`Hist.read_eq_readEnt :130`/`Hist.readSrc :136`/`Hist.readSrc_foreign_le :139` (`MachCSL/TsoMem.lean`), the
  per-byte input `LoadSrcs` built by `FlatMem.loadSrcs :320` (`loadSrcs_stampAt_le :324`), `HRead.afterLoad :354`
  (foreign-only stamp over `LoadSrcs`), `HRead.resetCoh :361`; `MState.afterLoad` (`Lang.lean:128-131`, builds the
  input from `σ.mem`), `MState.store :156` (`clearAcq.resetCoh pa n`); the four `afterLoad` files and the store rules
  re-proved; header texts updated; `Weak/TsoOfPf.lean` restated (`tsoAfterLoadCoh :179`; acceptance (ii) `g2TsoSched
  :251`, (iii) `m0 :270`/`g2OwnLog :272`); `Vtest` twins built.  W5b′'s `cohSrc` mirrors it from the pf log (`shSrc`,
  `shLoadSrcs`); the agreement is W2b's `hsrc` seam (§C W2 CLOSE).  The record of the design (kept for the audit): (1) the
  RESET — `MState.store` resets `coh` on its footprint (a new `HRead.resetCoh pa n` beside `clearAcq`, `TsoMem.lean:277`;
  `Lang.lean:147-153`) — CONFIRMED [OWN.21]; [R14.s3] the reset applies with `excl = true` too (cat's `po-loc-no-w`
  counts the SC/AMO write; `MState.store` is ONE function, `excl` a parameter — NO `excl` case split), and with `excl
  && acq` the floor already moves to `top + 1` (`Lang.lean:150`), so the reset there is harmless but still performed
  (uniformity with the shadow's store effect); (2) the FOREIGN-ONLY stamp — `HRead.afterLoad` stamps `coh a := max (coh a)
  t_a` for FOREIGN-sourced bytes only (`e.tid ≠ hartAgent cpu`), own-sourced bytes unstamped — RULED [OWN.23],
  LOAD-BEARING for (9d) (§B(10): without it the `m0`/`w_c'` candidate has no TsoMem realization and `hullRun` fails; the
  fallback, had the owner declined, was a W8 transported census of that shape, M, **unverified** — MOOT).  [R12.s3]
  `MState.afterLoad`'s SIGNATURE is unchanged (`Lang.lean:127-129`: it has `σ.mem` in hand and computes each byte's
  source author/timestamp via `Hist.read`'s `find?`); only `HRead.afterLoad` (`TsoMem.lean:268-270`) gains the per-byte
  stamp input.  [R13.s3] `Hist.read` returns the VALUE only (`TsoMem.lean:119-120`, `.map HEnt.v`); the foreign-only
  stamp needs the ENTRY (`HEnt.tid`, `HEnt.t`) — add `Hist.readEnt` (the same `find?`, entry returned) beside it and
  have `MState.afterLoad` build the per-byte `List (Option (Agent × Nat))` it hands to the new `HRead.afterLoad`; name
  that input so W5b′'s `tsoShadow` mirrors it from the pf log (`wmTid`, position + 1; `WeakMem.lean:106-111`).  So the four `afterLoad`-only files (`Wp`, `WpAtomic`, `WpSmodeFenceFloor`, `UIcache`) re-prove only
  where they UNFOLD it; no Iris resource exposes `coh` (`hartViewsAt` carries `tv`/`itv`/`rv`, `memModelAt` = top,
  authors, views, `resvMap`, `mmOk`; `Resources.lean:938-951`).  Files: the 7 of §D G2-Q plus the
  store rules' `clearAcq`/`resvMap_upd` sites (`Wp.lean:1337,1363`, `WpAtomic.lean:188,202`, `mmOk_store`
  `Resources.lean:824-840` — `HRead.bound`'s `coh a ≤ L`, `TsoMem.lean:280`, holds trivially at `0`); `relaxed-rr.md`'s
  CoRR gloss and `TsoMem.lean:20-24`'s header text updated.  **+ `Weak/TsoOfPf.lean` (MERGED, `Weak.lean:624`)
  [R14.1]**: `tsoAfterLoadCoh :171-173` unfolds `HRead.afterLoad` (`simp only [HRead.afterLoad]`) and STATES the old
  semantics (every footprint byte stamped `tvn` — exactly what (a′) makes false): ill-typed under the new arity —
  re-state it for the new `afterLoad` (foreign-stamped byte ↦ its source position; own-sourced byte ↦ unchanged),
  NAMING the per-byte input that W5b′'s `tsoShadow` mirrors ([R13.s3]) so the two agree; replace the G2 docstrings
  `:14-16`, `:212-214` (`g2Tso :215-225` itself is over `Hist.read`/`histOf` and survives).  **+ the `Vtest` lib**
  (found verifying [R14.1]; `lakefile.toml:43-49`, NOT a default target, `tools/ci/vtest.sh check`): `vtest-lean/
  Vtest/XState.lean:234-241` `afterLoadHR`/`afterLoadHR_eq` (`unfold … HRead.afterLoad`), `:251-256` `abs_afterLoad`,
  `:283-292` `XState.store`'s `hr := clearAcq`/`abs_store` — the computable twins gain the per-byte input and the
  reset; `HartExec.lean:242-244,328` call them (`cohOkB :56-61` unchanged if `cohOk` keeps its type).  Neither lane
  is in the Xv6/MachCSL CI build (`audit.sh:13-16`), so a worker building the `Xv6` cone per §B(12) sees GREEN while
  `Weak.lean:624`/`Vtest.lean` go red: **the brief's acceptance REQUIRES `lake build Weak.TsoOfPf Vtest`** (or the
  `--weak` lane + `vtest.sh check`).  **Acceptance** [R14.1][R14.s4] — three NAMED `decide`/`simp` facts over `histOf`
  in `TsoOfPf.lean` (S): (i) the restated `tsoAfterLoadCoh`; (ii) `g2TsoSched` — `g2Run` HAS a TsoMem schedule under
  the new `afterLoad` (the second load at `tvn = 0` reading byte `c = 0`); (iii) §B(10)'s own-store counterexample
  realized (`m0`/`w_c'`: byte `c` reads `w_c`); plus `lake build Weak.TsoOfPf Vtest` green.
  **W-RSV — D19 RULED (b) [OWN.19]; FORM (i-a) RULED [OWN.22][OWN.23]: reservations are CLEARED at the instruction
  boundary and the hart's fragment is THREADED through the cycle rules (L–XL, one `Xv6`-cone rebuild [R12.1]).**
  Rev 14's `inflight`-flag text was INCONSISTENT [R11.2]: dropping `blockedStep`'s store arm while `evStep`'s store/
  exclusive-read arms keep `¬ othersReserve` (`Lang.lean:368-378`; `hartStep` has no third arm, `:533-538`) leaves a
  foreign hart whose store overlaps an in-flight AMO with NO transition (stuck, `Reducible` fails); dropping the
  `evStep` guard instead un-atomizes the lock's `amoswap.w.aq` (`KernelImage.lean:2265-2270`).  **Semantics (form (i-a),
  W-RSV-Q §D)**: `hartStep`'s `.pure` arm (`Lang.lean:535`, today `σ' = σ`) becomes `σ' = σ.dropResv cpu` — what
  the pf twin already does (`pnodeStep`'s `LInstr`, `WeakEvInst.lean:284-288`; `instrPost … wRes := none`,
  `WeakMem.lean:720-721`); the `evStep` guards, BOTH `blockedStep` arms (`:433-436`) and the DMA `¬ anyReserve` guard/
  `devBlocked` arm (`:539,548-553`) ALL STAY, ranging over IN-FLIGHT reservations by invariant (none outlives its
  instruction) — no `inflight` flag, no invalidation rule; `Resv := Mem` (`TsoMem.lean:240`) and `ResvVal` keep their
  types.  A reservation-less SC is a PLAIN store with success by the opaque — TODAY's semantics, no new weakening
  ([R11.2] (ii); §0 F1 (ii)).  **Ghost side [R12.1]** (rev 15's "re-stated over `ctxTok`" was WRONG): the `.pure` step now changes `σ.resv cpu`, so
  `memModelAt`'s `E.resvName ↪●MAP resvMap σ` (`Resources.lean:949`; `resvMap_get? :611-612` = `(σ.resv c, acq)`) must
  be updated with the hart's EXCLUSIVE fragment in hand — `resvMap_congr :621` no longer applies; the ghost lemma
  ALREADY EXISTS: `memModel_dropResv` (`WpAtomic.lean:49-51`: `memModelAt E σ ∗ resvFragAt E cpu r b ⊢ |==> memModelAt E
  (σ.dropResv cpu) ∗ resvFragAt E cpu none b`).  But `wpLoop_restart` (`Wp.lean:385-400`, resource-free) is applied
  BARE — `iapply wpLoop_restart; iintro %tick` — inside the cycle rules (`WpCycle.lean:110,172`, `WpSmodeCycleB32.lean:
  42`, `WpSmodeCycleRvc.lean:41`, `WpSmodeCycleT.lean:87,154`, `WpSmodeWait.lean:98,176`, `UCycleSwp.lean:367`), whose
  premises are `mConf/confCells ∗ clockCells ∗ pcIs ∗ (transTok) ∗ R ∗ P` (`WpCycle.lean:96-105`, `WpSmodeCycleB32.lean:
  24-36`) and name NEITHER `ctxTok`, `kctx`, `ownCtx` nor `resvFrag` (grep: 0 in the four `WpCycle`/`WpSmodeCycle*`
  files; `UCycleSwp.lean:31` a comment); the fragment rides ONE LAYER UP — in `kctx` as `ctxToken` (`Ctx.lean:29-30`;
  `KCtx.lean:415,849,939`) and in user mode inside the walker frames as `uResvTok cpu rv := ∃ r, resvFragAny cpu r`
  (`URunRW.lean:501-502`, ≈ 30 mentions).  Two forms, both FAITHFUL (CSL plumbing, no semantics): **(i-a) RULED
  [OWN.23]** — every cycle rule gains a `resvFragAny cpu r` premise and a `resvFrag cpu none b` post: 16 rules in 9 files
  [R13.s1] (`wpLoop_m_base/_rvc/_instrClk/_instrP/_instr` `WpCycle.lean:96,157,282,321,332`; `wpLoop_s_base/_rvc`
  `WpSmodeCycleB32/Rvc`; `wpLoop_s_instr` `WpSmodeCycle.lean:29`; `wpLoop_s_instr_clk` `WpSmodeTime.lean:54`;
  `wpLoop_sT_base/_rvc` `WpSmodeCycleT`; `wpLoop_sT_instr` `WpSmodeSatpU.lean:280`; `wpLoop_wait_wfi/_s_wfi_cycle`
  `WpSmodeWait`; `wpLoop_ucStep/_uwStep` `UCycleSwp`); [R13.s2] the S-mode rules have TWO continuations (`▷ (… -∗ wpLoop
  cpu) ∧ trapBranch cpu c tier root sie pc P`, `WpSmodeCycleB32.lean:33-36`; `trapBranch` `WpSmodeCycleBase.lean:77`),
  so the `resvFrag cpu none b` post is delivered on BOTH arms (the trap handler re-forms `ctxToken cpu` on the same
  hart) — and EVERY caller supplies it — measured [R13.1], BY LANE: **25 MachCSL files** mention a cycle rule (20 apply
  one directly: `WpSmodeCycle.lean:49,65`, `WpSmodeRules`, `WpSmodeIntr`, `WpSmodeKpt`, `WpSmodeProc`, `WpSmodeSret`,
  `WpSmodeSwtch`, `WpSmodeTime`, `WpSmodeTrapCsr`, `WpStore.lean:201,223` (`ctxTok` in scope), `WpLockSchema`,
  `WpSmodeLwKey`, the five `WpMmode*` …; R12 counted ≈ 27).  (S-mode KERNEL lane) the schema wrappers `wpLoop_k_*`
  (`WpSmodeRules.lean:52-60`, premise `kctxL lent cpu k`; `kctxP` holds `ctxToken cpu` for EITHER `lent`, `KCtx.lean:
  839-850,925,931-952`; `ctxToken = ctxTok cpu curCtx :415` = `ownCtxAt ∗ ∃ r, resvFragAnyAt E cpu r`, `Ctx.lean:
  298-299`) ABSORB the fragment inside their proofs — their statements and the `Xv6` cone above them (3 `wpLoop_k_*`
  sites) stay.  (USER lane) `uFr` ∋ the walker `ctxTok` = `ownCtx ∗ uResvTok` (`UCycleSwp.lean:31-33`, `URunRW.lean:
  501-502`) absorbs it likewise.  (M-MODE lane — MISSED by rev 16) the five `wpLoop_m_*` rules are stated over `mConf
  cpu dq c ∗ clockCells cpu ∗ pcIs cpu pc ∗ R ∗ P` with NO bundle (`WpCycle.lean:103-105`), and the **35 `wp_m_*`
  wrappers** that apply them (`WpMmode.lean` 8, `WpMmodeAlu` 9, `WpMmodeCsr` 16, `WpMmodeCtl` 1, `WpMmodeMret` 1; 5 of
  the 25 files; `grep -c "ctxTok\|resvFrag\|kctx"` = 0 in four, and in `WpMmode.lean` only `wp_m_ld_same` threads
  `ctxTok cpu curCtx`, `:229-231,388-391` — [R13.s4] the TEMPLATE if a token is preferred to a bare fragment in M-mode)
  have NOTHING to absorb it into: **34 statements gain `resvFragAny cpu r`/`resvFrag cpu none b` (or a new M-mode
  token)**.  **`Xv6/` cost: 12 files** — the **8 that apply a cycle rule DIRECTLY**: `ProofSpin.lean:43`
  (`wpLoop_m_instr`), `UserretPt.lean:52,130,177`, `UserretEntryPt.lean:63,113`, `UservecPt.lean:55,129,212`,
  `UservecExitPt.lean:90,121,164,198` (`wpLoop_sT_instr`), `UserStepActive.lean:124`, `UkEngine.lean:178`
  (`wpLoop_ucStep`), `UserStepWait.lean:34` (`wpLoop_uwStep`) — the fragment IS available at each (the trampoline files
  frame `ctxTok cpu curCtx`, `UserretEntryPt.lean:164` frames `∃ r, resvFragAny cpu r` across `fence.i`; `kctx_cases`
  yields `Htok`, `WpSmodeWait.lean:257`; `UkEngine.lean:125` extracts `ctxToken` from `Rut`); PLUS the `wp_m_*` callers
  **`ProofEntry` (8 applications), `ProofStart` (39), `ProofTimerinit` (21)** — re-threaded at the PROOF level only,
  their spec bodies already carry `ctxTok cpu curCtx` (`SpecEntry.lean:48`, `SpecStart.lean:62`, `SpecTimerinit.lean:
  56`); PLUS **`SpecSpin.lean:34-42`'s `wp_spin_body`/`SPIN`** and `ProofSpin.lean:32-55`'s `wp_m_j`/`spin_loop`, which
  hold NO token — a STATEMENT change, isolated (`SPIN.wp_spin`'s only consumer is `LinkSpin.lean:14`; `ProofBoot.lean:
  27`/`SpecBoot.lean:75` use only the address `KA.«spin»`).  Mechanical but WIDE, L–XL (size class UNCHANGED by the
  M-mode lane), one `Xv6`-cone rebuild.  **(i-b)** (recorded, not ruled) —
  move the per-hart `∃ r, resvFragAny cpu r` out of `ctxTok`/`uResvTok` into a per-hart INVARIANT opened by the boundary
  rule and by the three rules that consume the fragment explicitly (`swp_sail_mem_write_plain_au` `WpAtomic.lean:
  538-544`, `swp_sail_mem_read_excl_au :698-704`, `swp_sail_mem_write_excl_au :711-717`): the cycle rules stay, but
  `ctxTokAt` (`Ctx.lean:298-299`, 19 sites), `KCtx`'s `ctxToken`, `URunRW`'s `uResvTok` and every `ctxTok_cases/_intro`
  user change — M–L, a context-token REDESIGN; the cycle rules, the 35 `wp_m_*`, `wpLoop_k_*` and ALL of `Xv6/` stay
  as they are, so (i-b)'s relative advantage GREW with [R13.1] (recorded for the owner, §D W-RSV-Q).  Form (ii) (the `inflight` flag) has the SAME ghost problem unless the
  flag is kept OUT of `ResvVal` — and then the exclusive-store rule cannot learn "in-flight" from a resource (`mmOk`'s
  clause "every reservation agrees with the top", `Resources.lean:781-782`, must weaken to in-flight reservations, and
  `memModel_store_excl :221-224` needs that fact) — so (ii) is NOT an escape hatch.  Devices are untouched by
  `dropResv`: `ObsTrace.hartStep_wire/_recvd` (`ObsTrace.lean:503,538`) and `DiskOf.hartStep_diskOf :134-136` are trivial.  **Census of blocking consumers** (21 MachCSL files [R11.s3] + `Weak/WeakLang.lean:52`, the
  pf twin that already DROPS the DMA guard — the precedent for the direction): `blockedStep` — `Wp.lean` 8 (the generic
  step rule's blocked disjunct and self-loop continuation `:495-497,536-538`, the `hnb` variants `:552`), `Lang` 4,
  `ObsTrace.lean:512,547`, `DecodeBridge.lean:86,147`, `DiskOf.lean:157`; `othersReserve` — `WpAtomic` 8, `Lang` 4,
  `WpSmodeDev.lean:75-76,160`, `Wp.lean:1344,1589,1800`, `Resources.lean:754-757,825`, `WpStoreOrd.lean:73,85`,
  `WpPtWalkOwn.lean:134,227`; `anyReserve` — `WpDma` 3, `WpDev` 1, `Resources` 1; `dropResv` — `WpAtomic` 9; `resvMap`
  — `Resources` 29, `WpAtomic` 8, `Wp` 8, `Power`/`PowerText` 3+3, `WpSmodeFenceFloor` 2, `WpDma` 1; `snapOf` —
  `WpAtomic` 11, `WpPtWalk` 7 / `WpPtWalkOwn` 6 / `WpSmodeAu` 2 / `WpSmodeAtomic` 1 — the Svadu A/D LR/SC pair
  (`exclReadAU … snapOf pa 8`, `WpPtWalk.lean:84,111,135,161`) is issued INSIDE one memory instruction's translation,
  hence IN-FLIGHT for its whole window: rev 14's "reservation-still-valid premise or retry" risk is WITHDRAWN, the
  re-proof mechanical [R11.2] (iii); `valid_reservation` — `UWait.lean:21-26`, `SailHooks.lean:5,14,26` (the opaque
  stays, no change); `MachGS.resvName` (`Resources.lean:122,433,475`; constructed by `Xv6/AppUnionPre.lean:89`,
  `Xv6/AppPreGS.lean:54`) UNCHANGED under form (i-a) (touched under (ii), whose `ResvVal` changes).  The bulk: `Wp`/`WpAtomic` re-proved
  against the invariant "reservations are in-flight", PLUS the (i-a) thread through 16 cycle-rule statements and their
  25 MachCSL files (35 `wp_m_*` statements among them) + 12 `Xv6/` files [R12.1][R13.1].
  **Interaction with W2** (§B(10)): the `LStore`/`DWrite` rows get `¬ othersReserve`/`¬ anyReserve` from `pairAdjacent`
  ALONE (no in-flight foreign reservation can straddle a step); `LExStore` needs nothing of the own reservation
  (TsoMem never reads it [R11.2] (i)); the [R2.3-alt] failure mode (a STANDALONE `LExLoad`'s dangling reservation
  blocking a foreign store) DISAPPEARS.  **Does the fused-pair restriction remain needed?**  For FAILING SCs, YES (the
  pf retry self-loop `WeakEvInst.lean:360-364` has no TsoMem twin — TsoMem's lost-reservation store is a plain store;
  an SC-failure row is M, not planned); for DANGLING LRs, NO once W-RSV lands: clause (i) of `execProgOk'S` (`lbFused`
  on the left arm) can be RELAXED to admit a standalone `LExLoad` realized as `LLoad` (`lbNobarex`, `projLbl :541`) —
  TsoMem's exclusive read takes `topBytes` = the pf's `lat` read, `afterExcl`'s `rv := top` is the shadow's (G1′) — a
  quantifier WIDENING, OPTIONAL follow-up (S–M: one W2 row + the clause).  [R12.s2] Under the widening a dangling
  `lr.aq` leaves `hr.acq = true` until the hart's next store (`clearAcq`), and an EXCLUSIVE next store would take `tv :=
  top+1` (`Lang.lean:150`, guard `excl && acq`) — a floor at the hart's OWN store position that cat does not give (no
  `W;po;R` ppo); so the boundary rule also clears `hr.acq` (same rule; `resvMap` carries the bit, `resvMap_get?`), or
  the widening relies on `pairAdjacent` pairing every later `LExStore` with its own `LExLoad`.  After landing: §0 F1 (ii) is removed from
  the strengthenings list, the "Honestly" line and §B(11)'s internal list drop "reservation serialisation", D19's mark
  is FAITHFUL for AMOs / WEAKER for user LR/SC (as today); acceptance also updates `TsoMem.lean:27-31`'s header text
  ("blocked … while a hart holds a reservation" → "within the issuing instruction") [R11.s2].  Deps: W-COH landed, then
  W4/M1 (D26 — W-RSV follows M1 so its `Xv6`-cone rebuild does not sit on W4's path — **MET [rev 31]: M1's core landed
  2026-10-12, F9 + W5 CORE merged**); **W8-β′ MERGED — not W8 (f2-ctx): Q-RSV-order RULED (b) [OWN.41] [R28.5]**, W-RSV goes
  right after β′ and (f2-ctx) rebases on W-RSV.  **Launch (rev 32) [R28.5].**  *Deps*: W8-β′ MERGED; M1 ✓ (D26).  *Rebase surface*
  (β′'s landed edits overlap W-RSV's census in ≈ 8 MachCSL files): `Resources.lean` (β′'s `⌜staticIn reg ∧ reservedOk σ reg⌝`
  conjunct and `rsvName` ghost in `memModelAt :951-956` sit beside W-RSV's `resvMap` conjunct `:955`; the era tuple is 15 fields
  after β′), `Wp.lean`/`WpAtomic.lean`/`WpDma.lean` (β′'s primitive-store `a ∉ reg` argument [R27.s1] at the same sites W-RSV
  re-proves against "reservations are in-flight"), `Power.lean`/`PowerText.lean` (`resvMap` 3+3 and β′'s mint), `KCtx.lean`
  (`ctxToken`/`cpuCells` halves), `WpLock.lean` (fraction-parametric rules; the `WpLock` overlap above).  *W4/W2 re-proof INSIDE
  this item* (supersedes "W4 re-checks three rows after it (S)", pre-F9 text): M1 is a REGISTERED root by then (W5 CLOSE-OUT) and
  W-RSV changes `MState`'s `.pure` arm (`hartStep`, `Lang.lean:535`), so the `Weak/` bridge is re-proved and rebuilt HERE — the
  reservation guards appear in `MachOfPf.lean` at 13 sites (pre-W5d/W-SCO numbering; the grep below returns 16 lines in the tip after
  the twins [R32.s7]): `notOthers :744-746`, the `hno` premises `:757,790`, and **F9's four
  disk-row `hres : ¬ anyReserve σ.resv pa n` sites `:1513,1590,1741,1848`** (`simDisk`'s `storeDma` rows, written AFTER the W-RSV
  brief) — plus `PfStepTsoMem.lean`/`PfStepTsoView.lean`/`PfStepTso.lean`'s rows (grep `othersReserve`/`anyReserve`/`resv`);
  `pairAdjacent` still supplies them (no in-flight reservation straddles a step, §B(10) above), so the re-proof is S–M; then
  `srvwmoXv6M1Core` (and W-SCO's corollary `srvwmoXv6M1`, if landed) rebuilt [rev 35: M1 is REGISTERED (W5 CLOSE-OUT DONE);
  `Weak/SailCycleOrderK.lean` (no reservation guard) and `Weak/PfRunUnpinned.lean` (MERGED [R32.2]) join the rebuild — §C top's rev-35
  W-RSV paragraph].  *Acceptance*: `lake build Xv6 MachCSL Weak Vtest`,
  `audit.sh --weak` green with the REGISTERED root(s), `tools/ci/vtest.sh check` (the `Vtest` `hartStep` twin,
  `vtest-lean/Vtest/HartExec.lean`), the `TsoMem.lean:27-31` header and §0 F1 (ii) as already written.  Critical path [R12.1]:
  W-RSV is the LONGEST serial MachCSL item; it gates M2 (W5d) only through the W4 re-proof, and Stage 2's graph lane
  (W12/W12b/W5d-G/W13) runs beside it.  **DONE and MERGED 2026-10-12 [rev 37] — the landed form, deviations and file counts are at §C top's
  rev-37 W-RSV paragraph; the W4 re-proof is inside, so M2 CLOSE now waits on W-SCO (A) only — DONE rev 40.**

**Stage 1b — M2, the fork path on the pf side (part of the target [OWN.3]).**
- **W5d `Weak/PfRunUnpinned.lean`** (L) [R2.1-alt][R3.1][OWN.3][R4.2][R6.4b].  The pf half ONLY: `execWfPfRunProgF`
  (replay at `pstepEv` with the CUT-form clause `∃ q, itv ≤ q ≤ |log| ∧ ifetchOk img log q base tvs` replacing
  `fetchPin`; W5b's replay carries a `pstepPinned` hypothesis — the M2 replay instantiates `fok` with the cut form and
  DROPS the pin; [W2s] the cut form adds `t ≤ q` per byte; **[R11.3] its `itv` is W5d's `itvOf` (§B(4)(iii) (ii):
  per-row, per-step, driven by the realizing `LFence false×4` label with the `fiArm` STATE carried as the free bit `fiOf`
  per [R31.1] (i) — `ls` alone does not tell `fence.i` from the marker —, frame condition on the other rows [R12.s1]; supplied BESIDE `fok`, not as an argument [R28.4]; S inside this L)**), W4's
  `LIFetch` row for user text at `tvn := q ≥ itvOf`, W5 restated — the first form in which `fork → ecall →
  sys_fork → allocproc` under contended `p->lock` from 7 scheduling harts is a candidate.  The user-fetch witness is
  NOT buildable by kernel evaluation (D44 [R7.4]).  The graph half is W5d-G (Stage 2).  Deps: W5 — **MET [rev 31] (M1's core
  `srvwmoXv6M1Core` landed 2026-10-12): LAUNCHABLE NOW on the `Weak/` lane**; its restated M1 is a NEW theorem `srvwmoXv6M2Core` in
  its own file (the M2 premise set a NEW definition `srvwmoXv6M2Premises` beside W5-pre's); the W4 `LIFetch` M2 row is consumed
  through `Hyps.cut` at the cut form (W2b's view row `rowFetchM2`, **`Weak/PfStepTsoView.lean:778`**, table row `:41` [R28.4]) —
  **[R29.s5]** its `hq :780` is supplied by `pfCutFactsT`'s witness DIRECTLY (no MachCSL-side source to look for); M2 CLOSES after
  W-RSV's W4 re-proof (D26).  **[R28.4] `fok`'s type is UNCHANGED** (5 arguments; `candKfetch`'s type and M1's registered ENTRY
  stable) — **[R29.1] the cut clause is carried by the new parameter `fcutT` (§B(4)(iii), binding)**: R28's carrier (`.LIFetch`
  arm of `pfLoadFactsT` + an `execProgOk'S` conjunct, "`Hyps.cut` from `pfStepFactsT`'s two conjuncts") does not type-check
  against `Hyps.cut` (`MachOfPf.lean:664-671` takes the UN-threaded `pfStepFacts`), breaks `pfLoadFactsTNonload`/`pfRunSTApp`
  (`TsoShadow.lean:579-581,622-632`, M1's run construction) and strengthens M1's premise.  **FIRST commit (S–M, ≈ 150–300 lines)**:
  `pfCutFactsT fcutT stamp st c i l := ∀ base tvs, l = .LIFetch base tvs → fcutT (tsoShadow stamp st i).itv c.pcImg c.pcLog i base
  tvs` as `pfRunST.snoc`'s third fact (`TsoShadow.lean:584-590`), **[R30.1] the Exec twin is the SECOND parameter `fcutE`** (per index, inside `execProgOk'S`'s existential beside `fetchesOk`;
M1 `True`; M2 carries `itvOf`'s cut, recurrence and frame condition, `itvOf` free in `srvwmoXv6M2Premises` — §B(4)(iii), binding:
nothing non-trivial enters M1's premise, `itvOf` is no shared parameter; M1 replay lemmas at both trivial instances),
  `contR.cons`/`simNode` carry it, `MachOfPf.Hyps fcutT …` with `cut` receiving it (passed at `:1043`), `cutOfPristine`,
  `machRunOfPfRun`, `sailCycleOrder :113` (at the trivial instance [R30.s3]), `srvwmoXv6M1Premises`/`srvwmoXv6M1PfRun`/`srvwmoXv6M1Satisfiable`
  (`SrvwmoXv6Witness.lean:272,280,599-607,624,733`), `m1Hyps :203-213`, `srvwmoXv6M1Core :276-284` at the trivial instance
  `fun _ _ _ _ _ _ => True`.  **Files edited beyond the new file**: `PfRunShape.lean`, `TsoShadow.lean`, `MachOfPf.lean`,
  `SrvwmoXv6Witness.lean`, `SrvwmoXv6Adequacy.lean` (trivial instances; M1's statement TEXT changes, its content, name and
  `axioms`/`opaques` entry do not (both parameters [R30.1]) — the W5 CLOSE-OUT's registration stands; one `Xv6`-free `Weak` rebuild); `PfStepTso.lean`
  (`pfRunSTAuthors :527-536`'s binder/`_` [R30.s1]; `proposedStmt :102-124` NOT re-pointed — clause (3) `:115-118` already states
  the cut conclusion as a hypothesis; `PfStepTsoView.lean` untouched).  Then M2: `fcutT itv img log i base tvs := ∃ q, itv ≤ q ∧ q ≤ |log| ∧
  ifetchOk img log q base tvs ∧ ∀ byte, t ≤ q`, `fok := fun _ _ _ _ _ => True` or `fok_cut` (worker's choice); `Hyps.cut` at M2 is
  the step's `pfCutFactsT` verbatim (the M2 twin of `cutOfPristine`, no MachCSL side).  Landing: after W-SCO's `Hyps.fi` widening,
  before W-SCO states `sailCycleOrderK`/`srvwmoXv6M1` (§C top).  **[R28.3]** `m2Hyps` instantiates `MachOfPf.Hyps`; if W-SCO's
  `Hyps.fi` widening (its first commit) has merged, build on it, else rebase (S) — the `fi` field is discharged from the general
  `sailCycleOrder` (`fiOfSco`), ignoring the extra `MRun`/`SimRel` premises.
  **[rev 35] M2 CORE DONE — `Weak/PfRunUnpinned.lean` (780 lines), MERGED in the tip and imported (`Weak.lean:636`; byte-identical to
  w5's) [R32.2]; NOT registered; [R32.1] RESOLVED rev 39 — `hsco` restated under `wbootFacts σ0` (which
  `srvwmoXv6M2Premises :596` already carries) and discharged by `sailCycleOrder_holds`, non-vacuous; read its header for the design and deviations.**  Delivered: the FIRST commit's threading as GENERIC TWINS with the plan's names as the TRIVIAL
  instances — `execProgOk'SC` (`PfRunShape.lean:252`; `execProgOk'S :273` = its `True` instance), `execProgOk'STC`/`pfRunSTC`
  (`TsoShadow.lean:583,620`; `execProgOk'ST :589`/`pfRunST :629` abbrevs), `contRC`/`HypsC` (`MachOfPf.lean:526,686`; `contR :538`/
  `Hyps :716` abbrevs) — M1's TEXT UNCHANGED (stronger than [R29.1]/[R30.1]'s "text changes, content does not"); **[R31.1] route (i)**:
  `fiStep :68`/`fiFold :75`/`lbFenceZeroL :78`/`fcutM2 :85`/`fcutM2Ifetch0 :91` (the cut form implies the pf view-0 check `PFIFetch`)/
  `itvStep :100`/`fcutEM2 :113`/`fokTriv :123`; the M2 replay `execPrefixPfRunProgF :342`/**`execWfPfRunProgF :558`** with THE REPLAY
  INVARIANT `(tsoShadow stamp st i).itv = itvOf n i ∧ .fiArm = fiOf n i` by construction; `srvwmoXv6M2Premises :594` (M1's with the
  unpinned LTS, `fok := fokTriv`, `fcutEM2 cohSrc (candExec c) itvOf fiOf`, boot values `itvOf 0 i = 0 ∧ fiOf 0 i = false` [R31.s3]),
  `srvwmoXv6M2PfRun :609`, `m2Hyps :632` (`HypsC` at `fcutM2`: `cut` IS the step's `pfCutFactsT` verbatim, `fi` = `fiOfSco` from
  `sailCycleOrder`), **`srvwmoXv6M2Core :652`** (M1's conclusions — the MachCSL run, every closed xv6 theorem at it, the allocproc
  shadow — for every M2 candidate, PLUS the replay invariant at the trace's end), `srvwmoXv6M2Satisfiable :758`.  Deviations (header):
  (1) `fok := fokTriv` — the cut lives in `fcutEM2`/`fcutM2` (the plan's "worker's choice"); (2) `fcutEM2` reads the realizing label from
  `E.exTr[k]?`, closing over `E` [R31.s1]; (3) M2Core also returns the replay invariant.  Axioms: the replay `propext`/`Classical.choice`/
  `Quot.sound`; `srvwmoXv6M2Core` adds `xv6FsAdequacy_closed`'s cone, as M1.  NOT registered: **M2 CLOSES after W-RSV's W4
  re-proof (D26) and — under [OWN.42] — with `hsco` discharged by W-SCO (A)'s `sailCycleOrder_holds` — BOTH MET (rev 39)** (the §A `∧ sailCycleOrder`
  conjunct is gone at M2 too; `srvwmoXv6M2` is STATED, `Weak/SailCycleOrderCycle.lean:179` [R32.s4]; **M2 CLOSE = registration, DONE rev 40 — §C top**).  w5 MERGED [R32.2] (the six shared files
  carry the twins and their trivial instances; W-SCO (A) appends to `PfRunUnpinned.lean` for commit 1; W13 (I)'s bundle half touches none).

**Stage 2 — THE TARGET: T-alloc-RVWMO via graph-tier robustness re-sourced from TsoMem (route 9d; XL).**
- **W12 `Weak/CatLin*.lean`** (M–L ≈ 1.2–1.8k, spike-sized; D25 RULED (a) [OWN.5]) [R6.1iii] — **DONE and MERGED 2026-10-13 (w1) [rev 42], §C top Rev 42 RESULTS
  (`hullCatAD`'s injectivity risk did NOT materialise; `xv6RvwmoSafeModuloT :403` STATED, not registered)** — the spike's design:
  (1) core predicate `rvwmoCoreD GD := gwf ∧ gloadValue ∧ gatomicity ∧ gdepsWf`; restate `topoLinearizes`' section
  variable, `topoExists`, `racyDMem`, `normalizeOfAcyclic(')`, `topoSupply`, `hullRealizable*`, `hullRun`,
  `topoLinearizesF` over it (statement edits, S); **[R21.2] the restated `normalizeOfAcyclic` ALSO concludes
  `gppoCat6Gmo GD'.gdG`** (the topo order extends the cat chain's `racyD`, which must contain `gppoCat6` — today's `racy`
  has a `gppo` arm, `racyD :200`/`rtRacy :207-211` in `WeakRvwmoAcyc.lean`; or keep RVWMO⁻ on `GD'` if `racyD` keeps `gppo`) — **unverified**, S–M;
  the producer of `linCandScaT`'s premise at Stage 2; (2) kill definitions from the scratch's §0–§3 — `rvwmoCatAD GD ad`
  (cat's six arms, lv, atomicity, deps, rule 12 over `ad ⊆ gdDeps`; entries `catADOfCatT` on `forget GT` with `ad :=
  gtAd`, `catADOfCat`, `catADOfMinus`), `rsameC`/`gcrossE`, `segPinC` as a same-hart CHAIN of `pinStep`s with the
  rule-12 forward case `segPinCForward` (why `ad` must be TAGGED), `CertC`/`chainC`/`cycleKillArmsC`, the lock kit
  `*C`, Glue §1 re-instantiated (`rawChainC`, `crunC`, `cycleSegmentsC`) (S–M); (3) **`hullCatAD`**: the hull of a
  `rvwmoCatAD GD ad` graph is `rvwmoCatAD (gdHull GD cs) (ad.filter cut)`, via `rowsRelGppoCat6` (rule 2's `t1 ≠ t2`,
  rule 3/12's `grfAt` through an injective `hren`; risk: injectivity on the cut's sources, believed via `hrenWix`, not
  built) — the one real proof (M); (4) restated chain `cycleKillC`, `t2linAuxC`, `t2linOfCycleKillC`, `t2linSupplyC`,
  `l2ClaimAtC` (`segPinC ∨ csHyps[gcrossE] ∨ Bad`), `rawChainChainC`, `cutSupplyC`/`certSupplyC`/`walkSupplyC`/
  `walkPolicyC`, `cycleKillOfL2C`, `t2linOfL2'''C` (S–M); (5) published capstone `xv6RvwmoSafeModuloT : ∀ GT : GdexecT,
  rvwmoCatConsistentT GT → gdexecQconfT boot d0 im nh GT → (∀ x, ¬ tc (racyD (forget GT)) x x) ∧ …` by `catADOfCatT`
  into the C-chain; `gdexecQconfT → gdexecQconf (forget GT)` from `rowDepsSubT` (S–M); (6) non-vacuity: existing
  witnesses via `catADOfMinus`; **acceptance gate [R6.s2]: ONE forwarding witness (SB+rfi-pos; `AxGraphCat`'s
  `epc`/`isw` are candidates) through `rvwmoCatAD`, cat-consistent but NOT RVWMO⁻**.  `WeakRvwmoLin*`/`Norm`/`PreNorm`
  untouched.  The cat arms are written ONCE against W13 (K)'s `racyDIO` (I/O arms gmo-forward by (T)); parameterize the cross order.
- **W12b `Weak/CatFloor*.lean`** (M–L ≈ 0.5–1k; NEW [R6.2]; D34 (a)).  **DONE and MERGED 2026-10-13 (w1) [rev 42] as TWINS (originals
  untouched); its premise `grelAcqGmoC` goes with D35-fix [OWN.54].**  Gate 3: Floor §4–§6 and Cert3 §2–§3 re-done
  on a per-byte coherence invariant through rules 1/2 in place of `gvisUb`; `greadSrcUb`, `finvStep`, `cinvReplay`/
  `floorOfCgraph`/`certFloorOk`/`cpolRead` over `rvwmoCatAD`; the `wVRel` hook per D35, forwarded `LLoad aq` per D36.
  **Acceptance** [R7.s5]: ONE forwarding read whose floor the old `gvisUb` mis-states — an own store `w` forwarded to
  a po-later read `r` with `w` gmo-AFTER `r`, the exact `finvStep` coh-hook case (`Floor.lean:619`) — certified by the
  new per-byte invariant.  WITH W12, BEFORE W10 (D26).
- **W5d-G `Weak/GraphFetch*.lean`** (L ≈ 1.8–2.2k + S–M re-creation + XL risk R1; D27 RULED (a) [OWN.6]; D42–D43
  RULED (a) [OWN.18]) [R4.2][R6.4b].  **G0 — DONE (`Weak/GraphFetchSpike.lean`, 339 lines, `propext, Quot.sound`;
  review `notes/W5dG-G0-review.md`: OK, header deviations R1–R10 justified; [OWN.26] `GraphFetchSpike.emSlot` = the
  REAL slot tag, RULED)**: proved `fetchCutPrefix :146`, `fetchCutEdge :161`/`fetchCutRel :248`, `fetchRelCut :215`,
  `fetchPinCutOk :322`; stated `gzFetch :278`, `gzFetchCut :264`, `emZifencei :312`, `gfcut :104`, `gwlog :100`,
  `gzContrib :272` (body = D41 (a)'s superset; docstring fixed, R7).  **Carried into G1 from the G0 review (binding
  for G1's brief):** (1) `emSlot` CONFIRMED [OWN.26] — `emZifencei` quantifies at `emSlot em.emItems n`; (2) `emSlotAdm
  :297` covers a block at the HEAD of the list only — add `emSlotShift` (`emSlot (pre ++ its) (|pre|+n) = emSlot its n`
  when a row item follows) or a `hemit`-induction corollary; (3) `emSlot`'s past-the-end default double-counts pairs —
  unreachable for `hemit` emissions; document or use the slot count; (4) **(Z2) is WEAKER than (H3)** (§B(4)(iii)):
  state (Z2) as "every own write at/after slot `k` is gmo-after the source" or adopt E1′ (R1 (a)) — list the chosen
  reading in §B(11); (5) docs: header `:8` says `emZifencei` VERBATIM (R8 changed the slot function), the `gzFetchCut`
  docstring's "`q ≤` next-own-write" should read "`<`", the out-of-scope list should say E1′ strengthens (Z2)/(H3) in
  G1; (6) §B(11) spec note: Sail's `fetch` does one 4-byte read at a 4-aligned pc under `Ext_Ziccif`, so (Z3)'s one
  fill instant per label follows from Sail + Ziccif.  Then, AFTER W13 (M) (D26; Q-W5dG-seq RULED (a) [OWN.24][R14.3]
  — G1/G3/G5 edit `Fab`/`Supply`/`Acyc`/`Glue`/`Hull`/`Topo`, the files W13 (I)/(K)/(M) rewrite), the spike's change
  list: **G1** `gzContrib`, `emFenceI` + `emFenceISound`, `emZifencei` in `xv6ConfS`/`gdexecQconf` replacing
  `emFetchImg` (`WeakRvwmoSupply.lean:367` today, was `:277-352` [R41.s2]; `emFetchImgRen/Prefix` → retime/hull versions; `Fab.lean:516-522`;
  `WeakEvInst`/`WeakEvLang` lemma only) + the six carry-overs above (M ≈ 350–450); **G2** tags = gmo indices — `wlblRen` renames `LIFetch` tags
  (reverts Q-C4, `WeakRvwmoConf.lean:57-66,147`), `pstepEvWren`/`projLblWren` `LIFetch` arms, M1 pin kept via `π 0 =
  0` (S ≈ 100); **G3** fetch fragment as data — `Gdexec.gdFetch`, `racyD` disjunct, `racyDSplit` arm (cross-hart →
  `gcross`), `gdHull` filter, `retime` keeps it — a STRUCTURE change to `Gdexec` (`WeakRvwmoGraph.lean:669-671`; default-`[]`
  field + literal sweep, or a `GdexecF` wrapper for `xv6ConfS`/`racyDX` — worker's choice in its first report [R41.2][R41.s5]); the pre-(K)/(F-dep)/(R3′) count
  "~31 literal sites" (`WeakRvwmoGraph.lean:613`, `Acyc.lean:200`, `Glue.lean:205-223`, `Hull.lean:716`, `Topo.lean:120-129,594-607`) is RE-COUNTED at launch (≥ 23
  `gdDeps :=` sites + `KillIO:701`, `GraphFabResidue.diskFab :339`, `AxDeps.ioGt :1441`, …) (M ≈ 300 + a full-cone rebuild + re-audit per increment); **G4** `retimeZifencei` + contributor
  invariance + `gwlog`/`gwix` bridge (Topo; L ≈ 600); **G5** `linPrefixLog`, the floor bound, `supplyOfQconf` producing
  the M2 cut clause (`Lin`, `Floor`, `Supply.lean:743-883`; M–L ≈ 500); **G6** re-thread `pstepPin` → `execProgOk'S`
  (the 19-file list in §B(10); ONE pass with W11 (iii)); **G7** kill arms for cycles through E1/E2/E3 ("fetch-entry
  segments", pinned only by `fence.i`; W8 vocabulary: user-text page ownership, exec/fork → `p->lock` → `userret`
  `fence.i`) — L, in W11/W8.  Witness files with literal fetch items (`WeakRvwmoConfWit2`, `WeakRvwmoAdm`) need only
  "the pin implies `gzFetch`".  Hull closure per §B(4)(iii) R1 (a).  **Every increment rebuilds and RE-AUDITS the registered cone
  (`audit.sh --weak --build`, 13 roots, `baseline-weak.json` unchanged, roots' statements unchanged): G1–G5's files are in every registered root's import closure
  [R41.2].**  Non-vacuity: user-text fetch witness → W14 (D44).
- **W13 `Weak/GraphFab*.lean`** (**XL ≈ 7–10k lines / ~70 files**, REDESIGNED rev 10, eight pieces; D38 RULED
  [OWN.14]) [R5.1][R6.3iii][R7.3].  **(E) the alphabet — PARTIAL, MERGED (2026-10-11; 85 files under `Weak/`;
  `PROGRESS-W13E.md`); RE-SEQUENCED (a) [OWN.27]**.  DONE: `IoKind = rd | wr | dev` (`Weak/WeakMem.lean:110`; D45 (a)),
  `Lbl.LIo (kind) (base) (vs)` (`WeakAxiomatic.lean:96`; `lbRd`/`lbWr` = `none`, `lbIsR`/`lbIsW` false by wildcard,
  new `lbIsIo :186`), `Wlabel.LDev (kind) (base) (vs)` (`WeakPromise.lean:89`); `pnodeStep`'s MMIO arms emit `LDev .rd/
  .wr (paZ req.pa) (wbytes n w)` (`WeakEvInst.lean:305,341`), `pstepPlic`, `pdiskProg` START/COMMIT, `pdiskUart` emit
  `LDev .dev 0 []` in the issuing row (D49 (a)); `unprojLbl (.LIo k b vs) = .LDev k b vs` (`WeakPromiseBridge.lean:962`);
  `wpPfStep.PFDev`/`wpstep.WPDev` carry the payload (implicit binders — existing patterns unchanged); `eraseLbl`/
  `wlblRen` carry it; `pdevEv`/`pclsEv`/`lbAdmin`/`lbNobarex`/`lbRfoldfree`/`lbFused`/`latFree` have `LDev ..` arms;
  every "no fabric marker" statement reads "at ANY payload" (`∀ kd ba bs, …`; helpers `notDevOfBlock`, `execStepNotIo`
  (`WeakAxiomatic.lean:318`), `candWsIo`); `LIo` arms in every exhaustive `Lbl` match (label maps carry it, per-step
  lemmas refute it); the retired tier's `AidentT.IIo`/`IdentT.IdIo`.  **NOT done — MOVED INTO (I) [OWN.27] (a)**:
  `projLbl .LDev … = some (.LIo …)` (STILL `none`, `WeakPromiseBridge.lean:538` — the T1 bridge `wpPfBridge :925` sends
  every projected pf step to an `mstep … lb`, and `mstep` (`WeakAxiomatic.lean:142`) has no `LIo` arm until (I)'s
  `MStepIo`/`WPIo`), `lblRealizes`/`lblRealizesUnproj`, and the `lbAdmin` DROP of `.LDev` (241 uses in 49 files: the
  dev-block folding `isDevBlock`/`emDev`, `supplyOfFconf`'s `hblkQ`, `admRunDevfree`/`hemitDevfree*`, the `AxFetch*`/
  `AxEpiChain` peels, `tailSilentNoLabel` all pass MMIO steps through the admin stars — (I) deletes `hblkQ` and makes
  the I/O step a left-arm realizing step, (R) re-threads).  So today the tree has payload-carrying I/O labels
  everywhere but the GRAPH side does not see I/O yet (exactly the pre-(E) semantics — neutral, no new weakening); the
  **`LIo` SHAPE ARMS are `False`** (`gwf`, `candShape`, `mstepOk`, `AxScRun.gshape`/`shapeInB`, `gshapeB`, the
  Topo/Hull/Floor/ConfWit2 copies — `linCand` replays every graph event on the machine and has no `LIo` step until (I);
  `mnext (LIo ..) = σ`), flipped to `True` in (I)/(M); the taggers `dstep`/`dstepT` stay INERT on `LDev ..` ((F-dep)'s
  item (1) owns the payload's `asrc`/`vsrc`; [R38.2] only `dstepT` ever gets arms — `dstep` stays inert for good).  Next W13 steps IN PLAN ORDER [OWN.27]: (T) then (M) — **BOTH DONE
  (2026-10-11, tip working copy)**; **(I) — gate MET (W-DISK DONE 2026-10-12: the fused `DWriteDev`, the state-aware `pdevEv :604` and the interim
  `gfexecConf` clause `Fab.lean:633` it DELETES are in the tree; [R16.1 (iv)]; W-DISK-Q2/Q3 RULED [OWN.31][OWN.32]) —
  launchable in the graph lane when a worker is free [rev 28]**.  [The
  original (E) list, for the record: `projLbl :529-543`, `unprojLbl`, `lblRealizes*` (`WeakAxRealize.lean:240-280`),
  `lbAdmin :130-134`, `elabOk :547` (`True`), `elabWs :571`; exhaustive `Lbl` matches in 41 chain files + 30 `Ax*` files,
  `Wlabel.LDev` arms in ~35 files [R8.4].]  **(M) the model — DONE**: `lbIsMem := lbIsR || lbIsW || lbIsIo`
  (`WeakRvwmoGraph.lean:126`, deviation 6) so I/O events are in gmo; the chain's "a `gmem` event is a read or a write"
  case splits (~10 I/O case sites) are CLOSED by the `False` `LIo` shape arm of `gwf` (`WeakRvwmoGraph.gwfNoIo :739`,
  `gwfMemRW :747`) — exactly the sites (I) RE-OPENS when the arm flips; `fenceGob` (`AxSpinProt3.lean:393-395`) now
  stated on `lbIsR || lbIsW`; `rvwmoCatConsistentT`'s TEXT unchanged.  NOT done in (M): `gdexecQconfT`/`xv6ConfS` do not
  exist yet — the fabric clause is stated as **`gfIoDev :172`** (`GraphFabResidue.lean`: `gisIo (i,k) ↔ (i,k) ∈ gfDev`) for
  W12/W13 (I)/(W) to consume, and (I) RESTATES it per [OWN.31][R22.2] as `(i,k) ∈ gfDev ↔ (gisIo (i,k) = true ∨ dvi k ≠ dvo k)` —
  I/O-class by CLASS plus every fabric-moving row item (§A(†)) [R23.2]; `emDevfree`'s retirement (`Supply.lean:284`) is DEFERRED to (I)/(R) per [OWN.27] (W-DISK's `devQuiet`
  start-state hypothesis keeps it meaningful until then, §C W-DISK (ii) [R17.3]).  **(T) — DONE**: `Weak/GraphFabResidue.lean`
  (268; `Weak.lean:630`): `gisIo :67`, `gisR :73`, `gfBefore :79` (= `before GF.gfDev`), `ioResidue :84` with the four
  arms (R1)(R2)(R2′)(R3) [W2s][OWN.17], `ioResidueGmo :99`, `ioResidueNodev :119`, `ioResidueAcyclic :148` (the
  `ioObAcyclicNodev` rank proof re-done), `GraphFabResidue.ioResidueGwfInterim :184` (no `gwf` graph carries an `LIo`
  event until (I) — the item is satisfied for free, the pre-(E) semantics), the acceptance `w13fIoResidueOk :236` (the
  re-encoded `w13f`, gmo `MMIO₀ < MMIO₁ < st < ld`) and `w13fIoRevExcluded :261` (reversing the fabric order is excluded —
  not vacuous); header = the owner-rule Spec text.  **(I) realization — M–L, now M on the fabric side [R16.1 (iv)]**:
  `execProgOk'` UNCHANGED — the I/O step is a left-arm realizing step with fabric endpoints `dvi k → dvo k` (`hemitf`'s
  `HFone`, `WeakRvwmoFab.lean:253-259` [R28.s6], already has them); `gfexecConfIO` = `gfexecConf` (`:522-535`) with the `isDevBlock` clause
  `:533` REPLACED by the endpoint criterion **[R22.2]** `(i,k) ∈ gfDev ↔ (gisIo (i,k) = true ∨ dvi k ≠ dvo k)` — **[OWN.43][rev 35]
  PLUS the third disjunct `∨ the block of item k has a pdevEv-true step` (fabric CONTACT; the rev-35 paragraph below)** — (§A(†): I/O by
  CLASS, fabric-moving `DWriteDev`s by endpoint — the endpoints bracket the BLOCK (admin run + tagged step, `HFone`/`HFpair`
  `Fab.lean:242-259`) [R23.s1]; `fab (n+1) = fab n` at a non-moving member unless its admin block moved (an (α) ABORT's
  `pre` moves before START, whose own step keeps `d' = d`, `WeakEvInst.lean:488`; own-guard SKIPs after a moving `pre`
  are unreachable, so no non-I/O item is a member by an admin move) [R23.s1]; admin-run moves stay inside
  `hemitf`'s threaded fabric) (its `hblkQ :318` consumers `:318-503` change shape — the M; its size is unchanged by [R22.2]) and `emFetchImg`
  → `emZifencei` — **[R28.s5] (I) only RENAMES the slot** (content unchanged; **[R32.3] the merged 4-ary `Weak.emZifencei`
  `GraphFetchSpike.lean:312` is renamed `GraphFetchSpike.emZifencei` in the same commit, or the rename is deferred to G1 — worker's choice,
  launch addendum**);
  W5d-G G1 fills its content AFTER (I), keeping `Fab`/`Supply` single-writer (D26); **[R18.2 (c)]** (I) also DELETES W-DISK's interim `gfexecConf` clause "a `.PDisk` row's emission is
  `LDev`-free" (the Fab family's `devQuiet ∧ LDev`-free-disk-row hypothesis of `hemitfStatesQ`/`hartConffStatesQ` goes
  with it) — until then the INTERNAL bundle `gfexecConf` is vacuous for a device-active disk row (the
  `ioResidueGwfInterim :184` pattern; D39), and the published bundle `xv6ConfS` is (I)'s; the state-aware `pdevEv` of
  W-DISK is (I)'s input (`pdevEvFalse`/`pstepEvDevfree` already restated with `devQuiet` [R17.3]; (I)'s `Fab :318-503`
  edits rebase on W-DISK's threading);
  `supplyOfFconf`'s block folding `hblkQ` (`:689-701`; today `hblkQ :332`/`supplyOfFconf :789`) is **GENERALIZED, not deleted
  [OWN.43][rev 35]** (rev 26–34 said "DELETED, not generalized" — FALSE under W-DISK's state-aware `pdevEv`, below); T1 gets an inert arm
  `mstep.MStepIo`/`wpstep.WPIo` and `promiseFreeCompleteClean` (`WeakAxiomatic3.lean:1445` [R28.s6], 2k lines of label case
  analysis) carries it — the real (I) cost.
  **[rev 35] RESULT + RELAUNCH [OWN.43] (`../weak-orch/parked/PROGRESS-W13I.md`; workspace `xv6iris-weak-w3`).**  REALIZATION half
  DONE and MERGED: T1's inert arm `mstep.MStepIo : mstep σ i (LIo kd base vs) σ` (`WeakAxiomatic.lean:170`; `execStepNotIo` RETIRED;
  Lean-only `mstepIoInv`/`execSttIo`/`execWsIo`; `mstepOk`/`candShape` `LIo` arms `True`, carried through `promiseFreeCompleteClean`
  — statement unchanged —, `AxViolSubsume`, `WeakSrvwmoLitmus`); `projLbl (LDev kd b vs) = some (LIo kd b vs)` (`WeakPromiseBridge.lean:542`),
  `LDev` DROPPED from `lbAdmin` (`WeakAxRealize.lean:140`), `lblRealizesUnproj`/`lblRealizesIntro`/`mstepWpPfStepProg` gain the
  `LDev`/`MStepIo` arm (replayed as `PFDev`), `admStepPf` loses its `LDev` arm, `execProgOk'` UNCHANGED in statement; `wpPfBridge`
  carries I/O (`PFDev` → `MStepIo`); NO `wpstep.WPIo` — the pf I/O arm is the existing payload-carrying `WPDev`/`PFDev`; the `False`
  `LIo` shape arms flipped to `True` (`gwf`, `gwfLblShape`, `WeakRvwmoFloor.gshape`, Topo/Hull `lblRenShape`, `ConfWit2.lbShapeOk`,
  `AxScRun.gshape`/`shapeInB`, `AxGraphDec.gshapeB(Spec)`), re-opened sites closed (`finvStep`, `gtraceSnocStep`, Walk/Walkb);
  `gwfNoIo`/`gwfMemRW`/`ioResidueGwfInterim` RETIRED; the `fence rw,w` release lemmas in 11 `AxSpin*` files take the RAM-only anchor
  premise `(lbIsR l || lbIsW l) = true` (RVWMO/D48: the fence does not order I/O); `gswapUpperIsRead`/`AxProtGate` take a non-I/O
  premise; `tailSilentNoLabel`/`witnessInstrTailSilent`/`csyncAdvance` take "the realizing label is not `LDev`"; the retired opax tier
  keeps MMIO administrative (`AxOpsem.lbAdminAx`, `lbAdminAxOf`; `hemitAstep*` take an `LDev`-free-emission premise); all headers carry
  a "W13 (I)" deviation note; `lake build MachCSL Xv6 Weak` green.  **The FABRIC-BUNDLE half STOPPED: the [R22.2] criterion does not
  support the realization.**  *Spec first.*  RVWMO/riscv.cat/Sail have NO device-internal events; Zifencei and the PMAs are silent;
  virtio 1.x says nothing about when the device re-reads its state — `gfDev` and (R1)–(R3) are device-MODEL/trusted-surface text
  (D45/D49 class); no ISA order is at stake.  *The gap.*  `supplyOfFconf`'s conclusion fixes the supply fabric to `fab ∘ dcnt`: the
  global fabric changes ONLY at `gfDev` members, so a NON-member block at trace position `k` must be replayed from `fab (dcnt k)` back
  to itself, while the bundle pins only its ROW-LOCAL endpoints `dvi k = dvo k`; today this is bridged by fabric-BLINDNESS (`∀ d, hblk
  d d`, via `pstepEvDevfree`/`devQuiet`) — but under W-DISK's state-aware `pdevEv` a disk-row block can READ the fabric WITHOUT moving it
  (`DWriteDev` store/skip/abort evaluate `pre (dvirtio d)` and `g s`), so non-members are not blind.  *Counterexample shape.*  After the
  POP member (`dvo = fab (m+1)`, `phase h = .popped`) the IN-fill block `[(LStore …, some k)]` is taken from a row-local `dvi k` with
  `phase h = .fetched r` and `reqOf … = some r`: `preFill`/`reqGuard` give `s' = s`, so `dvi k = dvo k`, `(i,k) ∉ gfDev`, every
  `gfexecConfIO` clause holds — but at the global `fab (m+1)` the same node's `preFill` MOVES (`setPhase .fetched`), so no `pstepEv`
  block `fab (m+1) → fab (m+1)` realizes the store: `execProgOk'` at `fab ∘ dcnt` is FALSE.  Unreachable on xv6's runs (phases move
  only by the disk's own program; every store/skip after a moving `pre` moves; non-moving skips/aborts only precede `LDev` START/UART
  blocks — members by class) — the gap is in the GENERIC bundle.  For the same reason "DELETE `hblkQ`" needs the supply to run at
  row-local endpoints everywhere, i.e. option (c)'s trace hypothesis.  *Options (marks against RVWMO/Sail/Zifencei/PMAs — all silent —
  and against [R22.2])*: **(a) membership by fabric CONTACT** — `(i,k) ∈ gfDev ↔ gisIo (i,k) ∨ dvi k ≠ dvo k ∨ the block of item k has
  a `pdevEv`-true step` (W-DISK's marker; `hemitf` records per-item quietness); non-members are `pdevEv`-quiet ⇒ fabric-preserving AND
  blind (`pdevEvOk`), `supplyOfFconf` goes through with the `∀ d` folding GENERALIZED, the interim clause deletable; FAITHFUL to RVWMO,
  EQUAL to [R22.2] on every xv6 run, STRONGER than [R22.2] as generic trusted text only by unreachable non-moving fabric-touching blocks
  ((R3) then orders them); cost M (the planned (I) delta); **(b)** keep [R22.2] + a bundle clause "every non-member block is
  fabric-blind", discharged by W14 from a `virtioProg` program-structure invariant — FAITHFUL, EQUAL on xv6 runs, a STRONGER conformance
  premise; M + an S–M W14 obligation; **(c)** keep [R22.2], supply at row-local endpoints, `hblkQ` deleted, with a TRACE premise "at a
  non-member position the global fabric equals the row's `dvi`" — (L)'s `ptraceRelIO` (`ptraceRel ∪ gmo|IO`) does not order a disk RAM
  store against another row's MMIO write, so the premise stays UNDISCHARGED: WEAKER (an unproved premise on the published path); not
  recommended.  **[OWN.43] RULED (a)** (13:59 2026-10-12; §D Q-GFDEV-contact); §A(†) updated.  Blocked with it, now unblocked:
  `gfexecConfIO`, the interim-clause deletion, `hblkQ`'s fate (GENERALIZED), `emFetchImg → emZifencei` in `gfexecConfIO`, and W5d-G
  G1–G5's `Fab`/`Supply` text.  **Remaining work = the rev-35 launch paragraph at §C top** (deliverables (1)–(6), files, rebase surface,
  acceptance) — **LAUNCHED at rev 36 (w3) with [R32.3] as a launch addendum; [R32.s3] (the `tch` carrier) and [R32.s6] (cites) recorded
  in that paragraph — DONE and MERGED 2026-10-12 [rev 37]: the landed form (the carrier is named `tq`; `gfexecConfIO` REPLACES `gfexecConf`;
  `gfIoDevOfConf`; deviations `tq` on `hemitf`/`hartConff`, `∀ i, devQuiet (boot i)` on `gfexecConfOfQconf`/`cycleKillOfF`) is recorded at §C top.**
  **(L)** T2-1c″ (M–L): `ptraceRelIO := ptraceRel ∪ gmo|IO` (`Lin2.lean:
  124`); I/O events are rule-14 ANCHORS like writes — `gnxw` (`Lin.lean:440`) → `gnxa` "next own write or I/O event",
  `glinEids :455`, `linCand :471`; **[W2s] under G3-Q (a″) DISK-ROW READS are anchors too (`gnxa` ∋ row-`NCPU` reads;
  trace ⊇ gmo between a disk read and every write; the pf `candDiskLat` then follows from `gloadValue`; +M)**;
  `gtraceLinearizationMin :623` restated, I/O steps no-ops for the cand;
  `fconfSupply'`'s `before L` premise (`:1000`) and FabInd's handed-back `trDevOrdered` (`:407`) are DISCHARGED from
  `ptraceExtIO` (fab order = the trace's I/O order = gmo|IO by (R3)).  **DONE and MERGED 2026-10-13 (w4) [rev 42] — the landed form,
  deviations D1–D3 and the residual premises are at §C top (Rev 42 RESULTS); the clause "= gmo|IO by (R3)" was TOO STRONG for the non-I/O fabric
  members → Q-L-R3 RULED (a) [OWN.53], W13 (R3′).**  **(K)** the kill (M–L; **[rev 42] LAUNCHABLE — the second batch, (R3′) its first increment,
  §C top; DONE and MERGED 2026-10-13 12:30 (w4) [rev 44] — `Weak/WeakRvwmoKillIO.lean` 708, Rev 44 RESULTS; its three open items are PLACED: check (ii) → W11 (i), check (i) on the cat chain → W13 (K-cat), the unused `gfexecConfHull` premise → FabInd-S (§C top THIRD LAUNCH SET)**): `racyDIO := racyD ∪
  ioResidue ∪ gmo|IO`; the cross kind `gmo|IO` and the same-row arms (R1)–(R3) are gmo-forward by (T) directly, so
  KillArms' chain composes in `gmoLt` AS TODAY (no `tc ioOrd`); segments ENTERING at an I/O event and exiting at a
  WRITE are free by (R2); `csChained` (`KillArms.lean:499`) generalized to "entry = any `gmem` event of the critical
  section" (S–M); `normalizeOfAcyclic` over `racyDIO` keeps I/O positions (its topo order ⊇ gmo|IO) **and the
  disk-read anchors (G3-Q RULED (a″); one more `racyDIO` disjunct, S–M) [W2s]**; `gdHull` keeps
  I/O events and filters `gfDev` → `cycleKillIO`, through `hullRun`, W11, W12.  **(R)** the re-thread of the
  constant-fabric chain onto `gfexecConfIO`: measured 8.6k lines / 14 files / ≈ 140 bundle mentions / 52 `fun _ => d0`
  sites (Supply, LinInd, Cert4, Glue, Glue2, Walk*, Progress, PreNorm*, Capstone); segments without I/O events have
  `dvi = dvo` and reuse the constant-fabric lemmas verbatim; witness files embed via `gfexecConfOfQconf`; KillArms,
  Hull, Lin unchanged except the new arms (L–XL, the bulk).  **(W)** `xv6ConfS` on `gfexecConfIO` + **W13-wit** (M–L; `gfDevWIo`'s discharge: HART half PROVED, DISK half the
  NAMED `usedElemGateOk` for W14 — §C top [R41.4]):
  hart 0's run `_entry → … → uartinitone` (entry `0x80000896`, `Xv6/KernelImage.lean:1515`; the `jal` at `:1590`) to
  **its first UART store, `sb zero,1(a5)` at `0x800008a0` (`:1525`, IER := 0)** [R6.5b] — the EVENT `LIo .wr
  0x10000001 [0]` in row 0, the first candidate with a non-empty `gfDev` (D31); ≈ 100 dynamic instructions, NO MMIO
  before it (`timerinit` is Sstc CSR-only, `Xv6/SpecTimerinit.lean:5-7`), by kernel evaluation on W5c's `esilAdmRun`;
  **gate 2 [R7.3c]: a device-ACTIVE DISK witness** "first disk START → DRead/DWrite → COMMIT" on the disk row (the first
  disk request is `fsinit`'s `bread(dev, 1)`, `Xv6/SpecFsinit.lean:7`, on the first `forkret`, past `kinit`'s
  `freerange` — shares D44's infeasibility, so W14 covers it).  **(F-dep) — IN SCOPE, D50 RULED (b) [OWN.17] — DONE and MERGED 2026-10-13 12:50 (w3) under (A1) [OWN.52] [rev 44] (Rev 44 RESULTS; OPEN: `gdexecQconfT` still requires `emDevfree`, `CatLinChain.lean:330`, so the I/O-endpoint edges first MATTER at W13 (W)'s `xv6ConfS`) — (M–L ≈ 1k, three increments
  [R38.3]; owner files `Weak/AxDeps.lean` + `Weak/WeakEvInst.lean` + `Weak/WeakPromise.lean` (`Wlabel.LDev :89`) + `Weak/AxSpinGate.lean` ((0c)
  only) — `Weak/WeakRvwmoConf.lean` is NOT an owner [R38.2]; after (E); **STOPPED GREEN 2026-10-13 before any edit** (`PROGRESS-W13Fdep.md`),
  RELAUNCH per the launch paragraph)**: **(0) THE GRAPH-SIDE MODEL TEXT — option A, the first green increment after the sweep (statement
  commit, S–M) [R38.1].**  The gap: `gtdepsWf` (`AxDeps.lean:168-171`, a conjunct of `rvwmoCatConsistentT :208-211`) demands `glblIs G e.1.1
  lbIsR` of every source and `lbIsW` of every `dtagW` target (`DTdata`/`DTctrl`/`DTtrans`/`DTr13`, `:150-152`; only `DTaddr`/`DTctx` targets are
  `gmem`); `lbIsR`/`lbIsW` are `false` on `LIo` (`WeakAxiomatic.lean:174-182`, D47 (a)), so the D50 (b) edges of (1)–(3) make `rvwmoCatConsistentT GT
  ∧ gdexecQconfT GT` UNSATISFIABLE on every I/O-active row — hart 0's first `printk` (`consoleinit → consputc → uartputc_sync`, `0x800009ac–
  0x80000a14`): `acquire`'s RAM loads → the never-reset `dtCtl` (`:461-463`) → `DTctrl` into the THR store `sb a5,0(a3)` `0x800009fa` (an `LIo .wr`,
  `dtagW DTctrl = true`, needs `lbIsW`); the LSR poll `lbu a5,0(a4)` `0x800009ec` → `beqz` → the same store (an I/O-load SOURCE, needs `lbIsR`);
  `uartwrite`'s THR `0x80000988` (`DTdata` from the RAM tx-buffer load); virtio init's six address-register stores `0x80005a46…a70` (`DTdata` from the
  `disk.*` loads); FEATURES → DRIVER_FEATURES `0x800059b2` (I/O→I/O data) — VACUITY ("no graph conforms"), not a false ordering.  Spec: riscv.cat's
  `r9`–`r13` are written `[M];addr;[M]` etc. in herd — reads in effect, only reads have register sources [R39.s5] — and range over ALL reads/writes (herd has no I/O class); appendix (c1) keeps ppo 9–13 when one access is I/O; Sail/Zifencei/PMAs SILENT on
  dependencies.  **(0a)** `gtdepsWf G deps := ∀ e ∈ deps, same row ∧ po-forward ∧ glblIs G e.1.1 (lbIsR ∨ lbIsIoRd) ∧ (if dtagW e.2 then glblIs G
  e.1.2 (lbIsW ∨ lbIsIoWr) else gmem G e.1.2)`, `lbIsIoRd (LIo .rd ..) = true`, `lbIsIoWr (LIo .wr ..) = true`, `.dev` events in NEITHER (device-side
  fabric moves carry no hart register dataflow, D49) — FAITHFUL to riscv.cat's `R`/`W` under (c1); `gtdepsGmo :174` unchanged (every edge gmo-forward).
  **(0b)** the chain projections filter the SOURCE too: `forgetDeps :178` and `gtAd :187` [R39.s1] keep edges with a `lbIsR` source and a `lbIsW` target (`gisW` +
  a Bool `gisRd`), so `catTAd :301` (via `gtdepsWfAd :292`/`gtdepsGmoAd`), `catTForgetAxioms :340`, W12's `catADOfCatT` (`CatOfMinusSpike.lean:37-43`)
  and `RvwmoXv6ScaT.lean:790` (`linCandScaTMinusA` [R39.s1]) keep their STATEMENTS; `CatLinChain.gdexecQconfTForget :331-338` (W12, landed) proves `forget GT` membership from the `gisW` TARGET fact only and now takes `hartConfRowDepsWf`'s SOURCE conjunct `lbIsR` (`WeakRvwmoConf.lean:837`) — S, the file joins (F-dep)'s list [R39.2] — the untagged chain sees FEWER deps (sound: the residue arms (R1)/(R2), `GraphFabResidue.lean:
  84-99`, carry the RAM→I/O and I/O→RAM-store orderings for the chain, as today); `catTOfCat :316`'s side condition `gtdepsRdOk :310` widens to
  "every edge `forget` drops" (read-targeted OR I/O-endpoint), still discharged by `tw`/`tw2` (§5; no I/O there); the `AxDeps` header's deviation list
  gains "`gtdepsWf` admits I/O endpoints (Rocq's is RAM-only)".  **(0c)** `AxSpinGate.gsrcT :205` filters its sources to `lbIsR` reads (the
  `filterMap` gains `gisRd d.1.1`); `gsrcTSpec :210`, `gsrcTSrc :247` (target conjunct `lbIsW ∨ lbIsIoWr`, or dropped — `gsrcTReal' :272` uses only
  the source conjunct), `gsrcTSrcPo :262` restated; `ctrlClosed :232` UNCHANGED — its quantifier asks for closure onto RAM-write targets only, and the
  never-reset `dtCtl` satisfies it for I/O-sourced edges and I/O-store targets too, so NO new premise reaches the LB roots [R38.s4]; the registered
  roots (`allocpidOpen`, `AxSpinT2b.lean:251`, `HconsT : rvwmoCatConsistentT GT`; 13 `Hcons := catTAd GT HconsT` files; `rvwmoCatConsistentT` in 35
  files, `gtAd`/`gtAdGd` in ~94, `gsrcT` in 6) keep their TEXT; their PREMISE is now weaker — a strictly stronger theorem, no re-registration (§A(6);
  `tools/ci/roots-weak.txt:13-18` gloss).  **(0d)** the Bool/SC tier in step: `gtdepsWfB :776`/`gtdepsWfBSound :784` (`AxSpinSpike.cDw :658`,
  `AxScCat.scGraphB :249`), `AxScCat.scGraph :112`/`scTdepsGmo :154`/`scPpo :168` (an `LIo` source's `gmem` from `lbIsIo`, not `glblIsRGmem`),
  `AxScRun.gDepsWf :1356` (`rowEdges` generalized).  **(0e) rule 12 from an I/O-load source — RULED (A1) [OWN.52] (rev 42; the (A2) text below is the RECORD, superseded before any code took it; `catADOfCatT` is now in W12's
  landed `Weak/CatLin.lean:54` and the spike `CatOfMinusSpike.lean:37`, both (F-dep)'s to edit)**: (A2) was: `gppoCatT :198` [R39.s1] UNCHANGED
  over the source-filtered `gtAd`, so the `[IoR];(addr|data);[W];rfi;[R]` instances are OMITTED — WEAKER than riscv.cat by exactly them (sound), NAMED
  in §A(3); **if Q-FDEP is RULED (A1)**: `gtAdFull G deps` := the addr/data edges into `lbIsW` targets from ANY source, `gppo12T`/`gppoCatT` over it,
  `catTAd` and `catADOfCatT` close by `gppo12` monotonicity (`gtAd ⊆ gtAdFull`, one line each — the second in W12's file after W12's statement commit,
  or by W12 [R38.6]), `AxScCat.scPpo :168`'s rule-12 case re-cased — S, a separate increment (`gppoCatT` is used directly only by `AxScCat`).
  Acceptance for (0): build green; the tagged premise is SATISFIABLE on an I/O-active row BY COMPUTATION — `gtdepsWfB` over `rowDepsT` of W13-wit's
  row (or of `tw` extended by one `LDev` item) evaluates `true`, kept as a PERMANENT smoke test beside `catTConsistentBSound` (the check that would
  have caught the gap; **[R38.s1] the same computed check is a standing acceptance item for EVERY conformance text — (W)'s `xv6ConfS`, W12's
  `gdexecQconfT`**).  **(1)** the `LDev`/`LIo` payload gains `asrc` (rd) / `asrc vsrc` (wr) — an ARITY change of `Wlabel.LDev` (`WeakPromise.lean:
  89`): ≈ 180 positional constructor sites in 35 files (grep; R38 counts 177/35, the worker 146/38; file list in the launch paragraph), landed as
  increment (1) ALONE (mechanical, one build) so W12 and (L) rebase ONCE [R38.3]; filled by `pnodeStep`'s MMIO arms (`WeakEvInst.lean:316-320`,
  `LDev .rd` `:319`; `:351-356`, `LDev .wr` `:355` [R38.s3]): **`LIo rd`'s `asrc := depsAsrc (depsOfIb ib.ibBits)` as the `LExLoad` arm does
  (`:345-346`), NOT as the plain `LLoad` arm, whose `asrc` is D-8's `[]` (`:336`; `AxDeps.lean:405-406`; `WeakAxiomatic3.lean:2065-2067` "rule 9
  (LOAD half) OMITTED BECAUSE OF D-8") — a worker mirroring `LLoad` would emit NO addr→I/O-load edge, i.e. D50 (a)
  [R11.4]; `LIo wr`'s `asrc/vsrc` as the `LStore` arm (`:351-356`)**; `oib` stays `none` ("`ib` unchanged" [R11.s1]);
  the I/O item is already tagged `(l, some k)` (§A(†)); (2) **`dstepT` arms ONLY (`AxDeps.lean:461-479`) [R38.2]**: `LDev .rd` = the `LLoad`/`LExLoad` arm
  SHAPE (`dedgesR :445`: ADDR edges in, `k :: dtLd` provenance OUT, `dtAcc` for rule 13, NO ctrl — exactly
  "no ctrl → I/O load"), `LDev .wr` = the `LStore` arm shape (`dedgesW :448`: addr/data/ctrl/trans/r13/ctx in); `dev`-kind
  items stay inert; **the UNTAGGED `WeakRvwmoConf.dstep :497-499` is NOT edited** (DEVIATION recorded in the `AxDeps` header: the untagged tree
  never sees I/O edges — sound; `gfexecConfIO`'s `rowDeps ⊆ gdDeps` (`Fab.lean:857`) and `gdepsWf` (`Graph.lean:629-631`, RAM read → RAM write,
  under `gfexecConsistent :864` → `rvwmoMinusDepsConsistent :638`) stay RAM-only; the chain's I/O orderings are (R1)/(R2)) — an untagged `LDev .wr`
  arm would put W13-wit's own target edge `ld a5,0(a0)` `0x8000089e` → `sb zero,1(a5)` `0x800008a0` (`KernelImage.lean:1523-1525`, an ADDRESS edge
  into an I/O store) into `rowDeps`, falsifying `gfexecConfIO ∧ gfexecConsistent` for row 0 and `gdexecConfDepsWf` (`Conf.lean:934-940`, concludes
  `lbIsW` targets) — the non-vacuity witness dies; and W12 (1)'s `rvwmoCoreD` is stated over that SAME untagged `gdepsWf` — the reason option (B)
  (loosen both models) is rejected; (3) **the I/O-load edges are the FIRST load-half `DTaddr` edges the emission produces** [R11.4]:
  RAM loads stay D-8-masked (rule 9's RAM load half remains omitted — a faithful ADDITION, not a D-8 unmasking);
  `lbLdepfree`/`pstepEvLdepfree` constrain `LLoad` ONLY (`WeakPromise.lean:112-115`), so an `LIo rd` with sources does
  not falsify `wpPfStepInv`/`pstepEvLatFreeHalf`/`pstepEvLatFreeProg`/`pstepEvTsOblivious` (`WeakEvCapstone.lean:238,
  714,1048,1058`); `rowDepsTAddr` (C) already admits `DTaddr` edges into pure READ items (`AxDeps.lean:702-707`);
  **proofs re-opened [R38.2]**: `dstepTState :592` becomes "the tagged state with I/O-load positions erased from `dtLd`/`dtProv` equals the
  untagged state" (or a pointwise INCLUSION invariant untagged ⊆ tagged); `rowDepsSubT :690` KEPT via that inclusion (tree edge ⇒ tagged edge);
  `rowDepsTSub :695` restated for RAM-read-sourced edges; `rowDepsTAddr :702-707` (C) gains the disjunct "or targets an `LDev .rd` item" (its
  `elbIsR` test, `Conf.lean:448-451`, is `false` on `LDev`); the pin bridge `pinSegPin`/`pinSegPin'`/`checkerTaintSubProv` (`PinBridge.lean` 21 sites,
  `PinBridge2.lean` 11) — DIRECTION [R11.4]: `pinSegPin` consumes "`rowDeps` ⊆ `gdDeps`" and proves checker `PDep` ⇒
  edge (`PinBridge.lean:312-316`), `checkerTaintSubProv` proves checker taint ⊆ provenance (`PinBridge2.lean:518-521`)
  — both PRESERVED when `rowDeps`/provenance GROW, so `gen_weak_pins.py` need not tag MMIO reads unless xv6 pins are
  to USE MMIO-sourced dependencies (none expected; rev 14's "or state the correspondence for RAM items only" was the
  wrong dichotomy), the `LDev` sweep sites of (1) (`WeakRvwmoSupply` 18, `WeakRvwmoFab` 12, `FabInd` … — not "`Supply` 4, `FabInd` 2"
  [R38.3]), the witness files (`ConfWit2` 3, `CycWit` 4, `Adm` 5 — `LDev`-free rows, trivial), the retired `Ax*` tier (`AxGate`
  30, `AxScRun` 28, `AxScCat` 33, `AxFetch5` 8 — new arms only, must build); `gdexecQconfT`'s trusted-surface TEXT now
  covers I/O items AND `rvwmoCatConsistentT`'s text changes in the one definition `gtdepsWf` (named: §A(3)/(6)/(†) [R38.1]).  **Coverage check against (R1)/(R3)** (§A(†)): in-edges from RAM accesses ⊆ (R1),
  from I/O loads ⊆ (R3); out-edges into RAM STORES ⊆ (R2); the one class beyond the residue is I/O-load →addr→ RAM
  LOAD (rule 9) — expected absent in xv6 (**unverified** census; a hit would be a graph-tier PIN, never a STOP).  So
  (F-dep) changes the trusted PROSE (the (F3) uses move to the graph tier) and the published quantifier at most by
  that class.  **[W13c] The census settles it for THIS image: rule-9 graph hits NONE** — 16 static MMIO loads traced to
  a fixpoint (`notes/W13-io-census.md` §(a)); the only AMO is `amoswap.w.aq` `0x80000c74`, no `lr`/`sc`, and no
  `acquire` call site's `a0` is reached by an MMIO value (the `uid` arguments are constants chosen by control); ONE
  D-8-masked ISA instance — `printint`'s `lbu a5,0(a5)` `0x800004c0` = `digits[irq % 10]` from `devintr`'s
  "unexpected interrupt" `printk`, whose location is never written (`textPristine`; `kernelData_digits`, `Xv6/
  KernelData.lean:2420`), so no edge is emitted and nothing is lost; the in-edges into I/O events come from RAM
  (`uarts[i].base`, `disk.*` pointer words — (R1)), I/O-load → I/O-store data edges (FEATURES → DRIVER_FEATURES, STATUS
  → STATUS/ACK, irq → complete, RHR → THR echo) are (R3), I/O-load → RAM-store edges (data, and ctrl via the never-reset
  `dtCtl`) are (R2); classes that never occur: addr → RAM store, addr → I/O access, addr → LR/AMO; no jump table is
  MMIO-indexed.  Cite drift (minor): D-8 plain-`LLoad` `asrc = []` is `WeakEvInst.lean:322`, `LExLoad`'s `:331-332`, the
  `LDev` arms `:305`/`:341`, "rule 9 (LOAD half) OMITTED" `WeakAxiomatic3.lean:2076-2077`.
  **(F-fence)/(F-trap)**: OUT, prose only (D46 RULED (a)).  Risks: **R2′** the alphabet sweep touches ~70 files including the retired `Ax*` tier (mechanical, one
  build) — DONE (85 files); **R5 — RE-ASSESSED [W13c]: STOP candidates NONE for this image, by composition** — rev ≤ 18
  said an I/O-ENTRY / READ-EXIT segment (I/O event →po→ racy read →fr→) has NO fence pin (rule 4 skips I/O) and must
  close by lock discipline or (R2)-rerouting, naming the PLIC claim/complete races, `plicinithart` and
  `pr.locking`/`panicked` (the last two DO NOT EXIST in the image, §B(9)); the census's **Claim L-IO** (an ARGUMENT, not
  Lean): `segPin` is one DIRECT rule-4/5/deps edge, but a segment is an `rtc rsame` path and `Cert.Pinned` needs only
  `gmoLt entry exit` (`KillArms.lean:294`) — with (K)'s same-row relation `rsameIO := gpow ∨ gppo ∨ deps ∨` the same-row
  arms of `ioResidue`, any path through an I/O event `x` gives `entry <gmo x` by (R1) (entry is RAM, po-before `x`),
  and every later event is gmo-after `x`: a RAM write by (R2), an I/O event by (R3) (fabric steps too), a RAM read via
  its `gppo`/`deps`/(R2′) in-edge from an event already gmo-after `x` — so the I/O event is a COMPOSITE pin.  Hence (K)
  may STATE this as a lemma (`ioSegPinned`, S–M) with TWO PRECONDITIONS to CHECK in Lean before relying on it: (i)
  `racyDIO` adds NO same-row edge INTO a read outside gmo ((F-dep)'s new edges must stay ⊆ gmo, as `rvwmoMinusDeps-
  Consistent`'s deps do, `Glue.lean:237,240`); (ii) **[rev 28 CORRECTED — W8-design §0 item 7, `notes/xv6-holding-race.md`]** the `lk->cpu` read at
  `holding+0x12` (`0x80000c04`, `PResidue`, `KernelPins.lean:255`) is NOT lock-protected: `acquire` calls `holding()` BEFORE
  its AMO, so a NON-holder reads the holder's PLAIN, still-unpublished `sd a0,16(s1)` (no fence after the AMO) — a genuine
  data race, benign because the value only feeds the `== mycpu()` compare and no hart can read its OWN pointer (its latest own
  entry is the 0 of its last `release`; `lkCpu_read_not_mine`, `MachCSL/Lock.lean:18-22`).  The precondition is therefore
  W8's **`lockWordDiscAt`** (every post-registration lock-word write a whole-word 0/1, a 0 only by the holder; every `lk->cpu`
  entry 0 or the writer's own `&cpus[w]`, written by the holder — `lockWordAt`/`lkCpuAt`, `Lock.lean:53-56,18-22`), fed by
  **W8-β′**, NOT `wprotAt`; the RAM kill of the same read routes through it too (rev ≤ 27's "`wprotAt` covers `lk->cpu` under
  its OWN lock" is WITHDRAWN; the plan's (iii) is false at this byte — the export exempts lock-layer bytes, §C W8).  Under the
  W12 CAT chain `racyDSplitC` moves rfi into `rsameC` and rfi ⊄ gmo (forwarding): the invariant becomes "gmo-after `x`,
  OR a read forwarded from a write gmo-after `x`", closed under every ppo/deps step EXCEPT a `PR∧SR∧¬PW` fence — the
  image's only one is `fence r,rw` `0x80000ee6` (harts ≥ 1's `started` spin, reached only BEFORE their first I/O
  event; hart 0 skips it) — an IMAGE fact to be named; user-mode code after `sret` (fs-image binaries) UNVERIFIED for
  that sub-case.  Per-site table (census §(b).2, rows 1–8): C1 `lk->locked` at `holding` `0x80000bf2` (unlocked —
  composite-pinned or vacuous: in `release(L)` the hart's last access to the word is its own amoswap po-before the
  I/O event, nothing has a ppo/dep edge into the read; the one NAMED composite pin: `release` store `0x80000cfa` then
  `gpoloc` W→R = rfi under cat); C2 `lk->cpu` `0x80000c04` ([rev 28] a RACY read for EVERY acquirer — the holder's plain `sd` is unpublished, so the
  census's "held: CSchained under `L` itself" is WITHDRAWN (the reader is never the holder at `acquire`'s `holding()`; the
  holder's own `release` → `holding()` read is its own write, forwarded, no cross-hart edge); closed by `lockWordDiscAt` +
  `lkCpu_read_not_mine`, the lock-layer route of W11 (i)/W13 (K)); C3 the
  `cons` ring fields after a `consputc` echo and the `vdisk` state after NOTIFY/STATUS/ACK — CSchained (`cons.lock`
  `0x80012420`, `vdisk_lock` `0x80023af8`), the (R2) step to the release store IS the "(R2)-rerouting"; C4 the
  DMA-written ring words after STATUS/ACK (`used->idx` `0x80005d5e`, `used->ring[].id` `0x80005d76`, `info[].status`
  `0x80005d82`) — writer = the disk row, NO lock, `Bad` NOT available, the window passes `fence` `0x80005d54` (no RAM
  write before it after the I/O) — composite-pinned VACUOUSLY (the only candidate predecessors are `ld disk.used`
  `0x80005d58` — an addr edge, D-8-masked — and `lhu used_idx` `0x80005d5a` with no ppo relation; from the second
  loop iteration `fence` `0x80005d66` pins via `0x80005d92`/`0x80005da4`); C5 open continuations (`plic_complete` →
  `kerneltrap` → `sret` into any SIE = 1 kernel code; `printk` returning to `balloc`/`ialloc`/`ireclaim`/`install_trans`/
  `syscall`/`usertrap`/`main`/`devintr`/`panic` — `procdump` has NO caller, dead; `uartwrite` through `consolewrite`/
  `filewrite`) — covered UNIFORMLY by L-IO, no per-site list possible or needed.  Windows end at the next `amoswap.w.aq`
  (or a `PW∧SR` fence with a RAM write between — only the four virtio `0x0ff0000f`; `fence rw,w` `0x80000cf6` does not
  close one); `holding()` runs BEFORE the amoswap inside `acquire`, so every window holds a C1 read AND a C2 read (both racy, both
  lock-layer bytes under `lockWordDiscAt` [rev 28]); **C6 [R25.1 (d)] kernel PTE reads by the WALKER** (every fetch/load/store
  translation in the window) — RACY against other harts' hardware A/D write-backs (`KptInv.lean:4-8`; Svadu ON,
  `SpecStart.lean:29,40`), the source is `.WCexcl` (`WeakKptStale.lean:26`), so never a `badSeg` source; the walker is
  variant-insensitive (`WeakKptStale`'s racy-absorption theorem); covered by `pteDiscAt`, no chain needed — **[rev 31][OWN.39] the
  USER-table PTE reads of a migrated process's walker are C6 too** (the previous hart's A/D write-back, `WpPtWalkOwn.lean:501-515`,
  reaches the new hart under `p->lock` in the TSO proof but an A-bit update may be speculative under the priv spec, so the
  `pte-key` arm, not a chain, covers it; same `.WCexcl` source, same `pteDiscAt`).  Excluded as
  non-racy (no concurrent writer): own stack/trapframe page, own `cpus[tp]`, `uarts[i].base/.rx` (`DFrac.discard`,
  `Xv6/UartInv.lean:63-69`), `digits`/format literals, `disk.desc/avail/used` (`diskGeom`) (NOT `kernel_pagetable`'s entries —
  moved to C6 [R25.1]: `KptInv.lean:4-8` says every hart's hardware writes them), `p->trapframe` of the running process,
  everything hart 0 reads during boot.  Verdict: R5 is NOT a STOP for this image;
  it becomes (K)'s `ioSegPinned` lemma + the two checks; **R6** the `gmem`
  case splits of (M).  Deps: W5c's `esilAdmRun` ✓; W5b's shape clauses ✓; `AxDevGraph.lean` (`Dlbl :134-142`, `dstep
  :152`, `DevConsistent :226-236`) as the device-step precedent for the `dev`-kind replay (its separate-row encoding is NOT what [OWN.14] rules).
- **W14 `Weak/ExistWitness.lean`** **[rev 46] + DISCHARGE `usedElemGateOk` (`GraphFabConf.lean:310`): the shape-to-gate invariant of `virtioProg`, the run-level
  gate from the disk invariant, the computed Bool twin on THIS witness (§C top STAGE 2 ROADMAP (rev 46)); else it stays a named device-model premise** — (NEW; D44 RULED (i) [OWN.11]; L–XL — the spike's table confirms the SC run
  satisfies `candScaT`/`candDiskLat` trivially, every load at the top [W2s], and the corrected (a′) likewise: stamps
  ≤ top, resets harmless [R11.s5]): the single-execution EXISTENCE theorem — ONE device-active TsoMem-side run (a `-<κs>->ₜₚ^[n]` run from
  `PowerOn` reaching `allocproc`, from the SC tree's reachability, not evaluation) lifted to a conformant cat candidate:
  a `GT` with `rvwmoCatConsistentT`, `ioResidueGmo`, `xv6ConfS` and a non-empty `gfDev` whose realization is that run —
  (↑) of W2 for a SINGLE run (not receptiveness, D15).  CHOOSE the SC run (every load at `tvn := top`, stores at the
  top, I/O events at their trace positions) so the graph is the trace's own (`gmo` = trace order of writes and I/O
  events, `fab` = its I/O restriction; (R1)–(R3) by construction) and SC ⊆ RVWMO makes it cat-consistent TRIVIALLY
  [R8.s3]; the fetch clause by `fetchPinCutOk`/`gzFetch` at tag 0 (kernel text) and the TsoMem `itv` (user text).
  Certifies non-vacuity AT `allocproc` ([OWN.3]); until it lands the header carries D44's caveat.  Deps: W2 CLOSE ✓
  (`pfStepTso` landed [R21.s4]), W-DISK (the disk rows it certifies are the ALIGNED program's) and
  table; W5b ✓; W13 (E)/(I)/(W); W5d-G.  Risk: "reaches `allocproc`" is LIVENESS-flavoured reachability of the SC tree,
  which exports safety only — a dedicated SC-tree lemma ("some run reaches `userinit`'s `allocproc` call") may be needed, M–L, **unverified**.
- **W8 `Xv6/AccessDiscipline.lean` + W8-β′ + W8 (f2-ctx) + the (r2) root** (D24 FIXED) [R4.3][R4.s3][R4.s4]; **[R21.1]
  Q-W8-lane RULED (α) [OWN.36] (W8-design first, then the serial MachCSL work before W-RSV) — RE-SIZED by [OWN.37] (Q-W8-feed
  RULED (a), rev 28): W8-β′ (M) → R-ctx gate (S, read-only) → W8 (f2-ctx) (L–XL, 2–4 rebuilds; fallback (f1) per part);
  export `xv6AccessDisc`, root (r2) `xv6DiscAdequacy_closed`.  W8-design is DONE (2026-10-11/12, `notes/W8-design.md`,
  read-only, nothing built; R24's s1–s6 folded); its results follow the spec text below.**
  **W8-design** (S, read-only; reviewed before W8 proper — DONE) pinned: (1) **the export statement** (fixes D24) — a Lean skeleton
  over `MState`'s per-byte histories (`HEnt.tid`/`HEnt.t`) and the author log for (i) ownership — **[R23.1] with a DYNAMIC
  per-byte owner**: process kernel stacks MIGRATE between harts at `swtch` (`wp_swtch_body` resumes on ANY hart `h`,
  `Xv6/SpecSwtch.lean:35-58`; the payload carries `stackOwn w1 av`, `Xv6/ProofSwtch.lean:140`; `stackOwn` is `DFrac.own 1`
  per word, `MachCSL/KCtx.lean:256-257` — exclusive ownership that CHANGES HANDS), so the skeleton states "every write to the
  byte since the last HANDOFF is by the current owner; a handoff is `swtch` under `p->lock` (release by the old hart's
  scheduler, acquire by the new one's)" — or classes process-context `PStack` under (ii) with `p->lock` ACROSS the handoff
  (the access is made with the lock RELEASED, so `wprotAt`/`wlpAt`'s "held" shape must be checked for fit; a third shape
  "owned since the lock handoff" is the likely answer); only `PPerCpu` (`cpus[tp]`) and the fixed per-hart boot/scheduler
  stacks (`stack0`; `scheduler` never returns) are STATICALLY owned, and the target runs on both (hart 0's boot stack in
  `userinit`, the caller's `p->kstack` in `fork`), (ii) lock-protected
  access, (iii) no foreign owned-unpublished message, checked against how W11 (i) `badSeg`/(ii) `protReg` consume it
  through `rmem`'s `R-log`/`R-hist` (`PfStepTsoMem.lean:57,62`); (2) **the ledger's file/lane** — ghost-only in
  `memModelAt` (`MState`/`Lang.lean` unchanged, so W4's `SimRel` and W2a's `rmem` are untouched), or name the machine
  field and its `Weak/` cost; (3) **whether a ledger-free (β) export** (D24 (c): W9a's static pin check + ownership
  facts proved in `Xv6/` at adequacy) covers (i)/(iii) — **[R23.1]** for (i) it can cover only the STATICALLY owned bytes — if so W8 SPLITS: (i)/(iii) an `Xv6/`-only parallel item, (ii)
  the ledger — ANSWERED (W8-design §4): NO such split, `stack0` is written by the generic rules of the BOOT/BOTH buckets
  and is not β-coverable; the split that exists is W8-β′ (MachCSL-side) / W8 proper [rev 28]; **[R22.1] (4) the FEEDING path of each class (i)–(iii)** — `mmOk` is a PURE predicate on `σ` carried as `⌜mmOk
  σ⌝` in `memModelAt` (`Resources.lean:779-785, 951-956`) and re-established GENERICALLY by every memory rule, but (ii) "a
  protected access under a held lock" is NOT generically re-establishable (the store rule cannot know the byte is
  `proc[3].state` under `proc[3].lock`; only the `Xv6/` proof's `procHeld` points-to does), so the ledger is FED by the
  `Xv6/` proofs and the spike says WHERE: (f1) at every protected load/store rule application (an `Xv6/` SWEEP of the
  `swp_*` sites — XL, NOT "a rebuild"); (f2) at the lock layer only (`acquire`/`release` specs hand a holder token to the
  state interpretation, the protected cells' points-to wrapped so a store through them records the holder — M–L if
  `procHeld` and its siblings are the only doors); (f3) derived from `σ` alone — **[R23.1] ONLY for `PPerCpu` and the fixed per-hart stacks** ("no foreign
  writer" is a function of `HEnt.tid` over the byte's history given a STATIC ownership map — the (β) question); the spike
  COUNTS the 1,034 `PStack` sites by context (scheduler/boot stack vs `p->kstack`, via the pin table's pcs) and names the
  handoff's doors as the (f2) wrapper layers [R23.s4]: `procHeld` (abbrev `Xv6/SchedCtx.lean:1590` of `procHeldAt :663`),
  `stackOwn` (`MachCSL/KCtx.lean:256`), the `swtch` payload (`wp_swtch_body`, `Xv6/SpecSwtch.lean:35-58`) — each with a COUNT of the `Xv6/`
  sites or wrapper layers it touches (the W-RSV precedent [R12.1][R13.1]: "NAMES untouched" ≠ "FILES untouched"); **(5) the
  ROOT path**: (r1) into `mmOk`/`xv6TracePure` (`Xv6/SystemSlot.lean:135-136`: the root's statement TEXT unchanged, its
  MEANING strengthened — a ghost ledger needs an existential inside `mmOk` or a state-side mirror; then recorded in §A(6))
  or (r2) a SIBLING root on the W3 pattern (`xv6TextAdequacy_closed` + power/boot/system twins `MachCSL/PowerText.lean` 734,
  `Xv6/BootSharedText.lean` 250, `Xv6/SystemBootEraText.lean` 196, `Xv6/SystemAdequacyText.lean` 580,
  `Xv6/LinkTextAdequacy.lean` 35 ≈ 1.8k lines, plus `roots.txt`/`baseline.json`/`tcb/expected.json` entries — W3's cost
  again).  Export from the SC tree, per reachable
  MachCSL state (the `mmOk` idiom) on `MState`'s author log + per-byte histories (`MachCSL/Lang.lean:147-153`), in
  the vocabulary `protReg`/`badSeg` consume: (i) bytes a hart OWNS — no foreign writer SINCE THE LAST OWNERSHIP HANDOFF [R23.1] (covers `PStack`/`PPerCpu`,
  the 58 `own = true` witnesses; `gen_weak_pins.py --check` as the audit; W11's kill of a cross-hart edge INTO a process-stack
  read goes through the `p->lock` handoff — if that shape forces (f1), [OWN.36] re-opens by the existing rule [R23.1]); (ii) a protected access under a held lock
  (`wprotAt`/`wlpAt`/`wlpAlt`, `Weak/WeakGhost.lean:1040,543,699`; `lockWordByte`, `KillArms.lean:340`); (iii) no
  hart's floor reaches a FOREIGN owned-unpublished message (`wmAk = .WCplain`, `WeakRobustMain.lean:390-395`; `¬
  wpublished :399-400`; `Weak/WeakViolation.lean:9-15`) — HART authors only, DMA exempt, mirroring `violationHart`
  (`WeakRobust.lean:100-107`) — **[rev 28] stated as (iii+) `chainOkAt` (every observed foreign hart entry is SYNC-CHAINED to
  the observer), with LOCK-LAYER bytes EXEMPT: at `holding+0x12` a non-holder DOES read a foreign unpublished plain store
  (W8-design §0 item 7), so (iii) as written is FALSE there; those bytes are covered by `lockWordDiscAt` instead**; (iv) ALL 182 `PCall`/`PResidue` sites and the 58 sp-frame witnesses classified into
  (i)–(iii) (W9b; D28 RULED (a) [OWN.7]); (v) user-text page ownership for W5d-G's G7.  A ledger threaded through the
  MachCSL memory rules (`Wp`, `WpAtomic`, `WpDma*`, beside `mmOk`) — mechanical but wide, one ≈ 0.73M-line `Xv6`-cone
  rebuild **ONLY under W8-design (4) = (f2)/(f3) [R22.1]; (f1) is the XL outcome (an `Xv6/` sweep) that RE-OPENS the lane
  decision ([OWN.36] was ruled on the one-rebuild cost)**, the `--weak` lane in acceptance (§B(12)); ownership residue ~5 idioms (`swtch` reloads, trapframe loads off `a0`,
  user-table walks, boot-published globals).  Exports hold on FORWARDING graphs.  **Design gate — G2-Q only [W2s]
  [R10.1][R10.2] — RESOLVED by G2-Q (a′) [OWN.20][OWN.23]** [R4.s5][R6.4a]: (★) is NOT a W8 export under any option
  (discharged by `candScaT`, §B(10)); under the RULED (a′) W8 owes (i)–(v) only.  Recorded: under (b) W8 would have
  gained **(vi) the MIXED-SIZE census** (po-ordered OVERLAPPING loads of DIFFERENT footprints on a concurrently
  written byte; expected vacuous, **unverified**) feeding W11 (iv) through `R`'s log identification — MOOT.  Deps: W2 CLOSE
  ✓ (`rmem ∧ viewRel` and `pfStepTso` landed [R21.s4]); W8-β′: none (launch now); W8 (f2-ctx): W8-β′ + R-ctx [OWN.37].  [W13c, CORRECTED rev 28] W8 covers `lk->cpu`
  by **`lockWordDiscAt`** (W8-β′), NOT by (ii)'s `wprotAt`: the `holding+0x12` read (`0x80000c04`, `PResidue`,
  `KernelPins.lean:255`) is a NON-holder's racy read of the holder's unpublished `sd` — (K)'s `ioSegPinned` precondition (ii)
  is restated on `lockWordDiscAt` (§C W13 R5; §D Q-HOLDING).
  **W8-design RESULTS (DONE; `notes/W8-design.md` §0–§8) and the [OWN.37] structure [rev 28].**
  *(1) The export — D24 FIXED.*  A PURE per-state predicate on `MState`, the `mmOk` idiom, NO ghost ledger (so (r1)'s
  "existential inside `mmOk`" problem never arises): ownership is σ-DERIVED — (f3′) the dynamic owner `kOwnerAt σ j t` = the
  hart whose `cpus[h].proc` word (`aCpuProc`, `KCtx.lean:526`) equals `&proc[j]` as of `t` (at most one, by `cpuProcDiscAt`:
  `c->proc := &proc[j]` is written AFTER `acquire(&p->lock)`, `:= 0` BEFORE `release`, `Xv6/SpecScheduler.lean:11,13`); the
  lock holder `lkHolderAt σ b t` = the alternation fold `lkStep` over the lock word's byte history (byte values suffice — TsoMem
  records no exclusive bit; mirrors `altStep`, `WeakGhost.lean:570`); the static carves `stack0_h`/`cpus[h]`
  (`Xv6/BootCarveHart.lean:81,84`); `bootEnd σ` = the timestamp of hart 0's release store to `started` (`0x8000a400`).  Lean
  skeleton (`Xv6/AccessDiscipline.lean`, names grep-checked free; W8-design §1 is the binding text):
  ```
  inductive Cust | hart (h : CPU) | proc (j : Nat) | prot (b : PAddr) | lockw (b : PAddr) | pte | ro | free   -- [R25.1 (a)] `pte`: the kernel
      -- table's pages, reachable from the root `MachCSL.KernelSyms.kernel_pagetable` (`Xv6/BootCarveProc.lean:348`, the `kptOn t M` tree);
      -- [OWN.39][rev 31] USER-table pages (`pptPost`'s, reachable from `proc[j].pagetable` as of `t`) are `.pte` TOO — NOT `.proc j`:
      -- their A/D write-backs are by the RUNNING hart (`WpPtWalkOwn.lean:501-515`, a dirty key at the running context) and the TSO
      -- proof carries them over `p->lock`, but the priv spec's A/D scheme lets an A-bit update be SPECULATIVE (ordered by nothing), so
      -- the chain reading is UNFAITHFUL; RULED (a): the `pte-key` arm (R-ctx Q-R2).  The open design point is CLOSED.
      -- [R26.s3] `.pte` custody is MachCSL-anchorable: the root is an era ghost (`kptRootName`, `Resources.lean:135,438`) and a
      -- constant (`bcp_kpt_val`, `BootCarveProc.lean:348`), so "a page of `kptOn t M`'s tree reachable from the word at `0x8000a408`
      -- as of `t`" needs no `Xv6/` custody — what (f2-ctx)'s MachCSL-generic load rule must use to express the exemption
  def custAt [KernelGeom] (σ : MState) (a : PAddr) (t : Nat) : Cust          -- kstack pages off KSTACK(j) leaves, trapframe/user pages off proc j
  def syncPath (σ : MState) (A : CPU) (t : Nat) (B : CPU) (τ : Nat) : Prop   -- hops (b_k, r_k, a_k): a zero write to lock word b_k by the
      -- releaser at r_k, the fold installing the next hart at the acquire write a_k; t < r_0, releaser 0 = A, releaser k+1 =
      -- acquirer k, last acquirer = B, last a_k < τ; OR the boot hop (A = 0, t ≤ bootEnd σ, B's acquire load of `started` saw it)
  /-- (iii+): hart j's FOREIGN-source coh stamp at a (TsoMem.lean:354-356; reset at own stores :361-363) names a sync-chained
      entry; DMA authors exempt (e.tid < NCPU, as violationHart); LOCK-LAYER bytes exempt (lockWordDiscAt covers them);
      PTE bytes of BOTH tables exempt [R25.1 (a)][OWN.39] (pteDiscAt covers them: the hardware A/D write-back is a foreign hart's
      EXCLUSIVE store that every other hart's walk plain-reads and coh-stamps with NO chain — WpPtWalk.lean:455-470,
      Lang.lean:373-375,400; for a USER table the write-back by the previous hart (WpPtWalkOwn.lean:501-515) may be a speculative
      A-bit update the priv spec orders by nothing, so no chain is claimed there either).  [OWN.38] "syncPath" here is the
      per-author chain: the load rule establishes it from the PER-AUTHOR vector `chain ξ` of the consuming key, not from a scalar bound. -/
  def chainOkAt [KernelGeom] (σ : MState) : Prop :=
    ∀ (j : CPU) (a : PAddr) (H : Hist) (e : HEnt), σ.mem[a]? = some H → e ∈ H → e.t ≠ 0 →
      e.t = (σ.hr j).coh a → (hA : e.tid < NCPU) → e.tid ≠ hartAgent j →
      (∀ b, custAt σ a e.t ≠ .lockw b) → custAt σ a e.t ≠ .pte → syncPath σ ⟨e.tid, hA⟩ e.t j (σ.top + 1)
  def lockWordDiscAt [KernelGeom] (σ : MState) : Prop     -- lockWordAt/lkCpuAt per registered lock (Lock.lean:53-56,18-22)
  /-- [R25.1 (a)] every post-boot entry on a kernel-table PTE byte is an A/D VARIANT (KptInv.pteVariant :38-41, the σ-form of
      kptBody :85's pin) of the entry's canonical value, authored by a hart (e.tid < NCPU) — the walk's write-back, never a
      remap; never a badSeg source (the write-back is .WCexcl).  [OWN.39][rev 31] the SAME clause for every USER-table PTE byte
      (custAt = .pte via proc[j].pagetable as of t): every post-publication entry (after the owner's satp + sfence.vma) is an A/D
      variant of the value the owner installed (pptPost's mapping), authored by a hart; the owner's own remaps (uvmunmap/uvmfree,
      under its own ownership) are entries BEFORE the next publication, so "variant of the canonical value" is read per
      publication epoch — the (f2-ctx) worker pins the epoch index (S).  [R26.s2] A DOCUMENTATION clause: the honest naming of the A/D
      write-back assumption, with NO Stage-2 consumer named — the walker's racy absorption `wtlbResPtTranslateAddrStaleAt`
      (Weak/WeakKptStale.lean:488-502) is a theorem over the pf model's `Wmstate` under `wkptN`, taking no premise about `MState`
      histories; if a consumer appears, its bridge from `pteDiscAt σ` is named then (by whom, where), not asked of (f2-ctx). -/
  def pteDiscAt [KernelGeom] (σ : MState) : Prop
  def cpuStaticAt [KernelGeom] (σ : MState) : Prop :=      -- PPerCpu (β′): cpus[h]'s bytes written only by h after power-on
    ∀ (h : CPU) (a : PAddr) (H : Hist) (e : HEnt), custAt σ a e.t = .hart h → σ.mem[a]? = some H → e ∈ H → e.t ≠ 0 → e.tid = hartAgent h
  def cpuProcDiscAt [KernelGeom] (σ : MState) : Prop      -- c->proc moves only under the target proc's lock
  def utextDiscAt [KernelGeom] (σ : MState) : Prop        -- (v): entries on proc j's executable user pages precede its owner's last fence.i
      -- [R25.s4] credible because the VERIFIED BRANCH's `userret` executes `fence.i` after the `satp` switch (`Xv6/KernelImage.lean:17614`,
      -- `0x8000609c`; `SpecUserret.lean:6` "the icache sees the process image") — the image's ONLY `fence.i`, so the clause holds on every
      -- return to user mode after a migration; upstream xv6 has NO such fence — an IMAGE FACT of this branch, to be named in W8's header
  def xv6AccessDisc [KernelGeom] (σ : MState) : Prop :=   -- [R25.1 (a)] pteDiscAt added; W8-β′ exports the provisional
    chainOkAt σ ∧ lockWordDiscAt σ ∧ pteDiscAt σ ∧ cpuStaticAt σ ∧ cpuProcDiscAt σ ∧ utextDiscAt σ   -- `lockWordDiscAt ∧ cpuStaticAt` [R25.2]
      -- [R34.1] (f2-ctx) exports the FIRST FOUR ("four of six"); `cpuProcDiscAt ∧ utextDiscAt` are W8 (f3-rest)'s (§C top)
  theorem xv6DiscAdequacy_closed {hlc : HasLC} (g : GState) (Hgen0 : g.gen = 0) (Hpow : g.pow = false)
      (Hdisk : diskOf g.m.devs = fsImgDisk) (n : Nat) (κs : List Obs) (t2 : List Expr) (g2 : GState)
      (hsteps : ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2)) :
      (∀ e2, e2 ∈ t2 → Reducible (e2, g2)) ∧ (g2.pow = true → AccessDiscipline.xv6AccessDisc g2.m)   -- the W3 pattern, LinkTextAdequacy.lean:26-31
  ```
  **[R25.1] W8-design §1's `chainOkAt`/`Cust`/`xv6AccessDisc` text is SUPERSEDED by the skeleton above at the three `pte` points**
  (the note is not re-edited; this block is binding).  *Spec, for the record (NOT an owner question — every form of the PTE
  clause is FAITHFUL: an INTERNAL predicate's shape, the published quantifier and conclusions unchanged).*  RVWMO orders
  implicit page-table accesses by `SFENCE.VMA`, not by `FENCE`; the privileged spec makes the A/D update atomic w.r.t. other
  accesses to the PTE; the Sail model in this tree performs it as `read_pte_exclusive`/`write_pte_conditional`
  (`WpPtWalk.lean:3-7,156-165`, `exclWriteAU`) and the walk's read as a plain `PageTableEntry` load (`:48-57`, `coh`-stamping
  `Lang.lean:400`, `TsoMem.lean:354-356`); Zifencei/PMAs silent.  *Reachable counterexample to the rev-28 text.*  Kernel text
  pages first executed AFTER boot (`sysfile.c`, `exec.c`, `pipe.c`; `A` is per 4 KiB page): hart `k` first-executes the
  `sys_open` page at `t₁ > bootEnd σ` — its fetch walk writes `A` back (`.WCexcl`, author `k`); hart `m`, in user mode since
  before `t₁`, traps and its fetch walk of the same page plain-reads `k`'s variant with NO intervening acquire by `m` (the
  `syscall` → `sys_open` fetches precede `m`'s first `acquire`), so `(σ.hr m).coh a = t₁`, `e.tid = k ≠ m`, no `syncPath` —
  rev 28's `chainOkAt` false on a run the SC tree certifies (`KptInv` admits exactly this interleaving; same for `D` on
  kernel-data pages first written post-boot).  Nothing downstream needs the chain: the write-back is `.WCexcl`
  (`WeakKptStale.lean:26`), so W11's `badSeg` (a `.WCplain` source) is vacuous there, and the walker's value-insensitivity
  is `WeakKptStale`'s racy-absorption theorem (landed).
  (iii+) covers (i) static and dynamic, (ii) and (iii) for every cross-hart rf edge into a read off the lock layer and the
  kernel table; the plan's (iii) is its corollary off those; the [R23.1] "third shape" is its single-lock instance ([R24.s4] example: A's `sched` prologue
  pushes on `p->kstack`, A's scheduler `c->proc = 0; release`, B `acquire; c->proc = p; swtch`, `sched+0x7e..+0x86`
  (`KernelPins.lean:549-553`) loads A's words — ONE hop; same shape at `kernelvec+0x28..`, `:1671-1673`).  [R24.s6] initial
  owners: `stack0_h`/`cpus[h]` by `h` from power-on; `kstack_j` `none` until the first `c->proc := &proc[j]`, its boot-era writes
  (hart 0's `proc_mapstacks` junk fills) reached by other harts only through the `started` hop.  (iv) is a STATIC table (W9b):
  the 182 `PCall`/`PResidue` sites and 58 `own` witnesses classed chained / lock-layer / ro / audited-racy, `KernelPins.lean`'s
  `--check` the audit; (v) = `utextDiscAt`.
  *(2) Ledger file/lane.*  No ledger in the EXPORT; the FEED's ghost state lives in `memModelAt` (`Resources.lean:951-956`) and
  the context layer; `MState`/`Lang.lean` unchanged, so W4's `SimRel` and W2a's `rmem` are untouched; serial MachCSL before
  W-RSV (overlap `Resources.lean`, the load rules, `WpLock.lean`).
  *(3) (β) covers almost nothing* — a ledger-free, feed-free export says only what `mmOk` says; **W8-β′** (the reserved-region
  change, no ledger) covers `cpus[h]` (`cpuCells`, `KCtx.lean:556-560`; the 3 `PPerCpu` sites `myproc+0x1e`, `sched+0x2a`,
  `sched+0x54`; stores through `wp_s_sd_proc` 3, `wp_s_sw_noff_lend` 2, `wp_s_sw_intena` 2, `wp_s_lw_noff` 4 — ≈ 11 uses,
  **unverified**: a proof storing `c->proc`/`noff`/`intena` through plain `wp_s_sd`/`wp_s_sw` would also need an edit) and the
  lock layer's own words (the STATIC spinlocks' two words, `lockWordAt`/`lkCpuAt` already proved per lock, `:590-597`; the cells
  `lkFresh :727` hands to `newlock_written :682-687` [R26.s6]) → `cpuStaticAt` + `lockWordDiscAt`, what W13 (K) needs — **delivered
  as the three Lean statements of §C top [R25.2]: (i) `⌜staticIn reg ∧ reservedOk σ reg⌝` (MachCSL, beside `⌜mmOk σ⌝` in
  `memModelAt`; `Xv6/` cannot be imported by MachCSL, so the invariant MUST be MachCSL-side; `reg` lives in the NEW era ghost
  `rsvName` and the reserving step is the `PowerOn` mint over the client's `KernelRsv.static` list [R26.2][R26.2-alt] — §C top has
  the mechanism, the file list and why not "at `initlock`'s stores / the boot carve"), (ii) `powerInterp_accessDiscβ` (`Xv6/`, the
  registration-lemma extraction `xv6LockWord σ b t → b ∈ reg` [R26.1], `powerInterp_mmOk`'s pattern [R26.s1]), (iii) the (r2)
  twin at the provisional conjunction** — without (iii) β′'s facts reach NO root and W13 (K)'s realizing-run fact would arrive
  only with W8 (f2-ctx) (L–XL, gated).  RECOMMENDED and APPLIED: the twin at β′ — paid once, settles W8-design §8's "no PowerOn
  hook" point early (β′'s facts are PURE conjuncts of the state interpretation, so the twin needs only the extraction, the cheap
  case — no TRACE hook; the registry gname and the static halves ARE minted at PowerOn [R26.2 (e)]), and makes "unblocks W13 (K)"
  true.  **Scope note [R26.2-alt]**: β′'s `lockWordDiscAt` is the STATIC lock words; the pipe lock (born at `pipealloc`, destroyed
  at `wp_s_sw_zero_release_cancel`) joins at W8 (f2-ctx), because a mid-run ghost registration is invisible to the twin's final
  hook `◇ ⌜phi g' h⌝` (`Adequacy.lean:359-366`) unless `memModelAt` carries a PURE σ↔`reg` tie — which MachCSL cannot state for
  "reachable from the open-file table" (an `Xv6/` fact): how (f2-ctx) exports the pipe part is an open design point (below).  Recorded alternative (not taken): twin in W8 (f2-ctx), in which case β′ unblocks only the
  STATEMENT of (K)'s precondition and the ≤ 1.8k twin moves to the lane's risk line.  NOT `stack0`: written by the generic rules in the BOOT
  bucket's 26 functions and the 41 BOTH-bucket functions whose proofs are shared with `p->kstack` — so [R24.s1]'s "static part
  splits off" does NOT hold and W8 does NOT split into an `Xv6/`-only item.  **The 1,034 `PStack` sites [R24.s2]**: BOOT
  (`stack0` only, static) 26 fns / **82** sites (`proc_mapstacks` 10, `procinit` 8, `freerange`/`binit` 6, …); PROC
  (`p->kstack`, dynamic) 115 / **747** (`kexec` 31, `pipewrite` 27, `sys_exec`/`readi` 23, …); BOTH 41 / **192** (`printk` 22,
  `kernelvec` 17, `mappages`/`consoleintr` 9, …, `allocproc` 4 — called by `userinit` on `stack0` AND by `kfork` on
  `p->kstack`, confirming "the target runs on both"); DEAD 3 / 13 (`procdump` 9, `memcpy`/`memcmp` 2 — no `jal`/`j` target);
  total 1,034 = `KernelPins.lean:23`; refinement: `yield`/`sched` from `kerneltrap` only when `myproc() != 0` → PROC 755, BOTH
  184; the 58 `own = true` witnesses: PROC 46, BOTH 11, DEAD 1.
  *(4) FEEDING — the deciding finding.*  **No (f2) and no (f3) feed exists** for any class except the lock-layer words and
  `cpus[h]`: custody is INVISIBLE to the memory rules — `wp_s_sd` takes a bare `wordPointsTo … (own 1)` + `kctxL`
  (`WpSmodeRules.lean:369-378`), the points-to is a context-free history points-to + a key (`Ctx.lean:430-432`), `stackOwn` is
  address-only cells (`KCtx.lean:256-257`), `KCtx` has no stack↔proc link (`:620-642`), lock payloads are opaque `R : CtxId →
  IProp` (`Lock.lean:357`) moved to the holder's own context at acquire (`:369-384`), and the context layer's clean keys are
  TSO-sound only (`ctx_absorb`, `CtxLaws.lean:479-480`; `ctxStamped_raise :577`: a clean key records "some acquire happened
  since", not "synchronised with the writer" — `SpecAcquire.lean:96-103` says so).  (f3′) is a valid EXPORT vocabulary, not a
  feed (a store into `kstack_j` cannot show `kOwnerAt σ j = h` — `cpuCells` ties `c->proc` to `k.proc`, nothing ties `k.proc`
  to the cell's address; lent cells reach functions whose specs know nothing about stacks).  The (f2) doors — `procHeld`
  (`SchedCtx.lean:1590`; 50 uses/13 files), `stackOwn` (273/93 `Xv6/` + 58/16 MachCSL), the `swtch` payload (3 sites), the lock
  layer (`wp_acquire` 39/36, `wp_release` 35/33, `locked` 422/129) — do not feed (i)/(ii): once a cell leaves its wrapper it is
  used through 634 `wp_s_sd`/839 `wp_s_ld` applications, and a wrapper surviving to the rule IS (f1).  **(f2-ctx) — chain-
  carrying contexts, the only generic candidate (RULED (a) [OWN.37])**: refine the CLEAN key to carry a sync chain — **[rev 31]
  [OWN.38] (F0, R-ctx §1) the chain is PER AUTHOR: a vector `chain ξ : CPU → Nat` kept BESIDE the unchanged scalar TSO floor
  (`ctxFloor`, `Ctx.lean:179-180`, still the visibility bound), consulted only by clean keys (`keyAt :187-188`) and by the load rule
  that establishes `chainOkAt`, JOINED at each hop, with two invariants: "every h-entry `t ≤ chain ξ h`, h ≠ hart(ξ), has a
  `syncPath` to hart(ξ)" and causal closure "`chain ξ h ≥ t` ⇒ `chain ξ ≥` the vector h released after t"** (the rev-28 scalar form
  "every foreign-HART entry `t ≤ bound ξ` has a `syncPath`" is FALSE at one ordinary hand-off: hart C stores `y` at log 5 and never
  releases; hart A, bound 0, stores `x` at 10 and releases L — `lock_pay_intro_hook`'s `ctx_stamp` stamps ξL at `max B W ≥ 10`; hart
  B acquires L, absorbs at the release stamp and `ctx_unstamp`s — B's bound ≥ 10 and C's entry at 5 is a foreign entry ≤ bound with
  no `syncPath`; a path from (h, t) is a path from every h-authored t′ < t, so each author's chained entries form a PREFIX — hence
  the vector; per-key certificate sets are the equivalent heavier form, recorded), maintained at `ctx_unstamp` (join the
  releaser's vector into the acquirer's at the release → acquire hop), `ctx_move` (inherited), `ctx_park`/`ctx_resume` (same-hart
  transports — **the cross-hart hop of the `swtch` handoff is NOT at `wp_swtch`: all 8 transports in `Xv6/ProofSwtch.lean` are
  same-hart moves; the hop is the `p->lock` PAYLOAD's `lock_pay_intro → lock_pay_take` (`Lock.lean:386-398,369-384`): A's scheduler
  releases `p->lock` with the migratable proc record (`procCtxAt`/`ctxParked ξp ξl`, `SchedCtx.lean:1199-1200`, riding
  `procSlotsAt :1321-1323`/`procLockResAt :1527-1533`) stamped into ξL, B's scheduler acquires and `lock_pay_take` moves it into B's
  context, `kctx_resume_tok` resumes ξp — ONE hop on `p->lock`, covering A's `sched` pushes ([R24.s4]) and A's dirty keys in ξp;
  `wpNext` migrations go through the same lock (`yield` → `sched`); `W8-design.md:350` corrected**); RESTRICTIONS: `ctx_stamp` stamps
  at `max bound dirty` (not the top receipt), `ctx_absorb` only at chained receipts (in `acquire` the release stamp `T`, not the
  AMO position `t` — `WpLock.lean:1141-1143` already derives `T ≤ t`; `WpLock.lean:1141,1345`, `Lock.lean:375,430`, `KCtxMove.lean:299`,
  `CtxBox.lean:104,162,1329,1742,1938` are the MachCSL-internal leaky sites), `ctxStamped_raise`/`lockHook_llb` only at chained
  receipts, DMA-authored keys get a "device key" arm exempt from chains, **PTE bytes (kernel AND user tables [OWN.39]) the `pte-key`
  arm**.  A load rule then establishes `chainOkAt` at its post-state GENERICALLY from the key it already consumes — no custody,
  no `Xv6/` site feed; migration and lock transfer are both hops.  **The five ADDITIONS the TSO proof never tracked (R-ctx §0 item 2;
  binding for the (f2-ctx) brief): (X1)** every `topLb` re-floor at a hook (`lockHook_llb`, `ctxStamped_raise`) becomes a floor the
  RELEASER's OWN vector already covers — each such stamp is the releaser's own store or deposit (its own component is free) or was
  chained to it through the same lock; `ctxDeposit` must stamp at bound ⊔ dirty, not the view K (rows 13–18, 24–25 of the table:
  `ProofBrelse.lean:97`, `BcacheLock.lean:132`, `IputLockedB.lean:109`, `ProofIunlock.lean:253`, `IcacheTable.lean:682,694`,
  `SpecRelease.lean:170-181`, `SpecReleasesleep.lean:84-107`/`SleepLockDefs.lean:239-250`); **(X2)** a new box row in
  `MachCSL/CtxBox.lean:1117-1121` — "every live key's stamp ≤ `max tp td`" — for a reference minted at a stamp its holder is not yet
  chained to (`bget`'s race with a parker, row 22: `SpecAcquire.lean:108-120`'s `wp_acquire_llb_body`, `bufEscrow_take`'s `hKt`,
  `BufEscrow.lean:376-380`); **(X3)** a BIRTH key for the payload stamp of a lock born after boot in `lkFresh`/`isLock`
  (`Lock.lean:727-729`; `lock_pay_take` uses it at the first acquire) — `PipeBirth.lean:303`'s pipe lock AND the `"log"` lock
  (`ProofInitlog.lean:434` → `LockBornHook.lean:123,30`), the handle reaching other harts only by chained transports (`isLock`'s
  `lkFloor curCtx`, `Lock.lean:604-617`); **(X4)** a DEVICE-only absorb for the virtio watermark (`ProofVirtioDiskIntr.lean:334`'s
  `ctx_absorb` of the handler's post-fence view `F` into `diskWm γ n F`, `DiskInvDefs.lean:1328-1330,4797-4811`: raise the device
  component only — a scalar absorb at `F` would raise every hart's); **(X5)** the `ACQUIRE_LLB`/`ACQUIRESLEEP_*LLB` "cash any `topLb`
  held before the call" surface (`SpecAcquire.lean:96-103`, `acqPost` `WpLock.lean:76-79`) is WITHDRAWN — it RESISTS as a LAW — and
  its consumers (the 31 files of R-ctx §5) re-route through (X1)/(X2).  [R26.s4] Precisely: `chainOkAt` is an `Xv6/` predicate (`custAt`,
  `xv6LockWord`) and MachCSL cannot import `Xv6/`, so the load rule establishes a MachCSL-generic chain invariant PARAMETRISED BY
  THE REGISTRY (the `.lockw` exemption via `reg`, the `.pte` exemption via `kptRootName` [R26.s3], DMA via `devBytes`), from which
  `Xv6/` derives `chainOkAt` — the same shape as β′'s registration lemma [R26.1]; an (f2-ctx) design point R-ctx cannot settle.  **R-ctx (the gate, S, read-only)**: the ≈ 35 TSO-leaky uses are
  DESIGNED to mint floors above the releaser's own view (`SpecRelease.lean:164-169`, `BcacheLock.lean:132`,
  `SpecAcquire.lean:96-103`); each must be re-justified by a chain, the device-key arm, or the **`pte-key` arm [R25.1 (c)]**
  (the A/D write-back `WpPtWalk.lean:455-470`/`Xv6/TransPt.lean` and the walk's plain PTE read: exempt from the chain invariant,
  covered by `pteDiscAt`; the walker's own rules CANNOT re-establish a chain — the write-back needs no key and the read raises
  `coh` outside any chain — so without this named arm R-ctx would miss the walker or table it as RESISTS for the wrong reason)
  (bcache/icache/sleeplock floors; the virtio completion floors in `DiskInvDefs`/`ProofVirtioDiskIntr`) — whether every one can
  is **unverified**; a use needing a cross-lock fact the TSO proof never tracked sends THAT part to (f1).  **R-ctx RESULT (DONE
  2026-10-12, `notes/W8-Rctx.md`, read-only, nothing built) [rev 31]**: (0) **F0** — the invariant as pinned is FALSE at one hand-off
  (above); every verdict is relative to the per-author vector bound ([OWN.38]); under the scalar form EVERY cross-hart row RESISTS
  and (f1) is the whole of W8 (XL ≈ 10–15k, ≥ 320 files).  (1) **31 rows: 18 CHAINED** (rows 1–11 and 31 same-hart transports or
  births — `ProofScheduler.lean:998,1000`, `ProofForkretPark.lean:250,253`, `ProofSwtch.lean:248,251,253,268,270,274,276,293`,
  `ForkretRecord.lean:37`; 19–21, 23, 26 consumption or pure folds — `IgetScan.lean:326`, `ProofIdup.lean:318`,
  `IcacheInvRef.lean:232`, `SpecAcquire.lean:47-61`, `BcacheInv.lean:950,1207`; 27 the boot hop `IcacheBootTable.lean:677`),
  **3 DEVICE-KEY** (rows 28–30: `ProofVirtioDiskIntr.lean:334,299`, `DiskInvDefs.lean:4751,4812`; row 29 CHAINED at nr = 0 via the
  boot hop), **10 NEEDS-X** (rows 12–18, 22, 24–25 — carried once X1–X5 land; row 28 also needs X4), **RESISTS: NONE at the program
  level** (row 22 resists as a generic LAW and is withdrawn by X5) — **the (f1) fallback list is EMPTY**.  (2) The `swtch`-handoff
  row: CHAINED via the `p->lock` payload hop (above).  (3) The walker row: kernel table PTE-KEY (`swp_update_and_write_pte_kpt`,
  `WpPtWalk.lean:455-470`, takes no key, acts on `kptOn`; `read_pte :52-60` stamps the foreign `coh` outside any chain; covers
  `Xv6/TransPt.lean:10-13`'s kernel-side TLB hit); user table — R-ctx tabled it CHAINED as owned stores modulo Q-R2, **RULED (a)
  [OWN.39]: PTE-KEY too** (§B(2)).  (4) Counts: the 21 files hold 21 CODE uses of the named laws + 10 definitional surfaces (the
  plan/W8-design counts `ctx_absorb` 6, `lockHook_llb` 13, … include prose); **4 direct leaky sites OUTSIDE the 21**:
  `IputParts.lean:461` and `ProofAcquiresleep.lean:809` (via `kctx_floor_of_view`, `MachCSL/KCtxMove.lean:295-303` — absorb a `viewLb`
  into a floor; `IputParts`'s `tl` is `iput`'s own park, `ProofAcquiresleep`'s is row 22's cash), `StartedInv.lean:198` (`ctxDeposit`)
  and `:344` (`ctxAbsorbLb`) — the boot hop, CHAINED, in the restricted forms; **31 more `Xv6/` files consume the hook/llb surfaces**
  (IputLockedA, IputEntry, IputParts, LinkAcquire, IputLocked, LinkAcquiresleep, ProofAcquire, ProofAcquiresleep, ProofIput,
  BufEscrow, BreadScan, BreadDefs, IlockMain, ProofIlock, ProofBread, SpecAcquiresleep, IgetRecycle, IgetTail, IputLockedC, IgetHit,
  LinkIget, IputTail, LinkRelease, LinkReleasesleep, LinkIdup, ProofBunpin, ProofIget, ProofRelease, ProofReleasesleep, SpecBrelse,
  StartedInv — many `Link*` pass-through); ONE more post-boot lock birth, the `"log"` lock (`ProofInitlog.lean:434`).  (5) Open
  questions raised: Q-R1 (F0) → [OWN.38] (a); Q-R2 (user-table walker) → [OWN.39] (a); Q-R3 cosmetic → applied here (`:1278`'s
  "only" and `:2684`'s `wp_swtch` hop).  **[R25.3] The file list
  is 21, not 19**: W8-design §3.4's 19 + `Xv6/ProofSwtch.lean` (`kctx_move_in/out` ×5, `:251,253,268,270,274` — `ctxCells`,
  `stackOwn` and the context payload cross the hart boundary HERE; the (f2-ctx) `p_j->lock` hop "supplied at the 3 `wp_swtch`
  sites" is concatenated across exactly this transport, so a check that never opens the file cannot say whether the hop is
  expressible — [rev 31] R-ctx opened it: the transports are same-hart, the hop sits on the LOCK layer at `lock_pay_take`, (4) above)
  + `Xv6/PipeBirth.lean` (`lock_pay_born :303` — the only lock born after boot [rev 31: one of TWO, with the `"log"` lock
  `ProofInitlog.lean:434` → `LockBornHook.lean:123,30` — both take X3's birth key], hence β′'s only cancellable-lock/
  reclaim registry case, W8-design §4); transport counts corrected: `ctx_park` 3 (2 files) [R26.s5], `ctx_move` 1 (`ProofForkretPark.lean:250`), `kctx_move_in/out`
  6 (`ProofSwtch` 5 + `ProofScheduler.lean:1000`), `lock_pay_born` 1 (the other four `lock_pay_*` hits are prose); the output
  table gains a `swtch`-handoff row (CHAINED via the `p->lock` hop / RESISTS) and a walker row (PTE-KEY).  **(f1) — per-site custody (the fallback per part)**:
  every `Xv6/` store application justifies `custAt` = writer (`wp_s_sd` 634, `wp_s_sw` 118, `wp_s_sb` 42, `wp_s_sh` 34, ≈ 60
  specialised) and every load at the 1,219 unpinned sites (`wp_s_ld` 839, `wp_s_lw` 245, `wp_s_lbu` 50, `wp_s_lh` 40, `wp_s_lhu`
  21, `wp_s_lwu` 3) — ≈ 2,153 applications in 309 files + a `KCtx` stack-region link through `procinit`/`allocproc`/
  `scheduler`/`sched`/`swtch`/`forkret`/`kernelvec`/`uservec`, page custody at `kalloc`/`kfree`/`uvm*`/`pipe*`/`exec`, payload
  footprints for the 12 spinlock classes + sleeplocks, spec changes for every buffer-taking function; XL ≈ 10–15k, ≥ 320 files
  — the outcome that RE-OPENED [OWN.36] (now ruled by [OWN.37]).
  *(5) ROOT — (r2).*  (r1) is NOT available: `mmOk` is MachCSL-generic (`Resources.lean:779-785`) while `xv6AccessDisc` names
  the xv6 lock registry and the kstack/proc/cpus addresses; a generic `∃ reg, chainOk σ reg` inside `mmOk` is UNUSABLE (W11
  needs every registered word's zero writes WCrel at the release site — an existential `reg` admits non-lock 0/1 words whose
  zero writes are WCplain, and σ records neither class nor pc); adding a conjunct to `xv6TracePure` changes the root's TEXT
  against [OWN.9]'s precedent.  (r2) = the sibling root `Xv6.xv6DiscAdequacy_closed` on the W3 pattern (`PowerText.lean` 734,
  `BootSharedText` 250, `SystemBootEraText` 196, `SystemAdequacyText` 580, `LinkTextAdequacy` 35 = 1,795 lines the UPPER
  bound; likely lower — W8's facts sit in the state interpretation, so the twin needs only the final extraction on
  `powerInterp_mmOk`'s pattern (`Adequacy.lean:481`) [R26.s1], no PowerOn TRACE hook — the registry gname and the static halves are
  minted at PowerOn [R26.2 (e)], **unverified**) + `roots.txt`/`baseline.json`/`tools/tcb/expected.json` entries; **[R26.1] the
  registration lemma `xv6LockWord σ b t → b ∈ reg`** (every σ-visible lock word is registered; in β′ a list-membership fact on
  `KernelRsv.static`) is the twin's `Xv6/` side — W8-design §5's "MachCSL ghost registry ⊆ `xv6LockWord σ`" (`W8-design.md:452-453`)
  is the WRONG direction, FALSE between a pipe lock's birth and its publication (`SpecPipealloc.lean:10-12`) and between the
  unlink and the reclaim (`SpecFileclose.lean:10-12`), and is W11's zero-write-WCrel concern via `custAt .lockw` if at all —
  **the twin is BUILT BY W8-β′ [R25.2]** (W8-design §5's "inside the twin" placed it under W8 (f2-ctx); superseded here).
  *(6) Sizes.*  **W8-β′** M–L ≈ 1.3–2.3k [R26.2 (d)] (rev 29's 1.1–2k + the era ghost through `Power`/`PowerText`/the three
  `MachGS` literals + `KernelRsv` + fraction-parametric `wordCell` ≈ 0.2–0.3k), ≈ 11 MachCSL + ≤ 30 `Xv6/` + 1 `Weak/` + the twin
  files, 1 full cone (MachCSL 78k + `Xv6` ≈ 0.66M lines), serial MachCSL.  **W8 (f2-ctx)** ≈ 3–5k core + `AccessDiscipline.lean` ≈ 0.5–0.8k (now incl. `pteDiscAt` [R25.1]) + STRENGTHENING the
  β′ twin's conjunction ≤ 0.3k (was: root twin ≤ 1.8k) → ≈ 4–6.5k (rev 29) — **[rev 31][OWN.38] RE-SIZED after R-ctx (`W8-Rctx.md`
  §6): + F0's per-author chain vector + causal closure beside the scalar bound (`Ctx`, `CtxLaws`, `Lock`, `WpLock`, `KCtxMove`;
  +1–1.5k) + the `CtxBox` stamps/registers lifted to join-vectors with row X2 (`CtxBox.lean`, 2,131 lines; +0.5–1k) + X1/X3–X5 in
  `Xv6/` (+1–1.5k) → ≈ 6.5–9.5k** (+ 1–1.5k findings 2–3 [rev 38]; **+ ≈ 2–3.5k F-C — `CtxBox`'s vector rows (i) over 27 client files [rev 40]
  [R36.4] → ≈ 9–13.5k**); **12 MachCSL** (the 11 + `WpPtWalkOwn` [OWN.39]; `KCtxMove`'s `kctx_floor_of_view` already in
  the 11) + **≈ 52 `Xv6/`** (21 + the 31 hook/llb consumers; the "up to 43 more through `ctxFloor`" overlap these and change only
  if the scalar floor's meaning changed — it does not) + the twin files; **3–4 full-cone rebuilds**; serial MachCSL AFTER W-RSV
  [OWN.41][R28.5].
  **(f1)** ≈ 10–15k, ≥ 320 files, many rebuilds (per resisting part only) — **list EMPTY after R-ctx** (it would be EVERYTHING —
  rows 3, 12–18, 22, 24, 25, 27, 28 and the handoff — had the scalar form been kept).  **(T)** trusted premise: S, WEAKER — NOT taken.  Plus, in every case: W11 gains a
  **`chainHyps`** kill arm (`csChained` generalised over `syncPath`, M, **unverified**) and W9b's table classifies the 182 + 58
  sites.  *Consumers*: W11 (i) `badSeg` refuted at the realizing run from `chainOkAt` (+ the static release-site fact `fence
  rw,w; sw`, W9a, through `R`'s log identification), `lk->cpu` reads through `lockWordDiscAt`; W11 (ii) `wlpAt`/`wlpAlt` off
  `lockWordDiscAt` through `rhist`, `wprotAt` only for registered bytes, the stack kill via `chainHyps` (§C W11); W13 (K)'s
  `ioSegPinned` (ii) on `lockWordDiscAt`; W5d-G G7 on `utextDiscAt` (W8 (f3-rest) [R34.1]); the walker's racy absorption (`WeakKptStale`) on
  `pteDiscAt` [R25.1] — a documentation clause, no consumer named [R26.s2].  *Acceptance*: **W8-β′ [R25.2] — THREE named Lean
  statements**: (i) `⌜MachCSL.staticIn reg ∧ MachCSL.reservedOk σ reg⌝` a conjunct of `memModelAt` (`Resources.lean:951-956`, beside
  `⌜mmOk σ⌝`), `reg` the era ghost `rsvName`'s map and the static regions' halves `[∗map]`-held there from the `PowerOn` mint
  [R26.2][R26.2-alt]; re-established by the dedicated cpu-cell and lock rules only — the half-points-to mechanism of W8-design §4
  keeps the generic rules out), (ii) `Xv6.powerInterp_accessDiscβ : powerInterp g ⊢ ⌜g.pow = true → lockWordDiscAt g.m ∧
  cpuStaticAt g.m⌝` in `Xv6/AccessDiscipline.lean` (`lockWordDiscAt`/`cpuStaticAt` stated there; `lockWordDiscAt` over the STATIC
  lock words via the registration lemma `xv6LockWord σ b t → b ∈ reg` [R26.1], on `powerInterp_mmOk`'s pattern [R26.s1]), (iii) `Xv6.xv6DiscAdequacy_closed` with `xv6AccessDisc` provisionally `:= lockWordDiscAt ∧ cpuStaticAt` (the skeleton's
  conjunction is the (f2-ctx) target), registered in `roots.txt`/`baseline.json`/`tools/tcb/expected.json`, axiom set =
  `xv6FsAdequacy_closed`'s; `lake build Xv6 MachCSL Weak Vtest` ([R14.1]), `--weak` audit unchanged; R-ctx — a per-use table
  (CHAINED / DEVICE-KEY / PTE-KEY / RESISTS) over the 21 files in `notes/W8-Rctx.md`, with the `swtch`-handoff and walker rows
  [R25.1 (c)][R25.3], no Lean edit — **DELIVERED (rev 31)**; W8 (f2-ctx) — **FOUR of the six conjuncts of `xv6AccessDisc` [R34.1]**: `chainOkAt` (with the `.pte`
  exemption for BOTH tables [OWN.39]) ∧ `lockWordDiscAt` ∧ `pteDiscAt` ∧ `cpuStaticAt` — `cpuProcDiscAt` and `utextDiscAt` DEFERRED to the
  named follow-up **W8 (f3-rest)** (§C top), the file header and `roots.txt:20`'s comment saying "four of six" — exported by the SAME root
  `xv6DiscAdequacy_closed` (statement strengthened, registration unchanged), **the PER-AUTHOR chain vector `chain ξ : CPU → Nat` + causal closure NAMED beside the unchanged scalar
  floor [OWN.38], the five additions X1–X5 landed and named in the file headers (X5: the `ACQUIRE_LLB`/`ACQUIRESLEEP_*LLB` surface
  gone from `SpecAcquire`/`SpecAcquiresleep`), the four outside-the-21 sites and the `"log"` lock's birth key covered, the (f1) list
  recorded as EMPTY (any part that turns out to RESIST during the proof is reported, not silently custodied)**, `WpPtWalkOwn`'s
  user-table write-back under the `pte` arm, `lake build Xv6 MachCSL Weak Vtest` ([R14.1]), axiom set = `xv6FsAdequacy_closed`'s.
  *Unverified points* (W8-design §8): (f2-ctx) soundness — the `Xv6/` fallout is now CHECKED (R-ctx, rev 31), what stays
  unverified is the per-author vector's maintenance proofs (`ctx_unstamp`'s join, X1's "the releaser's own vector covers the hook
  stamp", X2's box row being invariant under parks/deposits/mints, `CtxBox`'s registers as join-vectors) and the 3–4-rebuild
  estimate; the `chainHyps` arm; **[R26.2 (e)] no
  PowerOn TRACE hook (W3's `HtextRec`) in the (r2) twin — the registry gname IS allocated with the era's other ghosts at PowerOn and
  the static halves split off in `powerBootRes`; the extraction is `powerInterp_mmOk`'s pattern (`Adequacy.lean:481`), not
  `powerInterp_textPristine`'s (`eraRegistered` + the persisted window, `TextPristine.lean:120-123`)**; `custAt`'s σ-derivability for
  pipe locks and user pages; `xv6LockWord` enumerating every spinlock (β′: `KernelRsv.static` enumerating every IMAGE spinlock incl.
  the sleeplocks' inner locks — the ≈ 14 `initlock` callers' addresses); the ≈ 11 cpu-cell rule uses; **[R26.2-alt] the PIPE part of
  `lockWordDiscAt` at (f2-ctx)**: dynamic registration at `wp_s_sw_mint`/`wp_s_sd_mint`, de-registration at
  `wp_s_sw_zero_release_cancel` and a `tReg ≤ t < tEnd` index are executable STEPS, but the twin's hook `◇ ⌜phi g' h⌝` cannot see
  the ghost registration of a lock born mid-run, and "reachable from the open-file table" is not MachCSL-expressible — (f2-ctx) must
  either find a PURE σ↔`reg` tie `memModelAt` can carry or export the pipe part another way (an open design point, not a gate; W13 (K)
  needs only live STATIC locks); **[R26.s4] (f2-ctx)'s load rule establishes a MachCSL-generic, registry-parametrised chain
  invariant, `chainOkAt` derived `Xv6/`-side** (R-ctx cannot settle this).  **Deps [R28.5] — ALL MET at rev 37**: W8-β′ — DONE and MERGED 2026-10-12 (`../weak-orch/parked/PROGRESS-W8beta.md`: increments 1–4;
  `KernelRsv.static` = all 157 image spinlocks (both ports' `uarts[i].lock`, `cons`, `pr`, `kmem`, `pid_lock`, `wait_lock`, the 64 `proc[i].lock`,
  `tickslock`, `bcache.lock`, the 30 buffers' and 50 inodes' sleeplock inner locks, `itable.lock`, `log.lock`, `ftable.lock`, `disk.vdisk_lock`)
  + NCPU cpu regions, address-sorted, `decide +kernel`; pipe locks stay dynamic; `Xv6/AccessDiscipline.lean` 197 (`Cust :53`, `custAt :89`,
  `xv6LockWord :98`, `lockWordDiscAt :104`, `cpuStaticAt :109`, `xv6AccessDisc :115`, `xv6LockWord_registered :153`, `powerInterp_accessDiscβ :186`
  taking `MachFixedGS.rsvStatic = KernelRsv.static` — deviation 3), `SystemAdequacyDisc.lean:35`, `LinkDiscAdequacy.lean:26` root REGISTERED
  (`roots.txt:20`, `baseline.json:67`, `tcb/expected.json:2323`; axioms = `xv6FsAdequacy_closed`'s, 0 `sorryAx`); deviations: `reservedOk`/
  `staticIn` take the list explicitly, `lockRegionOk`'s owner pointer is a kind parameter (`RsvKind.lock cpusBase`), `custAt`/`xv6LockWord`
  ignore `σ`/`t` in β′ ((f2-ctx) makes them σ-readable), **four existing roots' `tcb/expected.json` module sets GROW** (`riscvPowerAdequacy` +
  `Reserved`/`RsvMint`/`WordHistDefs`; `xv6PowerAdequacy` + `Reserved`/`WordHistDefs`/`Geom`/`KernelRsv`; `xv6FsAdequacy_xv6GF`, `userProof` +
  `Reserved`/`WordHistDefs` — the reserved conjunct lives in `memModelAt` and `MachFixedGS` carries `rsvStatic`; no module leaves,
  axioms/opaques unchanged)); R-ctx — DONE; **W-RSV — DONE and MERGED** (§C top rev-37 paragraph); **W8 (f2-ctx) — LAUNCHABLE NOW**,
  rebasing on W-RSV's `resvFragAny` thread (`ctxTokAt :299`/`ctxTok :320`, `ctxTok_cases :406-407`) and on β′'s `Resources.lean`/`Lock.lean`/
  `WpLock.lean` — the LAUNCH PARAGRAPH (deps, deliverables, files, rebase surface against the tip, acceptance, size) is at §C top [rev 37].
  **[R28.s8]** the (f2-ctx) brief's first line tells the worker that `notes/W8-design.md` §4/§5/§8 state the SUPERSEDED scalar
  design (rev 30/31: per-author vector bound [OWN.38], X1–X5, `WpPtWalkOwn` [OWN.39]) — this plan's §C W8 (4)/(6) governs;
  **[R28.s6]** R-ctx's note was briefed as `notes/R-ctx.md` and written as `notes/W8-Rctx.md` (its header `:5-6`) — the plan's name.
- **W9a `Weak/WeakRvwmoPinBridge3.lean`** (L = M–L + M [R6.1]) [R4.1] — **[rev 44] LAUNCHABLE (third batch, §C top): W12 `segPinC` ✓, (F-dep) (2)/(3)'s pin-bridge re-proof ✓**.  R-3: a `pstepEv` run's items are grouped per
  instruction as the checker's pc walk assumes (`reaches`/`psites`, `PinBridge2.lean`; §8 has both halves on one
  computed stretch) → `pinSegPin'` applies at every certifying site of the REAL run, targeting `segPinC`
  (`pinStepOfSegPinArm`; PDep entries across an rfi via `segPinCForward`); with W8 (W9b) → `l2ClaimAtC`'s `segPinC ∨
  csHyps` arms for xv6.  No generator work (§B(9)).  **[rev 46] increment 1 MERGED (276 l.; §C top Rev 46 RESULTS); R-3 is FALSE of Sail as
  stated → Q-W9A, provisional (A): R-3 becomes the NAMED premise `runAligned` (per-instruction grouping at the announced word, no trap in the stretch, `ret`
  targets); increment 2 (RUNNING, w5) closes the taken-branch case (any-path `reaches` + soundness of the checker's all-paths search, S–M); before publication the
  premise is discharged by (B) (per-clause dataflow walker + trap crossing + W8 stack ownership, XL, spike first) or stays a named scope restriction.**
- **W10** (M–L, **unverified**; L if it absorbs W12b): `wsegSupply`/`walkPolicy` for xv6 graphs on the W12b floor kit — [rev 44] D35-fix ✓ (the `CatFloor` twins over `rvwmoCatAD` + `noPlainAqC` only); a SIZING PASS (S, read-only) precedes any launch (§C top third set).
- **W11 `Weak/RvwmoXv6Adequacy.lean`** (L) [R4.3][R4.4].  **[rev 46] NEW obligations (1)–(5), §C top STAGE 2 ROADMAP (rev 46): (K-cat′)'s non-closing
  segments by the CS-chained route (Q-KCAT (a)); the lock-word check for PIPE locks (Q-DYNLKDISC); the `ip->ref` audited-racy arm (Q-F-RACY (a)); the used-ring
  boot-fill arm (Q-F-DISKTAIL (a)); still no PTE arm.  Gate: S4 merged + (K-cat′).**  (i) **The `Bad` arm is LOG-LEVEL**: `l2ClaimAt GD P Bad`
  (`Glue.lean:440-447`) hands the prover `(GD, log, logOf, protReg)` while the capstone sets `Bad := badRun gen σ0 = ∃
  ρ, rtc epfRun … ∧ violationHart …` (`:384-385`), a RUN-LEVEL existential refuted by `noBadRun` (`:387-391`) over ALL
  `epfRun`-reachable configurations — unreachable on route (M); `rawChainChain` consumes `¬ Bad` globally (`:453-460`).
  Define `badSeg GD log prev s` := the entry's source message is owned (`wmAk = .WCplain`) and unpublished at `log` by
  a FOREIGN hart; restate `l2ClaimAt` with it; prove `¬ badSeg` at the certified run from W8 (iii+) `chainOkAt` through W4 (the
  realized hull run is a prefix of the realizing TsoMem run) — at the read's post-state `coh j a` is its foreign source, the
  floor only rises (`cohOk`), `chainOkAt` gives a release by the author after the entry, WCrel on the pf log (the static
  release-site fact `fence rw,w; sw`, W9a, carried by `R`'s log identification); **[rev 28] lock-layer bytes are EXEMPT from
  `chainOkAt` and routed through `lockWordDiscAt`**: the `holding+0x12` read of `lk->cpu` IS a foreign owned-unpublished source
  for a non-holder, so `badSeg` is refuted there not by a chain but by `lkCpu_read_not_mine` (the value only feeds the `==
  mycpu()` compare; no hart reads its own pointer) — a NEW lock-layer `badSeg` arm (S) — **[rev 44] W13 (K)'s check (ii) lands HERE**: `ioSegPinned` (`WeakRvwmoKillIO.lean:609`) uses only (R1)–(R3) + check (i); the `lk->cpu` discipline `lockWordDiscAt` is the precondition of the CERTIFICATES of the window's racy lock-layer reads C1/C2 (census §(b).2), a machine-state predicate with no graph-tier statement — discharged on this lock-layer route; the cat-chain twin of the graph lemma is W13 (K-cat); **PTE bytes need NO arm [R25.1 (b)]** —
  the hardware A/D write-back is `.WCexcl` (`WeakKptStale.lean:26`), never a `badSeg` source; `pteDiscAt` is a documentation
  clause with no Stage-2 consumer named [R26.s2] (the walker's racy absorption is a `Wmstate` theorem), not used here; derive the
  global `¬ Bad`.  (ii)
  `protReg P log` (`:364-368`) is a fold over the LOG — transfers through `R`'s log identification once W8 exports (ii) (D24):
  `wlpAt`/`wlpAlt` (`WeakGhost.lean:543-545,699-701`) read off `lockWordDiscAt` through `rhist`; `wprotAt` (`:1040-1044`) only
  for the registered bytes still killed by `csHyps`; the cross-hart kill INTO a process-stack read uses a NEW **`chainHyps`**
  arm (`csChained` generalised to `syncPath` hops, `WeakRvwmoGlue.lean:424-437`; the [R23.1] third shape; M, **unverified**) —
  `csHyps`' `wprotAt` side condition (`:421-422`) is FALSE for stack bytes, written WITHOUT `p->lock` [rev 28, W8-design §1].  (iii)
  re-thread `execProgOk'S` through `RunData`, `cstOk`, `segStep`, `topoSupply`, `t2linSupply` — one pass with W5d-G G6.
  (iv) **(iv)a `linCandSca` — DONE [R16.4] (`Weak/RvwmoXv6Sca.lean`, 327, `Weak.lean:629`: `tvnSca :50` = #writes
  gmo-before `r`, `gwixLeTvnSca :116`, `tvnScaMono :133`, the named linearization facts `linGmoEmitBefore :144`/
  `linLogEmitted :172` (W13 (L) re-proves only those), `linTvnScaLe :194`, `linScaOk :241`, `linCandSca :314`; no
  exhaustive `Lbl`/`Wlabel` match)** (S) [R4.4] **+ (iv)b `linCandScaT` — DONE [R20.3] (`Weak/RvwmoXv6ScaT.lean`, 792,
  `Weak.lean:632`: `linCandScaT :757` — what W11 (v)/W13 (L) consume, on the NORMALIZED `GD'` (premise producer W12 (1))
  [R21.2] —, `linCandScaTCatT :780` (input graph; NOT on the Stage-2 path),
  `linCandScaTMinus :787`; premises `gwf`/`gppoCat6Gmo`/`gloadValue`/`grule14`, rules 2/4/5, no `gatomicity`/rule 12, `LIo`
  handled without `gwf`'s interim arm) and (iv)c `linCandDiskLat` (after W13 (L)) [W2s][R10.2] — **(iv)c DONE and MERGED 2026-10-13 11:41 (w5) [rev 44]: `RvwmoXv6ScaT.lean` §(6) `:806-`, `linCandDiskLatA :837`/`linCandDiskLat`/`linCandDiskLatMinus`, Rev 44 RESULTS**: the §B(10) derivations — the SCA
  witness is the load's gmo position, ≥ the pair's position by rule 5/4 and the gmo|W log order (`ptraceRel`); the
  `coh` part GRAPH-ONLY under the RULED (a′) [OWN.20][OWN.23][R11.1] — the THREE-case induction of §B(10) (same source /
  different source ⇒ rule 2 with `po-loc-no-w` / own write po-between ⇒ reset), foreign-source stamps only, against
  `TsoShadow.cohSrc`'s `shStep` (the stamp input `shLoadSrcs`); M
  (recorded: (a‴) vanishes S–M [R10.s4]; (b) a TRANSPORTED hypothesis, MOOT); disk-row loads latest from the (L)
  anchors.  Deps: W-COH ✓, W5b′ ✓.  (v) Restate `cycleKillOfL2''` (`Glue2.lean:521`), `t2linOfL2'''` (`Walk3.lean:77`),
  `xv6RvwmoSafeModuloT` (W12) with W8-sourced facts replacing `wpPackage`/`wpPackageProt`/`noBadRun`/`protRegOfRun`/
  `efetchItvOk`; compose with M2, W5d-G, W13 (`gfexecConfIO`, `ioResidueGmo`, T2-1c″, `cycleKillIO`): **T-alloc-RVWMO**.  Header per §B(11).
- *Not on the path:* **W6** PSO machine (L–XL; optional de-risk, D4); **W7-P** promise-machine fallback (D2').

**Stage 3 — AxSL tier: retired** [OWN.1].  One-paragraph note on Theorem 2 (D6).

**Status of the launch (rev 46, 2026-10-13) [OWN.56]–[OWN.58]:** MERGED since rev 45 — FabInd-S, W13 (W) part 1, W13 (K-cat) (STOPPED: counterexample), W9a
increment 1, W5d-G G1, W8 (f2-ctx) S3; S4 DONE in w2 (merge pending; THREE of six) (§C top Rev 46 RESULTS).  **IN FLIGHT: W5d-G G2–G5 (w1), W13 (W) rest (w3), W9a
increment 2 (w5).**  **LAUNCHABLE: W8 (pte-ghost)** (serial, after the S4 merge) and **(K-cat′)** (graph, under Q-KCAT's provisional (a)).  **Serial MachCSL**: … →
W8 (f2-ctx) ✓ (on the S4 merge) → **W8 (pte-ghost)** → W8 (f3-rest).  **OPEN owner questions (all non-blocking; provisional option in brackets): Q-KCAT [(a)], Q-W9A
[(A)], Q-F-RACY [(a), landed], Q-F-DISKTAIL [(a) landed; (G) recommended], Q-PTEDISC [(P-c) landed; (P-a) recommended], Q-DYNLKDISC [(L-b) landed; (L-a)
recommended]**; RULED: Q-BATCH-3 = (1) [OWN.56], Q-F2-PTE-WINDOW = (c) [OWN.57]; weekly cap lifted [OWN.58].  The rev-44 record follows.
**Status of the launch (rev 44, 2026-10-13) [R40.1][OWN.55]:** DONE since rev 43 — **W13 (R3′)** ((α) applied at launch), **W11 (iv)c**, **D35-fix** (13 roots
re-audited, baseline unchanged), **W13 (K)**, **W13 (F-dep)**, **W8 (f2-ctx) (a′-r) + S3-a + S3-b + S3-c0** (§C top Rev 44 RESULTS) — the Stage 2 FIRST and SECOND
batches are COMPLETE.  **IN FLIGHT: none** ((f2-ctx) RELAUNCH 5 waits for the 15:10 reset).  **LAUNCHABLE: the THIRD Stage 2 batch — W5d-G G1–G5 (G1 first) ∥ W9a ∥
W13 (W) [FabInd-S → (K-cat) → (W)]** (graph lane; owner's batch nod **Q-BATCH-3**; §C top) and **W8 (f2-ctx) RELAUNCH 5** (serial MachCSL; S3 wiring → S4 under
Q-F2-PTE-WINDOW's provisional (a)).  **Gated**: W13 (R) on W5d-G; W14 on W13 (W) + W5d-G; W10 on its sizing pass; W11 on S4 + (K-cat); W8 (f3-rest) on (f2-ctx).
**Serial MachCSL**: W-COH ✓ → W-DMA0 ✓ → W8-β′ ✓ → W-RSV ✓ → **W8 (f2-ctx) (RELAUNCH 5)** → W8 (f3-rest).  **OPEN owner questions: Q-F2-PTE-WINDOW** (§D FIRST;
provisionally (a), non-blocking) and **Q-BATCH-3** (approval).  The rev-43 record follows.
**Status of the launch (rev 43, 2026-10-13) [OWN.52]–[OWN.54][R39.1]–[R39.3]:** DONE since rev 41 — **W12 (+W12b)**, **W13 (L)**, **W8 (f2-ctx) S0 + S2**
(§C top Rev 42 RESULTS).  **IN FLIGHT: W8 (f2-ctx) RELAUNCH 3** (w2); **W13 (F-dep) RELAUNCHED under (A1)** (w3; [OWN.52]; [R39.2] applied at launch).  **LAUNCHABLE:
the SECOND Stage 2 batch — W13 (K) [(R3′) first] ∥ D35-fix ∥ W11 (iv)c** (graph lane; the owner's batch nod; §C top; (R3′) lands before D35-fix
launches, D35-fix after (F-dep) (1) or coordinated on `WeakRvwmoAdm` [R39.2][R39.s3]).  **Gated**: W5d-G G3/G4 on
(K)'s `racyDIO` commit, G1/G2/G5 on (F-dep) (1); W9a on (F-dep) (2)/(3); W10 on D35-fix (+ a sizing pass); W13 (R)/(W) on (K) + (F-dep); W14 on W13
(W) + W5d-G; W8 (f3-rest) on (f2-ctx).  **Serial MachCSL**: W-COH ✓ → W-DMA0 ✓ → W8-β′ ✓ → W-RSV ✓ → **W8 (f2-ctx) (RELAUNCH 3)** → W8 (f3-rest).
**OPEN owner questions: NONE** (Q-FDEP (A1) [OWN.52], Q-L-R3 (a) [OWN.53], D35-rule7 (a) [OWN.54]).  The rev-41 record follows.
**Status of the launch (rev 41, 2026-10-13) [OWN.48]–[OWN.51][R38.5]:** **IN FLIGHT: W8 (f2-ctx) RELAUNCH 2** (w2; Q-F2-PIPEHOP-2 = (a′-r) [OWN.49] and
F-C = (i) [OWN.50] inside it), **W12 (+W12b)** (w1; course note [R38.6]), **W13 (L)** (w4) — briefs unchanged.  **STOPPED GREEN, RELAUNCH when rev 41 is
signed off: W13 (F-dep)** (no edit made; §C W13 (F-dep) (0) + its launch paragraph; (A2) shape now, (A1) on the ruling).  **Gated**: as at rev 40.
**Weekly cap [OWN.51]**: no new launch at seven_day ≥ 90%, wind down green at 95%.  **OPEN owner question: Q-FDEP** (§D FIRST; provisionally (A2),
recommended (A1)); Q-F2-PIPEHOP-2 RULED (a′-r) [OWN.49].  The rev-40 record follows.
**Status of the launch (rev 40, 2026-10-13) [R36.1]:** DONE since rev 39 — **M2 CLOSE** (`Weak.srvwmoXv6M2` REGISTERED; **M1 + M2 DONE, Stage 1b
CLOSED**; §C top), **W8 (f2-ctx) S1′ + S2-pre** (MERGED; the worker STOPPED GREEN 2026-10-13; §C top RESULTS (rev 40)).  **IN FLIGHT: none.**
**LAUNCHABLE NOW: W8 (f2-ctx) RELAUNCH 2** (serial MachCSL; S0 = `pipeLockNameStr` + hop-shape fix [R36.2][R36.3], then S2b with F-B, S2
`CtxBox` with F-C (i) rows first [R36.4], S3, S4; §C top) and the **Stage 2 first batch — W12 (+W12b) ∥ W13 (F-dep) ∥ W13 (L)** (graph lane;
owner's batch approval; W12 → `AxDeps` rebuild-only edge [R36.s3]).  **Gated**: as at rev 39 (W5d-G G1–G5 + W13 (K) on the first batch's
statement commits; W13 (R)/(W) on (L)(K)(F-dep); W14 on W13 (W) + W5d-G; W9a on W12, W10 on W12b, W11 on W8 (f2-ctx) + W12 + W13 (K); W8
(f3-rest) on (f2-ctx)).  **Serial MachCSL**: W-COH ✓ → W-DMA0 ✓ → W8-β′ ✓ → W-RSV ✓ → **W8 (f2-ctx) (RELAUNCH 2)** → W8 (f3-rest).  **OPEN
owner question: Q-F2-PIPEHOP-2** (§D FIRST; the merged (a″) name-word window vs the RULED (a′); adopted PROVISIONALLY (a″+shape) under the
non-blocking rule, (a′-r) the named S4 follow-up — the ruling is wanted before S4 fixes the export's text).  The rev-39 record follows.
**Status of the launch (rev 39, 2026-10-13) [OWN.46][OWN.47]:** DONE since rev 37 — **W-SCO (A)** (w4; `sailCycleOrder_holds` a THEOREM, 122/122
clauses; `Weak.srvwmoXv6M1` REGISTERED; M1/M2 non-vacuous; §C top).  **IN FLIGHT: W8 (f2-ctx) continuation** (w2; [R35.1]/[R35.2] at launch;
[OWN.46]/[OWN.47]).  **LAUNCHABLE NOW: M2 CLOSE** (S; registration of `Weak.srvwmoXv6M2`; §C top) and the **Stage 2 first batch — W12 (+W12b)
∥ W13 (F-dep) ∥ W13 (L)** (graph lane; owner's batch approval; §C top).  **Gated**: W5d-G G1–G5 + W13 (K) on the first batch's statement
commits (file contention, not deps); W13 (R)/(W) on (L)(K)(F-dep); W14 on W13 (W) + W5d-G; W9a on W12, W10 on W12b, W11 on W8 (f2-ctx) +
W12 + W13 (K); W8 (f3-rest) on (f2-ctx).  **Serial MachCSL**: W-COH ✓ → W-DMA0 ✓ → W8-β′ ✓ → W-RSV ✓ → **W8 (f2-ctx) (RUNNING)** → W8
(f3-rest).  **OPEN owner questions: NONE** (Q-F2-PIPEHOP RULED (a′) [OWN.46]; Q-F2-BOOTGATE RULED (a) as amended [OWN.47]).  The rev-37
record follows.
**Status of the launch (rev 37, 2026-10-12) [OWN.45]:** DONE since rev 36 — **W13 (I)** (both halves; `gfexecConfIO`, contact membership,
`.PDisk` clause gone; §C top), **W8-β′** (157 static locks + `cpus[h]`; root `Xv6.xv6DiscAdequacy_closed` REGISTERED; §C W8), **W-RSV**
(`.pure` arm `dropResv`; `resvFragAny` threaded; `TsoMem` header updated; §C top).  **IN FLIGHT: W-SCO (A)** (w4; commit 1 = the restatement
with `Rboot` pinning `pma_regions` AND `htif_tohost_base` [R33.1]; M1/M2 vacuous until it lands — LANDED rev 39).  **LAUNCHABLE NOW: W8 (f2-ctx)** (serial
MachCSL; §C top paragraph).  **Gated**: M2 CLOSE on W-SCO (A) only; W5d-G G1–G5 gate MET (launch paragraph pending); W14 on W13 (I)/(W) +
W5d-G; W11 (iv)c on W13 (L).  **Serial MachCSL**: W-COH ✓ → W-DMA0 ✓ → W8-β′ ✓ → W-RSV ✓ → **W8 (f2-ctx)**.  **OPEN owner questions: NONE**
(Q-SCO-PMA RULED (α) [OWN.45]).  The rev-36 record follows.
**Status of the launch (rev 36, 2026-10-12) [OWN.42]–[OWN.44]:** DONE since rev 31 — **W5 CLOSE-OUT → M1 DONE** (registered,
`roots-weak.txt:20`; INTERNAL [OWN.2]; **VACUOUS until W-SCO (A)'s first commit lands [R32.1] — LANDED rev 39**), **W-SCO shape (0) + generic half**
(`SailCycleOrderK.lean`, imported, unregistered; its targets `cycleOkAll`/`cycleOkK` are FALSE as defined [R32.1]), **W13 (I) realization
half** (`MStepIo`, `projLbl` flip, `lbAdmin` drop), **W5d M2 CORE** (`PfRunUnpinned.lean` MERGED and imported [R32.2]; unregistered;
vacuous as M1).  **IN FLIGHT: W8-β′** (increments 2–4, w2), **W13 (I) bundle half** (w3; LAUNCHED with [R32.3] as a launch addendum).
**NEXT: W-SCO (A)** [OWN.42] — launchable with the rev-36 §C-top brief (commit 1 = the premise restatement under `wbootFacts σ0`).
**Gated**: **W-RSV** on W8-β′'s MERGE [OWN.41]; W8 (f2-ctx) on W-RSV; M2 CLOSE on W-RSV's W4 re-proof + W-SCO (A); W5d-G G1–G5 on (I)'s
bundle half; W14 on W13 (I)/(W) + W5d-G; W11 (iv)c on W13 (L).  **Serial MachCSL**: W-COH ✓ → W-DMA0 ✓ → **W8-β′ (RUNNING)** → **W-RSV** →
W8 (f2-ctx) [OWN.41].  **OPEN owner questions: ONE — Q-SCO-PMA, adopted PROVISIONALLY as (α) (RULED (α) [OWN.45] at rev 37)**.  The
rev-31 record follows.
**Status of the launch (rev 31, 2026-10-12) [OWN.38–40]:** DONE since rev 28 — **W4 F9** (`Weak/MachOfPfDisk.lean` 1290 NEW +
`MachOfPf.lean` 2979; `simDisk`, `R-dev` = `diskSide`/`devAgree`/`VRel.holds`, `cacheWf`, `devrt` untracked; no disk hypothesis;
[OWN.40] stall-on-wrap in `VirtioProg.lean`), **W5 CORE** adapted (`Weak/SrvwmoXv6Adequacy.lean` 318: `srvwmoXv6M1Core` =
premises + `g0` boot facts + `sailCycleOrder`; **M1 PROVED, registration pending = W5 CLOSE-OUT**), the **import-hygiene fix**
(`ExecSC4` imports `UTlb`; `Weak.lean:634`), **R-ctx** (`notes/W8-Rctx.md`: F0 → per-author vector [OWN.38]; 31 rows, none RESISTS,
(f1) list EMPTY; X1–X5; user PTEs → `pte-key` [OWN.39]).  **IN FLIGHT: W8-β′** (serial MachCSL, since 10:26, rev-30 brief +
[R27.s1]–[R27.s3]).  **Now launchable (§C top; no owner gate)**: **W5 CLOSE-OUT** (S) ∥ **W-SCO** (M–L, `Weak/`; `sailCycleOrderK` +
`srvwmoXv6M1`) ∥ **W13 (I)** (M, graph lane) ∥ **W5d** (L, `Weak/`; `srvwmoXv6M2Core`).  **Gated**: W8 (f2-ctx) (≈ 6.5–9.5k, 12
MachCSL + ≈ 52 `Xv6/`, 3–4 rebuilds) on **W-RSV** [OWN.41]; **W-RSV** on W8-β′'s MERGE (M1 ✓) — **Q-RSV-order RULED (b) [OWN.41]
[R28.5]**; M2 on W5d + W-RSV's W4 re-proof; W5d-G G1–G5 on (I)'s `Fab`/`Supply` text; W14 on W13 (I)/(W) + W5d-G; W11 (iv)c on W13 (L).
**Serial MachCSL**: W-COH ✓ → W-DMA0 ✓ → **W8-β′ (RUNNING)** → **W-RSV** → W8 (f2-ctx) [OWN.41]; W8 (f2-ctx) waits for W-RSV and
rebases on its `resvFragAny` thread (`ctxTok`, `Ctx.lean:298-299`).  **Shared-file landing order of the four lanes [R28.3]**: W5
CLOSE-OUT → W-SCO (`Hyps.fi` widening first, registration last) → W5d rebases `m2Hyps`.  **OPEN owner questions: NONE** (rev 32;
R28: none missing — every change is proof organisation or registration, RVWMO/Sail/Zifencei/PMAs silent, every option FAITHFUL).
The rev-28 record follows.
**Status of the launch (rev 28, 2026-10-12) [W2s][OWN.16–37] — RECORD:** DONE — **W-DISK** (2026-10-12: `VirtioProg.lean` aligned,
ten-arm `pdiskProg`/`ediskStep`, `ewpDisk*`, `pfDWriteDevRowMem`/`pfDSkipRowMem`/`rowDiskDevMove`, `devQuiet`/`epsInitQuiet`,
interim `gfexecConf` clause; deviations d1–d4), **W8-design** (read-only; export `xv6AccessDisc`, buckets, feeds, W8-β′,
R-ctx, (r2), the `holding+0x12` race), W3, W5b, W5c, W1b (+ follow-up + (A)), W5b′,
W-COH, W5d-G G0, W2a, W2b, **W13 (T)+(M)** (`GraphFabResidue.lean`, `lbIsMem`), **W5-pre**, **W11 (iv)a** [R16.4], **W2
CLOSE** (`Weak/PfStepTso.lean`; item (3) → `sailCycleOrder` [OWN.35]), **W11 (iv)b** (`Weak/RvwmoXv6ScaT.lean` [R20.3]),
**W-DMA0** (option (A), `hzero` form), **W4 F1–F8** (`Weak/MachOfPf.lean`, `machRunOfPfRun`); the W2 spike (D7 STOP,
redesigned); W13 (E) PARTIAL (alphabet merged, three lines → (I)); censuses W4/W13 landed.  IN FLIGHT: none.  **Now
launchable** (§C top; no owner gate): **W4 F9** (L; `R-dev` = full `dvirtio` equality off the OUT capture segment,
`preCaptureHead` on it; re-proves every `SimRel.dev` consumer [R21.3 (c)]) ∥ **W8-β′** (M–L; serial MachCSL — the lane's next
item; `reservedOk` + `powerInterp_accessDiscβ` + the (r2) twin at `lockWordDiscAt ∧ cpuStaticAt` [R25.2]; unblocks W13 (K) at
the root level) ∥ **R-ctx** (S; read-only check of the ≈ 35 TSO-leaky uses in 21 files incl. the `swtch` door and the walker's
`pte-key` arm [R25.1][R25.3] — W8 (f2-ctx)'s gate) ∥ **W5 CORE** (M; M1 parametric in F9's `Hyps.disk`, discharging `winPristine`; PLUMBING, not counted or
registered until F9 [R21.4]).  **W13 (I)**: gate MET (W-DISK ✓), next in the graph lane when a worker is free.
**Gated**: W8 (f2-ctx) (serial MachCSL, L–XL, 2–4 rebuilds) on W8-β′ AND R-ctx [OWN.37]; M1's CLOSE on F9 + W5 CORE (NOT on
W8 — `Weak/`-only, no W8 fact in its premise set; it closes in parallel, §C top); W-SCO on M1; W-RSV on M1 AND W8 (f2-ctx);
W5d/M2 on M1; W5d-G G1–G5 — gate W13 (M) MET, launched after (I)'s brief fixes the
`Fab`/`Supply` text (D26); W14 on W13 (I)/(W) + W5d-G; W11 (iv)c on W13 (L).  **Serial MachCSL**:
W-COH DONE → W-DMA0 DONE → W8-β′ → W8 (f2-ctx) [OWN.37] → W-RSV after M1 (D19 (b), form (i-a) RULED [OWN.22][OWN.23]; L–XL, one `Xv6`-cone rebuild; 12 `Xv6/`
files incl. the M-mode lane [R12.1][R13.1]) — W-RSV waits for M1 (D26) and for W8 (f2-ctx) (file overlap), not for an owner;
M1 itself runs on the `Weak/` lane beside W8.  The published statement's
shape is FIXED (D32, D33, D37, D38, D44–D52 RULED [OWN.11–18]); W-DISK changes the DEVICE MODEL under it toward the
model of record, not the statement — `gdexecQconfT`/`xv6ConfS` gain ONE sentence ("the device's request-service RAM stores are fabric transactions — each reads
the device state at the store and may move it; the used-idx store is the one that raises the interrupt" [OWN.31][R22.2])
and the disk row ONE more `dev` event per request (the pop [OWN.32]) plus three to four fabric-moving `LStore`s per request
in `gfDev` (the [OWN.31]/[OWN.32] wording delta, REPORTED — §D Q-GFDEV-delta, no gate); the pf disk row's
SEQUENTIAL service is a named strengthening (§B(11) (viii)) — a concurrent pf disk agent is the follow-up after M2
[OWN.33].  W13 (F-dep) after
(I).  **OPEN owner questions: NONE** [rev 28 record — rev 31: Q-RSV-order OPEN; rev 32: RULED (b) [OWN.41], §D] (Q-GFDEV-delta rev 26 and Q-HOLDING rev 28 are REPORT level; R26: none missing — [R26.1]/
[R26.2] are proof organisation, every option FAITHFUL) — Q-W8-feed RULED (a) [OWN.37]
(rev 28); Q-W8-lane RULED (α) [OWN.36]; Q-FIARM RULED (b)+(a′) [OWN.35]; W-DISK-Q1–Q4 RULED [OWN.30]–[OWN.33], W-DMA0's
route RULED (A) [OWN.34].

## D. Owner questions (recommended first; RULED items kept, tightened — [R7.s1]'s appendix NOT adopted: this file only)
**FIXED: D32, D33, D37, D38, D44, D45 RULED.  G2-Q RULED (a′) with BOTH components — the reset CONFIRMED [OWN.21], the
foreign-only stamp RULED [OWN.23] — and LANDED (W-COH).  W-RSV-Q RULED (i-a) [OWN.22][OWN.23]; D19 (b) stands; Q-W5dG-seq
RULED (a) [OWN.24]; Q-CI-Weak (R15) RULED "no CI change until end to end" [OWN.25].  **RULED 2026-10-11 (rev 19): Q-W5dG-slot
= the REAL slot tag `emSlot` [OWN.26]; Q-W13E-seq = (a) re-sequence `projLbl`/`lblRealizes*`/`lbAdmin` drop into (I),
`LIo` shape arms `False` until (I)/(M), next (T) then (M) [OWN.27]; W1b-hist-Q = (A) fork-only joined history per era
[OWN.28]; E-D1 (the W4 census's disk model) = (a) align `virtioProg` to MachCSL's `serve` — RE-ASKED with full context,
the first answer (b) superseded [OWN.29]** (each recorded below).  **RULED 2026-10-11 (rev 20) [R16.2]: W-DISK-Q1 = (b)
the MachCSL `storeDma pa 0` no-op → the standalone serial item W-DMA0 [OWN.30][R16.3]; W-DISK-Q2 = (a) the fused used-idx
`DWriteDev`, `gfDev` = the fabric TRANSACTIONS (I/O-class events by class, plus fabric-moving stores) [OWN.31][R23.2]; W-DISK-Q3 = (a) guards folded into `DWriteDev`, the ring pop ONE `LDev .dev`
step, no pure re-read node [OWN.32] — all three recorded first below, "RULED as recommended"; RULED 2026-10-11 (rev
21): W-DISK-Q4 = (c) sequential pf disk now, named §B(11) (viii); a concurrent pf disk agent = named follow-up after M2
[OWN.33]; RULED 2026-10-11 (rev 23): W-DMA0's route = (A), the `n ≠ 0` premise on the DMA lease rule's `dmaWrite`
constructors [OWN.34] (recorded below, §C W-DMA0); RULED 2026-10-11 (rev 24): **Q-FIARM = (b)+(a′) [OWN.35]** — ONE named
trusted premise `sailCycleOrder`, demoted for kernel text by W-SCO after M1; RULED 2026-10-11 (rev 25): **Q-W8-lane = (α)
[OWN.36]** — W8-design spike, then W8's ledger as the next serial MachCSL item before W-RSV (FIRST below; raised by R21,
whose [R21.2]–[R21.4] are plan text in the sound direction and raised nothing else); REPORT 2026-10-11 (rev 26):
**Q-GFDEV-delta** — the [OWN.31]/[OWN.32] wording delta from [R22.2], applied as (a), no gate ([R22.1] and
[R22.3] are plan text in the sound direction); RULED 2026-10-12 (rev 28): **Q-W8-feed = (a) (f2-ctx) [OWN.37]** — W8-β′
(lock words + `cpus[h]`, M) first, the read-only R-ctx gate, then W8 (f2-ctx) (L–XL, 2–4 rebuilds; fallback (f1) per part),
export via the sibling root (r2) `xv6DiscAdequacy_closed`; supersedes [OWN.36]'s one-rebuild sizing (FIRST below); REPORT
2026-10-12 (rev 28): **Q-HOLDING** — the `holding+0x12` data race on `lk->cpu`: the plan's (iii) was FALSE there, the export
exempts lock-layer bytes and covers them by `lockWordDiscAt`, no gate (second below).  **RULED 2026-10-12 (rev 31): Q-R1 (R-ctx F0)
= (a) the per-author vector chain bound beside the scalar TSO bound [OWN.38]; Q-R2 (user-PTE A/D) = (a) user PTEs under the
`pte-key` arm [OWN.39]; W4-F9-wrap = (a′) the pf OUT capture STALLS on a wrapping buffer [OWN.40] (all three recorded below, after
the OPEN item).  Q-RSV-order RULED (b) [OWN.41] 11:09 2026-10-12 (FIRST below; lane order only) [R28.5].  OPEN: NONE (rev 32).  RULED 13:59
2026-10-12 (rev 35): **Q-SCO-words = (A) [OWN.42]** — W-SCO proves `cycleOkAll` for EVERY instruction, `sailCycleOrder` a THEOREM for all
text; **Q-GFDEV-contact = (a) [OWN.43]** — `gfDev` membership by fabric CONTACT, `hblkQ`'s folding generalized (both raised by the
W-SCO / W13 (I) workers' PROGRESS files, recorded below before Q-FIARM).  OPEN: NONE (rev 35).**  R20 (rev 24)
raised NO owner question ([R20.1]–[R20.2] are pf-internal device-model engineering in the SOUND direction, pf ⊆ MachCSL:
RVWMO, riscv.cat and this tree's Sail model have no device-internal events, Zifencei/PMAs are silent, virtio 1.x is
silent on reset-time bookkeeping and — unverified in-tree — on zero-length buffers; eliding a zero-length transfer is
EQUAL to MachCSL's `dmaRead pa 0`/`storeDma pa 0` after W-DMA0).  R19 (rev 23) and R18 (rev 22) raised NO owner question for
the same reason (pf-internal device-model engineering, pf ⊆ MachCSL; WHERE pf drains / samples `cfg` is EQUAL to one of
MachCSL's schedules; [R18.2]'s interim clause restricts an INTERNAL bundle, D39).  The
"Standing" D-items below are provisional recommendations
kept at the owner's instruction ("keep the recommendations as provisional"), not questions awaiting a ruling.  RULED by
[OWN.17]: G1-Q (e), G3-Q (a″), D46 (a), D47–D49 (a), D50 (b); by [OWN.18]: D42–D43 (a), D51–D52 (a); by [OWN.19]: D19
(b), D20 (a), D9 (a), D8 (a); by [OWN.16]: W1-Q (c), Q-W3a (A), D41 (a), D45 (a).**
**OWNER RULE (2026-10-09) [R8.1][R9.1][R9.s3]: every OPEN or STANDING semantics question below (G1-Q–G3-Q, D19, D20
included) opens with "Spec:" — what the RVWMO chapter,
the appendix "I/O Ordering" (quoted in §B(11b): (c1)–(c5), the FENCE and DEVICE sentences), the Sail model in this
tree (file:line), Zifencei and the PMAs say, or that they are silent — and marks each option FAITHFUL (the spec's
executions), STRONGER (excludes spec-allowed executions; must be a NAMED trusted item) or WEAKER (admits more; sound),
costs after.  Shared Sail/PMA facts: `execute_FENCE` keys on the low two bits of each set after
`effective_fence_set` (`InstsEnd.lean:18299-18313`, `BaseInsts.lean:568-573`; FIOM folds i/o INTO memory bits, FIOM
= 0 at `BootBoard.lean:30`); `fence.i` = `Barrier_RISCV_i` (`:18295-18297`); MMIO is an ordinary `mem_read`/
`mem_write` routed by `devAddr` (`MachCSL/Dev/Fabric.lean:126` [R9.2]); Sail's `PMA` has NO ordering/channel attribute
(`LeanRV64D/Defs.lean:549-566`); the platform table types `[0x2000000, 0x12000000)` `IOMemory`, non-idempotent
(`MachCSL/Platform.lean:220-239`; RAM `MainMemory :240-254`), consulted only through `matching_pma_ram`
(`PlatformFacts.lean:24`); Sail has NO device/DMA model (`MachCSL/Dev/*.lean`); PMA strong ordering is within ONE channel only.**
**RULED 16:56 2026-10-12 (rev 37): Q-SCO-PMA = (α) [OWN.45] — the Sail cycle-order fact (`sailCycleOrder`/`good`/`cycleOkBoot`) is stated
under `wbootFacts σ0` (the board after reset: device regions non-executable, HTIF window disabled [R33.1]).  **Q-F2-PIPEHOP and
Q-F2-BOOTGATE** (raised by the W8 (f2-ctx) worker at its S1 stop, `PROGRESS-W8f2.md` findings 2–3; rev 38: adopted PROVISIONALLY (a) under the
non-blocking rule) — **RULED 23:25 2026-10-12 (rev 39): Q-F2-PIPEHOP = (a) as amended by [R35.1] = (a′) [OWN.46]; Q-F2-BOOTGATE = (a) as
amended by [R35.2] [OWN.47]; R35 found no missing question (both corrected options FAITHFUL).  OPEN: NONE (rev 39).**  **OPEN (rev 40):
Q-F2-PIPEHOP-2 [R36.3] — the W8 (f2-ctx) worker MERGED Q-F2-PIPEHOP as (a″) (the lock's NAME-WORD window, indexed at the acquire), a DEVIATION
from the RULED (a′); adopted PROVISIONALLY as (a″+shape) under the non-blocking rule (owner informed), FIRST below; then Q-F2-PIPEHOP, Q-F2-BOOTGATE, Q-SCO-PMA.**  **RULED 05:18 2026-10-13 (rev 41): Q-F2-PIPEHOP-2 = (a′-r) [OWN.49] (the entry-receipt
anchor, inside W8 (f2-ctx)); F-C = (i) [OWN.50].  RULED 10:22 2026-10-13 (rev 42): **Q-FDEP = (A1) [OWN.52]** (W13 (F-dep) relaunches under (A1) directly); **Q-L-R3 = (a) [OWN.53]** (widen
(R3) to all `gfDev` members → W13 (R3′), §C top); **D35-rule7 = (a) [OWN.54]** (`lbRcsc` to riscv.cat's RCsc → D35-fix, §C top) — the two new
ones recorded FIRST below in the owner format (they arrived RULED; the briefing is for the record), then Q-FDEP, then Q-F2-PIPEHOP-2 (RULED).
OPEN: NONE (rev 42; rev 43 — R39 found none missing, [R39.3]'s refinement of RULED Q-L-R3 (a) recorded there).  **Rev 44: R40 found none missing ([R40.1] is a refinement WITHIN RULED Q-L-R3 (a) — RVWMO/riscv.cat/Sail have no device events, Zifencei/PMAs silent, (α)/(β) EQUAL in strength on every xv6 run; owner informed, no menu); NEW from the W8 (f2-ctx) worker: Q-F2-PTE-WINDOW (FIRST below; provisionally (a)), and the third batch's approval Q-BATCH-3.**  **Rev 45: R41 found none missing — [R41.1] CORRECTS OPEN Q-F2-PTE-WINDOW's bound (every option keeps its mark; (a) stays sound and recommended; the owner should see the corrected bound before ruling), [R41.5] puts Q-BATCH-3 in the format; [R41.4]'s `usedElemGateOk` is a named device-model hypothesis EQUAL to MachCSL's disk step on xv6 runs (RVWMO/riscv.cat/Sail/Zifencei/PMAs silent on device programs) — informed under the non-blocking rule, no menu.**  **Rev 46 (no new review): RULED [OWN.56] Q-BATCH-3 = (1), [OWN.57] Q-F2-PTE-WINDOW = (c); NEW, FIRST below in the owner format, each non-blocking under its provisional option: Q-KCAT, Q-W9A, Q-F-RACY, Q-F-DISKTAIL, Q-PTEDISC, Q-DYNLKDISC; INFORMED (no menu): G1's E1′ reading (after the six).**  R34 found no missing owner question ([R34.1]'s include-or-defer is a
scope choice, both options FAITHFUL; taken by the coordinator: DEFERRED to W8 (f3-rest)).**
- **Q-KCAT — OPEN, provisionally (a) (rev 46; raised by the W13 (K-cat) worker, `../weak-orch/parked/PROGRESS-W13W.md`; counter-model `Weak/WeakRvwmoKillIOC.lean`).
  The planned cat-model lemma "an I/O event pins the rest of its segment" is false; how to certify the segments it cannot pin.**  *Plain language.*  The published theorem
  quantifies over riscv.cat executions.  To rule out a forbidden cycle through an I/O event (an MMIO store), the proof cuts the cycle into SEGMENTS (stretches of one hart's
  program between cross-hart edges) and certifies each; for a segment starting at an I/O event it wanted one lemma: every later event of the segment is in memory order
  after the I/O event, or is a load that got its value forwarded from such a later store of the same hart.  Under riscv.cat that lemma is FALSE, by a computed
  counterexample with no fences at all, for two reasons the model really has: two loads of the same byte that read the SAME store are not ordered; and a load gets its
  value byte by byte, so "forwarded" can hold for one byte while the others come from elsewhere.  *Tiny example* (computed, `kcatCex :87`): hart 0 does `x`: MMIO store
  to the UART; `w`: `sb [1] ← 1`; `u`: `lh [0]` (byte 0 from the initial image, byte 1 forwarded from `w`); `v`: `lb [0]` (byte 0 from the image — `u`'s source for that
  byte).  Hart 1 does `w2`: `sb [0] ← 1`; `y`: MMIO store.  Memory order `u, v, w2, y, x, w` is riscv.cat-consistent (`:90`) and satisfies the trusted I/O residue (`:106`):
  `v` may perform before `x` because nothing orders it after `u` (same byte, same source), and `u` is "forwarded" only through byte 1.  The segment `x → w → u → v`
  exits at `v`, BEFORE `x`: no I/O-pin certificate exists (`:166`).  *Definitions*: *segment / certificate `CertC`* — the cat chain's unit of the cycle-kill argument and
  its evidence (`CatLin.lean`, W12); *`rsameC`* — the same-hart steps a segment may take (ppo, deps, rfi); *forwarded (`grfi`)* — a load reading a po-earlier store of its
  own hart; *gmo* — the global memory order; *I/O residue (R1)–(R3)* — the named platform assumption ordering I/O against RAM accesses (§B(11)); *W11* — the item proving
  xv6's lock discipline leaves no unchained racy read (the CS-chained / lock-layer route); *RVWMO⁻* — the tree's stronger internal model, where the lemma IS proved
  (`ioSegPinnedMinus`, `WeakRvwmoKillIO.lean:664`); *(K-cat′)* — the re-scoped S–M item of option (a).  *Why it matters*: without a certificate for such segments the I/O
  half of the kill argument has a hole; under every FAITHFUL option the published statement is unchanged — only where the proof gets the certificate changes.  *Spec
  (FIRST)*: RVWMO ppo rule 2 orders two same-address loads only if they return values for some byte from DIFFERENT writes; riscv.cat writes it `([R];po-loc-no-w;[R]) \
  rsw`; rf and the load value axiom are per byte (mixed-size); the Sail model is a per-hart sequential semantics with no memory-model text (silent); Zifencei and the PMAs
  are silent; the residue gives only (R1)–(R3).  *Options*.  **(a) RECOMMENDED — named per-step condition + the lock-layer route**: (K-cat′) proves `ioSegPinnedC` under a
  named condition listing the closing step kinds (write targets by (R2), I/O targets by (R3), forwarding, the cat-ordered arms out of a gmo-after-`x` event, `pw` fences
  out of forwarded reads, same-byte `gpoloc` on the forwarded byte); a segment taking any other step (`u → v` above) is certified by W11 instead — its outgoing cross edge
  (`fr v w2`) is a race on `v`'s byte, which `chainOkAt` excludes.  FAITHFUL (riscv.cat kept); cost S–M + a new segment shape in W11's census (S–M); unblocks W11's gate;
  risk: an xv6 segment of that shape that is NOT lock-protected would be a real race — a finding about xv6, surfaced by W11.  **(b) per-byte certificates**: widen
  `CatLin.CertC` to certify (segment, outgoing edge) pairs — an exit read not after `x` is fine when its outgoing edge is on a forwarded or coherence-later byte.
  FAITHFUL; M–L, edits W12's shared kit `CatLin.lean`, and STILL needs (a)'s lock route for the off-byte case (`v`'s byte 0).  **(c) keep RVWMO⁻'s order of same-address
  loads** (lemma already proved there): STRONGER than RVWMO — the theorem would stop covering hardware that performs same-source same-address loads out of order;
  EXCLUDED by [OWN.2]; cost 0.
- **Q-W9A — OPEN, provisionally (A) (rev 46; raised by the W9a worker, `../weak-orch/parked/PROGRESS-W9a.md`; increment 2 under (A) RUNNING, w5).  The checker's
  per-site certificates assume a certified stretch runs exactly as the checker walked it; a real Sail run need not.**  *Plain language.*  An offline checker walks the
  kernel code from each racy load (a "pin site") and certifies that the loaded value reaches later instructions only through dependencies the memory model respects.  W9a
  connects those certificates to the graph proof, which needs: the instructions the real run executes after the load are the ones the checker walked.  That fails in four
  ways on the Sail model: a pending enabled INTERRUPT is taken before the next instruction (the run jumps to `kernelvec`); a TAKEN branch goes to the arm the walk did not
  follow; a `ret` in a called function jumps to the `ra` reloaded from its stack frame (the walked target only if nobody overwrote that slot); and per-instruction register
  dataflow facts about each Sail `execute` clause are witnessed by examples only.  *Tiny example*: hart 1 executes a certified load `ld a5, 0(a0)` with S-mode interrupts on
  and a timer interrupt pending; Sail checks for interrupts before the next fetch (`Step.lean:332-333`) and runs `kernelvec`'s spills instead of the walked instruction at
  `pc+4` — the certificate's walk does not describe this run.  *Definitions*: *pin site / certificate* — a racy load and the checker's evidence for it; *R-3* — the plan's
  claim "a run's items are grouped per instruction as the checker's walk assumes"; *`segPinC`* — the cat-chain segment property the certificates must imply; *`runAligned`*
  — option (A)'s named premise (per-instruction grouping at the announced word, no trap inside the stretch, `ret` targets as walked); *DEC-7* — the per-instruction
  register read/write shape the checker assumes; *W8 stack ownership* — the access discipline's fact that a kernel stack frame is written only by its owner.  *Why it
  matters*: until discharged, the final theorem either carries `runAligned` (covers only runs whose certified stretches are trap-free and walk-aligned — a narrower scope)
  or proves it.  *Spec (FIRST)*: Sail dispatches a pending enabled interrupt at every instruction boundary BEFORE the fetch (`model/Lean_RV64D/LeanRV64D/Step.lean:331-335`;
  handled `:424`, → `stvec`); RVWMO's ppo has no trap or `sret` arm (a trap is not a memory barrier); Zifencei and the PMAs are silent.  *Options*.  **(A) RECOMMENDED now
  — named alignment premise**: R-3 becomes the NAMED premise `runAligned`; everything run-independent is proved (increment 1 ✓; increment 2 = taken branches by an
  any-path `reaches` + soundness of the checker's all-paths search, S–M, RUNNING).  FAITHFUL; the deliverable keeps a premise; cost S–M; unblocks W11's `segPinC ∨ csHyps`
  arms now; risk: without (B) the final theorem is restricted to aligned runs.  **(B) full discharge**: per-`execute`-clause dataflow lemmas by a W-SCO-style walker
  (≈ 121 clause lemmas), the trap crossing (a load's value spilled by `kernelvec` and restored is a rule-12 chain via `pdepSegPinCForward`, needing own-stack rf), `ret`
  targets from W8 stack ownership.  FAITHFUL; XL (≈ 3–5k); after S4 + stack ownership; a read-only spike first.  **(C) certify only interrupt-free windows** (`SIE = 0`,
  e.g. inside `push_off`): FAITHFUL; needs checker/generator changes (§B(9) excludes them) and routes more sites to W8.  **(D) treat trap entry as a fence**: STRONGER than
  RVWMO and Sail (a trap orders nothing in either) — rejected.  Recommended: (A) now; (B)'s spike after S4, so the final theorem has no `runAligned`.
- **Q-F-RACY — OPEN, provisionally (a) as landed (rev 46; raised by the W8 (f2-ctx) worker at S3, `PROGRESS-W8f2.md` F-RACY).  `ilock`/`iunlock` read an inode's
  reference count without the lock that guards it; the export exempts those bytes.**  *Plain language.*  `ip->ref` is written only under `itable.lock` (`iget`, `idup`,
  `iput`), but `ilock` and `iunlock` test `ip->ref < 1` (then `panic`) WITHOUT taking it (`kernel/fs.c:300,325`).  That read races with other harts' `idup`/`iput`:
  nothing orders it after their latest write, so "every racy read is chained to its writer" is false there.  The race is benign — the reader holds a reference, so it reads
  ≥ 1 whatever write it sees — but real.  S3 added a registered "audited racy" class: the 4 bytes of `ip->ref` in each of the 50 `itable` entries (`xv6IrefRacyR`,
  `KernelRsv.lean:79`) are exempt from the chain claim.  *Tiny example*: hart 1 holds a reference to `ip` (its `idup` wrote ref = 2 under `itable.lock`) and calls
  `ilock(ip)`; hart 2 concurrently `idup`s it (2 → 3 under the lock); hart 1's guard may read 2 or 3 — no lock hand-off orders it after hart 2's write, so no chain exists;
  both pass the test.  *Definitions*: *chain* — a release by the writer, lock hand-offs, an acquire by the reader (`chainOkAt`); *exempt / `racyByteIn`*
  (`ChainDefs.lean:682`) — bytes the export claims no chain for; *audited racy (W9b)* — W8-design's class of known benign races, justified separately; *W11* — the item
  showing no racy read breaks the RVWMO argument.  *Why it matters*: the export's sentence gets a named hole (200 bytes, each a counter whose only lock-free use is a panic
  test); W11 needs its own argument for these reads either way.  *Spec (FIRST)*: RVWMO/riscv.cat/Sail are silent on custody; on the read itself RVWMO lets a load return
  any write not coherence-before what the hart has already observed, so the guard can see any concurrent count (the race is real under RVWMO, as under TSO); Zifencei and
  PMAs silent.  *Options*.  **(a) RECOMMENDED — accept as a NAMED weakening (as landed)**: no chain claimed for `ip->ref` bytes; the docstring names the class and why it
  is benign; W11 gains an audited-racy `badSeg` arm (the value only feeds the `< 1` test, which never fires).  FAITHFUL; export WEAKER by exactly those 200 bytes; cost 0
  now + S in W11.  **(b) a value-safe claim instead of none**: for these bytes the export states "every value a guard read can return is ≥ 1" (an invariant over
  `ip->ref`'s history tied to the reader's held reference).  FAITHFUL; STRONGER export than (a) (still no chain, but the benign-ness is a theorem); M (`IcachePinwObl`,
  the `iget`/`idup`/`iput` proofs, a new export clause).  **(c) prove the read chained**: impossible — the race is real.  **(d) kernel change**: take `itable.lock` in the
  guard (or drop it): the race disappears, export EQUAL to the intended one, but xv6 changes (the `verified` branch's diff D12 grows), the image is re-dumped and
  `ilock`/`iunlock` re-proved — S if no pc shifts, XL if any does (a sizing pass decides).  Recommended: (a) now; (b) if the owner wants the benign-ness published.
- **Q-F-DISKTAIL — OPEN, provisionally (a) as landed; recommended (G) (rev 46; raised by the W8 (f2-ctx) worker at S3, F-DISKTAIL).  The disk driver can read the used
  ring's boot-time zero fill with no chain; the export exempts the whole used-ring page.**  *Plain language.*  The virtio disk reports finished requests through the
  "used ring", a 4 KiB page the DEVICE writes by DMA; hart 0 zero-fills it once at boot (`memset(disk.used, 0, PGSIZE)`, `virtio_disk.c:128`).  `virtio_disk_intr`
  reads `disk.used->idx` (`:318`) under `vdisk_lock`; before the device's first completion that read returns hart 0's zero, on ANY hart, and the proof holds only a
  "visibility key" for it, not a chain — so S3 exempted every byte of a page a registered device-ring pointer names (`devPageIn`, `ChainDefs.lean:688`; `xv6UsedPtrR`,
  `KernelRsv.lean:85`).  Device-written bytes already have a device certificate, so the exemption's real content is hart 0's boot fill.  *Tiny example*: hart 0 runs
  `virtio_disk_init` (zero fill), then sets `started = 1`; hart 2 starts after seeing `started`, takes a disk interrupt and reads `used->idx = 0` from hart 0's fill — this
  read IS ordered (hart 2 waited for `started`), but the proof's key does not say so.  *Definitions*: *used ring / `used->idx`* — virtio's device→driver completion queue
  and its counter; *visibility key* — a proof token weaker than a chain; *`started`* — the boot flag harts ≥ 1 spin on, whose hop `pubCover` the export already uses;
  *boot-gate arm* — a certificate kind "written by hart 0 before `started = 1`".  *Why it matters*: the published sentence exempts a whole page forever ("device memory
  unchecked") although its only hart-authored bytes are chained by the boot gate.  *Spec (FIRST)*: RVWMO/riscv.cat/Sail have no device or DMA model (`MachCSL/Dev/*.lean`
  is MachCSL's own); the PMAs type the ring page main memory (coherent RAM); virtio 1.x says the device writes the used ring and the driver reads it, silent on boot-time
  initialization ordering; Zifencei silent.  *Options*.  **(G) RECOMMENDED — a boot-gate certificate arm**: `srcCertAt` gains an arm for entries authored by hart 0 before
  its `started` store, paid to harts ≥ 1 by a receipt of that store entry (`StartedInv`); `devPageIn`/`RsvKind.devPtr` are DELETED.  FAITHFUL; export EQUAL to the
  intended one (the arm serves any hart-0 init data); S–M (MachCSL arm + `StartedInv` receipt + the disk invariant; unverified); a W8 (f3-rest) part after (pte-ghost).
  **(a) accept as a NAMED weakening (as landed)**: device-ring pages get no chain claim, named in the docstring; W11 proves the boot-fill arm itself (S).  FAITHFUL; export
  WEAKER; cost 0.  **(K) full keys**: the used ring's tail positions keyed in the `vdisk_lock` payload, positions fixed in the disk invariant.  FAITHFUL; EQUAL export;
  ≈ 300–500 lines (`DiskInvDefs`/`DiskAcc`/`ProofVirtioDiskIntr`), disk-specific.  Recommended: (G); (a) stands until it lands.
- **Q-PTEDISC — OPEN, provisionally (P-c) as landed by S4; recommended (P-a), kernel half first (rev 46; raised by the S4 worker, w2 `PROGRESS-W8f2.md` F-PTEDISC).
  Page-table bytes are exempt from the chain claim, but S4 could not state what discipline those bytes DO follow.**  *Plain language.*  Page-table entries (PTEs) are
  exempt from "every racy read is chained" because the hardware page-table walker may set a PTE's Accessed/Dirty bits at any time, ordered by nothing.  The plan's companion
  clause `pteDiscAt` said what replaces the chain: after the kernel table is sealed, every write to a kernel PTE byte is the sealed value with at most A/D changed, by a
  hart (likewise per publication epoch for user tables).  That fact is PROVED inside the machine proof (Iris invariants `KptInv`, `pptPost`), but the export is a pure
  predicate read from the machine-state interpretation, which says nothing about PTE bytes — so S4 could not export it.  *Tiny example*: hart 1's `walk` reads a kernel
  PTE while hart 2's hardware walker has just set its A bit; the export exempts the read from chains, and `pteDiscAt` would add "the value read is the sealed PTE up to
  A/D" — without it the theorem says nothing about PTE values.  *Definitions*: *seal* — the point after `kvminit` from which software leaves kernel PTEs alone except A/D
  (`kptOn_seal`); *A/D variant* — the same PTE with A/D possibly set; *state interpretation / `reservedOk`* — the machine invariant the export is read from, with its
  registry of disciplined regions; *[R26.s2]* — the review finding that no Stage 2 proof consumes `pteDiscAt`.  *Why it matters*: without it the `.pte` exemption is
  unconstrained in the published sentence — the largest class with no stated discipline (the proof does not need it; the reader does).  *Spec (FIRST)*: the privileged
  spec's Svadu makes the hardware A/D update atomic with respect to the PTE; Sail performs it as `read_pte_exclusive`/`write_pte_conditional`; RVWMO orders implicit
  page-table accesses only via `SFENCE.VMA`; Zifencei and the PMAs are silent.  *Options*.  **(P-a) RECOMMENDED — register the leaves at the seal, kernel table first**: the
  kernel table's leaf words become a region registered at `kptOn_seal` with the discipline "entries after the seal are hart-authored A/D variants of the sealed value" in
  `reservedOk` (the state interpretation holds half of each leaf; `kpt_exclWriteAU` the only writer), then the user tables per publication epoch.  FAITHFUL (= the plan's
  clause); ≈ 1–2k kernel + ≈ 1–2k user, serial lane, one cone; a W8 (f3-rest) part after (pte-ghost).  **(P-b) kernel table only**: (P-a)'s first half, user tables named
  uncovered.  WEAKER than the plan's clause; ≈ 1–2k.  **(P-c) drop the clause (as landed)**: `.pte` bytes exempt, named in the docstring, nothing more.  WEAKER
  (documentation only); cost 0.  Recommended: (P-a) staged ((P-b)'s increment first); (P-c) stands until it lands.
- **Q-DYNLKDISC — OPEN, provisionally (L-b) as landed by S4; recommended (L-a) (rev 46; raised by the S4 worker, F-DYNLKDISC).  The export's lock-word discipline covers
  statically allocated locks only; pipe locks are exempt and uncovered.**  *Plain language.*  Lock words (`lk->locked`, `lk->cpu`) are read racily by design (spinning,
  `holding`), so the export exempts them from chains and states their own discipline `lockWordDiscAt` (written only by the acquiring/releasing holder, in alternation).
  For locks at fixed addresses that is read off the machine-state registry.  A pipe's lock lives in a page `pipealloc` gets from `kalloc` and dies at `pipeclose`'s
  `kfree`; its discipline is only an Iris lock invariant (`Lock.lkDynRegW`) and the registry is static, so S4 exported static locks only and left live pipe-lock words
  exempt with no stated discipline.  *Tiny example*: hart 1 holds pipe `pi`'s lock; hart 2 calls `acquire(&pi->lock)`, whose `holding` check reads `pi->lock.cpu`
  racily; the export says nothing about which values that read can see.  *Definitions*: *`lockWordDiscAt`* — the export's lock-word clause; *windowed `lockRegionOk`* —
  [R36.3]'s per-lock discipline over its lifetime (birth at `lock_pay_born` → reclaim at `kfree`); *registry / `rsvExact`* — the static list of disciplined regions;
  *C1/C2* — W11's certificates for racy lock-layer reads, which take `lockWordDiscAt` as precondition.  *Why it matters*: beyond the sentence, W11's lock-layer arm
  (`lkCpu_read_not_mine`) needs the discipline for EVERY lock it certifies, pipe locks included — under (L-b) W11 carries a named premise for them.  *Spec (FIRST)*:
  RVWMO/riscv.cat/Sail are silent on lock disciplines (custody is not an ISA notion); the AMO/LR-SC semantics of the lock word are unchanged by either option;
  Zifencei/PMAs silent.  *Options*.  **(L-a) RECOMMENDED — register pipe locks at birth**: a dynamic registry entry created at `lock_pay_born`, retired at the `kfree`
  reclaim, with the windowed `lockRegionOk` in `reservedOk`.  FAITHFUL (= the plan's clause); ≈ 0.8–1.5k (`Reserved`, `Resources`, `WpLock`, `PipeBirth`, the reclaim);
  a W8 (f3-rest) part; unblocks W11's pipe-lock C1/C2.  **(L-b) static locks only (as landed)**: WEAKER than the plan's clause (= β′); cost 0; W11 carries a named
  premise for pipe locks.  Recommended: (L-a).
- **G1's E1′ reading of `gzFetch` (Z2) — INFORMED, no menu (rev 46).**  Assessment: the plan's CARRIED-OVER reading, not a new assumption — R1 (a) of §B(4)(iii)
  ("anchor sources to EVERY po-later memory access (E1′, stronger but gmo-true (H3))", recommended since rev 10), G0 carry-over (4) (§C W5d-G: "state (Z2) as … or adopt
  E1′ (R1 (a)) — list the chosen reading in §B(11)"), the third set's size line and Q-BATCH-3's option (1) ("mitigated by R1 (a) E1′"), which [OWN.56] approved; G1
  implemented exactly that (`GraphFetchSpike.lean:311-312`).  What it strengthens: (H3) — own STORES after the fetched instruction are gmo-after the fetch's source — to
  (H3′), own LOADS too.  Spec: RVWMO has no fetch model; Zifencei is silent on fetch vs later data accesses; Sail fetches before executing, per hart sequentially
  (`Step.lean:335`); PMAs silent — STRONGER than the spec text, true of Sail's per-hart order and in-order-fetch hardware; now LISTED in §B(11) as (H3′) inside the RULED
  fetch model [OWN.6].  The owner may re-open it; the alternative R1 (b) (keep (H3), cut hulls only after a memory event) needs an XL re-check of `t2linAux`'s cut
  selection.
- **Q-F2-PTE-WINDOW — RULED (c) [OWN.57] (14:18 2026-10-13, rev 46: the ghost freed-page set — the window is CLOSED by W8 (pte-ghost), §C top; the owner first asked whether the window is an xv6 BUG — answered NO: no hart walks the dying table, reuse goes through `kalloc`'s lock; it is an artifact of reading page-table-ness off memory) — the briefing below is the record; was OPEN, provisionally (a) (rev 44; raised by the W8 (f2-ctx) worker, `../weak-orch/parked/PROGRESS-W8f2.md` "Precision note", merged with
  S3-b 12:13 2026-10-13; non-blocking — RELAUNCH 5 proceeds under (a), only the export's `.pte` docstring text depends on the ruling; **bound CORRECTED rev 45
  [R41.1] — the window covers EVERY page-table page of the dying table, not the root alone, and is a window, not a page count**).  The (A′) page-table exemption
  keeps each freed page-table page exempt for a few instructions.**  *Plain language.*  The published access discipline (W8's export, the (r2) root) says every
  racy read of a RAM byte is CHAINED to its writer by a release/acquire path — EXCEPT page-table bytes, because the hardware may update a PTE's A/D bits speculatively,
  ordered by nothing (that is why [OWN.39] put PTE bytes under their own arm).  S3 had to say WHICH bytes are page-table bytes without a ghost ledger: (A′) reads it off
  memory — a byte is a PTE byte at time `t` if a Sv39 walk, started from a REGISTERED ROOT WORD as it stood at `t` (`kernel_pagetable`, or any `proc[i].pagetable`),
  reaches its page (root → level-1 → level-0, following pointer entries only).  xv6 frees a dying process's page table BOTTOM-UP and frees each page BEFORE clearing the
  one pointer that names it: `freewalk` (`kernel/vm.c:265-280`) does `freewalk(child); pagetable[i] = 0` for every pointer entry and `kfree(pagetable)` LAST, so a
  level-0 page is `kfree`d before its level-1 slot is cleared, a level-1 page before its root slot is cleared; and `freeproc` (`proc.c:156-163`) `kfree`s the root
  (via `proc_freepagetable` → `uvmfree` → `freewalk`) BEFORE `p->pagetable = 0` (image: `jal proc_freepagetable` `0x80001b2c`, `sd zero,80(s1)` `0x80001b30`).  In
  each such window a still-stored pointer names a page on the free list — from that page's `kfree` `release(&kmem.lock)` (`kalloc.c:62`: the page is allocatable) to
  the clear of its pointer: a few instructions and two returns for an interior page, four returns for the root (`kfree` → `freewalk` → `uvmfree` → `proc_freepagetable`
  → `freeproc`; fewer with tail calls) [R41.s4].  Leaf DATA pages have no window (`uvmunmap` frees them, but leaves have RWX ≠ 0 and the walk does not follow them).
  *Tiny example*: hart 1 runs `freeproc(p)` under `p->lock`: `freewalk` `kfree`s p's level-0 page `L` (filled with `0x01` bytes, `kalloc.c:55`) and is about to clear
  the level-1 slot naming it.  Hart 2's `kalloc()` returns `L` (filled with `0x05`, `:80`) and, say, `pipealloc` writes pipe fields into it.  Hart 3 reads one of those
  bytes.  Hart 1 then executes `pagetable[i] = 0`.  Under (A′) hart 3's read, if it happens before hart 1's clear, is a read of a "PTE byte" — the export demands NO
  chain for it; one instruction later the same read would need one.  The same shape recurs for p's level-1 pages and the root `R` (cleared by `sd zero,80(s1)`).  The
  junk fills themselves lead nowhere: `0x0101…` is a V-only pointer entry whose target is `0x4040404040000` (`ptPtrTo`, `ChainDefs.lean:651-653`), outside RAM
  (`0x80000000`–`0x88000000`); `0x0505…` has RWX = `0b010`, so it is not a pointer and the walk stops.  But if the NEW owner writes a V-only pointer-shaped word
  (`v &&& 0xF = 1`) whose PPN lies in RAM before the clear — user-controlled bytes in a pipe buffer or a `kalloc`ed user page can be anything — the walk reaches an
  UNRELATED RAM page during the window, so "exactly the freed page's 4 KiB" is NOT a theorem; the honest bound is the WINDOW: every page-table page of the dying table
  (≈ 5 for a small process: root, ≈ 2 level-1, ≈ 2 level-0 — the user region and the TRAMPOLINE/TRAPFRAME region), each from its `kfree` to the clear of its pointer, plus
  whatever a pointer-shaped word written there names.  *Definitions*: *export / `xv6AccessDisc`* — the discipline theorem's conclusion (`Xv6/AccessDiscipline.lean:115`,
  four of six conjuncts after S4); *`chainOkAt`* — its chain conjunct, quantified over bytes whose custody is NOT `.pte`; *`custAt`/`Cust.pte`* — the per-byte custody map
  and its page-table class (`:53`, `:89`); *(A′)* — the custody read off memory via *`ptByteAt`* (`MachCSL/ChainDefs.lean:670`; `ptPageAt :660` = root, level-1, level-0)
  from the *registry* entries `RsvKind.roots` (`Xv6/KernelRsv.lean:70-72`); *root word* — `kernel_pagetable` or `proc[i].pagetable`; *page-table page* — the root or an
  interior (level-1/level-0) page of a table; *window* — the instructions between a page-table page's `kfree` and the clear of the pointer naming it; *WEAKER* — the
  theorem claims less (sound), never something false.  *Spec (FIRST).*  RVWMO/riscv.cat/Sail: SILENT — custody is not an ISA notion; the one relevant ISA fact (Sv39: a
  hardware walker reads PTEs reachable from `satp` and may set A/D speculatively) does not touch the windows — the dying process runs on NO hart at `freeproc` (ZOMBIE in
  `wait`, or a never-scheduled child on `fork`'s failure path, `proc.c:272`; the freeing hart is on `kernel_pagetable`), so no hardware walk reads the freed pages;
  `exec` installs the new table in `p->pagetable` BEFORE `proc_freepagetable(oldpagetable)` (`exec.c:134-138`), and `uvmdealloc` frees leaves only — NO window there;
  Zifencei/PMAs silent.  Every option is custody-spec text, FAITHFUL to the ISA; the marks below compare the EXPORT to the intended statement "bytes in use as PTEs".
  *Why it matters.*  A reader checking "is every racy read chained?" finds named windows the theorem skips; it is honest (stated, bounded in time, sound) but a hole in
  the published sentence, and the user-table half of the exemption is never NEEDED by the proof (user PTE reads are owned context loads, paid by keys) — it exists only
  to make the export's `.pte` arm cover both tables [OWN.39].  *Options.*  **(a) RECOMMENDED — accept as a NAMED weakening**: S4's `.pte` arm is `ptByteAt` as built;
  its docstring, `pteDiscAt` and §A's export sentence state the windows ("… including a page-table page already freed by `freewalk`/`proc_freepagetable` until the
  pointer naming it is cleared — its parent's slot, or `freeproc`'s `p->pagetable = 0`, `0x80001b30`") with the junk-fill and pointer-shaped-word caveats above.
  Export WEAKER than intended by exactly those windows; cost 0 (text; RELAUNCH 5's addendum carries the sentence); unblocks S3 wiring/S4 NOW; risk: a reviewer reads it
  as a loophole — mitigated by the bound (the dying table's ≈ 5 pages, each for a few same-hart instructions, no hardware walk, no false claim).  **(b″) kernel reorder,
  clear-before-free**: `freeproc` saves the root in a local, stores `p->pagetable = 0`, then frees (one statement moved; the `verified` branch's named diff D12 grows by
  one line).  Because `ptRootAt :664` needs the root word to HOLD the root, the whole table is unreachable for the entire `freewalk` — this closes the INTERIOR windows
  too, not only the root's (which strengthens the case for its sizing pass [R41.1]).  Export EQUAL to the intended one (no registered word ever names a free page);
  FAITHFUL.  Cost: re-dump `Xv6/KernelImage.lean` and re-prove `freeproc`'s TsoMem Iris step (`Xv6/ProofFreeproc`/`LinkFreeproc`, 44 slots; M) — S overall IF gcc keeps
  the code size (same instructions reordered; every pc after `0x80001b2c` unchanged), XL if any pc shifts (literal pcs throughout `Xv6/`/`Weak/`); a read-only SIZING
  PASS (compile, diff the disassembly) decides, S.  Not before S4; a separate serial item.  **(b) σ-readable tightening in S4 ("freed-page receipt")**: exempt via a
  pointer only while the named page's as-of-`t` first word is not `kfree`'s fill — WEAKER than (b″) (a sub-window remains after `kalloc`'s refill, and it would have to
  be applied at every level) and brittle (keyed on fill constants); NOT recommended.  **(c) a ghost freed-page set**: EQUAL, but needs a second bridge ghost ⊆ σ-custody
  (W8-design (1): no ghost ledger) and must shrink at `freewalk`; L.  Recommended: (a) now; (b″)'s sizing pass as an optional S item if the owner wants the windows
  gone before publication.
- **Q-BATCH-3 — RULED (1) [OWN.56] (14:11 2026-10-13, rev 46; all three launched) — was OPEN (rev 44; rewritten in the owner format rev 45 [R41.5]): approval of the THIRD Stage 2 batch — W5d-G G1–G5 (G1 first) ∥ W9a ∥ W13 (W)
  [FabInd-S → (K-cat) → (W)]** (§C top; three graph workers beside the running W8 (f2-ctx) RELAUNCH 5; [OWN.55] covered the second batch only).  *Plain language.*
  Three more proof items on the GRAPH side (the RVWMO graph model of the kernel's runs — `Weak/`), run in parallel beside the serial MachCSL lane: **W5d-G** makes
  instruction FETCH a first-class part of the graph model (Zifencei: a hart's fetch of a text byte is ordered against stores to it only by `fence.i`), so user-text
  changes are covered — five increments G1–G5, and the ONE item of the three that rebuilds and RE-AUDITS the registered cone on every increment (its files are in
  every registered root's import closure [R41.2]); **W9a** connects the checker's pin certificates (the per-site evidence the checker emits) to the cat-model segments
  (`segPinC`) — a new file, nobody else's; **W13 (W)** states the real device-ACTIVE xv6 conformance bundle `xv6ConfS` (the trusted text saying what a conforming xv6
  run's graph looks like, including the disk) and builds the first witness with a non-empty fabric (hart 0 to its first UART store), after two S preparatory lemmas
  (FabInd-S drops an unused premise of the hull-transport lemma; (K-cat) proves the cat-model twin of (K)'s "I/O segment pinned" lemma); (W) makes ONE S rebase when G1
  lands.  *Definitions*: *W8 (f2-ctx) RELAUNCH 5* — the running serial-lane item wiring the access discipline (MachCSL/Xv6 files; disjoint from all three); *FabInd-S*,
  *(K-cat)* — the S items above, the same worker's first two increments; *registered cone* — the 13 `audit.sh --weak` roots and their 493-module import closure;
  *re-audit* — `audit.sh --weak --build`, baseline unchanged; *W13 (R)*, *W14* — the fourth set: the re-thread of the constant-fabric chain onto `gfexecConfIO`, and the
  device-active DISK witness.  *Why it matters.*  The fourth set — W13 (R) and W14, the disk witness that makes the published theorem NON-VACUOUS on I/O — waits on W5d-G
  and (W); every item is a planned proof item (no memory-model choice — the spec-first rule does not apply; FabInd-S and (K-cat) are proof devices with no trusted text;
  (W)'s one new named hypothesis `usedElemGateOk` is device-model text EQUAL to MachCSL's disk step [R41.4]).  *Options.*  **(1) RECOMMENDED — approve all three**:
  cost three graph workers + the serial lane = four under [OWN.51]; unblocks W13 (R)/W14 soonest; risks: W5d-G's XL hull-closure risk R1 (mitigated by R1 (a) E1′) and
  its full-cone rebuilds (minutes per increment).  **(2) approve W9a + the (W) chain (FabInd-S → (K-cat) → (W)) now, W5d-G after** [R41.s7]: the safest files (new or
  own, OUT of the roots' closure — no re-audit), three workers in all; defers the fetch model, so W14/W13 (R) wait one round and (W) needs no rebase.  **(3) approve
  W9a + FabInd-S only**: two S/M-L items, minimal usage; defers (W)'s bundle and the fetch model — the fourth set slips two rounds.  **(4) defer all**: cost — the fourth
  set slips a round; the serial lane alone runs.
- **Q-L-R3 — RULED (a) [OWN.53] (10:22 2026-10-13, rev 42; raised by the W13 (L) worker, `../weak-orch/parked/PROGRESS-W13L.md`; LANDS as W13
  (R3′), §C top).  The residue's fabric arm orders I/O pairs only; the disk's fabric-moving RAM stores are fabric members too.**  *Plain language.*
  The published model orders device traffic by a short list of "residue" rules (R1)–(R3) beyond what the ISA gives; (R3) says two MMIO events the
  fabric saw in some order are in that order in memory order.  The fabric list `gfDev` ALSO contains the disk's RAM stores that move the device
  (the used-index/status writes, 3–4 per request, [OWN.31][OWN.43]).  The landed (R3) says nothing about such a RAM store versus a hart's MMIO store,
  so W13 (L)'s trace theorem had to ASSUME it (`gfDevGmo`).  *Tiny example*: hart 0 stores NOTIFY to the virtio MMIO register (an I/O event, fabric
  member 7); the disk row later stores `used->idx` to RAM (a `DWriteDev`, member 8).  The fabric saw 7 then 8; under the landed text gmo may put 8
  before 7; under (a) gmo has 7 < 8.  *Definitions*: *fabric* — the device-side state the MMIO/DMA traffic drives, with its global trace `fab`;
  *`gfDev`* — the events that touch the fabric, in fabric order (`WeakRvwmoFab.lean:799`, membership `:857`); *(R3)* — `GraphFabResidue.lean:84`;
  *`ioResidueGmo`* — the trusted item "every residue pair is gmo-ordered" (`:101`); *`gfDevGmo`/`gfDevWIo`* — W13 (L)'s premises (fabric order ⊆
  gmo; every member is a write or an I/O event; `WeakRvwmoLin2.lean:1219-1222`); *gmo* — the model's global memory order; *anchor* — an event the
  (L) trace places at its gmo rank (writes, I/O events, disk-row reads; `gisAnc :1141`).  *Spec (FIRST).*  RVWMO, riscv.cat and the Sail model have
  NO device events; Zifencei is fetch-only; the PMAs order I/O accesses among themselves (channels), never a RAM store against MMIO; virtio 1.x is
  silent — every option is beyond the spec (device-model text, D45/D49 class).  *Why it matters.*  An undischarged premise on the published path
  reads as a hole; a widened trusted sentence reads as a named platform assumption the reader can check against MachCSL, where it is TRUE by
  construction (one fabric order).  *Options.*  **(a) RULED — widen (R3) to all members**: `gfBefore GF x y → gmoLt x y` for ANY members.
  STRONGER than the ISA (adds order the ISA never states), EQUAL to MachCSL and to Q-GFDEV-delta (a)'s plan text; cost S (W13 (R3′)); unblocks
  `gfDevGmo` as a theorem and uniform `racyDIO` arms for (K); risk none beyond the sentence — **but it does NOT give `gfDevWIo`**: that premise is
  about WHAT the members are, not their order; (R3′) replaces it by `gfDevAnc` (members ⊆ anchors) with a discharge lemma from the bundle's
  membership clause (§C top) — the ruling's "discharges `gfDevGmo`/`gfDevWIo`" is read this way.  **[R40.1] (α), rev 44: `gfDevWIo` itself STAYS the named premise — `gfDevAnc` was dropped BEFORE launch (a `DRead` is never a fabric member on this program; `devOrderOfPtraceExtIO` goes through the `gisWIo` arm); the ruling's reach is unchanged; LANDED (`Lin2.lean:1237/:1284`).**  **(b) keep `gfDevGmo` as a second named trusted
  item** — same strength, two sentences where one suffices.  **(c) leave it a premise** — WEAKER (an unproved premise on the published path).
  Recorded as RULED; §A(6) names the change.  **(a) as refined by [R39.3] (rev 43; a refinement of the RULED option, not a new question — owner
  informed under the non-blocking rule)**: the fabric arm ranges over the `gfDev` members that HAVE a memory-order position (`gmem` — writes, reads,
  I/O events), EQUAL in strength on every event the (L) trace places (anchors are `gmem`); `gfDevWIo` (not rev 43's `gfDevAnc` — [R40.1] (α)) is the NAMED premise of `fconfTraceRealizeIO`
  until W13 (W)/W14 discharge it from the disk program's shape.  *Why*: the disk row's one `DFence` is emitted as the row event `LFence true true
  true true` (`WeakEvInst.lean:511`), and a silent `DWriteDev` skip/abort (`:525-530`) can fold its `pdevEv`-true contact (`pdevEv :604`) into that
  block, so `gfDev` may hold a FENCE label; an unrestricted arm would make the TRUSTED `ioResidueGmo` UNSATISFIABLE there (`gmoLt :137` is over `gxGmo`
  members) — the discharge lemma `gfDevAncOfConf` rev 42 expected has this counter-model.  FAITHFUL/STRONGER/EQUAL marks unchanged from (a).
- **D35-rule7 — RULED (a) [OWN.54] (10:22 2026-10-13, rev 42; raised by the W12 worker, `../weak-orch/parked/PROGRESS-W12.md`; LANDS as D35-fix,
  §C top).  The tree's RCsc is narrower than riscv.cat's, so a floor-kit premise had to fill the gap.**  *Plain language.*  RISC-V lets an atomic
  instruction carry an acquire bit (`.aq`), a release bit (`.rl`) or both.  riscv.cat's rule 7 orders ANY two such annotated atomics of one hart in
  program order (herd `riscv-defs.cat`: `let RCsc = (Acq|Rel|AcqRel) & (EX|X)`, `r7 = [RCsc];po;[RCsc]`).  The tree's transcription calls a label
  RCsc only with BOTH bits (`lbRcsc := lbAq && lbRl`, `AxGraphCat.lean:143`), which only a fused RMW can have, so the tree's model omits riscv.cat's
  `[W.rl];po;[R.aq]` and `[W.rl];po;[W.rl]` orderings; the W12b floor kit needs the first and ASSUMED it (`grelAcqGmoC`, `CatFloor.lean:60`).  *Tiny
  example*: one hart runs `amoswap.w.rl zero,(lock)` (a release store) then `amoswap.w.aq t0,(other)` (an acquire load) to a different address.
  riscv.cat: the store is gmo-before the load (rule 7, both RCsc).  The tree's cat model: unordered (neither has both bits; rules 5/6 do not
  apply) — the model admits a reordering riscv.cat forbids.  xv6's kernel never emits a `.rl` (release is `fence rw,w; sw`; its only annotated atomic
  is `amoswap.w.aq`), so NO kernel graph changes; user code may.  *Definitions*: *RCsc/RCpc* — release-consistency flavours: RCsc orders a release
  before a later acquire, RCpc does not; the ISA says RISC-V's aq/rl are RCsc (RCpc only under Ztso); *`grcsc`/`gppoCat6`* — the tree's rule-7 arm
  and six-arm ppo (`AxGraphCat.lean:163-170`); *`grelAcq`* — RVWMO⁻'s rule-7 arm (`WeakRvwmoGraph.lean:227`), exactly `[W.rl];po;[R.aq]`;
  *`rvwmoCatConsistentT`* — the published model premise of the registered LB roots (`AxSpinT2b.lean:255`); *re-audit* — `audit.sh --weak --build`
  against `baseline-weak.json`.  *Spec (FIRST).*  riscv.cat as quoted; the ISA prose (RVWMO "Memory Model Primitives": aq/rl on LR/SC/AMO are RCsc
  annotations); Sail: silent (single-hart operational; annotations are access-kind bits); Zifencei/PMAs: silent.  *Why it matters.*  "The published
  model is riscv.cat" must be literally true; today it is WEAKER by one rule's instances (sound for the theorem, but a named departure) and the kit
  carries a premise an expert would question.  *Options.*  **(a) RULED — correct `lbRcsc` to `lbAq || lbRl`**: FAITHFUL (EQUAL to riscv.cat); the
  registered roots' premise STRENGTHENS (their statements cover exactly riscv.cat's graphs — fewer than before; text unchanged, meaning changes →
  re-audit); RVWMO⁻'s arm widened in step so the RVWMO⁻ ⇒ cat inclusion (`minusImpliesCat`) survives; `grelAcqGmoC` dropped; cost M ≈ 0.3–0.6k /
  ≈ 14 files (§C top D35-fix); risk: a litmus or certificate verdict flipping — impossible on kernel graphs (no `W.rl`), checked by build.  **(b)
  keep the premise** — FAITHFUL as a statement (riscv.cat implies it) but the model text stays weaker than riscv.cat and the kit carries an extra
  hypothesis; cost 0.  Recorded as RULED; §A(3)/(6) name the change; D35 (a) [OWN.13]'s "first check the decoder emits aq/rl only for atomics" is
  DONE here (hart side: `aq := akSync` of LR/AMO kinds only, `WeakEvInst.lean:336`; the disk row's `DRead avail idx (aq)`, `VirtioProg.lean:74`, is
  the one non-atomic `aq`, on the model-artifact row where rule 5 already orders it).
- **Q-FDEP — RULED (A1) [OWN.52] (10:22 2026-10-13, rev 42: `gtdepsWf` admits I/O endpoints (option A) AND rule 12 applies from I/O-load
  sources — `gppoCatT` over `gtAdFull`; W13 (F-dep) relaunches under (A1) directly, no (A2) interim; the `catADOfCatT` one-liner is (F-dep)'s own
  since W12 landed it in `Weak/CatLin.lean:54` (and the spike's `CatOfMinusSpike.lean:37`).  Rev 41: OPEN, provisionally (A2), (A1)
  recommended [R38.4] (raised by R38 from the W13 (F-dep) worker's STOP,
  `PROGRESS-W13Fdep.md`).  Rule 12 from an I/O-load source: (A1) faithful vs (A2) weaker; the graph-side fix (A) itself is a plan decision
  [R38.1], not a question.**  *Plain language.*  xv6 drivers read device registers (MMIO loads) and then do things with the value: branch on
  it, store it to RAM, store it to another device register.  The RISC-V memory model says a load that FEEDS a later store (by address, data or a
  branch) is ordered before that store — and the appendix says this still holds when the load or the store is to a device.  The plan already
  decided (D50 (b)) to record those edges.  But the published model's well-formedness clause currently says "every recorded edge starts at a RAM
  load and (for data/control edges) ends at a RAM store", so a graph with a device-sourced or device-targeted edge is REJECTED — not "the
  ordering is false" but "no graph of this program conforms".  Then the theorem's premise is false for every xv6 run that prints a character,
  and the theorem says nothing (it is VACUOUS).  [R38.1] fixes that by admitting device endpoints (option A, §C W13 (F-dep) (0)).  One corner
  remains to rule: riscv.cat's rule 12 (`[R];(addr|data);[W];rfi;[R]`): "a load `a`, a store `m` that depends on `a`, and a later load `b` of the
  SAME hart that reads `m`'s value (store-to-load forwarding) — then `a` is ordered before `b`".  Should that hold when `a` is a DEVICE load?
  *Tiny example* (one hart, the UART echo path): L1 = `lbu` RHR (device read, the typed key `c`); S = `sb c → cons.buf[i]` (RAM store,
  data-dependent on L1); L2 = a later `lb cons.buf[i]` by the same hart, satisfied by forwarding from S.  Rule 12 says gmo: L1 < L2.  Under (A1)
  the model asserts it; under (A2) it does not (L2 may sit anywhere gmo-after S's own constraints).  No hart ordering, lock or proof in the plan
  currently needs L1 < L2 (census [W13c]: no xv6 pin uses an MMIO-sourced dependency), so the choice is about the FAITHFULNESS of the published
  model text, not about closing a proof.  *Definitions.*  *ppo* — preserved program order, the same-hart orderings the ISA guarantees; *gmo* —
  the global memory order the model totalises; *tagged graph `GT`* — the published graph with its dependency list `gtDeps`, each edge carrying a
  tag (addr/data/ctrl/…); *`gtdepsWf`* — the model's well-formedness clause saying what shape an edge may have; *`gtAd`* — the addr/data edges
  the model's rule 12 ranges over (after [R38.1]: RAM-sourced only); *`rowDepsT`* — the edges the emission (the instruction-level tagger
  `dstepT`) RECORDS for a row; *`gdexecQconfT`/`xv6ConfS`* — the conformance text saying "the recorded edges are in `gtDeps`"; *vacuous* — the
  premise is never satisfiable, so the theorem is true but says nothing.  *Spec (FIRST).*  riscv.cat `r12 = [R];(addr|data);[W];rfi;[R]` over
  ALL reads (herd has no I/O class); RVWMO rule 12 prose ("b is a load, and there exists some store m between a and b in program order such that
  m has an address or data dependency on a, and b returns a value written by m"); appendix (c1): ppo applies when one access is I/O
  (non-normative, "generally applies" — named by D50); Sail (`MachCSL/Dev/Fabric.lean:125-126`: MMIO is an ordinary `mem_read`/`mem_write`),
  Zifencei (fetch only) and the PMAs (channel ordering among I/O accesses only): SILENT on dependencies.  *Why it matters.*  An xv6 expert
  reading the model text will ask whether it is riscv.cat; (A2) is a NAMED departure (one rule instance), (A1) is not.  *Options.*
  **(A1) FAITHFUL — recommended.**  `gppoCatT` ranges over the addr/data edges into RAM writes from ANY read (`gtAdFull`); the projections used
  by the proof chain (`forget`/`gtAd`) keep RAM sources.  Concretely: one new list function, two one-line monotonicity proofs (`catTAd` in
  `AxDeps`; `catADOfCatT` in W12's `CatOfMinusSpike.lean`), `AxScCat.scPpo`'s rule-12 case re-cased.  In practice: the model excludes exactly the
  executions riscv.cat excludes.  Cost S (after W12's statement commit; one line in W12's file, by W12 or by (F-dep) after rebase).  Unblocks: the
  §A(3) sentence "ppo applies as riscv.cat is written" stays literally true.  Risk: the "reuse hinge" `gppoCatT = gppoCat (gtAdGd GT)`
  (`AxDeps.lean:195`) is no longer definitional — ~94 `AxSpin*` files use `gtAd`/`gtAdGd` but none uses `gppoCatT` directly (only `AxScCat`), so
  the blast radius is two files; the worker verifies by build.  **(A2) WEAKER (sound) — the PROVISIONAL shape until ruled.**  `gppoCatT`
  unchanged over the source-filtered `gtAd`; rule 12 from a device load is NOT asserted.  Concretely: nothing beyond [R38.1]; §A(3) names "rule 12
  omitted for I/O-load sources".  In practice: the model admits a few executions riscv.cat forbids (the theorem covers them too — safe).  Cost 0;
  no W12 contact.  Risk: a named departure in the published model; a later proof wanting L1 < L2 has to add it then.  **(B) FAITHFUL, rejected on
  cost** — also loosen the UNTAGGED `gdepsWf` (`WeakRvwmoGraph.lean:629`) and give `dstep` the arms: changes the meaning of
  `rvwmoMinusDepsConsistent`/`rvwmoCatConsistent` (hundreds of `Ax*` uses, W12's `rvwmoCoreD`, the G3 kill files) while W12 is running; L–XL.
  **(C) WEAKER, rejected** — emission only; the conformance text admits RAM-endpoint `rowDepsT` edges only = D50 (a) in effect, contrary to
  [OWN.17].  Non-blocking: (F-dep) proceeds under (A2); the ruling flips it by the (0e) edits.
- **Q-F2-PIPEHOP-2 — RULED (a′-r) [OWN.49] (05:18 2026-10-13, rev 41: the RULED `f->pipe` window made provable by a persistent entry receipt —
  MachCSL ghost `entryAt` over append-only histories, `PipeBirth` passes the slot's entry to the lock handle, `isLk = static ∨ pipeLockAt`,
  user-forged lock shapes excluded σ-readably; inside W8 (f2-ctx) RELAUNCH 2; rev 40 OPEN, provisionally (a″+shape)) [R36.3] (raised by R36 from the W8 (f2-ctx) worker's deviation
  D1/D2, `PROGRESS-W8f2.md` finding F-A).  The MERGED registry (a″) versus the RULED (a′) [OWN.46]: which window may `chainOkAt`'s pipe hops
  use, and must the export exclude user-forged lock shapes by itself?**  *Spec (FIRST).*  RVWMO (PPO rules 4–7 and the load-value axiom): a
  store ordered by a FENCE or `.rl`, read by a load the reader orders behind it (`.aq`/FENCE), orders the writer's earlier accesses before the
  reader's later ones — AT ANY ADDRESS; the spec has no notion of "lock", "name" or "page owner".  The Sail model executes the AMO as
  `execute_AMO` (`model/Lean_RV64D/LeanRV64D/InstsEnd.lean:18663`) and the fence through `effective_fence_set` (`:18299-18313`); a plain `sb`
  and an `amoswap.w.aq` differ in width/atomicity/`aq`, NOT in what the byte history records (`MachCSL/TsoMem.lean:76-80 HEnt = ⟨t, tid, v⟩`).
  Zifencei silent.  PMAs: pipe pages and user pages are both `MainMemory` (`MachCSL/Platform.lean:240-254`).  So WHICH words are hops is a
  proof-partitioning question the spec is silent on: an option that RESTRICTS the chains the proof claims is FAITHFUL; one that removes bytes
  from the predicate is WEAKER.  *Plain language.*  The theorem's chain conjunct says "every cross-hart read of pipe data is reached by a chain
  of lock hand-offs".  The proof needs a rule for recognising, in the final memory trace alone, which words were pipe locks and when.  The
  MERGED rule reads the lock's own debug NAME field: a word is a pipe lock while the 8 bytes after it hold the address of the string `"pipe"`.
  The RULED rule reads the kernel's open-file table: a word is a pipe lock from the moment a file slot pointed at its pipe until the page was
  recycled.  *Example.*  Hart A: `acquire(&pi->lock); pi->data[0] = 'x'; release(&pi->lock)`.  Hart B: `acquire(&pi->lock); c = pi->data[0]` —
  both rules accept this hop (real).  Counter-example for the merged rule: hart A `release(&pi->lock)` (the pipe's last use); the closing thread
  migrates to hart C, which runs `kfree(pi)` (`kernel/pipe.c:70-71`): `memset(pa, 1, PGSIZE)` (`kalloc.c:55`) writes byte value 1 to the lock
  word FIRST (a byte loop low-to-high, `string.c:8-10`; the lock is at `+0`, `lk->name` at `+8`, `spinlock.h:2-7`) while the name field still
  reads `"pipe"` — the trace shows "0 by A over a held 1, then 1 by C" under a `"pipe"` name, the SAME shape as B's acquire; the merged rule
  calls it a hop, RVWMO does not (C's store is a plain `sb`; nothing orders C's later loads behind it).  A second one: a user program writes
  `1`, `0`, `1` as WORDS to its own page and `&"pipe"` eight bytes on — the merged rule calls it a hop; the ruled rule does not (no file slot ever
  pointed there).  A third, at BIRTH: `initlock` stores `lk->name` FIRST, then `lk->locked = 0` (`spinlock.c:16-17`), so the creator's zero sits
  above `kalloc`'s junk `5` bytes (`kalloc.c:80`) inside the window and reads as a "release from held".  *Definitions.*  `chainOkAt`/`syncPath`
  = the export's σ-readable chain conjunct (`Xv6/AccessDiscipline.lean`, S4); `syncHop` (`MachCSL/ChainDefs.lean:171`) = three adjacent entries
  of a lock byte's history (held, release `0`, acquire nonzero) — pure SHAPE; `isLk b a` (`:266`) = "`b` is a hop byte for an acquire at `a`";
  `nameLockAt` (`MachCSL/Reserved.lean:236`) = the merged name-word window; `pipeLockAt` = the ruled `f->pipe` slot-history window;
  `lockWordDiscAt` (`AccessDiscipline.lean:104`) = the custody conjunct "lock words are written only by the lock code", today over the WHOLE
  history (`lockRegionOk`, `Reserved.lean:108`); W11 = the Stage 2 item that consumes `chainOkAt` to prove robustness; "σ-readable" = decidable
  from the final memory trace without ghost state; "word-sized entry" = four entries at the same timestamp on `b..b+3` (what a 4-byte store
  pushes, `memGrow_writeBytes :156`; `memset` pushes one byte per timestamp).  *Why it matters.*  The published theorem's chain conjunct is only
  as strong as its hop rule: a rule that accepts shapes RVWMO does not order makes `chainOkAt` TRUE for the wrong reason, and W11 cannot pick
  the real chain out of an existential (`chainOkAt σ = ∀ racy read, ∃ chain` — W11's release-site pin identifies release STORES, it cannot
  select among the chains the export offers; rev 39's sentence saying otherwise is withdrawn).  A reviewer of the paper will ask exactly "what
  stops a user page from being a lock".  *Options.*  **(a″+shape) — the merged name window, hops restricted to WORD-sized entries**
  (RECOMMENDED now; adopted provisionally; [R36.3]): what changes — `syncHop` gains the word-shape clause (`wordEntAt` for the acquire, release
  and held entries), `lockWordDiscAt`'s dynamic arm is WINDOWED (from the `initlock` zero to the last word-sized entry before the name
  overwrite); FAITHFUL (restricts chains); kills the `kfree` and `initlock` shapes, NOT the user-forged word shape, which the export then leaves
  to W11 (≈ 0.3–0.5k there, from `custAt`/the page tables — marked there); cost S ≈ 0.1k now; unblocks S2b at once; risk: a paper caveat "hop
  words are name-tagged lock-shaped words" until (a′-r).  **(a′-r) — the RULED `f->pipe` window, made provable by a persistent entry receipt**:
  what changes — one MachCSL ghost `entryAt pa e` over the append-only histories, handed out by every store rule; `PipeBirth` passes the slot's
  entry to the lock handle; the hop request carries it; `isLk` = static ∨ `pipeLockAt` as RULED; FAITHFUL; excludes the user-forged shape
  σ-readably (file slots are kernel memory) — the RULED (a′) with the worker's objection F-A answered; cost S–M ≈ 0.2–0.4k MachCSL + the pipe
  files, one more cone rebuild; unblocks S4's clean statement; risk: the receipt ghost touches every store rule (the lane is serial anyway).
  **(a″-s) — accept (a″+shape) as the export's MEANING**: FAITHFUL, cheapest (0 beyond shape), WEAKER in documentation only (the conjunct says "a
  chain of name-tagged lock-shaped word hops exists"); risk: the paper caveat becomes permanent and W11 carries the user-page exclusion.
  **(c) exempt pipe bytes** — WEAKER, as in rev 38; not taken.  RECOMMENDATION: (a″+shape) NOW (RELAUNCH 2 S0 — done regardless of the ruling,
  it is sound under every option), (a′-r) as the NAMED S4 follow-up the owner rules on; the ruling is wanted before S4 fixes the export's text.
- **Q-F2-PIPEHOP — RULED (a′) = (a) as amended by [R35.1] [OWN.46] (23:25 2026-10-12, rev 39; rev 38 OPEN, provisionally (a); raised by the
  W8 (f2-ctx) worker, `PROGRESS-W8f2.md` finding 2; **MERGED as (a″) — a DEVIATION, provisional under Q-F2-PIPEHOP-2 above [R36.3]**). Which
  words may `chainOkAt`'s synchronisation chains hop through — in particular the PIPE locks, which are born at run time?**  *Spec (FIRST).*
  RVWMO has no notion of a "lock": a store ordered by a FENCE or a `.rl` annotation (PPO rules 4–7), read by a load the reader orders
  behind it (FENCE or `.aq`), extends the global memory order from writer to reader AT ANY ADDRESS; the Sail model executes the AMO as
  `execute_AMO` (`model/Lean_RV64D/LeanRV64D/InstsEnd.lean:18663`, `aq`/`rl` flags) and FENCE through `effective_fence_set` (`:18299-18313`);
  Zifencei silent; the PMAs put pipe structs (`kalloc`'d pages) in `MainMemory` (`MachCSL/Platform.lean:240-254`) like the static locks.  So
  WHICH words count as hops is a proof-partitioning question the spec is silent on: an option that only RESTRICTS the chains the proof
  claims is FAITHFUL; one that removes bytes from the predicate is WEAKER.  *Plain language.*  The export's chain conjunct `chainOkAt σ`
  says: every racy read of a byte another hart wrote is reached by a chain of release→acquire hops through lock words.  The merged S1 layer
  finds a hop in a lock word's byte history (an acquire AMO's entry right above a release entry).  For data under a STATIC lock (`kmem.lock`,
  …) the hop word is in the registry fixed at power-on.  Pipe data (`pi->data`, `pi->nread`, …) is protected by `pi->lock`, a lock inside a
  `kalloc`'d page that exists only after `pipealloc` — unless the proof knows that word is a lock, cross-hart pipe reads have NO chain and
  `chainOkAt` is FALSE on every run that uses a pipe (the export becomes unprovable, not weaker).  *Example.*  Hart A: `acquire(&pi->lock);
  pi->data[0] = 'x'; release(&pi->lock)`.  Hart B: `acquire(&pi->lock); c = pi->data[0]`.  RVWMO: B's `.aq` AMO reads A's fenced release
  store, so B's load sees `'x'` — ordered.  `chainOkAt` with a static-only registry: B's read has no hop word → a bare race → the predicate
  fails.  *Definitions.*  `chainOkAt`/`syncPath` (`Xv6/AccessDiscipline.lean`, S4, to come) = the σ-readable chain conjunct and its hop
  relation over byte histories (machine side: `ChainDefs.syncHop :129`/`hopChain`); the STATIC registry = the era ghost `rsvName` (= `rsvStatic`, pinned by `rsvExact`,
  `Resources.lean:1196`: static locks, `cpus[h]`, now `started`); the HOP registry `ChainEnv.isLk` (`ChainDefs.lean:266`, time-indexed) is derived from
  it and, under (a′), from `pipeLockAt` [R35.1] — as MERGED, from `nameLockAt names` with `KernelRsv.names = [pipeLockNameStr]`, which MUST be
  `KS.«pipe»` (`KernelImage.lean:18837`, `= 0x800075c0`): the hand-computed `KA.«pipealloc» + 0x48 + 0x3000 + 222` (`Xv6/KernelRsv.lean:104`) is
  `KernelStr.«digits» = 0x80007730`, the `addi` immediate being −146 (`KernelImage.lean:13328-13329`) — RELAUNCH 2 S0 [R36.2]; `custAt σ a t` = byte `a`'s custody class at `t`; the mint store
  `wp_s_sw_mint`/`wp_s_sd_mint` (`WpSmodeMint.lean:127/:40`) = the rule that turns a fresh word into a lock (`initlock` on a `kalloc`'d page);
  `ftable` = xv6's open-file table, from which every live pipe is reachable; W11 = the roadmap item pinning release sites per lock; σ =
  `MState`, whose memory is a per-byte history of STORES (loads are not recorded).  *Why it matters.*  Pipes are the only xv6 data the
  target's fork path [OWN.3] shares between harts under a run-time lock; a chain predicate false the moment a pipe is used is not credible,
  and an exemption would leave pipe data outside the discipline the paper claims.  *Second example [R35.s6] — the one that falsified rev 38's
  (a).*  Hart A `release(&pi->lock)` at `r` (its last use); hart B runs the LAST `fileclose`: `f->type = FD_NONE; release(&ftable.lock);
  pipeclose(ff.pipe, …)` (`SpecFileclose.lean:4-12`) — B's `acquire(&pi->lock)` hops on `r` and reads `pi->readopen`/`pi->writeopen`/`pi->nread`
  while NO `ftable` slot points at `pi`; an "as of `t`" reachability predicate says the hop word is not a lock, so `chainOkAt` fails on every run
  that closes a pipe from a hart other than its last releaser.  *Options.*  **(a′) RULED [OWN.46] — a TIME-INDEXED σ-readable live window
  [R35.1]** (rev 38's (a) "reachable from `ftable` as of `t`, registered at the mint store" was NOT implementable: FALSE at the mint store —
  `initlock` precedes `(*f0)->pipe = pi`, `SpecPipealloc.lean:10-11` — and at the last `pipeclose` (the second example); `rsvName` cannot be
  "registered" mid-run (`rsvExact`); and the merged `ChainEnv.isLk` is UN-TIMED and only GROWS (`ext :231-233`, `hopChain_mono :147-152`)
  while a pipe lock DIES (`wp_s_sw_zero_release_cancel`, `WpLock.lean:2491`; `kfree`'s junk fill, `SpecKfree.lean:130`) — a monotone "once a
  lock, always a hop byte" would let `syncHop :129-131` (pure history SHAPE) fire on a reused page's ordinary stores: option (b)'s problem
  smuggled in).  `pipeLockAt σ b t` := some `struct file` slot's `f->pipe` word (`ftable`, `FileBoot`) has HELD the address of `b`'s `struct
  pipe` at some timestamp ≤ `t` (a monotone PAST fact of the slot's history — it covers the last `pipeclose`), and `b`'s page carries no
  reclaim entry between that write and `t`.  What changes: `ChainEnv.isLk : PAddr → Nat → Prop` ("`b` is a hop word at `r`"), `ext` monotone in
  the past-fact sense, `hopChain`/`valid_hop`/`memModel_chainHop` check `isLk b r` at the release's position; `chainEnv σ`'s `isLk b r :=
  lockByteIn rsvStatic b ∨ dynLk σ b r` with a client-supplied σ-pure `dynLk : MState → PAddr → Nat → Prop` + monotonicity obligation (MachCSL
  stays kernel-generic [R26.s4]; `Xv6/` supplies `pipeLockAt`); `rsvName` UNTOUCHED (`rsvExact`); NO mint-store side condition (the window
  opens at the `f->pipe` write); `syncPath` (S4) and `xv6LockWord`'s dynamic arm hop through `isLk b r`.  Files: `ChainDefs`, `ChainCert`,
  `Resources` (`chainEnvAt_congr/_ext_*` gain the `dynLk` monotonicity; `rsvModelAt`'s `ChainEnv.ext`-stability proofs re-run) + `PipeBirth`/
  `PipeInv*`/`AccessDiscipline`.  FAITHFUL (restricts only the chains the proof claims; the export's statement unchanged).  Cost ≈ 0.5k + ≈
  0.2–0.3k (the time index), inside (f2-ctx)'s resize.  Unblocks the pipe rows of `W8-Rctx.md` §2 and `lockWordDiscAt`'s pipe part (§C W8
  [R26.2-alt]) with ONE mechanism.  Risk, stated honestly: ANY σ-shape hop predicate ((a′) or (b)) is satisfiable by a reused page whose stores
  happen to alternate like a lock; (a′) bounds this to the pipe's live window, (b) does not; **[R36.3] W11's release-site pin identifies
  release STORES; it cannot select among chains an existential export offers — the σ-predicate must be tight by itself** (rev 39's "the pin is
  what makes a claimed hop real" is withdrawn).  **(a″) AS MERGED (S1′, deviations D1/D2; FAITHFUL; provisional under the non-blocking rule,
  owner informed — Q-F2-PIPEHOP-2 above) [R36.3]:** the dynamic registry is the lock's NAME word — `nameLockAt names m top b a`
  (`Reserved.lean:236`: `lk->name` at `b+8` holds a registered name as of `a ≤ top`), `KernelRsv.names = [pipeLockNameStr]` (= `KS.«pipe»`
  [R36.2]), checked at the hop's ACQUIRE position (`hopChain :180,183`, `memModel_chainHop :173`); `rsvName` untouched; the AMO's step proves it
  from the name word's histories the lock invariant lends (`hopRegAt :613`); MachCSL-fixed shape (`names : List (BitVec 64)`) rather than a
  client `dynLk`.  Differs from (a′) in the WINDOW (name store → name overwrite, instead of `f->pipe` write → reclaim) and the INDEX (acquire,
  not release); D2 is FAITHFUL too (a real hop has `r < a` inside one live window, so indexing at `a` or `r` accepts the same real hops).  The
  worker's reason (F-A) is sound: the generic acquire holds the lock words, not `ftable`'s slots, and there is no persistent history-entry
  receipt.  **Shape fix (REQUIRED before S4, RELAUNCH 2 S0): `syncHop` requires its three entries to be WORD-sized** — `wordEntAt m b t :=
  ∀ i < 4, ∃ e ∈ m[b+i], e.t = t` (same agent) for `a`, `r` and the held entry — so `kfree`'s junk byte `1` on `b` inside the still-open name
  window (`memset` low-to-high, `kalloc.c:55`, `string.c:8-10`) and `kalloc`'s junk `5` under the `initlock` zero are not hops;
  `syncHop_mono`/`hopChain_*`/`memModel_chainHop`'s `hb` gain the word-shape hypothesis, discharged at the AMO from the lock invariant's
  `WordHist 4` (S ≈ 0.1k).  **`lockWordDiscAt`'s dynamic arm is WINDOWED**: for a dynamic `b`, `lockRegionOk` is stated on the sub-history from
  the `initlock` zero (the first word-sized entry inside the name window) to the last word-sized entry before the name overwrite — not on the
  whole history (`Reserved.lean:108` is whole-history; `AccessDiscipline.lean:104` as written would be FALSE at every `kfree` of a pipe).
  **Honest limit:** a user page can be written to LOOK like a live pipe lock (word alternation + `&"pipe"` at `+8`); (a″) + shape does not
  exclude it, (a′)'s kernel-only `f->pipe` history does; neither a release-site nor an acquire-site pin can repair an existential `chainOkAt`
  after the fact.  The residual's options — (a″-s) accept, (a′-r) the entry-receipt anchor — are Q-F2-PIPEHOP-2's.  **(b) any word whose
  history is lock-shaped is a hop**: `syncPath` hops through ANY byte whose history alternates like a lock's (`lkStep` fold).  FAITHFUL for
  the machine (RVWMO orders through any address); cost ≈ 0.3k here, but W11 must then pin the release site PER HOP (a lock-shaped history
  that is not a lock — a flag toggled under a fence — would be a hop W11 cannot locate): ≈ 0.5–1k moves into W11.  **(c) a `.pipe` custody
  exemption in `chainOkAt`**: pipe bytes excluded from the chain conjunct — WEAKER (the theorem says nothing about pipe-data races); cost
  ≈ 0.1k; not taken without a ruling.
- **Q-F2-BOOTGATE — RULED (a) as amended by [R35.2] [OWN.47] (23:25 2026-10-12, rev 39; rev 38 OPEN, provisionally (a); raised by the W8
  (f2-ctx) worker, finding 3). How does the boot publication
  (`started`) compose with lock hops, when σ records no loads?**  *Spec (FIRST).*  RVWMO: hart 0's `__sync_synchronize(); started = 1` is
  `fence rw,rw; sw`, a secondary's `while (started == 0); __sync_synchronize()` is `lw; …; fence rw,rw` (`Xv6/StartedInv.lean:5-9`,
  `SpecMain.lean:6,15`); PPO rule 4 (FENCE) plus the reads-from edge puts every pre-fence store of hart 0 before every post-fence access of
  the reader in the global memory order, and that order is TOTAL — so "hart 0 →(`started`) hart 1 →(lock) hart 2" IS a valid RVWMO ordering:
  the spec composes the two hops.  Sail: plain `mem_write`/`mem_read` (`Mem.lean`) and `effective_fence_set` (`InstsEnd.lean:18299-18313`);
  Zifencei/PMAs silent.  The difficulty is NOT the spec: `MState` keeps per-byte STORE histories and no read positions (`TsoMem.lean`), so
  "hart 1 read `started` BEFORE its release at `r`" is not a fact σ can state — a σ-readable `chainOkAt` cannot check the composed chain;
  only a per-hart ghost can.  *Plain language.*  Hart 0 initialises everything (`kmem.freelist`, the inode table, …) and publishes
  `started = 1`; every other hart spins on `started` before touching anything.  Later hart 2 takes `kmem.lock` after hart 1 released it and
  reads `kmem.freelist`, written by hart 0 at boot and never by hart 1.  The read IS ordered under RVWMO (hart 2 passed `started` itself),
  but the chain the predicate would like to use goes through hart 1's read of `started`, which σ does not record.  *Example.*  Hart 0:
  `freelist = p; fence; started = 1`.  Hart 1: `lw started` (sees 1), `fence`, `acquire(&kmem.lock)`, `release(&kmem.lock)` at `r`.  Hart 2:
  `acquire(&kmem.lock)` (hops on `r`), `ld freelist`.  From σ: the `kmem.lock` hop is visible (byte history), hart 0's store at `t₀ < r` is
  visible, "hart 1 saw `started` before `r`" is not — the certificate 0→1→2 cannot be built.  With the gate: hart 2 holds its OWN "I passed
  `started`" ghost (issued at its spin), and the boot hop `pubCover` carries hart 0's boot-era stores to hart 2 directly.  *Definitions.*
  boot hop / `pubCover` (`ChainDefs.lean:244`) = "every entry hart 0 wrote before its store to `started` reaches hart `j`"; `gateOk :257`/
  `gatePassedAt` (`Ctx.lean:92`) = the per-hart gate, issued when the hart's `started` read sees 1 (`memModel_gateIssue`,
  `ChainCert.lean:129`; `StartedInv.lean`); `RsvKind.pub w` (`Reserved.lean:123` [R35.s1]) = a reserved one-shot publication word written only by `w`
  (landed in S1; `KernelRsv.static` must list `started`, its arm exists `KernelRsv.lean:173`); a lock HANDLE = the persistent `isLock`/
  `lkFresh` fact a lock's creator mints (`Lock.lean:861/:1115`); `gateFloor curCtx` = the context-level flag "this context's hart has passed
  the gate" (S2a); certificate = "`h`'s entries ≤ `t` reach `j` before `τ`" (own / chain / boot hop, `ChainCert :271`).  *Why it matters.*
  Every static lock is born at boot on hart 0 and every lock payload carries boot-initialised data; without a mechanism either every such
  payload is unusable by a secondary hart (unprovable) or boot-era entries are exempted (WEAKER).  The theorem must say how the boot
  handover is justified, checkably.  *Options.*  **(a) RULED [OWN.47], as amended by [R35.2] — `started` a reserved one-shot publication word
  + the creator's gate in lock handles**: `started` joins `xv6RsvStatic` (`KernelRsv.lean:75`; the `decide +kernel` well-formedness checks
  re-run) as `.pub 0`; `main`'s `started = 1` goes through a HISTORY-AWARE reserved store — a variant of `ctxBytes_writeAURsv`/
  `execSpecF_sw_rsv` (`RsvCell.lean:91,127`) over `rsvStoreOk` (`WpAtomic.lean:432-437`, the window's histories `Hs`), because the
  history-free `rsvWordOk` (`RsvCell.lean:33-37`: "any store by the hart keeps `regionOk`") is UNPROVABLE for `.pub` — `regionOk`'s `.pub` arm
  is `cpuRegionOk w ∧ oneShotOk` (`Reserved.lean:158-166`) and a second post-power-on timestamp breaks `oneShotOk` [R35.2]; reserving
  `started` REMOVES its four bytes from the boot carve (`rsvErase`): `bcpBssWindows` (`BootCarveProc.lean:802`) / `bcpBssWindowsR`
  (`BootShared.lean:223`) lose the `started` window, `BootRsv.lean`'s `bootRsvHalves :15` gains the `.pub` group, and `StartedInv` (today an
  ORDINARY `wordCell startedAddr 4 0 0 W`, `StartedInv.lean:51`; `startedArmed :120`/`startedUnarmed :125`) is restated over the reserved HALF
  cell at the image history (`started_readAUr :255` at the fraction; `started_writeAUT :391` by the new rule) — β′'s `WpLockInit.lean` pattern
  for one word; each hart's gate is issued at its
  `started` read, INSIDE the load's atomic step (`memModel_gateIssue :129` needs `gateOk (chainEnv σ') j`, true by `HRead.afterLoad`'s foreign
  stamp, `TsoMem.lean:312-316,356-358`; no `coh` receipt ghost exists [R35.s5]); a lock HANDLE carries its creator's `gateFloor curCtx`, so taking a payload with boot-era coverage requires the taker's
  own gate (hart 0 passes trivially as the writer); every lock-creation site (`kctx_newlock`/`newlock_*`: 18 `Xv6/` files, ≈ 37 lines —
  `initlock` callers on hart 0 in `main`, `initlog`, `pipealloc`) supplies the creator's gate, and `main`'s specs (`SpecMain`/`ProofMain`/
  `MainSecondaryParts`) thread a persistent `gateFloor` premise; `memModel_chainHop :170` takes `gatePassedAt B` for EVERY hop conversion, not
  only for boot-era coverage (`valid_hop :347-350` needs `gateOk X B` in all three arms' bookkeeping), so every acquiring hart needs its gate —
  true in xv6 (a secondary acquires nothing before its spin) and the reason the acquirer's own context flag, not only the creator's handle flag,
  must be ≥ 1 at every acquire [R35.2].  FAITHFUL (an obligation xv6's code meets; the export unchanged; it claims
  only chains RVWMO gives).  Cost ≈ 0.5–1k + the 18 creation sites **+ ≈ 0.3–0.5k for the `started` reservation (`RsvCell` + `KernelRsv`,
  `BootRsv`, `BootCarveProc`, `BootShared`, `StartedInv`) [R35.2]**, inside (f2-ctx)'s resize.  Unblocks R-ctx row 27 and every boot-born
  payload.  Risk: a lock created by a hart before it passed `started` — none in xv6 (secondaries create nothing before the spin).  **(b) the
  gate in the per-hart KERNEL token**: FAITHFUL; every acquire rule demands it and every spec exposes it — ≈ +1.5k and a wider statement
  surface; rejected on cost.  **(c) record read positions in the machine** (`MState` gains a load log): FAITHFUL and σ-checkable, but an
  `MState` change touches W4 `SimRel`/W2a `rmem` — out of the lane, XL.  **(d) exempt hart 0's boot-era entries from `chainOkAt`** (as the
  image is): WEAKER — the theorem would say nothing about boot-initialised data read by secondaries; not taken without a ruling.
- **Q-SCO-PMA — RULED (α) [OWN.45] (16:56 2026-10-12, rev 37; rev 36 OPEN, adopted provisionally; raised by R32 [R32.1]).  What may the
  Sail-cycle fact `sailCycleOrder` assume about the platform's memory map AND HTIF window (`pma_regions`, `htif_tohost_base`, both pinned by
  `bootPost`, `BootInitModel.lean:39,41`) [R33.1]?**  *Spec (FIRST).*  RVWMO and riscv.cat order loads and stores and say nothing
  about the order of fetch, announce and execute inside one instruction (Q-FIARM).  Zifencei says what `fence.i` orders, not whether a hart
  may fetch from a device.  The privileged spec's PMAs make EXECUTABILITY a per-region PLATFORM attribute (an I/O region may or may not
  support instruction fetch); the Sail model in this tree checks it in `pmaCheck` (`model/Lean_RV64D/LeanRV64D/Mem.lean:263-274`) from the
  `pma_regions` register — a platform table, not architectural state — which the board sets at reset (`MachCSL/Platform.lean:199-250`
  `bootPMA`: the two I/O regions `executable := false`, RAM `executable := true`; `BootInitModel.lean:41`) and no instruction ever writes
  (`writeReg pma_regions` only at `ArchReset.lean:125` and `model/…/LeanRV64D.lean:265` `sail_model_init`, both outside the cycle [R33.s4]).  The Sail model with OTHER register contents CAN fetch from a device; the model as
  booted on this board cannot.  **[R33.1] A second platform register sits on the same path: `within_mmio_readable` (`Mem.lean:437-446`,
  between the PMA check and the RAM read) consults `htif_tohost_base` — the Sail model's host-interface (HTIF) window, NOT an ISA or PMA
  notion; `none` on this board (`BootBoard.lean:31`, `HwConfig.lean:53`), its only writer `enable_htif` uncalled — and with `some base` in
  RAM an instruction fetch is answered from the `htif_tohost` REGISTER with no memory read at all.  Pinning it is a platform hypothesis of
  the same kind as `bootPMA`, already inside `wbootFacts`; FAITHFUL to the model as booted; the trusted base gains nothing.**  *Plain language.*  The proof needs "after a hart announces an instruction it does not fetch, and an
  `sfence.vma` announce comes right after its own fetch".  That holds when every fetch comes from RAM.  If a hart could fetch its
  instruction from a DEVICE register (the PLIC, a UART, the virtio window), our graph alphabet would record the fetch as an I/O read
  (`LDev`), not as an instruction fetch (`LIFetch`), and the fact would be false.  On this board the memory map forbids executing from
  device regions, so the fact holds — but only if the theorem is allowed to KNOW the board's memory map.  *Example.*  Hart 0, machine mode,
  no PMP entries; a PLIC enable word at `0x0c002080` holds `0x12000073` — the encoding of `sfence.vma`; hart 0 jumps there.  With the
  board's map the fetch takes an access fault (no fetch, no announce).  With a map marking the PLIC executable, the fetch reads the device
  (`LDev`), announces `sfence.vma`, and hart 0's latest cycle label is the previous instruction boundary (`LInstr`), not a fetch —
  `sailCycleOrder`'s second clause fails; the registered `srvwmoXv6M1Core` and `srvwmoXv6M2Core`, whose hypothesis `hsco` IS that fact over
  EVERY `σ0`, then say nothing.  *Definitions.*  `sailCycleOrder` (`Weak/SrvwmoXv6Adequacy.lean:126`) = that fact, at rev 35 stated over
  every pf run from ANY `σ0`; `wbootFacts σ0` (`Weak/WeakLang.lean:482`) = "`σ0` is the board after reset" (boot image, empty log, each
  hart's registers the output of the boot program with `bootPMA`); `pma_regions` = the Sail register holding the memory map; `htif_tohost_base` = the Sail register locating the HTIF window (`Option
  (BitVec 64)`; `none` = disabled) [R33.1]; `pnodeStep`
  (`Weak/WeakEvInst.lean:294`) = how one Sail event becomes a graph label (a read at a device address is `LDev` whatever its kind,
  `:315-321`); `good`/`cycleOkAll` (`Weak/SailCycleOrderK.lean:139,232` at rev 36; `cycleOkAll` since DELETED) = the tree-level obligation; `cycleOkBoot`
  (`:251`, PROVED — `cycleOkBoot_holds`, `SailCycleOrderCycle.lean:128`) = the
  same with the register filter `Rboot` (`pma_regions = bootPMA` AND `htif_tohost_base = none` [R33.1]); M1/M2 = the internal composition milestones
  `srvwmoXv6M1Core`/`srvwmoXv6M2Core`.  *Why it matters.*  At rev 35 `sailCycleOrder` was quantified over EVERY `σ0`, so it was FALSE and M1/M2
  were VACUOUS; W-SCO (A) as briefed at rev 35 would have tried to prove a false tree fact — **[rev 39] restated under (α) and PROVED:
  `sailCycleOrder_holds`, M1/M2 non-vacuous**.  The published theorem must say which PLATFORM facts it
  relies on, and a reader must be able to see that the trusted base did not grow.  *Options.*  **(α) RECOMMENDED, ADOPTED PROVISIONALLY —
  state the fact under `wbootFacts σ0`** (M1/M2 already assume it in their premise sets, `SrvwmoXv6Witness.lean:599`/
  `PfRunUnpinned.lean:596`; `sailCycleOrderK :92-93` already does): what changes — `sailCycleOrder`'s TEXT gains `wbootFacts σ0 →`,
  `fiOfSco`/`m1Hyps`/`m2Hyps` take it, `good` gains a register filter pinning `pma_regions = bootPMA` and `htif_tohost_base = none`
  [R33.1], W-SCO (A) proves `cycleOkBoot` instead of `cycleOkAll`; names and
  the `baseline-weak.json` entry unchanged.  FAITHFUL to the Sail model AS BOOTED on this board — in practice the trusted base gains NOTHING
  (the boot table was already inside `wbootFacts`); a platform hypothesis, not an ISA strengthening (another board with an executable I/O
  region would need its own table).  Cost S–M (W-SCO (A)'s first commit, ≈ 200–400 lines).  Unblocks W-SCO (A); risk none.  **(β) state it
  under only `∀ c, (σ0.wgregs c) pma_regions = bootPMA`**: FAITHFUL, minimal; the same proof work plus the never-written invariant (needed
  in (α) too); cost = (α); gains a generality nobody needs.  **(γ) change the pf event instance so an instruction fetch at a device
  address is not a step** (`pnodeStep`'s device arm refuses `akIfetch`, `WeakEvInst.lean:315-321`): EQUAL to the model from reset, WEAKER
  than the Sail model with arbitrary registers (removes a behaviour the model has); keeps `sailCycleOrder` closed over all `σ0`; cost M (the
  arm + every W2/W4 row that cases on it); risk: a second place where the pf model is narrower than Sail, to be named in §B(11).  The plan
  adopted (α) WITHOUT waiting (it is the hypothesis M1/M2 already carry); **RULED (α) [OWN.45] 16:56 2026-10-12 — W-SCO (A) launched with
  it in its brief.**  [R33.1] changes the TREE filter (two pinned registers instead of one), not the premise — no further ruling needed.
- **Q-RSV-order — RULED (b) [OWN.41] (11:09 2026-10-12; rev 31 OPEN, raised by the re-check of W-RSV's gate, §C top (4)) [R28.5]:
  the serial lane is W8-β′ → W-RSV → W8 (f2-ctx); W-RSV launches when β′ merges (§C W-RSV "Launch (rev 32)").  The question as
  put: now that M1 has landed FIRST, does W-RSV go on the serial MachCSL lane right after W8-β′, or after W8 (f2-ctx) as
  [OWN.36]/[OWN.37] ordered?**  *Spec (FIRST).*
  Not a memory-model question: RVWMO, riscv.cat, the Sail model in this tree, Zifencei and the PMAs say nothing about the order in
  which two proof changes land; both items are RULED in substance (W-RSV = D19 (b), form (i-a) [OWN.19][OWN.22][OWN.23]; W8 (f2-ctx)
  = [OWN.37][OWN.38]) and neither option changes the published statement, its quantifier or the trusted base — every option is
  FAITHFUL.  What is at stake is schedule: which internal milestone waits.  *Plain language.*  Two large changes to the machine
  model's proof rules (`MachCSL/`) are queued behind the running W8-β′; each forces a rebuild of the ≈ 0.73M-line kernel proof cone,
  so they run one at a time, and whichever lands second re-does its edits where the two touch the same files (**[R28.s4]** ≈ 7:
  `Resources.lean`, the load rules, `WpLock.lean`, `Ctx.lean` (`ctxTokAt`), `KCtx.lean`, `WpDma.lean`, `WpPtWalkOwn.lean` — W-RSV's
  census ∩ (f2-ctx)'s 12; the rework is symmetric, so the count does not move the decision).  **W-RSV** makes a hart's LR/SC reservation vanish at the end of its instruction (so a foreign store is
  never blocked by a stale reservation) and threads a small ghost permission through every "one instruction retires" rule: L–XL, ONE
  rebuild.  **W8 (f2-ctx)** makes the proofs' context tokens carry a proof of release → acquire synchronisation per writer (the
  per-author chain vector) so the robustness step can later rule out stale reads: L–XL, ≈ 6.5–9.5k lines, THREE TO FOUR rebuilds.
  The owner put W8 first because the lane was idle until M1 and W-RSV had to wait for M1 anyway (D26); the plan recorded "if W8 is
  not done when M1 closes, W-RSV waits and the critical path moves".  M1 closed on 2026-10-12, before W8-β′ had finished its first
  day.  *Tiny example.*  Hart 0 runs `lr.w` on `x`, traps before its `sc.w`, and hart 1 stores to `x`: today TsoMem BLOCKS hart 1's
  store until hart 0 retires an SC — a model artifact W-RSV removes; separately, hart B reads words hart A pushed on a kernel stack
  before `swtch` — the read W8 (f2-ctx) justifies by the `p->lock` hop.  Neither change needs the other; only their edits overlap in
  three files.  *Definitions.*  **Serial MachCSL lane**: the one-at-a-time queue of `MachCSL/` changes (W-COH ✓ → W-DMA0 ✓ → W8-β′
  RUNNING → …).  **M1** (`srvwmoXv6M1Core`): the composed sRVWMO/kernel-only theorem, landed.  **M2** (W5d): the same with the
  fork path (user text, cut-form fetch), which CLOSES only after W-RSV's W4 re-check (D26; the published theorem drops "reservation
  serialisation" with it, §0 F1 (ii)).  **W13 (K)**: needs only W8-β′'s `lockWordDiscAt`, not (f2-ctx).  **W11 (i)/(ii)**: the
  Stage-2 consumers of (f2-ctx)'s `chainOkAt`, weeks away behind W13 (XL).  *Why it matters.*  Nothing in the theorem changes;
  under (a) M2 waits ≈ 4–5 rebuilds (β′ + (f2-ctx) + W-RSV), under (b) ≈ 2 (β′ + W-RSV) while (f2-ctx) finishes before anything
  consumes it (W11 comes after W13 (I)/(R), the expected bottleneck); the rework cost (the second lander rebases in ≈ 7 files
  [R28.s4]) is the same in either order, and the owner RULED the current order, so a swap needs a ruling.  *Options (recommended first).*
  **(b) RECOMMENDED — W8-β′ → W-RSV → W8 (f2-ctx)** ([OWN.36]'s recorded (α′), now with M1 landed): W-RSV launches when β′ merges;
  (f2-ctx) rebases on W-RSV's `resvFragAny` thread (its `Ctx.lean` token `ctxTok`, `Ctx.lean:298-299`, is where both meet — S) and on
  `Resources.lean`/`WpLock.lean`.  The theorem says the same, omits nothing; FAITHFUL.  Cost 0 now (brief order only); unblocks M2
  (W5d, launchable now, closes at W-RSV + the W4 re-check) 3–4 rebuilds earlier and retires the §0 F1 (ii) strengthening early;
  risk: (f2-ctx) lands later — harmless unless W13 (I)/(R) finish first (not expected); W5d-G G7 and W11 wait for it either way.
  **(a) keep the ruled order — W8-β′ → W8 (f2-ctx) → W-RSV**: FAITHFUL; cost 0; W-RSV (one rebuild) idles ≈ 3–4 rebuilds, M2 behind
  it; W-RSV rebases on (f2-ctx)'s context layer (also S); risk: M2 — the fork path, part of the target [OWN.3] — is the milestone
  delayed, with nothing gained for (f2-ctx) (no consumer is ready).  **(c) W-RSV's MACHINE change alone now (the `.pure` arm, one
  line) with the ghost thread deferred**: NOT available — the `.pure` step then changes `σ.resv cpu` and `memModelAt`'s `resvMap`
  conjunct needs the fragment in hand (§C W-RSV ghost side [R12.1]); the cone does not build.  *Recommendation:* (b); a ruling is
  needed because it reorders [OWN.36]/[OWN.37]'s lane.
- **Q-R1 — RULED (a) [OWN.38] (rev 31; raised by R-ctx, `notes/W8-Rctx.md` §7). The chain bound of W8 (f2-ctx)'s clean key.**
  *Spec:* RVWMO/riscv.cat define happens-before per EVENT (`rfe`/ppo with fence cumulativity): a chain of release → acquire hops
  carries, per author, a PREFIX of that author's writes; Sail, Zifencei and the PMAs are silent on how a proof represents it — every
  option is a proof-internal shape, the machine and the theorem unchanged.  *Plain language.*  A context's clean key must say
  "every foreign write I may have observed was synchronised to me".  W8-design pinned it as ONE number per context ("every foreign
  entry below `bound ξ` is chained"); R-ctx found this false at an ordinary lock hand-off — the acquirer inherits a bound above an
  unrelated third hart's unsynchronised store.  *Tiny example* (`W8-Rctx.md:61-69`) **[R28.s7]**: hart C stores `y` at stamp 5, hart A
  stores `x` at 10 and releases lock L, hart B acquires L — B's inherited bound ≥ 10 covers C's store at 5, which NOTHING synchronised
  to B.  The true shape is one bound PER WRITER.  *Options:* **(a) RULED — a per-author
  vector `chain ξ : CPU → Nat` beside the UNCHANGED scalar TSO floor, joined at each hop** — FAITHFUL, cheapest; re-sizes W8 (f2-ctx)
  to ≈ 6.5–9.5k / 12 MachCSL + ≈ 52 `Xv6/` / 3–4 rebuilds, with X1–X5 (§C W8); (b) per-key chain-certificate SETS — FAITHFUL,
  equivalent, heavier; (c) keep the scalar form → (f1) everywhere — FAITHFUL, XL ≈ 10–15k; (d) (T) trusted premise — WEAKER, not
  taken.  RULED as recommended.
- **Q-R2 — RULED (a) [OWN.39] (rev 31; raised by R-ctx §4/§7). The USER-table walker arm.**  *Spec (FIRST).*  The privileged
  spec's A/D update scheme (supervisor.adoc; Svadu ON: `menvcfg = ADUE | STCE`, `SpecStart.lean:29,40`): a hardware A/D update is
  ordered with respect to other accesses ONLY when it is ASSOCIATED with an access the hart's fences order, and the A bit MAY be set
  SPECULATIVELY (for a translation the hart never uses), in which case nothing orders it; RVWMO orders implicit page-table accesses
  by `SFENCE.VMA`, not `FENCE`; the Sail model in this tree performs the update as `read_pte_exclusive`/`write_pte_conditional`
  (`WpPtWalk.lean:3-7,156-165`; the user-table owned form `WpPtWalkOwn.lean:501-515`); Zifencei/PMAs silent.  *Plain language.*  When
  a process migrates, the new hart's page walks read PTE bytes the old hart's hardware wrote (A/D bits).  The TSO proof treats that
  write-back as the old hart's OWN store, carried over `p->lock` like its stack words.  Under RVWMO a speculative A-bit update
  need not be ordered before the old hart's `release`, so claiming a chain there would exclude spec-allowed executions.  *Options:*
  **(a) RULED — user PTE bytes under the `pte-key` arm** (`Cust.pte`/`pteDiscAt` cover both tables; `WpPtWalkOwn` joins W8
  (f2-ctx)'s file list) — FAITHFUL, STRONGER only in documentation; (b) CHAINED as owned stores — would need the ordering the spec
  does not give: UNFAITHFUL; rejected.  RULED as recommended.
- **W4-F9-wrap — RULED (a′) [OWN.40] (rev 31; raised by the F9 worker). An OUT capture buffer wrapping past `2^64`.**  *Spec:*
  the PMAs — no physical memory exists past the top of the address space (a wrapped DMA read is a model artifact of `PAddr`
  arithmetic); RVWMO/riscv.cat/Sail have no device/DMA model; virtio 1.x says nothing about a buffer past the end of memory.
  *Plain language.*  MachCSL's device wraps the address when it reads an OUT buffer that crosses `2^64`; the pf disk program reads
  `Int` addresses where the image aliases past `2^64` — the two capture different bytes and F9's rows would be false.  xv6 never
  publishes such a buffer (1 KiB, in DRAM).  *Options:* **(a′) RULED — the pf program STALLS the request** (`VirtioProg.outWraps`;
  §B(11) (x)): FAITHFUL to the PMAs, STRONGER than MachCSL, pf ⊆ MachCSL, no hypothesis left, MachCSL/`Xv6/` untouched; (a) an F9
  HYPOTHESIS `Hyps.noWrap` discharged by W5 from the SC tree — a driver fact (a new export), the cost W-DISK-Q1 (a) rejected; (b)
  make MachCSL's DMA read stall/fault — re-opens `WpDma*`/the driver proofs.  RULED as recommended.
- **Q-W8-feed — RULED (a) [OWN.37] (rev 28; raised by the W8-design spike, `notes/W8-design.md` §7, under the plan's own
  re-open rule `:2292-2294`/D24).  How is W8's access-discipline export FED — where do the proofs learn who may write a byte?**
  *Ruling as applied:* **(a) (f2-ctx) chain-carrying context tokens**, behind a read-only S check of the ≈ 35 TSO-leaky
  context-law uses (R-ctx, W8-design §3.4), with **W8-β′** (the lock layer's own words + `cpus[h]`, M) landing FIRST; the export
  `xv6AccessDisc` reaches a root through the SIBLING root (r2) `Xv6.xv6DiscAdequacy_closed`; supersedes [OWN.36]'s one-rebuild
  sizing — W8 is L–XL with 2–4 rebuilds (§C W8, §C top, D24, D26).  The question as asked:  *Spec (FIRST).*  Not a
  memory-model question: RVWMO, riscv.cat, the Sail model in this tree, Zifencei and the PMAs say nothing about how a PROOF
  states or feeds ownership; every form of W8's export is a fact about xv6's CODE, and every option below leaves the published
  quantifier unchanged — all FAITHFUL except (c), which puts an unproved program property in the trusted base (WEAKER).  What
  is at stake is cost, the serial lane, and one possible assumption.  *Plain language.*  The robustness step (route (9d))
  needs facts like "this stack byte was written only by the hart that owned the stack at the time" and "this read of
  `p->state` happened under `p->lock`".  W8-design found WHERE such facts can come from.  The EXPORT itself is easy to state:
  a predicate on the machine state, computed from the per-byte write histories and the `cpus[h].proc` words (who runs which
  process) — no extra bookkeeping.  The hard part is FEEDING it: proving, at every one of the ≈ 2,150 load/store proof steps
  in the kernel proofs, that the writer was entitled.  Today's memory rules know nothing about entitlement — a store rule sees
  "a cell I own" whether the cell is my stack or `proc[3].state` under `proc[3].lock`; the lock layer moves a protected cell
  into the holder's "context" at acquire, and a context's cleanliness means only "some acquire happened since" — fine on TSO,
  not on RVWMO.  So either every site is edited by hand ((f1), huge), or the CONTEXT itself is made to carry the proof of
  synchronisation: a chain of release → acquire hand-offs from the writer to the reader ((f2-ctx)).  *Tiny example.*  Hart A
  runs process P; `sched`'s prologue pushes `ra`/`s0` on P's kernel stack; A's scheduler sets `c->proc = 0` and releases
  `p->lock`; hart B acquires `p->lock`, sets `c->proc = p`, `swtch`es into P and `sched+0x7e` LOADS the words A pushed — a
  cross-hart read of plain stores.  Under (f2-ctx) B's context token, after the acquire, carries the chain "A released
  `p->lock` after writing; B acquired it", and the load rule concludes the read is sync-chained — no site edit.  Under (f1)
  the proof of `sched`'s loads (and of every `memmove`/`copyin` that ever touches a stack buffer) states who owns the stack
  words.  *Definitions.*  **Export**: `xv6AccessDisc σ` (§C W8) — `chainOkAt` (every foreign write a hart has observed is
  sync-chained to it, lock-layer bytes exempt), `lockWordDiscAt`, `cpuStaticAt`, `cpuProcDiscAt`, `utextDiscAt`.  **Feed**:
  how the state-interpretation invariant that implies the export is RE-ESTABLISHED by each proof rule.  **(f1)**: at every
  protected load/store application in `Xv6/`.  **(f2)**: at the lock layer's doors only (`procHeld`, `stackOwn`, the `swtch`
  payload, `wp_acquire`/`wp_release`).  **(f3)/(f3′)**: derived from σ alone — (f3′) the dynamic owner read off `cpus[h].proc`.
  **(f2-ctx)**: the clean context key carries a `syncPath`; `ctx_absorb`/`ctxStamped_raise`/`lockHook_llb` restricted to
  chained receipts; a device-key arm for DMA.  **R-ctx**: the read-only check that each of the ≈ 35 uses of the TSO-leaky
  laws (bcache/icache/sleeplock floors, virtio completion floors) can be re-justified by a chain or the device-key arm.
  **Serial MachCSL lane**: W-COH ✓ → W-DMA0 ✓ → W8-β′ → W8 (f2-ctx) → W-RSV.  *Why it matters.*  Nothing in the theorem
  changes under (a) or (b); the choice is cost (≈ 5–8.5k vs ≈ 10–15k lines; 2–4 vs many cone rebuilds), the lane (W-RSV waits
  for whichever W8 form lands), and one risk (R-ctx may send parts to (f1)).  (c) changes the trusted base.  *Options.*
  **(a) RULED — (f2-ctx) chain-carrying contexts**: L–XL ≈ 5–8.5k lines, 11 MachCSL + 19–62 `Xv6/` + 5 twin files, 2–4 cone
  rebuilds, serial MachCSL before W-RSV, as ruled; gate: R-ctx (S, read-only) before the worker starts; if any use resists,
  fall back to (b) for THAT part.  To an xv6 expert the theorem says exactly what it says now — the feed is proof-internal;
  it omits nothing.  FAITHFUL.  Cost L–XL; unblocks W11 (i)/(ii)'s `chainOkAt` consumption generically; risk: R-ctx finds a
  cross-lock fact the TSO proof never tracked (→ partial (f1)); `ctxFloor`'s meaning changes (108 uses, up to 43 more files).
  **(b) (f1) per-site custody**: XL ≈ 10–15k lines, ≥ 320 `Xv6/` files, a `KCtx` stack-region link, page custody, payload
  footprints for 12 lock classes + sleeplocks, spec changes for every buffer-taking function, many rebuilds.  Says the same;
  omits nothing; FAITHFUL.  Cost XL; unblocks the same; risk: the critical path moves to W8.  **(c) (T) `xv6AccessDisc` as a
  NAMED trusted premise** of T-alloc-RVWMO (the predicate at every reachable state), audited informally by the pin table: S
  (statement + W11 plumbing).  To an xv6 expert the theorem then ASSUMES xv6's access discipline instead of proving it — an
  unproved PROGRAM property beside `ioResidueGmo`/`gzFetch`/`sailCycleOrder`, which are MODEL properties; WEAKER.  Cost S;
  unblocks W11 at once; risk: a trusted-base item an expert will not accept as a model fact.  *Recommendation (W8-design):*
  (a) behind its S gate, with W8-β′ landing first (independent of the gate; unblocks W13 (K)'s `lk->cpu` precondition) —
  **RULED as recommended [OWN.37]**.
- **Q-HOLDING — REPORT level, no gate (rev 28; found by the W8-design spike, `notes/xv6-holding-race.md`): the plan's (iii)
  was FALSE at `holding+0x12` — a non-holder's racy read of `lk->cpu`.**  *Spec (FIRST).*  RVWMO (rules 1–3 / riscv.cat
  `gppo1`–`gppo3`, load-value): a PLAIN load racing a foreign PLAIN store may return any write to the byte not yet overwritten
  in the reader's coherence order, but a hart cannot read its OWN older store past its own newer one (per-location coherence);
  a naturally aligned 8-byte `ld`/`sd` is single-copy atomic (D20); Sail: `ld`/`sd` are ordinary `mem_read`/`mem_write`
  (no view semantics); Zifencei/PMAs silent; C11 calls the pattern a data race (undefined behaviour) — irrelevant here, the
  object of study is the COMPILED image [OWN.4].  So the race is a GENUINE RVWMO behaviour of the verified code; no option
  below may exclude it from the quantifier.  *Plain language.*  xv6's `acquire(lk)` first calls `holding(lk)` ("do I already
  hold it? then panic") — BEFORE taking the lock.  `holding` reads `lk->locked` and `lk->cpu` with plain loads.  Meanwhile the
  real holder writes `lk->cpu = mycpu()` with a plain store right after winning the AMO (no fence after it) and clears it
  in `release`.  So the acquirer's read of `lk->cpu` races with the holder's not-yet-published store.  It is harmless: the
  read is only compared with the reader's own `mycpu()`, every store to `lk->cpu` is 0 or the storer's own pointer, and the
  reader's own latest store there is the 0 of its last `release` — so a non-holder can never read its own pointer and
  `holding()` returns 0 on every RVWMO execution (the SC proofs already use exactly this: `lkCpu_read_not_mine`,
  `MachCSL/Lock.lean:18-22`).  But the plan said this read was "protected by its own lock", which a non-holder's read cannot
  be.  *Tiny example.*  CPU A holds `lk` and has executed `sd a0,16(s1)` (`lk->cpu = &cpus[A]`), still in A's store buffer.
  CPU B calls `acquire(lk)`: `holding+0x12` (`0x80000c04`) loads `lk->cpu` and may see 0 (A's store unpublished), `&cpus[A]`
  (published), or an older holder's pointer — never `&cpus[B]`.  B's `holding()` returns 0 either way; B then spins on the
  AMO.  Under the plan's (iii) ("no hart's floor reaches a foreign owned-unpublished message") the first outcome is a
  `violationHart` instance — so (iii) is false for this byte on a run the SC tree certifies.  *Definitions.*  **`holding+0x12`**:
  the `ld a5,16(a0)` of `lk->cpu` in `holding()`, pin `PResidue` (`Weak/KernelPins.lean:255`).  **(iii)/(iii+)**: W8's
  "no observed foreign owned-unpublished message" clause / its sync-chain form `chainOkAt`.  **`lockWordDiscAt`**: W8's
  lock-layer clause — every post-registration lock-word write a whole-word 0/1, a 0 only by the holder; every `lk->cpu` entry
  0 or the writer's own `&cpus[w]`, written by the holder.  **`lkCpu_read_not_mine`**: the SC lemma "a racy read of `lk->cpu`
  by a non-holder never returns its own pointer".  **W13 (K) precondition (ii)**: `ioSegPinned`'s lock-layer side condition.
  *Why it matters.*  Nothing in the published CONCLUSIONS changes and the quantifier is unchanged (the racy execution stays
  in it; its outcome is proved benign).  What changes is plan TEXT and the shape of W8's export and of W11's `badSeg`
  refutation: the W13 I/O census's C2 "held: CSchained under `L` itself" and [W13c]'s "W8's (ii) must cover `lk->cpu` under
  its own lock" were wrong; three plan sites are corrected (§C W13 (K) R5, §C W8, §C W11).  *Options.*  **(a) RECOMMENDED
  and APPLIED — exempt the lock-layer bytes from (iii+) and cover them by `lockWordDiscAt`**; W11's `badSeg` refutation and
  W13 (K)'s `ioSegPinned` route `lk->cpu` reads through it (`lkCpu_read_not_mine`'s argument: the value only feeds the
  `== mycpu()` compare).  The theorem says the same; omits nothing; FAITHFUL (proof-internal).  Cost: S text now + one
  `badSeg` arm in W11 (S); `lockWordDiscAt` is W8-β′'s deliverable anyway.  Risk: none beyond the honesty line.  **(b) keep
  (iii) and treat the read as `Bad`/exclude executions where the acquirer sees the unpublished store**: a quantifier
  RESTRICTION on a behaviour xv6 exhibits on every contended acquire — STRONGER and FALSE to the kernel; rejected.  **(c) fix
  xv6** (`__atomic_load_n`/`__atomic_store_n` relaxed on `lk->cpu` — same machine code — or drop `holding()` from
  `acquire`): the C11 cure; changes the object of study against [OWN.4] (and the compiled image would be identical for the
  first form, so it buys the proof nothing); [R25.s6] the SAME racy-read pattern exists at `holding+0x0` on `lk->locked` (C1 in
  the census table, covered by `lockWordDiscAt`'s word clause), so (c) would have to touch BOTH fields or drop the `holding()`
  call; recorded, not applied.  *Report:* (a) is the only consistent reading; no ruling
  needed unless the owner wants (c) recorded as a kernel follow-up.
- **Q-GFDEV-delta — REPORT level, no gate (rev 26; raised by R22 [R22.2]): a wording delta of [OWN.31]/[OWN.32] — which
  disk-row items count as fabric transactions in the published conformance premise.**  *Spec (FIRST).*  The RVWMO chapter
  and riscv.cat have no device-internal events and no notion of a device's register state; the Sail model in this tree has
  no device/DMA model (`MachCSL/Dev/*.lean` is the only device text; an MMIO access is an ordinary `mem_read`/`mem_write`
  routed by `devAddr`, `MachCSL/Dev/Fabric.lean:126-141`); Zifencei is silent; the PMAs order within ONE I/O channel only;
  virtio 1.x says the device reads the ring/descriptors and writes used elements/index, not when it re-reads its registers.
  Every option below is STRONGER than this silence (device-model text, D45/D49 class) and none changes the published
  CONCLUSIONS.  *Plain language.*  The published premise `xv6ConfS` lists, per row, which events are "fabric transactions"
  — steps at which a device's registers or its own bookkeeping are read or changed — in the order the devices served them
  (`gfDev`); platform assumption (R3) then says memory order agrees with that order.  Rev 20–25 said only I/O accesses and
  ONE disk-side store (the used-index write) are fabric transactions, and that every I/O access CHANGES the fabric.  At
  the tip neither holds: an I/O READ of a status register changes nothing (UART LSR `Uart.lean:120`; the virtio NOTIFY
  write `Virtio.lean:310` and every virtio register read `:337-338` likewise), though its VALUE depends on where it sits;
  and the device's status/used-element stores DO change the device's bookkeeping (their guards read it — [OWN.32]'s
  folding).  *Tiny example.*  Hart 0 polls the UART line-status register (reads `LSR`; nothing changes), then writes a
  byte to `THR`; meanwhile the disk, serving a request, writes the status byte into RAM — its guard first checks the
  request is still in flight and marks it served.  Under rev 25's text the `LSR` read is an I/O event that "must" move the
  fabric yet moves nothing: no emission conforms, the execution falls outside the quantifier (vacuity — the `emDevfree`
  shape one level up).  Under the fix the `LSR` read is listed by CLASS (the fabric sequence stutters there), the status
  store is listed because it moved the device's bookkeeping, and (R3) orders both against hart 1's MMIO.  *Definitions.*
  **Fabric** (`Efab`): the devices' registers, wires and internal state (virtio: in-flight phases, write cache, capture
  latch).  **`gfDev`**: the list of row items that are fabric transactions, in fabric order.  **`gisIo`**: the item is an
  I/O-class event (a hart MMIO access, a pin delivery, a device-thread move, the disk's START/pop).  **`dvi k`/`dvo k`**:
  the fabric before/after row item `k`.  **(R3)**: "I/O events are gmo-ordered as the fabric serializes them"
  (`GraphFabResidue.lean:84-99`).  **`DWriteDev`**: W-DISK's disk-side RAM store whose guard reads the device state and may
  move it.  *Why it matters.*  The trusted-surface sentence changes from "one RAM store per completed request is a fabric
  move" to "the device's request-service RAM stores are fabric transactions"; (R3) then couples three to four disk-side
  stores per request (not one) to hart MMIO order.  Conclusions unchanged; the quantifier omits executions in which those
  stores are reordered against unrelated MMIO — executions the one-row device model (D51) already excludes in spirit.
  *Options.*  **(a) RECOMMENDED and APPLIED — `gfDev ↔ gisIo ∨ (dvi ≠ dvo)`; every `DWriteDev` store that moves `dvirtio`
  is a member.**  Changes: §A(†)/(I) text only; (R3) over those stores.  STRONGER than the spec by (R3) on them (in
  practice: the theorem does not cover a device that reorders its own status store against an unrelated hart's MMIO);
  EQUAL to MachCSL; realization-necessary under [OWN.32] (a).  Cost: S text now, nothing in (I)'s size.  Unblocks W-DISK
  and (I) consistently; risk: none beyond the honesty line.  **(b) keep only the used-idx store in `gfDev`.**  Then the
  realization cannot place the status/used-element stores relative to hart MMIO although their guards read the fabric —
  the (L) trace existence FAILS; not available under [OWN.32] (a).  **(c) re-rule [OWN.32] to (b): pure device-state reads
  as `LDev .dev` events, the stores plain.**  FAITHFUL to the same executions (the `dev` events carry (R1)–(R3) instead of
  the stores); cost +S on (I) text and a W-DISK brief change before launch; no benefit over (a).  *Report:* the owner's own
  folding ruling [OWN.32] (a) makes (a) the only consistent reading of [OWN.31]; the plan applied it and reports the
  wording delta — a ruling is needed only if the owner prefers (c).
- **Q-W8-lane — RULED (α) [OWN.36] (rev 25; raised by R21 [R21.1]); its one-rebuild sizing SUPERSEDED by [OWN.37] (W8 =
  W8-β′ + W8 (f2-ctx), 2–4 rebuilds — Q-W8-feed above; the (β) split it hoped for does NOT exist, W8-design §4).  Which proof
  lane does W8 — the export of xv6's per-access discipline — run on?**  *Ruling as applied:* a read-only **W8-design** spike first (pins W8's export
  statement = D24, the ledger's file/lane, and whether a ledger-free (β) export covers W8 (i)/(iii)); then W8's ledger in
  the state interpretation is the next serial MachCSL item, BEFORE W-RSV: lane W-COH ✓ → W-DMA0 ✓ → W8 ledger → M1 →
  W-RSV (§C, D24, D26).  The question as asked:  *Spec (FIRST).*  Not a memory-model question: RVWMO, riscv.cat, the
  Sail model in this tree, Zifencei and the PMAs say nothing about how a PROOF organises its ghost state — every option is
  FAITHFUL (none changes the published statement or its quantifier).  *Plain language.*  The robustness argument (route
  (9d), the step that turns "xv6 is correct on the strong model" into "xv6 is correct on RVWMO") needs facts about HOW xv6
  touches memory — e.g. "this byte is hart 2's stack, so no other hart writes it", or "this read of `p->state` happens
  while `p->lock` is held".  Only the existing SC (strong-model) proofs know these facts, so a new export, **W8**, must
  state them as a property of every reachable machine state.  *Tiny example.*  Hart 0 reads `proc[3].state` at
  `allocproc+0x40` holding `proc[3].lock`; hart 5 writes that byte only under the same lock.  The final theorem's
  CYCLE-KILL (the proof step that rules out the weak-memory executions xv6 could not survive — e.g. hart 0 reading a
  stale `state` that hart 5 overwrote before releasing the lock) needs the state-level fact "every write to that byte in
  its history was made by a holder of `proc[3].lock`" — W8's (ii).  *Definitions.*  **Serial MachCSL lane**: the
  one-at-a-time queue of changes to the machine model's proof rules (`MachCSL/`); each change forces a rebuild of the
  ≈ 0.73M-line kernel proof cone, so two such changes in parallel collide.  Done: W-COH (coherence stamping), W-DMA0
  (zero-length DMA).  Queued: **W-RSV** (clearing LR/SC reservations at instruction boundaries), after M1.  **M1**: the
  first internal composed theorem (xv6 on sRVWMO = RVWMO with stores never performed early, kernel-only).  **State-interpretation
  ledger**: a ghost record kept beside the machine state and updated by every memory rule, as the invariant `mmOk`
  (`MachCSL/Resources.lean:779-785`) is today.  **`badSeg`/`protReg`**: the robustness proof's two consumers of W8's
  facts (W11 (i)/(ii)), read through the log identification `R` (`PfStepTsoMem.lean:57,62`).  *Why it matters.*  Nothing
  in the theorem changes; it is schedule and rework: W8 (L–XL) and W-RSV (L–XL) both edit the memory rules (`Wp`,
  `WpAtomic`, `Resources.lean`), and whichever lands second redoes its edits — rev 24 launched W8 "in parallel" while
  calling it `Xv6/`-only, which was wrong.  *Options (recommended first).*  **(α) RULED — ledger in the state
  interpretation (D24's recommendation) as the next serial MachCSL item, before W-RSV, after a read-only W8-design
  spike.**  Concretely: `memModelAt` gains the ledger, every `Wp*` memory rule maintains it, the cone is rebuilt once.
  FAITHFUL.  Cost: S (spike) + L–XL on the serial lane NOW (idle until M1).  Unblocks W11 (i)/(ii) early.  Risk: if it is
  not done when M1 closes, W-RSV waits and the critical path moves.  **(α′) the same, after W-RSV**: no collision; delays
  W8 by W-RSV's length — matters only if W8 becomes the bottleneck (W13, XL, is expected to be).  FAITHFUL.  **(β) an
  export derived WITHOUT touching the rules** (D24 (c): W9a's static pin check + ownership facts proved inside `Xv6/` at
  adequacy): FAITHFUL; parallel now, no cone rebuild; cost and feasibility **unverified** — (ii)'s lock-protection facts
  may not be derivable without a ledger; risk: a partial export, the rest a ledger later.  *Recommendation (R21):* (α) with
  the spike first; if the spike shows (β) suffices for (i)/(iii), split W8 accordingly — RULED as recommended.
- **Q-SCO-words — RULED (A) [OWN.42] (13:59 2026-10-12, rev 35; raised by the W-SCO worker, `../weak-orch/parked/PROGRESS-WSCO.md`).
  Which instruction words must the "no fetch during execute" proof cover?**  *Spec (FIRST).*  RVWMO, riscv.cat, Zifencei and the PMAs
  are silent on in-cycle order (Q-FIARM).  The Sail model (`model/Lean_RV64D/LeanRV64D/Fetch.lean:252-280`): with `Ext_Ziccif`
  (`Extensions.lean:528`) a 4-aligned pc is fetched as ONE 4-byte read; at `pc ≡ 2 (mod 4)` the low halfword at `pc` is fetched and —
  if it is not compressed — the high halfword by a SEPARATE `fetch_bytes pc (pc+2) 2` (`:217-226`) with its OWN `translateAddr`,
  announcing `ihi +++ ilo`; the ISA agrees (a page-crossing instruction may fault on either page).  *Plain language.*  W-SCO was to
  prove, for each 4-byte word of the kernel window, that executing it fetches nothing; but a hart whose pc is 2 mod 4 announces a word
  GLUED from two halfwords translated separately, and M1's fetch clause `candKfetch` pins only the ADDRESSES — so the word set the brief
  enumerated is not the set of words the model can execute.  *Example.*  Hart 0 at `pc = 0x80003ffe` (the last halfword of a page)
  fetches `lo` there and `hi` at `0x80004000` through a second page walk; if the two walks read different PTE values the announced word
  is not any aligned window word.  *Definitions.*  `cycleOkAll` (`Weak/SailCycleOrderK.lean:232`) = "for every `tick`, the Sail cycle
  `riscvStep tick`, once it has announced, fetches nothing, announces nothing more, and executes a `fence.i` barrier only after an
  announce / no `fence.i` after an SFENCE.VMA announce"; `sailCycleOrderOfCycle :470` turns it into the premise `sailCycleOrder`.
  *Why it matters.*  `sailCycleOrder` is the ONE named ISA-model premise of M1/M2/§A's statement; a word set with a hole would make
  the kernel-text proof unsound and leave the premise undischarged.  *Options.*  **(A) RULED — prove `cycleOkAll` for every
  instruction** (122 `execute_*` clauses, `fence.i`/SFENCE.VMA by hand, the instruction-independent cycle): FAITHFUL to Sail (no
  restriction); the premise leaves M1, M2 and the published statement for kernel AND user text; L ≈ 1.5–3k; risk: elaboration budget —
  the largest Sail-syntax proof in the tree.  **(B)** per-class over the TRUE word set (`lo` halves carry 31 of 32 major opcodes):
  FAITHFUL; no cheaper than (A), proves less (kernel text only).  **(C)** pin the second halfword to `pa + 2` by a TLB-register
  invariant: FAITHFUL; L+, fragile.  **(D)** restrict M1's candidates to adjacent halves: WEAKER than Sail (excludes runs the model has),
  M1's statement changes; rejected.  §C W-SCO is the RELAUNCH brief.  **[R32.1] (rev 36): `cycleOkAll` as defined is FALSE (a fetch from MMIO under an arbitrary
  `pma_regions`); (A) is proved as `cycleOkBoot` under the boot PMA table — Q-SCO-PMA (α), RULED [OWN.45].  [rev 39] DONE: `cycleOkBoot_holds`/
  `sailCycleOrder_holds` (`Weak/SailCycleOrderCycle.lean:128,137`), 122/122 clauses, `Weak.srvwmoXv6M1` registered.**
- **Q-GFDEV-contact — RULED (a) [OWN.43] (13:59 2026-10-12, rev 35; raised by the W13 (I) worker, `../weak-orch/parked/PROGRESS-W13I.md`; LANDED — W13 (I) bundle half DONE, rev 37).
  Which row items are `gfDev` members in the published conformance bundle?**  *Spec (FIRST).*  RVWMO/riscv.cat/Sail have no
  device-internal events; Zifencei and the PMAs are silent; virtio 1.x says nothing about when the device re-reads its state — `gfDev`
  and (R1)–(R3) are device-MODEL/trusted-surface text (D45/D49 class); no ISA order is at stake; every option is beyond the spec's
  silence.  *Plain language.*  The bundle fixes the global device state (the "fabric") to change ONLY at `gfDev` members; a NON-member
  block must then be replayed at the global fabric from where the row left it.  Under W-DISK's state-aware `pdevEv` a disk block can
  READ the fabric without moving it ([R22.2] made it a non-member), and a block that reads the fabric is fabric-DEPENDENT: at the
  global fabric it may MOVE, so no replaying step exists.  *Example.*  After the POP member the disk's IN-fill store runs, row-locally,
  at a state with `phase = .fetched` — its guard is the identity, `dvi = dvo`, non-member; at the global fabric `phase = .popped`, the
  guard sets `.fetched` — the store MOVES, and `execProgOk'` at the supply fabric `fab ∘ dcnt` is FALSE.  Unreachable in xv6 (phases
  move only by the disk's own program) — a gap of the GENERIC bundle.  *Definitions.*  `gfDev` = the fabric-ordered member list of the
  bundle (`WeakRvwmoFab.lean:606-609`); `dvi k`/`dvo k` = a tagged item's fabric endpoints (`hemitf :253`); `pdevEv p l p'`
  (`WeakEvInst.lean:604`) = "this step touches the devices"; `pdevEvOk :1792` = a `pdevEv`-false step neither changes nor depends on
  the fabric; `hblkQ :332` = the folding "a block is replayable at ANY fabric"; `supplyOfFconf :789` = the lemma that builds the
  candidate's device supply from the bundle.  *Why it matters.*  `xv6ConfS` is the published theorem's CONFORMANCE premise; a membership
  criterion the realization cannot discharge would be an unprovable premise on the published path.  *Options.*  **(a) RULED —
  membership by fabric CONTACT**: `(i,k) ∈ gfDev ↔ gisIo (i,k) ∨ dvi k ≠ dvo k ∨ the block of item k has a `pdevEv`-true step`;
  non-members are quiet ⇒ fabric-preserving AND blind (`pdevEvOk`); `hblkQ`'s `∀ d` folding GENERALIZED, the interim `.PDisk` clause
  deleted.  FAITHFUL to RVWMO (no ISA order added); EQUAL to [R22.2] on every xv6 run; STRONGER as generic trusted text only by
  unreachable non-moving fabric-touching blocks ((R3) orders them); cost M (the planned (I) delta); unblocks `gfexecConfIO`, W5d-G G1–G5.
  **(b)** keep [R22.2] + a bundle clause "every non-member block is fabric-blind", discharged by W14 from a `virtioProg` invariant:
  FAITHFUL, EQUAL on xv6 runs, a STRONGER conformance premise; M + an S–M W14 obligation.  **(c)** keep [R22.2], supply at row-local
  endpoints, `hblkQ` deleted, with a TRACE premise "at a non-member position the global fabric equals the row's `dvi`": (L)'s
  `ptraceRelIO` does not order a disk RAM store against another row's MMIO write, so it stays UNDISCHARGED — WEAKER; rejected.
  Supersedes [R22.2]; §A(†) and §C W13 (I) updated; §C W13 (I) is the RELAUNCH brief.
- **Q-FIARM — RULED (b)+(a′) [OWN.35] (rev 24; raised rev 23 by W2 CLOSE's day-one finding, `../weak-orch/parked/
  PROGRESS-W2CLOSE.md`).  Where does the proof get the fact "a hart's `fence.i` barrier comes AFTER its instruction's
  announce, and the announce AFTER its fetch"?**  *Ruling as applied:* ONE named trusted premise `sailCycleOrder` on
  `machRunOfPfRun` / M1 / M2 and §A's statement, listed in §B(11); W4 landed it as `MachOfPf.Hyps.fi :635`; [R20.s4] its
  FORM is a CLOSED proposition over every `pfRunST` run from `wpInit … (epsInit σ0)` (all `fok`, `σ0`) — the realized pf
  run is existential in §A's conclusion, so a per-run side condition could not appear there — the shape `bootImageSealed`
  has, stated on the hart rows' LABEL LISTS, not on the shadow's `fiArm` [R21.s1]; after M1, **W-SCO** (§C) proves it for xv6's kernel text ((a′), M–L) and demotes it from M1; M2/§A keep it for user
  text unless (a) is later taken — **[OWN.42][rev 35]: (a) IS TAKEN (Q-SCO-words above): W-SCO (A) proves `cycleOkBoot` (`cycleOkAll` under the boot PMA table [R32.1]) for EVERY
  instruction, so `sailCycleOrder` becomes a THEOREM for kernel AND user text and leaves M1, M2 and §A's statement; the kernel-text
  route (a′) was withdrawn because the per-word set cannot contain the two-halfword words the cycle announces; DONE rev 39 —
  `sailCycleOrder_holds`, `Weak/SailCycleOrderCycle.lean:137`**.  The question as asked:  *Spec (FIRST).*  RVWMO and riscv.cat order MEMORY operations; they say nothing about the ORDER OF EVENTS
  INSIDE one instruction's execution cycle (fetch, announce, execute are not RVWMO notions).  Zifencei says a `fence.i`
  orders the hart's earlier stores before its LATER instruction fetches — WHAT the fence does, not WHEN in the cycle the
  model emits it.  The Sail model in this tree fixes the order by its text: `run_hart_active`
  (`model/Lean_RV64D/LeanRV64D/Step.lean:331-404`) is `dispatchInterrupt` → `fetch ()` (`:335`; `Fetch.lean:233`, one or
  two instruction-fetch bus reads) → `instr_announce` (`:340` compressed / `:377` base, immediately after the fetch
  result) → decode (pure) → `execute` (`:370-371` / `:404-405`), and nothing in `execute` is an instruction fetch;
  `try_step :416` wraps it; `MachCSL/UCycleDefs.lean:11-17` already re-states this cycle by EQUATIONS (`uc_tryStep_eq`,
  `uc_runHartActive_eq`: `fetch () >>= ucAfterFetch`).  PMAs silent.  So the fact is TRUE OF THE MODEL **from this platform's reset — [R32.1]: the boot PMA table forbids
  instruction fetch from I/O regions and the HTIF window is disabled [R33.1]; over arbitrary register files it is FALSE (a fetch from a device address is an `LDev` step,
  `WeakEvInst.lean:315-321`), so the premise is stated under `wbootFacts σ0` (Q-SCO-PMA (α), RULED [OWN.45])**;
  the question is how the proof OBTAINS it.  *Plain language.*  The published theorem's hart rows are proved one EVENT at
  a time (a bus read, a store, a barrier …) through `pfStepTso` (`Weak/PfStepTso.lean:301`), which relates the pf hart
  (the weak-memory side's hart: a Sail program emitting labelled events) to MachCSL's TsoMem hart.  TsoMem keeps an
  INSTRUCTION VIEW `itv` — how new the bytes a hart FETCHES must be — and raises it at `fence.i` (`Lang.lean:155-163`).
  The weak side has no `itv`; W5b′'s SHADOW (`tsoShadow`, `TsoShadow.lean:290-318`) recomputes it from the hart's label
  list.  Two different instructions emit the SAME label `LFence false×4`: the `fence.i` BARRIER node, and the `sfence.vma`
  MARKER (the ANNOUNCE of an sfence.vma word — owner ruling Q7 route (a)).  The shadow tells them apart with one bit,
  **`fiArm`**: set by `LInstr` (the cycle boundary and the announce), cleared by `LIFetch` (an instruction-fetch read) —
  "the latest own `LInstr`/`LIFetch` was `LInstr`".  That works ONLY IF the model's cycle is boundary → fetches →
  announce → execute: then at a `fence.i` barrier the latest such step is the announce (`fiArm = true`, `itv` raised, as
  TsoMem does), and at the sfence marker it is the fetch (`fiArm = false`, `itv` kept, as TsoMem's announce arm keeps
  it).  `pfStepTso` TAKES these two facts as hypotheses ((c)/(d), `PfStepTso.lean:322-325` [R20.s5]); W4's F5 must discharge them
  at every hart barrier/announce node — and a `pfRunST` step list (`st`) alone cannot: it has no monad, and the pf state's
  `Ibch` records the announce but not later fetches.  *Tiny example.*  Hart 0 executes `sw` (store to `a`), `fence.i`,
  then jumps to `a` (what `exec` does with fresh user text).  The `fence.i` cycle's labels: `LInstr` (boundary) →
  `LIFetch` (the `fence.i` word) → `LInstr` (announce) → `LFence false×4` (barrier): `fiArm = true`, the shadow raises
  `itv` past the store, the later fetch of `a` sees the new text — exactly TsoMem.  An `sfence.vma` cycle: `LInstr` →
  `LIFetch` → `LFence false×4` (the marker IS the announce): `fiArm = false`, `itv` kept — exactly TsoMem.  If a model
  instead fetched AFTER announcing (say a second halfword), the barrier would see `fiArm = false`, the shadow would NOT
  raise `itv` while TsoMem does, and `viewRel` — hence `pfStepTso`'s conclusion — would fail at that step.  *Why it
  matters.*  This is the ONE Zifencei fact the theorem uses (the `exec` user-text row, §B(4)); today it is an UNDISCHARGED
  hypothesis of `pfStepTso` — if W4 cannot discharge it, M1 carries an unnamed assumption about the Sail model's cycle.
  *Options (recommended first).*  **(b) a NAMED emission-order item**: W4 F5 takes the premise "along the hart's
  `pfRunST` run, at every own `.barrier Barrier_RISCV_i` node the latest own `LInstr`/`LIFetch` step is `LInstr`, and at
  every own sfence-marker announce it is `LIFetch`", as ONE definition (`sailCycleOrder`) that becomes a premise of
  `machRunOfPfRun` and so of M1/M2's premise set, LISTED in §B(11) as a trusted item ("the Sail cycle fetches, then
  announces, then executes; `Step.lean:331-404`").  To an xv6 expert the theorem then says "…assuming the ISA model
  announces each instruction after fetching it and fetches nothing while executing it" — a statement about the ISA
  model's text, checkable by reading two pages; it omits a PROOF of that reading.  FAITHFUL (true of the Sail model;
  neither stronger nor weaker w.r.t. RVWMO/Zifencei, which are silent on in-cycle order).  Cost S (W4 F5 threads it; one
  §B(11) entry).  Unblocks F5 now.  Risk: the trusted base grows by one unproven (but inspectable) model fact; demotable
  by (a′).  **(a′) PROVE it for the hart's concrete text, after M1**: via `UCycleDefs`' equations the cycle is
  `ucDispatch` → `fetch ()` → `ucAfterFetch fr`, whose first event is the announce; the "no fetch during execute" half is
  per decoded instruction — for M1's pristine kernel text (`candKfetch`) W4 already decodes the words (the HSafe decode),
  so a per-word lemma over the instructions xv6's text contains suffices (M–L, **unverified**); the general statement over
  ALL of `execute` is XL.  FAITHFUL, no trust growth; cost M–L (text-specific) / XL (general); risk: a `SailM` residual
  invariant across nodes (the hart's `m` between the announce and the barrier) is new machinery.  **(a) a
  residual-program invariant over `try_step` for ALL instructions** (PROGRESS's (a)): FAITHFUL, no trust growth; L–XL
  (every `execute` clause shown ifetch-free); nothing else unblocked; risk: the largest Sail-syntax proof in the tree.
  **(c) a shadow redesign**: give `fence.i` and the marker DISTINCT labels (or carry the announce state in `viewRel`), so
  no `fiArm` is needed — re-opens Q7's ruling (marker = `LFence false×4`), edits the MERGED `TsoShadow.lean` (996),
  `PfStepTsoView.lean` (807), `PfStepTso.lean`, W5d's `itvOf`/`emFenceI` criterion and the graph side; and the
  marker/fence distinction AT THE NODE is what W4 knows anyway (`o` is the node), so the redesign buys nothing (b) does
  not.  FAITHFUL; M–L across merged files; risk: churn on landed Stage-1 files and a re-ruling.  *Recommendation:* **(b)
  now** (named, S) **+ (a′) as the named follow-up after M1** (demoting the item).  A ruling is needed because (b) grows
  the published trusted surface.
- **W-DMA0-route — RULED (A) [OWN.34] (rev 23; raised by W-DMA0's worker, not by a review).**  *Spec:* not a semantics
  question (the no-op itself is W-DISK-Q1 (b) [OWN.30], FAITHFUL); every option FAITHFUL.  *Plain language.*  Making
  `storeDma pa 0 w` a no-op breaks the DMA LEASE RULE's promise that a DMA write GROWS the footprint's byte histories
  (`dmaWriteLease`, `WpDevDma.lean:46`; `LeaseD.dmaWrite`, `WpDevDisk.lean:146-153`, proof `:522-560`): for `n = 0`
  nothing grows, so the rule as stated becomes unprovable — a consumer rev 22's W-DMA0 list ("`WpDevDisk.lean` (3)")
  missed.  *Options:* **(A) RULED** — the `dmaWrite` constructors gain `n ≠ 0`, discharged automatically at xv6's call
  sites (widths 1/8/2); cost S; risk — a site whose `n` is not syntactically non-zero (the fill's `(Chain.req
  c).len.toNat`, `Xv6/DiskInv.lean:2172`) needs the chain's `len` fact; **(A′) fallback** — adjust the 4 `Xv6/DiskInv.lean`
  constructor applications (`:2164, :2750, :2828, :2855`) instead; cost S–M.  Neither touches the published statement.
- **W-DISK-Q1 — RULED (b) [OWN.30] (rev 19 OPEN; W4 census (M5) [W4c]) → §C W-DMA0, a STANDALONE serial MachCSL S item
  launched NOW [R16.3]. The zero-length DMA log entry.**  *Spec (FIRST [R16.s2]; RVWMO, Sail, Zifencei, PMAs, virtio):*
  RVWMO's gmo is over "the primitive load and store operations generated by memory instructions" — a zero-byte access
  generates NONE; the Sail model in this tree has NO DMA model at all, and its own `mem_read`/`mem_write_value` take
  `width : Nat` with the Sail-source bound `0 < width` ERASED in the Lean export (docstring only: `model/Lean_RV64D/
  LeanRV64D/Mem.lean:494-496,612-614`) — Sail issues no event for a zero-byte access; Zifencei and the PMAs are silent;
  virtio 1.x: a 0-length device-writable buffer is legal and "bytes written" is then 0.  So MachCSL's 0-byte log entry
  (`storeDma pa 0 w` appends, `Lang.lean:171-173`; `ramBytes pa 0` vacuous) is a MODEL ARTIFACT, not a spec behaviour —
  (b) is FAITHFUL, (a) FAITHFUL as a program fact, (c)/(d) rejected below.  *Where it sits in the final
  theorem.*  Nowhere in the STATEMENT: it is inside the composition W4 (§B(10)) that turns a graph-realized weak run into
  a MachCSL run on which the SC tree's facts hold — specifically the disk rows F9, i.e. whether the disk device's steps
  on the two sides can be matched ONE log message to ONE log message.  *Concepts.*  Both machines keep a STORE LOG —
  the global order of writes, one entry per store, its position being the write's TIMESTAMP; W2's `R-log` says pf
  message `k` IS the TsoMem store at timestamp `k+1`, and W8/W11 consume that identification.  A virtio READ request
  tells the device "write `len` bytes of sector `s` into my buffer"; MachCSL's device performs that as `dmaWriteIf …
  r.buf n …` (`Virtio.lean:488-492`) → `storeDma pa n w` (`Lang.lean:172-174`), which APPENDS a log entry for ANY `n`,
  including `n = 0` (`ramBytes pa 0` is vacuously true).  The pf device program emits a memory EVENT per node, and a
  store event must carry a non-empty payload (`DmWf`, the WeakMem store arm) — so at `len = 0` pf emits NOTHING.
  *Concrete example.*  A (hypothetical) driver publishes a READ chain whose data descriptor has `len = 0`: MachCSL's
  log grows by one empty entry (every later timestamp shifts by one), pf's does not; the next hart store sits at
  timestamp `t+1` on one side and `t` on the other — `R-log` is false from then on and W4's simulation has no matching
  step.  xv6 NEVER does this: `virtio_disk_rw` sets `desc[idx[1]].len = BSIZE` (1024), a constant store.  *Options.*
  **(a) a W4 HYPOTHESIS "every chain the MachCSL device fetches has `len ≠ 0`" (E-S7, HSafe's sibling), discharged by
  W5 from the SC tree** — to an xv6 expert the theorem then says exactly what it says now (the hypothesis is TRUE of
  xv6 and is discharged, not published); it omits nothing; FAITHFUL (a program fact); cost: a NEW SC-tree EXPORT in the
  `mmOk` idiom ("the device invariant's fetched chains have `len = BSIZE`" — the driver proofs `ProofVirtio*` establish
  it for the published chain, `diskGeom`-style; S–M, **unverified**) + its threading through W5 (S); risk: the export
  must be stated over MachCSL's REACHABLE states from boot (like HSafe), and F9 cannot finish before it exists.
  **(b) RULED [OWN.30] — MachCSL: `storeDma pa 0 w` is a NO-OP (no log entry) — one arm in `Lang.lean:171-173`** — the
  theorem says the same; omits nothing; FAITHFUL (the Spec line); cost S, SERIAL on the MachCSL lane (`Lang.lean`, the
  `WpDma*` rules' proofs where `storeDma` unfolds, `mmOk_storeDma :862`, the `Vtest` twins and the two weak-side rows —
  the full list in §C W-DMA0; `Dev/Virtio.lean` and the driver proofs UNTOUCHED, since the device still CALLS
  `dmaWriteIf` and only the memory model drops the empty append) — **run as its OWN S item NOW (§C W-DMA0), NOT folded
  into W-RSV [R16.3]**: F9 needs the change LANDED to prove `R-log` across a 0-length DMA write, and W-RSV waits for M1
  which waits for F9 — folding would cycle; risk: one `Xv6`-cone rebuild on the serial lane (free until W-RSV).  **(c)
  the pf program emits a 0-byte store** — NOT expressible (`DmWf`/the WeakMem store arm require a payload; lifting that
  re-opens T1), rejected.  **(d) relax the log identification to tolerate empty entries** — a non-position-preserving
  log map, WEAKER chain, breaks W8/W11's consumption; rejected.  *RULED as recommended:* **(b)** — it removes a model
  artifact instead of importing a driver fact, costs S, and keeps `Dev/Virtio.lean` and every driver proof untouched
  (the merit [OWN.29] named for (a)).  Neither option touches the published statement; the choice was cost and lane only.
- **W-DISK-Q2 — RULED (a) [OWN.31] (rev 19 OPEN; W4 census (M4) [W4c]; CONFIRMS [OWN.29]'s wording "completion
  isr/usedIdx folded into the used-idx write"). A RAM store that moves the fabric, and W13's `gfDev` text.**  *Spec
  (FIRST [R16.s2]):* RVWMO/riscv.cat have NO device-internal events; the Sail model has NO device/DMA model
  (`MachCSL/Dev/*.lean` is the only device text in the tree); Zifencei and the PMAs are silent; virtio 1.x: the device
  writes the used index and MAY then send a used-buffer notification (sets the ISR bit) — a delay between the two is
  ALLOWED, so fusing them is STRONGER than the spec (fewer device behaviours), MachCSL's named choice (§B(11) (i)).
  *Where it sits in the final
  theorem.*  In `xv6ConfS` (§A(†)), the published theorem's CONFORMANCE premise: its text says which row items are fabric
  transactions (`gfDev`; rev 19: "the I/O EVENTS in fabric order", `gisIo (i,k) ↔ (i,k) ∈ gfDev`; now the [R22.2] disjunction [R23.2]) and (R3) orders those events as
  the fabric serializes them.  *Concepts.*  The FABRIC is the devices' state (UART/PLIC/virtio registers and ISR
  lines); MMIO accesses and device-thread moves change it and are `LIo` graph EVENTS (D38/D47); RAM stores enter the
  store log and change no fabric.  MachCSL's virtio COMPLETES a request in the SAME transition as it writes the used
  index into RAM (`dmaWriteStep … complete`, `Virtio.lean:552-555`: `isr` raised, `usedIdx+1`, in-flight removal) — so
  a hart reading `InterruptStatus` or the PLIC sampling source 1 sees the interrupt exactly from that write on.  The pf
  program today writes the index as a plain RAM `DWrite` and moves the fabric LATER at a separate COMMIT event.
  *Concrete example.*  Device writes `used->idx`; before its COMMIT, hart 2 (in `devintr`) reads `InterruptStatus`
  (`Virtio.read`, `offInterruptStatus`): MachCSL answers "used-buffer interrupt pending", pf answers 0 — a divergence
  no simulation relation can absorb (the PLIC `sample` of the virtio line is itself a step the one-row run can take in
  the window) — census (M4), UNCONDITIONAL.  *Options.*  **(a) RULED [OWN.31] — [OWN.29] as worded: the pf
  used-idx write carries the completion's fabric delta (`pdiskProg`'s used-idx node is a `DWriteDev` whose `g` is
  `complete`, §C W-DISK MECHANISM [R16.1])** — to an xv6 expert the theorem says "the device's interrupt becomes visible
  with its used-idx write, as the model of record has it"; it omits the spec-allowed delayed notification (already
  omitted by MachCSL); STRONGER than the spec, EQUAL to MachCSL — no NEW named item, §B(11) (i)/D51 cover it; cost:
  W-DISK (included; PLUS the `pdevOk` mechanism — the RAM store that moves the fabric needs a STATE-AWARE `pdevEv` and
  the restated devfree lemmas, S–M [R16.1]) + **W13 (I) TEXT and PROOF**: `gfDev` lists the FABRIC TRANSACTIONS —
  "`(i,k) ∈ gfDev ↔ (gisIo (i,k) = true ∨ dvi k ≠ dvo k)`" [R22.2] (I/O events by CLASS; the endpoints off `hartConff`,
  `Fab.lean:239-262`; the request's fabric-moving `DWriteDev` stores — status, used element, used idx, the IN fill with
  `:526` — are the non-I/O members, NOT only the used-idx store as rev 20–25 wrote); (R3) ranges over `gfDev` members (so it
  orders those RAM stores among the fabric transactions [R23.2] — ISA-wise a RAM store gets rule 4/rule 14 order anyway; the cross-row `gfBefore` arm is the
  only addition and it is REALIZATION-NECESSARY on the one-row model as (R3) already is); (L)'s anchors unchanged;
  **[R16.1 (iv)] the (I) delta is M, NOT "S–M text with no proof impact"**: the label-based `isDevBlock` clause
  (`Fab.lean:533`) and its `hblkQ` consumers (`:318-503`) change SHAPE, since `lbIsdev`/`emDev`/`isDevBlock`
  (`:119-152`) cannot see a fused `LStore` from its label; risk: the trusted-surface text `gdexecQconfT`/`xv6ConfS` gains
  a sentence (reworded [R22.2]: "the device's request-service RAM stores are fabric transactions; the used-idx store raises
  the interrupt"), reviewed against `hemitf`'s two endpoints
  (`:239-260` already carry `dvi`/`dvo` per row item, so the encoding is free).  **(b) keep a separate COMMIT and SPLIT
  MachCSL's fused transition into write-then-complete** — the theorem then admits the spec's delayed notification
  (FAITHFUL direction) but re-opens the SC virtio DEVICE INVARIANT and driver proofs that rely on the fusion (the
  `Virtio.lean` comment: "the store that publishes the index is the step at which the request leaves the in-flight
  map, `usedIdx` advances and the interrupt is raised" — the invariant is stated at that fused step); XL-adjacent,
  violates [OWN.29]'s "driver proofs untouched"; not recommended.  **(c) keep both as they are and make `R-dev` tolerant
  of `isr` in the window** — the simulation FAILS at an `InterruptStatus` read or PLIC sample in the window (the
  example); rejected.  *RULED as recommended:* **(a), as [OWN.29] already worded it**; the W13 consequence (`gfDev` =
  I/O events by class + fabric-moving stores; three to four RAM stores per request among them [R22.2]) is CONFIRMED and written into §A(†) and §C W13 (I); W-DISK and, after it, W13
  (I) proceed on (a).
- **W-DISK-Q3 — RULED (a) [OWN.32] (raised by R16 [R16.1]; the plan could have decided it, but it changes `gfDev`'s
  membership and the one-row artifact D51, so it was put to the owner). How the device's mid-burst fabric READS and the
  ring POP are encoded.**  *Spec (FIRST):* the RVWMO chapter, riscv.cat and the Sail model have NO device-internal events
  (Sail has no device/DMA model; `MachCSL/Dev/*.lean` is the only device text); Zifencei and the PMAs are silent; virtio
  1.x says the device reads the available index, the ring entry and the descriptors, and after writing the used index
  MAY notify — it says NOTHING about when the device re-reads its own configuration registers.  Every option is beyond
  the spec's silence (device-MODEL text, D45/D49).  *Plain language.*  The pf disk program must now behave like MachCSL's
  `serve`, which re-reads the device state (`DevM.get`) and tests it (`DevM.guard`, the guards of `dmaWriteIf`/
  `dmaWriteStep`) at several points; in the pf machine every step carries ONE label, and the tree's invariant `pdevOk`
  (`WeakPromiseFact.lean:613-614`) says a step NOT labelled `LDev` neither changes the devices' state nor depends on it —
  a "quiet" step is fabric-blind, which is what lets the realization replay quiet stretches at ANY fabric.  *Tiny
  example.*  The disk has popped request `h` and is about to write the used index when hart 2 writes the `QUEUE_SEL`/
  `STATUS` registers (`Virtio.write`); MachCSL's `dmaWriteStep` re-checks `s.cfg = c` at the write and, failing, SKIPS
  the write (`Lang.lean:574`); a pf program deciding from a START snapshot would write anyway — the two diverge unless
  the pf write also reads the CURRENT fabric.  *Definitions.*  FABRIC = the devices' registers/ISR lines (`Efab`); `LDev
  kind base vs` = the pf label for a fabric-touching step, projected to the graph event `LIo` under W13 (I); `gfDev` = the
  list of fabric TRANSACTIONS — I/O-class events by class, plus fabric-moving stores — in fabric order ([OWN.31][R23.2]); (R1)–(R3) = the platform assumption `ioResidueGmo`
  (a row's RAM accesses are gmo-before its I/O events, I/O events gmo-before its later RAM writes, I/O events ordered as
  the fabric serializes them — `GraphFabResidue.lean:84-99`); D51 = the one-row device model, in which the disk's DMA
  accesses and the device threads' moves share one row and so one po.  *Why it matters.*  Nothing in the published
  CONCLUSIONS changes; what changes is how many device-internal events enter `gfDev`/(R1)–(R3) — the TRUSTED-SURFACE
  text — and whether D51 couples more device-internal steps to the row's DMA accesses.  *Options.*  **(a) RULED —
  guards folded into the fabric-moving writes (`DWriteDev`), the pop as ONE `LDev .dev` step, no pure re-read node**:
  concretely, `pdiskProg` gains the node `DM.DWriteDev pre g pa bs k` — with STATE-DEPENDENT `pa`/`bs` [R18.4]: the read
  of `cfg`/`usedIdx`/`cacheView` is INSIDE the fabric-moving write, not a re-read node, so within this ruling — whose arm
  reads the current fabric and either writes and moves (`g = some s'`) or skips (`g = none`) [R16.1-alt] (a folded
  `DevM.guard` that fails ABORTS the burst — §C W-DISK FOLDING RULE [R17.1][R18.3]), and the `seen+1` pop is a separate
  `LDev .dev 0 []` step (which also re-snapshots `cfg` as `serve`'s `get :522` does [R18.4])
  after the ring `DRead` (MachCSL's guard-pop is a separate step, `Virtio.lean:576-578`); the graph gains exactly one
  `dev` event per request (the pop) beyond today's START (COMMIT retired) — STRONGER than the spec only by (R1)–(R3) on
  that event (D51-class, device-internal: "the DMA reads of the avail index and ring are gmo-before the pop"), EQUAL to
  MachCSL's step structure; cost: inside W-DISK (S–M over [R16.1]); unblocks W4 F9's 1 → 2 pop match and `fork` 1 → 0;
  risk: none beyond [R16.1].  **(b) a pure fabric-READ node labelled `LDev .dev` with `d' = d`** — every config re-read
  becomes a graph event: STRONGER (more (R1)–(R3) coupling, more `gisIo` events that are NOT fabric moves — members by class under
  "`(gisIo ∨ dvi ≠ dvo) ↔ gfDev`", the form (a) now carries anyway [R23.2]); cost +S on (I) text; no benefit over (a).  **(c) a
  pure fabric-READ node labelled `LSilent` with a STATE-AWARE `pdevEv`** (rev 19's (M9) `DGet`, repaired) — NOT a graph
  event, EQUAL to MachCSL; but the devfree-emission lemmas (`emDevfree` is label-based) need the "no START ⇒ no burst"
  invariant of [R16.1] (ii) to cover these nodes too; cost +S–M; risk: a fabric-DEPENDENT step invisible to the emission
  is exactly the shape `pdevOk` exists to exclude.  *RULED as recommended:* (a).
- **W-DISK-Q4 — RULED (c) [OWN.33] (raised by R17 [R17.4]; it changes the published trusted surface, so it was put to
  the owner). The pf disk agent serves one request at a time.**  *Spec (FIRST):* the RVWMO chapter, riscv.cat and the
  Sail model in this tree have NO device-internal events (Sail has no device/DMA model; `MachCSL/Dev/*.lean` is the only
  device text); Zifencei and the PMAs are silent; virtio 1.x (block device, split virtqueue) lets the device process
  requests in any order and complete them by writing used elements in any order — interleaved service and out-of-order
  completion are spec-LEGAL.  *Plain language.*  A disk may be asked for several blocks at once (xv6's log writes
  several blocks; `bio` can have more than one request pending).  Real and modelled devices (MachCSL forks one `serve`
  task per request, `Virtio.lean:579`) work on them concurrently and may finish a later one first.  The pf disk program —
  the device half of the published theorem's conformance premise — reads one request, completes it, and only then looks
  at the next (`pdiskProg`'s single residual program, `WeakEvInst.lean:485-488`; `virtioProg` `VirtioProg.lean:606-623`).
  *Tiny example.*  Hart 1 publishes request A (write block 5) then B (read block 7) and notifies; MachCSL's device may
  fetch B, DMA block 7 into B's buffer and raise the interrupt for B before A's status byte is written, so the driver's
  `virtio_disk_intr` wakes B's sleeper first; the pf device never produces this interleaving, so a graph exhibiting it is
  NOT in the published quantifier.  *Definitions.*  BURST = one START … completion span of the pf disk row; `pdiskProg` =
  the pf disk agent's step relation; `serve` = MachCSL's per-request device task; `xv6ConfS` = the conformance premise
  naming each row's program; TRUSTED SURFACE = the text a reader must accept, §A(6); W4 = the simulation pf ⊆ MachCSL; M2 =
  the unpinned internal sRVWMO milestone.  *Why it matters.*  Nothing in the published CONCLUSIONS changes; the QUANTIFIER
  omits spec- and model-legal device behaviours, which an xv6 expert will ask about ("does your device complete out of
  order like QEMU?").  *Options.*  **(a) keep the sequential pf program and NAME it** (§B(11) (viii)) — STRONGER than
  virtio and than MachCSL (excludes the interleaving above; in practice: the theorem says nothing about runs where the disk
  reorders); sound for W4; cost 0 (text); unblocks W-DISK as planned; risk: a reader may judge the device model
  unrealistic for multi-request workloads (xv6's correctness does not depend on order, so what is omitted is device
  behaviour, not kernel behaviour).  **(b) a concurrent pf disk agent** — `pdiskProg` holds a LIST of residual programs
  (one per popped request), a step picks any; `R-dev`/`poolRel` map each to a MachCSL `serve` task — EQUAL to MachCSL
  (interleaving admitted, completion order free), still STRONGER than virtio only by (R1)–(R3)'s one-row coupling (D51);
  cost M–L inside W-DISK (the `DM` list, `ediskStep`'s arms, `WeakEvDisk`'s per-node rules re-indexed) + M in W4 F9 (the
  `13+k` thread map becomes real; the rev-21 single-burst invariant (dropped by [R21.3 (b)]) is moot and [R17.1]'s abort does real work); unblocks a more
  credible device model; risk: W-DISK grows toward XL and delays F9/M1.  **(c) RULED — (a) now, (b) as a NAMED follow-up
  after M2**: the published statement's SHAPE is the same either way; (b) later replaces the pf device model under it.
  *Recorded:* (a) alone, (b) now (rejected: M–L on the critical path to M1).
- **Q-W5dG-slot — RULED [OWN.26] (G0 review item 1; engineering, every option FAITHFUL to the report's INTENT)**: the
  slot `emZifencei` checks a fetch at is `GraphFetchSpike.emSlot em.emItems n` (the tag of the first row item at/after
  `n`), NOT "#row items before `n`" — `HEpair` emits two row items per slot, so the count mis-numbers after an exclusive
  pair (WEAKER on (Z2), STRONGER on (Z3) — §B(4)(iii)).  Recorded: the report's literal (rejected).
- **Q-W13E-seq — RULED (a) [OWN.27] (`PROGRESS-W13E.md`; scheduling only, the published statement unchanged)**: the
  `projLbl .LDev → some (.LIo …)` flip, `lblRealizes*` and the `lbAdmin` drop of `.LDev` MOVE from (E) into (I) (next to
  `MStepIo`/`WPIo` and the `hblkQ` deletion); the `False` `LIo` shape arms flip in (I)/(M); next steps (T) then (M).
  Spec standing: NEUTRAL — until (I) lands the graph omits I/O events, the pre-(E) state, not a new weakening.
  Recorded: (b) pull (I)'s T1 part into (E) — "(E) + most of (I)", L–XL; (c) flip `projLbl` for `rd`/`wr` only — D49
  (a) wants `dev` events too and (1) still blocks it; both rejected.
- **W1b-hist-Q — RULED (A) [OWN.28] (not a memory-model question)**: the pid history exported across an era's forks
  is the FORK-ONLY joined history `AllocprocTrace.forkHist F k` (well-formed, below `niHist F k`, containing every fork
  citation ⇒ live pids distinct across forks), in `Xv6/AllocprocTrace.lean` only — DONE.  Recorded: (B) `pidHistWf` of
  the FULL joined `(niHist F k).pev` — NOT derivable from the NI conclusion (non-fork citing rows never read `ι.pev`),
  would need a new ledger row (M, serial on `NiLedger`).
- **E-D1 — RULED (a) [OWN.29] (W4 census; RE-ASKED with full context, the first answer (b) superseded). The disk
  model.**  *Spec:* virtio 1.x (§C W-DISK: used `len` = bytes written; a driver MUST NOT issue FLUSH unless `F_FLUSH`
  is negotiated — [R16.5] xv6 CLEARS it, so the device's answer is UNSPECIFIED and both models' choices are vacuous;
  malformed chains unspecified, driver MUST NOT; notification MAY follow the used-idx write); RVWMO/riscv.cat/Sail/PMAs
  silent on device threads.  **(a) RULED — align the weak-side `virtioProg` to MachCSL's `serve`** (one 16-byte
  descriptor read, one 8-byte used element with `usedLen`, `statusOf` incl. FLUSH OK (a choice on unspecified
  behaviour), no writes on malformed chains — stall, the completion folded into the used-idx write, `seen+1` at the
  ring read, cache-overlaid data view) — MORE FAITHFUL to virtio than today's pf; verified driver proofs untouched;
  L–XL (§C W-DISK, with (M5)–(M9) and the three sub-questions above, all RULED [OWN.30]–[OWN.32]).  Recorded: (b) align MachCSL's device to `virtioProg` — re-opens the SC virtio proofs (XL) and is LESS
  faithful (wrong used `len`) — the owner's FIRST answer, superseded on re-ask; (c) relax `R` to agree up to the
  used-`len` bytes with a non-position-preserving log map — WEAKER chain, breaks W8/W11; (d) premise "no disk burst" —
  vacuous for the target (every run reaching user code reads the disk).
- **G2-Q — RULED (a′) with BOTH components, CLOSED [OWN.20][OWN.21][OWN.23] — LANDED (W-COH, 2026-10-11): the own-store footprint `coh` RESET
  ([R11.1], CONFIRMED [OWN.21]) AND the FOREIGN-authored-source-only stamp ([R11.1-alt], RULED [OWN.23], load-bearing
  for (9d)). Footprint coherence stamps (G2): which `coh` stamp does TsoMem (and the shadow) use?**  History: [OWN.17]
  "(a)" predated [R10.1]; [OWN.20] "(a′) as worded in rev 14" predated [R11.1], which showed that wording STRONGER than
  riscv.cat; [OWN.21] confirmed the RESET only; [OWN.23] ruled the foreign-only component after R12 showed it
  LOAD-BEARING [R12.2].  **Spec** [R11.s4]: RVWMO
  rules 1–3 / riscv.cat rule 2 `([R];po-loc-no-w;[R]) \ rsw` (`gppo2`, `AxGraphCat.lean:151-156`) orders two same-hart
  reads of a common BYTE only when they return DIFFERENT writes AND **`po-loc-no-w`: no write to that byte, by ANY
  instruction of the hart, lies po-between** (`gppo2`'s conjunct `∀ w v, gwritesByte G w a v → gpo e1 w → gpo w e2 →
  False`) — per byte, nothing across a footprint; rule 1 orders a read before a po-later same-byte WRITE (`gppo1
  :146-147`, `M;po-loc;W`); load-value makes a hart's own po-earlier store visible at ANY gmo position (`gvisible`,
  `Graph.lean:236`: `gmoLt ∨ gpo`), so there is NO `W;po-loc;R` ppo and an own store carries no gmo constraint for a
  later same-source read — store-buffer forwarding is legal; "Memory Model Primitives": a misaligned access is a set of
  byte operations (N10 out of scope); Sail: `mem_read` per access, no coherence state (external); Zifencei/PMAs: silent.
  **TsoMem today** (§0 F1 (iii), three components): stamps the WHOLE footprint with `tvn` (`HRead.afterLoad`,
  `TsoMem.lean:268`; `cohOk :263` footprint-WIDE, checked at `Lang.lean:365`); the stamp SURVIVES the hart's own store
  (`MState.store` touches `hr` only by `clearAcq`, `Lang.lean:152`); own-sourced bytes are stamped (own stores are
  visible at any view, `HEnt.visible :116-118`) — STRONGER than rule 2 (`g2Tso`).  **Options** (recommended first):
  **(a′) CORRECTED — MachCSL: `afterLoad` stamps `coh a := max (coh a) t_a` for FOREIGN-sourced bytes only
  (`e.tid ≠ hartAgent cpu`), own-sourced bytes (forwarded OR below the view) UNSTAMPED, and `MState.store` RESETS
  `coh a := 0` on its footprint** — FAITHFUL: exactly rule 2 with BOTH exemptions (same source; `po-loc-no-w`) plus
  load-value's own-store visibility — the THREE-case derivation of §B(10), graph-only; the reset is per byte, so an own
  store to PART of a footprint exempts only those bytes (as `gppo2` does); keeps TsoMem's documented CoRR
  (`relaxed-rr.md`) for foreign-written bytes; cost [the spike's "re-opens `cohOk` users" corrected: `cohOk` has ONE
  use, `Lang.lean:365`]: `TsoMem.lean` (+ `HRead.resetCoh`), `Lang.lean:147-153,365-367`, `mmOk_afterLoad`/`mmOk_store`
  (`Resources.lean:788-840`), the load rules `Wp.lean:1257-1282,1729-1745`, `WpAtomic.lean:509-530`,
  `WpSmodeFenceFloor.lean:92-119,239-260`, `UIcache.lean:233-249`, the store rules' `clearAcq` sites (`Wp.lean:1337,
  1363`, `WpAtomic.lean:188,202`) — 7 MachCSL files, mechanical (NO Iris resource exposes `coh`; the `swp` statements
  the Xv6 cone consumes never mention it) **+ `Weak/TsoOfPf.lean` (`tsoAfterLoadCoh :171-173` restated, G2 docstrings
  `:14-16`, `:212-214`) and the `Vtest` twins (`XState.lean:234-256,283-292`) — both OUTSIDE the cone build, so the
  brief builds them explicitly [R14.1]** — S–M, SERIAL on MachCSL (W-COH); W11 (iv) graph-only (M).
  **(a′) RESET ONLY — the [OWN.21] state alone** — STRONGER: excludes §B(10)'s `m0`/`w_c'` candidate (cat-consistent,
  no TsoMem schedule), so (9d)'s hull realization has a HOLE unless a W8 TRANSPORTED census excludes the shape (M,
  **unverified**) — not taken [R12.2].
  **(a‴) MachCSL: DROP the coherence floor** (`afterLoad` = `rv := max rv tvn` only; `cohOk` and the `coh` field go) —
  WEAKER than rule 2 on the strong model (TsoMem then admits CoRR violations), SOUND for the composition (it needs
  only TsoMem ⊇ realized runs; no proof consumes `coh`), S, the same 7 files, deletions; `F = tv_S`, (★)'s `coh` part
  vanishes, W5b′ S and W11 (iv) S–M [R10.s4]; changes TsoMem's documented semantics — the smaller trusted surface.
  **Rev 14's (a′) — "stamp when `t_a ≤ tvn`, no reset"** — STRONGER, REJECTED [R11.1][R11.1-alt], two defects: (1) a
  per-byte CoRR floor that OUTLIVES the hart's own store (hart A `lb a` = `r_prev` from foreign `w`, `sb a` = `m`,
  `lh (a,b)` = `r` reading `a` from `m` and `b` from foreign `w_b`; hart B `w_b, w_b', w`; gmo `w_b <gmo r <gmo w_b'
  <gmo w <gmo r_prev <gmo m` is cat-consistent — rule 2 EXEMPT by `m`, rule 1 `r_prev <gmo m` ✓ — but `coh a = gwix w
  > gwix w_b'` makes TsoMem read `w_b'` for `b`; `candScaT` FALSE); (2) an own store BELOW the view is stamped at its
  position though a later same-source read may be gmo-before it (§B(10)'s `m0`/`w_c'` candidate).  **(a) as
  originally worded — "stamp each byte with ITS source timestamp"** — STRONGER, REJECTED [R10.1]: a forwarded byte's
  stamp `t_a > tvn` with footprint-wide `cohOk` forces every later OVERLAPPING load above it (hart A `sb j` = `w1`; `lh
  (j,m)` = `r1` from `w1`/foreign `w5` (gwix 10); `lh (j,k)` = `r` from `w1`/the image while foreign `w3` writes `k` at
  gwix 5; gmo `r <gmo w3 <gmo w5 <gmo r1 <gmo w1` cat-consistent; under (a) `r` is forced to view ≥ 10 and reads `w3`).
  **(b) keep TsoMem; W8 exports (vi)**: no po-ordered OVERLAPPING loads of DIFFERENT footprints on a concurrently
  written byte — FAITHFUL as a program fact (TsoMem stays STRONGER, all three components, named in F1); census M,
  **unverified**, a racy site is a STOP; W11 (iv) takes (vi) TRANSPORTED (+S–M) [R10.2]; no MachCSL change.  **(c)**
  strengthen `candSca` — NOT derivable (cat allows G2), rejected; **(d)** a footprint-coherence ppo rule in the
  published model — STRONGER than riscv.cat, violates [OWN.2], rejected.  RULED: (a′) with BOTH components [OWN.23];
  (a‴)'s smaller trusted surface recorded, not taken.
- **G1-Q — RULED (e) [OWN.17] [W2s]. The `.aq` floor debt (G1/G1′).**  Spec: RVWMO rule 5 / riscv.cat `[AQ];po` (`gacqPo`,
  `WeakRvwmoGraph.lean:214-215`): the acquire READ (the AMO's read half, `lbAq`) is ppo-before every po-later memory
  access of its hart; rule 4 covers the pair's read half for a later `fence r,*`; load-value: a later load's source is
  co-maximal among the writes gmo-before it — so the writes gmo-before the AMO ARE visible to the hart's later loads,
  and "floor = the AMO's gmo position" is what the chapter gives; NOTHING in the chapter ties a floor to the lock
  word's SOURCE timestamp (WeakMem's `max(wVrNew, t)`, `WeakMem.lean:608,834`) — the two coincide exactly when the
  log is gmo-ordered.  Sail: `execute_AMO` (`InstsEnd.lean:18663`) issues `mem_write_ea … aq`/`mem_read … aq`, the
  access kind carries the bit (`AS_rel_or_acq`, `PhysMemInterface.lean:315,364`), NO view semantics (the memory model
  is external).  Zifencei/PMAs: silent.  Options: (e) **`candScaT` — SCA at a view ≥ `tsoShadow`'s floor** (§B(10)) —
  FAITHFUL at Stage 2: DERIVED (`linCandScaT`, LANDED [R20.3]: `gppoCat6Gmo` + `grule14`, rules 2/4/5, consumed on the NORMALIZED `GD'` — NOT `linCandScaTCatT` on `GT.gtG` [R21.2]) given G2-Q (a′)/(a‴), or (b) + W8 (vi)
  transported [R10.2]; a PREMISE at M1/M2 only (restricts the candidate's log order to a gmo-extension); cost W5b′
  S–M + W11 (iv) M (S–M under (a‴)); re-opens nothing (RULED); (a) D7 (Rec):
  WeakMem's aq exclusive read takes TsoMem's view (`wVrNew := |log|`) — STRONGER pf machine; T1 `srvwmoRealizable`
  fails on G1-shaped candidates, so (9d)'s hull realization has a hole — rejected; (b) MachCSL: `afterExcl`/`store`
  floor := the read bytes' source timestamp (`Lang.lean:136,151`) — FAITHFUL direction (TsoMem weaker, = WeakMem);
  re-opens the `.aq` view receipt `viewLbAt E cpu (top+1)` (`WpAtomic.lean:166-167,225-226`; `acq_view`,
  `WpLock.lean:63`) consumed in 13 files (`Ctx.lean` 20 sites, `Lock`, `WpLock`, `Xv6/BootCarveHart`/`StartedInv`/
  `ForkretRecord`) — M–L, serial, owner-gated; unnecessary given (e); (c) (★) per load from W8's discipline — FAITHFUL
  but INSUFFICIENT: a racy byte written in `(t, top]` (`started`; rev ≤ 18 also named `panicked`, which does not exist
  in this image [W13c]) is a genuine RVWMO stale read TsoMem lacks.
- **G3-Q — RULED (a″) [OWN.17] [W2s]. DMA reads at the top vs the disk row's floor reads (G3).**  Spec: RVWMO — I/O and devices "not
  (yet) formalized"; the appendix's DEVICE sentence (§B(11b)): after the MMIO the device's memory accesses "must
  observe the effects of all accesses ordered prior to that MMIO operation" — the MP direction only, NOT "reads at
  the top"; riscv.cat: no device events; Sail: no device/DMA model; PMAs: silent.  The device MODEL of record reads at
  the TOP (`mem_view`, `DevLang.lean:20-21`; `dmaView`, `Lang.lean:189,535`) — STRONGER than the sentence, already
  named (F6); the pf disk row (`DRead` = `LLoad aq false`, `WeakEvInst.lean:491-494` [R23.s3]; `dreadAvailIdx` aq,
  `VirtioProg.lean:376`) is FAITHFUL to the sentence, WEAKER than the model.  Every closing option is STRONGER than
  the ISA; what each adds: (a″) **shape clause `candDiskLat`** (W5b′: disk-row loads `latest` per byte — `readOkD`'s
  `lat` condition, `WeakPromise.lean:183-188`) + graph twin **(R2′)** in `ioResidue` (§A(†)) + disk-row reads as (L)
  ANCHORS — EQUAL to the device model (a graph restatement of F6, realization-necessary; the only new trusted text is
  (R2′)'s one arm); cost W5b′ S + W13 (T) S + (L)/(K) M + W11 (iv) S–M; `latFree` untouched (recommended); (a) the
  spike's form: `DRead` with `lat = true` + the same twin — same executions, but FALSIFIES `pstepEvLatFreeProg`
  (`WeakEvCapstone.lean:1052`) and `lblRealizes`'s `latFree` (`AxRealize.lean:241`): 16 files (`WeakPromiseFact` 26
  sites, `WeakErase`, `WeakRvwmoConf`, the `WeakRobust*` family) — +M–L for nothing; (b) MachCSL: `dmaView` at a disk
  view with the acquire on the avail index — FAITHFUL to the DEVICE sentence, a WEAKER device model; re-opens `WpDma*`/
  `WpDevDma*` and `ProofVirtio*` (XL); (c) W8 device-ownership export making (★) hold at `F = top` — FAITHFUL on the pf
  side, INSUFFICIENT at Stage 2 (the stale-read GRAPH stays in the quantifier with no realization).  D51's one-row
  artifact extends to (R2′) (UART/PLIC moves po-before DMA reads).
- **W1-Q — RULED (c) [OWN.16]** (not a memory-model question): the counter tie `nextOf ≤ PIDMAX` and the `poolEmpty`
  export fold into W1b (`pidHistWf`; `niFitEv`/`niEntryOk`), `allocprocTraceAns` is the interim W1 (§A (b)).  Recorded:
  (a) NI-ledger-only export (M); (b) the interim forever — WEAKER at `pidPick` by the one fallback `pidPick = nextOf = 2^32-1 ∧ answer = -1`.
- **Q-W3a — RULED (A) [OWN.16]** (CSL plumbing, all options FAITHFUL): the power-thread persist twins (§C W3) — DONE;
  (B) the smaller-mask boot export (`Hboot'` returns `□ textRo E`) and (C) the XL re-size recorded.
- **D32 = Q-X / Q-W13a — RULED (a′) [OWN.12], re-encoded by D38 [OWN.14] as (R1)–(R3) of `ioResidueGmo`.**  Record:
  (a′) **the `dv → ev` arm restricted to WRITES — RULED**; (f) FAITHFUL `ioOrdF` alone — INFEASIBLE (§B(11b)); (a) the
  spike's two-way form (`W13Spike.lean:83-95`); (b) [OWN.8]'s literal acyclicity — refuted by `lbExcluded` (`:35`);
  (c) the same on the normalized graph; (d) `gdevAdj ⊆ gmo` on FOLDED blocks — excluded SC; on I/O EVENTS it is (R3).
- **D33 = Q-T / W12-Q1 — RULED (a) [OWN.13]**: tagged `rvwmoCatConsistentT`, chain on `forget GT`; (b) untagged with
  rule 12 over ctrl/translation deps NAMED a strengthening; (c) drop rule 12 — sound, the kill loses `segPinCForward`.
- **D34 = Q-U / W12-Q3 — RULED (a) [OWN.13]**: W12b `Weak/CatFloor*.lean` with W12; (b) W10 absorbs it; (c) kernel rows only.
- **D35 = Q-V / W12-Q2 — RULED (a) [OWN.13]**: `grcsc` riscv.cat-faithful (RCsc = any aq/rl on AMO/LR/SC; first check
  the decoder emits `LStore rl`/`LLoad aq` only for atomics); (b) weak rule 7 + side condition; (c) `Bad`-arm burden.  **[OWN.54] rev 42 (D35-rule7, above): riscv.cat's RCsc VERIFIED = `(Acq|Rel|AcqRel) & (EX|X)`; the decoder
  check DONE (`WeakEvInst.lean:336`); the `lbRcsc` correction = D35-fix (§C top), `grelAcqGmoC` dropped.**
- **D36 = Q-W / W12-Q4 — RULED (a) [OWN.13]**: row side condition "no plain `LLoad aq`" (true for the kernel); (b)
  change `fwdView` for aq (ripples into T1); (c) a named user-code gap.
- **D37 = Q-Y / Q-W13b — RULED (a) [OWN.12]**: "I/O accesses act as one-way fences for the issuing row and serialize
  as the fabric does — beyond FENCE i/o bits, dependencies, precise traps and the device models", QEMU TCG
  (program-order vCPUs + the BQL around MMIO) the platform, host-dependent; (b) fence-guarded MMIO — leaves
  `verified`, still needs D46 (b); (c) DROPPED: "PMA strong ordering" does not deliver (T).
- **D38 = Q-Z / Q-W13c — RULED [OWN.14] (b′)**: MMIO as an I/O-class LOAD/STORE EVENT of the row (`Lbl.LIo`, in gmo,
  ppo applies, device-supplied value); `projLbl` and the emission proofs change (accepted); realization keeps
  `execProgOk'` (§A(†), §C W13); (a) `execProgOkA` — RETIRED; (b) a tagged INERT-FENCE row event; (c) folded model + per-site representability — XL.
- **D39 = Q-W13d — RULED (a) [OWN.13]**: `xv6RvwmoSafeModuloF`/`gfexecConsistent'` retired as published forms, kept internal on normalized graphs.
- **D40 = Q-G1 — RULED (a) [OWN.15]**: emission-structural `emFenceI` + soundness lemma (M), the no-op `LFence false
  false false false` label stays; (b) distinct fence bits — perturbs Q7 and the AxSL pins; (c) a new `Wlabel` — XL.
- **D44 ([R7.4]) — RULED (i) [OWN.11] → W14.**  `kinit`'s `freerange` (`end = 0x80023b10`, `KernelImage.lean:17935`;
  `physTop = 0x88000000`, `KallocDefs.lean:71`; 32,732 page `memset`s) is 10^7–10^8 dynamic instructions — evaluation
  INFEASIBLE.  (i) **a single-execution EXISTENCE theorem** ((↑) for ONE run, not receptiveness; sized by W2's table);
  (ii) publish with "non-vacuity certified to the first UART store and first disk COMMIT only" (interim header
  wording); (iii) a reduced-RAM witness image (not the published kernel, [OWN.4]).
- **D45 ([R7.3]) — RULED (a) [OWN.16]**: one `LIo` label, `IoKind = rd | wr | dev` (hart MMIO `rd`/`wr`; pin
  deliveries, START/COMMIT, device-thread moves `dev`), one set of arms (R1)–(R3) (+ (R2′) under G3-Q (a″)).  Spec:
  SILENT — no device-internal events in the ISA (`pdiskProg :481-507`, `pdiskUart :514-520` are model-only); every
  option STRONGER than silence; (b) a separate device-side constructor — the same, +S–M.
- **D46 — RULED (a) [OWN.17] (with D50 (b): the DEPENDENCY part of (b) is nonetheless IN SCOPE as W13 (F-dep)).
  Machine-stating the I/O residue.**  Spec: the appendix gives (F1)–(F5) (§B(11b)); Sail's
  decoder gives NONE of (F1) (the i/o bits die, FIOM = 0); (R1)–(R3) are beyond both (the residue).  (a) **(R1)–(R3)
  alone; the header lists the ISA-given edges and per-arm trusted uses in prose (§B(11))** — STRONGER than the spec by
  exactly the named residue; recommended: no proof consumes the fragment; (b) W13 (F): the fence fragment `emIoFence`
  recovered from the instruction word (graph data, `gdFetch`'s style), dependency edges through `LIo` (= D50 (b)),
  trap-boundary edges, named readings (F3)/(F5); `ioOrdF ⊆ ioResidue` — the PROSE-FAITHFUL encoding of (F1)–(F5), the
  one option under which the four `fence iorw,iorw` order I/O at the graph tier; same quantifier as (a) once the
  residue holds (M–L, header-only value); (c) fabric-free realization (per-device commutation) — the only option that
  could DROP the residue (FAITHFUL), XL, fails for the PLIC's claim, NOT recommended.
- **D47 — RULED (a) [OWN.17]. How an I/O event is encoded.**  Spec: appendix — an I/O access is a load/store operation
  with a gmo position, outside load-value/atomicity; (c2) gives po-loc among overlapping I/O accesses; Sail — an
  ordinary `mem_read`/`mem_write` to an `IOMemory` address (`MachCSL/Dev/Fabric.lean:126`).  (a) **a NEW constructor
  `Lbl.LIo kind base vs` (+ payload on `Wlabel.LDev`)**: `lbRd`/`lbWr`/`lbIsR`/`lbIsW` stay RAM-only, so rf/co/fr/
  load-value/atomicity/`gmsg` and rules 1–4, 7 skip I/O BY CONSTRUCTION — FAITHFUL on load-value/atomicity, WEAKER
  on rules 1–3 for I/O ((c2)'s po-loc is not a graph edge; covered by the STRONGER (R3), so the same executions once
  (R3) holds); cost one-line arms in ~70 files (recommended); (b) the owner's literal wording — ordinary `LLoad`/
  `LStore` at an address with `ioAddr a := a < devBound` — FAITHFUL on rules 1–3 ((c2)), same executions once (R3)
  holds, but needs `¬ ioAddr` GUARDS in `gloadValue`, `greadsByte`/`gwritesByte` (else bogus `fr`/image reads at
  t = 0), `gmsg`, `candValues`, `rdOk`/`readOk`, the fence rule — a side-condition thread through the 33k-line chain,
  NOT recommended; (c) `AxDevGraph`'s separate device rows — WEAKER (no gmo position), not what [OWN.14] rules.
- **D48 — RULED (a) [OWN.17]. Rule 4 and I/O events.**  Spec: the FENCE text and the appendix's FENCE sentence — a fence WITH i/o
  bits orders I/O against RAM both ways, a fence WITHOUT them does not; Sail drops the bits (`InstsEnd.lean:
  18299-18313`, FIOM = 0), so `LFence pr pw sr sw` carries no I/O information; xv6's four `fence iorw,iorw` are
  `0x0ff0000f` (`KernelImage.lean:17301,17311,17441,17451`), read by the Xv6 proofs as `Barrier_RISCV_rw_rw`
  (`ProofVirtioDiskIntr.lean:92-99`).  (a) **`LFence` orders RAM accesses only; I/O events get NO fence edge; the
  residue covers the realization** — WEAKER than the prose (the four `iorw` fences give I/O nothing at the graph tier),
  Sail-FAITHFUL; recommended: the sound direction, consistent with (F1)/(F4) [R8.1]; (b) riscv.cat-literal: I/O events
  ordinary for rule 4 — STRONGER than the prose at every fence WITHOUT i/o bits (the locks' `fence r,rw`/`fence rw,w`
  would order MMIO), faithful only at the four `iorw` words; fewer trusted uses on the virtio path, still the residue on
  UART/PLIC; needs a `lbIsIo` disjunct in rule 4 (`gfenceCovers` keys on `lbIsR`/`lbIsW` under D47 (a)) [R8.s4].  The PROSE-FAITHFUL form is D46 (b).
- **D49 — RULED (a) [OWN.17]. The device-side fabric moves** (`pstepPlic`, `pdiskProg` START/COMMIT — after W-DISK START
  and the ring POP [OWN.32], COMMIT retired [OWN.31] —, `pdiskUart`).  Spec: SILENT on
  device-internal events; the DEVICE sentence orders a device's memory accesses only AFTER the MMIO it received; the
  UART and the virtio DMA engine are unrelated agents; a PLIC pin delivery is a trap — (F5) orders pre-trap LOADS
  only.  Every option is beyond the spec; what each adds: (a) **`LIo .dev` events in the issuing row (hart row for the
  pin delivery, row `NCPU` for the rest), under (R1)–(R3)** — adds the (R1)/(R2) coupling of pre-trap STORES to the
  pin delivery and of the disk's DMA accesses to UART/PLIC moves (D51): STRONGER than the spec, a one-row-model
  artifact; one mechanism, the block-folding defect cannot recur (recommended for this plan); (a′) [R8.2c] `dev`-kind
  events from `pdiskUart`/`pstepPlic` carry (R3) ONLY — fabric order alone (STRONGER than silence by (R3) only, the
  closest option), but NOT realizable in the one-row model (the trace must respect the row's po): costs the `WeakEv`
  row split of D51 (b), M–L, owner-gated; (b) admin-only via rev 9's `execProgOkA` for `dev` kinds — what (a) adds,
  through two mechanisms, +L; (c) leave them folded — STRONGER still: `scDevUnrealizable` recurs for pin deliveries, NOT acceptable.
- **D50 — RULED (b) [OWN.17], the NON-recommended option: EXTEND the taggers (W13 (F-dep), §C).**  Spec: appendix
  (c1) — ppo 9–13 apply to I/O accesses (addr/data/ctrl into an I/O STORE, addr into an I/O LOAD); a ctrl→I/O-LOAD
  edge is NOT ppo under either reading (the PMA non-idempotency "no speculative access" text is a reading to be NAMED);
  this tree — the taggers `dstep`/`dstepT` are inert on `LDev` (`WeakRvwmoConf.lean:497-499`, `AxDeps.lean:461-463`),
  `pnodeStep`'s MMIO arms emit `LDev` without the read set the RAM arms put in `asrc`/`vsrc` (`WeakEvInst.lean:
  300-304,335-338`; `Eitem = Wlabel × Option Nat`, `Conf.lean:424` — the tagger reads sources from the LABEL).
  **(b) RULED**: addr/data/ctrl → I/O store and addr → I/O load edges, provenance OUT of an I/O load, NO ctrl →
  I/O-load edge (= the existing `LLoad`/`LStore` arm shapes, `dedgesR`/`dedgesW`, `AxDeps.lean:445-451`) — FAITHFUL
  to (c1) ONCE the graph side admits the edges ([R38.1], §C W13 (F-dep) (0): the emission shapes alone are not a model [R38.s5]); M–L [R38.3];
  coverage vs (R1)–(R3) in §C W13 (F-dep) (one class beyond the residue: I/O-load →addr→ RAM load).  (a)
  taggers inert — WEAKER (sound; (R1) subsumes the in-edges, (R3) same-row I/O→I/O order), was recommended.
- **D51 — RULED (a) [OWN.18]. The one-row device model.**  Spec: RVWMO/riscv.cat/Sail are SILENT on device threads; the
  DEVICE sentence orders a device's memory accesses only after the MMIO it receives; the UART and the virtio DMA are
  unrelated agents.  (a) **keep ONE device row (`pstepDisk`, `WeakEvInst.lean:522-526`) and NAME the (R1)/(R2)
  coupling of DMA accesses with UART/PLIC moves as a model artifact** — STRONGER than the spec (excludes a DMA write
  delayed past an unrelated UART byte); zero cost (recommended for this plan); (b) split `pdiskUart` into its own
  row(s) so (R1)/(R2) bind only START/DMA/COMMIT — FAITHFUL to the spec's silence; `xN` (`Capstone.lean:94`), a new
  `pstepEv` row kind and `epsInit` entry change; M–L, owner-gated, after W13 (E).
- **D52 — RULED (a) [OWN.18]. Rule 5 over I/O.**  Spec: appendix (c1) — acquire/release annotations do NOT order memory↔I/O
  (quoted in §B(11b)); the graph's `gacqPo` (`Graph.lean:214-215`) orders an acquire READ before every later `gmem`
  event, which under W13 (M) includes I/O.  (a) **keep `gacqPo`'s `gmem e2`** — STRONGER than the text, but subsumed by
  (R1) (an acquire read is a RAM access po-before the I/O event): no coverage change, no new trusted use; zero cost
  (recommended); (b) add `¬ gisIo e2` to `gacqPo` — FAITHFUL; touches the cat arms and `cyBackwardNotAq` (`Cert4.lean:587-590`), S–M.
- **D41 = Q-G2 — RULED (a) [OWN.16]**: the superset contributor set "everything the hart wrote or read before
  `fence.i`" — retime-invariant, stronger than TsoMem's `itvPost` set (`WeakInterp.lean:378-384`), ≤ the Zifencei text
  ("a subsequent instruction fetch … will see any previous data stores already visible to the same RISC-V hart";
  RVWMO has NO fetch model; Sail's `fence.i` is the bare `Barrier_RISCV_i`, `InstsEnd.lean:18295-18297`) — SOUND [R8.1];
  (b) the exact `itvPost` set (aq reads, `pr∧sr`-fenced reads, address views, own stores) — equal to TsoMem's, +M.
- **D42 = Q-G3 — RULED (a) [OWN.18]. Where the fetch fragment `F` lives.**  Spec: an ENCODING question, the ISA is
  silent — every option FAITHFUL.  (a) **a `Gdexec.gdFetch` field, mirroring `gdDeps`, so hull, retime and acyclicity
  carry it for free**; (b) a parameter of `racyD`/`cycleKill` — the ~31 constructor sites untouched, 16 files' statements change.
- **D43 = Q-G4 — RULED (a) [OWN.18]. Pinned milestones.**  Spec: engineering only, no semantics — every option
  FAITHFUL.  (a) **keep `pstepPin`/`fetchPin` as the M1 kernel-text instance (`fetchPinCutOk`) until M2 lands**; (b) delete after G6.
**Standing (recommendations provisional unless RULED).**
- **D1 / D2 / D12** — RULED [OWN.1][OWN.2][OWN.4]: machine tier (Theorem 2 = validation); FULL RVWMO (the TAGGED cat
  model, D33), sRVWMO/pinned forms internal; the `verified` fork in the header.  **D2′.** If (9d) is too large: (Rec)
  hold publication; (b) the promising machine with "Promising-RISC-V ≡ RVWMO" trusted — not cat, violates [OWN.2].
- **D3.** (Rec) trace-level predicate via `xv6NiPhi` beside the Iris contract; (b) contract only.  **D4. W6** — (Rec)
  SKIP; (b) de-risk W8's export.  **D5.** (Rec) W3 first.  **D6.** (Rec) Theorem 2 = audited validation; note S.
  **D7. W2 failure mode — RESOLVED-BY-REDESIGN [W2s]** [R2.3][R3.s5][R9.1]: the STOP fired (G1–G3, §B(10)).  The
  suspects' marks, confirmed by the spike: (i) parked release fence — WeakMem's `wRelp` (`WeakMem.lean:684`) FAITHFUL
  at the fence, TsoMem's no-op (`TsoMem.lean:356-364`) STRONGER globally via rule 14 — CLOSED, a 0-step match; (ii)
  `wRes := none` at a non-trivial fence (`:688`) vs TsoMem keeping it (`Lang.lean:155-163`) — BOTH FAITHFUL (Zalrsc:
  invalidate at any time; FENCE does not cancel), VACUOUS on shaped runs; (iii) tearing — D20, CLOSED by `candSca`;
  (iv) the `.aq` floor — TsoMem's WRITE-position floor (`Lang.lean:136,151`) STRONGER than WeakMem's read-source floor
  (`:834`, FAITHFUL to the pf encoding), REFUTED as "off by one": off by `top − t` → **G1-Q**; (v) NEW footprint
  stamps → **G2-Q**; (vi) NEW DMA at the top → **G3-Q**.  The (Rec)/(b) dichotomy (move WeakMem toward MachCSL vs a
  MachCSL change) is superseded by the per-gap option sets above (G1-Q, G3-Q RULED; G2-Q RULED (a′) corrected); the table's
  marks column is W2's ACCEPTANCE [R9.s4][R10.s5].  **D8 — RULED (a) [OWN.19]**: "exactly 8 harts, all booted" named;
  (b) "≤ 8" (MachCSL change).  **D9. Panics — RULED (a) [OWN.19]**: not excluded, stated; (b) "no `panic:` bytes in
  the UART trace" (M–L; meaningful once W13 lands).  **D10.** (Rec) W1 via `xv6NiPhi`; (b) also W1b (L, serial).  **D11.** (Rec)
  observation-level β; (b) state-level α.  **D13.** (Rec) `Weak/`, `--weak` audit over the full `Xv6` cone; (b) a
  separate lane.  **D14.** (Rec) one boot; (b) multi-era W4 (M).  **D15.** (Rec) conclusions about the realizing
  MachCSL run + "the pf run never spins in the retry arm"; (b) none; (c) weak-side `Reducible` (XL).  **D16** → D22.
  **D17.** (Rec) the header names the SC-failure model; (b) §B(11) only — shares D19's Spec line [R9.1].
- **D18** — RULED [OWN.3]: W5d (M2) and W5d-G in the target; the user-fetch witness is not buildable by evaluation
  [R7.4] → D44 (i) → W14.
- **D19 — RULED (b) [OWN.19], the NON-recommended option: a MachCSL change so dangling reservations do NOT block
  (§C W-RSV: semantics, census, W2 interaction, the fused-pair restriction, serial order after W-COH). Fused pairs /
  reservations** [R9.1].  Spec: RVWMO's atomicity axiom constrains only PAIRED (successful)
  aligned LR/SC — no store from another hart to the byte between the LR's source and the SC in gmo; Zalrsc — the SC
  "succeeds only if the reservation is still valid", a reservation is invalidated by another hart's store to the
  reservation set or the hart's own SC, and an implementation MAY invalidate it at any time (spurious failure allowed;
  only constrained loops get eventual success); NOTHING says a live reservation blocks or delays other harts' stores.
  Sail in this tree: `load_reservation`/`cancel_reservation` are no-op stubs (`LeanRV64D/Xv6Extras.lean:65-68`);
  `match_reservation`/`valid_reservation` ARE the opaques `xv6_resv_matches`/`xv6_resv_is_valid` (`:75-80`; both SC
  arms theorems, `Xv6/UserMemLrsc.lean:7-12`) — SILENT on reservation semantics; PMAs — RAM `reservability :=
  RsrvEventual`, `atomic_support := AMOCASQ` (`MachCSL/Platform.lean:253-254`), I/O `RsrvNone` (`:214,234`).  Marks:
  TsoMem's reservation serialisation (`Lang.lean:366-378,395-403`) — STRONGER than the spec (excludes the spec-allowed
  execution where a foreign store lands mid-pair and the SC fails), named in F1 (ii) — PLANNED OUT; **(b) RULED: a
  MachCSL change so dangling reservations do not block** — FAITHFUL for AMOs (the blocking window = the instruction =
  the atomicity axiom), WEAKER than Zalrsc for user LR/SC (a lost reservation's SC becomes a plain store, success by
  the opaque — TODAY's semantics already, [R11.2] (ii); sound direction), L–XL, SERIAL after W-COH (form (i-a) RULED
  [OWN.22][OWN.23]); the census (§C W-RSV) is 21 MachCSL files of blocking consumers [R11.s3] + the (i-a) thread: 16
  cycle rules in 9 files, 25 MachCSL files (35 `wp_m_*` wrapper STATEMENTS among them) + 12 `Xv6/` files [R12.1][R13.1];
  `Xv6/` NAMES no reservation except `UserretEntryPt.lean:164`'s existential frag and the two `resvName := 0` literals,
  but 8 `Xv6/` files apply cycle rules whose statements change, 3 (`ProofEntry`/`ProofStart`/`ProofTimerinit`) apply the
  bundle-free `wp_m_*` wrappers (proof-level edits), and `SpecSpin`/`ProofSpin` gain the fragment in their statements; the
  Svadu A/D LR/SC in `WpPtWalk*` is in-flight (no risk, [R11.2] (iii)); (a, was
  Rec) **`execProgOk'S`'s fused pairs — a quantifier RESTRICTION** (executions with a dangling LR or a failing SC are
  outside the theorem; STRONGER as a premise) — STAYS for failing SCs, becomes RELAXABLE for dangling LRs once (b)
  lands (§C W-RSV); (c) a user-mode fact — unavailable.  D17 shares this Spec line.
- **W-RSV-Q — RULED (i-a) [OWN.22][OWN.23] (engineering; every option FAITHFUL for AMOs). Which form of D19 (b)?**  Spec:
  Zalrsc — a reservation MAY be invalidated at any time (spurious SC failure allowed), it is invalidated by another
  hart's store to the reservation set or the hart's own SC; the atomicity axiom constrains SUCCESSFUL pairs only;
  Sail in this tree — `load_reservation`/`cancel_reservation` are `pure ()` stubs and success is the opaque
  (`model/Lean_RV64D/LeanRV64D/Xv6Extras.lean:65-80`; `SailHooks.lean`); RVWMO/Zifencei/PMAs: nothing on blocking.
  The pf twin clears `wRes` at every instruction boundary and non-trivial fence (`instrPost`, `WeakMem.lean:720-721`;
  D7 (ii)).  Options [R12.1]: **(i-a) RULED — clear `σ.resv cpu` at the instruction boundary (`hartStep .pure`,
  `Lang.lean:535`) and THREAD `resvFragAny` through the cycle rules' statements and their callers** — FAITHFUL
  (Zalrsc's "at any time"), equal to the pf twin (W2's `R-resv` exact); the machine change is one arm, all guards
  stay, `Resv`/`ResvVal` unchanged; the ghost update is the EXISTING `memModel_dropResv` (`WpAtomic.lean:49-51`); cost
  L–XL = the §C W-RSV blocking census + 16 cycle-rule statements (9 files) + 25 MachCSL files INCLUDING the 35 `wp_m_*`
  wrapper STATEMENTS + 12 `Xv6/` files (8 direct cycle-rule callers; `ProofEntry`/`ProofStart`/`ProofTimerinit` proofs
  under `wp_m_*`; `SpecSpin` statement), one `Xv6`-cone rebuild [R13.1] — BY LANE: the S-mode kernel lane's
  `wpLoop_k_*` wrappers and the user lane's `uFr`/`uResvTok` absorb the fragment (their callers stay); the M-mode lane
  has no bundle, so its wrappers change statement (§C W-RSV) — [OWN.22] ruled (i), [OWN.23] re-ruled (i-a) at rev 16's
  census (8 `Xv6/` files); **(i-b)** the same machine change with the per-hart `∃ r,
  resvFragAny cpu r` moved out of `ctxTok`/`uResvTok` into a per-hart invariant opened by the boundary rule and the
  three `swp_*_au` rules — FAITHFUL, L, a context-token REDESIGN (`ctxTokAt` 19 sites, `uResvTok` ≈ 30 mentions, every
  `ctxTok_cases/_intro` user), cycle rules, `wp_m_*`, `wpLoop_k_*` and ALL of `Xv6/` untouched — recorded; **(ii)** an `inflight : Bool` on the
  reservation, cleared at retirement, plus "an overlapping foreign/DMA store INVALIDATES a non-in-flight reservation"
  — FAITHFUL (Zalrsc's named invalidation), rev 14's design made consistent, but the SAME ghost cost as (i-a) unless
  the flag leaves `ResvVal` — and then `mmOk`'s reservation clause (`Resources.lean:781-782`) and `memModel_store_excl
  :221-224` must learn "in-flight" without a resource; +M over (i-a) (`resvName`'s sites `Resources.lean:122,433,475`,
  `Xv6/AppUnionPre.lean:89`, `Xv6/AppPreGS.lean:54`, every `resvFrag` statement) — not an escape hatch.  Rev 15's "(i)
  is L, `wpLoop_restart` re-stated over `ctxTok`, `Xv6/` untouched" was WRONG [R12.1]; rev 16's "the rest of the `Xv6`
  cone stays" was WRONG for the M-mode lane [R13.1].
  **Census DELTA — the coordinator REPORTS it (no gate [R14.s5]) [R13.1]; (i-a) stays RULED; NOT re-opened (owner, 2026-10-10).**
  *Plain language.*  Under (i-a) every "one instruction retires" proof rule must now hand over a small ghost
  permission — the hart's RESERVATION FRAGMENT (`resvFragAny cpu r`: this hart's share of the ghost cell that mirrors
  `σ.resv cpu`, the address the hart's last LR reserved, or none) — because retiring an instruction now clears that
  cell.  Tiny example: hart 0 runs `lr.w` on `x`, then its `sc.w` is skipped (e.g. a trap); before W-RSV hart 1's store
  to `x` is BLOCKED in TsoMem until hart 0 retires an SC; after W-RSV (i-a) hart 0's next instruction boundary clears
  the reservation and hart 1's store proceeds.  Rev 16 priced the proof plumbing at 8 `Xv6/` files because the S-mode
  kernel rules carry a CONTEXT BUNDLE (`kctx`, a package of per-hart ghost state that already contains the fragment),
  so the Xv6 proofs above them need no change.  The M-MODE lane (boot code: `_entry`, `start`, `timerinit`, the `spin`
  park loop — run before paging, in machine mode) has no such bundle: its 35 instruction rules (`wp_m_*`) must name
  the fragment EXPLICITLY, so the three Xv6 proofs that apply them (68 applications) are re-threaded (their
  specifications already hold the token, so only proof text changes) and the `spin` specification gains the token
  (nothing imports it but `LinkSpin`).  *Why it matters for credibility:* nothing in the PUBLISHED statement changes
  (the fragment is CSL plumbing; FAITHFUL under every form, §D D19); the delta is COST and schedule only — the owner
  ruled (i-a) "at this cost" and the cost was understated by 4 files and 35 lemma statements, within the same L–XL
  class.  *Per option:* **(i-a) as RULED** — 16 rules / 9 files, 25 MachCSL files incl. 35 `wp_m_*` statements, 12
  `Xv6/` files, one cone rebuild; FAITHFUL; L–XL; unblocks M2 after M1 exactly as before; risk [R14.s1]: one
  `Xv6`-cone rebuild (≈ 0.73M lines, `MachCSL/` + `Xv6/`) on the serial lane, and the 35 statement edits are
  mechanical but each of the 68 `wp_m_*` caller sites is re-threaded by hand.  **(i-b)** — a per-hart
  reservation INVARIANT (a shared ghost assertion any rule may open) instead of a threaded fragment: `ctxTokAt`/
  `uResvTok` redesign (M–L) but cycle rules, `wp_m_*`, `wpLoop_k_*` and all of `Xv6/` untouched; FAITHFUL; L;
  unblocks W-RSV WITHOUT the cone rebuild (the serial lane W-COH → W4 → M1 → W-RSV → M2 shortens by that build); risk
  [R14.s1]: the invariant must be openable at the `swp_*_au` rules AND the boundary rule under `wpLoop`'s mask — a new
  Iris invariant in `Ctx`, 19 `ctxTokAt` sites and 30 `uResvTok` mentions re-proved, the user-lane walker frames
  (`uResvTok`, `URunRW.lean:501-502`) included; its
  relative advantage grew by exactly this delta — RECORDED, not recommended over a standing ruling.  **(ii)** unchanged
  (same ghost cost as (i-a)); unblocks nothing (i-a) does not; risk: `resvName`'s type changes at `Resources.lean:122,
  433,475` and the two `Xv6/` constructions (`AppUnionPre.lean:89`, `AppPreGS.lean:54`) [R14.s1].  Recommendation: keep (i-a) RULED at the corrected census; the coordinator reports the
  8 → 12 delta; the owner may re-rule to (i-b) at any time before W-RSV launches (serial after W-COH → W4 → M1).
- **D20 — RULED (a) [OWN.19]. `candSca`** [R9.1].  Spec: RVWMO "Memory Model Primitives" — a NATURALLY ALIGNED load/store of ≤ XLEN bytes
  is single-copy atomic; a misaligned access may be split into byte operations, not SCA; Sail in this tree — `mem_read`
  splits misaligned accesses via `split_misaligned` (`Mem.lean:414,511,547`; `SplitAccessUtils.lean:256`), RAM PMA
  `misaligned_exceptions.load_store := none` (`MachCSL/Platform.lean:250`: no fault, so the split path IS reachable);
  TsoMem reads EVERY load's bytes at one `tvn` regardless of alignment (`Lang.lean:363-367`); the cat model's
  `gloadValue` gives one gmo position per load EVENT regardless of alignment (mixed-size N10, out of scope, §A).
  Marks: (a, RULED) **`candSca` over every `LLoad` at M1/M2 ONLY, derived at Stage 2** (now `candScaT`, G1-Q (e) RULED [OWN.17]) — FAITHFUL for naturally aligned
  loads ≤ 8 bytes, STRONGER for misaligned ones (kernel loads are compiler-aligned — **unverified** as a census; user
  code may misalign); (b) an atomicity axiom in sRVWMO — same mark, XL.
- **D21.** (Rec) report M1 as
  "composition milestone, kernel-only by premise `candKfetch`, loads SCA by premise `candSca`"; (b) nothing before M2 — **(Rec)
  APPLIED at rev 31 in the W5 CLOSE-OUT's wording (§C W5: + `candScaT`/`candDiskLat` by premise, the named `sailCycleOrder`, the
  disk rows PROVED, axioms, the quiescent witness)**.
  **D22.** (Rec) the `_entry` first-load witness gates M1 (SATISFIABLE, QUIESCENT, not reaching `allocproc`); (b)
  follow-up.  **D23.** (Rec) W1 via `xv6NiPhi` (S–M); (b) the rev-3 ledger hook (M).  **D24. W8's export form — FIXED by W8-design (DONE) [R21.1][OWN.36][OWN.37]**: the PURE per-state
  predicate `xv6AccessDisc σ` on `MState` (`mmOk` idiom; NO ghost ledger in the export — ownership is σ-derived: `kOwnerAt`
  from `cpus[h].proc`, the lock holder by the alternation fold `lkHolderAt`, the static carves; §C W8 has the Lean text),
  consumed by `badSeg`/`protReg` through `R`'s log identification; the FEED is (f2-ctx) [OWN.37] (chain-carrying context
  tokens), with W8-β′ for the lock-layer words and `cpus[h]`; the ROOT is (r2) — **built by W8-β′ at the provisional conjunction
  `lockWordDiscAt ∧ cpuStaticAt`, strengthened by W8 (f2-ctx) [R25.2]**; `chainOkAt` EXEMPTS kernel-PTE bytes and the clause
  `pteDiscAt` covers the hardware A/D write-back [R25.1].  History: (Rec) a per-state predicate on
  `g.m` + a ghost access ledger exported like `mmOk`, in `protReg`/`badSeg`'s vocabulary — its LANE RULED (α) [OWN.36]:
  serial MachCSL, before W-RSV; **[R22.1]** W8-design also pins
  the FEEDING path (f1)/(f2)/(f3) and the ROOT path — (r1) `mmOk`/`xv6TracePure` (text unchanged, meaning strengthened) or
  (r2) a W3-pattern sibling root (≈ 1.8k lines of twins), §C W8; **[R23.1]** (i)'s owner is DYNAMIC (kernel stacks migrate at
  `swtch`; owner changes at the `p->lock` handoff), so the export carries a per-byte owner; (b) a new `Obs` per
  access; (c) trace-free from W9a's check + ownership facts — W8-design checks whether (c) covers (i)/(iii) (for (i): only
  the statically owned bytes [R23.1]).
- **D25** — RULED [OWN.5], spike-CONFIRMED: (a) cat-sound kill arms (`rsameC`/`gcrossE`, lock kit `*C`,
  `normalizeOfAcyclic` over the core), M–L.  **D26. Stage-2 sequencing** [R4.s5][R6.3][W2s][R10][R11] — rev 19 state:
  the Stage-1 brace {W5b′ ∥ W1b ∥ W13 (E) ∥ W5d-G G0 ∥ W-COH} is DONE (W13 (E) partial per [OWN.27]), W2a/W2b DONE,
  W13 (T)+(M), W5-pre, W11 (iv)a DONE (rev 20 [R16.4]).  (Rec) **{W2 CLOSE ✓ ∥ W4 F1–F8 ✓ ∥ W11 (iv)b ✓ ∥ W-DMA0 ✓ (rev 24)} → {W-DISK ✓
  ∥ W5 CORE (plumbing [R21.4]) ∥ W8-design ✓} → **{W4 F9 (W-DISK DONE) ∥ W5 CORE ∥ W8-β′ → R-ctx → W8 (f2-ctx) (serial
  MachCSL [OWN.37])}** → M1 CLOSE (= F9 + W5 CORE, IN PARALLEL with W8 — rev 28; **DONE 2026-10-12 [rev 31]: F9 ✓, W5 CORE ✓,
  R-ctx ✓ while W8-β′ had just launched — the W5 CLOSE-OUT registers it**) → {**W-SCO ∥ W5d ∥ W13 (I) ∥ W5 CLOSE-OUT — launchable
  now** ∥ W-RSV (after M1 ✓ AND W8-β′'s MERGE — Q-RSV-order RULED (b) [OWN.41] [R28.5]; W8 (f2-ctx) then follows W-RSV)}** ((i-a)
  RULED [OWN.23]; L–XL, the LARGEST serial MachCSL item, one `Xv6`-cone rebuild; W4 re-check, S) **→ M2; graph lane:
  W13 (I) (gate MET — W-DISK ✓; M on the fabric side [R16.1]) → {W12 ∥ W12b ∥ W5d-G G1–G5 (gate (M) MET [OWN.24]; after (I)'s
  `Fab`/`Supply` text is fixed, to keep those files single-writer) ∥ W13 (L)(K)(F-dep)} → W13
  (R)(W) → W9a/W10 → W11, W14 after W2 CLOSE and W13 (I)/(W)**; (b) start W8 with Stage 1 (risk: `R` not fixed — now
  MOOT: `R` and `pfStepTso` are landed [R21.s4]).  [R14.3][OWN.24] W5d-G G1–G5 HERE, after
  W13 (M) — landed; sequenced behind (I)'s brief for file hygiene only.  [R12.1][OWN.36] W-RSV's L–XL lengthens the serial
  MachCSL lane (W-DMA0 ✓ → W8-β′ → W8 (f2-ctx) → W-RSV → M2, M1 beside it on the `Weak/` lane); W8 uses the lane while
  W-RSV waits for M1 (if W8's 2–4 rebuilds outlast F9 + W5 CORE, W-RSV waits — likelier under [OWN.37]'s sizing); the graph lane is unaffected, so the
  overall critical path moves to W-RSV only if it outlasts W13 (I) + (R) — W13 (XL) remains the expected bottleneck;
  W-DISK (DONE 2026-10-12) cleared W4 F9 → M1's path and W13 (I)'s gate; what now sits on M1's path is F9 + W5 CORE
  only, and on W-RSV's path M1 AND W8 (f2-ctx) [OWN.37].
  **Q-W5dG-seq — RULED (a) [OWN.24] (raised by R14): when do W5d-G's G1–G5 start?**  *Spec*: not a semantics question
  — RVWMO, Sail, Zifencei and PMAs are silent on how proof files are sequenced; every option FAITHFUL.  *Plain
  language*: W5d-G is the graph-tier fetch model (how the published theorem accounts for WHICH BYTES a hart executes
  when user text is written by `exec` and made visible by `fence.i`); G0 re-creates its lost scratch file from
  `notes/W5dG-spike.md`; G1–G5 then edit the SHARED chain files (`Fab` = the fabric/device conformance bundle, `Supply`
  = how a graph yields a candidate execution, `Acyc`/`Glue`/`Hull`/`Topo` = the cycle-kill and linearization
  machinery) — the SAME files W13 (the I/O-events redesign, XL) rewrites in its (I), (K), (M) pieces; (M) is SERIAL
  because its `gmem` case splits touch every chain file.  *Tiny example*: worker A (G3) adds the field `Gdexec.gdFetch`
  and fixes its ~31 construction sites (`Acyc.lean:200`, `Glue.lean:205-223`, `Hull.lean:714`, `Topo.lean:120-129,
  594-607`); worker B (W13 (M)) changes `gmem` (which events count as memory events) and re-proves the case splits in
  the same files; whoever merges second re-does both edits by hand.  *Why it matters*: nothing in the theorem changes
  — schedule and rework only; but rev 17's launch set and D26 disagreed, so the first worker launched would have fixed
  the order by accident.  *Options*: **(a) RULED — D26's order: G0 now, G1–G5 after W13 (M)**: the launch set and
  Status drop "then G1–G5"; cost 0; unblocks a clean G1–G5 on the post-(M) chain; risk — W5d-G's XL hull risk R1
  (§B(4)(iii)) is probed later (after W13 (M), weeks).  **(b) G1–G5 now, W13 (M) rebases on them**: (M)'s brief says
  "rebase on `gdFetch`/`emZifencei`"; cost — (M)'s sweep grows by the fetch fragment's arms (S–M) + one rebase; unblocks
  early probing of R1 (G4's retime invariance is where it bites); risk — two XL-adjacent items in flight on the same
  files.  **(c) G1–G2 now (`Supply`/`Conf` only), G3–G5 after (M)**: keeps `Acyc`/`Glue`/`Topo` single-writer; cost 0;
  unblocks `emZifencei`'s text early for W13 (I)'s `gfexecConfIO`; risk — G1's `Fab.lean:516-522` edit meets W13 (I)'s
  `:522-535`, one small rebase.
  **D27** — RULED [OWN.6], spike-SHAPED: `gzFetch`, admin form, D40–D43.  **D28** — RULED [OWN.7]: all 182 + 58 sites through W8.
- **D29** [R5.1, Q-R] — RULED [OWN.8]; UPDATED [R6.3][OWN.14]: T2-1c′ LANDED; the literal axiom refuted → D32; `gdevAdj
  ⊆ gmo` on FOLDED blocks rejected, on I/O events it is (R3).  **D30** — RULED [OWN.9]: sibling root
  `xv6TextAdequacy_closed`; existing roots/baseline untouched; `tcb/expected.json` gains an entry [R6.5c] — DONE
  (Q-W3a (A) [OWN.16]).  **D31. W13-wit timing.**  (Rec) build on W5c's `esilAdmRun` bridge (LANDED) as W13 (W)'s gate 1 — the only
  pre-Stage-2 evidence that a device-active candidate exists; end = the first UART `sb` at `0x800008a0`, an `LIo` EVENT
  (needs W13 (I)'s `projLbl` flip — (E) is merged but projects `LDev` to `none` until (I) [OWN.27]); (b) defer to Stage 2.

