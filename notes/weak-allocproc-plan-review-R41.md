VERDICT: NOT SATISFIED

# Review R41 of `notes/weak-allocproc-plan.md` (rev 44) — six merges verified, the THIRD Stage 2 launch set, RELAUNCH 5, Q-F2-PTE-WINDOW / Q-BATCH-3

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git/jj, no subagents).  Scope per the R41
brief: rev 44 = rev 43 + R40 ([R40.1] (α) applied at launch) + the RESULTS of six merges + the placement of W13 (K)'s open
items (W11 (i), NEW W13 (K-cat), NEW FabInd-S) + the THIRD launch set (W5d-G G1–G5 ∥ W9a ∥ W13 (W) via FabInd-S → (K-cat) →
(W)) + the W8 (f2-ctx) RELAUNCH 5 paragraph + the two new owner questions.  Every cite below was read at the working-copy
tip of `../xv6iris-weak`; the kernel source read is `~/dev/xv6-riscv/kernel/{proc,vm,kalloc,start}.c` (its `kernel.asm` is a
DIFFERENT build — at `0x80001b2a-0x80001b30` it has `freeproc`'s tail stores, not the image's `jal`/`sd` — so every pc claim
was checked against `Xv6/KernelImage.lean` directly); the registered roots' import closure was computed from
`tools/ci/roots-weak.txt` (theorem → defining module → transitive `import Weak.*`): 13 roots, 493 modules.

**Sign-off.**  NO — FIVE required changes, ALL S plan text, none a redesign, none shrinking: (1) Q-F2-PTE-WINDOW
UNDERSTATES the window it asks the owner to accept — `freewalk` frees every interior page-table page BEFORE clearing the
parent slot that names it, so the over-exemption is the dying table's EVERY page-table page (not "the ONE 4 KiB root
page"), and the "exactly R's 4 KiB" bound is not a theorem once the new owner may write a pointer-shaped word; (a) stays
SOUND and recommended, its stated bound must change in §D, RELAUNCH 5's docstring text and Rev 44 RESULTS; (2) W5d-G's
acceptance "`audit.sh --weak` unchanged (no registered root imports these files)" is FALSE — `Graph`/`Acyc`/`Topo`/`Conf`/
`Supply`/`Hull`/`Lin`/`WeakEvInst`/`WeakEvLang` are in EVERY registered root's closure, so each increment is a full-cone
rebuild + RE-AUDIT as D35-fix was; (3) FabInd-S and W5d-G G3 BOTH edit `WeakRvwmoKillIO.lean` (the "∩ = ∅" sentence is
wrong; one gate line fixes it); (4) W13 (W)'s acceptance promises to PROVE `gfDevWIo`'s disk half from `pdiskProg`'s
shape, but the used-element SKIP depends on a RUN-LEVEL virtio gate (`g s = none`) — name it as a hypothesis for W14;
(5) Q-BATCH-3 does not meet the owner-question format.  Everything else in the brief's focus VERIFIED: the six merges
are in the tip exactly as the RESULTS say (every cite re-read, below); W9a, FabInd-S, (K-cat) are LAUNCHABLE AS WRITTEN;
W5d-G and (W) after the one-line fixes; RELAUNCH 5 is EXECUTABLE (its binding step list is `PROGRESS-W8f2.md:37-63` 1–4
verbatim; every named site exists); Q-F2-PTE-WINDOW's recommended (a) is SOUND (the junk-walk claim holds: `ptPtrTo`
sends `0x0101…` to `0x4040404040000`, outside RAM; `0x0505…` has RWX ≠ 0 and is not followed), only its BOUND is wrong.

## R40 application — VERIFIED in the tip

- **[R40.1] (α)**: `WeakRvwmoLin2.lean:1222` `def gfDevGmo`, `:1225` `def gfDevWIo` (the plan's "`gfDevWIo :1222`" in the §C
  (R3′) header is a rev-43 cite — [R41.s2]); **`gfDevGmoOfRes :1237 : ioResidueGmo GF → gfDevWIo GF → gfDevGmo GF`**;
  **`fconfTraceRealizeIO :1284-1290`** premises = `rvwmoMinusConsistent`, `grule14`, `ioResidueGmo`, `gdiskRead14`,
  `gfexecConfIO`, `gfDevWIo`, `gxProg.length ≤ N` — EXACTLY (α)'s acceptance; `:1305` `have hgmo := gfDevGmoOfRes GF hres
  hwio`; the three arbitrary-trace lemmas `devOrderOfPtraceExtIO :1245-1246`, `trDevOrderedOfPtraceIO :1253-1256`,
  `fconfSupply' :1263-1268` KEEP `gfDevGmo GF → gfDevWIo GF →` (the recorded deviation; harmless, discharged at `:1309-1310`);
  `w13fIoDevOrdered` at `:1427` uses `gfDevGmoOfRes w13fIo w13fIoResidueOk`; header `:52-60` says (R3′)/[R40.1] (α).
  `GraphFabResidue.lean:112-124` — (R3) = `(gisIo x ∧ gisIo y ∧ gpo x y) ∨ (gmem x ∧ gmem y ∧ gfBefore GF x y)`;
  `ioResidueIo :149`, `ioResidueNodev :161`, `w13fIoResidueOk :286`; §5 `:322-361` the [R39.s4] computed check with
  `usedIdxSt`/`diskFabG` (`:331-334`).  No `gfDevAnc` anywhere (grep empty).
- **[R40.s1]** D35-fix launched at once (w1) — consistent with the closure fact (R3′)'s files are outside every root's closure
  (`GraphFabResidue`, `Lin2`, `FabInd` all OUT in my computation).  **[R40.s3]–[R40.s5]** D35-fix's (5)/(2)/file counts in
  §C (`:2397`); the landed grep `lbRcsc|grcsc|grelAcq` is **20 files** (verified).  **[R40.s7]** cite drift noted at `:2396`.

## Rev 44 RESULTS — VERIFIED (every cite re-read)

- **D35-fix**: `WeakRvwmoGraph.lean:252 def lbRcsc l := lbAq l || lbRl l`, `grcsc :256-257` (defined HERE), `lbRcscMem :262`,
  `grelAcqGrcsc :272`, `gppo :282-283`'s fourth arm `grcsc`; `CatFloor.lean:29-33` "D35 — CLOSED … `grelAcqGmoC` is DELETED";
  `roots-weak.txt:18-23` glosses "model rule 7 = riscv.cat's RCsc [OWN.54]".
- **W11 (iv)c**: `RvwmoXv6ScaT.lean:806` §(6), `linCandDiskLatA :837`, `linCandDiskLat :859` (via `ancOkIO GF h14 hres hdr`,
  `:863`), `linCandDiskLatMinus :869`; header `:42-49`.
- **W13 (K)**: `Weak/WeakRvwmoKillIO.lean` = 708 lines; `ioExtra :86`, `racyDIO :90`, `normalizeOfAcyclicIO :308`,
  `fconfRealizeIO :345`, `cycleKillIO :396`, `gfexecConsistentOfRes :406`, `t2linIO :454`, `hullRunIO :465`, `ioCross :540`,
  `racyDIOSplit :543`, `cycleKillIOC :566`, `noReadEdgeOutsideGmo :584`, `ioSegPinned :609`, `rsameNoReadEdge :655`,
  `ioSegPinnedMinus :664`, `w13fIoRacyDIOAcyclic :693`, `w13fIoRevRacyDIOCycle :701`; header deviations (1)–(4) at `:47-61`;
  `Weak.lean:646 import Weak.WeakRvwmoKillIO`; `Acyc.lean:213 def racyDX`, `Topo.lean:641 topoExistsX`/`:659
  normalizeOfAcyclicX`.  Its ONE use of `gfexecConfHull` is `:423` with `gfexecConsistentOfRes` — FabInd-S's premise.
- **W13 (F-dep)**: `AxDeps.lean:203/208/216/218` the I/O label classes, `gtdepsWf :236`, `gtAdFull :265`, `dstepT :631` with
  `| LDev kd _ _ asrc vsrc => :637`, `ioGt :1441`, `ioGtDepsWfB :1446`, **`ioGtCatT :1449`**, `ioGtForgetDeps :1453`;
  `roots-weak.txt:13-17` the (0) note; `CatLinChain.lean:324-331 gdexecQconfT` still carries `emDevfree em` (`:330`),
  `gdexecQconfTForget :337` — the OPEN consumer gap is real and correctly routed to (W).
- **W8 (f2-ctx) S3-a/b/c0**: `MachCSL/Reserved.lean:137 | roots (cnt stride : Nat)` (footprint-free: `:162 => []`);
  `ChainDefs.lean:642 entAsOf`, `:646 wordAsOf`, `:651 ptPtrTo` (`V ∧ RWX = 0 ∧ c = ((v >>> 10) <<< 12) &&& 0x00FFFFFFFFFFF000`),
  `:655 ptChildAt`, `:660 ptPageAt` (root, level-1, level-0 — depth ≤ 2), `:664 ptRootAt` (`r ≠ 0`), **`:670 ptByteAt`**,
  `:674 lockPubByteIn`, `:678 lockWordsByte`, `:684 chainExAt`, `ptByteAt_grow`; `Xv6/KernelRsv.lean:70 xv6KptRootR =
  ⟨KA.kernel_pagetable, .roots 1 8⟩`, `:72 xv6ProcRootsR = ⟨KA.proc + 80, .roots 64 376⟩`, both in the region list `:104-107`;
  `Resources.lean:1265 byteSrcOk`, `:1273 loadSrcOk`, `:1288 loadsChained_load` (plan: `:1292`); `AccessDiscipline.lean:53
  Cust`, `:89 custAt`, `:115 xv6AccessDisc` (still β′ — S4 not yet).  Image: `KernelImage.lean:5243 ⟨0x80001b2c, 4,
  0xf9dff0ef⟩` = `jal` to `0x80001ac8 = KA.proc_freepagetable` (`:17770`, decoded), `:5245 ⟨0x80001b30, 4, 0x0404b823⟩` =
  `sd zero,80(s1)`, then `0x0404b423` = `sd zero,72(s1)` (`p->sz = 0`) — the cites are RIGHT.

## REQUIRED changes

**[R41.1] Q-F2-PTE-WINDOW (§D `:4880-4914`, RELAUNCH 5 `:2310-2312`, Rev 44 RESULTS `:2241-2245`): the window is
UNDERSTATED — every page-table page of the dying table has it, not only the root; and the "exactly R's 4 KiB" bound is
not a theorem.**
  *Evidence.*  (i) `vm.c freewalk`: `freewalk((pagetable_t)child); pagetable[i] = 0;` for each pointer PTE, then
  `kfree((void*)pagetable)` LAST — i.e. every level-0 and level-1 page is `kfree`d (junk-filled, pushed on `kmem.freelist`
  under `kmem.lock`, `kalloc.c:55-63`) BEFORE the parent slot naming it is cleared.  Under (A′) that page stays
  `ptPageAt`-reachable from the still-stored root word (`ptPageAt :660-662` covers depth ≤ 2: root → level-1 → level-0)
  between `kfree`'s `release(&kmem.lock)` and the parent's `pagetable[i] = 0` — the SAME shape as the root window, one per
  interior page (a small process has ≈ 2 level-1 + ≈ 2 level-0 pages: the user region and the TRAMPOLINE/TRAPFRAME region).
  Leaf DATA pages are NOT affected (`uvmunmap` frees them before `*pte = 0`, but leaves have RWX ≠ 0 and `ptChildAt` follows
  `ptPtrTo` pointers only — correct in the plan).  (ii) The "unless the new owner stores pointer-shaped words — e.g. `R`
  becomes a page table again, which is then exempt rightly" hedge is incomplete: a page reused for user-controlled bytes
  (a pipe buffer, a `kalloc`ed user page) can hold a V-only word (`v &&& 0xF = 1`) whose PPN lands in RAM — the walk then
  reaches an UNRELATED RAM page during the window, over-exempted WRONGLY.  So "the over-exemption is exactly `R`'s 4 KiB
  for that window" is false as a bound; (a) remains SOUND (WEAKER: fewer obligations, never a false claim) but the
  honest statement is the WINDOW, not a page count.  (iii) The junk arithmetic: `ptPtrTo` maps `0x0101010101010101` to
  `((v >>> 10) <<< 12) &&& 0x00FFFFFFFFFFF000 = 0x4040404040000` (= Sv39's PPN `0x4040404040` ≪ 12), not
  "`0x40404040404000`" — both outside RAM (`0x80000000-0x88000000`); `0x0505…` has `RWX = 0b010` so `ptPtrTo` fails and the
  walk stops — VERIFIED, the recommended (a) is sound.  (iv) "the dying process … ZOMBIE": `freeproc` also runs on
  `fork`'s failure path (`freeproc(np)`, `np` never scheduled) — same window, same soundness; `exec` swaps `p->pagetable`
  BEFORE `proc_freepagetable(oldpagetable, …)`, so it has NO window; `uvmdealloc` frees leaves only — NO window.
  *Change.*  (1) §D Q-F2-PTE-WINDOW — *Plain language* and the tiny example: "`freeproc`/`freewalk` free each page-table
  page (level-0, level-1, then the root) BEFORE clearing the one pointer that names it (the parent's `pagetable[i] = 0`
  in `freewalk`; for the root, `p->pagetable = 0`, `0x80001b30`); in each such window the word still names a page on the
  free list"; *bound*: "every page-table page of the dying table (≈ 5 for a small process), each from its `kfree`'s
  `release(&kmem.lock)` to the clear of its pointer (a few instructions for interior pages; the `kfree` → `freewalk` →
  `uvmfree` → `proc_freepagetable` → `freeproc` returns for the root), plus — if the new owner writes a V-only
  pointer-shaped word before the clear — whatever RAM page that word names; the junk fills themselves reach no RAM page".
  (2) Option (a)'s docstring sentence (§D and RELAUNCH 5 `:2311`): "… including a page-table page already freed by
  `freewalk`/`proc_freepagetable` until the pointer naming it is cleared (its parent's slot, or `freeproc`'s
  `p->pagetable = 0`, `0x80001b30`)".  (3) Option (b″): keep "EQUAL" — clear-before-free (`p->pagetable = 0` BEFORE
  `proc_freepagetable`) makes the whole table unreachable from the root word for the entire `freewalk` (`ptRootAt :664`
  needs the word to HOLD `r`), so it closes the interior windows too — say so (it strengthens the case for (b″)'s sizing
  pass).  (4) Fix the junk address to `0x4040404040000` (`ptPtrTo :651-653`), and "ZOMBIE" → "not running on any hart
  (ZOMBIE in `wait`, or a never-scheduled child on `fork`'s failure path); `exec` swaps the word first — no window".
  (5) Rev 44 RESULTS `:2244-2245` "the over-exemption is the ONE 4 KiB root page for that window" → the same correction.
  Spec marks unchanged (custody is not an ISA notion; every option FAITHFUL to the ISA; (a) WEAKER than the intended export
  by the stated windows, (b″)/(c) EQUAL, (b) WEAKER and brittle).  Provisional (a) and RELAUNCH 5 proceeding under it: FINE.

**[R41.2] W5d-G (§C top `:2246-2262`): the acceptance "build/`audit.sh --weak` unchanged (no registered root imports
these files)" is FALSE; W5d-G is a RE-AUDIT item like D35-fix.**
  *Evidence.*  The 13 registered roots (`roots-weak.txt`: `AxSpinT2b/T2b2/T2c/T2e3/T2q1-4`, `SrvwmoXv6Adequacy`,
  `SailCycleOrderCycle`) have a 493-module import closure that CONTAINS `WeakRvwmoGraph`, `WeakRvwmoAcyc`, `WeakRvwmoTopo`,
  `WeakRvwmoConf`, `WeakRvwmoSupply`, `WeakRvwmoHull`, `WeakRvwmoLin`, `WeakEvInst`, `WeakEvLang` (and `AxDeps`, `Adm`,
  `AxSpinSpike`, `SrvwmoXv6Witness`, `VirtioProg`, `WeakAdequacy`); OUT are only `Fab`, `GraphFetchSpike`, `Glue`, `Floor`
  (and all of `KillIO`/`CatLin*`/`Lin2`/`FabInd`/`GraphFabResidue`/`PinBridge*`).  So G1 (`Supply`, `WeakEvInst`/`WeakEvLang`),
  G2 (`Conf`), G3 (`Graph`, `Acyc`, `Hull`, `Topo`), G4 (`Topo`), G5 (`Lin`, `Supply`) each rebuild the whole registered cone,
  and G3's **`Gdexec.gdFetch`** is a STRUCTURE-FIELD change to `WeakRvwmoGraph.lean:669-671` (`structure Gdexec where gdG;
  gdDeps`) — every anonymous constructor `⟨G, deps⟩` in the closure breaks (23 structure-syntax `gdDeps :=` sites + the
  anonymous literals, e.g. `WeakRvwmoKillIO.lean:701 ⟨⟨w13fIoG, []⟩, …⟩`, `GraphFabResidue.diskFabG`, `AxDeps.ioGt`); the §C
  item's "~31 literal sites (M ≈ 300)" (`:4010-4012`) predates the (K)/(F-dep)/(R3′) merges.  The roots' TEXT must stay
  unchanged: M1/M2's premises are candidate-level, the AxSpin roots are over `GdexecT`/`forget` — a default-valued field or a
  `forget`-side fill keeps them, but only the audit shows it.
  *Change.*  Replace the acceptance clause by: "every increment: `lake build` of the registered cone + `audit.sh --weak
  --build` — 13 roots, `baseline-weak.json` UNCHANGED, roots' statements unchanged (report); `Graph`/`Acyc`/`Topo`/`Conf`/
  `Supply`/`Hull`/`Lin`/`WeakEvInst`/`WeakEvLang` are in every registered root's import closure — `Fab`/`GraphFetchSpike`/
  `Glue`/`Floor` are not".  In G3: "`Gdexec.gdFetch` — a structure change: either a field with default `[]` + a sweep of the
  anonymous-constructor literals (re-count at launch; ≥ 23 structure-syntax sites + the literals added by (K)/(F-dep)/(R3′)),
  or a wrapper `GdexecF := ⟨GD, gdFetch⟩` consumed by `xv6ConfS`/`racyDX` only — the worker says which in its first report;
  `forget : GdexecT → Gdexec` fills it".  Size: keep L ≈ 1.8–2.2k but add "+ full-cone rebuild per increment (minutes, not
  lines)".  Also correct the same sentence where it recurs for FabInd-S/(K-cat)/(W)/W9a — there it is TRUE (their files are
  OUT of the closure; `audit.sh --weak` unchanged is automatic, as [R40.s1] said for (R3′)).

**[R41.3] FabInd-S ∩ W5d-G G3 ≠ ∅ (§C top `:2267-2272`, `:2304-2306`): both edit `Weak/WeakRvwmoKillIO.lean`.**
  *Evidence.*  FabInd-S must fix "the ONE external caller `WeakRvwmoKillIO.lean:423`" (verified: the only use outside
  `FabInd`); G3 adds the combined `racyDX GD (ioExtra ∪ fetchE)` instance "in `WeakRvwmoKillIO.lean` beside `racyDIO :90`"
  or widens `ioExtra :86`, and re-proves `normalizeOfAcyclicIO :308` there.  The plan says "vs FabInd-S ✓ (`FabInd` is nobody
  else's)" and "∩ (W)/(K-cat)/FabInd-S = ∅ except the `Gfexec` CONSUMER rebase" — wrong for `KillIO` (different regions,
  `:423` vs `:86-90/:308`, but the same file and G3 rebuilds it).
  *Change.*  One sentence: "FabInd-S and G3 share `WeakRvwmoKillIO.lean` (`:423` vs `:86-90/:308`): FabInd-S LANDS BEFORE
  G3 STARTS (a gate, not a preference — G1/G2 precede G3, so it costs nothing), else G3 rebases the one-line `:423` call".
  (W) and (K-cat) only IMPORT `KillIO` — fine as written.

**[R41.4] W13 (W) (§C top `:2284-2297`): "the discharge of `gfDevWIo` — PROVED here, not assumed: disk side from
`pdiskProg`'s shape + xv6's guard invariant" over-promises — the disk half is a RUN-LEVEL virtio fact, W14's.**
  *Evidence.*  The SKIP arm (`WeakEvInst.lean:519-525`) fires when `g s = none ∨ ¬ ramBytes (pa s) (bs s).length`; for the
  used-ELEMENT `DWriteDev` (the one whose skip folds into the `DFence` block, [R40.s6]) `g` is "the gate `phase ∧ completeOk ∧
  pushOk` → `.pushed`" (`VirtioProg.lean:88-90`) and `pa s` is the used-ring address the DRIVER supplied.  Whether the gate
  holds and the address is RAM on an xv6 run is a property of the virtio STATE produced by `virtio_disk_rw`'s descriptor/
  avail discipline — not of `pdiskProg`'s shape, and not available in (W)'s files (`Fab`/`CatLinChain`/`Lin2`/`KillIO`
  consumer).  (W)'s witness (hart 0 to the first UART store, `0x800008a0 ⟨…, 0x000780a3⟩` = `sb zero,1(a5)`, verified) has
  NO disk activity, so the disk half is VACUOUS on it — the Bool twin cannot catch a wrong guess.
  *Change.*  "`gfDevWIoOfXv6` takes a NAMED disk-side hypothesis — `usedElemGateOk` (or the worker's name): on an xv6 run the
  used-element `DWriteDev`'s gate holds and its target is RAM (equivalently: no own-guard SKIP at that node); the hart half
  is PROVED here by [R40.s2]'s three cites (`lbAdmin` never `LDev`; hart arms keep `d' = d`; `LDev` projects to `LIo`); the
  disk hypothesis is DISCHARGED by W14's device-active witness / the disk invariant, or stays a named premise".
  Acceptance: "`fconfTraceRealizeIO`'s premise list closes on xv6 runs except `gdiskRead14` (by (K)), the trusted
  `ioResidueGmo`, and the named `usedElemGateOk` (W14)".  Size unchanged (M–L).  Record it under (W)'s spec line as
  device-model text (RVWMO/riscv.cat/Sail/Zifencei/PMAs silent on device programs; EQUAL to MachCSL's disk step on xv6 runs).

**[R41.5] Q-BATCH-3 (§D `:4915-4918`) does not meet the owner-question format (owner, 2026-10-10).**
  *Evidence.*  Four lines: no plain-language statement of what each of the three items DELIVERS toward the target
  theorem, no definitions of `W5d-G`/`W9a`/`W13 (W)`/`FabInd-S`/`(K-cat)`/`RELAUNCH 5`, no "why it matters", and the options
  carry no per-option cost/unblocks/risk except "defer".  (It is not a memory-model question — the spec-first rule does not
  apply, and the plan says so correctly.)
  *Change.*  One short paragraph per the format: *Plain language* — "three more proof items on the graph side, in parallel,
  beside the running W8 lane: W5d-G makes instruction FETCH (Zifencei) a first-class part of the graph model so user-text
  changes are covered (five increments, the one item that rebuilds and re-audits the registered cone [R41.2]); W9a connects
  the checker's pin certificates to the cat-model segments (a new file); W13 (W) states the real device-active xv6
  conformance bundle `xv6ConfS` and builds the first witness with a non-empty fabric, after two S preparatory lemmas
  (FabInd-S, (K-cat))"; *Definitions* (one line each); *Why it matters* — "the fourth set (W13 (R), W14 — the device-active
  disk witness that makes the published theorem non-vacuous on I/O) waits on W5d-G and (W)"; *Options* — approve all (cost:
  three graph workers + the serial lane = four, under [OWN.51]; unblocks W13 (R)/W14; risk: W5d-G's XL hull-closure risk R1
  and its cone rebuilds); approve W9a + FabInd-S/(K-cat)/(W) only (safest files; defers the fetch model, so W14/W13 (R) wait);
  defer all (cost: the fourth set slips a round).

## Launchability (the brief's items; files, disjointness, sizes)

- **W5d-G G1–G5** — launchable after [R41.2] (acceptance) and [R41.3] (the G3 gate).  Files verified at the tip:
  `WeakRvwmoSupply.lean:367 def emFetchImg` (the plan's "was `:277-352`" has drifted — re-cite at launch, as the plan says),
  `supplyOfQconf :827` (inside the named `:743-883` region ✓), `Fab.lean:816-821` the `emZifencei` SLOT (today `:= emFetchImg
  im em`), `WeakRvwmoConf.lean:57-66` the `LIFetch`/Q-C4 block and `:147` the `wlblRen` `LIFetch` arm ✓, `Glue.lean:205-223`
  the `racyDSplit` induction + `cycleSegments` ✓, `Hull.lean:716 hullRule14` (plan `:714`), `Acyc.lean:213 racyDX`,
  `Topo.lean:641/659` parametric forms ✓, `GraphFetchSpike.lean:89,314` ✓.  Deps (F-dep) ✓ (K) ✓ W12/W12b ✓ (L) ✓ — all in the
  tip.  ∩ W9a = ∅ ✓; ∩ (W) = the `Gfexec` consumer rebase on G1 ✓ (named); ∩ FabInd-S = `KillIO` ([R41.3]); ∩ (f2-ctx) = ∅ ✓.
  Size L ≈ 1.8–2.2k plausible for lines; the rebuild cost is the omission ([R41.2]).  G1 first ✓ (M ≈ 350–450; six G0 carry-overs
  listed at `:3997-4005`).
- **W9a** — LAUNCHABLE AS WRITTEN.  `PinBridge.lean` 360 / `PinBridge2.lean` 601 ✓; `PinBridge2.lean:514 psites`, `:530
  pinSegPin'`, `reaches` (header `:14,:59-60`) ✓; `CatLin.lean:187 segPinC`, `:202 segPinCForward`, `:180 pinStepOfSegPinArm` ✓;
  `PinBridge*` and `CatLin` are OUT of the roots' closure → "`audit.sh --weak` unchanged" automatic ✓.  ∩ everything = ∅ ✓.
  Size L ≈ 0.8–1.2k: unverifiable but consistent with the two files it aligns.
- **FabInd-S** — LAUNCHABLE AS WRITTEN (modulo [R41.3]'s gate and [R41.s1]'s count).  `WeakRvwmoFabInd.lean:377-383` takes
  `gfexecConsistent GF` and `hullOk …`, `:384 rintro _ hdc _ ⟨h0, hnd, hbnd, hc⟩` discards both ✓; in-file uses `:535`, `:570`
  (the only two); external `KillIO:423` (the only one) ✓; `gfexecConfRen` untouched ✓; OUT of the closure ✓.  S ✓.
- **W13 (K-cat)** — LAUNCHABLE AS WRITTEN.  `CatLin.lean:114 rsameC := gpow ∨ gppo ∨ deps ∨ grfi`, `:80 grfi := grf ∧ same
  hart` (no gmo) ✓ so `noReadEdgeOutsideGmo :584` fails on it ✓; the refined invariant is CLOSED under this model's other
  arms — `deps` target writes (`gdepsWf :675-677`; (R2) orders them after `x`), `gpoloc :279-280` R→R same-address keeps the
  later read "forwarded from a po-later write or coherence-after", `gacqPo`/`grcsc` need an `aq`/`rl` label a forwarded plain
  load lacks — and BREAKS only at `gfenceCovers :228-232` with `pr ∧ sr ∧ ¬ pw`: the plan's `PR∧SR∧¬PW` side condition is
  exactly right for this model ([R41.s3]).  Image census (`KernelImage.lean`, opcode `0x0f`/funct3 0): 4 × `fence iorw,iorw`,
  2 × `fence rw,w`, **1 × `fence r,rw` at `0x80000ee6`** (`KernelPins.lean:306`, `WkStartedLoad.lean:22` "main+0x18") — the
  plan's "the image's only such fence" is TRUE; `timerinit` is sstc CSR-only (`start.c:56-65 w_stimecmp`), so harts ≥ 1
  issue NO MMIO before it (`W13-io-census.md:32,:153`) ✓.  New leaf, imports `KillIO` + `CatLin` (both OUT) ✓.  S–M ✓.
- **W13 (W)** — launchable after [R41.4].  `gdexecQconfT :324-331` with `emDevfree :330` and `gdexecQconfTForget :337` ✓;
  `xv6ConfS` exists only in docstrings (`Fab.lean:816`, `GraphFetchSpike.lean:89,314`) ✓; W13-wit's pc `0x800008a0` ✓,
  `esilAdmRun` in `SrvwmoXv6Witness` (IN the closure — imported read-only, fine) ✓; new files, consumer-only, OUT of the
  closure ✓.  ∩ W5d-G = the G1 rebase ✓; ∩ W9a = ∅ ✓.
- **W8 (f2-ctx) RELAUNCH 5** — EXECUTABLE.  Steps S3-c1/c2/c3/S4 are `PROGRESS-W8f2.md:37-63` items 1–4 verbatim; sites exist:
  `ChainCert.lean:3,44,59,125 chainModelAt`, `Power.lean:723`, `PowerText.lean:473`, `Wp.lean:1184 rsvModel_mono` (`:1190`),
  `Wp.lean:1325 memModel_load`, `WpSmodeFenceFloor.lean:90 memModel_load_rv` and `:252` the two calls, `UIcache.lean:245`
  `memModel_load`, `Wp.lean:2012 swp_sail_mem_read_plain_ctx`, `:1685 ctxBytes_srcOk`, `WpAtomic.lean:407 srcCertAt`, `:416
  readCertsAt`, `:429 memModel_readCerts`, `WpLock.lean` 12 × `unfold readAU` ✓, `Lock.lean:283 lkCpu_read_not_mine` (W11 (i)'s
  lemma — exists), `KptBoot.lean:135 kptRoot_persist`, `PtTree.lean:89 PTree.wf`; `ACQUIRE_LLB|ACQUIRESLEEP_LLB` = 31 hits in
  10 `Xv6/` files today (the "both greps EMPTY" is the X1/X5 TARGET — say "today 31 in 10 files; after X1/X5 both greps
  EMPTY").  Serial lane; ∩ graph items = ∅ ✓ (`WeakAdequacy` IS in the roots' closure, so its `audit.sh --weak` in the
  acceptance is load-bearing — present ✓).  Under [R41.1] only the docstring sentence changes.
- **W11 (i) placement** (`:4686`) — consistent with `ioSegPinned :609`'s statement (takes `S` + check (i) only) and with
  `lockWordDiscAt` being a machine-state predicate; `lkCpu_read_not_mine` exists.  OK.

## SUGGESTIONS

- **[R41.s1] FabInd-S count**: "fix the 7 in-file uses (`:535`, `:570`, …)" → "2 in-file uses (`:535`, `:570`) + 4 docstring
  mentions (`:17,:37,:51,:61`) + the def; 1 external (`KillIO:423`)".
- **[R41.s2] Cite drift**: `gfDevWIo` is `Lin2.lean:1225` (`:1222` is `gfDevGmo`) in the §C (R3′) header and §D Q-L-R3;
  `loadsChained_load :1288` (plan `:1292`); `hullRule14 :716`; `emFetchImg :367`; `diskFabG :331-334`; RELAUNCH 5's
  `Adequacy:508`/`WpAtomic:938`/`Wp:1679` are the worker's pre-S3-c0 lines — mark "re-cite at launch".
- **[R41.s3] (K-cat)**: write the closure argument of the Launchability bullet above into the item (one sentence per arm)
  so the worker neither widens the side condition to `PR∧¬PW` nor misses that `gpoloc`'s R→R arm is covered; and name the
  image census (1 × `fence r,rw`, 4 × `iorw,iorw`, 2 × `rw,w`) as the discharge's input.
- **[R41.s4] Q-F2-PTE-WINDOW timing**: "about a dozen same-hart instructions, three returns" → "from `kfree`'s
  `release(&kmem.lock)` (the page becomes allocatable) to the clear; four returns for the root (`kfree` → `freewalk` →
  `uvmfree` → `proc_freepagetable` → `freeproc`), fewer with tail calls; two for an interior page".
- **[R41.s5] W5d-G G3 literal count**: re-count the `Gdexec` literals at launch (the (K)/(F-dep)/(R3′) merges added several:
  `KillIO:701`, `GraphFabResidue.diskFabG`, `AxDeps.ioGt`, …) and state the chosen mechanism (default field vs wrapper).
- **[R41.s6] (W) witness honesty**: say W13-wit exercises `gfDevWIo`'s HART half only (no disk activity before the UART
  store); the disk half's computed check belongs to W14's device-active witness.
- **[R41.s7] Q-BATCH-3 subset option**: name W5d-G as the one item with full-cone rebuilds + RE-AUDIT ([R41.2]) and (W)'s
  one rebase on G1, so the owner can weigh "approve W9a + the (W) chain first, W5d-G after" as a third option.
- **[R41.s8] RESULTS wording**: "`gfDevGmo :1222` is a THEOREM" → "`gfDevGmo :1222` stays the Prop; `gfDevGmoOfRes :1237`
  PROVES it from `ioResidueGmo` + `gfDevWIo`".

## Owner questions the plan is missing

None new.  [R41.1] is a CORRECTION of OPEN Q-F2-PTE-WINDOW's content (the window's extent), not a new question: every
option keeps its mark (custody is not an ISA notion — RVWMO, riscv.cat, the Sail model, Zifencei and the PMAs are SILENT;
all options FAITHFUL to the ISA; (a) WEAKER than the intended export by the stated windows, (b″) and (c) EQUAL, (b) WEAKER
and brittle), (a) stays sound and recommended, and the corrected text makes (b″) slightly MORE attractive (it closes the
interior windows too) — the owner should see the corrected bound before ruling.  [R41.4]'s `usedElemGateOk` is a named
device-model hypothesis of EQUAL strength to MachCSL's disk step on xv6 runs (the spec is silent on device programs) —
inform under the non-blocking rule, no menu.  Q-BATCH-3 needs the format ([R41.5]), not new content.
