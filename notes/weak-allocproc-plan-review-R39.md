VERDICT: NOT SATISFIED

# Review R39 of `notes/weak-allocproc-plan.md` (rev 42) — the second Stage 2 launch set

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git/jj, no subagents).  Scope per the R39
brief: revs 41 + 42 — the R38 application, the rev-42 RESULTS, the rulings [OWN.52]–[OWN.54], and the launchability of
**W13 (F-dep) RELAUNCH (A1), W13 (R3′), D35-fix, W13 (K), W11 (iv)c** (files, pairwise disjointness incl. vs the RUNNING
W8 (f2-ctx) in w2, order).  Every cite was read at the working-copy tip of `../xv6iris-weak`; herd's `riscv-defs.cat` was
fetched today (raw.githubusercontent.com/herd/herdtools7/master/herd/libdir/riscv-defs.cat).

**Sign-off.**  NO — three required changes, all S plan-text, none a redesign and none shrinking.  Two are file-list /
disjointness corrections that would otherwise collide two concurrent workers or leave a lemma that becomes FALSE unnamed;
one is a trusted-text satisfiability gap in W13 (R3′) of exactly the class R38 found (the plan asserts a fact about the disk
row that the emission contradicts).  W11 (iv)c is launchable as written; W13 (K) is launchable after (R3′) as planned;
(F-dep), D35-fix and (R3′) are launchable once [R39.1]–[R39.3] are in the text.  R38's six required changes are applied
correctly (checked §C (F-dep) (0a)–(0e), the `dstep`-inert clause, the sweep sizing, Q-FDEP, the header/launch text, the W12
course note); the rev-42 RESULTS are in the tip (`Weak.lean:641-646` imports; `CatLin.lean:54`, `CatLinChain.lean:320/403`,
`CatFloor.lean:60/63`; `WeakRvwmoLin2.lean:1083/1091/1141/1153/1203/1219-1222/1271/1403`; `WeakRvwmoLin.lean:2288`;
`RvwmoXv6Sca.lean:209`, `RvwmoXv6ScaT.lean:748/790`).

## Spec first (shared by the items below)

- **herd `riscv-defs.cat` (fetched)**: `let AQ = (Acq|AcqRel) and RL = (Rel|AcqRel)`; `let AMO=X`; `let SC=EX&W`;
  **`let RCsc = (Acq|Rel|AcqRel) & (EX|X)`**; `r5 = [AQ];po;[M]`, `r6 = [M];po;[RL]`, `r7 = [RCsc];po;[RCsc]`; `r9`–`r13`
  start at `[M]` (the plan writes `[R]`; identical in effect — only reads have register sources).  The plan's quote is EXACT;
  [OWN.54]'s reading (every aq/rl-annotated LR/SC/AMO is RCsc) is the cat text.  **RVWMO prose** ("Memory Model
  Primitives"): aq on LR/AMO = acquire-RCsc, rl on SC/AMO = release-RCsc; RCpc annotations arise only under Ztso — the plan's
  sentence is right.  **Sail** (`vendor/lean-sail`): single-hart operational, annotations are access-kind bits — SILENT on
  ppo.  **Zifencei**: fetch only — SILENT.  **PMAs**: channel ordering among I/O accesses; nothing on RCsc or on device-row
  events — SILENT.  RVWMO/riscv.cat/Sail have no device-internal events: (R1)–(R3)/(R3′) and `gfDev` are device-model text
  (D45/D49 class), as the plan says.

## REQUIRED changes

**[R39.1] §C top D35-fix: the consumer/file list is incomplete, one named lemma becomes FALSE, and the `racyD` meaning
change must be stated.**  Evidence and change, item by item:
  (a) **`AxGraphCat.grcscGrelAcq :250` (`grcsc → grelAcq`) becomes FALSE** under `lbRcsc := lbAq || lbRl` (two `LStore true`
  in po are `grcsc` but not `grelAcq`).  The plan names the NEW converse `grelAcqGrcsc` but not the deletion.  Add: "DELETE
  `grcscGrelAcq :250`; `gppoCat6Gppo :264`'s sixth arm becomes the direct `Or.inr (Or.inr (Or.inr h))` once `gppo`'s arm is
  `grcsc`; header `:39` and the port-map line `:85` (`grcsc_grel_acq`) rewritten".
  (b) **`Weak/CatLinWit.lean:42`** is a Bool twin of `racy` that uses `grelAcqB` (`gacqB || grelAcqB || decide (∈ gdDeps)`),
  with its spec at `:56` — it MUST widen to `grcscB`-wide or `sbrfi`'s `racyD`-acyclicity (`:124`) no longer matches
  `racyD`.  **`Weak/CatLinHull.lean:94-126`** (`lblRenRcsc`, the hull `grcsc` transport) re-elaborates.  Neither file is in
  the list (the grep `lbRcsc|grcsc|grelAcq` over `Weak/` returns exactly 14 files: the plan's 12 + these two).
  (c) **`rowsRelGppo` (`WeakRvwmoAcyc.lean:512`)** unfolds `grelAcq` and rewrites with `lblRenAq`/`lblRenRl`
  (`WeakRvwmoNorm.lean:362-363`); with the arm `grcsc` it needs a `lblRenRcsc` BELOW `Acyc` — today it lives in
  `CatLinHull.lean:94` (which imports `Acyc`'s descendants).  Add: "move `lblRenRcsc` next to `lblRenAq`/`lblRenRl` in
  `WeakRvwmoNorm.lean`; `Xchg.lean:896` likewise needs `lblTswapRcsc` beside `lblTswapRl :743`".
  (d) **State the semantic consequence**: `racy :197` carries `gppo` BY NAME, so widening RVWMO⁻'s rule-7 arm (route (i))
  WIDENS `racyD :200` — the acyclicity premise of `normalizeOfAcyclic :607`, `hullRun`, the kill, W5d-G G3/G4 and (K)'s
  `racyDIO := racyD ∪ …` all inherit it with NO text change ((K) is unaffected textually; the kill must exclude rule-7-wide
  cycles — on xv6 graphs the arm is empty, no `W.rl`).  `linGppo` (`Topo.lean:333`) and `linwGppo` (`PreNorm2.lean:387`)
  prove `gppoGmo` of the retimed graph THROUGH `rowsRelGppo` and `racy`'s `gppo` arm — automatic after (c).  Also add the
  Rocq deviation: `WeakRvwmoGraph.lean`'s header (RVWMO⁻'s `gppo` in Rocq has `grelAcq`; here `grcsc`-wide).
  (e) **`AxDeps.lean` is NOT touched** — the grep for rule 7/RCsc/RCpc in `AxDeps.lean` is EMPTY; make the "(4) … `AxDeps`'s
  deviation list if it names rule 7" unconditional ("it does not") so the (F-dep) ∩ D35-fix claim rests on fact.
  Size unchanged (M; the additions are S).  Acceptance: add "`grcscGrelAcq` gone; `CatLinWit.sbrfi*` recomputed".

**[R39.2] §C top SECOND LAUNCH SET: the pairwise-disjointness claims are wrong in two places; one (F-dep) file is missing.**
  (a) **D35-fix ∩ (F-dep) ≠ ∅**: `Weak/WeakRvwmoAdm.lean` is in BOTH — D35-fix re-cases `mp2PpoGmo :850` (`rcases h with
  hloc | hf | hacq | hrel`), (F-dep)'s sweep hits the positional `LDev kd ba bs` at `:696` (and (F-dep) lists `Adm` among
  its witness files).  `AxSpinSpike.lean` is also in both lists ((F-dep) `cDw :658`; D35-fix `:749`, "text unchanged" — a
  rebuild, not an edit: say so).  Change the "∩ … = ∅" sentence to "∩ = {`WeakRvwmoAdm.lean`} (disjoint sites `:696`/`:850`,
  rebase S — whichever lands second rebases)".
  (b) **`Weak/CatLinChain.lean` joins (F-dep)'s files**: `gdexecQconfTForget :331-338` proves membership in `forget GT` from
  `elemOfForgetDeps` with the `gisW` TARGET fact only; after (0b) `forgetDeps :178` also filters the SOURCE (`gisRd`), so the
  proof needs `hartConfRowDepsWf`'s source conjunct (`WeakRvwmoConf.lean:837`, `lbIsR` — available, S).  No other batch item
  touches `CatLinChain`, so disjointness holds; the list must say it (the relaunch brief is built from it).
  (c) Verified TRUE and worth keeping: (K)/(R3′) ∩ (F-dep) = ∅ (`LDev` appears in none of `Acyc`/`Topo`/`Hull`/`Glue`/
  `KillArms`/`GraphFabResidue`/`Lin2`/`FabInd`; 61 files mention `LDev`, all under `Weak/`); W11 (iv)c ∩ everything = ∅;
  (f2-ctx) (w2: `MachCSL/`, `Xv6/`, `Weak/WeakAdequacy.lean`) ∩ the four graph items = ∅ (`WeakAdequacy` has no `LDev`,
  no rule-7 name); `gppoCatT`/`gppoCatTGmo` are used outside `AxDeps` ONLY by `AxScCat.scPpo :168` — the (A1) blast radius
  claim is exact; `gdexecQconfT :320` is stated UNFILTERED (`rowDepsT ⊆ gtDeps`) as [R38.6] (ii) required.

**[R39.3] §C top W13 (R3′) (and §D Q-L-R3's record): a FALSE sentence about the disk row, and the widened TRUSTED item is
unsatisfiable on bundles with a non-memory fabric member.**  Evidence: the plan says "every disk-row (`NCPU`) event is a
write, an I/O event or a read" and expects `gfDevAncOfConf : gfexecConfIO … → gfDevAnc GF` from the membership clause.  But
the disk program has a `DFence` (`VirtioProg.lean:28`, `:91` — one, before the used-idx write), emitted as the ROW event
**`LFence true true true true`** (`WeakEvInst.lean:511`); and a `DWriteDev` own-guard SKIP or ABORT is SILENT (`:525-530`,
`l = LSilent`, no row item) while `pdevEv :609` is `true` on EVERY `.PDisk (some (DWriteDev ..))` state, so the contact bit
`tq k` of the block whose row item is that `LFence` is `true` → `(NCPU, k) ∈ gfDev` by the membership clause
(`WeakRvwmoFab.lean:857`, `… ∨ tq k = true`) with a label that is neither `gisAnc` nor `gmem` (`lbIsMem :127` is
R ∨ W ∨ Io).  Consequences: (i) `gfDevAncOfConf` has a counter-model — it is NOT provable from the clause (the W13 (L)
worker already said `gfDevWIo` "holds on xv6 runs (per (I)'s analysis) but not for a generic bundle"); (ii) worse, (R3′)'s
arm `gfBefore GF x y → gmoLt x y` with `gmoLt :137` requiring `x ∈ gxGmo` (memory events only; `graphOfCand :276` filters
`lbIsMem`) makes **`ioResidueGmo` — the TRUSTED item — FALSE on every such bundle**: the published premise is unsatisfiable
there (R38's vacuity class, now on trusted text; harmless on W13-wit's hart-only graph, but an expert will find it).
Change: (1) (R3′)'s fabric arm = **`gmem x ∧ gmem y ∧ gfBefore GF x y`** — EQUAL in strength on every anchor (anchors are
`gmem`), still STRONGER than the silent ISA and EQUAL to MachCSL's one fabric order on the events that HAVE a memory-order
position; (2) `gfDevGmoOfRes : ioResidueGmo GF → gfDevAnc GF → gfDevGmo GF` (or restate `gfDevGmo` over `gmem` members);
`ioResidueIo :114` → "an I/O endpoint, or both endpoints `gmem` fabric members"; (3) **`gfDevAnc` is a NAMED premise of
`fconfTraceRealizeIO`** (not "if the characterisation is not at hand"), discharged by W13 (W)/W14 from the disk program's
shape plus xv6's guard invariant (no own-guard skip folds into the `DFence` block on an xv6 run — (I)'s analysis, to be
PROVED there) and, hart-side, from "`pdevEv`-true hart steps are MMIO" (`pdevEv :604`, `WeakEvInst.lean:316-320/351-356`);
(4) acceptance: the header states the counter-model; `w13fIoResidueOk :236` re-proved (members I/O ⇒ `gmem`); `audit.sh
--weak` unchanged.  §D Q-L-R3's record gains one line: "(a) as refined by [R39.3]: fabric arm over `gmem` members; `gfDevAnc`
a named premise" — a refinement of the RULED option, not a new question (owner informed; non-blocking rule).  Size stays S.

## Launchability (the brief's five items)

- **W13 (F-dep) RELAUNCH (A1)** — launchable after [R39.2] (b) (`CatLinChain` in the list; the `Adm` rebase note).  (A1) is
  coherent: `gtAdFull` (addr/data edges into `lbIsW` targets, any source) ⊇ `gtAd`, `gppoCatT` over it, `catTAd :301` /
  `catADOfCatT` (`CatLin.lean:54`, `CatOfMinusSpike.lean:37`) by `gppo12` monotonicity; the hinge `gppoCatTAlt :201`
  (`Iff.rfl`) is restated.  Order (1) → (0) → (2)/(3) stands; "NEVER merge (1)+(2) without (0)" stands.
- **W13 (R3′)** — NOT as written ([R39.3]); S text fix, then launchable as (K)'s first increment.
- **D35-fix** — launchable after [R39.1].  The model reading is verified against the fetched cat text; the kernel census (only
  `amoswap.w.aq`; release = `fence rw,w; sw`) means no kernel graph changes; `grelAcq → grcsc` holds under the new `lbRcsc`
  (W.rl ⇒ `lbRl`, R.aq ⇒ `lbAq`), so dropping `grelAcqGmoC :60` through `gppoCat6Gmo` is sound.
- **W13 (K)** — launchable after (R3′) as planned; files verified (`racyD :200`, `normalizeOfAcyclic :607`, `KillArms :499`);
  D35-fix's only contact is `Acyc.lean:512` (S rebase, named).  Note [R39.1] (d): `racyDIO`'s meaning widens with `gppo`.
- **W11 (iv)c** — launchable AS WRITTEN: `linNwAAnc :209`, `gisAnc :1141`, `linCandIO :1147`, `gdiskRead14 :1153`,
  `linCandScaTA :748` are in the tip; the derivation (source visible ⇒ gmo-before by `gdiskRead14` on the forwarded case,
  co-maximality ⇒ latest same-byte write in the prefix log) is S–M as sized.
- **Order**: (R3′) → (K); D35-fix ∥ W11 (iv)c ∥ (F-dep) (1); `Adm` rebase by whichever of D35-fix / (F-dep) (1) lands second;
  ONE combined `audit.sh --weak` after D35-fix and (F-dep) (0), as planned.

## SUGGESTIONS

- **[R39.s1]** Cite drift: `gppoCatT` is at `AxDeps.lean:198` (§D says `:195`); `gisAnc :1141` (plan `:1140`);
  `RvwmoXv6ScaT.lean:783` in (0b) is now `linCandScaTMinusA :790`; `forgetDeps :178`/`gtAd :187` (plan `:175`/`:185`).
- **[R39.s2]** D35-fix (4): also `AxLitmus.lean:110` docstring ("Rule 7's RCpc arm") and `gppoMinusB :119` (the Bool `gppo`
  twin — widen with `grelAcqB :115`); `lbRcsc`'s docstring `:142` ("both annotation bits").
- **[R39.s3]** Five workers concurrently (f2-ctx, F-dep, K, D35-fix, iv-c) under [OWN.51]: D35-fix and (R3′) both change
  trusted/model text and both re-audit — consider landing (R3′) before launching D35-fix so one audit covers both.
- **[R39.s4]** (R3′) acceptance: add a computed check that `ioResidueGmo` is SATISFIABLE on a bundle with a `DWriteDev`
  member (the disk row's used-idx store) — the (R3′) analogue of [R38.s1]; today only `w13fIo` (two MMIO events) exists.
- **[R39.s5]** §A(3): "`r9`–`r13` range over ALL reads/writes" — herd writes them `[M];addr;[M]` etc.; say "`[M]` in herd,
  reads in effect" once, so the quote is literal.

## Owner questions the plan is missing

None blocking.  The two rev-42 questions (Q-L-R3, D35-rule7) meet the spec-first and plain-language formats; D35-rule7's cat
quote is verified against today's fetch.  One informational item for the owner (non-blocking rule, no menu needed): [R39.3]
refines the RULED Q-L-R3 (a) — the fabric arm ranges over the fabric members that have a memory-order position (`gmem`), which
is the same strength on every event the trace places and avoids an unsatisfiable trusted item; `gfDevAnc` becomes a named
premise until W13 (W)/W14 discharge it from the disk program's shape.  FAITHFUL/STRONGER/EQUAL marks unchanged from (a).
