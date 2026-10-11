VERDICT: SATISFIED

# Review R15 of `notes/weak-allocproc-plan.md` rev 18 (adversarial, evidence-based; 2026-10-10)

Scope (per the R15 brief): rev 18 = R14's three required changes ([R14.1] W-COH + `Weak/TsoOfPf.lean` + `Vtest`;
[R14.2] `LExStore` after W-COH, exload instance-independent; [R14.3] W5d-G G0 only) + s1–s5 + [OWN.24].  Audited
hardest: (1) every NEW file:line rev 18 cites (the `Vtest` lines nobody had checked); (2) whether the Stage-1 launch
set at the top of §C (plan:777-788) is launchable AS WRITTEN — file-disjoint workers, correct dependencies, a W-COH
brief whose acceptance catches what the cone build cannot; (3) the standing (a)–(e) checks on the published statement
and the sRVWMO claim.  `file:line` cites `../xv6iris-weak`.  Advisory only; no proofs or builds; no git/jj; no subagents.

**Sign-off.**  YES — I would launch the Stage-1 set exactly as written at plan:777-788: **W5b′ → W2 (table +
instance-independent rows), W-COH (+ `Weak/TsoOfPf.lean` + `Vtest`, built explicitly), W13 (E) → (T), W5d-G G0 only,
W1b**.  Every rev-18 text is correct against the code; no REQUIRED change.  Six suggestions, one of which ([R15.s1],
W2's output FILE) must be settled before W2's brief is written — W2 launches after W5b′, so today's launch is
unaffected.  Found verifying, both harmless: `Weak` IS a default `lake build` target (`lakefile.toml:2`) though not in
the CI/README build command (`lake build Xv6 MachCSL`), and `Vtest` has one more `coh` reader (`lowView`,
`HartExec.lean:206-207`) that W-COH leaves alone.

## What was verified (holds as cited; not to re-litigate)

**[R14.1] applied correctly** (header plan:4-8; §B(12) :767-770; §C W-COH :924-939; §D G2-Q :1294-1296).  Code:
`TsoOfPf.tsoAfterLoadCoh` (`Weak/TsoOfPf.lean:171-174`) is `simp only [HRead.afterLoad]; rw [if_pos …]` — it UNFOLDS
`HRead.afterLoad` and states "every footprint byte = `tvn`" ✓; the G2 docstrings `:14-16` and `:212-214` record the old
semantics ✓; `g2Tso :215-225` is over `Hist.read`/`histOf` only ✓; `Weak.lean:624` imports it ✓.  `Vtest`:
`XState.afterLoadHR`/`afterLoadHR_eq` (`vtest-lean/Vtest/XState.lean:234-247`, `unfold afterLoadHR HRead.afterLoad`),
`XState.afterLoad :244`, `abs_afterLoad :247-250`, `XState.store :283-291` (`hr := h.hr.clearAcq`), `abs_store :293-`
✓; `HartExec.lean:242-244` calls `x.afterLoad`, `:328` `x.store … (akExcl …)` ✓; `cohOkB :56-61` is `HRead.cohOk`'s
boolean twin — unchanged if `cohOk` keeps its type ✓.  `lakefile.toml:43-50`: `Vtest` is a `lean_lib` NOT in
`defaultTargets` ✓; `tools/ci/audit.sh:13-16` ("Weak/ is not in the Xv6/MachCSL build CI audits") and `:51` (`lake build
Xv6 MachCSL`), `.github/workflows/lean-ci.yml:200`, `README.md:74-75` ✓ — so `lake build Weak.TsoOfPf Vtest` in the
brief's acceptance (plan:935, :769-770) is the right requirement.  The three acceptance lemmas (:936-939) are
well-posed: (ii) `g2Run`'s second load at `tvn = 0` reads byte `c = 0` — legal under (a′) because the first load
(`g2St`, `TsoOfPf.lean:179-182`: footprint `(a, b)`, `a` from hart 1's store at ts 2, `b` from the IMAGE at `t = 0`)
stamps only `a` (foreign, `coh a := 2`); `b`'s image entry stamps `max (coh b) 0`, a no-op (whatever its `tid`), so the
second load's footprint `(b, c)` has `coh = 0` and `cohOk` at 0 holds ✓; (iii) the `m0`/`w_c'` schedule exists: hart A's `tv = 0` (no fence/aq), `coh a` unstamped (own `m0`), `coh c = 0`,
so `r` at `tvn = 1` is legal and reads `w_c` ✓.  `mmOk_afterLoad`'s `bound` (`Resources.lean:788-800`, `coh a ≤ top`)
survives: a FOREIGN visible entry has `t ≤ tvn ≤ top` (`HEnt.visible`, `TsoMem.lean:115-116`), own-sourced bytes are
unstamped ✓; `memModelAt` (`:946-951`) and `resvMap_get?` carry `resv`/`acq`, never `coh` ✓.
**[R14.2] applied correctly** (§C top :779, :784-788; §C W2 :824-836; Status :1234-1235; D26 :1591-1592; acceptance
table :541-546).  Code: `MState.store … (excl : Bool)` is ONE function (`Lang.lean:147-153`), `hr := clearAcq`, `tv`
moves iff `excl && acq` (`:150`) ✓; `evStep`'s `.memWrite` RAM arm `σ' = σ.store cpu req.pa n w (akExcl …)` (`:372-375`)
realizes BOTH `LStore` and `LExStore` ✓; the exclusive READ arm goes to `σ.afterExcl` (`:368-371`) and
`HRead.afterExcl … = ⟨top, hr.coh, acq⟩` keeps `coh` (`TsoMem.lean:274`) ✓ — exload IS the instance-independent row.
`MState.fence` (`:155-163`) touches `tv`/`itv` only (`rv`, `coh`, `acq` untouched) ✓; `dmaRead` `σ' = σ` (`:536`),
`storeDma` writes `mem`/`log` only (`:168-170`) ✓; `hartStep .pure` `σ' = σ` (`:500-502`) ✓.  "exstore" survives only
in the three "NOT exstore" corrections (:9, :826, :1234) ✓.
**[R14.3] + [OWN.24] applied correctly**: §C top "W5d-G G0 ONLY … G1–G5 per D26, AFTER W13 (M)" (:782-783); §C
W5d-G "Then, AFTER W13 (M) (D26; …)" (:1082-1083); Status (:1236-1237); D26 (:1586-1593, "§C top, §C W5d-G and Status
agree") ✓; `grep "then G1"` = 0 ✓.  Q-W5dG-seq (:1596-1615) is in the plain-language format (Spec line, statement,
tiny example, definitions, why it matters, three options with cost/unblocks/risk) and RULED (a) ✓.
**s1–s5**: (s1) :1557-1568 all three options have unblocks/risk ✓; (s2) :861-863 wildcard `LDev` arms ✓; (s3)
:907-910 reset with `excl = true`, `top + 1` note ✓; (s4) :936-939 three named lemmas ✓; (s5) :18, :1541 "REPORTS (no
gate)" ✓ — `grep -i coordinator` hits the header history and §D only; no "to confirm" ✓.
**(a) `Xv6.Allocproc`**: `LinkAllocproc.lean:14-16` ✓; `wp_allocproc_body` `SpecAllocproc.lean:204-224` with exactly
§A(1)'s premises ✓; `roots.txt:6,19` ✓; `baseline.json:11-14` = 3 axioms + 3 opaques ✓.
**(b) TsoMem vs sRVWMO**: residue table `WeakAxiomatic3.lean:2051-2071` (1–5, 7, 14 IN; 6, 9-load, 12 OMITTED) ✓;
litmus divergences LB + reader-fence-only MP `WeakSrvwmoLitmus.lean:1663-1695` ✓; TsoMem header `TsoMem.lean:1-39`
(stores never early; load–load reordering; reservation blocking; non-coherent I$) ✓; `NCPU = 8 :54`; `hartAgent c =
c.val :59`, `diskAgent = NCPU :60`, `ifetchAgent :61` — the (a′) foreign test is well-typed, DMA entries foreign, the
fetch agent never authors ✓.
**(c) Launch-set file-disjointness** (the "one worker, one file each" rule, plan:774): W5b′ = new `Weak/TsoShadow.lean`
(absent ✓) + `PfRunShape.lean` (its only `match` is `pfStepFacts :266-270`, wildcard ✓); W-COH = the 7 MachCSL files
(grep `afterLoad|cohOk`: `Lang` 4, `Resources` 4, `TsoMem` 2, `UIcache` 2, `WpAtomic` 2, `Wp` 8, `WpSmodeFenceFloor` 8 —
exactly the plan's list) + `TsoOfPf.lean` + `Vtest/XState,HartExec`; W13 (E) = the `Wlabel.LDev`-arm files (28 by
arm-regex — NONE of `PfRunShape`, `SrvwmoXv6Witness`, `TsoOfPf`; `SrvwmoXv6Witness.lean:42` mentions `LDev` in a
comment only); W5d-G G0 = a new file whose statements (`W5dG-spike.md:66-87`) use existing `gnxw`/`gwrites`/`gmsg`/
`Hemission` and match `(.LIFetch base tvs, none)` NON-exhaustively (`:86-87`), so (E)'s new constructor does not break it;
W1b = `Xv6/` only.  Pairwise disjoint ✓.  `Xv6/` names none of `afterLoad`/`cohOk`/`HRead`/`.coh` (grep = 0) ✓, so
W-COH's cone rebuild is a rebuild, not a re-proof.

## REQUIRED changes

None.

## SUGGESTIONS

- **[R15.s1] (settle BEFORE W2's brief) Name W2 proper's output file.**  Plan:774 says "one file each" and names every
  launch item's file except W2's: §C W2 (:817-839) names only the SPIKE's `Weak/TsoOfPf.lean`, and `histOf` — W2's
  `R-hist` — lives there (`TsoOfPf.lean:58`), so a W2 worker would naturally extend that file; but W-COH edits it in
  parallel (:924-939: restated `tsoAfterLoadCoh`, two docstrings, three new lemmas).  Add at :818: "W2 proper lands in
  a NEW `Weak/PfStepTso.lean` importing `Weak.TsoOfPf` (for `histOf`/`fenceRow`) and `Weak.TsoShadow`; `TsoOfPf.lean`
  is W-COH's file during Stage 1 — W2 does not edit it"; mirror in the header's "NOT in any merged file" list (:235-236).
- **[R15.s2] Fix the per-byte input's NAME now, not "name it".**  :918-919 and :928 ask W-COH to name the
  `List (Option (Agent × Nat))` input and W5b′ to mirror it — two PARALLEL workers.  Write the name into the plan, e.g.
  `abbrev LoadSrcs := List (Option (Agent × Nat))`, `HRead.afterLoad (hr) (pa) (n) (tvn) (srcs : LoadSrcs)`,
  `Hist.readEnt (h) (tv) (H) : Option HEnt`, and on the pf side `pfLoadSrcs (log) (i) (base) (tvs) : LoadSrcs`
  (`wmTid`, position + 1) in `TsoShadow.lean`.
- **[R15.s3] The restated `tsoAfterLoadCoh` (:927, "foreign-stamped byte ↦ its source position") must be stated
  with `max`.**  `HRead.afterLoad` is a pure function of `hr`; without a `cohOk` premise "`= t_a`" is false for an `hr`
  with `coh a > t_a`.  Write "foreign-stamped byte ↦ `max (hr.coh a) t_a`; own-sourced or unlisted byte ↦ `hr.coh a`"
  (under `cohOk … tvn` and `t_a ≤ tvn` the `max` is `t_a` only if `coh a ≤ t_a`, which the legal-read argument gives
  but the lemma need not carry).
- **[R15.s4] `Weak` IS a default `lake build` target** (`lakefile.toml:2`: `defaultTargets = ["MachCSL", "Xv6",
  "Weak"]`); what omits it is the CI/README command `lake build Xv6 MachCSL` (`lean-ci.yml:200`, `README.md:74`,
  `audit.sh:51`, `run_all.sh:20`); `Vtest` is omitted by BOTH (`lakefile.toml:43-50`, `README.md:75`).  At :934 and
  :767-770 say so, so a worker running bare `lake build` on the VM knows it covers `Weak/` but still not `Vtest`.
- **[R15.s5]** `Vtest`'s `lowView` (`HartExec.lean:206-207`: the fold of `h.hr.coh` over the footprint into `h.tv`,
  the computable MINIMAL view) also reads `coh` — unaffected by W-COH (type unchanged; it computes a smaller view
  under (a′), still `cohOk`), but list it at :930-933 so the worker's grep (XState 10 hits, HartExec 8) matches the
  plan.  Also `Run.lean:139,276` construct `HRead.zero` — unchanged.
- **[R15.s6]** W5d-G G0's brief: say, as [R14.s2] does for W5b′, that the re-created file uses the report's
  NON-exhaustive `(.LIFetch base tvs, none)` patterns (`W5dG-spike.md:86-87`) and no `Lbl`/`Wlabel` exhaustive match,
  so W13 (E)'s `Lbl.LIo` lands beside it without a rebase; and that it must build with `lake build Weak.<file>`
  explicitly (the same CI gap as [R14.1]).

## Owner questions the plan is missing

- **Q-CI-Weak — should the CI build cover `Weak/` (and `Vtest`) now that MachCSL changes (W-COH, then W-RSV) land
  under them?  (engineering; every option FAITHFUL; no memory-model content.)**  *Spec*: not a semantics question —
  RVWMO, the Sail model, Zifencei and the PMAs are silent on how a proof tree is built; every option FAITHFUL.
  *Plain language*: the proof tree has three Lean libraries — `MachCSL` (the machine and its program logic), `Xv6`
  (the kernel proofs) and `Weak` (the weak-memory development, which imports `MachCSL`) — plus the `Vtest`
  device-conformance suite (computable twins of the machine, checked against QEMU captures).  CI and the documented
  build command compile only `MachCSL` and `Xv6` (`lean-ci.yml:200`, `README.md:74`); `Weak` is compiled only when
  someone runs bare `lake build` (`lakefile.toml:2`) or `audit.sh --weak`, `Vtest` only by `vtest.sh check`.  *Tiny
  example*: W-COH changes the type of `HRead.afterLoad` in `MachCSL/TsoMem.lean:268`; `Xv6` and `MachCSL` build green
  (nothing there unfolds it); `Weak/TsoOfPf.lean:173` and `vtest-lean/Vtest/XState.lean:241` no longer type-check, and
  CI says nothing — R14 found this by hand and rev 18 patched the W-COH brief ("build `Weak.TsoOfPf Vtest` explicitly").
  W-RSV (12 `Xv6/` files, 25 MachCSL files) comes next on the same lane with the same blind spot, and every later
  MachCSL touch inherits it.  *Why it matters for the published theorem*: nothing in the STATEMENT changes; the risk is
  a merged MachCSL change silently breaking the `Weak/` chain the published theorem is built on (the 33k-line Tier-2
  chain, W5b/W5c's landed files), discovered weeks later by a Stage-2 worker.  *Options*: **(a) add `Weak` to the CI
  build** (`lake build Xv6 MachCSL Weak`, and `vtest.sh check` as a CI step — the latter already exists as `check-ci`,
  `lean-ci.yml:240`): what changes — one line in `lean-ci.yml` and `run_all.sh`; FAITHFUL; cost — CI wall-clock grows by
  the `Weak` build (the chain is ≈ 33k lines plus the retired `Ax*` tier; the increase is **unverified**, plausibly
  tens of minutes); unblocks — every MachCSL brief drops its explicit-build clause; risk — a red scratch file in
  `Weak/` (the spikes are merged, `Weak.lean:620-624`) blocks the kernel CI.  **(b) keep as is; briefs name the
  extra builds** (rev 18's state): cost 0; risk — the blind spot recurs on every MachCSL item; the reviewer, not CI, is
  the gate.  **(c) a cheap smoke target**: CI builds `Weak.PfRunShape Weak.SrvwmoXv6Witness Weak.TsoOfPf` (the Stage-0
  files that import `MachCSL` most directly) plus `vtest.sh check` — minutes, not the whole chain; catches exactly the
  W-COH/W-RSV breakage class; misses deep-chain breaks (those import `MachCSL` only through `WeakLang`/`WeakInterp`,
  whose MachCSL surface W-COH/W-RSV do not touch — **unverified** for W-RSV's `blockedStep` consumers,
  `Weak/WeakLang.lean:52`).  Recommendation: (c) now (S, one CI line), (a) when Stage 2 starts touching `Weak/` on the
  critical path.
