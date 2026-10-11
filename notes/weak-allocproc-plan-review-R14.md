VERDICT: NOT SATISFIED

# Review R14 of `notes/weak-allocproc-plan.md` rev 17 (adversarial, evidence-based; 2026-10-10)

Scope (per the R14 brief): rev 17 = R13's two required changes + s1–s5 + the Stage-1 launch set at the top of §C.
Audited hardest: (1) the [R13.1] text (W-RSV (i-a) per-lane census: 16 rules / 9 files, 25 MachCSL incl. the 35
`wp_m_*` statements, 12 `Xv6/` files) against the code; (2) the [R13.2] text (W2's hart `LLoad`/`LStore` rows after
W-COH) — and, adversarially, whether the rows the plan now calls "instance-INDEPENDENT" really are; (3) whether EVERY
item of the Stage-1 launch set is launchable AS WRITTEN with correct dependencies and a worker brief that cannot break
the tree; (4) the new OWNER QUESTIONS FORMAT against §D; plus the standing (a)–(e) checks.  `file:line` cites
`../xv6iris-weak`.  Advisory only; no proofs or builds; no git/jj; no subagents.

**Sign-off.**  NOT as written — three REQUIRED changes, all S text fixes to worker-facing lists, none touching the
published statement: **[R14.1]** W-COH's file list omits the MERGED `Weak/TsoOfPf.lean`, which UNFOLDS `HRead.afterLoad`
(`tsoAfterLoadCoh`, `TsoOfPf.lean:171-173`) — the signature change the plan prescribes breaks the Weak lane, which the
MachCSL/Xv6 CI does NOT build (`tools/ci/audit.sh:13-16`), so a W-COH worker launched on the plan's list lands green
and leaves `Weak.lean:624` red; **[R14.2]** W2's "exstore" row is NOT instance-independent: `LExStore` is realized by
`MState.store … (akExcl …)` (`Lang.lean:372-375`), the SAME function as the plain store (`:147-153`, `excl` is a
parameter), which W-COH changes (the `coh` RESET) — the plan's parenthesis "(`afterExcl` keeps `coh`)" describes the
exclusive READ; **[R14.3]** the launch set and the Status line say "W5d-G G0 then G1–G5" NOW, while D26 — the
sequencing of record — puts G1–G5 AFTER W13 (M); G1/G3/G5 edit `Fab`/`Supply`/`Acyc`/`Glue`/`Hull`/`Topo`, the files
W13 (I)/(K)/(M) rewrite.  Everything else audited holds.  **May launch now, with the three corrections in the
briefs**: W5b′, W2 (instance-independent rows minus `LExStore`), W-COH (+ `TsoOfPf.lean`), W13 (E) → (T), W5d-G G0
only, W1b.

## What was verified (holds as cited; not to re-litigate)

**[R13.1] applied correctly** (plan:930-955, :1460-1465, :1479-1494, header :4-11): `wp_m_*` declarations =
`WpMmode.lean` 8, `WpMmodeAlu` 9, `WpMmodeCsr` 16, `WpMmodeCtl` 1, `WpMmodeMret` 1 = **35** ✓; `grep -c "ctxTok\|
resvFrag\|kctx"` = 0 in four of the five, 4 in `WpMmode.lean` (all `wp_m_ld_same`) ✓; `Xv6/` applications `ProofEntry`
8, `ProofStart` 39, `ProofTimerinit` 21 = 68 ✓ (`ProofSpin` 4 more, its own `wp_m_j`); spec bodies carry `ctxTok cpu
curCtx` at `SpecEntry.lean:48`, `SpecStart.lean:62`, **`SpecTimerinit.lean:56`** (the plan corrected R13's `:57`) ✓;
`wp_spin_body` (`SpecSpin.lean:34-42`: `mConf ∗ clockCells ∗ pcIs ∗ gprFile ∗ kernelText ⊢ wpLoop`) holds NO token ✓;
`ProofSpin.lean:43` applies `wpLoop_m_instr`, `:35` `wp_m_j`, `:50` `spin_loop` ✓; `SPIN`'s only consumer is
`LinkSpin.lean:14` ✓.  `UserretEntryPt.lean:164` frames `∃ r : Option Resv, resvFragAny cpu r` across the `fence.i` ✓;
`kctx_cases` yields `Htok` at `WpSmodeWait.lean:257` ✓.  s1 (9 files, plan:923-927) ✓, s2 (`trapBranch` both arms,
:927-930) ✓, s3 (`Hist.readEnt`, :889-892) ✓, s4 (`wp_m_ld_same` template, :941-942) ✓, s5 (Status "waits for W-COH
… and for M1 (D26)", :1198-1199) ✓.  The §D "Census DELTA" paragraph (plan:1495-1516) is in the new plain-language
form (statement, tiny example, definitions of `resvFragAny`/`kctx`/`wp_m_*`/the M-mode lane, why it matters, per
option) ✓ — see [R14.s1] for the one missing column.
**[R13.2] applied** at the §C top (plan:762-770), §C W2 (:803-815), Status (:1191-1193), D26 (:1538-1539); W1b
"RULED-in by [OWN.16] (c); schedule at the owner's discretion (D10)" (:796) ✓.  The machine facts behind it:
`MState.afterLoad` `{ σ with hr := updCpu σ.hr cpu ((σ.hr cpu).afterLoad pa n tvn) }` (`Lang.lean:127-129`; `σ.mem` in
hand) ✓; `HRead.afterLoad hr pa n tvn` stamps the footprint with `tvn` (`TsoMem.lean:268-270`) ✓; `HRead.afterExcl`
`⟨top, hr.coh, acq⟩` keeps `coh` (`:273`) ✓; `clearAcq :276`, `bound :279-280` ✓; `MState.fence` touches `tv`/`itv`
only (`Lang.lean:155-163`) ✓; `dmaRead` `σ' = σ` (`:536`), `storeDma` writes `mem`/`log` only (`:168-170`) ✓; `Hist.read`
returns the value only (`TsoMem.lean:119-120`) ✓.
**(a) `Xv6.Allocproc`**: `LinkAllocproc.lean:14-16` ✓; `wp_allocproc_body` `SpecAllocproc.lean:204-224` with exactly
§A(1)'s premises (`kctx`, `procsInv`, two `isLock`s, `kallocAvail`, `procsAvailAt`, `□ (killCred -∗ Q (-1))`,
`actLend`, `wpNext` with the `sieArm` arm) ✓; roots `roots.txt:6,19` ✓; `baseline.json:11-14` = 3 axioms + the 3 opaques ✓.
**(b) TsoMem vs sRVWMO**: the residue table (`WeakAxiomatic3.lean:2050-2071`: 1–5, 7, 14 IN; 6, 9-load, 12 OMITTED)
and the litmus record (`WeakSrvwmoLitmus.lean:1663-1695`: LB and reader-fence-only MP are the two divergences) ✓;
`evStep`'s plain-load arm with `cohOk` (`Lang.lean:363-367`), exclusive-read arm `¬ othersReserve` + `topBytes` +
`afterExcl` (`:368-371`), store arm `¬ othersReserve` → `σ.store … (akExcl …)` (`:372-375`), DMA `¬ anyReserve`
(`:539`) ✓; `hartStep`'s `.pure` arm `σ' = σ` (`:499-502`) and `wpLoop_restart` resource-free (`Wp.lean:385-400`) ✓.
**(c)/(e)**: W5b's `pfStepFacts`/`pfRunS` over `List (Nat × Wlabel)` with `pfStepFacts fok c1 i l` on the PRE-config
(`PfRunShape.lean:265-277`) ✓ — W5b′'s "shadow of the prefix `st`" is the right hook; `Weak/TsoShadow.lean` absent ✓.

## REQUIRED changes

**[R14.1] W-COH's file list omits `Weak/TsoOfPf.lean` (MERGED, `Weak.lean:624`), which unfolds `HRead.afterLoad` —
the signature change breaks the Weak lane, and the MachCSL/Xv6 CI does not build it.**  Evidence: the plan prescribes
"only `HRead.afterLoad` (`TsoMem.lean:268-270`) gains the per-byte stamp input" (plan:888) and lists W-COH's files as
"the 7 of §D G2-Q plus the store rules' sites" (plan:894-896; §D: `TsoMem`, `Lang`, `Resources`, `Wp`, `WpAtomic`,
`WpSmodeFenceFloor`, `UIcache`, plan:1246-1250) — the grep of `afterLoad\|cohOk` outside `TsoMem.lean` gives exactly
those 7 MachCSL files PLUS **`Weak/TsoOfPf.lean` (2 hits)**: `theorem TsoOfPf.tsoAfterLoadCoh (hr : HRead) (pa :
PAddr) (n tvn j : Nat) … (hr.afterLoad pa n tvn).coh (pa + …) = tvn := by simp only [HRead.afterLoad]` (`:171-173`) —
ill-typed under the new arity, and its STATEMENT (every footprint byte stamped `tvn`) is exactly what (a′) makes
false.  `tools/ci/audit.sh:13-16`: "Weak/ is not in the Xv6/MachCSL build CI audits" — a W-COH worker building the
`Xv6` cone per §B(12) sees green.  `g2Tso` itself (`:215-225`) is stated over `Hist.read`/`histOf` and survives, but
its docstring (`:212-214`, "it stamps byte `b`'s floor with `tvn₁` (`tsoAfterLoadCoh`), so the second load runs at a
view ≥ 2") and `TsoOfPf.lean:14`'s header record the OLD semantics, and the plan's acceptance "`g2Tso`'s witness now
has a TsoMem schedule" (plan:897-898) names no lemma.  **Change**: in §C W-COH (plan:894-896) and §D G2-Q (a′)'s cost
line (plan:1245-1250) add "**+ `Weak/TsoOfPf.lean`** (MERGED): re-state `tsoAfterLoadCoh :171-173` for the new
`HRead.afterLoad` (foreign-stamped byte ↦ its source position; own-sourced byte ↦ unchanged) and replace the G2
docstrings `:14`, `:212-214`; acceptance = a NEW lemma `g2TsoSched` (or similar) exhibiting the TsoMem schedule of
`g2Run` under the new `afterLoad` (second load at `tvn = 0` reading byte `c = 0`)"; in §B(12)/the W-COH brief require
`lake build Weak.TsoOfPf` (or the `--weak` lane) in the worker's acceptance, since the cone build cannot catch it.
Also note W5b′ (parallel) defines `tsoShadow`'s stamp instance from the SAME per-byte input — name it in `TsoOfPf`'s
restated lemma so the two agree ([R13.s3] already asks for the name).  S.

**[R14.2] The "exstore" row is W-COH-DEPENDENT, not instance-independent: `LExStore` is realized by `MState.store`,
the same function as the plain store.**  Evidence: the plan's instance-independent list reads "the store-reservation
side, exstore (`afterExcl` keeps `coh`, `TsoMem.lean:273`), fence …" (plan:763-764, :806-807) — but `afterExcl` is the
EXCLUSIVE READ's post-state (`evStep` `.memRead` arm with `akExcl`, `Lang.lean:368-371` → `σ.afterExcl`); the exclusive
STORE is `evStep` `.memWrite`'s RAM arm `σ' = σ.store cpu req.pa n w (akExcl req.access_kind)` (`:372-375`), and
`MState.store … (excl : Bool)` (`:147-153`) is ONE function whose `hr` update is `clearAcq` today and `clearAcq` +
the (a′) RESET after W-COH (plan:881-883: "`MState.store` resets `coh` on its footprint (a new `HRead.resetCoh pa n`
beside `clearAcq`)" — no `excl` case split, and none is wanted: cat's `po-loc-no-w` exemption counts an SC/AMO write
as a write).  So the `LExStore` row's `hr_T = hr_S` has exactly the hart-`LStore` row's dependence ([R13.2]).  The
exclusive-READ row (`LExLoad`: `afterExcl` keeps `coh`) IS instance-independent and is the row the parenthesis
describes.  **Change**: in the §C top launch set (plan:763-764), §C W2 (plan:806-807) and the Status line (:1192)
replace "exstore (`afterExcl` keeps `coh`, `TsoMem.lean:273`)" by "**exload** (`LExLoad`: `afterExcl` keeps `coh`,
`TsoMem.lean:273`)", and extend the W-COH-dependent clause to "the hart `LLoad` row's `afterLoad` post-state and the
hart `LStore` AND `LExStore` rows' `coh` RESET (both through `MState.store`, `Lang.lean:147-153,372-375`)"; mirror in
D26 (plan:1538-1539: "`LLoad`/`LStore`/`LExStore` post-states after W-COH").  The acceptance table's `LStore` row
"records BOTH shadow effects" (plan:531-532) — add that the `LExStore` row records the same two (reset + `resv :=
none`) plus the `excl && acq` floor move (`Lang.lean:150`).  S.

**[R14.3] The launch set and the Status line launch W5d-G G1–G5 NOW; D26 sequences them AFTER W13 (M).  Make the
three agree (recommended: D26's order).**  Evidence: §C top "W5d-G G0 (re-creation) then G1–G5" (plan:766); Status
"W5d-G G0 (re-creation) then G1–G5 (D41–D43 RULED)" under "Now launchable" (plan:1194); §C W5d-G "G0 … Then the
spike's change list: G1 …" (plan:1037-1041) — versus D26 (plan:1533-1537): "{W5b′ → W2 … ∥ W13 (E) → (T) ∥ **W5d-G G0**
∥ W-COH} → W4 → M1 → W-RSV → M2 → W13 (M) (SERIAL: the `gmem` case splits touch every chain file) → {W12 ∥ W12b ∥
**W5d-G G1–G5** ∥ W13 (I)(L)(K)(F-dep)}".  D26's order is the right one: G1 rewrites `gdexecQconf`'s fetch clause
(`WeakRvwmoSupply.lean:277-352`) and `Fab.lean:516-522` — W13 (I) rewrites `Fab.lean:522-535` (`gfexecConfIO`) and (M)
`gdexecQconfT`/`xv6ConfS` in the same files; G3 adds the `Gdexec.gdFetch` field (~31 sites in `Graph`, `Acyc.lean:200`,
`Glue.lean:205-223`, `Hull.lean:714`, `Topo.lean:120-129,594-607`) — W13 (K)'s `racyDIO` and (M)'s `gmem` sweep touch
`Acyc`/`Glue`/`Topo` too; G5 edits `Supply.lean:743-883`, W13 (I) deletes `hblkQ :689-701` beside it.  Launching G1–G5
beside W13 (E)/(T) is survivable, but the plan says NOTHING about the merge order against W13 (M)/(I)/(K), which it
calls SERIAL.  **Change**: at plan:766 and :1194 write "W5d-G **G0 only** (re-creation, S–M; acceptance: builds, each
statement matches `notes/W5dG-spike.md`); G1–G5 per D26, after W13 (M)"; at plan:1041 "Then, AFTER W13 (M) (D26), the
spike's change list: G1 …".  (If the author instead wants G1–G5 now, D26 and W13 (I)/(K)/(M)'s "SERIAL" text must say
who rebases on whom — the owner question below.)  S.

## SUGGESTIONS

- **[R14.s1]** The §D Census DELTA (plan:1510-1515) meets the FORMAT except the "what it unblocks / risks" column:
  add for **(i-a)** "risk: one `Xv6`-cone rebuild (≈ 0.65M lines) on the serial lane; 35 statement edits are
  mechanical but each `wp_m_*` caller site (68) must be re-threaded by hand"; for **(i-b)** "unblocks: W-RSV without
  the cone rebuild — the serial lane W-COH → W4 → M1 → W-RSV → M2 shortens by that build; risk: the invariant must be
  openable at the three `swp_*_au` rules AND the boundary rule under `wpLoop`'s mask — a new Iris invariant in `Ctx`,
  19 `ctxTokAt` sites and ≈ 30 `uResvTok` mentions re-proved, the user-lane walker frames (`URunRW.lean:501-502`)
  included"; for **(ii)** "unblocks nothing (i-a) does not; risk: `resvName`'s type changes at `Resources.lean:122,433,
  475` and two `Xv6/` constructions".
- **[R14.s2]** W5b′/W2 run in parallel with W13 (E), which gives `Wlabel.LDev` a payload (`WeakPromise.lean:86`,
  plan:1059).  `PfRunShape.lean:14` already notes it for W5b; say the same in W5b′/W2's brief: `tsoShadow` and
  `pfStepTso` match `LDev` with a WILDCARD arm (`| .LDev .. => …`), never an arity-specific pattern, so (E) joins
  without a rebase.
- **[R14.s3]** W-COH's `HRead.resetCoh pa n` on the EXCLUSIVE store: record in §C W-COH that the reset applies to
  `excl = true` too (cat's `po-loc-no-w` counts the SC/AMO write), so a worker does not add an `excl` case split; and
  that with `excl && acq` the floor already moves to `top + 1` (`Lang.lean:150`), so the reset there is harmless but
  still performed (uniformity with the shadow's store effect).
- **[R14.s4]** The W-COH acceptance (plan:897-898) should name its lemmas: (i) the restated `tsoAfterLoadCoh`; (ii)
  "`g2Run` has a TsoMem schedule" as a theorem in `TsoOfPf.lean` (the second load at view 0 reads byte `c = 0`);
  (iii) §B(10)'s own-store counterexample realized (`m0`/`w_c'`: byte `c` reads `w_c`) — three `decide`/`simp`
  facts over `histOf`, S.
- **[R14.s5]** Plan:8 and :1495 now mention "the coordinator" (reporting instructions, not gates) — R13's "`grep -i
  coordinator` hits only the header" record is stale; say "coordinator REPORTS (no gate)" once so the next reviewer's
  gate check is not tripped.

## Owner questions the plan is missing

- **Q-W5dG-seq — when do W5d-G's G1–G5 start?  (engineering: every option FAITHFUL; no memory-model content.)**
  *Spec*: not a semantics question — RVWMO, Sail, Zifencei, PMAs are silent on how proof files are sequenced.
  *Plain language*: W5d-G is the graph-tier fetch model (how the published theorem accounts for instruction fetch —
  which bytes a hart executes — when user text is written by `exec` and made visible by `fence.i`).  Its day-one step
  G0 re-creates a lost scratch file from a report; G1–G5 then edit the SHARED chain files (`Fab` = the fabric/device
  conformance bundle, `Supply` = how a graph yields a candidate execution, `Acyc`/`Glue`/`Hull`/`Topo` = the
  cycle-kill and linearization machinery).  W13 — the I/O-events redesign, XL — edits the SAME files in its (I), (K)
  and (M) pieces, and the plan calls (M) SERIAL because it touches every chain file.  *Tiny example*: worker A (G3)
  adds a field `gdFetch` to the structure `Gdexec` and fixes its 31 construction sites; worker B (W13 (M)) changes
  `gmem` (which events count as memory events) and re-proves the case splits in the same 31 files; whoever merges
  second re-does both edits by hand across ~30 files.  *Why it matters*: no change to the theorem; schedule and
  rework only — but D26 (the sequencing of record) and the launch set disagree, so the first worker launched decides
  the order by accident.  *Options*: **(a) D26's order — G0 now, G1–G5 after W13 (M)**: what changes — the launch set
  and Status drop "then G1–G5"; faithful; cost 0; unblocks a clean G1–G5 on the post-(M) chain; risk — W5d-G's XL hull
  risk R1 (§B(4)(iii)) is discovered later, after W13 (M) (weeks).  **(b) G1–G5 now, W13 (M) rebases on them**: what
  changes — D26 moves G1–G5 into the Stage-1 set and W13 (M)'s brief says "rebase on `gdFetch`/`emZifencei`";
  faithful; cost — W13 (M)'s sweep grows by the fetch fragment's arms (S–M) and one rebase; unblocks — R1 is probed
  early (G4's retime invariance is where it bites); risk — two XL-adjacent items in flight on the same files.  **(c)
  G1–G2 now (fetch sites + tags, `Supply`/`Conf` only), G3–G5 after (M)**: the split that keeps `Acyc`/`Glue`/`Topo`
  single-writer; faithful; cost 0; unblocks the `emZifencei` text early for W13 (I)'s `gfexecConfIO`; risk — G1's
  `Fab.lean:516-522` edit still meets W13 (I)'s `:522-535`, one small rebase.  Recommendation: (a) unless the owner
  wants R1 probed early, then (c).
