VERDICT: NOT SATISFIED

# Review R38 of `notes/weak-allocproc-plan.md` (rev 40) — W13 (F-dep) graph-side gap

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git/jj, no subagents).  Scope per the R38
brief (narrow, memory-model): the W13 (F-dep) worker's STOP finding `~/dev/weak-orch/parked/PROGRESS-W13Fdep.md` against
rev 40 §C W13 (F-dep) (`:3665-3692`) and its launch paragraph (`:2107-2112`), the §A model text (`:654-658`, `:676-682`,
`:856-866`), D50 (`:5251-5259`).  Every cite below was read at the working-copy tip of `../xv6iris-weak`.  R37 (SATISFIED,
no required changes) verified R36's application; nothing there is re-opened.  The W12 (+W12b) worker is RUNNING in w1 on
`allocproc_S2_w1_prompt.txt` (batch approved [OWN.48]); what it must know is [R38.6].

**Sign-off.**  NO.  The worker's finding is CORRECT in substance: the plan's §C W13 (F-dep) clause tells the worker to emit
dependency edges that the published model's well-formedness `gtdepsWf` cannot hold, so the plan, executed as written, makes
the published premise `rvwmoCatConsistentT GT ∧ gdexecQconfT GT` FALSE on every xv6 run that prints a byte (vacuity), and its
sub-clause "(2) `dstepT`/`dstep` arms" kills the planned non-vacuity witness W13-wit through the UNTAGGED route.  The fix is
a model-TEXT decision the plan does not make; I make it below (option A, rule-12 shape to be RULED: Q-FDEP), and it is
option-independent enough that the worker can be relaunched once [R38.1]–[R38.5] are in the plan.  Two details of the
worker's write-up are inaccurate and are corrected in [R38.s2] so they do not propagate into the plan.

## Spec first (what the texts say; shared by every item below)

- **riscv.cat** (herd; not in this tree — fetched by R8, plan `:1515-1518`): `r9 = [R];addr;[M]`, `r10 = [R];data;[W]`,
  `r11 = [R];ctrl;[W]`, `r12 = [R];(addr|data);[W];rfi;[R]`, `r13 = [R];addr;[M];po;[W]`.  `R`/`W` are ALL reads/writes of
  the hart; herd has NO I/O class.  So riscv.cat's dependency edges start at ANY read and end at ANY write (10, 11, 13) or
  any access (9); no `ctrl` edge into a load is ppo.
- **RVWMO chapter** (unpriv. spec, "Preserved Program Order", rules 9–13): the same five rules in prose over "memory
  operations"; rule 12 = "b is a load, and there exists some store m between a and b in program order such that m has an
  address or data dependency on a, and b returns a value written by m".  I/O memory is "not (yet) formalized" (plan `:1515`).
- **Appendix "I/O Ordering" (c1)** (plan `:1519-1523`, quoted from `mm-explanatory.adoc`): when one access is I/O, "memory
  access a precedes memory access b in global memory order if a precedes b in program order and" a ppo rule of the RVWMO
  chapter holds, "with the exception that acquire and release ordering annotations apply only" memory→memory and I/O→I/O.
  Hence the FAITHFUL reading: dependency edges may START at an I/O load and END at an I/O store or I/O load; no ctrl→I/O-load
  edge; rule 12 with an I/O-load source into a RAM store forwarded to a RAM load IS ppo.  (Explanatory text, "generally
  applies": non-normative — already named by the plan, D50.)
- **Sail** (`vendor/lean-sail`): a sequential ISA model; MMIO is an ordinary `mem_read`/`mem_write` routed by `devAddr`
  (`MachCSL/Dev/Fabric.lean:125-126`); it has NO dependency or inter-hart ordering semantics — SILENT.  **Zifencei**: fetch
  only — SILENT.  **PMAs**: channel ordering among I/O accesses and the FENCE pointer for I/O vs main memory (plan `:4303-4310`);
  nothing on register dependencies — SILENT (the non-idempotency "no speculative access" sentence is a reading, not a ppo rule;
  D50).

## The two gaps, verified against the code

**Gap 1 (tagged model; CONFIRMED).**  `gtdepsWf` (`Weak/AxDeps.lean:168-171`), a conjunct of the PUBLISHED model
`rvwmoCatConsistentT` (`:208-211`, plan `:1378`), requires every tagged edge's SOURCE to satisfy `glblIs G e.1.1 lbIsR` and,
for `dtagW` tags (`DTdata`/`DTctrl`/`DTtrans`/`DTr13`, `:150-152`), the TARGET to satisfy `lbIsW`; only `DTaddr`/`DTctx`
targets are `gmem`.  `lbIsR`/`lbIsW` (`Weak/WeakAxiomatic.lean:174-182`) match `LLoad`/`LRmw` resp. `LStore`/`LRmw` ONLY —
`Lbl.LIo` (`:98`) is `false` in both (D47 (a), plan `:5218-5222`).  The plan's (F-dep) clause (`:863-865`, `:3671-3677`,
D50 (b) `:5256-5258`) orders the worker to emit `DTdata`/`DTctrl`/`DTtrans`/`DTr13` edges INTO I/O stores and every edge
OUT OF an I/O load, and §A(†) `:831` / W12 (5) `:3494-3495` put `rowDepsT ⊆ GT.gtDeps` into `gdexecQconfT`/`xv6ConfS`.
Therefore `rvwmoCatConsistentT GT ∧ gdexecQconfT GT` is UNSATISFIABLE on every row with such an edge.  Concrete, hart 0's
first `printk` (consoleinit → `consputc` → `uartputc_sync`, `0x800009ac–0x80000a14`): `acquire`'s `amoswap.w.aq`/loads
(RAM) → `dtCtl` (never reset, `AxDeps.lean:461-463`) → **`DTctrl` into the THR store `sb a5,0(a3)` `0x800009fa`** (an `LIo .wr`:
`dtagW DTctrl = true`, needs `lbIsW` — FALSE); the LSR poll `lbu a5,0(a4)` `0x800009ec` (an `LIo .rd`) → `beqz` → the same THR
store (**an I/O-load SOURCE**, needs `lbIsR` — FALSE); in the echo path the RHR byte (`0x80000a64`, census `W13-io-census.md:48`)
flows as `DTdata` into THR (`0x800009fa`), I/O→I/O.  Other definite instances: `uartwrite`'s THR `0x80000988` (`DTdata` from the
RAM tx-buffer load), virtio init's six address-register stores `0x80005a46…a70` (`DTdata` from the RAM `disk.*` loads),
FEATURES → DRIVER_FEATURES `0x800059b2` (I/O→I/O data).  The worker's own example is slightly off, see [R38.s2].

**Gap 2 (untagged route; CONFIRMED).**  Sub-clause "(2) `dstepT`/`dstep` arms" (`:3677`) also puts `LDev` arms into the
UNTAGGED tagger `WeakRvwmoConf.dstep` (`Weak/WeakRvwmoConf.lean:497-499`, inert today).  Its edges enter the untagged graph
through `gfexecConfIO`'s clause `∀ jk ∈ rowDeps em.emItems, … ∈ GF.gfGd.gdDeps` (`Weak/WeakRvwmoFab.lean:857`), whose model
`gfexecConsistent` (`:864`) → `rvwmoMinusDepsConsistent` (`WeakRvwmoGraph.lean:638`) → `gdepsWf` (`:629-631`) demands RAM read →
RAM write.  W13-wit's target event, hart 0's first I/O store, is `ld a5,0(a0)` `0x8000089e` → `sb zero,1(a5)` `0x800008a0`
(`Xv6/KernelImage.lean:1521-1525`), an ADDRESS edge into an I/O store: with an untagged `LDev .wr` arm it lands in `rowDeps`,
`gdepsWf` fails on its target, `gfexecConfIO ∧ gfexecConsistent` is FALSE for that row — the planned non-vacuity witness dies
and `gdexecConfDepsWf` (`WeakRvwmoConf.lean:934-940`, concludes `lbIsW` targets) becomes false.  Also `W12 (1)`'s
`rvwmoCoreD GD := gwf ∧ gloadValue ∧ gatomicity ∧ gdepsWf` (`:3478`) is stated over the SAME untagged `gdepsWf`: any loosening
of it (option B) changes the meaning of every W12 statement while W12 is running.

**Consumers of `gtdepsWf`'s RAM-endpoint shape (what option A must restate).**  `catTAd :301` via `gtdepsWfAd :292` (needs
`gdepsWf (gtAd …)`); `catTForgetAxioms :340` (needs `gdepsWf (forget GT)`) → W12's `catADOfCatT` (`Weak/CatOfMinusSpike.lean:37-43`)
and `RvwmoXv6ScaT.lean`; `catTOfCat :316` with `gtdepsRdOk :310`; `AxSpinGate.gsrcTSrc :247-259` (returns `lbIsR` source and
`lbIsW` target of a ctrl edge; `gsrcTReal' :272` uses the source conjunct, discards the target one) → the gate map `gsrcT :205`
used by `tierAAdequacyAnnGateT` and the REGISTERED LB roots (`allocpidOpen`, `AxSpinT2b.lean:251`, premise `HconsT :
rvwmoCatConsistentT GT`; `rvwmoCatConsistentT` in 36 files, `gtAd`/`gtAdGd` in ~90 `AxSpin*` files, `gsrcT` in 6);
`gtdepsWfB :776` (the Bool checker, `AxSpinSpike.cDw :658`, `AxScCat :249`); `AxScCat.scGraph :112`/`scTdepsGmo :154`/`scPpo :168`;
`AxScRun.gDepsWf :1356` (the SC tier builds `gtDeps` from `rowDepsT`).  `rvwmoCatConsistent` (untagged, `AxGraphCat.lean:188`)
and `gdepsWf` are NOT touched by option A.

## REQUIRED changes

**[R38.1] §C W13 (F-dep) and §A: decide and state the graph-side model change — option A (tagged model generalized; untagged
world unchanged).**  Wrong: the plan has no graph-side sentence at all; D50 (b)'s "FAITHFUL to (c1)" (`:5257-5258`) is true of the
EMISSION shapes only.  Evidence: Gap 1 above.  Change — add to §C W13 (F-dep) as item **(0), the FIRST green increment (statement
commit, S–M)**, and mirror it in §A(3) `:654-657` ("ppo applies to them as riscv.cat is written" + "and the tagged
well-formedness `gtdepsWf` admits I/O-read sources and I/O-write targets"), §A(6) `:679-680` (`rvwmoCatConsistentT`'s TEXT changes
in ONE definition, `gtdepsWf` — a trusted-surface change; the registered LB roots' premise WEAKENS accordingly, their text
unchanged), §A(†) `:858` ("`lbIsR`/`lbIsW` stay RAM-only" + "the tagged dependency well-formedness no longer keys on them
alone") and D50 `:5258` (graph side = this item):
  (0a) `gtdepsWf G deps := ∀ e ∈ deps, same row ∧ po-forward ∧ glblIs G e.1.1 (lbIsR ∨ lbIsIoRd) ∧ (if dtagW e.2 then glblIs G
  e.1.2 (lbIsW ∨ lbIsIoWr) else gmem G e.1.2)` with `lbIsIoRd (LIo .rd ..) = true`, `lbIsIoWr (LIo .wr ..) = true`, `.dev`-kind
  events in NEITHER (device-side fabric moves carry no hart register dataflow — D49).  Marks: FAITHFUL to riscv.cat's `R`/`W`
  under appendix (c1); `gtdepsGmo :174` unchanged (every edge gmo-forward).
  (0b) the chain projections FILTER the source as well: `forgetDeps :175` and `gtAd :185` keep edges with a `lbIsR` source and a
  `lbIsW` target (`gisW` + a Bool `gisRd`), so `catTAd :301`, `catTForgetAxioms :340`, `gtdepsWfAd`/`gtdepsGmoAd`, W12's
  `catADOfCatT` and `RvwmoXv6ScaT.lean:783` keep their STATEMENTS (the untagged chain sees FEWER deps — sound: the residue arms
  (R1)/(R2) `GraphFabResidue.lean:84-99` carry the RAM→I/O and I/O→RAM-store orderings for the chain, as today); `catTOfCat :316`'s
  side condition `gtdepsRdOk :310` is widened to "every edge `forget` drops" (read-targeted OR I/O-endpoint); `tw`/`tw2` (§5)
  still discharge it (no I/O there).  Header deviation list: add "deviation N: `gtdepsWf` admits I/O endpoints (Rocq's is RAM-only)".
  (0c) `AxSpinGate.gsrcT :205` filters its sources to `lbIsR` reads (the `filterMap` gains `gisRd d.1.1`); `gsrcTSpec :210`,
  `gsrcTSrc :247` (target conjunct `lbIsW ∨ lbIsIoWr`, or dropped — `gsrcTReal' :272` does not use it), `gsrcTSrcPo :262`
  restated; `ctrlClosed :232` UNCHANGED (its quantifier is over RAM-write targets and the emission's never-reset `dtCtl` still
  satisfies it).  **Add `Weak/AxSpinGate.lean` to (F-dep)'s files** (no other Stage 2 item lists it — checked against W12's and
  (L)'s lists `:2094-2117`).  The registered roots (`AxSpinT2b.lean:251` and the ~15 `Hcons := catTAd GT HconsT` files) keep their
  text; record in §A(6) and `roots-weak.txt`'s gloss that their PREMISE is now weaker (admits I/O-endpoint deps) — a strictly
  stronger theorem, no re-registration.
  (0d) the Bool/SC tier in step: `gtdepsWfB :776`/`gtdepsWfBSound :784`, `AxScCat.scGraph`/`scTdepsGmo`/`scPpo` (the `gmem`
  of an `LIo` source comes from `lbIsIo`, not `glblIsRGmem`), `AxScRun.gDepsWf :1356` (`rowEdges` generalized) — "the retired
  `Ax*` tier builds" already in the acceptance; name these.
  Acceptance for (0): build green; the tagged premise is SATISFIABLE on an I/O-active row BY COMPUTATION — `gtdepsWfB` over
  `rowDepsT` of W13-wit's row (or of `tw` extended by one `LDev` item) evaluates `true` (this is the check that would have caught
  the gap; it must be a permanent smoke test next to `catTConsistentBSound`).

**[R38.2] §C W13 (F-dep) item (2): the UNTAGGED `dstep` stays INERT on `LDev`; only `dstepT` gets the arms.**  Wrong: `:3677`
"(2) `dstepT`/`dstep` arms".  Evidence: Gap 2 above (`Fab.lean:857`, `:864`; `Graph.lean:629-639`; `KernelImage.lean:1521-1525`).
Change: "(2) `dstepT` arms ONLY (`AxDeps.lean:461-479`): `LDev .rd` = the `LLoad`/`LExLoad` arm shape (`dedgesR :445`: `DTaddr` in,
`k :: dtLd` provenance out, `dtAcc` for rule 13, no ctrl — 'no ctrl → I/O load'), `LDev .wr` = the `LStore` arm shape (`dedgesW :448`),
`.dev` inert; **`WeakRvwmoConf.dstep :497-499` is NOT edited — DEVIATION recorded in the AxDeps header: the untagged tree never
sees I/O edges (sound; `gfexecConfIO`'s `rowDeps ⊆ gdDeps` and `gdepsWf` stay RAM-only; the chain's I/O orderings are (R1)/(R2))**.
Proof obligations restated accordingly: `dstepTState :592` becomes 'the tagged state with I/O-load positions erased from
`dtLd`/`dtProv` equals the untagged state' (or a pointwise INCLUSION invariant untagged ⊆ tagged); `rowDepsSubT :690` KEPT via that
inclusion (tree edge ⇒ tagged edge); `rowDepsTSub :695` restated for RAM-read-sourced edges; `rowDepsTAddr :702-707` (C) gains the
disjunct 'or targets an `LDev .rd` item' (its `elbIsR` test `WeakRvwmoConf.lean:448-451` is false on `LDev`)."  Also correct the
OWNER-FILE list `:3665-3666`/`:2108`: `Weak/WeakRvwmoConf.lean` is no longer an owner file (unless a label test is added there);
the payload type `Wlabel.LDev` lives in **`Weak/WeakPromise.lean:89`** (owner file, missing from the plan); re-examine the
"NOT parallel-safe vs W5d-G G1/G2 (`WeakEvInst` lemma, `WeakRvwmoConf.lean:57-66,147`)" sentence `:2110-2111` — the `Conf` half
of that conflict disappears.

**[R38.3] §C W13 (F-dep) item (1) and the launch paragraph: size the `LDev` payload sweep honestly.**  Wrong: "Size M", arm sites
"`Supply` 4, `FabInd` 2, the witness files" (`:3686-3689`, `:2108-2109`, `:2112`).  Evidence: the payload is an ARITY change of
`Wlabel.LDev`; positional constructor sites (`LDev .rd/.wr/.dev …`, `LDev kd ba bs`, `LDev _ _ _`) number ≈ 177 in 35 files by
grep (the worker counts 146 in 38) — `WeakEvInst` 52 mentions, `WeakRvwmoFab` 31, `WeakRvwmoSupply` 27, `WeakEvCapstone` 23,
`AxOpsem` 15, `WeakRvwmoCert3b` 13, `WeakEvPf` 11, `WeakRobustGraph`/`PfStepTsoView` 9, …; `LDev ..` wildcard patterns need
nothing.  Change: list the files; size (F-dep) **M–L (≈ 1k, three increments)**; land the sweep as increment (1) ALONE (mechanical,
one build) so W12 (`Supply.lean:954`, `Fab.lean:909`) and (L) (`FabInd`) rebase on it ONCE (their sites are disjoint from the
`LDev` sites — still "rebase S" per file, but name the files); the per-row `asrc`/`vsrc` fill in `pnodeStep` (`WeakEvInst.lean:
319`/`:355`; `LIo .rd` as the `LExLoad` arm `:345-346`, NOT the plain `LLoad` arm `:336` — unchanged content, re-cited) is part
of (1).

**[R38.4] §D: add Q-FDEP (rule 12 from an I/O-load source: A1 vs A2) — RULED by the owner; §C carries the non-blocking form.**
Wrong: the plan has no question and no provisional choice.  Evidence: `gppoCatT :195-196` is `gppoCat (gtAdGd GT)`; after
[R38.1] (0b) `gtAd` filters sources, so rule 12 silently LOSES the `[IoR];(addr|data);[W];rfi;[R]` instances (A2) unless
`gppoCatT` is re-pointed at an unfiltered `gtAdFull` (A1).  Change: §C W13 (F-dep) gets "(0e) **provisional A2**: `gppoCatT`
unchanged over the filtered `gtAd` — WEAKER than riscv.cat by the rule-12 I/O-source instances (sound), NAMED in §A(3); **if
Q-FDEP is RULED A1**: `gtAdFull G deps := addr/data edges into `lbIsW` targets, any source`, `gppo12T`/`gppoCatT` over it,
`catTAd` and W12's `catADOfCatT` close by `gppo12` monotonicity (`gtAd ⊆ gtAdFull`, one line each — the second in W12's file
after W12's statement commit, or by W12 itself [R38.6]), `AxScCat.scPpo :168`'s rule-12 case re-cased — S, a separate
increment".  §D gets Q-FDEP in the owner format (text below, ready to paste).  Recommendation: **A1** (faithful; the only
faithful option that keeps the untagged world and W12 untouched beyond one line).

**[R38.5] Header `:3-37`, launch state `:2042-2046`, the (F-dep) launch paragraph `:2107-2112`, history `:526-527`.**  Wrong: the
header still says "awaiting the owner's batch approval" (it was approved, [OWN.48], per the W12 brief) and does not record the
W13 (F-dep) STOP.  Change: rev 41 status — "W13 (F-dep) STOPPED GREEN before any edit (PROGRESS-W13Fdep.md): §C clause
incomplete/wrong on the graph side; FIXED by [R38.1]–[R38.4]; RELAUNCH when rev 41 is signed off"; rewrite the launch paragraph
with the increments **(1) payload sweep → (0) model text + projections + `gsrcT` filter + Bool/SC tier → (2)/(3) `dstepT` arms +
row lemmas + pin bridge → (0e) rule-12 shape after the ruling**, the corrected files (`AxDeps`, `WeakEvInst`, `WeakPromise`,
`AxSpinGate` owners; the sweep list), size M–L, acceptance + the computed satisfiability smoke test of [R38.1]; "No new owner
questions" → "Q-FDEP (provisional A2, recommended A1)".

**[R38.6] W12's launch paragraph `:2098-2100` and the parallel-safety edge [R36.s3]: say what W12 must know.**  Wrong: "W12 →
`AxDeps` is a rebuild-only edge" is no longer exact.  Change (and send to the running W12 worker as a course note): (i) `gtdepsWf`,
`forgetDeps`, `gtAd`, `rvwmoCatConsistentT` CHANGE in (F-dep) increment (0); `catADOfCatT :37`'s statement survives and its proof
survives under A2; under A1 it needs ONE line (`gppo12` monotonicity, lemma exported by (F-dep)); (ii) W12 (5)'s `gdexecQconfT` must
be stated as `rowDepsT em ⊆ GT.gtDeps` against the GENERALIZED `gtdepsWf` — NO RAM-endpoint filter (that is option C/D50 (a),
contrary to [OWN.17]) — and should not be stated before increment (0) has merged (until then `rvwmoCatConsistentT ∧ gdexecQconfT`
is unsatisfiable on I/O rows); (iii) W12's `rvwmoCoreD` over the UNTAGGED `gdepsWf` is unaffected (option A leaves it alone — the
reason B is rejected); (iv) W12 must not derive `lbIsR`/`lbIsW` of a tagged edge's endpoints from `gtdepsWf` in new lemmas — take
them from `forget GT`/`gtAd`'s `gdepsWf` as today; (v) rebase once after increment (1)'s `Supply`/`Fab` sweep (disjoint sites).

## SUGGESTIONS

- **[R38.s1]** Make "the published premise is computably SATISFIABLE on an I/O-active row" a standing acceptance item for EVERY
  conformance text ((W)'s `xv6ConfS`, W12's `gdexecQconfT`): a `Bool` evaluation of the model's well-formedness over the real
  `rowDepsT` of W13-wit's row.  Cheap, and it is exactly the class of vacuity R-reviews cannot see by reading.
- **[R38.s2]** Two corrections to carry into the worker's relaunch brief (not into the plan): (a) W13-wit's edge `ld a5,0(a0)` →
  `sb zero,1(a5)` is an ADDRESS edge, `dtagW DTaddr = false`, target clause `gmem` — it IS representable in the tagged model
  today; it dies only on the untagged route (Gap 2).  The tagged vacuity (Gap 1) comes from `DTdata`/`DTctrl`/`DTr13` → I/O store
  and from every I/O-load-sourced edge (first instance: the first `printk`'s THR store, above).  (b) `uartstart` does not exist in
  this image (census `:314`); the data example is `uartwrite`'s THR `0x80000988`.
- **[R38.s3]** Cite drift in §C W13 (F-dep) `:3667-3671`/`:3690-3691`: the MMIO arms are `WeakEvInst.lean:316-320` (`LDev .rd`
  `:319`) and `:351-356` (`LDev .wr` `:355`); plain `LLoad` `asrc = []` `:336`; `LExLoad`'s `depsAsrc` `:345-346`.
- **[R38.s4]** Note in (0c) that `ctrlClosed` is satisfied by the emission for I/O-store targets too (the quantifier asks only
  for RAM-write closure), so no new premise appears in the LB roots.
- **[R38.s5]** D50's "(b) … (= the existing `LLoad`/`LStore` arm shapes …) — FAITHFUL to (c1)" should read "FAITHFUL once the
  graph side admits the edges ([R38.1]); the emission shapes alone are not a model".

## Owner question the plan is missing — Q-FDEP (paste into §D, FIRST)

- **Q-FDEP — Rule 12 from an I/O-load source (A1 faithful vs A2 weaker); the graph-side fix (A) itself is a plan decision
  [R38.1], not a question.**  **Plain language.**  xv6 drivers read device registers (MMIO loads) and then do things with the
  value: branch on it, store it to RAM, store it to another device register.  The RISC-V memory model says a load that FEEDS a
  later store (by address, data or a branch) is ordered before that store — and the appendix says this still holds when the load
  or the store is to a device.  The plan already decided (D50 (b)) to record those edges.  But the published model's
  well-formedness clause currently says "every recorded edge starts at a RAM load and (for data/control edges) ends at a RAM
  store", so a graph with a device-sourced or device-targeted edge is REJECTED — not "the ordering is false" but "no graph of this
  program conforms".  Then the theorem's premise is false for every xv6 run that prints a character, and the theorem says nothing
  (it is VACUOUS).  [R38.1] fixes that by admitting device endpoints (option A).  One corner remains to rule: riscv.cat's rule 12
  (`[R];(addr|data);[W];rfi;[R]`): "a load `a`, a store `m` that depends on `a`, and a later load `b` of the SAME hart that reads
  `m`'s value (store-to-load forwarding) — then `a` is ordered before `b`".  Should that hold when `a` is a DEVICE load?
  **Tiny example** (one hart, the UART echo path): L1 = `lbu` RHR (device read, the typed key `c`); S = `sb c → cons.buf[i]` (RAM
  store, data-dependent on L1); L2 = a later `lb cons.buf[i]` by the same hart that is satisfied by forwarding from S.  Rule 12
  says gmo: L1 < L2.  Under A1 the model asserts it; under A2 it does not (L2 may sit anywhere gmo-after S's own constraints).
  No hart ordering, lock or proof in the plan currently needs L1 < L2 (census: no xv6 pin uses an MMIO-sourced dependency), so
  the choice is about FAITHFULNESS of the published model text, not about closing a proof.  **Definitions.**  *ppo* — preserved
  program order, the same-hart orderings the ISA guarantees; *gmo* — the global memory order the model totalises; *tagged graph
  `GT`* — the published graph with its dependency list `gtDeps` where each edge carries a tag (addr/data/ctrl/…); *`gtdepsWf`* —
  the well-formedness clause of the model saying what shape an edge may have; *`rowDepsT`* — the edges the emission (the
  instruction-level tagger `dstepT`) RECORDS for a row; *`gdexecQconfT`/`xv6ConfS`* — the conformance text saying "the recorded
  edges are in `gtDeps`"; *vacuous* — the premise is never satisfiable, so the theorem is true but says nothing.  **Spec:**
  riscv.cat `r12 = [R];(addr|data);[W];rfi;[R]` over ALL reads; RVWMO rule 12 prose (above); appendix (c1): ppo applies when one
  access is I/O; Sail/Zifencei/PMAs: SILENT on dependencies.  **Why it matters.**  An xv6 expert reading the model text will ask
  whether it is riscv.cat; A2 is a NAMED departure (one rule instance), A1 is not.  **Options.**
  (A1) **FAITHFUL** — `gppoCatT` ranges over the addr/data edges into RAM writes from ANY read (`gtAdFull`), the projections
  used by the proof chain keep RAM sources.  Concretely: one new list function, two one-line monotonicity proofs (`catTAd` in
  AxDeps; `catADOfCatT` in W12's `CatOfMinusSpike.lean`), `AxScCat.scPpo`'s rule-12 case re-cased.  In practice: the model
  excludes exactly the executions riscv.cat excludes.  Cost S (after W12's statement commit; one line in W12's file, by W12 or
  by (F-dep) after rebase).  Unblocks: the §A(3) sentence "ppo applies as riscv.cat is written" stays literally true.  Risk: the
  "reuse hinge" `gppoCatT = gppoCat (gtAdGd GT)` (`AxDeps.lean:195`) is no longer definitional — ~90 `AxSpin*` files use
  `gtAd`/`gtAdGd` but none uses `gppoCatT` directly (only `AxScCat`), so the blast radius is two files; the worker verifies by
  build.  **Recommended.**
  (A2) **WEAKER (sound)** — `gppoCatT` unchanged over the source-filtered `gtAd`; rule 12 from a device load is NOT asserted.
  Concretely: nothing beyond [R38.1]; §A(3) names "rule 12 omitted for I/O-load sources".  In practice: the model admits a few
  executions riscv.cat forbids (the theorem covers them too — safe).  Cost 0; no W12 contact.  Risk: a named departure in the
  published model; a later proof wanting L1 < L2 has to add it then.  This is the PROVISIONAL shape until ruled.
  (B) **FAITHFUL, rejected on cost** — also loosen the UNTAGGED `gdepsWf` (`WeakRvwmoGraph.lean:629`) and give `dstep` the arms:
  changes the meaning of `rvwmoMinusDepsConsistent`/`rvwmoCatConsistent` (hundreds of `Ax*` uses, W12's `rvwmoCoreD`, the
  G3 kill files) while W12 is running; L–XL.
  (C) **WEAKER, rejected** — emission only; the conformance text admits RAM-endpoint `rowDepsT` edges only = D50 (a) in effect,
  contrary to [OWN.17].

## What the W13 worker must also know at relaunch (beyond the plan text)

Order: increment (1) sweep → (0) model text (A2 shape) → (2)/(3) arms and row lemmas → (0e) on the ruling.  Do not merge (1)+(2)
without (0): that is exactly the Gap-1 vacuity for W12's `gdexecQconfT`.  `AxSpinGate.lean` is yours for (0c) only; the
registered roots' text must not change (audit: "registered roots unchanged in statement").
