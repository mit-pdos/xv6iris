VERDICT: NOT SATISFIED

# Review R6 of `notes/weak-allocproc-plan.md` rev 6 (adversarial, evidence-based; 2026-10-09)

Scope: (1) were R5's three required changes applied; (2) is the plan LAUNCHABLE — every Stage-0/Stage-1
item concrete (file, statement, deps, size, acceptance); (3) does the published statement survive the
Stage-0 spike reports that now exist: `../xv6iris-weak-w1/notes/W12-spike.md` (+ `Weak/CatOfMinusSpike.lean`,
399 lines, no `sorry`) and `../xv6iris-weak-w2/notes/W13-spike.md` (+ `Weak/W13Spike.lean`, 145 lines, no
`sorry`); the W5d-G spike has a scratch (`../xv6iris-weak-w3/Weak/GraphFetchSpike.lean`, 226 lines) but no
report yet.  `file:line` cites `../xv6iris-weak` unless prefixed.  Advisory only; no proofs or builds run.

## R5 application check (what NOT to re-litigate)

All three R5 items are in rev 6 and substantively right.  [R5.1] §A(†) states the quiescence vacuity with the
right cites (`WeakRvwmoSupply.lean:273,281-289`; `WeakEvInst.lean:300-303,335-338,484,502`; `SpecMain.lean:7-10`;
`SpecUartinitone.lean:6-13`), W13 + W13-spike + W13-wit added, §B(3) "OPEN at the graph tier", §B(11) names
the dev-order model, D9/D29/D31.  [R5.2] W3 is `textPristine` on `[bcRoLo, bcRoHi)` (`BootCarve.lean:143-144`
re-confirmed: `bcRoLo = ramBase`, `bcRoHi = _data`), the `imgByte` `□` singleton history (`Ctx.lean:435-436`),
`imgByte_readable` (`Wp.lean:1477-1478`: `∀ h tvn, m.read h tvn a = some v`), the hook chain
(`Adequacy.lean:481` → `SystemSlot.lean:590-612`, which indeed sees only `powerInterp` and `▷ xv6Slot`), the
sibling root [OWN.9], SERIAL, M–L; `candKfetch`'s region aligned (plan:180-181).  [R5.3] `pairAdjacent` is
defined once in §B(10) (plan:327-332), W5b defines/proves it, W2 takes it as a hypothesis.

Re-confirmed this round: `rvwmoCatConsistent` (`AxGraphCat.lean:191-194`), `grcsc` both-bits (`:163`),
`minusImpliesCat :274`, `obCatSubGmo :320`; `racyDSplit` (`Glue.lean:103-110`), `segPinGmo :233-240`,
`hullRun :282`, `wpPackage :338`, `badRun :384`, `l2ClaimAt :440`; `gcrossGmo` (`KillArms.lean:270-275`),
`csChained :499`; `grfGmo` (`Acyc.lean:217-233`); `cycleKill` (`LinInd.lean:155`); `linCand` (`Lin.lean:471`);
`Gfexec`/`gfexecConf`/`gfexecConsistent` (`Fab.lean:516-544`), `trDevOrdered` (`FabInd.lean:407-410`),
`t2linSupplyF :523`, `lbfNotDevOrdered :583`, `linCrossHartGmoReversed :600`; `xv6RvwmoSafeModulo`
(`Capstone.lean:187-215`); `lblRealizesPair` (`WeakAxRealize.lean:305-313`), `execProgOk' :373-386`,
`execWfPfRunProg :802`; `admRun` (`Conf.lean:374-381`); `epsInit` (`EvCapstone.lean:1026-1027`); W1's chain
(`LinkNiAdequacy.lean:82-90`, `NiTrace.lean:646,660`, `UsysDet.lean:293-302`, `PidEv.lean:77,136`,
`KallocEv.lean:45-52,72`, `NiAdequacy.lean:91-92`); `wp_allocproc_body` (`SpecAllocproc.lean:204-224`);
`Allocproc`/`allocproc_proof` (`LinkAllocproc.lean:14-16`, `ProofAllocproc.lean:3623`); the census
(`KernelPins.lean:22-23`); R-3 (`PinBridge2.lean:28-29`); the roots/baselines (`tools/ci/roots.txt`,
`roots-weak.txt`, `tools/audit/baseline.json`, `baseline-weak.json`, `audit.sh:44`).

## REQUIRED changes

**[R6.1] The published quantifier `rvwmoCatConsistent` is NOT riscv.cat — it is STRICTLY STRONGER, and the
tree itself calls the extra edge "UNSOUND for safety".**  The plan (lines 76-79, 106, 384-385) says the cat
transcription "omits 6, 7-RCpc, 8 — sound direction".  Evidence: `AxGraphCat.gppo12` ranges over the UNTAGGED
`gdDeps`, which mixes addr/data/ctrl/translation edges, so it also orders `ctrl;[W];rfi;[R]`, which riscv.cat
does not (`Weak/AxDeps.lean:12-18`: "UNSOUND for safety"); the separation is machine-checked — `twCatT`
(`:876`, tagged-consistent) with `twNotCatForget` (`:883`, `¬ rvwmoCatConsistent (forget AxDeps.tw)`).  The
faithful model exists: `rvwmoCatConsistentT GT` over `GdexecT` (`AxDeps.lean:208-211`; rule 12 over `gtAd`,
the addr/data edges only); `catTOfCat` goes cat→tagged, the converse fails (`:22-27`).  The W12 spike (F1)
found this and sized the fix.  Change: (i) T-alloc-RVWMO quantifies over `GT : GfexecT` (the fabric bundle
over `GdexecT`) with `rvwmoCatConsistentT GT.gfGd`; the chain runs on `forget`; the conformance premise
carries `rowDepsT` tags (`gdexecQconfT`-style; `rowDepsSubT`, `AxDeps.lean:690`, gives the untagged bundle
back) — this is within [OWN.2]'s wording ("rvwmoCatConsistent / the RVWMO axiomatic model in this tree"),
but put it to the owner as Q-T below; (ii) §A(3)/§B(11): delete "sound direction" for rule 12; name the
tagged model and `gdexecQconfT` as NEW trusted-surface text (spike risk 3: review against `rowDepsT`'s
correction (5), `AxDeps.lean:56-60`); (iii) W12's item (plan:502-504) becomes the spike's design: core
predicate `rvwmoCoreD` (statement edits to `Topo`/`topoSupply`/`hullRealizable*`/`hullRun`), the kill at
`rsameC`/`gcrossE` (rfi → same-hart; `gcrossE` = rfe ∪ co ∪ fr, `gwf` + load value only), `segPinC` as a
same-hart CHAIN with the rule-12 forward case (`segPinCForward` — why `ad` must be the TAGGED edges),
`hullCatAD` (the one real proof: rule 2's `t1 ≠ t2` and rule 3/12's `grfAt` through an injective `hren`),
the restated chain `cycleKillC`/`t2linSupplyC`/`l2ClaimAtC`/…/`xv6RvwmoSafeModuloT`; witnesses by
`catADOfMinus` (NO re-proof of `lkw`/`lkw2` — this corrects [R5.s1] and plan:460-462); one forwarding witness
cat-consistent but not RVWMO⁻.  Size **M–L (≈1.2–1.8k lines)**, not "L–XL, likely L"; W9a gains M (PDep pins
across an rfi need a rule-12 chain).

**[R6.2] A THIRD gate the plan does not have: the certification walk's floor kit BREAKS under cat and needs a
REDESIGN, not a re-hypothesis.**  Evidence: `greadSrcUb` (`Weak/WeakRvwmoFloor.lean:442-453`) closes its po
case with `gpolocGmo` W→R; `finvStep` (`:605-619`) uses `gpolocGmo` for the coh hook (`hoacc`); `gvisUb`
(`:100-101`: "every write of index ≤ n is gmo-before r") is FALSE under cat for an own store forwarded to a
po-later read (it may be gmo-after the read).  Consumers: `cinvReplay`/`floorOfCgraph`/`certFloorOk`/`cpolRead`
(`Cert3.lean:311,393,430,470`, all under `rvwmoMinusConsistent G`), reached from `wblkPolAt` (`Walk.lean:
700-731`, hypothesis `rvwmoMinusConsistent G`, the `LLoad` arm via `cpolRead`) — i.e. W10's toolkit.  Plus two
mismatches: the `wVRel` hook consumes rule 7 RCpc (`Floor.lean:21`, `grelacqGmo`), which `grcsc` (both bits,
`AxGraphCat.lean:163`) lacks; and WeakMem's forwarded ACQUIRE load (`fwdView … true … = t`, `WeakMem.lean:
585-613` per the spike) is stricter than cat.  Both are vacuous for kernel rows — release is `fence rw,w; sw`
(`Xv6/ProofRelease.lean:83-86`), acquire the RMW `amoswap.w.aq` (`ProofAcquire.lean:5`) — and OPEN for user rows
under [OWN.3].  Change: add **W12b `Weak/CatFloor*.lean`** (M–L, ≈0.5–1k: Floor §4–§6 and Cert3 §2–§3 on a
per-byte coherence invariant through rules 1/2 in place of `gvisUb`), scheduled with W12 and BEFORE W10
(or W10 → L and absorbs it — owner choice, Q-U); §B(9)'s "the gap is CONFINED to the kill" (plan:247) is false —
say "the kill AND the walk floor"; §B(11) names the rule-7 and forwarded-`LLoad aq` user-row gaps (Q-V, Q-W).

**[R6.3] `devAcyclic GF` as stated EXCLUDES load buffering and W→W reordering on the quantified graph — the
published theorem as written contradicts [OWN.2] — and T2-1c′ already LANDED.**  Evidence: the plan's
`devAcyclic` (plan:106,128-129,475-476: `po ∪ rf ∪ gmo|W ∪ gdevAdj` acyclic on the quantified `GF`) is
exactly `gfexecConsistent'` (`Weak/WeakRvwmoLin2.lean:761-762`: `rvwmoMinusDepsConsistent ∧ ∀ x, ¬ tc
(ptraceRelF GF) x x`, `ptraceRel` = po ∪ rf ∪ gmo|W).  `po ∪ rf` acyclic IS "no load buffering" and
`po ∪ gmo|W` acyclic IS "no W→W reordering" — machine-checked: `lbExcluded : rvwmoCatConsistent lbgd ∧
¬ gfexecConsistent' ⟨lbgd, []⟩` (`…-w2/Weak/W13Spike.lean`, at an EMPTY fabric).  It also subsumes the kill:
`xv6RvwmoSafeModuloF` (`Weak/WeakRvwmoCapstone.lean:228-265`) carries NO `l2Claim`/`walkSupply`.  So it is a
robustness ASSUMPTION, not a hardware model, and cannot be the trusted-base item.  Second finding:
block-atomic folding of `LDev` into the next tagged step (`execProgOk'`, `WeakAxRealize.lean:373-386`) makes
EVERY block-level dev-order condition exclude plain SC executions (`scDevExcluded`, `scDevUnrealizable`: MMIO₀;
MMIO₁; st x; ld x = 1 fails both `gfexecConsistent'` and `gdevAdj ⊆ gmo`, and no `ptraceExt` trace visits the
blocks in fabric order) — a realization-interface change is needed.  Third: T2-1c′ is in the tree —
`gtraceLinearizationMin` (`Lin2.lean:623`), `ptraceExistsF :836`, `trDevOrderedOfPtrace :944` (discharges
FabInd's guard), `fconfSupply' :995`, `fconfTraceRealize :1012`; `Fab.lean` is already imported by `FabInd` and
(via it) `Lin2`.  Change: (i) T-alloc-RVWMO: replace `devAcyclic GF` by the spike's **`ioObAcyclic GF`**
(`W13Spike.lean` §3: gmo extended by I/O nodes `dv i k`, each ordered in program order against its hart's
memory events and by the fabric among themselves; free at an empty fabric, `ioObAcyclicNodev`; admits the SC
case, `w13fIoOk`) — PROVISIONAL pending the owner's re-ruling of [OWN.8], whose literal form is refuted (Q-X
below; the owner's intent "the fabric order is realizable by the machine's own ordering" is preserved);
(ii) §B(11): the dev-order item is a PLATFORM assumption — strongly-ordered I/O in program order; the image has
4 bare `fence` (iorw,iorw) words, all in virtio, plus `fence r,rw` ×1, `fence rw,w` ×2, `fence.i` ×1
(`Xv6/KernelImage.lean`, `-- fence` lines), so xv6's UART/PLIC paths are NOT fence-ordered under RVWMO's text,
and `LFence` has no i/o bits (`WeakAxiomatic.lean:90`) — name QEMU-virt/PMA strong ordering (Q-Y);
(iii) W13 (plan:509-517) re-sized **XL** and decomposed per the spike: (T) the item (S, done in scratch);
(I) `execProgOkA` — admin-only trace steps that may move the fabric, with its T1 lift (L); (L) T2-1c″ —
`gtraceLinearizationMin` over events ∪ dev positions (M–L); (K) the kill with dev edges as a cross kind and
`iopo` as a same-hart arm, composed in `tc (ioOrd GF)` (M–L) — W12's cat arms written ONCE against it;
(R) the re-thread of the constant-fabric chain, measured 8.6k lines / 14 files / ≈140 bundle mentions / 52
`fun _ => d0` sites (L–XL, the bulk; witness files embed via `gfexecConfOfQconf`); (W) `xv6ConfS` on the A-bundle
+ W13-wit (M–L).  Delete "T2-1c′ … sizeable … to build", "`Fab.lean` stops being a leaf" (plan:300,476,511,614,
622); D29's text updated; (iv) W13 (I) and W5b's `execProgOk'S` are BOTH shapes of `execProgOk'` — co-design
them (see [R6.4]); (v) retire `xv6RvwmoSafeModuloF`/`gfexecConsistent'` as a publishable form (Q-Z).

**[R6.4] Stage 0 is stale on the day it is to launch, and one Stage-0 deliverable has no owner.**
(a) W12-spike and W13-spike are DONE (reports + building scratch files, no `sorry`); the plan lists them as
"launch now".  Mark done; ingest [R6.1]–[R6.3]; W8's design gate "all THREE spike reports" now waits on
W5d-G only.  (b) The W5d-G spike scratch (`…-w3/Weak/GraphFetchSpike.lean:1-25`) keeps the fetch
ADMINISTRATIVE with an existential CUT `q` (`itv ≤ q ≤ cut`, `fetchCutOk`; `fetchCutPrefix` = the pf/W5d
admissibility at the realizing prefix with ONE view for all bytes; `fetchCutEdge` = the new edges are
index-forward) — the oracle-with-side-condition shape, NOT the [R4.s1] fetch-as-event shape the plan says to
"test first" (plan:209-213).  Do not pre-commit §B(4)(iii)/W5d-G's text; hold it for the report, and note
that W2's `R` must then carry `itv ≤ q` for the `LIFetch` row.  (c) **`execProgOk'S` exists in NO file**
(grep `Weak/ Xv6/ MachCSL/`: only `execProgOk'Snoc`/`SnocPair`); the plan has W5b "consume" it, W2
"hypothesise" it, W5c "produce" an S-variant of `execProgOk'Snoc` — nobody DEFINES it.  Change: W5b defines
`execProgOk'S` AND `pairAdjacent` on day one (both statements handed to W2/W5c), stated over the step list so
that W13 (I)'s admin-only steps (`execProgOkA`) can reuse the same shape clauses (fused left arm; label-carrying
`admRun`s; no foreign step between pair halves) rather than orphaning W5b's theorem.

**[R6.5] Cite and acceptance fixes needed for the first items to be handed over.**  (a) `bootByte_zero` is
`MachCSL/BootImage.lean:31`, not `Xv6/BootImage.lean:30-33` (plan:185; the file does not exist under `Xv6/`).
(b) W13-wit: `0x80000896` (plan:514) is `uartinitone`'s ENTRY (`KernelImage.lean:1515`, `c.addi sp,sp,-16`);
`:1590` is the `jal`.  Name the witness end as "the first UART `sb` of `uartinitone`" and give its address
from the image.  (c) W3's acceptance (plan:410-412) names `roots.txt`/`baseline.json` (`tools/ci/lint.sh`
checks the two agree); add whether `Xv6.xv6TextAdequacy_closed` enters the trusted-base report
(`tools/ci/tcb.sh` vs `tools/tcb/expected.json`, `--update`) — a one-line decision the worker needs.
(d) W1's acceptance is "cite `xv6NiPhi` + pure lemmas"; give the theorem shape: from `xv6NiAdequacy`'s three
boot hypotheses, `∀ q, ∀ s ∈ utrace q κs F`, a fork round's `a0 = usysForkAns ι` and `forkOk ι → 1 ≤ pidPick
PIDMAX ι.pev ≤ PIDMAX` (`PidEv.lean:136`) — otherwise W1 has no checkable finish line.

## SUGGESTIONS

- [R6.s1] Header: after [R6.1]/[R6.3] the honest one-liner is "quantifier: riscv.cat RVWMO (tagged deps,
  `rvwmoCatConsistentT`), plus an I/O-order platform assumption (`ioObAcyclic`) and a graph-tier Zifencei fetch
  model, both named trusted-base items with no reference model".
- [R6.s2] W12-spike's recommended non-vacuity witness (SB+rfi-pos through `rvwmoCatAD`) is the first
  machine-checked evidence that the published quantifier admits a forwarding execution RVWMO⁻ rejects — make it
  W12's acceptance gate, as `_entry` is W5c's.
- [R6.s3] Plan length is 622 lines against the reviser brief's ≤ ~400 [R5.s2]; §B(9)'s route inventory
  ((9a)–(9c)) and D1–D23 can move to an appendix now that they are RULED.
- [R6.s4] W13-spike R3: unlocked cross-hart PLIC claim/complete and `plicinithart` are real fabric races that
  only the strong-ordering arm of (T) covers — list them as the trusted uses of the platform assumption.

## Owner questions the plan is missing

- **Q-T. The published model ([R6.1]).**  (a) tagged `rvwmoCatConsistentT`, chain on `forget GT`
  (recommended; within [OWN.2]'s wording); (b) untagged `rvwmoCatConsistent` with "rule 12 also over ctrl/
  translation deps" NAMED as a strengthening of riscv.cat; (c) drop rule 12 — sound, but W9a must split PDep
  pins at every rfi.
- **Q-U. Gate 3 ownership ([R6.2]).**  (a) W10 absorbs it (W10 → L); (b) a new W12b `Weak/CatFloor*.lean`
  (M–L) scheduled with W12 (recommended); (c) restrict the walk to kernel rows, defer user-row aq/rl cases.
- **Q-V. Rule 7.**  (a) make `grcsc` riscv.cat-faithful (RCsc = any aq/rl on AMO/LR/SC; check the decoder
  emits `LStore rl`/`LLoad aq` only for atomics); (b) keep the weak rule 7 + a conformance side condition "no
  rl write followed by an aq read" (vacuous for the kernel); (c) carry the `Bad`-arm burden in user rows.
- **Q-W. Forwarded `LLoad aq`.**  (a) row side condition "no plain `LLoad aq`" (true for the kernel);
  (b) change WeakMem's `fwdView` for aq (ripples into T1); (c) a named gap for user code.
- **Q-X. [OWN.8] is refuted as literally stated ([R6.3]).**  (a) `ioObAcyclic` as THE trusted-base item
  (recommended); (b) the literal `po ∪ rf ∪ gmo|W ∪ dev` acyclic — drops LB and W→W, contradicts [OWN.2]
  (`lbExcluded`); (c) the same on the normalized graph only — not a statement about the input; (d) `gdevAdj ⊆
  gmo` — excludes SC executions (`scDevExcluded`).
- **Q-Y. The platform assumption behind (T).**  (a) name QEMU virt / strongly-ordered I/O in the header;
  (b) require fence-guarded MMIO (i/o bits in `LFence` + an xv6 code change — leaves the `verified` branch);
  (c) restrict the claim to platforms with PMA strong ordering.
- **Q-Z. The realization interface and the F capstone.**  (a) admin-only trace steps `execProgOkA`
  (recommended); (b) MMIO as a tagged inert-fence row event (changes `projLbl` and merged emission proofs);
  (c) keep the folded model and prove representability per xv6 MMIO site (fragile, also XL).  And: retire
  `xv6RvwmoSafeModuloF`/`gfexecConsistent'` as a published form, or keep with a header warning?
