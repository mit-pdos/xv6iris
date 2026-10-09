VERDICT: NOT SATISFIED

# Review R5 of `notes/weak-allocproc-plan.md` rev 5 (adversarial, evidence-based; 2026-10-09)

Scope: (1) were R4's five required changes applied correctly, including the reviser's own
correction of [R4.5] (`racyDSplit`); (2) is the plan LAUNCHABLE — are Stage 0's spikes and first
work items concrete enough to hand to workers, and is the published statement (T-alloc-RVWMO, the
[OWN.2] target) non-vacuous for allocproc.  `file:line` cites `../xv6iris-weak`.  Advisory only; no
proofs or builds run.

## R4 application check (what NOT to re-litigate)

All five R4 items are in rev 5 and substantively right.  [R4.1] the Lean census (`Weak/KernelPins.lean:22-23`:
1034/3/289/1/180/63/119, 58 `own = true`; 1,901/639/1,004 lines), R-3 (`Weak/WeakRvwmoPinBridge2.lean:28-29`),
W9a/W9b, no "callee summaries".  [R4.2] W5d split, W5d-G + spike, (†) rewritten, §B(11) names the graph fetch
model, D18/D27.  [R4.3] W11's `Bad` arm log-level (`badSeg`), `protReg` as a log fold (`Glue.lean:364-368`),
re-thread list, size L, restated theorems named (`Glue2.lean:521`, `Walk3.lean:77`, `Capstone.lean:187`).
[R4.4] `candSca` out of `xv6ConfS`, `linCandSca` in W11 (iv), M1/M2-only in D20/D21.  [R4.5] W12-spike names
the gates; D25 (a) default, (b) dropped.

**The reviser's correction of [R4.5] is RIGHT.**  `racyDSplit` (`Weak/WeakRvwmoGlue.lean:103-110`) destructs
`racyD = (gpow ∨ grf ∨ gco ∨ gfr ∨ gppo) ∨ deps` and sends the SECOND arm — ALL of `grf`, rfi included — to
`.inr (.inl h)` = `gcross`; `rsame` (`:101-102`) is `gpow ∨ gppo ∨ deps` only.  Under cat, an rfi edge is
po-increasing (rule 1 `[M];po-loc;[W]` forbids a read reading its own hart's po-later store), so adding an rfi
case to `rsame` keeps `rsameLex`/`rsameAcyclic` (`:120-141`); `gcross` then needs `grfe` only, for which
`grfeGmo` already exists (`Weak/AxGraph.lean:239,261`, from `gloadValue` alone).  Gate 2 also checks out:
Lock's `hppo` uses are rule 1 (W→W `gpoloc`, `Weak/WeakRvwmoLock.lean:200,235` — both arguments
`gwritesByte`), rule 4 (`gfenceCovers`, `:125`) and rule 5 (`gacqPo`, `:120`); KillArms `:537,586` go through
those two lemmas.  Counts re-confirmed: `pstepPin` in 15 `WeakRvwmo*` files (Supply 14, Cert 9, Cert2 8,
Cert3 7, Fab 7, Cert4 6, CycWit 6); `hppo` Lock 11 / KillArms 9 / Hull 4 / Cert4 1 / Lin 47.

Also re-confirmed this round: `gloadValue`/`gvisible` (`Weak/WeakRvwmoGraph.lean:236-243`); `rvwmoCatConsistent`
(`Weak/AxGraphCat.lean:191-194`), `minusImpliesCat :274`, `obCatSubGmo :320-332`; `segPin`/`segPinGmo`
(`Glue.lean:229-240`), `hullRun :272-290`, `wpPackage :338-346`, `badRun`/`noBadRun :384-391`, `l2ClaimAt
:440-447`, `rawChainChain :453-460`; `topoSupply` (`Weak/WeakRvwmoSupply.lean:865-883`); `linCand`
(`Weak/WeakRvwmoLin.lean:471`); `cycleKill`/`t2linOfCycleKill`/`t2linSupply` (`LinInd.lean:155,231,240-255`);
`walkSupply` (`Glue2.lean:453`), `walkSupplyOfQconf` (`Walk2.lean:563-568`); `cstOk` (`Cert4.lean:370-373`);
`hullOk` (`Hull.lean:557-560`); `xv6RvwmoSafeModulo` (`Capstone.lean:187-215`); W1's chain
(`Xv6/LinkNiAdequacy.lean:82-90`, `Xv6/NiTrace.lean:646,660`, `Xv6/UsysDet.lean:293-302`, `Xv6/PidEv.lean:77`,
`Xv6/KallocEv.lean:45-52,72`); W5c's (`Weak/WeakRvwmoConfWit2.lean:26-28`, `Cert2.lean:180`,
`WeakEvLift.lean:897`, `Floor.lean:1025-1035`, `Xv6/KernelImage.lean:14-17`, `MachCSL/BootRun.lean`); W11's
vocabulary (`Weak/WeakRobustMain.lean:390-400`, `Weak/WeakViolation.lean:9-15`, `Weak/WeakGhost.lean:1040,543,
699`, `Weak/WeakRvwmoKillArms.lean:340`, `Weak/WeakRobust.lean:100-121`); `wp_allocproc_body`'s premises
(`Xv6/SpecAllocproc.lean:204-224`); the audit roots (`tools/ci/roots.txt`, `roots-weak.txt`,
`tools/audit/baseline.json:11-14`).

## REQUIRED changes

**[R5.1] The published quantifier is QUIESCENT: no `gdexecQconf` candidate performs any MMIO, so no
candidate reaches `allocproc` — T-alloc-RVWMO as written is VACUOUS for allocproc, and a whole Stage-2
work item (the fabric on the graph tier) is missing.**  Evidence: `gdexecQconf` requires `emDevfree em` of
every row (`Weak/WeakRvwmoSupply.lean:281-289`), `emDevfree em := LDev ∉ emLabels em` (`:273`); the event LTS
emits `LDev` for EVERY device-address access — MMIO read (`Weak/WeakEvInst.lean:300-303`) and MMIO write
(`:335-338`) — and for the disk row's START/COMMIT (`pdiskProg`, `:484,502`; `xboot σ0` includes the disk row:
`epsInit σ0 = cpus.map (.PHart …) ++ [.PDisk none]`, `Weak/WeakEvCapstone.lean:1026-1027`, `xboot`/`xN`,
`Weak/WeakRvwmoCapstone.lean:90-94`).  Every xv6 hart performs MMIO before `scheduler()`: hart 0's `main`
runs `consoleinit()` FIRST (`Xv6/SpecMain.lean:7-10`) = `uartinitone`'s seven `WriteReg`s
(`Xv6/SpecUartinitone.lean:6-13`), then `printk`, `plicinit`, `virtio_disk_init`, and only then `userinit`;
every secondary hart runs `printk` and `plicinithart` (`Xv6/SpecMainSecondary.lean:7-11`).  Hence a conformant
candidate's hart rows end before `uartinitone`'s first store; `userinit → allocproc` is unreachable in EVERY
`GD` the theorem quantifies over, conclusion (b) holds vacuously and (a)'s realizing run never reaches
allocproc.  The W5d-G user-fetch concern is downstream of this: without the disk row stepping (START is
`LDev`), `exec("/init")` never completes, so user `fork` is unreachable even with graph-tier fetches.  The
plan's (†) says "device-free" in passing (`plan:115`) and §B(3) declares devices CLOSED (`plan:147-148`) — true
on route (M), FALSE at the graph tier; the plan never mentions quiescence, `emDevfree`, `WeakRvwmoFab` or
`gfexecConf` (grep: none).  The route-b design calls quiescence an "HONEST MILESTONE … not the final theorem"
(`claude-notes/design/weak-memory-route-b.md:1009-1020`).  What EXISTS: B1b-2 `Weak/WeakRvwmoFab.lean` (936
lines: `Gfexec`/`gfexecConf` with `gfDev` + `fab : Nat → Efab`, `hemitf`, `supplyOfFconf`/`fconfSupply`; "A
LEAF: nothing imports this file"; non-vacuity only at `gfDev = []` — "no `LDev`-emitting run witness exists in
the tree", header §6) and `Weak/WeakRvwmoFabInd.lean` (623: `cycleKillF`, `t2linSupplyF` with the guard
`trDevOrdered` HANDED BACK, header §4; §5 THE FINDING: `linCand` does NOT respect the fabric order —
`lbfNotDevOrdered`, `linCrossHartGmoReversed`).  Route-b's verdict on the fix: the honest axiom is
"`po ∪ rf ∪ gmo|W ∪ dev` ACYCLIC", the build item is "T2-1c′ — the trace-flexible linearization … generalizes
`WeakRvwmoLin`'s proof; sizeable.  PARKED" (`route-b.md:1040-1055`).  Change: (i) add **W13 `Weak/GraphFab*.lean`**
(Stage 2, L–XL **unverified**): `xv6ConfS` built on `gfexecConf` (fabric order + `fab 0 = efInit σ0.wgdev`),
not `gdexecQconf`; the kill mirror (`cycleKillF`, `t2linSupplyF`) with `trDevOrdered` DISCHARGED — i.e.
T2-1c′ or an equivalent — threaded through `hullRun`/W11; a `LDev`-emitting non-vacuity witness (natural
candidate: hart 0's first `WriteReg` of `uartinitone`, the `_entry` witness's successor); (ii) add
**W13-spike** (Stage 0, read-only, S) beside W12-spike/W5d-G-spike: state the vacuity, audit `fconfSupply`'s
handed-back guard and FabInd §5, size T2-1c′, decide the dev-order axiom form; W8's design waits for it too
([R4.s5] list); (iii) §A (†): "the fabric-ORDERED conformance bundle (W13), not today's quiescent
`gdexecQconf`"; §B(3): "CLOSED on route (M); OPEN at the graph tier (W13)"; §B(9d) sizes: Stage 2 gains W13;
(iv) §B(11): the graph-tier fabric/dev-order model is a trusted-base item (the M5 fence discipline is what makes
hardware honour it, `route-b.md:1023-1024`), beside the graph fetch model; (v) D9's UART-trace reading of "no
panic" depends on (i); (vi) a new owner question (Q-R below).

**[R5.2] W3 is mis-stated and mis-scoped for the FIRST item on the critical path.**  The plan: "no reachable
store (hart or DMA) targets `[text, etext)`, as a trace export of the state interpretation … Deps: none …
none touching shared `MachCSL/`" (`plan:382-384,503`).  Evidence: (a) the state interpretation does not export
per-STEP facts; the idiom is a per-STATE predicate pulled through the hook — `powerInterp_mmOk`
(`MachCSL/Adequacy.lean:481`) → `xv6TraceHook` (`Xv6/SystemSlot.lean:590-612`) → `xv6TracePure`'s conjunct
`g.pow = true → mmOk g.m` (`:135-136`) → the root statement (`Xv6/LinkSystemAdequacyClosed.lean:20-26`).  (b)
The available fact is a HISTORY fact, and it is exactly what W4's `LIFetch` row needs: the kernel text is held
as `imgByte a v := ∃ tid, a ↦ₕ□ [⟨0, tid, v⟩]` — a DISCARDED-fraction singleton history (`MachCSL/Ctx.lean:
433-436`), persistent, assembled into `kernelText` (`Xv6/KernelText.lean:25-30`) from `bootRo (imgFlat
bootImage) bcRoLo bcRoHi` (`Xv6/BootCarve.lean:582`; `bcRoLo = ramBase`, `bcRoHi = _data`, `:143-144`); the
auth heap then says every reachable state's history at those addresses IS that singleton, so TsoMem's fetch
(`σ.mem.readBytes (ifetchAgent cpu) tvn …` at any `itv ≤ tvn ≤ top`, `MachCSL/Lang.lean:360-362`) returns the
image bytes — and a DMA write needs `histBytes … (DFrac.own 1)` (`MachCSL/WpDma.lean:142-145`), impossible
against `□`.  "No store" is neither exportable nor needed (an identical-value store is harmless).  (c) The
export touches shared files: a `powerInterp_textPristine` twin in `MachCSL/Adequacy.lean`, the hook and
`xv6TracePure` in `Xv6/SystemSlot.lean` (or a sibling root theorem), `kernelText` made reachable from the hook
(today the hook sees only `powerInterp` and `▷ xv6Slot`), `roots.txt`/`baseline.json` (a changed root
statement).  (d) `candKfetch`'s region `[0x80000000, 0x80007000)` (`plan:123-124`) must coincide with what W3
covers: state both over `[bcRoLo, bcRoHi)` (⊇ text + padding + rodata) or over `Kernel.text`'s footprints.
Change: W3 := `textPristine σ` ("every byte of `[bcRoLo, bcRoHi)` has history `[⟨0, _, img a⟩]`", or the
`readBytes`-at-any-view corollary) exported like `mmOk`; list the files above; size M–L; mark it SERIAL on the
adequacy files (nothing else in Stage 0 touches them, so still "launch first"); align `candKfetch`'s region;
W4's `LIFetch` row cites the history fact.

**[R5.3] `pairAdjacent` does not exist; W2 and W5b are both told to use it, and only one of them can define
it.**  Evidence: grep over `Weak/ Xv6/ MachCSL/ claude-notes/` finds `pairAdjacent` nowhere; it appears only
in the plan (`plan:313,398,405`) and in reviews R2/R3 (R2 coined it, `…-R2.md:107-110`).  W2 ("under
`pairAdjacent` + `execProgOk'S`'s shape") and W5b ("carries `pairAdjacent`") launch in parallel with "Deps:
none/W3's statement".  Change: W5b DEFINES it — "`pairAdjacent` (NEW): in a shaped run every exclusive pair's
two halves are separated only by the `LInstr`-free administrative star of `lblRealizesPair`
(`Weak/WeakAxRealize.lean:380-386`), no foreign store between them" — and W2's spike takes W5b's definition as
its hypothesis (dependency W2 ← W5b's statement, S, day one), or the plan fixes the definition text itself so
both workers copy it.

## SUGGESTIONS

- [R5.s1] W12-spike: the non-lemma `hppo` uses are two witness-graph proofs of `gppoGmo`
  (`Weak/WeakRvwmoKillArms.lean:811-813,1179-1181`, `intro e1 e2 hppo` for `lkw`/`lkw2`) which must be re-proved
  for `gppoCatGmo` (more arms: rules 2, 3); and "cat rules 1/4/5/7" → "1 (`Lock.lean:200,235`), 4 (`:125`), 5
  (`:120`)".
- [R5.s2] The plan is 570 lines against the reviser brief's "≤ ~400"; move the rev history, the verified-cite
  inventories and the RULED D-items to an appendix or to the review files.
- [R5.s3] W5c/D22: say the `_entry` witness is quiescent and certifies nothing about W13's bundle; the
  `uartinitone` first-`WriteReg` block is the natural `LDev` witness (Fab.lean §6: none exists in the tree).
- [R5.s4] §B(4): cite `imgByte`'s `□` singleton history (`MachCSL/Ctx.lean:433-436`) as THE mechanism behind
  "text never written" — it is also why `candKfetch` can be discharged for kernel text (W3) but not for user
  text (user pages are `own 1` cells).
- [R5.s5] (a)'s "devices as modelled" (`plan:73-74`) should say "device-ACTIVE runs are covered only once W13
  lands; until then the graph-side bundle is device-quiet" — the honest sentence for the header.

## Owner questions the plan is missing

- Q-R. The fabric at the graph tier ([R5.1]): accept a dev-order model as a trusted-base item of the
  published theorem (route-b's honest axiom `po ∪ rf ∪ gmo|W ∪ dev` acyclic, with T2-1c′ — sizeable), or
  accept `gdevAdj ⊆ gmo` as a NAMED STRENGTHENING (FabInd §5 shows it is not realized by today's
  linearization), or hold publication?  Device-quiet publication is not an option — it is vacuous for allocproc.
- Q-S. W3's export ([R5.2]): a new conjunct in `xv6TracePure` (changes the root theorem's statement and the
  audit baseline) or a sibling root `xv6TextAdequacy_closed` (new root, old statements untouched)?
