VERDICT: NOT SATISFIED

# Review R31 of `notes/weak-allocproc-plan.md` (rev 34)

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git or jj, no subagents).  Every cite
below was read at the working-copy tip of `../xv6iris-weak` (plan rev 34, 4,258 lines).  Scope per the R31 brief
(narrow): verify that rev 34 applied [R30.1] (`itvOf` free in `srvwmoXv6M2Premises`; the second per-index parameter
`fcutE` inside `execProgOk'S`'s existential carrying the fetch cut / recurrence / frame; M1 instantiates `True`) against
`Weak/PfRunShape.lean`, `TsoShadow.lean`, `MachOfPf.lean`, `SrvwmoXv6Adequacy.lean`, and decide whether **W5d is
launchable as written**.  W8-β′, W13 (I), W5 CLOSE-OUT and W-SCO briefs are untouched (nothing unsound found).  Items
(a)/(b)/(d) of the standing brief were settled in R1–R30 and are not re-opened.

**Sign-off.**  NO — ONE required change, S text (one paragraph), confined to the M2 INSTANCE of `fcutE` in §B(4)(iii)
(`:803-806`) and §C W5d (`:2635`); **W5d's FIRST commit (the `fcutT`/`fcutE` threading, `:1423-1424`) is unaffected and
may start today; the paragraph can be handed as a launch addendum** (R30's precedent).  **[R30.1] is applied as R30 wrote
it and every cite holds** (below).  The remaining defect is in what the M2 instance's `itv` recurrence may use: the plan
says `ls` "serves ONLY to tell `fence.i` from the `sfence.vma` marker by `emFenceI`'s criterion" (`:781-782`), i.e. the
raise at a `LFence false×4` step is decided from THIS index's admin block alone — but the step-list shadow's raise is
`lbFenceZero l && f.fiArm` with `fiArm` a STATE carried across steps (`TsoShadow.lean:310-319`), equal to "the latest
own `LInstr`/`LIFetch` in the WHOLE step list is `LInstr`" (`fiArmLastCyc`, `SrvwmoXv6Adequacy.lean:135-137`); an index's
`ls` decides it only when `ls` contains a cycle label, and the Exec side cannot see earlier stars (existential per
index, `PfRunShape.lean:247`).  "Every fence step's star contains its own fetch and announce" is a fact of the Sail
cycle that is NOT in the assumed premise (`sailCycleOrder :113-124` speaks of `lastCyc` over the whole `st`) and whose
generic proof is W-SCO's residual-invariant work ([R29.s2], M–L, kernel text only).  Followed literally, the replay
invariant `∀ i, (tsoShadow cohSrc st i).itv = itvOf n i` (`:813`) is unprovable at a fence step whose star is
cycle-free, and the worker meets an unplanned design choice mid-item.  The fix is S and lives entirely in W5d's own
file (`itvOf` is free, so a companion free bit costs nothing in any shared definition) — [R31.1] gives the two
routes and what each needs from the first commit's signature.  Do not shrink anything.

## What was checked and holds

- **[R30.1] applied as written.**  Header `:3-14` ✓; §B(4)(iii) `:777-821` ✓ (`itvOf` "a FREE variable of M2's premise
  set `srvwmoXv6M2Premises` — NOT a parameter of `execProgOk'S`/`execProgOk'ST`/`pfRunST`" `:778-779`; `fcutE : Nat → Nat →
  List Wlabel → Mstate → Prop` as "one conjunct `fcutE k s.esAg ls (stt E k)` INSIDE `execProgOk'S`'s per-index existential
  beside `fetchesOk fok (stt E k) s.esAg ls`" `:801-803`; M1 `fun _ _ _ _ => True` `:803-804`; the bold sentence `:806-809`;
  M1 replay lemmas at both trivial instances `:810-812`; the replay invariant `:813`; `:821` "(both parameters; `itvOf`
  appears in no shared definition [R30.1])"); §C top `:1423-1424` ✓; §C W5d `:2634-2636` ✓.  Code: `execProgOk'S`
  `PfRunShape.lean:242-262`, the per-index existential `∃ (p pa : P) (da : D) (p' : P) (ls : List Wlabel), …` `:247`,
  `fetchesOk fok (stt E k) s.esAg ls` `:251` — the slot for `fcutE k s.esAg ls (stt E k)` ✓; `stt E k : Mstate`
  (`WeakAxiomatic.lean:294`; `Mstate` = `msImg`/`msLog`/`msWs` `:108-111`) ✓, so `σ.msImg σ.msLog` in the M2 instance
  type-check ✓.  `fcutT`'s 6-ary type and `pfCutFactsT`'s shape are as R30 verified; `Hyps.cut`'s conclusion
  `MachOfPf.lean:668-671` is still verbatim M2's `fcutT` at `itv := (tsoShadow cohSrc st (hartAgent cpu)).itv` ✓; the
  `fi` field `:672-680`; `simNode :879`, `hfT :886`, `hH.fi :1035`, `hH.cut … hrun hreach hR0 cpu base tvs c' hs hf` `:1043`
  ✓; `simStep :2773-2782` (ALSO takes `hH : Hyps fok g0 c0` + `hrun : pfRunST …` — a second induction/plumbing site beside
  `simNode`, see [R31.s2]); `simRun :2815-2817`; `machRunOfPfRun :2854-2870`; `cutOfPristine :2907-2930` ✓.
  `sailCycleOrder :113-124` quantifies `∀ fok σ0 st c` over `pfRunST pstepEv pclsEv fok TsoShadow.cohSrc (wpInit …)`; stating
  it AT the trivial `fcutT` [R30.s3] keeps `fiOfSco :163-171` (which just applies `hsco fok σ0 st c hrun`) one-line, and
  M2's `fi` discharge is `fiOfSco` after `pfRunSTForgetCut` ✓.  `m1Hyps :203-213` (`cut := cutOfPristine …` `:211-212`,
  `fi := fiOfSco hsco _ σ0` `:213`) ✓; `srvwmoXv6M1Core :276-310` names `pfRunST … (candKfetch …) TsoShadow.cohSrc` `:284-285`
  and `MachOfPf.contR (candKfetch …)` `:291-292` — statement TEXT changes, name/axioms/opaques do not ✓ (registration by
  NAME, `baseline-weak.json`, R28/R29).  `SrvwmoXv6Witness.lean`: `execProgOk'SNil :272-273`, `execProgOk'SSnoc :280-293`
  (takes `fetchesOk fok (candLastSt c) i ls` `:286` — the `fcutE` twin goes beside it, trivial at M1),
  `srvwmoXv6M1Premises :599-607` (`execProgOk'ST … (candKfetch …) TsoShadow.cohSrc pst dv (candExec c)` `:605-606`),
  `m1PremisesS :611-617`, `srvwmoXv6M1PfRun :624-640` via `execWfPfRunPinShapedT`, `srvwmoXv6M1Satisfiable :733`, the
  `hfetch` block `:751-756`, `execProgOk'SSnoc … hfetch hsca trivial …` `:775-778` ✓.  `TsoShadow.lean`: `execProgOk'ST
  :559-560`, `execProgOk'STForget :562-563`, `pfLoadFactsT/pfStepFactsT :568-577`, `pfLoadFactsTNonload :579-581` (the
  [R30.s6] cite now correct `:11`) ✓, `pfRunST :584-589`, `pfRunSTForget :591-597`, `pfRunSTFacts :599-620`, `pfRunSTApp
  :622-632`, `pfRunSTPinSub :634-640`, `execPrefixPfRunProgShapedT :660`, the `pfRunST.snoc` at `:755` and `pfRunSTApp` at
  `:721,:781`, `execWfPfRunProgShapedT :789`, `execWfPfRunPinShapedT :808-822` ✓.  `PfStepTso.lean`: `pfRunSTAuthors
  :527-536` in the edited-file list ([R30.s1] adopted, `:2642-2643`) ✓; `proposedStmt :102-124`'s clause (3) `:115-118` is
  the cut conclusion as a hypothesis — NOT re-pointed ✓.  `rowFetchM2` `PfStepTsoView.lean:778-786`, `hq :780` ✓.
- **The bold sentence is TRUE of the design as pinned**: `fcutE`'s M1 instance `True` makes the new `execProgOk'S`
  conjunct vacuous, so `execProgOk'ST`, `srvwmoXv6M1Premises`, `execProgOk'SNil/SSnoc` and `srvwmoXv6M1Satisfiable` keep
  their content; `pfCutFactsT` at `fcutT := True` is discharged by `trivial` in `pfRunSTApp`'s step (`:631-632`) and in
  the `pfRunST.snoc` at `:755`; `itvOf` appears nowhere shared ✓.  The `execProgOk'S` census (grep over `Weak/ Xv6/
  MachCSL/`): `PfRunShape.lean` (def + `execProgOk'SForget :300`, `execProgOk'SSca :310`), `TsoShadow.lean:560,563`,
  `SrvwmoXv6Witness.lean:273,283,293,614` — all in the edited-file list ✓; `fetchesOk` users: `PfRunShape.lean:251`,
  `SrvwmoXv6Witness.lean:286,751` ✓; `Hyps` users outside `MachOfPf.lean`: `SrvwmoXv6Adequacy.lean:206` only ✓; `contR`
  outside: `SrvwmoXv6Adequacy.lean:291` only ✓; `MachOfPfDisk.lean` uses none of `pfRunST`/`Hyps`/`contR` ✓.
- **Within an admin star the shadow's `itv` and the log are constant**, so the M2 instance's cut conjunct at `(stt E k)`
  with `itvOf k ag` transfers to `pfCutFactsT` at each fetch's own prefix: `shStepF` raises `itv` only at `lbFenceZero l`
  (`TsoShadow.lean:310-313`), `lbAdmin true` admits only `LSilent/LDev/LRegW/LCtrl/LInstr/LIFetch` (`WeakAxRealize.lean:
  130-134`), none a fence or a write ✓ — the same argument the landed replay already makes for `fetchesOk → pfStepFacts`.
- **`Hyps.cut` at M2 is `pfCutFactsT` verbatim** (`:668-671` vs `pfCutFactsT fcutT_M2 cohSrc st c (hartAgent cpu) (.LIFetch
  base tvs)` unfolded at `base tvs rfl`) ✓; `rowFetchM2`'s `hqt : q ≤ (stAuthors st).length` comes from `q ≤ c.pcLog.length`
  + `pfRunSTAuthors` (`PfStepTso.lean:527-536`) ✓.
- **`LFence false false false false` is exactly fence.i's barrier label and the `sfence.vma` marker**: `ebarLabel`
  (`WeakEvInst.lean:287-290`) gives it iff `ebarNow b = none`, and `.Barrier_RISCV_i` is the ONLY `none` arm
  (`WeakEvLang.lean:741-753`; `.Barrier_RISCV_tso => some (true,false,true,false)` `:752`) ✓; the marker is `annLabel`'s on
  `sfAnnB` (`:418-422`).  So at a `LFence false×4` realizing step the hart's node `pa` is a `.barrier .Barrier_RISCV_i`
  node or an `.instrAnnounce n w` node with `sfAnnB n w` — the discriminator `Hyps.fi`/`sailCycleOrder` already use
  (`MachOfPf.lean:672-680`, `SrvwmoXv6Adequacy.lean:119-124`).  This is what makes route (ii) of [R31.1] available.

## REQUIRED changes

- **[R31.1] The M2 instance of `fcutE` must carry the `fiArm` STATE (or read the node `pa` under `sailCycleOrder`);
  "`ls` serves ONLY to tell `fence.i` from the marker" is not enough for the replay invariant.**
  *What is wrong (evidence).*  (1) `:781-782`: "`ls` serves ONLY to tell `fence.i` from the `sfence.vma` marker by
  `emFenceI`'s criterion (the marker's star ends in `LIFetch`, `fence.i`'s in the announce `LInstr`)", and `:805`: "`itvOf
  (k+1) ag = itvStep (itvOf k ag) (shadowOf cohSrc (E.exTr.take k) ag).tv/.rv (ownPub ag …) ls`" — the raise is a function
  of `ls` (plus `itvOf k ag`, the memory shadow, the log).  (2) The step-list side it must match: `shStepF`
  (`TsoShadow.lean:310-319`) raises `itv` iff `lbFenceZero l && f.fiArm`, with `fiArm` set by `LInstr`, cleared by
  `LIFetch`, else CARRIED (`| _ => f.fiArm`, `:318`); `fiArmLastCyc` (`SrvwmoXv6Adequacy.lean:135-137`): `fiArm = fiOf
  (lastCyc i st)` over the WHOLE step list.  (3) The Exec side sees one index's `ls` (`PfRunShape.lean:247`); earlier
  stars are not in `E.exTr` (`Estep` = `esAg`/`esLb : Lbl`, `WeakAxiomatic.lean:103-106`; `Lbl` has no `LInstr`/`LIFetch`
  `:87-97`).  When the fence step's `ls` has no cycle label, "latest in `ls` is `LInstr`" is `false` while the shadow's
  `fiArm` may be `true` (the previous latest own cycle label an `LInstr`): the shadow raises, `itvOf` does not, and
  `:813`'s invariant `∀ i, (tsoShadow cohSrc st i).itv = itvOf n i` fails at that step.  (4) The missing fact — "a
  `pstepEv` star that ends at a barrier node contains that instruction's `LIFetch` and `LInstr`" — is the Sail cycle
  (`UCycleDefs.lean:11-17`), NOT the assumed premise: `sailCycleOrder :119-124` constrains `lastCyc (hartAgent cpu) st`
  over the full `st`, not this star; its generic proof over `SailM` residuals is W-SCO's [R29.s2] invariant (M–L,
  kernel text).  W5d (user text, M2) cannot rely on it.  (5) The plan already records the pattern once: `fiArm` is a
  bookkeeping bit "of `emFenceI`'s criterion" in `ShFull` (`:1680`), added precisely because the memory fields do not
  determine it.
  *Exact change (one paragraph replacing `:781-782`'s "`ls` serves ONLY …" clause and `:805`'s `itvStep` line; one
  clause at `:2635`).*  "The raise at a `LFence false×4` step is decided by the step-list shadow's `fiArm` STATE
  (`shStepF`, `TsoShadow.lean:310-319`), which this index's `ls` determines only when `ls` contains a cycle label; the
  M2 instance therefore carries it by ONE of two routes, the worker's choice, both S and both inside W5d's own file:
  **(i) a companion free bit `fiOf : Nat → Nat → Bool` bound in `srvwmoXv6M2Premises` beside `itvOf`** — `fiOf (k+1) ag =
  foldl (LInstr ↦ true, LIFetch ↦ false, else keep) (fiOf k ag) ls`, `itvOf (k+1) ag = if s.esLb = .LFence false false
  false false ∧ fiOf' then max (itvOf k ag) (fencePost true false tv rv pub) else itvOf k ag` where `fiOf'` is that fold
  (the realizing label is never a cycle label), frame `∀ i ≠ ag, fiOf (k+1) i = fiOf k i ∧ itvOf (k+1) i = itvOf k i`, boot
  `∀ i, itvOf 0 i = 0 ∧ fiOf 0 i = false` (= `ShFull.zero`, `:299`); the replay invariant becomes `∀ i, (tsoShadow cohSrc
  st i).itv = itvOf n i ∧ (tsoShadow cohSrc st i).fiArm = fiOf n i` and holds BY CONSTRUCTION (no Sail fact); needs
  `s.esLb`, obtained by closing the instance over `c` (`(candExec c).cdTr[k]?`) or by passing `s : Estep` in `fcutE`'s
  signature.  **(ii) read the realizing node `pa` under `sailCycleOrder`**: raise iff `pa = .PHart cpu (.impure (.ok
  (.barrier .Barrier_RISCV_i)) k) …` (`ebarLabel`/`ebarNow`: `.Barrier_RISCV_i` is the only `none` arm, `WeakEvLang.lean:
  741-753`, so `LFence false×4` at a barrier node IS fence.i and at an announce node IS the marker); the replay then
  uses `sailCycleOrder` (M2's premise anyway) at that node to get `fiArm = true`/`false` and match `shStepF`; needs `pa : P`
  in `fcutE`'s signature (`fcutE : Nat → Nat → List Wlabel → P → Mstate → Prop`, applied `fcutE k s.esAg ls pa (stt E k)`;
  `P` is `PfRunShape`'s section variable, `:218`), i.e. a FIRST-commit decision.  Either way `ls` is NOT the carrier of
  `emFenceI`'s criterion on the Exec side; the bold sentence of [R30.1] is unchanged (`fiOf`, like `itvOf`, is free in
  `srvwmoXv6M2Premises` and a parameter of no shared definition; `fcutE` stays `True` at M1 whatever its arity)."  At
  `:2635` add "(the `fiArm` state carried per [R31.1] (i) or (ii); the first commit fixes `fcutE`'s arity accordingly)".
  S text; FAITHFUL (proof organisation; the published quantifier, the trusted base — `sailCycleOrder` the one named
  ISA-model premise — and every conclusion unchanged; RVWMO/Sail/Zifencei/PMAs silent on how a Lean replay tracks a
  bookkeeping bit).  The first commit needs this paragraph only to choose `fcutE`'s arity (route (ii)); with route (i)
  the type at `:801` stands as written.

## SUGGESTIONS

- **[R31.s1] Make the closure over `c` explicit in the M2 instance.**  `:805` writes `(shadowOf cohSrc (E.exTr.take k) ag)`
  inside `fcutE k ag ls σ := …` with `E` unbound; `Mstate` has no views (`WeakAxiomatic.lean:108-111`), so the instance must
  be `fcutE_M2 c itvOf` (and `fiOf`) closing over the candidate, with `E := candExec c`.  Say "`fcutE_M2 c itvOf : Nat → Nat
  → List Wlabel → Mstate → Prop`, closing over `c`" once at `:804`.  Cosmetic.
- **[R31.s2] Name the two remaining `pfRunST`/`Hyps` sites the first commit touches in `MachOfPf.lean` and `TsoShadow.lean`.**
  `simStep :2773-2782` (takes `hH : Hyps fok g0 c0`, `hrun`, `hfT` — the fact is passed on to `simNode`) and `simRun
  :2815-2817`; `TsoShadow.lean`'s spike theorems `g1NoRunT :890-898` (`pfRunSTFacts` destructuring gains one `_`) and `g2RunT
  :953-963` (four explicit `pfRunST.snoc` applications, each gaining a `trivial`).  Cosmetic; `:2637-2638`'s list is otherwise
  complete.
- **[R31.s3] State the boot values of the free functions in `srvwmoXv6M2Premises`** (`itvOf 0 i = 0`, and `fiOf 0 i = false`
  under route (i)) — the replay invariant's base case at `st = []` is `ShFull.zero` (`TsoShadow.lean:299`).  The plan never
  writes `itvOf 0`.  S, one clause.
- **[R31.s4] Say the M1 replay lemmas may be stated at ANY `fcutE` (unused) and the trivial `fcutT`.**  `execPrefixPfRunProgShapedT
  :660` only needs to DROP the Exec conjunct; "stated at BOTH trivial instances" (`:810-811`) is fine but the generic-`fcutE`
  form costs nothing and is what `execProgOk'SForget`-style forgetful lemmas want.  Cosmetic.
- **[R31.s5] `fiOfSco` keeps one line under [R30.s3]** — note at `:818` that `m2Hyps.fi` is `fiOfSco hsco _ σ0 st c
  (pfRunSTForgetCut … hrun)`, so the worker does not generalise `sailCycleOrder` by hand.  Cosmetic.

## Owner questions the plan is missing

None.  [R31.1] is proof organisation (which per-index data the Exec-side recurrence may read so that the replay
invariant is provable without the Sail-cycle fact).  *Spec (FIRST).*  RVWMO (the memory-model chapter), riscv.cat, the
Sail model in this tree (`vendor/lean-sail`, `model/Lean_RV64D`; the cycle `ucDispatch >>= fetch >>= ucAfterFetch`,
`UCycleDefs.lean:11-17`), Zifencei and the PMAs say nothing about how a Lean conformance predicate tracks "an announce
has happened since the last fetch" — the Sail model DOES fix that order per cycle (which is why both routes are
sound), but it is silent on the bookkeeping; routes (i) and (ii) are both FAITHFUL (the published quantifier, the
trusted base — `sailCycleOrder` stays the one named ISA-model premise until W-SCO demotes it for kernel text;
`gzFetch`/`ioResidueGmo` unchanged — and every conclusion do not move; route (ii) merely USES the premise M2 already
has).  The plan's existing questions keep their "*Spec (FIRST).*" lines and the 2026-10-10 format (unchanged since
R30; Q-RSV-order `:3296-3300` RULED).
