VERDICT: NOT SATISFIED

# Review R30 of `notes/weak-allocproc-plan.md` (rev 33)

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git or jj, no subagents).  Every cite
below was read at the working-copy tip of `../xv6iris-weak` (plan rev 33, 4,227 lines).  Scope per the R30 brief
(narrow): verify that rev 33 applied R29's two fixes ([R29.1] the `fcutT` parameter / `pfCutFactsT` third fact; [R29.2]
the stale lane sentence) against `Weak/TsoShadow.lean`, `Weak/MachOfPf.lean`, `Weak/SrvwmoXv6Adequacy.lean`, and decide
whether **W5d is launchable as written**.  W8-β′, W13 (I) and the W5 CLOSE-OUT are RUNNING; nothing below touches their
briefs (nothing unsound found).  Items (a)/(b) of the standing brief were settled in R1–R29 and are not re-opened.

**Sign-off.**  NO — ONE required change, S text, confined to W5d's first commit.  **[R29.1] is applied as R29 wrote it
and every cite holds** (below).  **[R29.2] is applied exactly** (`:2388-2389`).  **W5d is NOT launchable as written**
because rev 33 kept §B(4)(iii)'s pre-R29 sentence that `itvOf` AND its recurrence/frame condition are added to
`execProgOk'S` as per-index conjuncts (`:765-771`), and R29.1's inserted text re-states it ("the Exec twin in
`execProgOk'ST` (`itvOf k i`, `ls` in scope)", `:787`, `:2605`) — but `fcutT`'s type sees ONE `itv` value and nothing
else, so the recurrence `itvOf (k+1) s.esAg = itvStep (itvOf k s.esAg) … ls` and the frame condition are NOT guarded by
`fcutT` and do NOT vanish at M1's trivial instance.  Followed literally, the first commit either strengthens M1's premise
(the exact defect [R29.1] (3) rejected) or forces the worker to choose an `∃ itvOf` route whose "content unchanged" claim
needs an unplanned choice lemma — a design fork on day one of an L item.  The fix is one paragraph ([R30.1]); W5d is
launchable the moment it is in the brief (it can be handed as an addendum).  Do not shrink anything.

## What was checked and holds

- **[R29.1] applied as written** (`:3-13` header, `:775-796` §B(4)(iii), `:1394-1398` §C top, `:2350-2352` W-SCO NOTE,
  `:2598-2617` §C W5d).  Code evidence for every cite:
  `pfLoadFactsT`/`pfStepFactsT` `TsoShadow.lean:568-577` ✓ (`| _ => True` fetch arm `:573`); `pfLoadFactsTNonload :579-581`
  (plan says `:581-583` — off by two, cosmetic) ✓; `pfRunST` `:584-590`, `snoc` with exactly TWO facts `pfStepFacts fok c1 i l`
  and `pfLoadFactsT stamp st c1 i l` `:587-588` ✓ — the third fact `pfCutFactsT fcutT stamp st c1 i l` slots beside them;
  `pfRunSTFacts :599-620` ✓; `pfRunSTApp :622-632` discharges the load fact by `pfLoadFactsTNonload` `:631-632` ✓;
  `execPrefixPfRunProgShapedT :660` uses `pfRunSTApp` `:781` for the admin-star block ✓; `execWfPfRunPinShapedT :808` ✓.
  `contR.cons` `MachOfPf.lean:518-522` carries `pfStepFacts` + `pfLoadFactsT TsoShadow.cohSrc st c i l` `:520-521` ✓;
  `contRSnoc :524-528` ✓; `Hyps :658-680`, `cut :664-671` takes `pfStepFacts fok c (hartAgent cpu) (.LIFetch base tvs)`
  (UN-threaded) and concludes `∃ q, (tsoShadow cohSrc st (hartAgent cpu)).itv ≤ q ∧ q ≤ c.pcLog.length ∧ ifetchOk … ∧ ∀ byte
  t ≤ q` `:668-671` ✓ — M2's `fcutT itv img log i base tvs := ∃ q, itv ≤ q ∧ q ≤ |log| ∧ ifetchOk img log q base tvs ∧ ∀
  byte, t ≤ q` at `itv := (tsoShadow cohSrc st i).itv`, `img := c.pcImg`, `log := c.pcLog` IS that conclusion verbatim ✓
  (6 arguments: `Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop` ✓).  `simNode :878-896`, `hfT :886` ✓;
  `hH.fi` application `:1035`, `hH.cut … hrun hreach hR0 cpu base tvs c' hs hf` `:1043` ✓ (the new fact is in `simNode`'s
  hands once it is a premise beside `hfT`).  `machRunOfPfRun :2854-2870` (`contROfRun fok hrun` `:2866` is the
  `pfRunST → contR` builder) ✓; `cutOfPristine :2907-2975`, `hs`-case `PFIFetch` `:2924-2926`, `hnw :2928`, `ht0 :2948`,
  `hbound :2957` ✓.  `sailCycleOrder` `SrvwmoXv6Adequacy.lean:113-124` quantifies `∀ fok σ0 st c` over `pfRunST pstepEv pclsEv
  fok TsoShadow.cohSrc (wpInit …)` ✓; `fiOfSco :163-171` ✓; `m1Hyps :203-213` (`cut := cutOfPristine …` `:211-212`, `fi :=
  fiOfSco hsco _ σ0` `:213`) ✓; `srvwmoXv6M1Core :276-310` — its STATEMENT names `pfRunST pstepEv pclsEv (candKfetch …)
  TsoShadow.cohSrc … st cf` `:285-286` and `MachOfPf.contR (candKfetch …) … [] r cf` `:293-294`, so with `fcutT` threaded
  through `pfRunST` and `contR` **M1's statement TEXT changes exactly as the plan says**, and `tools/audit/baseline-weak.json`
  keys entries by NAME with `axioms`/`opaques` (R28/R29 verified) — the registered entry is stable ✓ (the W5 CLOSE-OUT's
  registration, running, is unaffected).  `SrvwmoXv6Witness.lean`: `execProgOk'SNil :272`, `execProgOk'SSnoc :280`,
  `srvwmoXv6M1Premises :599-607` (uses `execProgOk'ST … (candKfetch …) TsoShadow.cohSrc pst dv (candExec c)` `:604-605`),
  `srvwmoXv6M1PfRun :624-640` (via `execWfPfRunPinShapedT`), `srvwmoXv6M1Satisfiable :733` with the two-fetch `hfetch`
  `:751-756` ✓.  `PfRunShape.lean`: `fetchesOk :232-234`, `execProgOk'S :242-262` (the per-index `∃ (p pa : P) (da : D) (p' :
  P) (ls : List Wlabel), …` `:247-262` — `ls` in scope ONLY inside that existential), `pfStepFacts :265-269` ✓.
  `rowFetchM2` `PfStepTsoView.lean:778-786`, `hq :780` is exactly `(tsoShadow stamp st (hartAgent cpu)).itv ≤ q` — supplied by
  `pfCutFactsT`'s witness directly, as [R29.s5] says ✓; `proposedStmt` `PfStepTso.lean:102-124`, clause (3) `:115-118` already a
  hypothesis in the cut shape, its facts premise `pfStepFactsT fok TsoShadow.cohSrc st c (hartAgent cpu) l` `:110` — not
  re-pointed ✓.  `ifetchByteOk`/`ifetchOk` `WeakPromise.lean:220-226` ✓.
- **Census of `pfRunST`'s users** (grep over `Weak/ Xv6/ MachCSL/ tools/ vtest-lean/`): `PfRunShape.lean` (none — `pfRunS`
  only), `TsoShadow.lean`, `MachOfPf.lean`, `PfStepTso.lean` (**`pfRunSTAuthors :527-536`**, explicit `fok`/`stamp` binders),
  `SrvwmoXv6Witness.lean`, `SrvwmoXv6Adequacy.lean`.  `contR`/`machRunOfPfRun`/`cutOfPristine`/`sailCycleOrder`: `MachOfPf.lean`,
  `SrvwmoXv6Adequacy.lean` only (`AxEpilogue.lean:29,193` is `HcontRun`, `WeakRvwmoGlue.lean:400` is `csHyps` — different names).
  So the plan's edited-file list (`PfRunShape`, `TsoShadow`, `MachOfPf`, `SrvwmoXv6Witness`, `SrvwmoXv6Adequacy`) misses ONE
  signature in `PfStepTso.lean` ([R30.s1], cosmetic).
- **[R29.2] applied exactly** (`:2388-2389`): "**W8-β′** (RUNNING), then **W-RSV** (when β′ merges; M1 ✓ per D26; L–XL
  [R12.1]), then **W8 (f2-ctx)** rebasing on W-RSV — [OWN.41][R28.5][R29.2]; [OWN.37]'s earlier order superseded" ✓; the
  rev-28 RECORD block stays historical ✓.
- **Header bookkeeping**: `:3-20` and `:314` record R29's two fixes, s1/s5 adopted, s2/s3 deferred to merge review ✓; the
  W-SCO brief is unchanged with the [R29.s1] NOTE appended `:2341-2352` ✓ (the brief's own text `:2296-2330` still reads
  "`srvwmoXv6M1Core`'s statement unchanged" — true OF W-SCO's edits, see [R30.s4]).
- **The step-list side is consistent with M2's needs**: `ShFull` `TsoShadow.lean:292-295` carries `itv`/`fiArm`; `shStepF
  :310-319` raises `itv` to `max itv (fencePost true false tv rv (ownPub i au))` at an own `LFence false×4` with `fiArm`, set
  by `LInstr`, cleared by `LIFetch` ✓ (the fence.i/`sfence.vma`-marker split by `sailCycleOrder`, not by `ls`); `tsoShadow
  :500`, `shadowOf :508` MEMORY-only ✓.  So "the step-list `tsoShadow`'s `itv` equals `itvOf` along the replay" (`:794`) is
  the `itv` analogue of the `.mem` projection lemma — plausible M2-side work, PROVIDED the Exec side defines `itvOf` by a
  recurrence that mirrors `shStepF` — which brings us to [R30.1].

## REQUIRED changes

- **[R30.1] W5d's first commit: `itvOf` and its recurrence/frame condition must be `fcutT`-GUARDED (trivial at M1), and
  `itvOf` must not be a parameter of any shared definition; today's text puts both into `execProgOk'S` unguarded.**
  *What is wrong (evidence).*  (1) `:765-771`: "W5d therefore adds a per-row, per-step `itvOf : Nat → Nat → Nat` to
  `execProgOk'S`, … CONSTRAINED inside each index's conjunct, where `ls` IS in scope …: `itvOf (k+1) s.esAg = itvStep (itvOf k
  s.esAg) (tv, rv of the memory-field shadow at k) pub ls` …, plus the FRAME condition `itvOf (k+1) i = itvOf k i` for every
  row `i ≠ s.esAg` and at every non-fence step" — pre-R29 text, kept.  (2) `:787` and `:2605`: "the Exec twin in
  `execProgOk'ST` (`itvOf k i`, `ls` in scope)" — R29.1's text, which names `itvOf k i` as if it were a parameter of the
  shared predicate; and `:789-792`/`:2607-2611`: "**M1 instantiates `fcutT := fun _ _ _ _ _ _ => True`** … M1's statement
  TEXT changes; its content … do[es] not".  (3) `fcutT : Nat → Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop`
  (`:775-776`) receives ONE `itv` value, the pre-state and the fetch; it cannot see `itvOf (k+1)`, `ls`, or the other rows,
  so neither the recurrence nor the frame condition can live inside the M2 instance of `fcutT` — as written they are
  UNGUARDED conjuncts of `execProgOk'S` (`PfRunShape.lean:242-262`), which is M1's premise through `execProgOk'ST`
  (`TsoShadow.lean:560-561`) and `srvwmoXv6M1Premises` (`SrvwmoXv6Witness.lean:604-605`).  Consequences: if `itvOf` is a
  PARAMETER (the natural reading of (1)), M1 must name one — any fixed choice (e.g. `fun _ _ => 0`) makes the recurrence
  FALSE on candidates where a hart executes `fence.i` after an own store (`fencePost true false tv rv pub ≥ pub ≥ 1`,
  `MachCSL/Lang.lean:161-166`, mirrored by `shStepF` `TsoShadow.lean:312-313`), so `srvwmoXv6M1Core` would apply to FEWER
  candidates — a STRENGTHENED premise, exactly [R29.1] (3)'s rejected defect, and `:792` "its content … do[es] not [change]"
  would be false; if `itvOf` is EXISTENTIAL (`∃ itvOf, …` around `execProgOk'S`), M1's content is preserved only by an
  unplanned lemma "`execProgOk'S` (today) → `∃ itvOf, execProgOk'S′`" (choose the per-index `(p, pa, da, p', ls)` tuple
  classically, define `itvOf` by recursion with the frame condition — S–M), `srvwmoXv6M1Satisfiable :733` must exhibit a
  witness, and `m1PremisesS :611-618`'s forgetful direction changes shape.  Either way the worker hits a design fork on
  commit 1 that the brief is supposed to have closed.  Note the step-list side needs NONE of this: `tsoShadow`'s `itv` is
  already computed from `st` (`shStepF`), and M1's run construction (`execWfPfRunPinShapedT :808` → `pfRunSTApp :622`)
  discharges `pfCutFactsT` at `fcutT := True` by `trivial`.
  *Exact change (`:765-771` §B(4)(iii); `:787` and `:2605` the two "Exec twin" clauses; one sentence at `:792`/`:2609`).*
  Replace `:765-771`'s "adds a per-row, per-step `itvOf … to execProgOk'S` … CONSTRAINED inside each index's conjunct" by:
  "W5d defines `itvOf : Nat → Nat → Nat` (per step `k`, per row) as a FREE variable of M2's premise set
  `srvwmoXv6M2Premises` — NOT a parameter of `execProgOk'S`/`execProgOk'ST`/`pfRunST` — DRIVEN by …" (keep the
  `itvStep`/`ownPub`/frame text as the content of M2's INSTANCE).  Replace `:787` and `:2605`'s "the Exec twin in
  `execProgOk'ST` (`itvOf k i`, `ls` in scope)" by: "**the Exec-level twin is a SECOND parameter `fcutE`, per INDEX**, added
  as one conjunct INSIDE `execProgOk'S`'s per-index existential (`PfRunShape.lean:247-262`, beside `fetchesOk fok (stt E k)
  s.esAg ls` so it shares that index's `ls`): `fcutE k s.esAg ls (stt E k)` with `fcutE : Nat → Nat → List Wlabel → Mstate →
  Prop`; **M1 instantiates `fcutE := fun _ _ _ _ => True`**; M2 instantiates `fcutE k ag ls σ := (∀ base tvs, .LIFetch base
  tvs ∈ ls → fcutT_M2 (itvOf k ag) σ.msImg σ.msLog ag base tvs) ∧ itvOf (k+1) ag = itvStep (itvOf k ag) (shadowOf cohSrc
  (E.exTr.take k) ag).tv/.rv (ownPub ag (authors of σ.msLog)) ls ∧ (∀ i ≠ ag, itvOf (k+1) i = itvOf k i)` with `itvOf` free
  (bound in `srvwmoXv6M2Premises`); `fetchesOk`'s `fok` conjunct is unchanged.  Every new conjunct of a SHARED definition
  (`execProgOk'S`, `execProgOk'ST`, `pfRunST.snoc`, `contR.cons`, `Hyps`) is a parameter instance that is `True` at M1 —
  `itvOf`, its recurrence and its frame condition included — so M1's content is unchanged BY CONSTRUCTION (no choice lemma).
  The M1 replay lemmas (`execPrefixPfRunProgShapedT :660`, `execWfPfRunProgShapedT :789`, `execWfPfRunPinShapedT :808`) are
  stated at the trivial instances of BOTH parameters (their `pfRunSTApp` step discharges `pfCutFactsT` by `trivial`); the
  M2 replay `execWfPfRunProgF` (the new file) is the one that turns `fcutE`'s per-index instance into `pfCutFactsT`'s
  per-fetch fact, carrying `∀ i, (tsoShadow cohSrc st i).itv = itvOf n i` as a replay invariant beside the `.mem` projection
  (`:794`'s lemma, stated there)."  At `:792`/`:2609` add "(both parameters; `itvOf` appears in no shared definition)".
  S text on an L item; FAITHFUL (proof organisation; the published quantifier, the trusted base and every conclusion
  unchanged; RVWMO/Sail/Zifencei/PMAs silent).  The worker may pick a different guard shape (e.g. one Exec parameter
  receiving `itvOf k`/`itvOf (k+1)` whole) — the REQUIREMENT the plan must state is the sentence in bold: nothing
  non-trivial enters M1's premise, and `itvOf` is not a shared parameter.

## SUGGESTIONS

- **[R30.s1] Add `PfStepTso.lean` to W5d's edited-file list.**  `pfRunSTAuthors` (`PfStepTso.lean:527-536`) takes `pfRunST pstep
  pcls fok stamp c0 st c` with explicit binders and inducts on it (`| snoc c1 c2 st i l _ hs _ _ ih`) — one binder and one
  `_` more after the threading.  `:2609-2612` says `PfStepTso.lean` is touched "only if `proposedStmt` is re-pointed"; make
  it "`PfStepTso.lean` (`pfRunSTAuthors`'s binder; `proposedStmt :102-124` NOT re-pointed)".  (Its single use is `MachOfPf`'s
  `R-log` link; grep `pfRunSTAuthors` when threading.)
- **[R30.s2] `pfRunSTFacts` (`TsoShadow.lean:599-620`) should return the third fact too** (`pfStepFactsT … ∧ pfCutFactsT …`, or a
  bundled `pfStepFactsTC`), so W-SCO's [R29.s1] recipe and M2's `rowFetchM2` consumers read every fact of a PAST step from
  one lemma.  S; say it in the first-commit list.
- **[R30.s3] `sailCycleOrder`'s `∀ fcutT` is redundant; either form is fine, say which.**  `pfRunST` at ANY `fcutT` forgets to
  the trivial instance (a one-line `pfRunSTForgetCut`, the twin of `pfRunSTForget :591-597`), so "`∀ fcutT`" and "stated at
  the trivial instance" are equivalent premises.  Stating the named premise at the trivial instance keeps its text closest
  to today's (`:113-124`) and lets W-SCO's `sailCycleOrderK` (being stated now over today's type) adapt by the forget lemma
  alone.  Cosmetic; FAITHFUL either way.
- **[R30.s4] Qualify two "unchanged" claims.**  `:1387` "`srvwmoXv6M1Core` untouched" and `:2296`/`:2301` "`srvwmoXv6M1Core`'s
  statement unchanged" are true of W-SCO's edits only; W5d's threading changes that statement's TEXT (`:285-286,293-294` name
  `pfRunST`/`contR`), as `:11`/`:1398` already say.  Add "by W-SCO" at the two sites so the merge reviewer does not flag a
  contradiction.
- **[R30.s5] Name the induction sites.**  `:788`/`:2606` "`contR.cons`/`simNode` carry it" — also `contRSnoc :524-528` and
  `contROfRun :540` (`machRunOfPfRun :2866`'s builder from `pfRunST`), both inducting on the run; and `pfRunSTForget :591`,
  `pfRunSTPinSub :634` (one `_` each).  Cosmetic.
- **[R30.s6] Cosmetic cites.**  `pfLoadFactsTNonload` is `TsoShadow.lean:579-581` (plan: `:581-583`); `pfRunSTApp`'s
  `Nonload` discharge is `:631-632`.

## Owner questions the plan is missing

None.  [R30.1] is proof organisation (which conjunct is guarded by which parameter so that M1's premise keeps its content).
*Spec (FIRST).*  RVWMO, riscv.cat, the Sail model in this tree (`vendor/lean-sail`, `model/Lean_RV64D`), Zifencei and the
PMAs say nothing about how a Zifencei side condition is threaded through a Lean conformance predicate or whether an
instruction-view counter is a parameter or a free variable of a premise set; every option in [R30.1] and the suggestions is
FAITHFUL — the published quantifier, the trusted base (`sailCycleOrder` the one named ISA-model premise until W-SCO demotes it
for kernel text; `gzFetch`/`ioResidueGmo` unchanged) and the conclusions do not move.  The plan's existing questions keep
their "*Spec (FIRST).*" lines and the 2026-10-10 format (unchanged since R29; Q-RSV-order `:3296-3300` RULED).
