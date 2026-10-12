VERDICT: NOT SATISFIED

# Review R29 of `notes/weak-allocproc-plan.md` (rev 32)

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git or jj, no subagents).  Every cite
below was read at the working-copy tip of `../xv6iris-weak` (plan rev 32, 4,166 lines).  Scope per the R29 brief
(narrow): verify that rev 32 applied R28's five S fixes correctly and decide whether **W5 CLOSE-OUT**, **W-SCO**, **W5d**
and **W-RSV** (after W8-β′ merges) are launchable as written.  W8-β′ and W13 (I) are RUNNING; nothing below touches
their briefs (nothing unsound found).  Items (a)/(b) of the standing brief were settled in R1–R28 and are not re-opened;
the spot-checks that bear on this round are under "What was checked".

**Sign-off.**  NO — two required changes.  **W5 CLOSE-OUT: LAUNCHABLE as written** ([R28.1] applied exactly; the pinned
entry is `Xv6.xv6FsAdequacy_closed`'s, the audit's rules are cited correctly).  **W-SCO: LAUNCHABLE as written** ([R28.2]
applied; one S recipe gap recorded as [R29.s1], not a stall).  **W-RSV: LAUNCHABLE right after W8-β′ merges** ([R28.5]
applied; the Launch (rev 32) paragraph, its 13 `MachOfPf.lean` guard sites and the lane order check out), modulo ONE
stale lane-order sentence that still states the superseded order inside §C's serial-items paragraph ([R29.2], one
sentence).  **W5d: NOT launchable as written** — [R28.4]'s route ("`fok` stays 5-ary, the `itvOf` bound enters through a
new `.LIFetch` arm of `pfLoadFactsT` and a conjunct of `execProgOk'S`, `Hyps.cut` discharged from `pfStepFactsT`'s two
conjuncts, `SrvwmoXv6Adequacy.lean` untouched, M1 text-identical") does not type-check against `Hyps.cut` and, as
stated, breaks the REGISTERED M1's proof: the two shared definitions it changes are the ones M1's run construction and
non-vacuity witness are proved over ([R29.1]).  The fix is S text and proof organisation (a trivially instantiated
parameter), FAITHFUL; it changes where the M2 clause is carried, not what it says.  Do not shrink anything.

## What was checked and holds

- **[R28.1] applied exactly** (`:2225-2237`).  The pinned entry equals `tools/audit/baseline.json:11-14`
  (`Xv6.xv6FsAdequacy_closed`: three axioms, opaques `xv6_resv_is_valid`/`xv6_resv_matches`/`MachCSL.bootImageSealed`) ✓;
  `isBvCertName`/`plain` filter and the "stale baseline" rejection are `Audit.lean:119-124` and `:305-313` as cited ✓;
  `#print axioms` vs `opaque`s `:41-53` ✓; `bv_decide_certificates` is printed at `:393` ✓; `audit.sh:44`
  (`XV6_AUDIT_MODULES`) and `:51` (the `--build` list) are the two lists to extend ✓; `lint.sh:37-57` checks roots ↔
  baseline name agreement only (not the module list) ✓; `platform_hooks` identical in both baselines (`baseline.json:68-72`,
  `baseline-weak.json:130-142`) ✓; `lake build MachCSL Xv6 Weak` = `lakefile.toml:2`'s default targets ✓.  The ten current
  `baseline-weak.json` entries list the two `resv` opaques only (none has `bootImageSealed`) ✓.  Comment sites: `audit.sh:
  13-18`, `roots-weak.txt:1-7`, the `comment` of `baseline-weak.json:2-6` (still says "Weak.AxSpinT2b,Weak.AxSpinT2c"),
  `Audit.lean:85-95` (same stale pair) — all named by the CLOSE-OUT ✓.
- **[R28.2] applied** (`:2255-2302`).  `MachOfPf.Hyps` is `:658-680`: `cut :664-671` takes `pfRunST → MRun → SimRel →`,
  `fi :672-680` takes `pfRunST` only ✓; the single `fi` application is `:1035` (`hH.fi st c hrun cpu o k …`) and `:1043`
  passes `hrun hreach hR0` to `cut` ✓ — `hreach`/`hR0` are `simNode`'s premises (`:881`, `:896`) ✓.  `m1Hyps.fi` is
  `SrvwmoXv6Adequacy.lean:213` (`fiOfSco hsco _ σ0`); with the widened shape the binder order `st c t g n κ, pfRunST →
  MRun → SimRel → ∀ cpu …` makes the plan's `fun st c _ _ _ _ hrun _ _ => fiOfSco hsco _ σ0 st c hrun` correct (`fiOfSco
  :163-171` returns the `∀ cpu o k …` tail) ✓.  `cutOfPristine :2907-2975`: `hR.mem.2.2.1.1 :2942`, `histNoWrite :2882`,
  `winPristine :2878`, the `t = 0` step `:2948-2956` ✓; `candKfetch` `PfRunShape.lean:53-55` addresses only ✓; the pf
  fetch `WeakEvInst.lean:631` (`ifetchOk (imgZ σ.wgimg) σ.wglog (σ.wgitv c)`) ✓; `ifetchOk` `WeakPromise.lean:226-228`
  (`ifetchByteOk :220-222`: `logByte … t a = some v ∧ ¬ writesIn log a t (max t itv)`) ✓; `wbootFacts.2.1` `WeakLang.lean:
  483` (`wgimg = bootImage`) ✓.  The W-SCO Shape (0)–(iv), landing order, [R28.s2]/[R28.s3] text ✓.  `UCycleDefs.lean:11-17`
  (`uc_runHartActive_eq`: `ucDispatch >>= … fetch () >>= ucAfterFetch`) ✓.  `AxSpinTextCerts.lean` 245 lines ✓;
  `bcRoLo = ramBase`, `bcRoHi = _data` (`BootCarve.lean:143-144`) ✓.
- **[R28.3] applied** (`:1353-1359`, `:2244-2247`, `:2287-2292`).  CLOSE-OUT (5)'s deviation-(4) wording names
  `sailCycleOrderK_holds`; W-SCO "does NOT edit `PfStepTsoView.lean`'s header" ✓; the header's deviation (4) today is
  `PfStepTsoView.lean:64-66` ("both facts of the step list's instruction structure, W4's to supply") ✓; registration is
  W-SCO's CLOSE step ✓.
- **[R28.4] applied as R28 wrote it** (`:751-761`, `:2548-2557`): `fok` 5-ary at `PfRunShape.lean:242` (`execProgOk'S`),
  `:265-269` (`pfStepFacts`), `TsoShadow.lean:555-590`, `MachOfPf.lean:658`, `sailCycleOrder :114`,
  `srvwmoXv6M1Premises` (`SrvwmoXv6Witness.lean:599-607`), `srvwmoXv6M1Core :276-284` ✓; `rowFetchM2` is
  `PfStepTsoView.lean:778` (table row `:41`) ✓; `fetchesOk` `PfRunShape.lean:232-234` ✓; `pfLoadFactsT`/`pfStepFactsT`
  `TsoShadow.lean:568-577` ✓.  **But the route itself does not hold — [R29.1].**
- **[R28.5] applied** (`:2516-2533`, order sites `:17`, `:60`, `:1359-1361`, `:2304-2305`, `:2331-2333`, `:3148-3149`,
  `:3208`, `:3296-3297`, D26 `:4127`).  The guard sites: `notOthers :744-746` ✓, `hno :757,790` ✓, `hres :1513,1590,1741,
  1848` ✓ (13 with the `:768,774,801,807` uses); `PfStepTsoMem.lean` 15, `PfStepTsoView.lean` **5** (R28 said 6; the plan
  says "rows (grep)" — fine), `PfStepTso.lean` 2 ✓; `hartStep`'s `.pure` arm `Lang.lean:535` (`σ' = σ`) ✓; `memModelAt`
  `Resources.lean:950-956`, the `resvMap σ` conjunct `:955` ✓; the ≈ 8 files named are 8 ✓ (β′'s edits themselves live in
  w2's workspace and cannot be checked here).  Q-RSV-order's §D entry keeps its "*Spec (FIRST).*" line (`:3299`) ✓.
- **W-SCO's `fetchIsImage` for a PAST fetch** — the ingredients exist: `pfRunSTFacts` (`TsoShadow.lean:599-620`)
  recovers, for every `st = st0 ++ (i, l) :: rest`, the step's `wpPfStep … c1 c2` and `pfStepFactsT` at the prefix;
  `wpPfStepLogK :839`/`pfRunSLogK :845` give log append-only under a CONSTANT class function (`hk`) — `pclsEv` is not
  constant (`pclsEvEqr`, `WeakEvCapstone.lean:1090`), so a `pclsEv` prefix lemma is S new work ([R29.s1]).

## REQUIRED changes

- **[R29.1] W5d's carrier for the M2 cut clause, as pinned by [R28.4], cannot be executed: `Hyps.cut` never sees the
  shadow-threaded clause, and the two shared definitions it changes are the ones the REGISTERED M1 is proved over.  Pin
  a trivially-instantiated PARAMETER instead, and record that M1's statement TEXT (not its content, name, axioms or
  opaques) changes.**
  *What is wrong (evidence).*  (1) `:2554-2555` "`Hyps.cut` at `fok_cut` is discharged from `pfStepFactsT`'s two
  conjuncts (no MachCSL side needed)".  `Hyps.cut`'s premises (`MachOfPf.lean:664-671`) are `pfRunST … c0 st c`, `MRun`,
  `SimRel`, `wpPfStep … (.LIFetch base tvs) c c'` and **`pfStepFacts fok c …`** — the UN-threaded facts of the step.  The
  conclusion needs `(tsoShadow cohSrc st (hartAgent cpu)).itv ≤ q` for the SAME `q` as `ifetchOk`; from `fok_cut`
  (`∃ q ≤ |log|, ifetchOk q ∧ ∀ byte t ≤ q`) alone it is not derivable, and it cannot be repaired by taking `max q itv`:
  `ifetchByteOk … itv' a t v := … ∧ ¬ writesIn log a t (max t itv')` (`WeakPromise.lean:220-222`) is STRONGER at a larger
  `itv'`.  The step's `pfLoadFactsT` IS in hand at the only application site (`simNode`'s `hfT :886`, not passed at
  `:1043`), so `Hyps.cut` must gain that premise — an edit to `MachOfPf.Hyps`, `cutOfPristine :2907-2920` and `m1Hyps.cut`
  (`SrvwmoXv6Adequacy.lean:211-212`): the file the W5d brief says is "untouched" (`:2546`).  (2) `:757-758`/`:2550-2551` "a
  new clause beside `pfLoadFactsT` in `pfStepFactsT` for `.LIFetch`".  `pfLoadFactsT`'s fetch arm is `| _ => True`
  (`TsoShadow.lean:568-573`); **every fetch of the M1 run enters `pfRunST` through `pfRunSTApp :622-632`, whose load facts
  are discharged by `pfLoadFactsTNonload :581-583`** (`cases l <;> simp_all [lbIsLoad, pfLoadFactsT]`) — the realizing
  label of a step is never `LIFetch` (`:739-741` closes that case by `simp [projLbl] at hpr'`, a contradiction), fetches are
  admin-star labels.  Any non-trivial `.LIFetch` arm makes `pfLoadFactsTNonload` FALSE for `LIFetch` and
  `execWfPfRunPinShapedT :808` (W5-pre's construction, hence `srvwmoXv6M1PfRun` `SrvwmoXv6Witness.lean:624-640`)
  unprovable unless the arm is proved PF-SIDE for `candKfetch` runs — and no `itv`-aware fetch clause is pf-side provable
  for M1: "no log write hits the fetched bytes below `itv`" is the SC tree's `textPristine`, which reaches the pf side only
  through `SimRel` (exactly [R28.2]'s finding, `:2265-2266`).  (3) `:756`/`:2552` "`itvOf k i ≤ q` is a conjunct of
  `execProgOk'S`'s per-index clause".  `execProgOk'S` (`PfRunShape.lean:242-262`) is M1's premise through `execProgOk'ST`
  (`srvwmoXv6M1Premises :599-607`); a new conjunct STRENGTHENS M1's premise (its meaning changes though its text does not)
  and `srvwmoXv6M1Satisfiable :733` — whose witness run has TWO fetches (`hf base tvs hm`, `kfetch4`, `:751-756`) — plus
  `execProgOk'SNil :272`/`execProgOk'SSnoc :280` must be re-proved.  So as briefed the W5d worker reaches a three-way
  design fork on day one (widen `Hyps.cut` and edit the "untouched" file; or make the arm M1-provable, which is
  impossible pf-side; or change M1's premise meaning silently) — a stall, on an L item, in a lane that shares `Hyps` with
  W-SCO's first commit.  [R28.4]'s goal (keep `candKfetch`'s type, M1's registered ENTRY and W-SCO's `sailCycleOrderK`
  stable) is right; its means ("text-identical, `SrvwmoXv6Adequacy.lean` untouched") is not attainable: the M2 clause
  needs a carrier that M1 instantiates TRIVIALLY, and in Lean that is a parameter.
  *Exact change (`:751-761` §B(4)(iii); `:2536-2557` §C W5d; `:1353-1359` §C top; `:2287-2288` W-SCO landing order).*
  Replace the [R28.4] text by: "**[R29.1] The M2 cut clause is carried by ONE new parameter `fcutT : Nat → Image → List
  Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop`** (the shadow's `itv` first; `fok` stays 5-ary and keeps its role as the
  un-threaded fetch clause): `pfRunST.snoc` gains a THIRD fact `pfCutFactsT fcutT stamp st c i l := ∀ base tvs, l = .LIFetch
  base tvs → fcutT (tsoShadow stamp st i).itv c.pcImg c.pcLog i base tvs` beside `pfStepFacts`/`pfLoadFactsT`
  (`TsoShadow.lean:584-590`), `execProgOk'ST` gains the Exec-level twin with `itvOf k i` in the per-index clause where `ls`
  is in scope (`PfRunShape.lean:232-234`, `:242-262`), and `MachOfPf.Hyps` is parametrised by `fcutT` with `cut` receiving
  `pfCutFactsT fcutT cohSrc st c (hartAgent cpu) (.LIFetch base tvs)` (`simNode :886` already holds the step's threaded
  facts; pass at `:1043`).  **M1 instantiates `fcutT := fun _ _ _ _ _ _ => True`**: `pfLoadFactsTNonload`, `pfRunSTApp`,
  `execWfPfRunPinShapedT`, `srvwmoXv6M1PfRun`, `srvwmoXv6M1Satisfiable`, `cutOfPristine`, `machRunOfPfRun`/`contR`
  (`MachOfPf.lean:515,2854`; the induction ignores the fact), `sailCycleOrder :113` (quantifies `∀ fcutT` as it does `∀
  fok`) and `srvwmoXv6M1Core`'s statement gain the trivial instance — **M1's statement TEXT changes, its content, name,
  `axioms` and `opaques` entry do not** (the W5 CLOSE-OUT's `baseline-weak.json` entry and gloss stand; one `Xv6`-free
  `Weak` rebuild).  M2: `fcutT itv img log i base tvs := ∃ q, itv ≤ q ∧ q ≤ |log| ∧ ifetchOk img log q base tvs ∧ ∀ byte
  t ≤ q`, `fok := fun _ _ _ _ _ => True` or `fok_cut` (the worker's choice; `Hyps.cut` at M2 is then the step's
  `pfCutFactsT` verbatim — the M2 twin of `cutOfPristine`, no MachCSL side).  **Files W5d edits beyond its new file**:
  `PfRunShape.lean`, `TsoShadow.lean`, `MachOfPf.lean` (the parameter, `Hyps.cut`, `cutOfPristine`, the induction),
  `SrvwmoXv6Witness.lean` (`:272,280,599-607,624,733`), `SrvwmoXv6Adequacy.lean` (`sailCycleOrder :113`, `m1Hyps :203-213`,
  `srvwmoXv6M1Core :276-284` — trivial instances), `PfStepTso.lean`/`PfStepTsoView.lean` only if `proposedStmt`
  (`PfStepTso.lean:102-124`) is re-pointed (it need not be: its clause (3) `:115-118` already states the cut conclusion as
  a hypothesis).  **Landing order (replaces `:2287-2288`, `:1357-1359`)**: W-SCO's `Hyps.fi` widening lands FIRST (S,
  ready); **W5d's parameter threading is W5d's FIRST commit** (S–M, ≈ 150–300 lines of signatures and trivial instances),
  rebased on it, and lands BEFORE W-SCO's `sailCycleOrderK`/`srvwmoXv6M1` are stated (W-SCO states them over the
  parametrised `pfRunST` at M1's trivial instance; if W5d's commit is late, W-SCO states them over the current type and
  W5d adapts them — S either way); the W5 CLOSE-OUT is unaffected (registration by NAME).  `:761` "M1's `candKfetch` is
  unaffected" stays true."  Delete `:2546` "`SrvwmoXv6Adequacy.lean` untouched" and `:2548-2549` "M1 text-identical"; keep
  "the M2 premise set a NEW definition `srvwmoXv6M2Premises`".  S text on an L item; FAITHFUL (proof organisation; the
  published quantifier, the trusted base and every conclusion unchanged; RVWMO/Sail/Zifencei/PMAs silent).

- **[R29.2] One lane-order sentence in §C's serial-items paragraph still states the superseded order; [R28.5] required
  every site.**
  *What is wrong (evidence).*  `:2337-2339`: "Order: **W-COH first — DONE** …, **W-DMA0 — DONE** …, **W8-β′** next, then
  **W8 (f2-ctx)** [OWN.37], **W-RSV last** (L–XL [R12.1]; waits for M1 per D26 and for W8 (f2-ctx) by file overlap)".  This
  is present-tense text inside the same paragraph that six lines earlier (`:2331-2333`) records [OWN.41]'s W8-β′ → W-RSV →
  W8 (f2-ctx); the W-RSV worker reading §C top-to-bottom meets both.  (The rev-28 RECORD block `:1448-1451` is labelled
  historical and is fine.)
  *Exact change (`:2338-2339`).*  "**W8-β′** (RUNNING), then **W-RSV** (when β′ merges; M1 ✓ per D26), then **W8 (f2-ctx)**
  rebasing on W-RSV — [OWN.41][R28.5]; [OWN.37]'s earlier order superseded".  S text; FAITHFUL (lane order only).

## SUGGESTIONS

- **[R29.s1] (W-SCO) `fetchIsImage` is about a PAST step; give the two-lemma recipe.**  `cutOfPristine`'s `hnw`/`ht0`
  argument (`MachOfPf.lean:2922-2956`) is at the CURRENT step's pre-configuration; W-SCO needs it for the latest own
  `LIFetch base tvs` INSIDE `st` at a later node.  Recipe: (a) `pfRunSTFacts` (`TsoShadow.lean:599-620`) on `st = st0 ++
  (hartAgent cpu, .LIFetch base tvs) :: rest` gives `c1`, the fetch's `wpPfStep` (hence `ifetchOk c1.pcImg c1.pcLog _ base
  tvs`, the `PFIFetch` arm) at the prefix; (b) a `pclsEv` log lemma "`pfRunST pstepEv pclsEv … c1 st' c → c1.pcLog <+:
  c.pcLog ∧ c1.pcImg = c.pcImg`" (S; `pfRunSLogK :845` needs a constant class function, which `pclsEv` is not — induct on
  `wpPfStep` directly, or read it off `SimRel.auth`/`stAuthors`); then `hnw` at the final `c` (via `SimRel.mem` +
  `winPristine`) transfers to the prefix log and `ht0` gives `t = 0` for every byte, so `tvs`'s bytes are `logByte img _ 0`
  = the image's.  State `fetchIsImage` once over "a fetch label at any position of `st`" so `cutOfPristine` is its
  `rest = []` instance.
- **[R29.s2] (W-SCO) Say which `SailM` state the barrier-clause invariant is over.**  The per-word lemma gives "`execute
  (decode w)` emits no fetch before its `Barrier_RISCV_i`"; the node holds `.impure (.ok (.barrier .Barrier_RISCV_i)) k`
  (`Hyps.fi`'s shape) — the invariant that connects them is "the hart's agent state is a residual of `ucAfterFetch` on the
  word of the latest own `LIFetch` in `st`, with no fetch since the announce" along `pfRunST`.  Naming it in the brief
  (it is the recorded risk) lets the worker state it before proving the per-class lemmas.
- **[R29.s3] (W5 CLOSE-OUT) Two of the comment sites are stale TODAY**, not just after the CLOSE-OUT: `baseline-weak.json:
  2-6` and `Audit.lean:91-92` still say `Weak.AxSpinT2b,Weak.AxSpinT2c` while `audit.sh:44` lists eight modules.  The
  worker should write the list ONCE (e.g. "the modules of `audit.sh:44`") rather than enumerate it in four places.
- **[R29.s4] Cosmetic cites.**  `:2527` "`PfStepTsoView.lean`'s rows" — 5 guard mentions, not R28's 6; `:2573`
  (`promiseFreeCompleteClean`) and `:2566` (`hemitf`/`HFone`) were fixed per [R28.s6] — confirm the (I) brief's `:1445`/
  `:253-259` landed (not re-read here, W13 (I) is running).
- **[R29.s5] (W5d) With [R29.1], `rowFetchM2`'s `hq` (`PfStepTsoView.lean:780`) is supplied by `pfCutFactsT`'s witness
  directly;** say so where the brief says "consumed through `Hyps.cut` at the cut form" (`:2547`), so the worker does not
  look for a MachCSL-side source.

## Owner questions the plan is missing

None.  [R29.1] and [R29.2] are proof organisation and record-keeping (where a clause is carried; which lane order a
sentence states).  *Spec (FIRST).*  RVWMO, riscv.cat, the Sail model in this tree (`vendor/lean-sail`,
`model/Lean_RV64D`), Zifencei and the PMAs say nothing about how a premise is threaded through a Lean inductive or in
which order two workers edit a structure; every option above is FAITHFUL — the published quantifier, the trusted base
(`sailCycleOrder` stays the one named ISA-model premise until W-SCO demotes it for kernel text; `gzFetch`/`ioResidueGmo`
unchanged) and the conclusions do not move.  The plan's existing questions keep their "*Spec (FIRST).*" lines and the
2026-10-10 format (Q-RSV-order `:3296-3300` RULED, Q-R1/Q-R2/W4-F9-wrap unchanged since R28).
