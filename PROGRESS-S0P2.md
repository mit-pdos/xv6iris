# PROGRESS — S0-P part (2): machine v2 over the litmus corpus (label level); milestone 2 (certification)

## m2b (S0P2c, 2026-11-02) — explorer completeness

**COUNTEREXAMPLE to statement 5 as stated (`sigmaAll_complete`: "`ownMsgs h cfg.pcLog ∈ sig[h]`").**  `sig[h]`
holds each hart's message lists in PROGRAM order (`FH.msgs` appends in po), but a hart may fulfil its stores out of
timestamp order, so its own messages in LOG order need not be a member.  Example: one hart `sw 1,(x); sw 1,(y)`;
the valid run `prom y; prom x; st sw-x (ts 2); st sw-y (ts 1)` (both EXT premises `0 < ts`, `coh = 0 < ts` hold)
has log `[y:=1, x:=1]`, so `ownMsgs 0 = [y, x]`, while `sig[0] = [[x, y]]`.  The EXPLORER is not affected (it
`arrange`s the po-order lists, and `arrange` reorders non-overlapping messages), only the statement: the correct
form is "the hart's FULFILLED messages in program order are a member of `sig[h]`, and the log is a permutation of
their concatenation" (statement 6 must then take the po-order lists).  The m2b checker below is built on that form.

**SECOND COUNTEREXAMPLE to statement 5 (the free runs' alignment check).**  `FH`'s `stepF` (and RefProg/`litNext`)
drop a run at a misaligned access.  Every access except a FAILING SC has its address view captured by `vcap`
(rule 13), hence below the EXT bound of any later message; a failing SC (`LExFail`, no view effect) does not, so a
free run over the domain may stop at an SC whose address the valid run computes from a not-yet-justified value.
Example (init `x = 1`, `y = 0`): H0 `lw r1,0(x); sc.w r2,r3,0(r1); sw r5(=1),0(y)` ‖ H1 `lw r,0(y); xori r,r,1;
sw r,0(x)`.  Valid run: `prom y:=1 (H0); prom x:=0 (H1)`; H1 reads `y = 1` (ts 1), writes `x := 0` (ts 2);
H0 reads `x = 0` (ts 2), its SC fails at the ALIGNED address 0, `sw y` fulfils ts 1 (`stPre = 0`).  The closure:
`D(y) = {0}` ⇒ H1's messages `x := 1` ⇒ `D(x) = {1}` ⇒ every free run of H0 stops at the SC (address 1) ⇒
`sig[0] = []`: the milestone-1 explorer reports NO outcome for this test while the machine has one (STRONGER,
explorer-only; no corpus test has a dependent SC address, so no corpus result changes).  The m2b checker's free runs
(`litNextF`) skip the failing SC's alignment check (`scNextF`), which makes NOTA provable.

Green increments (m2b):
- `Weak/Prom/MachWf.lean` — [R7.s1] invariant: `memStep_bnd` (every arm keeps `psBounded ws |log|` and
  `promWf`), `pmStep_wf`/`pmSteps_wf` (`runWf` = `cfgWf` + every log message non-trivial with an existing author),
  `pmSteps_prefix` (append-only log), `pmSteps_len`.  PROVED.
- `Weak/Prom/MachFactor.lean` — **statement 1 PROVED** for machine v2, any `pstep`, any fabric `D`, no premise:
  `validRun_factorL : validRun pstep img d0 ps evs cfg → validRun pstep img d0 ps (cfg.pcLog.map promEv ++
  evs.filter PEvt.isSt) cfg` and `validRun_factorL_trace` (+ `∀ h, traceOf h evs' = traceOf h evs`).  Core:
  `memStep_extend` (every arm append-stable and own-promise-monotone, from `psBounded`).  Axioms: propext,
  Classical.choice, Quot.sound.
- `Weak/Prom/MachSolo.lean` — **statement 2 (the direction used) PROVED**: `sep` (a run of state events projects
  to each hart's `soloSteps` against the fixed log), `validRun_statePhase`, `validRun_solo` (every valid run gives,
  for every hart, a solo run against the final log from `(ps[h], psInit, own messages)` to its final agent, with
  trace `traceOf h evs`); `memStep_prom`, `solo_fulfil` (a promise gone at the end was fulfilled by a step).
- `Weak/Prom/MachComplete.lean` — **statements 3–4 PROVED for the new per-hart explorer**: `memStepF_complete`
  (`memStepF` is exact, with milestone 2's `memStepF_sound`), `invalReadB_complete`, `loadOkB_complete`;
  `insLabs`/`labCands` (every first label, answers from `ansRuns`: per byte every timestamp `0 … |M|` holding it),
  `labCands_complete`; `soloDFS` + `soloDFS_complete` (no fuel-out ⇒ every solo run's final state is listed).
- `Weak/Prom/MachNota.lean` + `Weak/Prom/MachNI.lean` — **statement 5 (corrected) PROVED, `nota`**: with a domain
  `D` that holds the image and is CLOSED for every hart (`closedFrom`: every message of every free run
  `freeSteps D` over `litNextF` has its bytes in `D`), every byte of the final memory is in `D`.  Proof: strong
  induction on the message's timestamp `θ`; the noninterference simulation `ni_step`/`ni_run` (a free run copies
  every LOW load — result view `< θ` — and answers every HIGH load from `D`; `agree` = equal on every register whose
  syntactic view is `< θ`; `fwdInv` for forwarding; all addresses and branches are low because `vcap ≤ stPre < θ`)
  and `ni_final` (the fulfilling step is a free step with the SAME label).
- `Weak/Prom/MachFree.lean` — `freeDFS` (free runs over `D`, canonical answers) + `freeDFS_complete`;
  `perms` + `perms_complete`; `choicesG` + `choicesG_complete`; `perm_owner` (statement 6, corrected: the final log
  is a PERMUTATION of the concatenation of the harts' fulfilled-message lists; no `arrange` pruning is used).
- `Weak/Prom/MachForbid.lean` — **the checker and its soundness, PROVED**:
  `forbidMachB_sound (T) (K) : forbidMachB T K = true → ¬ allowedMach T`.  `forbidMachB`: untrusted domain
  iteration (`domIter`, K rounds), closedness + fuel check of every hart's `freeDFS`, then for every choice of
  complete free-run message lists and every permutation `M` of their concatenation, every hart's `soloDFS` against
  `M` (fuel checked) and no combination of finished final states satisfies the condition.  Proof composes
  statements 1, 2, 3–4, 5 (`nota`), 6 (`perm_owner`, every message fulfilled once by its author: `solo_fulfils`).
- `Weak/Prom/MachForbidden{,2,3}.lean` — **46 kernel-checked theorems** `mach_<test>_forbidden : ¬ allowedMach
  Lit.<test>` (`forbidMachB_sound _ 6 (by decide +kernel)`): lbdd (row 2), lbDatas (row 3, LB+fakedep), lbCtrls,
  lbCtrlsBeq, lbLrsc, oota42, mpFF, mpFFrr, mpFAddr, mpAmoRlAq, mpFAmo, amoStorePart, sbFF, datarfi, addrpo, addrpoR,
  w22F, coWW, coWR0, coWR, coRW1, coRW2, coRR, coRR2, isa2F, wrcF, iriwF, mix26a, mix26b, mix26c, mix26dNot,
  mix26h, mix26i, mpAmoData, mpAmoCtrl, mixSca, lrScSc, wsub, armWeak, lbAcq, lbRel, coh, seqT, lbfd, disjLists,
  ramAq.  Build: 41 s / 106 s / 143 s (three files in parallel; ≈ 20 GB peak).  Axioms: propext, Classical.choice,
  Quot.sound.  No sorry/axiom/native_decide.
- `rng` (row 60) and `parInc` (row 23): no closed domain exists (`x := y + 1`, `amoadd` grow values), so
  `forbidMachB` returns false for them.  SOLVED by the DEPTH form: `nota_depth` (MachNI.lean; a chain
  `Ds 0 ⊆ Ds 1 ⊆ …` holding the image with every free run over `Ds j` closing into `Ds (j+1)` for `j < N` puts the
  byte at timestamp `t ≤ N` in `Ds t`), `valid_msgs_le` (a valid run has at most `Σ |prog|` messages: each
  instruction emits at most one, `litNext_pc`/`solo_msgcount`), and `forbidChainB` + `forbidChainB_sound`.  This
  needed FREE RUNS WITH OWN-STORE FORWARDING (`freeOk D w l`: a load answer is a domain byte OR the run's own latest
  byte there, `lastByte w a`; `freeSteps` carries the emitted messages `w`): a low load may forward from an own store
  fulfilled LATER than `t`, whose bytes are only in `Ds (t+1)`.  With forwarding in the free runs the simulation no
  longer needs closedness at all (`ni_step` lost its closure premise).  `MachForbidden4.lean`:
  `mach_rng_forbidden`, `mach_parInc_forbidden` (`forbidChainB_sound _ (by decide +kernel)`, 38 s).
- ALL 48 FORBIDDEN rows of RefLitmus*.lean now have `mach_<test>_forbidden` (46 closed-domain + 2 chain).

Worker: Opus (S0P2, S0P2b), 2026-11-02. Workspace `/home/bsdinis/dev/xv6iris-pcsl2`. Plan of record rev 7 (§1A, §8 S0-P).

## LATEST (S0P2b part A, 2026-11-02): D3 FIXED; corpus re-run

- `machine-cap8-D3.txt` (cap 8, machine + reference + fresh herd logs): 7869 compared, **machine = reference on all
  7869** (Never/Sometimes/Always verdicts all agree; `HAND/LR-SC-NOT-FENCE` now eq).  Machine vs herd: 7863 eq,
  3 herd-has-more = the 3 known appendix-bug tests (`LR-SC-diff-loc3`, `LR-SC-diff-loc4`, `PPOLDSTLD02`), 3 `na`
  (herd timeouts, `ATOMICS/CO/2+2W+…sxx…`).  19 parse-out-of-scope, 19 over the cap (as before).  4 min 36 s wall.
- `machine-cap99-noref-D3.txt` (machine vs herd, no cap): 7888 parsed, 7876 eq, 9 `na` (herd timeouts), the same 3
  appendix-bug tests; 189 CPU-s machine.
- No new disagreement.

## LATEST (S0P2b part B, 2026-11-02): MILESTONE 2 (certification) GREEN

- `Weak/Prom/MachSound.lean` — Bool↔Prop lemmas (`writesInB_iff`, `writesInOtherB_iff`, `exclOkB_iff`,
  `cmoAtB_iff`, `invalReadB_sound`, `bytesAllB_sound`, `loadOkB_sound`, `cohBelowB_iff`, `promHas_iff` =
  `ExtTreeSet.contains_iff_mem`, `writeTs_mem`) and
  `explorerStep_sound : s ∈ succ img log i prom ws t → memStep img log i prom ws s.l s.ots s.ws s.prom` (PROVED, every
  template); `memStepF` (the memory half as a function of the full label + fulfil timestamp) and
  `memStepF_sound : memStepF … l ots = some (ws', prom') → memStep … l ots ws' prom'` (PROVED, every label).
- `Weak/Prom/MachCert.lean` — the litmus PROGRAM HALF `litStep` (= `litNext s l = some s'`: RefProg's ISA, each
  instruction's label sequence of MachLitmus's table, first label with the answers, the rest queued in `LP.q`);
  `allowedMach T := ∃ evs cfg, validRun litStep (testImg T) () (progs T) evs cfg ∧ allDone cfg ∧
  T.cond.eval (regOf cfg) (memOf T cfg) = true`; checker `certOk T evs` (replays `evs` with `stepF` = `pmStep` as a
  function: promise arm, or `litNext` + `memStepF`; then `noPromB`, `doneB`, the condition);
  `certOk_sound : certOk T evs = true → allowedMach T` (PROVED via `stepF_sound`, `runF_sound`). `PLabel` gets a
  standalone `deriving instance DecidableEq` there (Machine.lean untouched for it).
- `Weak/Prom/MachLitmus.lean` — `MH.tr` records each hart's trace (label, fulfil ts) in the DFS; outcome sets
  unchanged (`machine-cap99-noref-M2.txt` = `…-D3.txt` line for line).
- `Weak/Prom/MachCertGen.lean` — generator (`lake env lean --run Weak/Prom/MachCertGen.lean > Weak/Prom/MachCerts.lean`,
  0.7 s): per row, the first explorer run (all harts done) satisfying the condition, printed as
  `[.prom … (M in order)] ++ per-hart .st events`; it also evaluates `certOk` (all passed).
- `Weak/Prom/MachCerts.lean` (GENERATED, 77 theorems, each `certOk_sound _ cert (by decide +kernel)`):
  ALLOWED rows (29): `mach_lb, mach_mp, mach_sbT, mach_sbFwd, mach_ppoca, mach_datacoirfi, mach_datacoirfiR,
  mach_frirfi, mach_rsw, mach_w22, mach_isa2, mach_wrc, mach_iriwCtrlFi, mach_iriw, mach_mix26d, mach_mix26e,
  mach_mix26f, mach_mix26g, mach_lbAmoPo, mach_lbAmoAd, mach_lrsc, mach_lrldsc, mach_lrsdsc_a … _d, mach_lrAmoSc,
  mach_lbMisa, mach_updStuck` (every ALLOWED `ref_*` of RefLitmus*.lean); FORBIDDEN rows (48): `mach_<test>_exec :
  allowedMach (anyOutcome <test>)` (the machine has a complete valid run: forbidden verdicts are not vacuous).
- `#print axioms` (`mach_lb`, `mach_lrsdsc_d`, `explorerStep_sound`, `certOk_sound`): `[propext, Classical.choice,
  Quot.sound]` only.  No sorry/axiom/native_decide.  Lint: only the expected drift findings (Weak/Prom/* not under
  a root, by rule).

### Milestone 2b — explorer COMPLETENESS (statements, not proved)

Notation: `T` a litmus test, `img := testImg T`, `ps := progs T`, `pstep := litStep`.
1. `PF.validRun_factorL`: `validRun pstep img () ps evs cfg → validRun pstep img () ps
   ((cfg.pcLog.map (fun m => PEvt.prom (m.tid.getD 0) m)) ++ evs.filter PEvt.isSt) cfg` (promises first in log
   order, state events in their order; append-stability + own-promise-monotonicity of every arm).
2. HART SEPARATION: after all promises, `pmSteps pstep c0 sts cfg ↔ ∀ h, pmSteps pstep c0 (sts.filter (·.tid = h))
   (c0.update h (cfg.pcAgs[h]))` (memStep reads only the log and the hart's own state; harts commute).
3. `succ_complete`: `memStep img log i prom ws l ots ws' prom' → ∀ t, Tmpl.Inst t l →
   ∃ s ∈ succ img log i prom ws t, s.l = l ∧ s.ots = ots ∧ s.ws = ws' ∧ s.prom = prom'` (`Tmpl.Inst t l`: `l`
   instantiates `t`), with `readCands_complete : loadOk img log ws vpre base tvs → tvs.length = sz →
   tvs ∈ readCands img log ws vpre base sz` and `writeTs_complete` (every fulfilled `ts ≤ |log|`).
4. `runM_complete`: every solo run of hart `i` (`litStep` × `memStep` against `M`, from `mhInit T M i`, done, no
   outstanding promise) has its final registers in `(hartRuns T M i).fin` (with `runM`'s fuel `|prog| + 1`:
   forward-only programs).
5. NOTA / `sigmaAll_complete`: `validRun … cfg → sigmaAll T b = some (sig, _) → ∀ h, ownMsgs h cfg.pcLog ∈ sig[h]`
   (a message's address/data/existence depend only on answers below its EXT bound, so value chains have ≤ K
   messages).
6. `arrange_complete`: the final log of every valid run is in `arrange (n + 1) ch` for `ch = (ownMsgs h M)_h`
   (own overlapping messages in program order: `cohBelow` + `coh` monotone).
Composed: `machOutcomes T obs = {o | ∃ evs cfg, validRun … ∧ allDone cfg ∧ outcome cfg = o}` (⊆ by milestone 2's
soundness applied to each enumerated run, ⊇ by 1–6).
**m2b status (S0P2c):** 1 PROVED (`validRun_factorL`); 2 PROVED in the direction used (`validRun_solo`); 3–4 PROVED
for the m2b checker's explorer (`memStepF_complete`, `labCands_complete`, `soloDFS_complete`; the brute-force
answer generator `ansRuns` replaces `readCands`, so `readCands_complete` itself was not needed); 5 FALSE as stated
(two counterexamples at the top), PROVED in corrected form (`nota`, `nota_depth`, over `litNextF` free runs with
own-store forwarding); 6 PROVED in corrected form (`valid_perm`: permutation, no `arrange` pruning).  The
milestone-1 `sigmaAll`/`arrange`/`runM` explorer itself is not proved complete (and is incomplete on the second
counterexample's program class).

## Defects of machine v2 found by the corpus (each with its fix status)

**S0P2-F1 — FIXED. Acquire load forwarded from an own plain store got view `t` (STRONGER, K1M class).**
- Where: `Weak/Prom/Machine.lean` `fwdView` (was `if aq then t else …`, ~line 267).
- Found by: 116 tests, all `MR=STRONGER MH=STRONGER` (`RELAX/PosWRPAq` 69, `RELAX/Rfi` 23, `RELAX/PosWR` 15,
  `SAFE/*[ws-rf]paq*` 6, `ATOMICS/SAFE_PosWRXAq` 3). Example `RELAX/PosWRPAq/SB+pospaq-addraqps`:
  `sw x5,0(x6); lw.aq x7,0(x6); xor; add; lw x9,0(x11)` ‖ symmetric, `exists (0:x9=0 /\ 1:x9=0)`: reference and herd
  Sometimes, machine Never.
- Spec: no RVWMO ppo rule orders a po-earlier PLAIN store before an acquire load that reads it (rule 5,
  rvwmo.adoc:287 "a has an acquire annotation", orders the acquire before LATER operations; rule 7 needs both RCsc,
  and a release store is already under `ldPre`'s `wVRel`); the load value axiom lets the load return "Stores that
  write that byte and that precede i in program order". PARM `FwdItem.read_view` (papers/pulte/coq/Promising.v:528–531)
  gives the forward view except for an EXCLUSIVE write on RISC-V (v2's exclusive forward view is already `ts`, M1).
- Fix: a forwarded byte gets the forward view whatever `aq` (argument kept, unused). Mark after fix: FAITHFUL.
  After the fix all 116 agree with the reference and herd.

**S0P2-F2 — FIXED. Mismatched LR/SC: the SC could precede the store its LR read (WEAKER).**
- Where: `Weak/Prom/Machine.lean` `memStep.sc` (new premise `∀ t ∈ R.rvTs, t < ts`, ~line 578);
  `MachExplore.succ` `.sc` mirrors it.
- Found by: `HAND/LR-SC-diff-loc4` (`MR=WEAKER`; the machine agreed with herd's appendix cat, the known appendix bug):
  P1 `sw.rl x7,0(z); lr.w x9,0(z); sc.w x2,x1,0(x)`: the LR forwards from the own `sw.rl` at `tf`; the SC to `x`
  could take `ts < tf` (`exclOk`'s window `(tf, ts-1]` empty; the forward view is below `tf`), closing a cycle the
  reference forbids.
- Spec: Atomicity Axiom, rvwmo.adoc:330–334 "s is a store to byte x, and r returns a value written by s, then s must
  precede w in the global memory order". For matched pairs `cohBelow` already implied it. Mark after fix: FAITHFUL.

**S0P2-D3 — FIXED (S0P2b, coordinator decision under the fidelity rule). LR/SC and Zalasr second annotation dropped
(WEAKER).**
- Fix (2026-11-02), every item FAITHFUL, docstrings quote rvwmo.adoc:124–128 / unpriv_zalasr.adoc:68–69, 122–123:
  `LLoad aq rl`, `LExLoad aq rl`, `LStore aq rl`, `LExStore aq rl` (Machine.lean §7); `ldPre ws aq rl va` adds
  `vrOld ⊔ vwOld` for `rl` (rule 6); `loadRun`/`readView` take `rl`, and a release load raises `wVRel` to its
  post-view (rule 7 RCsc, the load as `a`); new `stPreA ws aq rl va vd = stPre ⊔ (aq ? wVRel)` (rule 7, the store as
  `b`) in the `store`/`sc` arms; new `acqPost ws aq ts` (rule 5: `vrNew/vwNew ⊔= ts`) on the `store`/`sc` posts.
  AMO read halves pass `rl = false` (the AMO's release is its write's, M0).  Front end: `lr` → `LExLoad aq (aq&&rl)`,
  `sc` → `LExStore (aq&&rl) rl`, `l*.aq[rl]` → `LLoad true rl`, `s*.[aq]rl` → `LStore aq true` (RefProg's own
  annotations).  Emit.lean: new `akStrong` (`AK_arch` = Sail's `aq && rl` LR/SC kinds, PhysMemInterface.lean:
  296–365, Mem.lean:222–255); `LExLoad (akAcq ak) (akStrong ak)`, `LExStore (akStrong ak) (akRel ak)`, plain
  `LLoad`/`LStore` likewise (Sail has no Zalasr kind, so plain accesses get `false`).  `MachExplore.succ` mirrors
  every arm.  Result: `LR-SC-NOT-FENCE` eq; no other test changed.
- Where: `PLabel.LExLoad`/`LLoad` have no release bit, `LExStore`/`LStore` no acquire bit (Machine.lean §7); Emit.lean
  passes only `akAcq ak` (ramRead/ramWrite). So `lr.aqrl` (release-RCsc), `sc.aqrl` (acquire-RCsc), `l*.aqrl`,
  `s*.aqrl` lose one annotation.
- Found by: `HAND/LR-SC-NOT-FENCE` (`lr.w.aq.rl; sc.w.aq.rl` between `sw a` and `lw b`, both harts,
  `exists (c=1 /\ d=1 /\ 0:x7=0 /\ 1:x7=0)`): reference and herd Never, machine Sometimes (SB through the pair).
- Spec: rvwmo.adoc:124–128 "An AMO, lr, or sc instruction with both aq and rl set has both acquire-RCsc and
  release-RCsc annotations"; rules 5/6 (rvwmo.adoc:287–288). Either missing bit alone lets the SB outcome through.
- Fix proposal (not applied): `LExLoad aq rl …` with `rl → ldPre ⊔ vrOld ⊔ vwOld` (rule 6) and the RCsc `wVRel`
  raise; `LExStore aq rl …` with the acquire post (`vrNew/vwNew ⊔= ts`, rule 5); same for Zalasr `LLoad`/`LStore`;
  Emit must pass both bits from the access kind. Touches the alphabet, two arms each, and Emit: reported, not done.

## Results (`~/dev/weak-orch/promising/litmus/`)

- `machine-cap8.txt` (final, after F1/F2; machine + reference outcome sets + herd States, ≤ 8 memory instructions):
  7907 files, 7869 compared, 19 parse-out-of-scope (same as S0P1), 19 over the cap.
  - machine vs reference (OUTCOME SETS, projected on herd's state keys ∪ condition keys): **7868 eq, 1 WEAKER**
    (D3). Verdicts: Never 4908, Sometimes 2950, Always 10 agree; 1 differs (D3).
  - machine vs herd (appendix cat + LrScDiffOk): 7862 eq, 3 herd-has-more (`LR-SC-diff-loc3`, `LR-SC-diff-loc4`,
    `PPOLDSTLD02` — the three known appendix-weaker tests, notes/riscv-model-bugs.md; machine = reference),
    1 machine-has-more (D3), 3 `na` (herd timed out: `ATOMICS/CO/2+2W+…sxx…`; machine Never = old herd logs).
- `machine-cap99-noref.txt` (machine vs herd, no cap): all 7888 parsed files; the 19 over-cap tests are compared
  too: all eq with herd or herd timed out (6 more `na`, machine Never). Same 4 disagreements.
- `machine-run1-prefix.txt` (before F1/F2): 116 STRONGER (F1), LR-SC-diff-loc4 WEAKER (F2), D3.
  `machine-run2-afterF1F2.txt`: intermediate (herd duplicate-name lookup not yet fixed: SF_THESIS/HAND/CoWR `na`).
- No test hit an explorer budget; no run was dropped as out of scope (no misaligned access); `varsOkB` held on every
  reference path; every closure reached its fixpoint at iteration 2.
- Time: machine 185–226 CPU-s for the whole corpus (interpreted, `lean --run`; 27 s wall on 80 shards);
  reference outcome sets 10 265 CPU-s (≈ 4 min wall on 80 shards).

## Done (green)

- `Weak/Prom/MachExplore.lean` — `Mach.succ img log i prom ws t`: every `memStep` whose label instantiates template
  `t`, as a plain function over v2's types with v2's own post-state functions; Bool transcriptions of every premise
  (`writesInB`, `exclOkB`, `invalReadB`, `loadOkB`, `cohBelowB`, `promHas`); complete read-candidate generator
  (`readCands`, argument in the header; candidates are filtered by `loadOkB`, so only completeness rests on it).
- `Weak/Prom/MachLitmus.lean` — label-level front end (table + Sail-gap list 1–8 in the header), explorer
  (promises-first normal form; per-hart message-list closure `sigmaAll`; arrangements `arrange`; per-hart DFS
  `hartRuns`; outcome product `outcomesM`).
- `Weak/Prom/MachOracle.lean` — driver `<repo> <herd.logs> <cap> <shard> <shards> [noref]`; reference outcome sets
  via RefCheck's enumerator (`refOutcomes`, every consistent candidate); herd `States` (k-th block of a name for the
  k-th file of that name, LC_ALL=C path order).
- Machine.lean: F1, F2 (above). Emit.lean rebuilds unchanged. Lint: only the expected drift findings.

## Explorer completeness (what milestone 1's exactness rests on; statements: milestone 2b above)

1. `PF.validRun_factorL` (promises-first normal form; append-stability + own-promise-monotonicity, Machine.lean
   header). 2. `succ` complete per template (MachExplore header). 3. NOTA: a message's address/data/existence depend
   only on answers below its EXT bound, so value chains have ≤ K messages and `sigmaAll`'s domain covers every valid
   run (the corpus reaches the fixpoint anyway, but a fixpoint alone does not exclude self-justifying values: NOTA
   does). 4. `arrange`'s pruning (own overlapping messages in program order) follows from `cohBelow` + `coh` monotone.

## Next

- Milestone 2: DONE (above).  Milestone 2b: the completeness statements 1–6 above.
- Milestone 3: the same corpus through `pstepV2` (Sail): fetch labels, split AMOs (`amoSplitFused`), decoder sources
  vs litmus operands, `match_reservation` both ways, parked FENCE.TSO half; and `litStep` vs Emit.lean's labels
  (gap list 1–8 in MachLitmus's header; item 8 closed by D3).

## Runner (was `litmus-appx/run.sh`; `litmus-appx/` = `model-results/herd.logs` (copy of
herdcheck/herd-appendix-lrscdiffok.logs) + `tests/` of litmus-tests-riscv 08728edc, created in the workspace for the
VM sync and deleted after the runs)

```sh
N=$1; X=$2; rm -rf /tmp/machor; mkdir -p /tmp/machor; k=0
while [ $k -lt $N ]; do
  (lake env lean --run Weak/Prom/MachOracle.lean litmus-appx litmus-appx/model-results/herd.logs ${CAP:-8} $k $N $X \
     > /tmp/machor/out-$k.txt 2>&1; echo "exit $?" >> /tmp/machor/out-$k.txt) &
  k=$((k+1)); done; wait
k=0; while [ $k -lt $N ]; do cat /tmp/machor/out-$k.txt; k=$((k+1)); done
```
