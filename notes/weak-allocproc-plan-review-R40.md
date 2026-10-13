VERDICT: NOT SATISFIED

# Review R40 of `notes/weak-allocproc-plan.md` (rev 43) — the second Stage 2 launch set, R39 applied

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git/jj, no subagents).  Scope per the R40
brief: rev 43 = rev 42 + R39 ([R39.1] D35-fix file list, [R39.2] disjointness vs (F-dep), [R39.3] W13 (R3′)'s fabric arm
over `gmem` members with `gfDevAnc` a named premise); launchability and order of **W13 (R3′), D35-fix, W13 (K), W11 (iv)c**
beside the RUNNING **W13 (F-dep)** (w3) and **W8 (f2-ctx)** (w2).  Every cite below was read at the working-copy tip of
`../xv6iris-weak`; the two running workspaces were compared by DIRECTORY diff (`diff -rq`, not jj) to see what they have
actually touched so far.

**Sign-off.**  NO — ONE required change, S plan text, on W13 (R3′): the item's `WeakRvwmoLin2` scope ("§8.3 only",
"LEAVES `fconfSupply'`/`fconfTraceRealizeIO`/`trDevOrderedOfPtraceIO`") contradicts its own acceptance (`gfDevAnc` a
premise of `fconfTraceRealizeIO`), and with `gfDevAnc` as written the lemma `devOrderOfPtraceExtIO :1233` is NOT provable
from `ptraceExtIO` as stated (its proof goes through `ptraceRelIO :1079`'s `gisWIo` arm).  The fix is one paragraph and
there is a strictly simpler option the plan's own evidence supports (keep `gfDevWIo`: on the actual disk program no
disk-row READ is ever a fabric member).  Not a redesign, not shrinking.  Everything else in the brief's focus is in order:
**D35-fix, W13 (K) [after (R3′)] and W11 (iv)c are launchable as written**; (R3′) is launchable after [R40.1].

## R39 application — VERIFIED

- **[R39.1]** in §C top D35-fix (plan `:2209-2263`): `grcscGrelAcq :250` DELETE (verified FALSE under `lbAq || lbRl`:
  `AxGraphCat.lean:245-255` proves it via `lbRcscBits`, which gives `lbIsW ∧ lbRl ∧ lbIsR ∧ lbAq` — two `LStore true`
  break it); `gppoCat6Gppo :257-264`'s sixth arm (`:264` is today `Or.inr (Or.inr (Or.inr (grcscGrelAcq _ _ _ h)))`);
  header `:35-43` + port map `:85`; `CatLinWit.lean:42` (`racyChk` uses `grelAcqB`; spec `racyChkOf :44`; `sbrfiAcyclic
  :124`); `CatLinHull.lean:94` `lblRenRcsc` + `hullGrcsc :123-126`; `WeakRvwmoNorm.lean:362-363` `lblRenAq`/`lblRenRl`;
  `WeakRvwmoAcyc.lean:510-519` `rowsRelGppo` unfolds `grelAcq` and rewrites with exactly those two; `Xchg.lean:743`
  `lblTswapRl`, `:895-902` `gswapwRelAcq`; `racy :197`/`racyD :200` carry `gppo` by name; `AxDeps.lean` has no
  rule-7/RCsc/RCpc/`grelAcq` mention (grep empty).  The grep `lbRcsc|grcsc|grelAcq` over `Weak/` is 14 files, as stated.
- **[R39.2]** in §C top (plan `:2255-2263`, `:2292-2299`) and §C (F-dep) (`:2393-2399`): `WeakRvwmoAdm.lean:690-696` is the
  positional `LDev kd ba bs` site, `:850` `mp2PpoGmo`'s `rcases h with hloc | hf | hacq | hrel`; `AxSpinSpike.lean:658`
  `cDw`, `:749` the Bool rule-7 twin; `CatLinChain.lean:331-338` `gdexecQconfTForget` uses `hartConfRowDepsWf`
  (`WeakRvwmoConf.lean:833-838`, source conjunct `lbIsR`); the relaunch brief carries the addendum
  (`~/dev/weak-orch/allocproc_Fdep_relaunch_prompt.txt:2`).  **Empirically confirmed**: the w3 workspace differs from the
  tip in 35 `Weak/` files (the `LDev` payload sweep — `AxDevGraph`, `AxEpiChain`, `AxFetch1/3`, `AxLock3Wp2`, `AxOpsem`,
  `AxPair`, `AxRunGV2`, `MachOfPf*`, `PfStepTso`, `VirtioProg`, `WeakAxRealize`, `WeakErase`, `WeakEvCapstone`,
  `WeakEvInst`, `WeakEvPf`, `WeakPromise*`, `WeakRefuse`, `WeakRobust*`, `WeakRvwmoAdm`, `Cert3b`, `Cert4`, `Conf`,
  `CycWit*`, `Fab`, `Progress`, `Supply`, `Walk*`); its ONLY edit to `WeakRvwmoAdm.lean` is `:692/:696` (`LDev kd ba bs
  sa sv`); it touches NONE of D35-fix's other 17 files, none of `GraphFabResidue`/`Lin2`/`FabInd`, none of
  `Acyc`/`Topo`/`Hull`/`KillArms`/`Glue`, none of `RvwmoXv6Sca*`, and not yet `AxDeps`/`CatLinChain`/`AxSpinSpike`
  (increment (1) before (0), as the plan orders).  w2 differs in `Weak/WeakAdequacy.lean` + 10 `MachCSL/` files only.
- **[R39.3]** in §C top (plan `:2179-2208`), §A(6) (`:775-778`), §D Q-L-R3 (`:4707-4709`): the counter-model is REAL —
  `pstepDisk`'s `DFence` arm emits the ROW event `LFence true true true true` (`WeakEvInst.lean:511`); the `DWriteDev`
  own-guard SKIP is `LSilent` (`:519-525`) and `LSilent` is an ADMIN label (`WeakAxRealize.lean:140-144`), so it folds into
  the NEXT row item's block via `admRunT` (`WeakRvwmoFab.lean:285-292`, `pdevEv p l p1 || b`) where `pdevEv :605-611` is
  `true` on `.PDisk (some (DWriteDev ..))`; `hemitf`'s `tq k = (b || pdevEv pa l p')` (`:370`); the membership clause
  `… ∨ tq k = true` (`:857`); `lbIsMem :127` = R ∨ W ∨ Io, so the `LFence` member is neither `gmem` nor `gisAnc :1141`;
  `gmoLt :137` needs `gxGmo` membership and `graphOfCand :272-279` filters `lbIsMem`.  The program order
  (`VirtioProg.lean:68-95`: used-element `DWriteDev` → `DFence` → used-idx `DWriteDev`) puts exactly the used-ELEMENT
  store's skip into the `DFence` block.  The §A/§D text is in place and honest.

## REQUIRED change

**[R40.1] §C top W13 (R3′): the `WeakRvwmoLin2` scope and the "LEAVES" sentence contradict the acceptance, and
`gfDevAnc` as written does not fit `devOrderOfPtraceExtIO`'s proof.**
  *Evidence.*  (a) The plan says "Files: … `WeakRvwmoLin2.lean` (§8.3 only)" and "LEAVES `fconfSupply' :1251` /
  `fconfTraceRealizeIO :1271` / `trDevOrderedOfPtraceIO :1241`", yet two sentences later "`gfDevAnc` is a NAMED premise
  of `fconfTraceRealizeIO`" and the acceptance lists `fconfTraceRealizeIO`'s premises WITHOUT `gfDevGmo`/`gfDevWIo` and
  WITH `gfDevAnc`.  Today `fconfTraceRealizeIO :1266-1272` takes `gfDevGmo GF → gfDevWIo GF →`; `fconfSupply' :1247-1252`
  and `trDevOrderedOfPtraceIO :1237-1241` take both too.  Their STATEMENTS must change (drop `gfDevGmo`, replace
  `gfDevWIo`) — the worker gets two instructions.  (b) `devOrderOfPtraceExtIO :1233-1236` proves "members are trace-
  ordered" from `hext.2 e e' (Or.inr ⟨hwio e …, hwio e' …, hgmo …⟩)` — i.e. through `ptraceRelIO :1079`'s SECOND arm
  `gisWIo x ∧ gisWIo y ∧ gmoLt x y`.  With `gfDevAnc` ("every member is `gisAnc`": writes, I/O events, **disk-row
  READS**), a disk-row-read member is NOT `gisWIo`, so this lemma is NOT provable as stated from `ptraceExtIO`; either
  `ptraceRelIO`'s arm widens to `gisAnc` (then `glinIOPtraceExtIO :1195-1199` is re-proved with `fun _ h => h` in place of
  `WeakRvwmoLin2.wioAnc` — S, but that is §8 preamble + §8.2, not "§8.3 only") or the lemma is specialised to the anchored
  trace via `glinAAncIff :2288`.  (c) The plan's reason for preferring `gfDevAnc` over `gfDevWIo` — "`gisWIo` misses
  only on disk-row READ members, e.g. a descriptor read at a `pdevEv`-true guard step" — names a case the disk program
  does not have: a `DRead` block's own step is `pdevEv`-false (state `.PDisk (some (DRead ..))`), `DRead` keeps `d' = d`
  (`WeakEvInst.lean:504-509`) and is not I/O; the only silent steps that are `pdevEv`-true are the `DWriteDev` SKIP/ABORT
  (`:519-531`), and the row item FOLLOWING each is (`VirtioProg.lean:68-95`): fill → status `DWriteDev` (W), status →
  used-element `DWriteDev` (W), used-element → `DFence` (the counter-model), used-idx → `DRet DIdle` (`LSilent`,
  `pdevEv`-false, `:556-557`) → START (`LDev`, I/O), ABORT → `dp' = none` → START.  So on THIS program the `tq`-members are
  writes, I/O events and (only via the one skip) the `DFence`; a `DRead` is NEVER a member, and `gfDevWIo` and `gfDevAnc`
  have IDENTICAL discharge obligations on xv6 runs (both reduce to "the used-element store's guard never skips").
  *Change (pick ONE, write it consistently in the item's files / what-changes / acceptance lines; both S):*
  **(α) RECOMMENDED — keep `gfDevWIo :1222` as the NAMED premise** (rename nothing): `gfDevGmoOfRes : ioResidueGmo GF →
  gfDevWIo GF → gfDevGmo GF` (`gisWIo ⇒ gmem`, so the `gmem`-wide arm fires on every `gfBefore` pair; replaces
  `gfDevGmoOfIo :1225`); `fconfTraceRealizeIO :1271` DROPS `gfDevGmo` only; `devOrderOfPtraceExtIO`, `trDevOrderedOfPtraceIO`,
  `fconfSupply'` are then literally LEFT ALONE and "§8.3 only" becomes TRUE; the disk-side discharge in W13 (W)/W14 is the
  same sentence as today's `gfDevAnc` one (no own-guard skip at the used-element `DWriteDev` on an xv6 run), the hart side is
  immediate (below, [R40.s2]).  Acceptance: premises = `rvwmoMinusConsistent`, `grule14`, `ioResidueGmo`, `gdiskRead14`,
  `gfexecConfIO`, **`gfDevWIo`**, `length ≤ N`.  **(β) keep `gfDevAnc`**: then say "`ptraceRelIO :1079`'s second arm → `gisAnc
  x ∧ gisAnc y ∧ gmoLt x y` (§8 preamble); `glinIOPtraceExtIO :1195` re-proved (`fun _ h => h`); `devOrderOfPtraceExtIO :1233`,
  `trDevOrderedOfPtraceIO :1241`, `fconfSupply' :1251`, `fconfTraceRealizeIO :1271` take `gfDevAnc` in place of `gfDevGmo ∧
  gfDevWIo` (STATEMENT changes, §8.3); `gfDevWIo :1222` deleted or kept as a lemma-level name" and delete the "LEAVES" clause
  and "(§8.3 only)".  Either way, correct the motivating sentence: "(`gisWIo` would miss a disk-row READ member; the current
  program has none — the only non-W/I/O `tq`-member is the `DFence`)".  §D Q-L-R3's refinement line (`:4707-4709`) names
  `gfDevAnc` — align it with the choice.  Size of (R3′) stays S.  No other file is affected: outside `Lin2`/`GraphFabResidue`
  the only mentions of `gfDevWIo`/`gfDevGmo`/`ptraceRelIO`/`fconfSupply'`/`fconfTraceRealizeIO` are the `FabInd.lean:464-465`
  docstring (already in the list).

## Launchability (the brief's four items, beside w3 and w2)

- **W13 (R3′)** — NOT as written ([R40.1]); after the one-paragraph fix, launchable at once as the (K) worker's first
  increment.  Its files are untouched in w3 and w2 (directory diff); `GraphFabResidue`/`Fab`/`Lin2`/`CatLin` are in NO
  registered root's import closure (computed over `import Weak.*` lines for `AxSpinT2b/T2b2/T2c/T2e3/T2q1-4`,
  `SrvwmoXv6Adequacy`, `SailCycleOrderCycle`), so `audit.sh --weak --build` cannot change — "`audit.sh --weak` unchanged" is
  automatic, see [R40.s1].
- **D35-fix** — LAUNCHABLE AS WRITTEN.  All 18 named files verified (`AxGraphCat`, `WeakRvwmoGraph`, `Kill :86-87/162/
  192/221`, `Dec :244`, `Xchg :743/896`, `Acyc :512`, `Norm :362-363`, `Floor` (`grelacqGmo`, header `:21`), `ConfWit2 :324`
  `g2PpoGmo`, `Adm :850`, `AxLitmus :111/115/119/316`, `AxGraphDec :419-433`, `AxProtLock3 :163/182`, `AxSpinSpike :749`
  rebuild, `CatLinWit :42`, `CatLinHull :94-126`, `CatFloor :29-34/60/330…825`, `CatFloorWit :35`).  The registered roots'
  closures DO reach `WeakRvwmoGraph`/`AxGraphCat`/`Acyc`/`Adm`/`AxDeps`/`AxSpinSpike` (all ten roots) — the RE-AUDIT is
  load-bearing and correctly required.  No theorem outside the concrete witness files derives `gppoGmo` or
  `rvwmoMinusConsistent` from the operational side (grep), so widening `gppo` creates no new proof obligation; M1/M2's
  premises are candidate-level (`srvwmoConsistent c`, `SrvwmoXv6Witness.lean:599-607`, `PfRunUnpinned.lean:594-598`) —
  statements unchanged, rebuild only ([R40.s3]).  vs w3: the one shared file `WeakRvwmoAdm.lean` is ALREADY edited in w3 at
  `:692/:696`; D35-fix's `:850` hunk is disjoint — rebase S as planned.
- **W13 (K)** — launchable after (R3′) as planned: `racyD :200`, `normalizeOfAcyclic :607-617`, `Hull :716-722`
  (`hullRule14`), `KillArms :499` `csChained`, `Glue` `hullRun` verified; none touched in w3/w2.  Under [R40.1] (α) or (β)
  `racyDIO := racyD ∪ ioResidue ∪ gmo|IO ∪ …` is textually unaffected; its `ioResidue` arm now carries the `gmem`-wide
  fabric pairs, all gmo-forward by `ioResidueGmo` — the kill's "arms gmo-forward by (T)" sentence still holds.
- **W11 (iv)c** — LAUNCHABLE AS WRITTEN: `linNwAAnc :208`, `linCandScaTA :748`, `linCandScaTMinusA :790`, `gisAnc :1141`,
  `linCandIO :1147`, `gdiskRead14 :1153` in the tip; `RvwmoXv6Sca*` untouched in w3/w2; ∩ everything = ∅.
- **Order**: (R3′) → (K) (one worker); W11 (iv)c any time; D35-fix any time in its own workspace — see [R40.s1] on the
  "(R3′) lands first" gate.  ONE `audit.sh --weak --build` after D35-fix and (F-dep) (0) are both in, as planned.

## SUGGESTIONS

- **[R40.s1] The "(R3′) lands BEFORE D35-fix launches so ONE audit covers both" gate is not load-bearing** — (R3′)'s
  files are outside every registered root's import closure (above), so its `audit.sh --weak` is a no-op; the audit that
  matters is D35-fix's (and (F-dep) (0)'s).  Suggest: launch D35-fix NOW in its own workspace (∩ w3 = `Adm :850` vs `:692-696`,
  disjoint; ∩ (R3′)/(K)/(iv)c = ∅), keep the single combined audit after D35-fix + (F-dep) (0); let (R3′) land whenever
  green.  This removes a serial dependency between two independent workers.  Not required (the plan's order is safe, only
  slower).
- **[R40.s2] (R3′) hart-side discharge: add the two cites that make it immediate.**  A hart block is a member only via an
  `LDev` row item: admin labels are `LSilent`/`LRegW`/`LCtrl` (+ `LInstr`/`LIFetch` under `instr`) — `lbAdmin`,
  `WeakAxRealize.lean:140-144` — never `LDev`, so `pdevEv` is false on every hart admin step (the `.PDisk` match fails for
  harts, `WeakEvInst.lean:605-611`); hart RAM/fetch arms keep `d' = d` (`:316-360`), so `dvi k ≠ dvo k` also needs an `LDev`
  step; `LDev` projects to `LIo` (`WeakPromiseBridge.lean:542`), hence `gisIo` — a member by class.  With (α) this IS the
  hart half of `gfDevWIo`.
- **[R40.s3] D35-fix (5)**: say "all 13 registered roots rebuild (the ten audited modules import `WeakRvwmoGraph`/
  `AxGraphCat`); M1/M2 (`srvwmoXv6M1Core`/`M1`/`M2`, `roots-weak.txt:23-25`) have candidate-level premises — statement and
  meaning unchanged; the LB roots' premise strengthens as stated".
- **[R40.s4] D35-fix (2)**: "`grcsc` defined there (`WeakRvwmoGraph`)" needs `lbRcsc` to move with it (today
  `AxGraphCat.lean:143`; `lbAq` `WeakAxiomatic.lean:184` and `lbRl` `WeakAxiomatic2.lean:434` are already below `Graph`,
  as `grelAcq :227-229` shows) and a `Decidable (grcsc …)` instance beside `grelAcqDec` (`Dec.lean:244`) for `gppo`'s
  decidability.
- **[R40.s5] File-count wording**: the D35-fix header says "≈ 16 files — rev 42's 14 + `CatLinWit`/`CatLinHull`" while
  R39 counted rev 42's list as 12 and the body says "the grep … is exactly these 14 files" after naming 18 (17 edits +
  `AxSpinSpike` rebuild).  Say "grep = 14 files; edits = 17 (+ `Norm`, `ConfWit2`, `Adm` beyond the grep) + 1 rebuild".
- **[R40.s6] Counter-model wording**: "a `DWriteDev` own-guard SKIP or ABORT … folds into the `DFence`'s block" — only the
  SKIP at the used-ELEMENT `DWriteDev` does (ABORT ends the burst, `dp' = none`, next row item START = `LDev`); say so, it
  sharpens the (W)/W14 obligation to one guard.
- **[R40.s7] Cite drift**: `grelAcqB` is `AxLitmus.lean:111` (`:115` is its spec); `grcscB`'s cat use is `:316`;
  `pdevEv`'s def is `:605-611` (`:604` is the docstring); `rowsRelGppo` spans `:510-519`.  After w3 merges, every
  `WeakEvInst`/`VirtioProg`/`Fab` line in the (R3′) header will drift — the (R3′) worker should re-cite at merge.

## Owner questions the plan is missing

None.  Q-L-R3 and D35-rule7 remain RULED and in the spec-first / plain-language format (R39 checked the cat quote);
[R39.3]'s refinement line is recorded (`:4707-4709`).  [R40.1] is a refinement WITHIN the RULED option (a) — which named
premise replaces `gfDevWIo`, and whether any — not a new memory-model question: RVWMO/riscv.cat/Sail have no device events,
Zifencei and the PMAs are silent, and both (α) and (β) are device-model text of EQUAL strength on every xv6 run (same
discharge obligation); the owner is informed under the non-blocking rule, no menu needed.
