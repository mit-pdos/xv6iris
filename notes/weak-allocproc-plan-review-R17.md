VERDICT: NOT SATISFIED

# Review R17 of `notes/weak-allocproc-plan.md` rev 20 (adversarial, evidence-based; 2026-10-11)

Scope (per the R17 brief): rev 20 = rev 19 + R16's six required changes (+ [R16.1-alt]) + [OWN.30]–[OWN.32] + the
W13 (T)+(M) / W5-pre / W11 (iv)a DONE records + the NEW W-DMA0 item.  Audited: (1) every R16 change against the plan
text AND the code it cites; (2) [R16.1-alt] — `DWriteDev g = none` SKIPS — against `MachCSL/Lang.lean:540-544` and
`:561-577`, and the liveness-weaker consequence the plan names; (3) the W-DISK (M4)/(M9) MECHANISM against `pdevOk`
(`WeakPromiseFact.lean:613-614`), `pdevEv`/`pdevEvOk` (`WeakEvInst.lean:544-547, 1670-1700`) and EVERY consumer of
the devfree lemmas (`WeakRvwmoSupply.lean:164-246`, `WeakRvwmoFab.lean:346-503, 689-842`, `WeakRvwmoLin2.lean:997-1037`,
`WeakRvwmoFabInd.lean:443`); (4) the pinned `pfStepTso` statement against the types it names (`pstepEv`
`WeakEvInst.lean:533`, `pnodeStep :280-346`, `wpPfStep` `WeakPromiseBridge.lean:339`, `pfStepFactsT` `TsoShadow.lean:576`,
`rmem` `PfStepTsoMem.lean:62`, `viewRel` `PfStepTsoView.lean:135`, `evStep` `Lang.lean:355`); (5) the W-DMA0 consumer
list by grep; (6) the three new DONE records line by line; (7) the launch set.  `file:line` cites `../xv6iris-weak`.
Advisory only; no proofs or builds; no git/jj; no subagents.

**Sign-off.**  NO — not as written, but close.  All six R16 changes and the three rulings ARE applied where the plan
says; the DONE records are exact; W-DMA0 is launchable as written (one over-listed consumer, [R17.s2]); W11 (iv)b is
launchable.  Three briefs are NOT yet launchable: **W-DISK** — the MECHANISM's `g = none → skip and continue with k`
arm, taken from `dmaWrite`'s own guard (`Lang.lean:544`, correctly), is applied to the FOLDED `DevM.guard`s, whose
MachCSL semantics is BLOCK-and-retry (`devBlocked :561-563`, `devStep :575-577`), and nothing in the brief makes a
skipped guard propagate — so the pf program can perform a used-idx write + `complete` that MachCSL's blocked task
cannot match, and W4 F9's simulation has no closing case ([R17.1]); the state-aware `pdevEv` FALSIFIES the devfree
lemmas as STATED (they quantify over an arbitrary start state `p`) and the ripple reaches `WeakRvwmoFab.lean`, which
W-DISK's file list does not name ([R17.3]); **W2 CLOSE ∥ W4 F1–F8** — the pinned `pfStepTso` is not a Lean statement
yet: `c'` is unbound, `m` and `o` are unrelated binders, `MemReq` does not exist in the tree, `wpPfStep`/`pfStepFactsT`
miss their explicit parameters ([R17.2]).  One honesty gap in (d): the pf disk program serves ONE request per burst,
in ring order, to completion — a device-model STRENGTHENING over both virtio (out-of-order completion is legal) and
MachCSL (concurrent `serve` tasks) that §B(11) does not name ([R17.4]).

## What was verified (holds as cited; not to re-litigate)

**[R16.1]** The MECHANISM text is in §C W-DISK (:1253-1291) with the invariant quoted correctly: `pdevOk pstep pdev :=
∀ p d l p' d', pstep p d l p' d' → pdev p l p' = false → d' = d ∧ ∀ d0, pstep p d0 l p' d0` (`WeakPromiseFact.lean:
613-614`) ✓; `pdevEv (_p) (l) (_p') := match l | LDev .. => true | _ => false` with docstring "a function of the LABEL
alone" (`WeakEvInst.lean:543-547`) ✓; header convention `:30-33` ✓; START reads `dvirtio d` (`:488`) ✓;
`pdiskProgDevFree :1670`, `pstepDiskDevFree :1686`, `pdevEvOk :1694` ✓; the sole direct consumer of `pdevEvOk` on the
path is `WeakEvCapstone.lean:1183` (`wpBehaviorFulfilOnceDev pstepEv pdevEv … pdevEvOk`) ✓ (the other `pdevOk` mentions,
`WeakRobustGraph.lean:912`, `WeakRobustMain.lean:1521-1638`, are parametric in `pdev`); `pdevEvFalse :164`,
`pstepEvDevfree :169`, `admRunDevfree :175`, `hemitDevfreeConst :202`, `hemitDevfreeRefab :241`, `emDevfree :284`,
`gdexecQconf :292` ✓; `lbIsdev :119-122`, `emDev :144-150`, `isDevBlock :152`, `hemitf :239-262`, `hartConff :262`,
`Gfexec`/`gfDev :516-518`, `isDevBlock ↔ gfDev :533`, `gfexecConfOfQconf :649`, `hblkQ :318` and consumers `:346-503`
✓ (`WeakRvwmoFab.lean`); `DevM.dmaWriteStep` `DevLang.lean:164-167` with "`g s = none` blocks nothing and writes nothing"
✓; **DWild = 21** (`VirtioProg` 14, `WeakEvLang` 3, `WeakEvDisk` 2, `WeakEvInst` 2; `WeakEvPf` 0) ✓;
`eprimStepDiskReducible :1347` with its DWild arm `:1359` ✓; W13 (I) marked M ✓ (§C W13 (I) :1620, §D Q2 :1905).
**[R16.1-alt]** `Lang.lean:540-544`: `.dmaWrite g pa n w` → `(∃ s', g … = some s' ∧ devObsOk … ∧ ramBytes pa n ∧
¬ anyReserve … ∧ σ' = (σ.storeDma pa n w).setDev d s') ∨ ((g … = none ∨ ¬ ramBytes pa n) ∧ σ' = σ)` — a `none` guard
SKIPS and the task CONTINUES ✓ as the plan says; `devBlocked` for `.dmaWrite` requires `(g …).isSome` (`:561-563`) ✓.
**[R16.2]** [OWN.30]/[OWN.31] recorded in header (:3-4), §C top (:973), §C W-DISK (M4)/(M5), Status (:1797-1807), §D
(:1816-1819, :1836, :1876), D26 (:2306-2307) ✓; [OWN.32] likewise ✓.  **[R16.3]** W-DMA0 is a standalone §C item
(:1354-1371) on the serial lane, ordered W-COH ✓ → W-DMA0 → (M1) → W-RSV, the cycle named (:1351-1353) ✓; the Spec
line is FIRST and cites Sail `Mem.lean:494-496,612-614` ✓; consumers by grep: `MachCSL/Resources.lean` 2 (`mmOk_storeDma
:862` ✓), `WpDma.lean` 19 (`:55, :64, :80-82, :118, :142` ✓), `WpDevDisk.lean` 3 ✓, `vtest-lean/Vtest/XState.lean:
315-320` ✓, `DevExec.lean:77` ✓, `Weak/PfStepTsoView.lean` 6 (`sameReadStoreDma :155` ✓, `rowDiskWrite :797-800` ✓);
`MState.storeDma` IS an `abbrev` at `Lang.lean:171-173` ✓; `lakefile.toml:43-49` `Vtest` not default ✓;
`tools/ci/vtest.sh` exists ✓.  **[R16.4]** `SrvwmoXv6Witness.lean` 805 lines, header `:17-24`, `srvwmoXv6M1Premises
:599-607` quoted VERBATIM in §A (:386-392) ✓, `m1PremisesS :611`, `srvwmoXv6M1PfRun :624`, `srvwmoXv6M1Satisfiable
:733`, `esilAdmRun :169`, `execProgOk'SNil/SSnoc :272/280` ✓; `RvwmoXv6Sca.lean` 327: `tvnSca :50`, `gwixLeTvnSca
:116`, `tvnScaMono :133`, `linGmoEmitBefore :144`, `linLogEmitted :172`, `linTvnScaLe :194`, `linScaOk :241`,
`linCandSca :314` ✓; W11 (iv)b LAUNCHABLE ✓.  **W13 (T)+(M)**: `GraphFabResidue.lean` 268: `gisIo :67`, `gisR :73`,
`gfBefore :79`, `ioResidue :84`, `ioResidueGmo :99`, `ioResidueNodev :119`, `ioResidueAcyclic :148`, `gfIoDev :172`,
`ioResidueGwfInterim :184`, `w13fIoResidueOk :236`, `w13fIoRevExcluded :261` ✓; `lbIsMem` `WeakRvwmoGraph.lean:126`,
`gwfNoIo :739`, `gwfMemRW :747` ✓; `fenceGob` on `lbIsR || lbIsW` `AxSpinProt3.lean:393-395` ✓; `Weak.lean:629-630`
imports both ✓.  **[R16.5]** `SpecVirtioDiskInit.lean:10` "clear RO/SCSI/FLUSH/…" ✓, `ProofVirtioDiskInit.lean:935`
"DRIVER_FEATURES := 0" ✓, `vdi_wce_15 :559` ✓; the FLUSH mark is "UN-negotiated → UNSPECIFIED; both choose; vacuous"
at §0 F1 (:166-169), §B(11) (:831, :848-850), W-DISK Spec (:1198-1202), (M7) (:1230), E-D1 (:1971-1973) ✓; the
PERMANENT "Machine-model choices" list (i)–(vii) is in §B(11) (:842-856) ✓ with `complete :423-427`, `completeOk
:412-416`, `stall :457`, `fetch :466-481`, `statusOf :377-379`, `dmaView :189`, `usedLen :382` all exact ✓.
**[R16.6]** the pinned statement is in §C W2 CLOSE (:1059-1080); item (3) `fiArm` assigned to W2 CLOSE in both places
(:1035-1036, :1043-1046) ✓.  **Suggestions**: [R16.s1] cite-drift line (:393-399) ✓; [R16.s2] Spec FIRST on Q1/Q2 ✓;
[R16.s3] the `diskOf` note (:853-856, :1234-1236) ✓; [R16.s4] `Supply :164-175` merge clause (:1316-1317) ✓; [R16.s5]
F9 bookkeeping (:1179-1185) ✓; [R16.s6] launch set (:973-981) ✓.  **(a)/(b)** spot-checked, unchanged from R16:
`LinkAllocproc.lean:14-16`, `wp_allocproc_body` premises `SpecAllocproc.lean:204-224`, `roots.txt:6,19`, `baseline.json:
11-14` (3 axioms + 3 opaques), `notes/adequacy_axioms_baseline.md` (the `bv_decide` certificate count, 445 for the
closed root) ✓; the sRVWMO residue table `WeakAxiomatic3.lean:2054-2082`, `srvwmoConsistent :2084`, `srvwmoRealizable
:2088`, litmus `WeakSrvwmoLitmus.lean:1663-1695`; `TsoMem.lean:1-40` header now states the foreign-only stamp and the
reset ✓.  **Virtio cites**: `taken` guard `:530`, status `:536-537`, `pushed` gate `:539-541`, `let c := v.cfg :545`,
used-element guard `:546-547`, `dmaWriteStep … complete :552-555`, root loop `:558-587`, guard-pop `:571-578` (plan
`:576-578` — the guard body), `fork :579`, `capture :515-518`, `fill :488-492`, `deviceFeatures :100` bit 9 ✓.

## REQUIRED changes

- **[R17.1] The MECHANISM's `g = none → skip, continue with k` arm is the right twin of `dmaWriteIf`/`dmaWriteStep`'s
  OWN guard but the WRONG twin of the FOLDED `DevM.guard`s; as written the pf program can complete a request whose
  MachCSL twin is blocked, and W4 F9 cannot close.**  *What is wrong.*  Two MachCSL constructs are being folded into one
  pf arm.  (i) A `dmaWrite` whose `g` answers `none` SKIPS the write and the task CONTINUES (`Lang.lean:544`; `DevLang.
  lean:166-167`) — [R16.1-alt] is right for the write's own `reqOf s h = some r ∧ usedIdx = ui ∧ cfg = c` guard.  (ii)
  A `DevM.guard` is a `.step g`; when `g` answers `none` the step is BLOCKED and the task RETRIES it (`devBlocked :561-
  563`: `.step g => ∀ s' os, g … = some (s', os) → ¬ devObsOk …`, vacuous for `none`; `devStep :575-577`: `devBlocked d
  o σ ∧ m' = m ∧ σ' = σ`) — the task does NOT continue.  The plan folds (ii)'s guards (`taken :530`, `pushed :539-541`)
  "into the NEXT fabric step's `g` as its failure case, where 'fail' is the skip" (:1271-1274) and ALSO says pf carries
  "COARSER phases … equal up to phase" (:1279-1281).  Trace the `taken` latch of an OUT request: MachCSL blocks at `:530`
  until the latch frees and performs NO later write of that `serve`; the pf twin SKIPS the status `DWriteDev` and
  CONTINUES to the used-element `DWriteDev` (its `g` has `completeOk`'s `taken = some h`, so it skips) and then to the
  used-idx `DWriteDev`, whose `g` as the plan states it (`cfg = c ∧ usedIdx = ui`, re-checked "exactly as `serve :553`
  does", :1276-1277) is TRUE — pf performs the used-idx RAM store and `complete` (ISR raised, request removed) while
  MachCSL's task sits blocked at `:530`.  `R-log` and `R-dev` have no matching MachCSL step.  The same shape arises
  from a failed `pushed` gate.  The brief's "SAFETY-equivalent to MachCSL (RAM and fabric unchanged on both sides; a
  stuttering match)" (:1273) holds at the skipped step only, not for the continuation.  Two further gaps in the same
  paragraph: (b) `completeOk`'s drain conjunct (`!reqCached`, `:412-414`, under `wce = false`) must NOT enter any `g` —
  pf has no drain step (F9 bookkeeping :1183-1184 already says the idx `DWriteDev` "absorbs the root loop's drain
  steps"), so if a worker folds `completeOk` verbatim the pf program skips EVERY OUT request's used-element/idx writes
  and xv6's `virtio_disk_rw` sleeps forever on `b->disk`: a safe but write-dead disk; (c) the sentence "the mid-burst
  config write that distinguishes them is unreachable under the verified driver" (:1275-1276) is true only AFTER (b)
  and the single-burst invariant below are stated — `taken`/`pushOk` are trivially true in pf only because the pf disk
  program serves one request per burst (`pdiskProg` holds ONE `Option (DM Dres)`; START only from `none`, `WeakEvInst.
  lean:488`; `virtioProg :606-623` pops `seen` and runs to `dcomplete`), an F9 INVARIANT ("`dvirtio.inflight` has at
  most one entry during a burst") the brief does not name.  *Exact change (replace :1268-1281 by a FOLDING RULE,
  binding for the worker; choose (α) or (β) and say which):*
  **Per MachCSL construct:** `dmaWriteIf`/`dmaWriteStep` own guards → folded into the SAME node's `g`, failure = SKIP
  (1 → 1, `Lang.lean:544`); `DevM.guard` (taken `:530`, pushed `:539-541`) → folded into the NEXT fabric step's `g` as
  its failure case, failure = **(α) ABORT**: `g (dvirtio d) = none → l = LSilent ∧ dp' = none ∧ d' = d` — the burst
  ends with the request left IN FLIGHT exactly as MachCSL's blocked task leaves it (phase set, `taken` held, `complete`
  not run), matched 1 → 1 by `devStep`'s blocked arm (`:576-577`), after which the MachCSL twin's task is a ZOMBIE that
  the matching schedule never steps again (no fairness) and pf's next START ↔ MachCSL's root-loop pop; `R-dev` stays
  EQUALITY on `inflight`/`taken`/`isr`/`usedIdx`.  Or **(β) SKIP with PROPAGATION**: keep `dp' = some k` but drop
  "coarser phases" — pf's `g`s perform MachCSL's `setPhase` moves EXACTLY (the folded `modify`s run inside the next
  fabric step's `g`) and every `g` REQUIRES the phase its MachCSL predecessor set (`reqOf` already reads the phase, `:454`;
  add `phase s h = some (.pushed r)` to the idx write's `g`), so a skipped guard makes every later `g` of the request
  `none`; state as an F9 obligation "`g_j = none → g_{j+1} = none` along a request".  The reviewer recommends (α): no
  phase bookkeeping, `R-dev` stays equality, and the one-row program never carries a half-served request.  **Not in any
  `g`**: `completeOk`'s `!reqCached` (discharged by inserting MachCSL `drain` steps, `body :582-586`, before the gate in
  the matched run — say so here, not only in F9's bookkeeping) and `DevM.guard`s that are trivially true under the
  **single-burst invariant** (name it; (M9)'s pop guard "a head already held" `:571-578` is likewise never false in pf).
  **Snapshot**: the `pa`/`bs` of every `DWriteDev` are fixed at node construction, so the burst's `cfg`, `usedIdx` (for
  `usedElemAddr c ui`, `usedIdxAddr c`, `ui + 1`) AND `cacheView` (the IN request's data; (M8)'s "reads `cacheView v`
  at fill time" (:1231) is impossible without a re-read node — correct it to "from the START snapshot, equal to
  MachCSL's fill-time view in the matched run because drains preserve `cacheView` and the single-burst invariant
  excludes a concurrent capture") come from the START snapshot `v`, with `g` re-checking `s.cfg = c ∧ s.usedIdx = ui`.
  **Mark**: after this rule the ONLY reachable divergence from MachCSL is a `cfg`/`usedIdx` change mid-burst (device
  reset or config rewrite — unreachable under the verified driver, `virtio_disk_init` writes the queue config once
  before DRIVER_OK), where MachCSL skips the write(s) and pf aborts/skips — LIVENESS-weaker there only, SAFETY-equal;
  the "pf abandons a request MachCSL would have completed later" sentence is to be rewritten to this scope.  Cost:
  text only (S); W-DISK's size class unchanged; F9's bookkeeping rows "each `DWriteDev` 1 → k" and "the `none` arm 1
  → 0" (:1182-1185) become "`none` arm 1 → 1 (`devStep`'s blocked arm) under (α)".
- **[R17.2] The pinned `pfStepTso` (:1062-1077) is not a Lean statement; W2 CLOSE and W4 F1–F8 would still each write
  their own.**  *What is wrong, against the code.*  (i) `c'` occurs in `wpPfStep (hartAgent cpu) l c c'` and in the
  conclusion but is NOT bound.  (ii) `m : SailM Unit` and `o : Outcome Register RegisterType` are unrelated binders;
  `pnodeStep` dispatches on `m = .impure (.ok o) k` (`WeakEvInst.lean:284-296`) and `evStep cpu o σ v σ'` (`Lang.lean:
  355`) is about THAT `o`; without `m = .impure (.ok o) k` the conclusion quantifies an arbitrary node.  (iii) `MemReq`
  does not exist in the tree (grep `MachCSL/`, `Weak/`, `model/`: none); the RAM arms destructure `o` as `.memRead n
  _va req` / `.memWrite n va req` with Sail's request records (`:298-346`; `req.pa`, `req.access_kind`, `req.value`),
  whose types differ between read and write and depend on `n` — `(req : MemReq) (n : Nat)` cannot be stated.  (iv)
  `wpPfStep` takes `pstep pcls` explicitly (`TsoShadow.lean:588`: `wpPfStep pstep pcls i l c1 c2`) and `pfStepFactsT`
  takes `fok stamp` (`:576`, `pfStepFacts fok …`); the pinned text omits `pstepEv pclsEv` and `fok`.  (v) the
  conclusion's `v = ⟨the answer the pf continuation consumed …⟩` is prose.  *Exact change (replace :1062-1077):*
  ```
  variable (fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop)
  theorem pfStepTso (c c' : Wpcfg Pexv6 Efab) (st : List (Nat × Wlabel)) (σ : MState) (cpu : CPU)
      (o : Outcome Register RegisterType) (k : o.ret → SailM Unit) (rs : RegFile)
      (fn : Option (Bool × Bool × Bool × Bool)) (ib : Ibch) (l : Wlabel) (p' : Pexv6) (d' : Efab) :
      pstepEv (.PHart cpu (.impure (.ok o) k) rs fn ib) c.pcDev l p' d' →      -- the node IS `o` (E-M1)
      wpPfStep pstepEv pclsEv (hartAgent cpu) l c c' →                          -- WeakPromiseBridge.lean:339
      pairAdjacent (st ++ [(hartAgent cpu, l)]) →
      pfStepFactsT fok TsoShadow.cohSrc st c (hartAgent cpu) l →                -- TsoShadow.lean:576
      (∀ n va req, o = .memRead n va req → ramBytes req.pa n) →                 -- E-M4, from HSafe
      (∀ n va req, o = .memWrite n va req → ramBytes req.pa n) →
      rmem c st σ → viewRel TsoShadow.cohSrc σ st →
      ∃ (v : o.ret) (σ' : MState),
        evStep cpu o σ v σ' ∧                                                     -- Lang.lean:355
        (∃ rs' fn' ib', p' = .PHart cpu (k v) rs' fn' ib') ∧                     -- `v` IS what the pf continuation took
        rmem c' (st ++ [(hartAgent cpu, l)]) σ' ∧ viewRel TsoShadow.cohSrc σ' (st ++ [(hartAgent cpu, l)])
  ```
  with `pfStepTsoStutter`/`pfStepTsoSame` as before (same hypotheses; `σ' = σ`), and the sentence "binders may be
  renamed, hypotheses may be WEAKENED by the prover, the conclusion's shape and the explicit-parameter order are fixed".
  (If `fn`'s type is not `Option (Bool × Bool × Bool × Bool)` — `pnodeStep`'s `fn'` is, `:281` — W2 CLOSE fixes it on
  day one and W4 takes the file's `variable`.)  S, text only.
- **[R17.3] The state-aware `pdevEv` falsifies the devfree lemmas AS STATED; the fix is a START-STATE hypothesis that
  ripples into `WeakRvwmoFab.lean` (and the `fconfSupply` family), which W-DISK's file list does not name.**  *What is
  wrong.*  `admRunDevfree`, `hemitDevfreeConst :202`, `hemitDevfreeRefab :241` (`WeakRvwmoSupply.lean`) and
  `hemitfStatesQ :346` / `hartConffStatesQ :471` (`WeakRvwmoFab.lean`) quantify over an ARBITRARY start state `p :
  Pexv6`.  With `pdevEv p l p' := lbIsdev l || (p is .PDisk (some (DWriteDev ..)))`, a start state `p = .PDisk (some
  (DWriteDev g pa bs k))` followed by the fused `LStore` (no `LDev` item) moves the fabric — `admRunDevfree`'s `d' = d`
  and `hemitDevfreeConst`'s `dv j = dv k` are FALSE for that `p`.  The plan's "ONE new lemma 'a row with no `LDev` item
  never leaves `.PDisk none`'" (:1286-1288) is the right INVARIANT but it cannot rescue lemmas stated for all `p`:
  their statements must gain the hypothesis, and `hemitfStatesQ`'s induction (`WeakRvwmoFab.lean:384-387, 431-438` call
  `admRunDevfree`/`pstepEvDevfree`/`admRunRefab`) must thread it; `hartConffStatesQ :471` gets `devQuiet p0`;
  `supplyOfFconf :689` / `fconfSupply :782-842` and `fconfSupply'` (`WeakRvwmoLin2.lean:997-1037`), `WeakRvwmoFabInd.
  lean:443` take `boot : Nat → Pexv6` unconstrained and must receive `∀ i, devQuiet (boot i)` (discharged at `xboot σ0`
  = `epsInit`, `WeakRvwmoCapstone.lean:90-91`, `WeakEvCapstone.lean:1026-1027`: harts `.PHart`, the disk `.PDisk none`).
  *Exact change (§C W-DISK MECHANISM (ii) and the file list):* define `devQuiet : Pexv6 → Prop` (`.PDisk (some _) → False
  | _ → True`); prove `devQuietStep : pstepEv p d l p' d' → (∀ kd ba bs, l ≠ LDev kd ba bs) → devQuiet p → devQuiet p'`
  (the "no START ⇒ no burst" lemma; `.PDisk none` has no `LDev`-free successor arm, `WeakEvInst.lean:488-516`);
  restate `pdevEvFalse : devQuiet p → (∀ …, l ≠ LDev …) → pdevEv p l p' = false`, `pstepEvDevfree` likewise, and give
  `admRunDevfree`/`admRunRefab`/`hemitDevfreeConst`/`hemitDevfreeRefab` a `devQuiet p` hypothesis (S); add
  **`Weak/WeakRvwmoFab.lean`** (`hemitfStatesQ :346-460`, `hartConffStatesQ :471-503`, `supplyOfFconf :689`,
  `fconfSupply :782-842`) and **`Weak/WeakRvwmoLin2.lean:997-1037`**, **`Weak/WeakRvwmoFabInd.lean:443`** to W-DISK's
  file list with "a `devQuiet` start-state hypothesis threaded; no proof change beyond the hypothesis" (S–M), OR hand
  these three files to W13 (I) EXPLICITLY ("W-DISK leaves `WeakRvwmoFab.lean`/`Lin2`/`FabInd` RED behind a `sorry`-free
  `#exit`?" — no: `lake build Weak` must be green, so W-DISK owns the minimal restatement; say so).  Correct the claim
  "keep their LABEL-based `emDevfree` via ONE new lemma" (:1286) to "keep `emDevfree` label-based; the lemmas gain a
  start-state hypothesis discharged at `epsInit`".  Size class unchanged (L–XL); the (I) rebase clause [R16.s4] should
  name these ranges too.
- **[R17.4] Name the pf disk program's SEQUENTIAL ONE-REQUEST-PER-BURST service as a device-model strengthening in
  §B(11), §A(6) and W-DISK's header acceptance.**  *Evidence.*  `pdiskProg` holds ONE residual program (`dp : Option
  (DM Dres)`, `WeakEvInst.lean:485`), START only from `none` (`:488`), and `virtioProg` (`VirtioProg.lean:606-623`)
  pops `v.seen` and runs that request to `dcomplete` — the next request is not read before this one completes; after
  W-DISK the structure is the same (F9's "`fork` 1 → 0: the fork is the START of the next pf burst", :1181).  MachCSL
  FORKS a `serve` task per popped request (`body :579`) and runs them concurrently (interleaved DMA, out-of-order
  completion); virtio 1.x lets the device process and complete requests in any order (the driver tolerates it:
  `virtio_disk_intr` dispatches on `used->ring[].id`).  So the pf disk row — the DEVICE MODEL the published theorem's
  conformance premise `xv6ConfS` imposes on row `NCPU` — EXCLUDES spec-legal and MachCSL-legal device behaviours: a
  STRENGTHENING of the trusted surface, sound for W4 (pf ⊆ MachCSL) and INVISIBLE in §B(11), whose "ONE sequential
  device row" entry (:839-842) names only the UART/PLIC coupling (D51).  *Exact change.*  §B(11) "Machine-model choices"
  gains **(viii)**: "the pf disk program serves ONE request per burst, in available-ring order, to completion before
  the next pop — STRONGER than virtio (out-of-order and interleaved completion are legal) and than MachCSL (concurrent
  `serve` tasks), excluded executions: two requests' DMA accesses interleaved, a later request completing first; sound
  direction for W4; the kernel's correctness does not depend on completion order"; §A(6)'s trusted-base list cites it;
  W-DISK's acceptance header sentence (:1324-1325) becomes "Deviations from MachCSL's `serve`: the DM encoding, the
  folded guards ([R17.1]'s rule), and SEQUENTIAL single-request service (no `fork`)"; §C W13 (W)/W14's disk witness is
  unaffected.  S, text only.  (Whether to ALSO offer the owner a concurrent pf disk agent is W-DISK-Q4 below — the plan
  may close it as "(a) keep, named" without a ruling, but the strengthening must be named either way.)

## SUGGESTIONS

- **[R17.s1] `VirtioProg.lean` retire/keep ranges contradict each other.**  §C W-DISK says "Equivalence theorems
  `:803-952` — RETIRE" (:1291) and "KEEP … `virtioProgWf :952`, `runVirtioProg :664`" (:1298-1299).  Actual map:
  §0b model fragment `:211-317` (`virtioComplete :286`, `virtioReqStep :305`, `virtioUsedWrites :279`, `writeByteList
  :224`), §7 `:660-795` (`runVirtioProg :664` — stated against `virtioPending`/`chainAt`/`reqAt`/`vdelta`/`vprogWs`,
  i.e. the ROCQ model: "keep" means RE-STATE as a shape lemma over the new program, not keep), `vmodelVprogPerm :779`,
  `virtioCompletePair :792`, §8 `:796-895` (`virtioProgDisj :800`, `virtioProgReqStep :803`, `Stalled :836`, `Idle
  :850`, `Trichotomy :860`, `ReqStepState :869`, `DoneStep :884`), §9 `:897-979` (`dmWfDwriteData :919`, `dmWfDcomplete
  :944`, `virtioProgWf :952` — KEEP).  Write: RETIRE `:211-317`, `:729-895`; RE-STATE `runVirtioProg :664-728` over the
  aligned program (three shapes → done / idle / stall); KEEP §9.
- **[R17.s2] W-DMA0's consumer `PfStepTsoMem.pfDWriteRowMem :669 (case n = 0)` is a non-item**: the file has NO
  `storeDma` mention; the lemma's log clause is a HYPOTHESIS on `σ'` (`σ'.log = σ.log ++ [diskAgent]`, `:678-680`) and
  its `LStore` comes from `wpPfStep`, whose `elabOk` requires `data ≠ []` (`WeakEvInst.lean:556`), so `n = 0` never
  arises.  Drop it from W-DMA0's list and from (M5′)'s "mirrors it"; the weak-side consumers are `PfStepTsoView.lean`'s
  6 sites only.
- **[R17.s3] (M8)/(M9) snapshot wording**: "(M8) … reads `Virtio.cacheView v` at fill time" (:1231) and "(M9) … the
  START snapshot is kept for `cfg`" (:1238) — per [R17.1] the snapshot carries `cfg`, `usedIdx` AND `cacheView`; say so
  once in (M9) and cross-reference from (M8) and F9's bookkeeping.
- **[R17.s4] `WeakEvPf.ediskStepLabel`'s "DWild arm"** (:1218): `grep DWild Weak/WeakEvPf.lean` = 0 — the case is
  covered by a wildcard; write "(no textual arm; verify the exhaustive match still closes)" so the worker does not hunt
  for it; the "21 in 4 files" count already excludes it ✓.
- **[R17.s5] F9 bookkeeping after [R17.1]**: under (α) the row "the `none` arm of a `DWriteDev` 1 → 0" (:1184-1185)
  becomes "1 → 1 (`devStep`'s blocked arm for a folded guard; `dmaWrite`'s skip arm for the write's own guard)"; add the
  single-burst invariant to F9's invariant list beside `R-dev`.
- **[R17.s6] Cite drift (minor)**: Virtio's guard-pop is `:571-578` (`let popped ← DevM.get` at `:569`, the guard
  `:576-578` ✓ as the plan has it; the census row `W4-structural-census.md:250` says "`get`, guard-pop … `fork :579`" ✓);
  `hartConff :262` (plan `:262-263` ✓); `hblkQ :318` ✓; `pdevEv :544` ✓ (plan writes `:544` and `:544-547` — fine);
  `epsInit` is `WeakEvCapstone.lean:1026-1027` (plan `:1027` ✓); `xboot`/`xN` `WeakRvwmoCapstone.lean:90-94` ✓.
- **[R17.s7] §C top "MAY LAUNCH NOW"**: after this round — W-DMA0 ∥ W11 (iv)b immediately; W2 CLOSE ∥ W4 F1–F8 once
  [R17.2]'s statement is pasted; W-DISK once [R17.1]/[R17.3]/[R17.4] are written into its brief.

## Owner questions the plan is missing

- **W-DISK-Q4 — the pf disk agent serves one request at a time (raised by [R17.4]; the plan may decide it, but it
  changes the published trusted surface, so it belongs here).**  *Spec (FIRST).*  The RVWMO chapter, riscv.cat and the
  Sail model in this tree have NO device-internal events (Sail has no device/DMA model; `MachCSL/Dev/*.lean` is the only
  device text); Zifencei and the PMAs are silent; virtio 1.x (block device, split virtqueue): the device "MAY process
  requests in any order" and completes them by writing used elements in any order — interleaved service and
  out-of-order completion are spec-LEGAL.  *Plain language.*  A disk may be asked for several blocks at once (xv6's
  log writes several blocks; `bio` can have more than one request pending).  Real and modelled devices (MachCSL forks
  one `serve` task per request, `Virtio.lean:579`) work on them concurrently and may finish a later one first.  The pf
  disk program — the device half of the published theorem's conformance premise — reads one request, completes it,
  and only then looks at the next (`pdiskProg`'s single residual program, `WeakEvInst.lean:485-488`; `virtioProg :606-
  623`).  *Tiny example.*  Hart 1 publishes requests A (write block 5) then B (read block 7) and notifies; MachCSL's
  device may fetch B, DMA block 7 into B's buffer and raise the interrupt for B before A's status byte is written — the
  driver's `virtio_disk_intr` wakes B's sleeper first; the pf device model never produces this interleaving, so a graph
  candidate exhibiting it is NOT in the published quantifier.  *Definitions.*  BURST = one START … completion span of
  the pf disk row; `pdiskProg` = the pf disk agent's step relation; `serve` = MachCSL's per-request task; `xv6ConfS` =
  the conformance premise naming the rows' programs; "trusted surface" = the text a reader must accept, §A(6).  *Why it
  matters.*  Nothing in the published CONCLUSIONS changes; the QUANTIFIER omits spec- and model-legal device
  behaviours, which an xv6 expert will ask about ("does your device complete out of order like QEMU?").  *Options.*
  **(a) keep the sequential pf program and NAME it** (§B(11) (viii)) — STRONGER than virtio and than MachCSL (excludes
  the interleaving above); sound for W4 (pf behaviours ⊆ MachCSL's); cost 0 (text); unblocks W-DISK as planned; risk:
  a reader may judge the device model unrealistic for a multi-request workload — xv6's correctness does not depend on
  order, so the omission is of device behaviours, not kernel ones.  **(b) a concurrent pf disk agent**: `pdiskProg`
  holds a LIST of residual programs (one per popped request) and a step picks any; `R-dev`/poolRel map each to a
  MachCSL `serve` task — EQUAL to MachCSL (interleaving admitted; completion order free), STILL stronger than virtio
  only by (R1)–(R3)'s one-row coupling (D51); cost M–L inside W-DISK (the `DM` list, `ediskStep`'s arms, `WeakEvDisk`'s
  per-node rules re-indexed) + M in W4 F9 (the thread map `13+k` becomes real) + the single-burst invariant of
  [R17.1] is replaced by MachCSL's `pushOk`/`taken` guards folded as in [R17.1] (now genuinely falsifiable → (α)'s
  abort or (β)'s propagation does real work); unblocks a more credible device model; risk: W-DISK grows toward XL and
  delays F9/M1.  **(c) (a) now, (b) as a named follow-up after M2** — the reviewer's recommendation: the published
  statement's SHAPE is unchanged either way; (b) replaces the pf device model under it later.
