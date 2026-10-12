VERDICT: NOT SATISFIED

# Review R32 of `notes/weak-allocproc-plan.md` (rev 35)

Reviewer: one-off adversarial advisor (advisory only: no builds, no proofs, no git or jj, no subagents).  Every cite
below was read at the working-copy tip of `../xv6iris-weak` (plan rev 35, 4,575 lines) and in `../weak-orch/`
(`parked/PROGRESS-WSCO.md`, `parked/PROGRESS-W13I.md`, `parked/PROGRESS-WSCO-spike.lean.txt`, `allocproc_WSCO_A_prompt.txt`,
`allocproc_W13I_bundle_prompt.txt`, `allocproc_revise3_extra.txt`).  Scope per the R32 brief: the rev-35 RESULT records,
the two RELAUNCH briefs (W-SCO (A) [OWN.42], W13 (I) bundle half [OWN.43]), the W-RSV launch paragraph, the 122-vs-124
census, and whether W-SCO (A) and the W13 (I) bundle half are launchable.  W8-β′'s brief is untouched.  Items (a)/(b)/(d)
of the standing brief were settled in R1–R31 and are not re-opened — EXCEPT where (d)'s vacuity check bites below.

**Sign-off.**  NO — FOUR required changes.  **[R32.1] is a soundness/vacuity defect, not record-keeping**: the named
ISA-model premise `sailCycleOrder` (`Weak/SrvwmoXv6Adequacy.lean:126-137`) is FALSE as stated, so the REGISTERED root
`Weak.srvwmoXv6M1Core` (`roots-weak.txt:20`) and `srvwmoXv6M2Core` (`PfRunUnpinned.lean:652`) are VACUOUS today (their
hypothesis `hsco` is refutable), and W-SCO (A)'s target `cycleOkAll` (`SailCycleOrderK.lean:232`) is FALSE as defined —
the brief asks the worker to prove a false proposition.  The hole is one the per-instruction census cannot see: the
instruction FETCH itself, when it hits a DEVICE address.  The fix is S–M and lives entirely in W-SCO's files; **W-SCO (A) is
NOT launchable as written** and becomes launchable the moment [R32.1]'s paragraph is in its brief (its FIRST commit).  **The
W13 (I) bundle half IS launchable** once [R32.3] (one name clash, S) is handed as a launch addendum (R30/R31 precedent).
[R32.2] and [R32.4] are S text.  Do not shrink anything.

## What was checked and holds

- **Result records vs the tree.**  `Weak.srvwmoXv6M1Core` registered: `tools/ci/roots-weak.txt:20` ✓, `baseline-weak.json`
  entry EXACTLY [R28.1]'s (three axioms; opaques = the two `resv` + `MachCSL.bootImageSealed`) ✓, `audit.sh:47` module list /
  `:54` build list ✓, `Audit.lean:93-94` comment ✓ ([R29.s3] closed ✓).  `Weak/SailCycleOrderK.lean` 631 lines ✓; its cites
  all hold: `sailCycleOrderK :92`, `good :139`, `cycleOk :219`/`kWin :224`/`cycleOkK :229`/`cycleOkAll :232`,
  `sailCycleOrderOfCycle :470`, `sailCycleOrderKOfCycle :536`, `fiOfScoK :554`, `m1HypsK :578`, `srvwmoXv6M1OfK :593` ✓; no
  `sorry` in `SailCycleOrderK.lean` or `PfRunUnpinned.lean` ✓.  `Weak/PfRunUnpinned.lean` 780 lines, byte-IDENTICAL to
  `../xv6iris-weak-w5/Weak/PfRunUnpinned.lean` (`diff` empty) and all cites hold: `fiStep :68`, `fiFold :75`, `lbFenceZeroL
  :78`, `fcutM2 :85`, `fcutM2Ifetch0 :91`, `itvStep :100`, `fcutEM2 :113`, `fokTriv :123`, `srvwmoXv6M2Premises :594` (boot
  values `∀ i, itvOf 0 i = 0` ∧ `fiOf 0 i = false` [R31.s3] ✓, `fcutEM2 cohSrc (candExec c) itvOf fiOf` closing over the
  execution [R31.s1] ✓), `srvwmoXv6M2PfRun :609` (returns the replay invariant ✓), `m2Hyps :632` (`fi := fiOfSco hsco …` ✓),
  `srvwmoXv6M2Core :652`, `srvwmoXv6M2Satisfiable :758` ✓.  The generic twins are in the tip: `execProgOk'SC`/`execProgOk'S
  :273` (`PfRunShape.lean`), `execProgOk'ST :589`/`pfRunSTC :620`/`pfRunST :629` (`TsoShadow.lean`), `contRC :526`/`contR
  :538`/`HypsC :686`/`Hyps :716` (`MachOfPf.lean`) ✓.  **[R31.1] route (i) is applied as R31 wrote it**: `fiOf` is a free
  function of `srvwmoXv6M2Premises` only; `itvStep` raises iff `lbFenceZeroL s.esLb && arm` ✓.
- **W13 (I) realization half**: `mstep.MStepIo` `WeakAxiomatic.lean:170` ✓, `projLbl (LDev …) = some (LIo …)`
  `WeakPromiseBridge.lean:542` ✓, `lbAdmin` without `LDev` `WeakAxRealize.lean:140-142` ✓.  Bundle-half cites: `gfexecConf
  :620` ✓ (the interim clause is at `:633-634`, its docstring at `:614-619`), `hemitf :253-278` ✓, `hblkQ :332` ✓,
  `hemitfStatesQ :396` ✓, `hartConffStatesQ :556` ✓, `supplyOfFconf :789` ✓, `fconfRowsPin :885` ✓, `fconfSupply :928`;
  `pdevEv` `WeakEvInst.lean:604-610` (an `LDev` label OR the disk at `.PDisk (some (DWriteDev ..))`) ✓, `pdevEvOk :1792` with
  `pdevOk := ∀ p d l p' d', pstep p d l p' d' → pdev p l p' = false → d' = d ∧ ∀ d0, pstep p d0 l p' d0`
  (`WeakPromiseFact.lean:613-614`) — "fabric-preserving AND blind" is exactly that ✓; `devQuiet` `WeakRvwmoSupply.lean:177`,
  `pdevEvFalse :209`, `pstepEvDevfree :219`, `admRunDevfree :239`, `emDevfree :360`, `emFetchImg :364` ✓.  The [OWN.43]
  criterion is recorded verbatim in §A(†) `:645-650`, §C W13 (I) `:2967-3022` and §D Q-GFDEV-contact `:3916-3940` ✓.
- **The census: 122 is right, 124 is wrong.**  `def execute_*` in `model/Lean_RV64D/LeanRV64D/InstsEnd.lean` = 122 (the
  only file with any); the dispatcher `def execute` (`InstsEnd.lean:18769`) has 122 arms; no `F*`/`D*`/`V*` clause ("no F/D/V"
  ✓; present: Zicond, Zba/Zbb/Zbs, Zimop/Zcmop, Zicbo*, shadow-stack `SS*`, `C_*`).  `PROGRESS-WSCO.md` and the
  coordinator's `allocproc_WSCO_A_prompt.txt` say 124 — fix the prompt ([R32.s5]).  `execute_FENCEI` = `sail_barrier
  Barrier_RISCV_i; pure RETIRE_SUCCESS` (`:18295-18297`) ✓; `execute_SFENCE_VMA` (`:18009`) emits no barrier (`flush_TLB`) ✓.
- **Spike sizing as recorded**: `maxHeartbeats 1000000` for `nctPmpCheck`/`nctPmaCheck`, `2000000` for `nctJal`
  (`PROGRESS-WSCO-spike.lean.txt:224-237`) — the brief's "1–2M per clause" ✓; both kits (`good` CPS `sco_auto`, additive `ncT`
  `nct_auto`, `ncTRUntilFuelM` for the fuel loops) are in the spike ✓.
- **§D format**: Q-SCO-words (`:3895-3915`) and Q-GFDEV-contact (`:3916-3940`) carry *Spec (FIRST)*, plain language, a
  concrete example, definitions, why it matters, and per-option marks/costs ✓ (the 2026-10-10 format).  Q-FIARM `:3941-3950`
  updated ✓.  §A(6) `:507-509`, §B(11) `:1331-1338` say "a THEOREM after W-SCO (A)" ✓ — but see [R32.1]: the surrounding claim
  "FAITHFUL (true of the model by inspection …)" is what is wrong.
- **Two-halfword fetch** (`Fetch.lean:252-280`, second `fetch_bytes pc (pc+2) 2` at `:217-226`, `Ext_Ziccif` `Extensions.lean:528`)
  as the plan describes ✓.  `riscvStep`: `MachCSL/Lang.lean:241-243` (see [R32.4]).  `Weak.lean:635-636` imports BOTH new
  files (see [R32.2]).

## REQUIRED changes

- **[R32.1] `sailCycleOrder` is FALSE as stated (M1 and M2 are vacuous today), and `cycleOkAll`/`cycleOkK` are FALSE as
  defined — W-SCO (A)'s deliverable (1) cannot be proved; re-shape the premise and the tree obligation around the boot PMA
  table.**
  *What is wrong (evidence).*  (1) The pf event instance labels EVERY read at a device address `LDev`, whatever its access
  kind: `pnodeStep`'s `.memRead` arm tests `devAddr req.pa` FIRST (`WeakEvInst.lean:315-321`; `devAddr pa := pa.toNat <
  0x80000000`, `MachCSL/Dev/Fabric.lean:125-126`); only the `¬ devAddr` branch produces `LIFetch` (`:322-330`).  So an
  INSTRUCTION FETCH from an MMIO address leaves no cycle label (`lbCyc` is `LInstr`/`LIFetch` only, `SrvwmoXv6Adequacy.lean:108-112`).
  (2) `sailCycleOrder :126-137` is closed over EVERY `σ0 : WGState` with NO boot hypothesis — `epsInit σ0` seats each hart at
  `σ0.wgregs c` (`WeakEvCapstone.lean:1026-1027`), i.e. an ARBITRARY register file (PC, privilege, `pma_regions`, …), and
  `efInit σ0.wgdev` an ARBITRARY fabric.  Refuting run: hart `cpu` with `cur_privilege = Machine`, `pmpcfg = 0`, `mie = 0`,
  `pma_regions` a list marking the PLIC region executable, `PC` = a PLIC per-context enable word (4-aligned), and `σ0.wgdev`'s
  PLIC `enable c w = 0x12000073`.  Steps: boundary `.pure` → `LInstr` (`WeakEvInst.lean:297-302`); `try_step` → `run_hart_active`
  → `dispatchInterrupt` none → `fetch` (`Fetch.lean:252-258`: aligned, `Ext_Ziccif` → one `fetch_bytes … 4`) → `translateAddr`
  in M-mode (identity) → `mem_read InstructionFetch` → `pmpCheck` passes (M-mode, no entry) → `pmaCheck` reads `pma_regions`
  (`Mem.lean:265`) and returns `attributes.executable = true` (`:274`) → the `.memRead` node issues → `pnodeStep`: `devAddr` →
  `devRead` → PLIC `read … = some (p.enable c w, p)` (`MachCSL/Dev/Plic.lean:130-131`) → label `LDev .rd …`, `w = 0x12000073` →
  `F_Base w` (low bits `11`, not RVC) → `ucAfterFetch` → the node `.instrAnnounce 32 w` with `sfAnnB 32 w = true`
  (`WeakEvLang.lean:421-422`) is at the head.  `sailCycleOrder`'s second clause (`:136-137`) demands `lastCyc (hartAgent cpu) st =
  some (.LIFetch base tvs)`; the step list's latest own cycle label is the boundary's `LInstr`.  FALSE.  Hence `hsco` is
  unsatisfiable, `srvwmoXv6M1Core`/`srvwmoXv6M2Core`/`machRunOfPfRun`'s `fi`-consumers are vacuous; `srvwmoXv6M1Satisfiable
  :733` certifies the PREMISE SET, not `hsco`.  §B(11)'s "FAITHFUL (true of the model by inspection — R21's grep: no
  `execute_*` … uses `InstructionFetch`)" (`:1327-1329`) looked at `execute`, never at `fetch` to a device address.  (3) The
  tree obligation has the SAME hole independently of any device model: `good`'s `.memRead` arm (`SailCycleOrderK.lean:146-150`)
  sends a `devAddr` read to the second conjunct — "any answer `v`, SAME phase"; `.regRead` is "any answer" (`:156`); `.instrAnnounce`
  requires `ph = .fetch` when `sfAnnB` (`:153-155`).  The tree path above (arbitrary `pma_regions` answer, arbitrary MMIO
  answer `0x12000073`) is therefore a path of `riscvStep tick` on which `good … .instr` is FALSE: `cycleOkAll` (`A = True`) and
  `cycleOkK` (the fetch filter `A` is not consulted on the device arm) are both refutable.  `sailCycleOrderOfCycle :470` and
  `sailCycleOrderKOfCycle :536` are sound but their premises are false.  (4) What makes the statement TRUE for THIS platform:
  the boot PMA table `MachCSL/Platform.lean:199-250` (`bootPMA`) has three regions — `[0x1000, 0x2000)` IOMemory `executable :=
  false` (`:205`), `[0x0200_0000, 0x1200_0000)` IOMemory `executable := false` (`:225`; CLINT/PLIC/UARTs/virtio), `[0x8000_0000,
  0x8800_0000)` MainMemory `executable := true` (`:245`); any other address matches no region and `pmaCheck` throws an access
  fault (`Mem.lean:265-268`).  So under `pma_regions = bootPMA` an `InstructionFetch` `.memRead` node can only carry `pa ≥
  0x80000000`, i.e. `devAddr = false`, and the model never writes `pma_regions` (no `writeReg pma_regions` outside
  init/config).  `wbootFacts σ0` (`WeakLang.lean:482-490`) pins every hart's register file to `bootRun (bootProg (bootHid c)
  bootPMA) f₀` (`:488`), whose output satisfies `bootPost` with `pma_regions = pma` (`MachCSL/BootInitModel.lean:29-41`;
  `bootRun_bootLand` `BootReset.lean:118-123`).  M1 and M2 BOTH have `wbootFacts σ0` in their premise sets
  (`SrvwmoXv6Witness.lean:599`, `PfRunUnpinned.lean:596`), and `sailCycleOrderK :92-93` already assumes it.
  *Spec (FIRST).*  RVWMO and riscv.cat order memory operations and say nothing about in-cycle event order (Q-FIARM);
  Zifencei is silent; the PMAs are exactly where the privileged spec puts EXECUTABILITY: a PMA attribute per region
  ("Physical Memory Attributes": I/O regions may or may not support instruction fetch; the platform decides), which the Sail
  model checks in `pmaCheck` (`Mem.lean:263-274`) from the `pma_regions` register — a PLATFORM table, not architectural state.
  Pinning that table to the modelled board's (`bootPMA`) is FAITHFUL to the Sail model AS BOOTED on this platform (it is what
  `wbootFacts` already says); it is a platform hypothesis, not an ISA strengthening (another platform with an executable I/O
  region would need its own table).  Option (γ) below is WEAKER than Sail-with-arbitrary-registers but EQUAL to Sail from
  reset on this platform.
  *Exact change — three paragraphs, W-SCO (A)'s FIRST commit (S–M ≈ 200–400 lines; files `SrvwmoXv6Adequacy.lean`,
  `SailCycleOrderK.lean`, `PfRunUnpinned.lean`, `MachOfPf.lean` header text; all W-SCO's per its prompt).*  (i) **Restate
  `sailCycleOrder` under the boot hypothesis** — recommended **(α)**: `∀ fok σ0, wbootFacts σ0 → ∀ st c, pfRunST … → …`
  (the shape `sailCycleOrderK :92-93` has); alternative **(β)**: the weakest sufficient fact `∀ c, (σ0.wgregs c) pma_regions
  = bootPMA` (then the never-written invariant is still needed, so (β) saves nothing); `fiOfSco :176` takes `hb : wbootFacts
  σ0`; `m1Hyps :218` / `m2Hyps :632` / `fiOfScoK :554` / `m1HypsK :578` take `hb` (M1/M2 have it in `hP`); `srvwmoXv6M1Core
  :289`'s and `srvwmoXv6M2Core :652`'s `hsco` becomes the restated premise — statement TEXT changes, name and
  `baseline-weak.json` entry do not (registration by NAME, [R21.4]/§B(12); the premise got WEAKER, the theorem STRONGER).
  (ii) **Give `good` a register filter**: `good A R Q ph m` with `R : ∀ r : Register, RegisterType r → Prop`; `.regRead r, k ↦ ∀
  v, R r v → good … (k v)`; `.regWrite r v, k ↦ r ≠ pma_regions ∧ ∀ u, good … (k u)` (so the run invariant below is
  preserved — the model never writes `pma_regions`, the walk proves it); `Rboot r v := r = pma_regions → v = bootPMA`
  (dependent equality on `RegisterType pma_regions = List PMA_Region`, `Defs.lean:1553`); `cycleOkBoot := ∀ tick, good (fun _ _ =>
  True) Rboot (fun _ _ => True) .instr (riscvStep tick)` REPLACES `cycleOkAll` as deliverable (1) (`cycleOkAll`/`cycleOkK` are
  deleted or kept as records with a header note "FALSE — fetch from MMIO; superseded"); `invStep :359`'s `regRead` case
  (`:335-338`) instantiates `v := rs r` from the new run invariant "every hart's `rs pma_regions = bootPMA`" (base: `wbootFacts
  σ0` + `bootPost`; step: `pnodeStep`'s `regWrite` arm `rs.set r v` with `r ≠ pma_regions` from `good`); `invRun :430`,
  `scoOfInv :450`, `sailCycleOrderOfCycle :470 : cycleOkBoot → sailCycleOrder` (restated), `sailCycleOrderKOfCycle :536` adapt.
  (iii) **The PMA lemma the cycle needs** (new, S, `bv_decide`/`decide` over the literal table): `matching_pma_region bootPMA
  pa w = some r → r.attributes.executable = true → 0x80000000 ≤ pa.toNat` and `… = none → pmaCheck throws` (`Mem.lean:265-268`);
  hence under `Rboot` every `InstructionFetch` `.memRead` node of `fetch_bytes` (`Fetch.lean:217-226`, both halfwords) has
  `devAddr = false` and `good`'s FIRST arm applies — the device arm is never reached by an ifetch.  This is the ONE place where
  route (A)'s footprint walk must be PRECISE about a value (the PMA result), not just about event kinds; the brief must say so
  (the `pmaCheck` lemma of the spike, `nctPmaCheck`, is a footprint lemma and does NOT give it).  (iv) **Records**: §C top and §C
  W5's "M1 DONE" gain "**VACUOUS until [R32.1] lands** (`hsco` refutable: fetch from MMIO of an SFENCE.VMA word under an
  arbitrary `pma_regions`); the registered entry is unaffected (axioms/opaques), the theorem's content is restored by W-SCO (A)'s
  first commit"; §A(6) `:507-509`, §B(11) `:1327-1331`, Q-FIARM `:3941-3950` replace "FAITHFUL (true of the model by inspection
  …)" with "TRUE of the model FROM THIS PLATFORM'S RESET (the boot PMA table forbids instruction fetch from I/O regions); FALSE
  over arbitrary register files — the premise is stated under `wbootFacts σ0` [R32.1]"; `SrvwmoXv6Adequacy.lean`'s header and
  `MachOfPf.lean`'s `fi` docstring (`:679-680`) say the same (TEXT).  (v) The brief's deliverable (2) `sailCycleOrder_holds :=
  sailCycleOrderOfCycle cycleOkBoot_holds` and (3) `srvwmoXv6M1` stand; acceptance's "no hypothesis, no restriction on the
  fetched word" becomes "no hypothesis beyond the restated premise's `wbootFacts σ0`; no restriction on the fetched word".
  Options (γ) "make `pnodeStep`'s device arm refuse `akIfetch` reads" (M: `WeakEvInst.lean:315-321` + every W2/W4 row that
  cases on the arm; EQUAL to Sail-from-reset, WEAKER than Sail-with-arbitrary-registers; not needed once (α) is in) is the
  recorded alternative.  **Launch rule**: W-SCO (A) launches when this paragraph is in its brief (addendum form is fine); its
  first commit is (i)–(iii); the per-instruction walk follows.
- **[R32.2] Record the merges: `Weak/PfRunUnpinned.lean` and `Weak/SailCycleOrderK.lean` are IN THE TIP and IMPORTED.**
  *What is wrong (evidence).*  `Weak.lean:635` `import Weak.SailCycleOrderK`, `:636` `import Weak.PfRunUnpinned`; the tip's
  `PfRunUnpinned.lean` is identical to w5's.  The plan says otherwise at: header `:16-19` ("DONE in workspace `../xv6iris-weak-w5`
  … not yet in the shared default checkout"), `:24` ("`SailCycleOrderK.lean` 631 lines, not registered, not imported"), §C top
  `:1469-1471` ("DONE in workspace `../xv6iris-weak-w5`, MERGE PENDING"), the W-SCO launch paragraph `:1488` ("not registered, not
  imported"), deliverable (4) `:1495` ("imported from `Weak.lean`" as work to do), rebase surface `:1499-1501` ("with W5d's w5 …
  which w5 keeps as the trivial-`fcutT` ABBREV"), the W13 (I) paragraph `:1525` ("NONE with W-SCO (A) or W5d's w5"), the W-RSV
  paragraph `:1531-1533` and §C W-RSV `:2801-2803` ("once w5 merges"), WAITS `:1534` ("M2 CLOSE for w5's merge"), §C W-SCO
  `:2537` ("not registered, not imported"), §C W5d `:2851-2853` ("NOT in the shared default checkout at this revision — merge
  pending … The merge of w5 into the default is the coordinator's step").
  *Exact change.*  At each site: "MERGED in the tip (`Weak.lean:635-636`); `SailCycleOrderK.lean` imported, NOT registered;
  `PfRunUnpinned.lean` imported, NOT registered (M2 closes after W-RSV and [R32.1])"; delete the "once w5 merges"/"coordinator's
  step" clauses; W-SCO deliverable (4) drops "imported from `Weak.lean`"; the two rebase-surface sentences become "W5d: MERGED,
  no surface".  S text; FAITHFUL (record only).
- **[R32.3] W13 (I) deliverable (5) "`emFetchImg → emZifencei` RENAME only" collides with a merged declaration.**
  *What is wrong (evidence).*  `Weak/GraphFetchSpike.lean:312` already declares `Weak.emZifencei (G : Gexec) (C : Nat → Geid →
  Prop) (i : Nat) (em : Hemission)` (namespace `Weak`, `:93`; imported by `Weak.lean:626`; kept merged per [OWN.10]).
  `WeakRvwmoSupply.emFetchImg (im : Image) (em : Hemission)` (`:364`, namespace `Weak`, `:111`) renamed to `emZifencei` is a
  second `Weak.emZifencei` — a duplicate declaration (at the spike's definition if it imports `Supply` transitively, else at
  `Weak.lean`'s import).  `:1520` and `:2974` ("`emZifencei := emFetchImg` at the use sites, content unchanged") cannot be executed
  as written.
  *Exact change (one clause at both sites).*  "(5) the slot rename `emFetchImg → emZifencei` [R28.s5] ALSO renames the G0
  spike's 4-ary `emZifencei` (`GraphFetchSpike.lean:312`) to `GraphFetchSpike.emZifencei` (the file-qualified Lean-only
  convention) in the same commit, so W5d-G G1 later REPLACES the 2-ary slot's content with the spike's definition; alternatively
  keep `emFetchImg` and leave the rename to G1 — worker's choice, say which in the header."  S; FAITHFUL (names).  The bundle
  half is launchable with this as an addendum.
- **[R32.4] The W-SCO (A) brief's description of the instruction-independent cycle is wrong at the top and incomplete.**
  *What is wrong (evidence).*  `:1490-1493` says "`riscvStep tick` = prelude/`dispatchInterrupt` → `fetch ()` → `instr_announce`
  → decode → `execute` → finish/`try_step`'s handlers".  `riscvStep tick := try_step 0 false; if tick then tick_clock () else pure
  ()` (`MachCSL/Lang.lean:241-243`): the brief omits **`tick_clock`** (`Platform.lean:549-554`: `mcycle`/`mtime` bumps and
  `clint_dispatch false` — register-only, but a footprint lemma nonetheless), **`run_hart_waiting`** (`Step.lean:230-242`, the
  WFI-parked body `ucBody` dispatches to, `UCycleDefs.lean:61`), the **`ExecuteAs` redirect** (`uxaExecAs`
  `MachCSL/UExecAluGpr.lean:281-284`: `execute ast` then `execute i` on `.ExecuteAs i`; 46 `ExecuteAs` sites in `InstsEnd.lean` —
  the compressed clauses — so the ∀-clause lemma is applied TWICE per cycle and the `C_*` lemmas are one-liners that reduce to the
  base clause), `ext_pre_step_hook`/`ext_post_step_hook`, `ucPrelude`'s `should_inc_minstret` and `ucEpilogue`'s PC/`minstret`
  bump (`UCycleDefs.lean:55-59`, `:123-130`).  A brief that claims a census must name the whole decomposition.
  *Exact change.*  Rewrite the (c) clause: "`riscvStep tick = try_step 0 false >>= λ_, (if tick then tick_clock () else pure ())`
  (`Lang.lean:241-243`); `try_step` (`Step.lean:416-440`) = `ext_pre_step_hook`, `minstret_increment`, then `run_hart_waiting`
  (parked hart) or `run_hart_active` = `ucDispatch` → `fetch ()` (one or two `fetch_bytes`, `Fetch.lean:217-226,252-280`) →
  `ucAfterFetch` (`UCycleDefs.lean:169-210`: `instr_announce` (phase `.instr`, or `.fetch` kept at the SFENCE marker), pure decode,
  `is_landing_pad_expected`, `nextPC`, `uxaExecAs` = `execute` + one `ExecuteAs` redirect) → `ucFinish`'s arms (interrupt trap,
  fetch fault, execute trap, illegal, wait, retire) → `ucEpilogue`; then `tick_clock` (`Platform.lean:549-554`).  Footprint lemmas
  for ALL of these; `pmaCheck` PRECISE per [R32.1] (iii)."  S text; FAITHFUL.

## SUGGESTIONS

- **[R32.s1] Stale `MachOfPf.lean` and `SrvwmoXv6Adequacy.lean` line cites in the rev-35 text** (read before the W5d merge
  moved the file): `Hyps.fi :677` → the `fi` field is `HypsC.fi :704-715` (`HypsC :686`, `Hyps :716`); `noWriteOfPristine :2913`
  → `:2982`; `fetchIsImage :2940` → `:3009`; `cutOfPristine :2959` → `:3028`; `machRunOfPfRun` → `:2928`; the application site
  `:1102` is right; `sailCycleOrder :113` (several sites) → `:126`; `fiOfSco :163` → `:176`; `m1Hyps :203-213` → `:216-227`;
  `fiArmLastCyc :135` → `:148`.  Cosmetic.
- **[R32.s2] The "demotes" gloss is not in `roots-weak.txt:20`.**  `:1497` says "`roots-weak.txt:20`'s gloss 'W-SCO demotes it for
  kernel text' → 'proved by W-SCO (A)'"; `roots-weak.txt:20` reads "premises … + `sailCycleOrder` [OWN.35] (SrvwmoXv6Adequacy)"
  — the phrase is `SrvwmoXv6Adequacy.lean:18`'s (and `:80` names `sailCycleOrderK_holds`, like `PfStepTsoView.lean:67`).  Point
  the brief at those two header lines; `roots-weak.txt:20` needs only "(THEOREM after W-SCO (A))".  Cosmetic.
- **[R32.s3] `blockTouches em k` has ONE viable carrier.**  `:1512-1514` offers "a per-item quietness beside the two endpoints,
  or read off the block's step list".  `Hemission.emItems` holds labels only (`WeakRvwmoConf.lean:721`), and `pdevEv p l p'`
  is STATE-aware (`.PDisk (some (DWriteDev ..))`, `WeakEvInst.lean:608-610`), so nothing can be read off the items; the carrier
  is a third per-item function `tch : Nat → Bool` beside `dvi dvo` in `hemitf`/`hartConff` (`:253,:278`), fixed by `HFone`/
  `HFpair`'s premises (`har`'s admin run + `hre`/`hst`), existentially quantified in `gfexecConfIO` like `dvi dvo`.  Say so, and
  add `gfexecConfRen :290`/`gfexecConfHull :332` (`WeakRvwmoFabInd.lean`) to the consumers list (they transport the per-row
  clauses; the file is already listed).  S.
- **[R32.s4] Say who states `srvwmoXv6M2`.**  The coordinator's prompt gives W-SCO (A) "the M2 twin `srvwmoXv6M2 :
  <srvwmoXv6M2Core without hsco>` (`PfRunUnpinned.lean:652`)"; the plan's W-SCO paragraph lists only `srvwmoXv6M1` and leaves
  M2's `hsco` to "M2 CLOSE" (`:1534-1535`, `:2871-2873`).  Either is fine; make them agree (one clause in deliverable (3)).
- **[R32.s5] Fix the coordinator's W-SCO prompt**: "124 clauses" → 122 (`def execute_*` and dispatcher arms both 122); add
  [R32.1]/[R32.4] verbatim.  Not a plan edit.
- **[R32.s6] Cites in the W13 (I) paragraph**: the interim `.PDisk` clause is `WeakRvwmoFab.lean:633-634` (`:615-618` is its
  docstring); `GraphFabResidue.gfIoDev :172` → `:176`.  Cosmetic.
- **[R32.s7] W-RSV `:2797-2800` "13 sites"**: the reservation-guard grep over the tip's `MachOfPf.lean` now returns 16 lines
  (the twins); the listed line numbers predate W5d/W-SCO.  Keep "grep `othersReserve`/`anyReserve`/`resv`" as the instruction.
- **[R32.s8] Keep `PROGRESS-WSCO.md` honest**: its "What remains is ONE closed proposition about the Sail model, `cycleOkK`"
  is now known FALSE ([R32.1] (3)); the relaunch brief should tell the worker to rewrite that section first.

## Owner questions the plan is missing

- **Q-SCO-PMA (new; raised by [R32.1]).  What may the Sail-cycle fact assume about the platform's memory map?**
  *Spec (FIRST).*  RVWMO and riscv.cat order loads and stores; they say nothing about the order of fetch, announce and execute
  inside one instruction (Q-FIARM).  Zifencei says what `fence.i` orders, not whether a hart may fetch from a device.  The
  privileged spec's PMAs make EXECUTABILITY a per-region PLATFORM attribute (an I/O region may or may not support instruction
  fetch); the Sail model in this tree checks it in `pmaCheck` (`model/Lean_RV64D/LeanRV64D/Mem.lean:263-274`) from the
  `pma_regions` register, which the board sets at reset (`MachCSL/Platform.lean:199-250` `bootPMA`: the two I/O regions
  `executable := false`, RAM `executable := true`; `BootInitModel.lean:41`) and no instruction ever writes.  The Sail model with
  OTHER register contents can fetch from a device; the model as booted on this board cannot.
  *Plain language.*  The proof needs "after a hart announces an instruction it does not fetch, and an `sfence.vma` announce
  comes right after its own fetch".  That is true when every fetch comes from RAM.  If a hart could fetch its instruction from a
  DEVICE register (the PLIC, a UART, the virtio window), the fetch would be an I/O read, not an instruction fetch, in our
  graph alphabet — and the fact would be false.  On this board the memory map forbids executing from device regions, so the
  fact holds — but only if the theorem is allowed to KNOW the board's memory map.
  *Example.*  Hart 0, machine mode, no PMP entries; some earlier code (or the initial device state) left `0x12000073` — the
  encoding of `sfence.vma` — in a PLIC enable word at `0x0c002080`; hart 0 jumps there.  With the board's map the fetch takes an
  access fault (no fetch happens).  With a map that marks the PLIC executable, the fetch reads the device, announces
  `sfence.vma`, and the latest "cycle label" of hart 0 is the previous instruction boundary, not a fetch — the fact fails.
  *Definitions.*  `sailCycleOrder` (`SrvwmoXv6Adequacy.lean:126`) = that fact, stated over every pf run from a boot
  configuration `σ0`; `wbootFacts σ0` (`WeakLang.lean:482`) = "`σ0` is the board after reset" (image, empty log, each hart's
  registers as the boot program leaves them); `pma_regions` = the Sail register holding the memory map; `pnodeStep`
  (`WeakEvInst.lean:294`) = how one Sail event becomes a graph label; `good`/`cycleOkAll` (`SailCycleOrderK.lean:139,232`) = the
  tree-level obligation W-SCO (A) proves.
  *Why it matters.*  Today `sailCycleOrder` is quantified over EVERY `σ0`, so it is false and M1/M2 are vacuous; W-SCO (A) as
  briefed would try to prove a false tree fact.  The published theorem must say which platform facts it relies on.
  *Options.*  **(α) RECOMMENDED — state the fact under `wbootFacts σ0`** (M1/M2 already assume it; `sailCycleOrderK` already
  does): FAITHFUL to the Sail model as booted on this board; in practice the trusted base gains nothing new (the boot table was
  already part of `wbootFacts`); cost S–M (W-SCO (A)'s first commit, [R32.1]); unblocks W-SCO (A); risk none.  **(β) state it
  under only `∀ c, (σ0.wgregs c) pma_regions = bootPMA`**: FAITHFUL, minimal, same proof work plus the never-written invariant
  (needed in (α) too); cost = (α); gains generality nobody needs.  **(γ) change the pf event instance so an instruction fetch at
  a device address is not a step** (`pnodeStep`'s device arm `WeakEvInst.lean:315-321` refuses `akIfetch`): EQUAL to the model from reset, WEAKER than the
  Sail model with arbitrary registers (removes a behaviour the model has); cost M (`WeakEvInst.lean:315-321` + the W2/W4 rows
  that case on the arm); keeps `sailCycleOrder` closed over all `σ0`; risk: a second place where the pf model is narrower than
  Sail, to be named in §B(11).  The plan can adopt (α) without a ruling (it is the hypothesis M1/M2 already carry); the question
  is listed so the owner sees why the premise's text changes.
