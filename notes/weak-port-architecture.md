# Weak-memory port: architecture recommendations (A–E)

*Design-advisor note, 2026-10-05.  Inputs: `notes/weak-port-map.md`, `notes/weak-port-iris-gaps.md`,
the Rocq weak line at `xxvzwolszwmp` (`../xv6iris-spinlock/iris`, design notes under
`claude-notes/design/weak-memory*.md`), and this tree (`MachCSL/Lang.lean`, `TsoMem.lean`, `Wp.lean`,
`BootRun.lean`, `URunRW.lean`, `DecodeBridge.lean`, `UCycleDefs.lean`, lean-sail `Outcome`).  Every count
below was re-checked against the sources; where a claim depends on something I could not run (the Sail
backend, the GCP VM) it is marked CHECK.*

## A. Base semantics — recommendation: (i) with a derived evaluator, not (ii)

**What the 204 `RiscvExec` importers actually use.**  89 of them import it and use *no* name from it
(boilerplate header).  88 use the `exec` API, and almost always in one of two shapes: the leaf
certification `exec_eff m s = Some (tt, s', es)` of `WeakCert`/`WeakEff` (63 files; `exec_eff` is the
weak tier's *own* instrumented interpreter, "an arm-for-arm mirror of `exec`"), and the J0 ledger method
(`AxEpiProbe`, `AxEpiLedger*`, `AxSym*`, `AxSpin*`: closed Boolean equations about one concrete
`riscv_step`, discharged by `vm_compute`, through the weak tier's own evaluators `erd`/`ewr`/`epure`/
`node_step`/`drive`).  The SC `exec_*` library they compose with (`WpMmodeLeafBase.exec_execute_LOAD_8_gpr`,
`RiscvFetchExec.exec_read_ram_plain_4`, `RiscvTryStep.exec_pmpCheck_machine_none`, the `WpGprCsr*`
leaves — 127/142/133 importers) is what is genuinely MISSING in Lean; `exec` itself is 50 lines.

**What the weak tier takes from the base language.**  `RiscvLang` names used: `riscv_step` (149 files),
`mstate`/`regstate` (231/169), `register_lookup`/`set_reg` (209/110), `try_step` (62), `dev_state` (54);
`prim_step`/`mexpr`/`gstate` in 3–4 files.  The AxSL tier (`AxOpsem` → `AxWp` → `AxLifting` →
`AxAdequacy` → `AxTierA*` → `AxSpin*`) does **not** use Iris's `Language`/`wp` at all: `AxWp.wp` is its own
fixpoint over `iProp`, its adequacy is its own phase-1/phase-2 argument, and its thread is
`(pexv6, k)` stepped by `WeakEvInst.pnode_step` (58 files) — the program half of the event language's
step, which sees only the hart's residual Sail monad, its register file, the instruction bits and the
device fabric.  Only `WeakEvLang` → `WeakEvAdequacy`/`WeakEvCapstone` instantiates Iris `language`, over
*its own* `eexpr`/`wgstate`.  So `MachCSL.primStep` is irrelevant to every root; the base the weak tier
needs is the Sail monad, the register file, `riscv_step`, the devices, and a deterministic evaluator.

**Recommendation.**  No second semantics.  The weak tier sits on `MachCSL.Lang`'s *constructs* and
defines its own language instance, exactly as Rocq does over `RiscvLang`:

| Rocq layer | Lean construct (reuse) or new file |
|---|---|
| `RiscvLang.{CPU, riscv_step, try_step, regstate, register_lookup, set_reg, power_fork, boot_image, reset_regs}` | `MachCSL.{CPU, riscvStep, Functions.try_step, RegFile, f r, RegFile.set, powerFork, bootImage, bootFacts/bootLand}` — `riscvStep tick` is byte-for-byte Rocq's `riscv_step tick` |
| `RiscvLang.{uart,plic,disk}_step`, `DevModel.dev_read/dev_write/dev_state` | `MachCSL.Dev.{devRead, devWrite, DevStates}`; the weak language's `EUart`/`EPlic` arms call these |
| `VirtioProg.DM`/`virtio_prog` (M5 disk-as-program; `DRead/DWrite/DFence/DWild`) | **port as `Weak/VirtioProg.lean`, Rocq-literal**.  Lean's `Dev.DevLang` has no fence op and its `dmaRead/dmaWrite` carry no weak-memory labels; unifying with `MachCSL/Dev/Virtio.lean` would be a MachCSL change for no root — record as a later cleanup |
| `WeakMem` (pure, stdpp-only, 3001 lines) | `Weak/WeakMem.lean`, pure; keys `BitVec 64`/`Nat` directly, so `WeakInterp`'s `pa_z`/`z_pa` address seam collapses to identities |
| `WeakInterp.{classify, wm_class_of, wrun, wexec}` | `Weak/WeakInterp.lean`; `classify` over `MachCSL.AK` reusing `akExcl/akAcq/akIfetch/akPlain` from `TsoMem.lean`; `wrun`/`wexec` ported (they are in the AxSpin cone via `WeakSailLTS*`/`WeakRvwmoConf`) |
| `WeakLang.wgstate`, `WeakEvLang.eexpr` (`Sail gen cpu m fn | EUart | EDisk | EPlic | EPower`), `ecycle_step` | `Weak/WeakLang.lean`, `Weak/WeakEvLang.lean`: same constructors; `regs : CPU → RegFile`, `dev : DevStates`; one arm per `Outcome` constructor (announce arms: §B) |
| `RiscvExec.exec`, `exec_bind_Some`, …; `ExecCommon` | **new `Weak/Exec.lean`**: `exec`/`execEff` structural on `FreeM` (no fuel), bind lemmas by induction, plus ONE bridge `exec_of_runRW : runRW … = some … → exec … = some …`.  Every `exec_*` fact a weak file consumes is then derived from Lean's walk equations (`runRW`/`runRead` by `rfl`, D50) or by `decide +kernel` at a closed state — not re-proved from scratch |
| `RiscvPtsto.{reg_pointsto, mstate_interp, power_interp, kernel_text, addr_is_ram}` | `MachCSL.Resources` (`↦ᵣ[cpu]`, `machInterp`, `powerInterp`), `MachCSL.Ctx.imgBytes`, `ramBytes` |
| `AxOpsem/AxWp/AxLifting/AxAdequacy` | `Weak/Ax*.lean`, literal; `axirisG`/`weakGS`/`axannotGS` become classes over `GF` with `ElemG` fields (one capacity instance per camera) |

**TSO.**  `MachCSL.TsoMem` is a sibling view machine (store order, per-hart floor, forwarding by author,
reservations, non-coherent `itv`) but it has no per-register dependency views (`w_regv`/`w_ldv`/`w_tbank`),
no message class and no parked fence; `WeakMem` is strictly richer.  It is **orthogonal**: leave it
untouched, reuse its `Agent/CPU/NCPU`, `AK` classifiers, `nthByte`, `ramBytes/devBytes`.  A theorem
"every `TsoMem` run is a promise-free run" would tie the tiers, but Rocq never had it — out of scope.

## B. The SYMBOLIC model change — necessary; blast radius small and mechanical

**Where it bites.**  Lean's model has the announcements as pure `let _ : Unit := sail_instr_announce h`
(`model/Lean_RV64D/LeanRV64D/Step.lean:341,378`, right after the fetch in `run_hart_active`) and
`sail_branch_announce xlen pc` in `set_next_pc` (`PcAccess.lean:213`); lean-sail's `Outcome` has no
announce constructors.  In Rocq-weak, **`BranchAnnounce` is already silent and label-free**
(`WeakEvLang.v:1026`: the `LCtrl` label is emitted at the `nextPC` write), so it is needed by nothing.
**`InstrAnnounce` is load-bearing**: `WeakEvInst` banks the announced bits (`wgib`, D3) and emits the
second `LInstr` there; `WeakDeps.deps_of_bits` decodes RVWMO operand roles from those bits; `AxFetch`,
`AxOpsem`, `AxSym*`, `AxIntr*`, the leaves and shape kits step over the node (71 files mention it).

**Alternative without the model change** (reading the opcode off the ifetch `memRead` answers; both
models tag fetches `AK_ifetch`): the bits can be banked from the two halfword answers, but the second
`LInstr` reset exists because the fetch's own read view must not leak into `w_ldv` (that would add
dependency edges RVWMO does not have — the unsound direction).  Without an announce node there is no
event between the fetch and decode's first `regRead` to carry that reset, so the fix is either a
fetch-flagged load label (a change to `WeakPromise.wlabel`, rippling through the 20k-line Layer-1
robustness tier) or a program-half hack.  Not worth it.

**Recommendation: regenerate with `-D SYMBOLIC`, as Rocq did, as Phase-0 commit #1.**  Scope:

1. `vendor/lean-sail/Sail/ConcurrencyInterfaceV1.lean`: `Outcome.instrAnnounce (n) (w : BitVec n)` and
   `branchAnnounce (n) (pc : BitVec n)`, `ret := Unit`; emitting primitives.  CHECK whether the Sail Lean
   backend maps the `instr_announce`/`branch_announce` externs; if not, define them in
   `model/Xv6Extras.lean` (as the reservation hooks are), plus the no-op `mark_register`.
2. `tools/regen_sail_model.sh`: add `-D SYMBOLIC` at the **same** `SAIL_RISCV_REV`; review `git diff model/`
   — it must be the announce sites, `register_bool`'s two new `__monomorphize_*` registers and nothing
   else.  The two registers enlarge `Register`, hence `RegFile`: boot-chain lemmas (`BootRun`, `BootReset`,
   `BootPeel`, `ArchReset`, `bootFacts`) and `tools/gen_model_facts.py` output must be regenerated;
   `tools/tcb/expected.json` moves.
3. `MachCSL/Lang.lean`: two silent `evStep` arms (`σ' = σ`), `blockedStep` false, `hartObs` silent by
   computation.  `Wp.lean`: two `swp_silent` instances.  `Tactics.lean`: `swp_run` dispatches them;
   `sail_norm` unchanged.  `BootRun.bootRun`, `DecodeBridge.runRead`, `URunRW.runRW`: one skip arm each
   (`URunRW`'s header already lists "the announce events" among the silent ones).
4. SC proof sites that step through the two points: the post-fetch stretch (`UCycleDefs.ucAfterFetch`,
   `UCycle.uc_afterFetch_*`, `WpCycle*`/`WpStages*`, `Xv6/UkFetchArm`) and the five `set_next_pc`
   unfolders (`UCycleDefs`, `UTrap`, `UExecCtlBase`, `Xv6/UserStepTrap`, `Xv6/UkArms`) plus the
   control-flow leaves reached through `swp_run` (`WpMmodeCtl`, `WpSmodeCtl/Jalr/Sret`, `WpTrap`,
   `WpMmodeMret`).  If the walkers and the dispatcher skip the events generically, each is a one-line fix
   or none.  Estimate 1–3 agent-days plus one full rebuild; verify with `lake build Xv6 MachCSL` and the
   audit/tcb steps.

**Drift item zero (CHECK).**  The Rocq weak line pinned sail-riscv `c32fbf41…`; Lean pins `070832a1…`.
The weak files' closed model facts (ledgers, event counts, `exec_eff` traces at concrete states) were
computed on the former.  Diff the fork between the two revisions before Phase A; any change to
`fetch`/`step`/the walker changes event streams and hence the certificates.

## C. Drift policy

1. **Always target the Lean (09-30) module.**  Never port an 08-09 SC file; `Weak/` imports `MachCSL`/`Xv6`
   names only.
2. **Names vs statements.**  The weak files' SC dependencies are overwhelmingly on *definitions* (types,
   interpreters, points-tos, `CPU`, the model) whose Lean twins exist (map §2), and on the `exec_*` leaf
   library, which is the one real hole: fill it once in `Weak/ExecLib.lean` from the walk equations via
   `exec_of_runRW` (§A), re-deriving exactly the names the weak sources consume (script the list).
3. **When a weak proof depends on a changed SC statement**, restate over the Lean vocabulary, keep the weak
   theorem's conclusion unchanged up to renaming, and record it in the header's **Drift** list
   (`Rocq 08-09 X → Lean Y`).  Where Lean is strictly more general (eb-generic contracts, D5), take the
   generalisation.  Known cases: `IntrDefs` (weak files use only `intena` ×9, `sie_cap` ×1; Lean has no
   SIE ghost, D27 → `KCtx`'s sie index), `WpSconf*` (merged into the `KCtx` index), `CpuOwn`/`HartTp`/
   `StackOwn` (→ `KCtx.cpuOwn/tpPin/stackOwn`), `WpStartNew`/`WpTimerinit`/`WpEntryNew` (→ the
   Spec/Proof pairs in `Xv6/`).
4. **When Lean deliberately dropped a mechanism the weak proof uses**, supply it in `Weak/`, not in
   `MachCSL/`: `MinstretInv` (45 importers; Lean's counters are existential → `Weak/MinstretInv.lean` over
   `RegFile`), `UserBits.pa_window`, `VcGen`, and the **`PtAdBits` write-back lemmas** (`update_PTE_Bits_A1`,
   `_ne`: lemmas about a model function → `Weak/PtAdBits.lean`, no shared change).  Only if an invariant
   must live in `machInterp` does it become an owner decision.
5. **Decode catalogs.**  67 weak/Wk files import `KernelDecode*`/`Code*`.  Per site, a `kd_<word>` fact
   becomes a `decodes32`/`decodes16` lemma closed by `rfl` at the reference map
   (`DecodeBridge.decodes32_bridge`, `Xv6/KernelTac`, `CodeTactics`); whole-image uses (`KernelPinsDef`,
   `KernelSitesDef`) become `decide +kernel` sweeps over `Xv6/KernelText` in the `FsImgCheckSweeps` style.
   No catalog is regenerated.

## D. Scope and order

The 130 `AxSpin*` files' import cone is 348 files / 214,941 lines; the critical path
(`WeakMem` → … → `AxSpinJ2`, 53 files, 50.4k lines) lies entirely inside it.  Outside: 224 files /
146,083 lines — `WeakRvwmo*` 26.5k (incl. the `WeakRvwmoCapstone`/`WeakSrvwmoCapstone` roots), `WeakLeaf*`
20.3k, `AxLock*` 13.8k (the primer marks most as VACUOUS/TRIVIAL older slices), all of `WeakShape*` 8.1k
(generated), `AxEpi*` 6.6k, `WeakRobustL2*`, `WeakSailCone`, `WeakKpt`/`WeakStale`, every `Wk*` proof but
`WkEntryEff`/`WkEntryNew`, `KernelPins`.

**Order.**
- **Phase 0 (serial, owner-gated where shared):** §B; `Weak/Exec.lean` + `ExecLib`; the library shims
  G1–G8 of the gaps note as `Weak/Lib/{Rel,StdppMap,StdppSet,SetSolver,Qp,Fin,Keys}.lean`; CI plumbing
  (§E); the MonPred spike `WeakView`+`WeakVProp`; `WeakMem`+`WeakPromise`+`WeakPromiseFact` (pure, exercise
  the shims at scale); `WeakDeps` (126 `vm_compute` → `decide +kernel`, the reflection recipe's first test).
- **Phase 1: the spin cone**, by the map's file-level schedule restricted to the cone (18 lanes become
  ~11); the critical path to the strongest worker.  Value lands at: `WeakRobustMain` (Layer 1),
  `WeakEvCapstone.xv6_ev_weak_robust`, `AxGraph*`/`AxLitmus` (closed deciders), `AxWp`/`AxAdequacy`,
  `AxTierA3/A4` adequacy, `AxLock3Thm`, `AxEpiRun`/`AxEpiSound3`, then the 18 `AxSpin*` roots
  (`AxSpinJ2`, `AxSpinU4`, `AxSpinAp9`, `AxSpinAm4`, `AxSpinAq*`, …).
- **Phase 2: the rest**, by value: `WeakRvwmo*`/`WeakSrvwmo*` capstones and their leaves; `Wk*`
  whole-function proofs; `WeakLeaf*` remainder; `AxLock*`/`AxEpi*` remainder; `WeakShape*` via the
  retargeted generator; `KernelPins`/`Sites`; the archived lift tree (`WeakComposeLang`, `WeakSailCone`,
  `WeakRobustL2*`).

**Most at risk** (in order): (1) `vm_compute` certificate files — `WkStartAux` 287 sites, `WeakDeps` 126,
`AxLeafS5` 115, `WkTimerinitAux` 93, `AxLock3` 82, `WeakLeafCsrw2` 79, `WkStartNew` 70 — and the 78
open-term `vm_cast_no_check` sites (`AxPair.rsw_lbls_pre`): checkers must be structural/fuelled for
`decide +kernel`, open terms go through walk equations; (2) `Wk*` boot proofs: decode catalogs + the most
drifted SC modules (`WpStartNew`, `WpTimerinit`, `CodeStart*`); (3) `WeakShape*`: the 151-lemma
`Defs.bind/try_catch/liftR/foreachM` kit re-proved over lean-sail `FreeM`/`ExceptT` and `gen_shape.py`
retargeted; (4) `AxEpiChain` (410 s cold in Rocq) and `AxFetch` (4,951 lines): split; (5) the 27 `monPred`
files on iris-lean's unexercised `MonPred`; (6) 838 `set_solver` calls; (7) `Countable` key types → `Ord`
law instances.

## E. Porting protocol

**Files and names.**  `Weak/<RocqName>.lean`, module `Weak.<RocqName>`, `namespace Weak` with
`open MachCSL`; one file per Rocq file, including `VirtioProg`, `KernelPins{,Def}`, `KernelSites{,Def}`,
`Wk*`.  A file may be split only as `<Name>Parts<N>.lean` re-exported by `<Name>.lean`, so the Rocq name
resolves.  **Keep Rocq lemma and definition names verbatim** (snake_case) — the 9.8k lines of design
notes, the DAG and the file headers cite them, and 572 files by many workers need one rule, not taste;
rename only on a clash (suffix `'`), recorded in the header.  (Deviates from the SC port's camelCase:
owner to bless.)

**Header** (module docstring): (1) `Rocq: iris/<File>.v @ xxvzwolszwmp (1cc222280)`; (2) the Rocq header
verbatim — they are the authoritative design records (FINDING/RESIDUALS/VACUOUS blocks included);
(3) **Deviations from Rocq**, numbered (the 805 SC headers' convention); (4) **Drift** (§C.3);
(5) **Not ported**: each dropped declaration with "uses checked: none" (D36 precedent); (6) **Statements
checked**: the list of exported theorems whose Lean statement was diffed against Rocq.

**Generated files.**  Never hand-port `KernelPins.v`, `KernelSites.v`, `WeakShapeGen01–15.v`,
`WeakShapeExecGen01–03.v`.  Retarget `tools/gen_pins.py`, `gen_sites.py`, `gen_shape.py` to emit Lean from
`Xv6/KernelText`/`KernelImage` and `model/Lean_RV64D`, register them in `make check-gen`.  The hand-written
checkers (`KernelPinsDef`, `KernelSitesDef`) port as `Bool` deciders proved by `decide +kernel` sweeps.

**Statement-faithfulness check (per file).**  (i) Once, on the Rocq VM, dump every exported
`Lemma/Theorem/Definition` of the 572 files with its printed type into
`notes/weak-port-statements/<File>.txt` (workers cannot run Rocq); (ii) a script
(`tools/weak_port_check.py`, on top of `tools/ConstDeps.lean`) fails if a Lean file lacks a name of its
list without a **Not ported** entry; (iii) **statement first**: the worker writes every exported statement
with `sorry` in its workspace and a fresh reviewer diffs it against the dump *before* proofs start — a
cheap port of a changed theorem is the failure mode; (iv) each root: `#print axioms` = `propext`,
`Classical.choice`, `Quot.sound`, `bv_decide` certificates; (v) port the satisfiability/race witnesses
beside every Prop result (the primer: "VACUITY is the #1 review finding").

**Tractability of 570–5,000-line files.**  One Lean lemma per Rocq lemma, never merged.  Ltac (324
definitions: `lk`, `off`, `c_go`, `vr`, `zsimp`, `leaf_peel`, `ev_go`, …) becomes Lean macros in
`Weak/<Family>Tac.lean`, written once by the family's first worker.  `vm_compute` → `decide +kernel` on
structural checkers, split into sweeps under `ulimit` (D34); `Eval vm_compute` Ltac → `dsimproc`s.
Proof mode: `FrameFilter`/`KApply`, `ihave … $$ H` for `iEval in`.  Time budgets per declaration (stage
≤ 5 s, rule ≤ 3 s, certificate ≤ 60 s; `maxHeartbeats` per declaration only).  Workers never edit
`MachCSL/`, `Xv6/`, `model/`, `vendor/`, `tools/ci` — those are Phase-0 items; shared helpers go to
`Weak/Lib/`, owned by one library worker.  `sorry` only in a workspace, never in the squashed commit.

**CI.**  `tools/lean_lint.py` `TREES`/`ROOTS` must gain `"Weak"` (today `Weak/` is exempt from the
sorry/axiom/native_decide/drift lints); `tools/ci/roots.txt`, `tools/audit/baseline.json`,
`tools/tcb/expected.json` gain the weak roots; `tools/check_layering.sh` is unaffected (no Spec/Proof/Link
in `Weak/`).  One commit on bookmark `weak`: workers in `jj workspace add ../xv6iris-weak-<lane>`, squashed
by the owner after a full `lake build` (`Weak` is already a default target) and `tools/ci/run_all.sh`.

## Owner decisions required

1. **§B** — lean-sail `Outcome` constructors, model regeneration with `-D SYMBOLIC`, `Xv6Extras` externs,
   the two new registers; touches `MachCSL/Lang.lean`, `Wp.lean`, `Tactics.lean`, the boot chain, the TCB
   baseline.
2. **Drift item zero** — diffing sail-riscv `c32fbf41` vs `070832a1`, and what to do if the event streams
   differ.
3. **Superseded files** — the design notes declare `WeakSailLTS*`, `WeakSailComplete/Cone`, `WeakShape*`,
   `WeakRetag`, `WeakComposeLang` dead; the mandate says port everything.  Recommended: port all, last.
4. **Names** — snake_case verbatim in `Weak/`.
5. **CI** — adding `Weak` to the lints and the audit/tcb/roots baselines (routine, but owner-visible).

No decision is needed for `TsoMem` (untouched), `VirtioProg` (Weak-local), `PtAdBits` (Weak-local),
`MinstretInv` (Weak-local) or the `exec` evaluator (Weak-local, bridged to `runRW`).

## Owner decisions (2026-10-05)

- **§B: YES** — the Lean line gets `-D SYMBOLIC` too (as the Rocq weak line did): lean-sail `Outcome`
  announce events, model regenerated, silent `evStep` arms, SC proofs fixed in the same change.
- **Sail revision:** target Lean's `070832a1` (diff against the weak line's `c32fbf41` and record any
  event-stream change that moves a weak certificate).
- **Superseded / retired Rocq files: skipped** (listed in this note's skip list as they are met, with the
  header line that marks them).
- **Naming: the tree's convention (camelCase)**, with a Rocq→Lean name map in each file header — not the
  verbatim-Rocq-names rule of §E.
- **Proofs: everything fully proved** — no `sorry`/`admit`/axiom; `native_decide` stays banned
  (`bv_decide` allowed as in the tree).
- Library shims live in `MachCSL/` (`Rel`, `QpLemmas`, `FinToSet`, `StdppSet`, `StdppMap`, `SetSolver`,
  `OrdKeys`, `StdppList`), not `Weak/Lib/`.
- **Fetch / walker access kinds (sail-riscv drift, notes/weak-port-sail-drift.md): O2 — Lean semantics.**
  The Lean model tags fetches `AK_ifetch` and non-atomic walker reads `AK_ttw`; the weak tier follows
  MachCSL (ifetch = the i-cache agent, moves no view; ttw per MachCSL), NOT the Rocq "fetches are plain
  explicit reads" classification. This redesigns WeakInterp's `classify`, WeakEvLang's read arm, the fetch
  lift (WeakEvLift §5c) and the fetch-event leaves; certificates computed on the old classification are
  re-derived. Design: notes/weak-port-o2-design.md.
- **O2 design decisions (notes/weak-port-o2-design.md):**
  - **D1: fetches STAY graph read events in the AxSL/RVWMO-graph tier** (as in Rocq: explicit reads with
    po-loc/fr/dependency edges; sound because text is never written) — the design's `LFetch`-out-of-graph
    route is NOT taken; O2 changes the view/promising tier (classify, i-cache agent) only, and the AxSL tier
    keeps the Rocq fetch treatment (the design's §2 "fallback if D1 is refused").
  - **D2: Stage B now** — the per-hart i-cache view `itv` and `fence.i` semantics are modelled during the
    port (not the Stage-A over-approximation).
  - **D3** (per-byte i-cache view, one-way bridge) and **D4** (new `LIFetch` wlabel constructor, `lat`
    kept inert): the design's recommendations, adopted.
  - **D5: the archive is skipped** — `WeakSailLTS*`, `WeakCompose*`, `WeakShape*` (and files that only
    serve them) are not ported; listed in notes/weak-port-skip.md.
- **Exec layer (WeakBridge blocker, 2026-10-06): route (a)** — build `Weak/Exec.lean` (a deterministic
  evaluator over the Sail free monad + its library, bridged once to MachCSL's runRW) before WeakBridge and the
  exec-using certificate files; WeakBridge then ports nearly literally with the O2 fetch pin
  `latestTs log a ≤ itv`.
- **Write answers aligned to MachCSL:** the weak interpreter answers memory writes `.Ok (some true)` like
  MachCSL (not `.Ok none`); WeakInterp and dependents are changed accordingly.
- **Q1 (2026-10-06): device programs modelled in the event tier.** WeakEvInst's PLIC/UART steps must follow the
  actual device programs (kept in the fabric state), not over-approximate them, so WeakEvCapstone needs no
  `evDevCover` premise.
- **Q2 (2026-10-06): accepted** — WeakRvwmoSupply's `candFetchInert` premise, discharged by consumers.
- **Q3 (2026-10-06): option A** — Rocq's `mmode_config` (hw_config + minstret/clock invariants + hart cells)
  is restated as the Lean SC tree's `mConf cpu dq c` plus the five owned clock cells (`clockCells cpu`), mask
  ⊤; `MinstretInv` is NOT ported. All weak leaf files that take `mmode_config` use this interface.
- **Q4 (2026-10-06): leave as premise** — the 'kernel text is never written' premises (efetchItvOk, fetchSrcOk) stay carried and documented in the capstones; to be lifted later (not part of the port).
- **Stage C (owner, 2026-10-06 ~21:10) — D1 REVERSED: fetches leave the graph tier and go through the
  per-hart i-cache view there too** ("merge the graph tier into the Lean tier; going through the i-cache view
  seems the correct way"). The O2 design's `LFetch`-out-of-graph route (notes/weak-port-o2-design.md) is now
  the target. Goals from the owner: verify the main assumptions first, and make it AS SIMPLE AS POSSIBLE.
  Consequence: the fetch-inertness bridge (`lbFetchInert`, `candFetchInert(F)`, `hullRunFetchInert`,
  `t2linFetchInert`, `fconfFetchInert`, `wfetchSite`; open question Q5) is to be REMOVED rather than carried.
  Q4 (text never written / fence.i discipline) remains, on the i-cache view (`efetchItvOk`).
  Design + rework list: notes/weak-port-o2-stageC.md (consult, then one rework lane). Until approved,
  files on the fetch-in-graph path are HELD.
- **Stage C rulings (owner, 2026-10-07 ~00:35, on notes/weak-port-o2-stageC.md):** Q-C1 ADMIN label (LIFetch has no
  row item/identity/edges; boot-image pin = `emFetchImg` clause in `gdexecQconf` + `pstepPin`); Q-C2 delete the
  oracle params `T`/`fetchImg`/`fetchAnswers` and `AxWp.axText` now; Q-C3 delete `pstepNoFetch`/`pfFetchLoadOk`;
  Q-C4 `wlblRen` fixes `LIFetch`. Rework = stageC.md §C lanes 1–3 (39 files) in workspace ../xv6iris-weak-sc.
