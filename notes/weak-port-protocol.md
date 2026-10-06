# Weak port — worker protocol (read this first)

You are porting part of the Rocq weak-memory development to Lean. The orchestrator assigns you a FILE LIST
and a WORKSPACE (a jj workspace = a full Lean tree). Rules:

**Version control / builds**
- Never run `git` or `jj`, not even read-only. Never spawn subagents.
- Never run `lake build` locally. Build on the GCP VM:
  `~/.local/bin/lean-gcp -C <your workspace> lake build Weak.<Module>` (syncs the tree, builds there).
  `-C` is mandatory. A first build in a fresh workspace is cold (~6 min): build `lake build MachCSL` once.
- Before reporting: `~/.local/bin/lean-gcp -C <ws> tools/ci/lint.sh` must pass for your files (lint covers
  `Weak/`; it bans sorry/admit/axiom/native_decide and checks the import drift — the drift finding for your
  files is expected because you do NOT edit `Weak.lean`; ignore drift findings for your own new files only).

**Files**
- Rocq sources: `/home/bsdinis/dev/xv6iris-spinlock/iris/<Name>.v` (the weak line, jj change xxvzwolszwmp).
- Target: `Weak/<Name>.lean` (same base name as the Rocq file; split as `<Name>2.lean`… only if one file
  elaborates in > ~2 min).
- Do NOT edit `Weak.lean` (the orchestrator maintains its imports). Import your dependencies directly.
- Do NOT edit files you were not assigned. If a dependency you need is missing in your tree, STOP and
  report (do not copy files around). Helper lemmas go in your own files. Library additions that clearly
  belong in a shared shim go in a NEW file `MachCSL/WeakAux<YourFirstFile>.lean` (never edit an existing
  shim), and you report them.

**Faithfulness**
- Port EVERY definition and lemma. Drop one only if no downstream weak file uses it (grep the Rocq tree)
  and list it in the header. Skipped Rocq files: `notes/weak-port-skip.md` (do not port them; if your file
  imports one, port only what your file uses, inside your file, and say so).
- Statements faithful (same quantifiers/premises). Any change → header "Deviations from Rocq".
- FULLY PROVED: no `sorry`, `admit`, new `axiom`, `native_decide`. `decide +kernel` / `bv_decide` are fine.
- Names: the tree's camelCase convention; each header has a Rocq→Lean name map.

**Header** (tree style): the Rocq source path; what the file proves; "Deviations from Rocq"; the name
map; dropped lemmas.

**Design decisions you must follow** — `notes/weak-port-architecture.md` (all "Owner decisions"),
`notes/weak-port-o2-design.md` (O2: Lean access-kind semantics for fetch/ttw — with owner D1: fetches STAY
graph reads in the AxSL tier; D2: Stage B, the per-hart i-cache view `itv` and `fence.i` are modelled;
D3/D4 as recommended), `notes/symbolic-model.md` (announce events), `notes/weak-port-iris-gaps.md`
(shims; vm_compute → `decide +kernel` recipe in `Weak/WeakDeps.lean`'s header), `notes/weak-port-map.md`
(DAG; Lean counterparts of Rocq SC modules).

**Lessons so far** (keep adding in your report)
- Field lemmas are `rfl`; view-bound goals: `simp only [defs]` then `(try split) <;> omega` (omega does `max`).
- Rocq conversion facts (e.g. `Nat.max 0 x ≡ x`) are not definitional in Lean: use the rewrite lemmas.
- Heavy unification against structure-literal projections can hit heartbeats: `(by dsimp only; exact h)`.
- `set_solver` (normalise + `grind`) is slow in big contexts: factor small set facts into lemmas.
- No doc comments on `variable`/`include`. Block comments must not contain `-/`.
- `|==> P ∗ Q` parses as `(|==> P) ∗ Q`: parenthesise. MonPred files import `MachCSL.MonPredExtra`; each
  `def`-level VProp needs a `MakeMonPredAt` instance; state index instances at `View`.
- iris-lean OFEs use plain equality (camera lemmas by `funext`); `MaxNat` instances are scoped (`open Iris`);
  `icases iOwn_cmraValid_op` wants `[$Ha $Hf]`.
- stdpp `rtc`/`tc` are the library closures built from the LAST step (`MachCSL.Rel` header).

**Report** (≤ 300 words): files, decl counts Rocq vs Lean, dropped lemmas, deviations, shim additions,
build times, new lessons, anything blocking.

**Duplicated Rocq names (all files share `namespace Weak`).** Rocq names are module-qualified; 326 names
are defined in more than one Rocq weak file (`notes/weak-port-dupnames.json`: name → files). If a name
you port is in that table, declare it FILE-QUALIFIED: `theorem <RocqFile>.<camelName> …` inside
`namespace Weak` (e.g. `theorem WeakLitmus.msgByteSingle`), and refer to it qualified. When you USE a
duplicated name from a dependency, use the qualified name of the file you actually import.

**Pre-translated drafts: NOT used.** An A/B test (2026-10-06, 3 vs 3 comparable files) found drafts from
tools/weak_rocq2lean.py cost MORE (≈178 vs ≈149 agent tokens per Rocq line): workers kept the names and
statements but rewrote every proof, and draft errors (untyped binders, record literals, maps as lists)
hit the 100-error cap and hid the real ones. You MAY use `tools/weak_rocq2lean.py --names <Name>` for the
Rocq→Lean name map only.

**Cross-file facts later ports must respect** (read the named headers):
- Fetches: `fetchSrcOk` premise carried by the robustness capstones (WeakRobustSim/Main); `pstepNoFetch` on
  WeakErase/WeakRefuse bridges; the bridge fetch → plain load premise `pfFetchLoadOk` (WeakPromiseBridge);
  `LtsEnabled.leIfetch` (WeakRobustBlocks); text pin `pinnedRead ∧ fetchPinned` (WeakInstr/WeakBridge).
- Event pool (WeakEvPf): harts, then uart0, uart1, disk, plic — disk at index `NCPU+2`, plic at `NCPU+3`
  (Rocq: disk `NCPU+1`); device arms have the new shapes and `plicAgent` (WeakEvPf header).
- Exec layer: Weak/Exec + ExecLib (+ ExecSC*), `exec_steps` tactic; writes answer `.Ok (some true)`;
  MMIO test `mmioAcc` (= `devAddr pa && n != 0`).
- Archive files imported by live files are ported only as far as live files use them (WeakRobustL2 = one
  lemma; WeakSailComplete = its register-file section).
- WeakRvwmoConf: `hlblRealizes` keeps Rocq's 4 conditions; `hlblRealizesAx` is now
  `lblRealizes … ↔ hlblRealizes … ∧ lbFetchInert σ i l` — users that turn `hart_conf` blocks into
  `lblRealizes` (AxOpsem, AxDeps, B0b-2) must supply `lbFetchInert` at the machine state
  (`hlblRealizesAxNoFetch` for non-fetch labels). Under D1 `LIFetch` is treated like `LLoad false` there.
- WeakRvwmoSupply: `supplyOfQconf` takes `candFetchInert boot d0 N c` (every fetch item of a constant-fabric
  emission is fetch-inert at its trace position); `hullSupply`/`topoSupply` return the supply conditional on
  it. Consumers (WeakRvwmoGlue, capstones) discharge it for the candidate they receive (e.g. fetches of
  never-written text at timestamp 0).
- `bv_decide` adds an auxiliary `<Enum>.enumToBitVec` the first time it meets an enum; two modules that each
  trigger it clash when imported together ("environment already contains … enumToBitVec"). Import the module
  that already encodes that enum (e.g. `MachCSL.WpTrap` for `Privilege`, `Weak.ExecSC5` for
  `MemoryRegionType`, `MachCSL.BvEnumSatp` for `SATPMode`) so `bv_decide` reuses it.
- WeakEvLift: `ewpEvExstore` is stated at `hlc := .hasLC` (the retry loop spends a later credit;
  `lc_fupd_elim_later` needs `InvGS`) — lock-acquire leaves that use it run the hlc-generic adequacy
  theorems at `.hasLC`. Rocq's `efetch_ws*` are gone (a fetch leaves `ws` unchanged).
- **Lean-only helpers must be FILE-QUALIFIED** (`theorem <File>.helperName`), like duplicated Rocq names —
  two files adding the same helper name (e.g. `execEffWithinMmioReadableFalse`) cannot be imported together.
- WeakVariant: 8 variant/cover lemmas take `ak.akIfetch = false` (the i-cache window doesn't exclude the
  initial image); Rocq's PtAdBits write-back lemmas live in WeakVariant as `PtAdBits.*` — reuse them, don't
  redefine.
- Q3: Rocq `mmode_config dq` ↦ Lean `mConf cpu dq c ∗ clockCells cpu` (mask ⊤; no MinstretInv) — see
  WeakFunnel's header.
- AxPtProt: Rocq PtTree's shallow 3-level pieces (ptree_maps, ptree_set_leaf, ptree_canon, tlb_ok_pt, …) live in AxPtProt as `AxPtProt.*` over MachCSL.PTree — reuse them (AxWalk3, AxSfence2, …).
- WeakLeafWin: `wwin`, the `leaf_peel` macro, `loadSexecFacts` and the GPR frame lemmas `WeakLeafWin.setGprRegsNe`/`setGprMem`/`setGprDev`/`inRamByte` — later leaves reuse them. `(s.setReg r v).regs r = v` needs `simp only [ExecSt.setReg_regs, RegFile.set_same]`.
- WeakFetchRvc: the `Ext_Zca` probe runs in `run_hart_active` (not in `fetch`); 2-aligned (two-halfword) fetch arms are not covered by WeakFetchRvc.
- Decoding SFENCE_VMA by `rfl` needs `virtual_memory_supported`, `hartSupports`, `currentlyEnabled` `local semireducible` (AxSfence).
- WeakRvwmoCert2: `hlblRealizesLoadShape` has a third (fetch) case `aq = false ∧ l = LIFetch base tvs`; `certBlockSnoc` takes `lbFetchInert (candLastSt c) x l`, and `certSegment`'s policy `Hpol` must also return `lbFetchInert (candLastSt c0) x l'` (Cert3/Cert4/Walk/Glue supply it; `WeakRvwmoCert2.lbFetchInertOfStoreNe` for store labels; trivial for non-fetch labels).
