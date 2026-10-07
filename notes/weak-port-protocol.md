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
- WeakFetch2: 2-aligned fetch arms — F_Base emits `[.WEread wakIfetch pc 2, .WEread wakIfetch (BitVec.addInt pc 2) 2]`, F_RVC `[.WEread wakIfetch pc 2]`; `BitVec.addInt pc 2` is defeq `pc + BitVec.ofNat 64 2` (WeakCert form; may need `show`). Never ascribe `extractLsb` halves (silent `setWidth`).
- WeakRvwmoAdm: tactic `weak_adm_krfl` (kernel `Eq.refl` over the local context, for facts with free vars that `decide +kernel` refuses) — reuse it; do not name a tactic `kernel_rfl` (MachCSL.URunRW and Xv6/UserTextDecode both define one).
- WeakLeafLw4: GPR-cell regInterp helpers `WeakLeafLw4.gprValid`/`gprUpdate`/`gprSetNe` — reuse in later leaves.
- WeakWalkEff: `WeakWalkEff.uAcc6` is Rocq u_acc (6 arms; ExecSC2.uAcc has 3), PtTree pieces ptSlotMem/ptreeBlocks/ptreeMapsBlocksExcl/uweMatchOther/pteValidInvalidExcl as `WeakWalkEff.*`. WeakPmpEff and WeakPmpTorEff clash on `execEffPmpReadAddrReg` (do not import both).
- **GPR leaves (wPEff*/wwp*Leaf whnf timeouts):** WeakLeafLw4 is the worked example — import it and reuse `WeakLeafLw4.gprValid`/`gprUpdate`/`gprSetNe`/`keepPure2`/`winstrBytesNotRVC` (do NOT re-prove gpr-cell lemmas; a 31/32-arm match or `uxa_bv5_cases`+`dsimp [gpr]` in a new file blows whnf). The `(⟨regs, M, dev⟩ : ExecSt).gpr r` vs `(wflatSt σ).gpr r` mismatch times out the unifier: `unfold ExecSt.gpr at h ⊢; exact h`. Model `wPEff<X>` on `wPEffLw4`.
- WeakRvwmoLin2: `fconfSupply'` takes `candFetchInertF boot N (candOf G L)`; `fconfTraceRealize` returns `∃ L, … ∧ (candFetchInertF boot N c → ∃ pst, …)` — consumers discharge `candFetchInertF` at their candidate.
- GPR leaves: a whnf timeout at `exact` after `rw [(lemma _ x _ y _ _).field]` comes from open metavariables — instantiate all args. Before `WeakLeafLw4.gprUpdate` on a `.setMem` state, `rw [show … = (… .setMem M).regs from rfl]` (never pass `_` for the state). WeakLeafCsrw is the worked CSR leaf.
- Wide (8-byte) leaves: whnf unfolds `wwin pc ea 8` inside the confined-state literal — use `WeakLeafLd8.confBytes`/`confDom` (stated over an abstract window W) instead of stating BytesAt/bmDomSub at the literal.
- `exact wwinWdom σ pc ea n vs` against a `(⟨r, m, d⟩ : ExecSt).mem` goal times out — `dsimp only` first. Model wPEff<X> as in wPEffLw4: apply `wPEffOfLeafBase`, one bullet per premise.
- WeakLeafPmpcfg0: `execEffForInInv` (execEff loop rule), `execEffItePure` (do not `split` an if-pure after exec_eff_steps), `fetchInWindowRegonly`/`fetchFreshRegonly` (fetchPin for any register-only leaf), `pmpcfgWritten` & WpGprCsrwA/C pmpcfg0 helpers — all `WeakLeafPmpcfg0.*`, reuse.
- **CSR-in-mConf leaves (Q3 consequence):** a leaf that WRITES a CSR bundled in `mConf` (stimecmp, medeleg, mepc, satp, …) cannot use `wwpInstr`; it splits `mConf` (`mconf_cases`), runs `WeakFunnelCfg.wwpInstrConfig`, rebuilds with `mConf_introW` — and therefore takes `mConf cpu (DFrac.own 1) c` (Rocq: any `q`). See WeakLeafStimecmp. Callers (WeakLeafM/O, …) must hold the full config fraction at the call site; if a caller only has a fraction, STOP and report (orchestrator question).
- Register-only CSR leaves: copy WeakLeafCsrrTime (alignment-generic route; `execEffCsrrReadStepP`, `execEffCheckCSRReadP`/`execEffCheckCSRResultReadP`). `fetchInWindowRegonly`/`fetchFreshRegonly` exist in Pmpcfg0, CsrrTime and Stimecmp (file-qualified) — import one, don't add a fourth.
- Hidden width casts: `f _ n w` with `w : BitVec 32` where `BitVec (8*n)` is expected elaborates as `setWidth` silently — state words as `BitVec (8 * n)`; check with `set_option pp.explicit true in #check @thm`. WeakEvFunnel: `ewpEvOneFetch`/`ewpInstrPure` take `ak.akIfetch = true`.
- WeakEvProv2: tactic `weak_ev_prov2_kwhnf` (Kernel.whnf both sides, syntactic check, two kernel Eq.refl) for equations between monad terms at two different free words ("continuation independent of the answer") where `weak_adm_krfl` times out — reuse it. lean-sail register writes have no access-kind argument; `pnodeStepPair`/`tparStep` carry `obar`.
- setReg chains: `simp (disch := first | decide | (simp (disch := decide) only [ExecSt.setReg_regs, RegFile.set_same, RegFile.set_other, <hyps>]; done)) only [...]`; rfl fold lemmas (e.g. `WeakLeafMret.cms1`…) keep named-state hyps matching; before `iexact` on `regInterp (…setReg…).regs`, `simp only [ExecSt.setReg_regs]`.
- WeakLeafCsrw3: satp/mie/mideleg/pmpaddr leaves on the CSR-in-mConf interface (full fraction; satp leaf takes `_get_Mstatus_SXL c.mstatus = 2#2`); WpGprCsrwB pure defs (satpLegalized, sieNewMie, pmp0Newaddr, satpPpnMaskId) live there as `WeakLeafCsrw3.*`. `physaddr_bits`/`pagesize_bits`: use `LeanRV64D.Functions` (Nat).
- Full-fraction check (orchestrator, 2026-10-06): Rocq top level instantiates `mmode_config (DfracOwn 1)` (WkStartNew → `WeakLeafO.whart_run ξ 1`; WkEntryNew at 1). So WeakLeafM/WeakLeafO wrappers around CSR-in-mConf leaves may be stated at `DFrac.own 1` (deviation: Rocq generic `q`); keep `q` generic for wrappers whose leaves do not write mConf CSRs. No need to stop for this.
- WeakLeafCsrw2: generic CSR-in-mConf csrw leaf `WeakLeafCsrw2.wwpCsrwLeaf` (medeleg/mideleg/mepc/mcounteren/menvcfg); rebuild mConf with `iapply confCells_intro; simp only []; iframe; iexact Hhw`. A Sail `if` on a variable stops `exec_eff_steps`: `cases hp : <cond>` first and add `hp` to the simp set.
- WeakLeafTor: `wPEffOfLeafRvc` + TOR PMP helpers (`WeakLeafTor.*`, re-proved because WeakPmpTorEff cannot be imported with WeakPmpEff) — WeakLeafM/SdspOff/WkTimerinit/WkStartNew/WkStartAux import and reuse. Reading a register the funnel holds but does not read: split `mConf (own q)` into halves (`Qp.half_add_half`; register cells via `ghost_map_elem_fractional`), read off the kept half in the callback.
- WeakLeafCsrrM: CSR-READ leaves for CSRs inside mConf (menvcfg, mcounteren, mie/mideleg→sie) take no separate CSR cell (Rocq does) and read `c.<csr>`; fraction split helpers `WeakLeafCsrrM.regSplit`/`mConfSplit`/`mConfHalves`/`mConfCsrFacts` and core `wwpCsrrCore` — reuse. Callers drop the Rocq CSR cell argument. `(pure true : SailM Bool)` in premises (iprop `pure` ambiguity).
- WeakEvWire (Q1 consequence): `ewpPlic` needs `WeakEvWire.wireInv ∗ WeakEvWire.plicInv` (PLIC is a stateful device program; `plicInv` = `∃ p, devFragAt era .plic p`, allocated by `plicInvAlloc`). Names `WeakEvWire.wireN/wireInv` (MachCSL.WireInv has its own). lean-sail `regRead` has no `direct` flag. OPEN (not blocking, no live composer): `WeakEvDisk.ewpEdiskLatch` still takes `devFragAt .plic p` directly — composing it with `plicInv` needs a design choice; hart MMIO to the PLIC window will also need `plicInv`. If a file you port composes them, STOP and report.
- `iapply (show A ⊢ B from .rfl)` bridges defeq-but-not-syntactic state interps (`σ.setReg` vs `ewgReg`); `exacts` and `swap` are Mathlib — unavailable.
- GPR file: Rocq `gpr_file m` ↦ `MachCSL.gprFile cpu m` (x0 not owned): reads `m.get r` (x0 = 0), updates `m.set rd v` — WeakLeafM/WkStart*/WkTimerinit use this. Generic RVC register leaf `WeakLeafRtypeW.wwpGprRvcLeaf` (operator-abstracted) — reuse for ALU leaves.
- WeakLeafItype: generic register-only leaves over `(i, op)` — `WeakLeafItype.wwpGprBaseLeaf`/`wwpGprRvcLeaf`; whole-file read/write `WeakLeafItype.gprFileValue`/`gprFileWrite`; `fetchPinRvc0`. Prefer these (or WeakLeafRtypeW.wwpGprRvcLeaf for two-source ops) over new funnel scripts.
- WkEntryNew: generic gprFile register-only leaf `WkEntryNew.wwpRegLeaf` (+ fetch-arm lemmas armBase4/armRvc4/armBase2/armRvc2); decode facts = two `kernel_rfl` walks (drefM; supervisor map without mseccfg). Two GPR cells from one gprFile: read operand with `gprFile_lookup_acc` and restore, then take dest with `gprFile_acc`.
- WeakRvwmoGlue (provisional, owner Q5): `hullRun`/`cycleKillOfL2`/`t2linOfL2` carry `WeakRvwmoGlue.hullRunFetchInert boot d0 im nh N` and the fetch-view premise `∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2`; consumers CARRY both (name them after the Rocq lemma) unless they can discharge them. `RunData` fields rdCons/rdImg/rdPst0/rdDv0/rdProg; `d0 = efInit σ0.wgdev`.
