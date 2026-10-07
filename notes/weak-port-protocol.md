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
- **Stage C (2026-10-07, merged): fetches are NOT graph events.** `LIFetch` is an ADMIN label in the graph tier
  (`lbAdmin instr (LIFetch ..) := instr = true`; `projLbl`/`lblIdent` give `none`; no row item, no edges;
  `AStepFetch`, the opax oracle params `T`/`fetchImg`/`fetchAnswers` and `AxWp.axText` are deleted — a fetch is an
  `AStepAdmin` step / `wpSkipStep`). `lblRealizes` is Rocq's 4 conjuncts and `hlblRealizesAx` is `Iff.rfl`.
  The only graph-tier fetch content is the boot-image pin `WeakAxRealize.fetchPin img l`: the program LTS is
  `pstepPin img pstepEv` (supplies, Cert chain, Glue `RunData`, capstones' internals), `emFetchImg im em` is a
  clause of `gdexecQconf`/`gfexecConf`, appended blocks are `WeakRvwmoCert2.cblkPin` / `cblkpPin`,
  `certSegment*`/`segStepOfSegment`/`wlkSegOf*` take `WeakRvwmoCert2.esPin`; project back with
  `WeakRvwmoCapstone.execProgOkPinSub` / `wpPfRunPinSub`. Walk: `wwitNd`/`poisonedNoFault`/`wpoisSite` are stated
  on pinned blocks `∀ im`; `wemit` ends with `esPin`. ALL fetch-inertness names (lbFetchInert, candFetchInert(F),
  emFetchInert, hullRunFetchInert, t2linFetchInert, fconfFetchInert, wfetchSite, pfFetchLoadOk, hlblRealizesAxNoFetch)
  are GONE. The capstones carry only `efetchItvOk` (Q4). `pstepNoFetch` survives only in WeakRobustMain (Q6);
  `fetchSrcOk` stays on the robustness line. Design: notes/weak-port-o2-stageC.md. Rows: a fetch that ended a Rocq
  row is followed by the next real memory event (hemit allows no trailing admin items). AxSfence: Q7 implemented — sfence.vma marker = `LFence false false false false` at the SFENCE.VMA `instrAnnounce` (`WeakEvLang.sfAnnB`/`annLabel`/`annPost`); generic admin-run lemmas take `WeakEvLang.noSfAnn m s`; WeakEvProv boundary lemmas take `LFence false false false false ∉ ls`.
- Event pool (WeakEvPf): harts, then uart0, uart1, disk, plic — disk at index `NCPU+2`, plic at `NCPU+3`
  (Rocq: disk `NCPU+1`); device arms have the new shapes and `plicAgent` (WeakEvPf header).
- Exec layer: Weak/Exec + ExecLib (+ ExecSC*), `exec_steps` tactic; writes answer `.Ok (some true)`;
  MMIO test `mmioAcc` (= `devAddr pa && n != 0`).
- Archive files imported by live files are ported only as far as live files use them (WeakRobustL2 = one
  lemma; WeakSailComplete = its register-file section).
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
- WeakFetch2: 2-aligned fetch arms — F_Base emits `[.WEread wakIfetch pc 2, .WEread wakIfetch (BitVec.addInt pc 2) 2]`, F_RVC `[.WEread wakIfetch pc 2]`; `BitVec.addInt pc 2` is defeq `pc + BitVec.ofNat 64 2` (WeakCert form; may need `show`). Never ascribe `extractLsb` halves (silent `setWidth`).
- WeakRvwmoAdm: tactic `weak_adm_krfl` (kernel `Eq.refl` over the local context, for facts with free vars that `decide +kernel` refuses) — reuse it; do not name a tactic `kernel_rfl` (MachCSL.URunRW and Xv6/UserTextDecode both define one).
- WeakLeafLw4: GPR-cell regInterp helpers `WeakLeafLw4.gprValid`/`gprUpdate`/`gprSetNe` — reuse in later leaves.
- WeakWalkEff: `WeakWalkEff.uAcc6` is Rocq u_acc (6 arms; ExecSC2.uAcc has 3), PtTree pieces ptSlotMem/ptreeBlocks/ptreeMapsBlocksExcl/uweMatchOther/pteValidInvalidExcl as `WeakWalkEff.*`. WeakPmpEff and WeakPmpTorEff clash on `execEffPmpReadAddrReg` (do not import both).
- **GPR leaves (wPEff*/wwp*Leaf whnf timeouts):** WeakLeafLw4 is the worked example — import it and reuse `WeakLeafLw4.gprValid`/`gprUpdate`/`gprSetNe`/`keepPure2`/`winstrBytesNotRVC` (do NOT re-prove gpr-cell lemmas; a 31/32-arm match or `uxa_bv5_cases`+`dsimp [gpr]` in a new file blows whnf). The `(⟨regs, M, dev⟩ : ExecSt).gpr r` vs `(wflatSt σ).gpr r` mismatch times out the unifier: `unfold ExecSt.gpr at h ⊢; exact h`. Model `wPEff<X>` on `wPEffLw4`.
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
- AxPair: under D1 `lblIdent (LIFetch base tvs)` = identity of the projected `LLoad false … []`; lean-sail regRead/regWrite have no access kind; write values are `Option` (`tpiMw`/`tgMw` take `rq1.value.isSome = rq2.value.isSome`, `pnodeStepStore` takes `rq.value = some v`); step lemmas carry `obar` (regreadStepInv/pairResume/pairResumeDd conclude `obar = none`). Dup names `AxPair.Ident`/`lblWdata`/`phrunApp`.
- WeakKpt: new ghost class `WeakKpt.KptGS GF` (GhostVarG GF PTree + name) for Rocq's `kpt_lb` (Lean SC tree lacks it). Downstream files (WeakKptStale, Wk*) take `[WeakKpt.KptGS GF]` as an instance argument; the adequacy/boot file that allocates ghost state must ALLOCATE it (ghost_var alloc at the boot tree) and report doing so. `kmap_auth` = `MachGS.kmapName ↪●MAP{.discard} M` over `RegMapF (BitVec 64)`; `kptTreeSpecGen` has an extra conjunct (keys < 2^27). `wbyteOkGe` & collapse lemmas take `ak.akIfetch = false`. Kernel leaves via Lean `KPerm`/`mkPte` (A=D=0; statements A/D-closed).
- `iexact` won't unify defeq `regInterp` args: `ieval (rewrite [h])`. Definitions as hyps: `iunfold X at H` before `icases`.
- WeakLeafM: 34 M-mode wrappers `wwp*` + token `winstrM`; 9 CSR-in-mConf write wrappers at `DFrac.own 1` (written value returned in `{ c with … }`), others generic `q`; no separate CSR cells; `wwpCsrwSatp` takes `_get_Mstatus_SXL c.mstatus = 2#2`. is_rvc-generic statements: `simp only [↓reduceIte]` (+ `Bool.false_eq_true`) on the proof-mode goal after `cases is_rvc`. `WkEntryNew.pcIsSplit` splits pcIs.
- Instruction-token files (Wk*Aux): restate the SC vocabulary file-qualified; decodes via `WkEntryNew.decBase`/`decRvc` on walks over `drefM` and `WkEntryNew.drefS0`; builders wrap `winstrMOfText`/`wkbWindow` (see WkTimerinitAux.tokBase/tokRvc). `simp only [fetchIsRvc] at H0` before `ihave` to get `winstrM pc true/false i`.
- Kernel drift (start): Lean `start` = 0x80000058; at `start+0x24` Lean has `addi a5,a5,-426` (0xE5678793; Rocq -506) because Lean main = start+0xe76 — `WkStartAux.stw43`/`si43`=3670/`wsti43` carry the Lean immediate; other 38 words/offsets match.
- **Scratch files: use a PRIVATE subdirectory** of the scratchpad named after your workspace slot (e.g. `<scratchpad>/w12/`) — the scratchpad is shared by all concurrent workers, and files at its top level get overwritten.
- WeakLeafO: `whartRun cpu ξ q c := mConf cpu (DFrac.own q) c ∗ wrunning cpu ξ` (c a parameter); CSR-in-mConf `_o`/`_run` wrappers at `whartRun cpu ξ 1 c`. Keep a floor token without losing the authority: `WeakLeafO.addrsKeep` (persistent_entails_left); ghost update under the loop WP: `WeakLeafO.wwpBupd`.
- AxDevGraph: two UARTs (DUartTx/DUartRx carry the port; uart results per port); `DWire h mm b` covers M and S contexts; `Plic.latch` total (latching a pending/claimed source is a no-op); `devReducible`/`mmioStepAt` over the full fabric `F : Efab`. A pure dstep that reads the disk level and latches the PLIC is NOT the open PLIC-ownership point (that concerns Iris ownership: devFragAt .plic / plicInv / ewpEdiskLatch).
- AxWp (Ax-tier hub): no seals/notations — `AxAnnot.annotOwn e P` (↦ₐ), `interpMod P` (|=i=>), `AxWp.wp st i s Φ` (WP), `wpc st i s Φ` (WPc); classes `AxirisG`/`Axpol`/`AxirisGChk`; skeleton `skelAxirisG γg Φp T` named explicitly. **Map unions on GMapF: write `PartialMap.union`** (bare `∪` picks Std ExtTreeMap union). `GF` at universe 0 where `AxannotGS` appears. `InvGS_gen hlc GF` for any hlc. Proper instances are theorems (`wpProper`, `wpMono'`, `interpModProper`). Dup names `AxWp.wp`/`atBoundary`/`growLookup`.
- AxInstrFacts: Rocq `rdat` (Z * nat * bv 8, left-nested) is Lean `Int × Nat × BitVec 8` (right-nested): `.1.1/.1.2/.2` ↦ `.1/.2.1/.2.2` (AxProtGate/N, AxEpilogue). `Lbl` (graph alphabet) has no fetch constructor.
- Ax WP lemmas with `[InvGS_gen hlc GF]`: if applying one times out in whnf, give `@lemma hlc GF _ _ …` explicitly (hlc not inferred from the goal) — AxReadAll.
- AxWpD: `wpdM M` (plain fixpoint, no seal/notations), `wpd` abbrev at rvwmoCatConsistent, `AxWpD.wpdMUnfoldStep` (unfold at a hart state); `GModel` is a Prop class (`gmWf`), `catGmodel` its instance. `omit … in` goes before the doc comment.
- WkTimerinit: `wwpTimerinit` runs at `whartRun cpu ξ 1 c` (full fraction; three CSR writes), returning `tiConfOut c tv`. **WATCH for WkStartNew:** Rocq calls `wwp_timerinit` at q = 1/2 — the Lean port must call it at 1. Before porting, check why Rocq split the config there (what holds the other half across the call); if that half is needed concurrently, STOP and report (owner question). Never put `assumption` in lookup macros used in large contexts (defeq blow-up not caught by `first`).
- Ax lemmas over `[axG : AxirisG GF]` at a concrete instance: pass `(hlc := hlc) (GF := GF) (axG := skelAxirisG …)`; binders of `AxirisG.obSt GF` need `@AxirisG.obSt GF (skelAxirisG …)`. Persistence of `⌜φ⌝ → P`: state as `∀ _ : φ, P` (no BIPlainly for IProp) — AxProt.
- AxProtLock: new camera class `AxLockG GF` (`axLockInG : ElemG GF (constOF (Auth ClaimedUR))`, `ClaimedUR := DisjointLeibnizSet (GSet Geid)`) — adequacy files using `protInvLock` take `[AxLockG GF]` and must ALLOCATE the claimed ghost (like WeakKpt.KptGS). `AxProtLock.claimed` (dup with AxSpinProt).
- WkFetchPeel: text reads are i-cache reads (`.WEread wakIfetch pa 4`); "text bytes pinned" premises are `fetchPinned σ (accAddr pa j)` (not pinned_read), carried by `WkFetchPeel.fetchPinnedTsMono` + `wrunItvLe` — WkStepPeel / WkWalkTails / WkWalkCapstone must supply `fetchPinned`/`fetchPin` for the text. `wstepOkRacyKR` = `wstepOkRacyK` on ExceptT.run; peel recipe via `wstepOkRacyKBindEq`/`runLiftM`/`wstepOkRacyKPure`.
- Ax WP premises `⊢ ∀ na, … AxirisG.annotInterp na …`: annotate `na : Mea GF` (else "stuck AxirisG ?m"). `insert na e R` ↔ wpEvStep's `PartialMap.union (PartialMap.union {[e:=R]} ∅) na`: `AxLockWp.annotInsertEq`.
- AxProtLock2: only `lockXwriteFlowEq` takes `hxy : x ≠ L` (first arg); `lockExtRmwReaderUnique`/`lockAcqFlowEq`/`lockRelFlowEq` take only the section vars they mention — AxLock3*/AxProtLock3 must not pass Hxy to them. Instance `lock2AxirisG L x γ γc` (reducible def) is named: `@flowEqDyn hlc GF _ (lock2AxirisG L x γ γc) …`. `by_contra` is Mathlib — unavailable.
- AxSpinProt: camera class `SpinlockG GF` (saved pred over Geid; ghost maps Nat→Option Geid and Int→GName×GName) — adequacy must allocate it. iprop `∃` binders with types must each be bracketed: `∃ (γR : GName) (γh : GName) (R : T), …`.
- Stage C: the stageC.md list of "witness files with literal fetch rows" is unreliable (AxDeps and the 4 Rvwmo witnesses had none). A real fetch row = a 4-byte instruction-text read at a pc; 1-byte data `LLoad`s are not fetches. Grep before reworking.
- Stage C: the image pin is `WeakAxRealize.fetchPin img l` (file-qualified; `fetchPin σ es` is WeakCert's, unrelated). Always file-qualify new Lean-only names in rework too.
- Stage C (WeakRvwmoAdm): `hemit` allows no admin items after a row's last event — a fetch that was the last event of a Rocq row must be followed by the next real memory event in Lean (Adm: hart 1 row ends with the `fence r,rw` now).
- AxRunClose: the excluded register set is BOTH pins: `AxRunClose.pinReg r := r = sig_seip ∨ r = sig_meip` (Lean `pinSet` writes either; Rocq `seip_reg` only seip). ~30 downstream Rocq files using peqv/aeqv/gstep/Pbefore/awire_aeqv (AxBoundaryWpd, AxEpiLedger*, AxCjrWpd, AxLdspWpd, AxSmodeProbe, …) use `AxRunClose.pinReg` where Rocq has `regs_agree seip_reg`. `gstep` has no oracle params.
- AxLifting: `wlabel_is_fetch` is DROPPED (Stage C) — the ~11 Rocq uses (AxAdequacy `astep_any_nf`, …) drop the fetch exclusion. `(notElemOfDom (S := GSet Geid))` for GMapF dom lemmas.
- WeakRvwmoCycWit: `WeakRvwmoCycWit.cyBlkSubstPin` discharges Walk's pinned `wwitNd` shape (∀ im, cblkPin); kernel drift: Lean `started` = 0x8000a400. Requests that keep every field but the address: `{ evReqw with pa := a }` (projections rfl).
- AxFetch is split: `Weak.AxFetch` is an umbrella importing AxFetch1 (row shapes, peel, ld8), AxFetch2 (`AxFetch2.fetchPeel`, ld8/sd8 row runs), AxFetch3/3b/3c (jalr/ret, RVC, c.ldsp/c.sdsp, afCldspContRd), AxFetch4 (demo), AxFetch5 (c.jr gate, afCjrRdsAtNextpc, afCjrEpilogueGateSrcs'). Dropped (no fetch row item): af_fetch_ident, af_cfetch_ident, af_*_row_shape_fetch, af_jalr_row_shape, af_cjr_row_shape — downstream (AxRegOnly, AxEpiChain, …) drop their fetch-item premises and fetch steps.
- AxAdequacyChk: `AxAdequacyChk.stepAnnotGen` (+skipCaseGen/evCaseGen) is AxAdequacy.stepAnnot generic in the WP continuation — reuse it for wpc/other continuations. Q8 pin threads only through stepAnnotGen and AxAdequacy.stepAnnot.
- Soundness in iris-lean: Rocq `step_fupdN_soundness(_no_lc)'` = `step_fupdN_soundness_close (hlc := …) n m`; `uPred.pure_soundness` = `Iris.pure_soundness (PROP := IProp GF)` (AxLockRace3).
- AxProtInst declares a GLOBAL `instance axprotPol : Axpol …` (as Rocq). Files importing it get it for every anonymous `[Axpol]` binder — files that need another policy (AxLockGen, …) must pass a local instance / named def explicitly (`@lemma … inst`), never rely on resolution.
- `AxAdequacy.stepFupdNSucc/Zero` need `[AxirisG GF]`; outside an AxirisG context use the instance-free `AxTierA2.stepFupdNSucc/Zero`. `AxirisG.localInterp GD j 0 ls` needs `(GF := GF)`.
- Section `[Axpol]`/`[AxirisG GF]` variables are silently included in theorems (flowEqDynMono, flowEqDynFromFlowin, stepFupdNSucc take AxirisG); use local rfl copies to avoid the dependency. `iapply` does not unify across definitional unfolding — `have h : T := lemma; iapply h` (AxLockAdeq). AxLockAdeq2.lockInitialAlloc allocates history γ + claimed γc (`claimedAllocEmpty`).
- AxProtLock3: policy `lockAxpol` is a NAMED reducible def (not an instance, to avoid clashing with AxProtInst.axprotPol); callers pass it explicitly (`@tierAAdequacyAnn … lockAxpol …`) and use lockAxpolWf/lockAxpolHsPolSub/lockAxpolHlobpSub, `lockHobAlloc hxy` (allocates history + claimed). Ob-state tuple right-nested: σ.1=g, σ.2.1=D, σ.2.2=hm. `iempintro` is the emp tactic.
- flowEqDyn is UNSEALED in Lean: a flow equation proved at one AxirisG instance transfers by `exact` to another with the same obSt/obStInterp (AxLock3Wp; use for AxLock3Wp2/3 instead of copying Rocq scripts).
- AxProtGate: `hOf'`/`naOf'`/`naVal'` take `(γ GD wdat rdat)`; `gateDeliversExpected*`/`axprotgateGateFacts*`/`naPureGlobal*` need `(GF := GF)`; `gateFacts` is `∀ e ∈ gsrcs` (start with `intro e He`). AxLockMutex2: use `AxLockMutex.protInvLock''`, `lockMutexDiscWrite` takes only L, pass `axLockMutexG` explicitly.
- Files with `[AxlogG …]`-free statements that call universe-0 lemmas (gateSrcsDomOfSched): use `{GF : BundledGFunctors.{0,0,0}}` (AxProtGateN).
- AxTokLedger: camera class `LedgerG GF` (GhostMapG GF Int Holder) — adequacy files using the ledger take `[LedgerG GF]` and ALLOCATE via `ledgerAlloc`; `lhCur`=`LH.getLast?.getD ∅`, reuse `lhCurApp`. `icombine Ha Hf gives %h` reads a ghost-map lookup without consuming.
- Concrete GF for a Rocq `#[invΣ]` inside Weak (no Xv6 import): `AxDefer2.refGF` (BundledGFunctors.default |>.set 0..3 InvMapF/CoPsetDisjL/DisjointLeibnizSet PosSet/Auth Credit, ElemG ⟨i, rfl⟩, InvGpreS) — reuse it. `{[k := v]}` is PartialMap.singleton (lookupSingleton/lookupSingletonNe).
- AxEpiSat (Stage C renumbering, CONVENTION for AxEpiAdeq/AxEpiSound3/AxAllHarts): the `c.sdsp; c.ldsp` row is `[SD; LD]` (no fetch items) — `AxEpiSat.eSD = (0,0)`, `AxEpiSat.eLD = (0,1)`, `epiLobp` uses `eidsBefore GD 0 1`; `Hlob_gmo (0,1) (0,3)` becomes `(0,0) (0,1)`; pass `epiPol` explicitly (`@axpolWf epiPol`, `(self := epiPol)`), never an instance. `epi_not_dev2`, eF0/eF1/eF2 dropped.
- `decide +kernel` does not reduce `List.mergeSort` (wf recursion): prove concrete mergeSort results by `List.Perm.eq_of_pairwise` + decided sortedness/distinctness (AxDefer3). `omega` does not see `Nat.max` as `max`.
- AxClsStep: `Aprog` (apHarts/apS0/apImg; no ap_T), `clsStep` has no T; `CSProg` program arm takes the boot-image pin (`WeakAxRealize.fetchPin GD.gdG.gxImg l`) in place of Rocq's `wlabel_is_fetch l = false`. Downstream (AxLedgerG …) drop `ap_T`/`T`.
- AxRowConf: `rowEmittedFromRun` has no `RowEmitFetch` and no T/img — fetches go through `RowEmitAdmin` (AxRunGV etc. drop T/img).
- AxRunGV: `runAtGraphValuesNfGv` takes `hpin : ∀ p d l p' d', pstepProg p d l p' d' → lbAdmin true l → WeakAxRealize.fetchPin GD.gdG.gxImg l` (admin steps may be fetches; discharge from the pinned LTS, cf. AxAdequacy.astepProgNfOfPinned).
- **AxEpiLedger two-pin boundary (CONVENTION, forced by the Lean model reading `sig_meip` then `sig_seip`):** Rocq's single `to_seip` split becomes two: `AxEpiLedger.toPin` (stops at either pin, fails at an sfence announce), first split at `AxEpiLedger.meipNode` (exits `seipExit`, via `AxEpiLedger.wpdOfSplitFrom`), then the `sig_seip` split with `erdExit` as in Rocq. So `branchAt`/`ldBranchAt` take TWO answers, ledgers have FOUR branch fields (`lfBranch00/01/10/11`, `lg..`) plus `lfMeipDr`/`lfMeipD`, `ledgerInv`/`ledgerLdInv` gain a meip disjunct, `AxEpiLedger.ledgerStep` a meip-answer step. Downstream (AxEpiLedgerSd, AxEpiLedgerTick, AxEpiChain*, …) follow this shape. Concrete load facts over a free word: boolean twins + `ax_epi_ledger_krfl`. `ldLoadOk` adds `akIfetch = false` (replaces Hntext).
- AxLedgerG: `polGate` (named def; polGateOk/Wf/Pin), `obStInterpLG`, `ledgerJointGOfJoint`, `progLedgerVerifiedG.mk` (program args take L0, gsF after OC) — AxLedgerG2/3, AxSpinWit reuse. Rocq `LH ++ replicate m c ++ [L']` is right-nested; Lean statements use the left reading (lhCurApp applies).
