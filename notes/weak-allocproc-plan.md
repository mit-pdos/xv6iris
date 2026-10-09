# allocproc on RVWMO: target theorem, gap analysis, roadmap (design advisor, 2026-10-09)

Advisory only; read-only survey of `../xv6iris-weak` (Lean weak tier `Weak/`, the SC/machine tier
`Xv6/` + `MachCSL/`), `notes/weak-memory-scope.md`, `notes/weak-lb-thm2-final.md`,
`notes/weak-port-architecture.md`, `claude-notes/completed/{relaxed-rr,relaxed-ww,weak-memory-lift}.md`,
`~/dev/weak-orch/open_questions.txt`.  `file:line` cites this tree.  Sizes: S ≤ 300 lines,
M ≤ 800, L ≤ 2k, XL = multi-week / many files.  Anything I could not confirm is marked **unverified**.

## 0. The two findings that reshape the question

**F1. allocproc is ALREADY fully verified in this tree — on a weak-memory machine, not on SC.**
`Xv6.Allocproc : ALLOCPROC` (`Xv6/LinkAllocproc.lean:14`, proof `Xv6/ProofAllocproc.lean:3623`,
3.6k lines; spec `Xv6/SpecAllocproc.lean:118` `allocprocPost`, `:204` `wp_allocproc_body`) covers
the whole function on the real image (`allocproc` = 0x80001b72..0x80001c72): the `proc[]` scan with
`acquire`/`release` per slot (interrupts may be ON; the scan runs at a migrating hart via `wpNext`),
the inlined allocpid under `pid_lock` with the 64-word collision scan (Löb-closed outer loop,
`PidLock.pidLedger`/`pidTie`, `Xv6/PidLock.lean:88,113`), `p->state = USED`, `kalloc` (kmem lock +
freelist, `Xv6/SpecKalloc.lean`, `KallocDefs`), `proc_pagetable` → `uvmcreate`/`mappages`/`walk`/
`kalloc` with PTE writes into fresh OWNED pages (`Xv6/SpecProcPagetable.lean` `pptPost`), `memset`
of the context, `ra = forkret`, `sp = kstack + PGSIZE`, both failure tails through `freeproc`, and
`p->pid`/`p->state` as `p->lock`-protected cells (`procHeld`).  Its callees are verified too
(`Proof{Kalloc,ProcPagetable,Mappages,Walk,Uvmcreate,Memset,Freeproc,Acquire,Release,PushOff,
PopOff,Mycpu}.lean`, ≈ 11k lines).  It is in the cone of the audited roots
(`tools/ci/roots.txt`: `xv6FsAdequacy_closed`, via `LinkSyscall`/kfork/userinit).

The memory model under all of that is `MachCSL.TsoMem` (`MachCSL/TsoMem.lean:1-40`; design
`claude-notes/completed/relaxed-rr.md`, `notes/design/tso-memory-model.md`): one total store order
with per-byte write histories, per-hart view FLOORS (a plain load reads at any view ≥ floor:
load–load reordering), store forwarding by author, store buffering, `fence` semantics
`fencePost` (`:345`: W→R edge drains past the hart's own last store, R→R edge acquires past the
read watermark; `fence rw,w`/`w,w`/`r,w` are NO-OPS, `:356-364`), `.aq` AMOs, LR/SC reservations,
a non-coherent i-cache view `itv` + `fence.i`.  **What it forbids that RVWMO allows:** store–store
reordering (stores append in po) and load buffering (stores are never early).  That is exactly the
sRVWMO strengthening of the weak tier (`Weak/WeakAxiomatic3.lean:2050-2071`, rule 14 "stores never
early"; the two deliberate divergences LB and reader-fence-only MP, `Weak/WeakSrvwmoLitmus.lean:1658-1695`).
Dependency order (ppo 9–13) is absent in TsoMem — the sound (weaker-than-RVWMO) direction.
So the honest description of the landed system theorem is "xv6 on sRVWMO", not "on SC".

**F2. The AxSL tier cannot reach allocproc.**  Theorem 2 (`allocpidOpen2`, `Weak/AxSpinT2b2.lean:325`)
covers ≈ 230 dynamic instructions on literal row families and cost ≈ 57k lines in the `AxSpin*`
cone (`wc` of AxSpinT2*/Ap*/Aq*/Rl*/PO*/Hd*/E*/X*/Row*).  allocproc's dynamic footprint is
≈ 8k instructions for a 64-slot scan (64 × acquire/push_off/holding/mycpu/release ≈ 130) plus
≈ 16k per `memset(…, 4096)` page × 4 pages (trapframe + 3 page-table nodes) ≈ 80k instructions,
with four more lock protocols (every `p->lock`, `kmem`), the freelist, and private page-table
pages.  Literal rows are out; loop-invariant WPd reasoning on the AxSL tier for memset/scan would be
a new programme (XL), and gap (1) would still stand.  Recommendation: keep Theorem 2 as what it is
(a validation of the handle-based lock protocol on riscv.cat) and do NOT extend its segment.

## A. The target theorem

**What "credible for xv6" requires** (an xv6/weak-memory expert's checklist):
1. the real kernel binary (`Xv6/KernelImage.lean`, xv6-riscv `b72cbac1`), every callee real, no
   mocks, no hand nodes; failure paths included;
2. N harts (MachCSL `NCPU = 8`), the other harts running ARBITRARY xv6 kernel/user code verified
   against the same invariants (the Iris "rest of the kernel" — this is how the SC tree already
   states it: the third party is every other hart of the whole-system proof), interrupts on where
   xv6 allows them, devices as modelled (2 UARTs, PLIC, virtio with DMA as a store-order agent);
3. memory: RVWMO as the ISA defines it — in this tree `rvwmoCatConsistent` (`Weak/AxGraphCat.lean:188`,
   riscv.cat transcription, fidelity by litmus) or the promising machine + `robustMain`; with every
   strengthening NAMED (today: "stores never early");
4. page tables live: the shared kernel table with concurrent hardware A/D write-back (the SC tier
   has this: `MachCSL/KptInv.lean:39` `pteVariant`, `:85` `kptBody`; TLB `MachCSL/UTlb.lean`), the
   fresh user table as private memory until published;
5. the conclusion is functional AND safety: returned slot `&proc[j]`, `j < NPROC`, `p->lock` held by
   the caller, `state = USED`, `pid ∈ [1, PIDMAX]` distinct from every live pid, fresh trapframe
   page (4096 bytes of `5`), fresh user table with trampoline + trapframe mapped, context
   `[forkret, kstack+PGSIZE, 0×12]`; or `0` with the lock released and everything freed; no hart
   stuck/panicking (`Reducible`), all kernel invariants preserved — i.e. exactly `allocprocPost`;
6. axioms `propext`/`Classical.choice`/`Quot.sound` + `bv_decide` certificates, no `sorry`; the
   trusted base named: the Sail model, the kernel image dump, the cat/sRVWMO transcriptions.

**Legitimately out of scope:** liveness/fairness (spin termination, `kalloc` eventually non-null),
timing, the published Promising-RISC-V ≡ RVWMO equivalence (restated natively, D-M6-3), mixed-size
fidelity of the hand-written cat model (scope N10), MMIO ordering beyond the modelled devices, and
hardware outside the Sail model.

**The statement to aim for (two layers, both real theorems):**

*T-alloc (contract layer, exists):* `Xv6.Allocproc` on the MachCSL machine.  Nothing to prove; the
work is to make its memory model honest and composed.

*T-alloc-RVWMO (the credible claim):*
```
∀ execution E of the xv6 image from power-on on ≤ NCPU harts, E consistent with RVWMO
  (step 1: srvwmoConsistent — "RVWMO, stores never early"; step 2: rvwmo via robustMain):
  (a) no hart of E is ever stuck (Reducible), and
  (b) the pid-ledger / allocation trace of E is well-formed: every PAlloc event has a pid in
      [1, PIDMAX], live pids are pairwise distinct, live slots are pairwise distinct, every
      allocated trapframe / page-table page is disjoint from every other live process's pages
      and from the free list.
```
(b) is the trace-observable shadow of `allocprocPost` (Iris WPs do not export internal state; the
tree already exports ghost ledgers to the adequacy level — `Xv6.xv6NiTwoRun`,
`Xv6/LinkNiAdequacy.lean:100`, "at equal ledger histories" — so this is the idiom to reuse).

## B. Gap analysis

Legend: *need* = needed for T-alloc-RVWMO; *route* = (M) machine tier / (A) AxSL tier.

**(1) AxSL tier not composed with the machine tier.**  Need: only on route (A).  Candid verdict:
there is no cheap AxSL soundness theorem.  What exists: `t2Ev` (`Weak/WeakEvInst.lean:2046`, pf run
⇒ `execWf` execution), `hemitAstep` (conformance IS an opax run), T1 `srvwmoRealizable`
(`Weak/WeakAxiomatic3.lean:2077`, sRVWMO candidate ⇒ pf run), `rule14Linearization`.  Missing:
(i) pf run ⇒ `srvwmoConsistent` candidate (T2 proper; grep finds no such theorem); (ii) sRVWMO
candidate (`Cand`, `WeakAxiomatic3`) ⇒ tagged `GdexecT` with `rvwmoCatConsistentT` + ctrl closure
(`AxGraphCat`/`AxDeps`) — two independently hand-written models to relate; (iii) the per-hart opax
runs `Hrun`/`Hk0`/`Hend` of `tierAAdequacy` (`Weak/AxTierA.lean:91-98`) from the pf run's program
half (plausible: `pstepEv` and `AxOpsem` are both over `MachCSL.riscvStep`, `Weak/WeakEvInst.lean:286`);
(iv) the row-family premises (`allocPre`, Option V pins, warm TLB, SIE=0) must hold of EVERY real
execution — they do not (cold TLB, interrupts), and prefix closure is informal
(`Weak/AxSpinT2b2.lean:126`).  Cost XL and the result would still be conditional on (iv).
*Recommended treatment:* do not pursue for allocproc; record Theorem 2 as a riscv.cat-tier
validation.  The cheapest CREDIBLE composition is on route (M), §B(9).

**(2) Page tables (HAD, read-only PTE pages, identity map, warm TLB).**  Route (M): CLOSED for
allocproc's own accesses — the kernel table is a live shared invariant with A/D variants
(`KptInv.pteVariant`), TLB hit/miss/fill/write-back modelled (`MachCSL/UTlb.lean`,
`UFetchWalk`, `WpPtWalk*`); user-table pages written by `mappages`/`walk` are fresh owned memory
(`pptPost`'s `procPtAt`), published only at `satp` write + `sfence.vma` (`MachCSL/WpSmodeKpt.lean`).
The direct map is xv6's real layout, not an assumption.  Remaining named assumption: the Svadu
A/D write-back is modelled as a plain LR/SC that moves no view (relaxed-rr stage E) — a
hardware-model choice beyond RVWMO's text (implicit accesses), to be stated in the header.
Route (A): L–XL (`AxPtwModel`/`AxPtProt` switch, plan rev 8 (ii)).  Size (M): S (documentation).

**(3) SIE = 0, 3 harts, no devices/DMA.**  Route (M): CLOSED (`KCtx.sie`, `wpNext` migration,
`NCPU = 8`, device fabric with DMA at the store order, `MachCSL/Lang.lean:1-60`).  Route (A):
excluded by design (`devAddr = false`, scope N6).  Size (M): none.

**(4) Text never written / fetch pinned.**  Carried on BOTH tiers (`efetchItvOk`/`fetchSrcOk`,
owner Q4 "leave as premise").  On the machine tier the fact is derivable: kernel text is the
persistent image byte `imgByte` (`notes/design/tso-memory-model.md`: `imgByte a v` at t = 0,
persistent), every store leaf consumes an owned/context byte, and no `↦ₕ` fraction for text bytes
is ever minted — so "no reachable log entry writes a text byte" is a trace export of the state
interpretation.  `WeakEvCapstone.efetchItvOkRunOfUnwritten` (`Weak/WeakEvCapstone.lean:697`)
then discharges the weak-tier premise.  Size M; independent; fixes an existing honesty debt.

**(5) Segment coverage; `p->pid`/`p->state` hart-private.**  Route (M): CLOSED (F1).  Route (A):
XL (F2).  Size (M): none.

**(6) Scope pins `npNowrap`/`npNcoll`.**  Route (M): CLOSED — the pid register/ledger handles wrap
and collision retries (`ap_pidloop`, `PidEv.cycAt`, `pidPick`, `Xv6/ProofAllocproc.lean:16-24`).

**(7) Store-value row conditions, image facts, informal prefix closure.**  Route (M): none exist —
the WP is over the decoded instruction stream, text facts by `rfl`/`decide` against
`Xv6/KernelImage.lean`.  CLOSED by construction.

**(8) Stack/cpu privacy as WOK, not points-to.**  Route (M): real resources (`stackOwn`,
`MachCSL/StackOwnBounds.lean`; `kctx`/`ctxTok`).  CLOSED.

**(9) NEW — the real gap: TsoMem is sRVWMO, not RVWMO** (stores never early: no W→W reordering,
no LB).  Need: yes — this is the whole weak-memory content of T-alloc-RVWMO.  Three routes:
- (9a) *Name it.*  State T-alloc at `srvwmoConsistent` ("RVWMO with stores never early") after the
  composition §B(10).  Honest and credible as a first landing; an expert will note that xv6's
  release idiom (`fence rw,w; sw lk,0`) is load-bearing on real RVWMO and is a no-op here
  (`fenceDrains`), so the proof does not exercise it.  Size: §B(10).
- (9b) *Relax the machine to PSO* (`claude-notes/completed/relaxed-ww.md`: design checkpoint,
  two-log machine — issue log + drain log, store pending in a per-hart buffer, `fence` with a W
  predecessor waits for own drains; "exactly two ghost steps become fence-bound: `ctx_stamp` (the
  lock's release) and `ctx_dom_to_stamped`, both already at a release fence in every xv6 use").
  Never implemented in Lean.  Moves the machine to "RVWMO minus LB minus dependency order" and
  makes `fence rw,w` load-bearing.  Size: L for `TsoMem`/`Lang`/`Ctx`/`Lock` + re-threading; the
  design predicts few whole-function proofs move.  **unverified** against the Lean tree.
- (9c) *Robustness for LB*: `robustMain` (`Weak/WeakRobustMain.lean:1520`, promising → pf) needs
  violation-free pf runs (φ) + `fetchSrcOk`; the Rocq line found φ REFUTABLE at event granularity
  (`claude-notes/completed/weak-memory-lift.md`, finding 1) and closed it only through the
  block-granular cone composition `WeakComposeLang.xv6_weak_robust_lifted`, which the Lean port
  SKIPPED (`notes/weak-port-skip.md`).  The graph-side alternative `xv6RvwmoSafeModulo`
  (`Weak/WeakRvwmoCapstone.lean:187`) carries `l2Claim` (`Weak/WeakRvwmoGlue.lean:449`, "L2′
  proper, the project's remaining content") and `walkSupply` (`Weak/WeakRvwmoGlue2.lean:453`).
  Either way XL.
*Recommended:* (9a) now, (9b) as the next machine step (owner question D4), (9c) as the long-term
programme.

**(10) NEW — the machine-tier composition is missing too, but it is tractable.**  The SC tree's
adequacy conclusions are trace properties over MachCSL runs (`MachCSL/Adequacy.lean:266`
`riscvPowerAdequacy`, `Xv6/SystemAdequacy.lean:543` `xv6FsAdequacy`: `Reducible` + `xv6TracePure`).
The weak tier's pf machine is `WeakMem` (`Weak/WeakMem.lean`), strictly RICHER in restrictions than
TsoMem (per-register dependency views, message classes, parked release fence; the fence shape is
MachCSL's, `Weak/WeakInterp.lean:376`; the access classifiers are MachCSL's, `:34`,
`classify :306`).  The program half is literally shared (`MachCSL.riscvStep`,
`Weak/WeakEvInst.lean:286`).  So the needed theorem is a SIMULATION, not a re-verification:
every `wpPfStep` (`Weak/WeakPromiseBridge.lean:339`) / `epfRun` step of the event language is a
`MachCSL.primStep` (`MachCSL/Lang.lean:599`) with the same hart expression and observations; then
T1 (`srvwmoRealizable`) + the simulation give: every sRVWMO-consistent execution is realized by a
MachCSL run, to which `xv6FsAdequacy` applies.  Risks to check first (spike): WeakMem's parked
`fence rw,w` / release-pending `w_relp` vs TsoMem's no-op; `.aq` carried bit `hr.acq`
(`MachCSL/TsoMem.lean:255-280`) vs WeakMem's; reservation blocking (`othersReserve :247`) vs
WeakMem's `Wresv`; the i-fetch agent; devices (`Efab` vs `MState.devrt`, "Lean-only, as
MachCSL.MState.devrt", `Weak/WeakLang.lean:202`).  Size: L (pure simulation) + L (language lift)
+ M (corollary).  This is the cheapest credible route to a composed statement, and it lifts the
WHOLE system theorem, not just allocproc.

**(11) Model fidelity (trusted base, name in the header).**  `rvwmoCatConsistent` omits rules 6,
RCpc 7, 8 (sound direction) and is checked by litmus only (`Weak/AxLitmus.lean:29`); sRVWMO is a
hand-written strengthening; the Sail fork `070832a1` with `-D SYMBOLIC`; two opaque reservation
predicates; `Xv6/KernelImage.lean` by `tools/dump_kernel.py`.  Treatment: keep, list.

**(12) Audit coverage.**  Weak theorems are audited only for the 8 T2 modules
(`tools/ci/audit.sh:44`); the machine route rides the audited Xv6 roots.  New composition files must
be added to `tools/ci/roots.txt` / `tools/audit/baseline.json`.  Size S.

## C. Roadmap

Each stage ends in a theorem; "∥" = can run in parallel (one Opus worker, one file each).

**Stage 0 — launch now (∥ W1, W2, W3).**
- **W1 `Xv6/AllocprocTrace.lean`** (M).  Milestone `allocprocLedgerAdequacy`: the trace-level
  shadow of `allocprocPost` on the MachCSL machine — from the pid ledger (`PidLock.pidLedger`,
  `pidTie`, `pidAllocRcpt`) and the kalloc ledger (`KallocDefs.kmemLedger`), a pure predicate on
  the exported histories: every `PAlloc` pid ∈ [1, PIDMAX], live pids pairwise distinct, live slots
  distinct, allocated pages disjoint from the free list; derived as an `xv6PowerAdequacyGen` hook
  in the `xv6NiAdequacy` idiom (`Xv6/NiAdequacy.lean`, `Xv6/LinkNiAdequacy.lean:100`).  Deps: none.
  This is the "real verified theorem on allocproc" an outsider can read without Iris.
- **W2 `Weak/TsoOfPf.lean`** (L; spike first, ≤ 200 lines, report the risk list of §B(10)).
  Milestone `pfStepTso`: for every memory label (load/store/fence/AMO/LR-SC/ifetch), a `WeakMem`
  pf step from a state related by `R` (views: TsoMem floor ≤ WeakMem effective view; histories =
  log projection; reservations; `itv`) is a TsoMem step with the same bytes, to a related state.
  Deps: none.  If the spike finds a WeakMem behaviour TsoMem lacks, STOP and report (the fix would
  be a MachCSL change — owner-gated).
- **W3 `Xv6/TextUnwritten.lean`** (M).  Milestone `kernelTextUnwritten`: no reachable store (hart or
  DMA) targets `[text, etext)`, as a trace export of the state interpretation (`imgByte` persistence
  + the store leaves' ownership premise); corollary discharging `efetchItvOk`/`fetchSrcOk` via
  `efetchItvOkRunOfUnwritten`.  Deps: none.  Closes owner Q4.

**Stage 1 — the composed sRVWMO theorem (after W2).**
- **W4 `Weak/MachOfEpf.lean`** (L).  Milestone `machRunOfEpfRun`: an `epfRun` of `WeakEvLang` from
  `epInit` projects to a `MachCSL.primStep` run (`-<κs>->ₜₚ^[n]`) with the same hart expressions,
  the same observations (`hartObs`), and devices aligned.  Deps: W2.
- **W5 `Xv6/SrvwmoAdequacy.lean`** (M).  Milestone **T-alloc-sRVWMO**: for every `srvwmoConsistent`
  candidate of the image (T1 `srvwmoRealizable` → pf run → W4 → MachCSL run) the conclusions of
  `xv6FsAdequacy_closed` and of W1 hold.  Header lists the named strengthening ("stores never
  early") and the trusted base (§B(11)).  Add to `roots.txt`/audit.  Deps: W1, W4.

**Stage 2 — towards RVWMO proper (owner decision D4 first).**
- **W6 (option 9b) PSO machine** (L, serial, MachCSL change): `TsoMem` two-log drain semantics per
  `relaxed-ww.md` §1; `fenceDrains` becomes load-bearing for W predecessors; re-thread `Lock`,
  `Ctx` (`ctx_stamp`/`ctx_dom_to_stamped` fence-bound), `WpSmodeFencePub`, the lock Spec/Proofs;
  full `lake build` + audit.  Then W2/W4 are re-checked (the relation `R` gains the drain log).
  Milestone: `xv6FsAdequacy` on "RVWMO minus LB minus deps".
- **W7 (option 9c) robustness composition** (XL): either revive `WeakComposeLang` (block-granular
  cone premises `xv6_cone_premises`) or discharge `l2Claim`/`walkSupply` for xv6.  Milestone:
  `xv6FsAdequacyRvwmo`.  Not before W5 lands.

**Stage 3 — optional, AxSL tier.**  Park Theorem 2's segment; if the owner wants the AxSL tier tied
in, the item is §B(1)(i)–(iii) (XL) — recommend NOT scheduling.

**First three work items to launch now:** W1 (`Xv6/AllocprocTrace.lean`), W2 spike
(`Weak/TsoOfPf.lean`, risk report first), W3 (`Xv6/TextUnwritten.lean`).  All three are
independent, each one file, none touches shared `MachCSL/` (W2's spike is read-only on MachCSL).

## D. Owner questions (recommended option first)

- **D1. Tier.**  (Rec) Build the allocproc theorem on the machine tier (SC tree + composition,
  §C), retiring further AxSL segment work; (b) extend Theorem 2's segment (XL, still gap (1)).
- **D2. First landing statement.**  (Rec) T-alloc-sRVWMO with the strengthening named in the
  theorem's header ("RVWMO, stores never early"); (b) hold publication until RVWMO proper (W7, XL).
- **D3. Conclusion form.**  (Rec) trace-level ledger predicate (W1) beside the Iris contract;
  (b) Iris contract only (not readable as "a theorem on allocproc" by outsiders).
- **D4. Machine relaxation.**  (Rec) schedule the PSO two-log machine (W6) right after W5 — it
  shrinks the named gap to LB only and makes xv6's `fence rw,w` load-bearing; (b) skip to W7;
  (c) stay at sRVWMO.
- **D5. Q4 now.**  (Rec) launch W3 (text-unwritten lemma) now; (b) keep the premise carried.
- **D6. Theorem 2.**  (Rec) keep `allocpidOpen2` + certificates as the audited riscv.cat-tier
  validation of the lock protocol, header amended to say so; (b) continue the reduce-pins lanes.
- **D7. W2 failure mode.**  If the spike shows WeakMem admits a step TsoMem lacks (parked release
  fence is the suspect), (Rec) change `WeakMem`'s event instance to MachCSL's fence shape where
  the kernel proofs allow, else (b) accept a MachCSL change (owner-gated, serial).
