# allocproc on RVWMO: target theorem, gap analysis, roadmap (design advisor, 2026-10-09)

**Status: rev 3 = rev 2 + review R2 (5 required changes, tags [R2.n]).**
History: rev 1 (2026-10-09) initial survey; rev 2 (2026-10-09) applied `weak-allocproc-plan-review-R1.md`
(11 required, s1–s5, Q-A..Q-F → D8–D13); rev 3 (2026-10-09) applied `weak-allocproc-plan-review-R2.md`
(5 required, two as [R2.n-alt]; s1–s5; Q-G..Q-J → D14–D17; D18–D19 from the alt findings).

Advisory only; read-only survey of `../xv6iris-weak` (`Weak/`, `Xv6/`, `MachCSL/`), `notes/weak-memory-scope.md`,
`notes/weak-lb-thm2-final.md`, `notes/weak-port-architecture.md`, `claude-notes/completed/{relaxed-rr,
relaxed-ww,weak-memory-lift}.md`, `~/dev/weak-orch/open_questions.txt`.  `file:line` cites this tree.
Sizes: S ≤ 300 lines, M ≤ 800, L ≤ 2k, XL = multi-week / many files.  Unconfirmed claims are **unverified**.

## 0. The two findings that reshape the question

**F1. allocproc is ALREADY fully verified in this tree — on a weak-memory machine, not on SC.**
`Xv6.Allocproc : ALLOCPROC` (`Xv6/LinkAllocproc.lean:14`, proof `Xv6/ProofAllocproc.lean:3623`, 3.6k
lines; spec `Xv6/SpecAllocproc.lean:118` `allocprocPost`, `:204` `wp_allocproc_body`) covers the whole
function on the real image (`allocproc` = 0x80001b72..0x80001c72): the `proc[]` scan with `acquire`/
`release` per slot (interrupts may be ON; the scan runs at a migrating hart via `wpNext`), the inlined
allocpid under `pid_lock` with the 64-word collision scan (Löb-closed outer loop, `PidLock.pidLedger`/
`pidTie`, `Xv6/PidLock.lean:88,113`), `p->state = USED`, `kalloc` (`Xv6/SpecKalloc.lean`, `KallocDefs`),
`proc_pagetable` → `uvmcreate`/`mappages`/`walk`/`kalloc` with PTE writes into fresh OWNED pages
(`Xv6/SpecProcPagetable.lean` `pptPost`), `memset` of the context, `ra = forkret`, `sp = kstack + PGSIZE`,
both failure tails through `freeproc`, and `p->pid`/`p->state` as `p->lock`-protected cells (`procHeld`).
Callees verified too (`Proof{Kalloc,ProcPagetable,Mappages,Walk,Uvmcreate,Memset,Freeproc,Acquire,
Release,Pushoff,Popoff,Mycpu}.lean`, ≈ 10.7k lines).  In the cone of the audited roots
(`tools/ci/roots.txt:6` `xv6FsAdequacy_closed`, via `Xv6/LinkSyscall.lean:84`/`LinkMain.lean:53`).

The memory model under all of that is `MachCSL.TsoMem` (`MachCSL/TsoMem.lean:1-40`; design
`claude-notes/completed/relaxed-rr.md`, `notes/design/tso-memory-model.md`): one total store order with
per-byte write histories, per-hart view FLOORS (a plain load reads at any view ≥ floor: load–load
reordering), store forwarding by author, store buffering, `fencePost` (`:345`: W→R edge drains past the
hart's own last store, R→R edge acquires past the read watermark; `fence rw,w`/`w,w`/`r,w` are NO-OPS,
`:356-364`), `.aq` AMOs, LR/SC reservations, a non-coherent i-cache view `itv` + `fence.i`.  **What it
forbids that RVWMO allows** [R1.7]: (i) store–store reordering and load buffering (stores are never
early) — the same ppo residue as the weak tier's sRVWMO (rules 1–5, 7, 14, `Weak/WeakAxiomatic3.lean:2050-2071`;
divergences LB and reader-fence-only MP, `Weak/WeakSrvwmoLitmus.lean:1663-1695`), **checked by reading,
not by theorem** — nothing relates TsoMem to `srvwmoConsistent`, and after [R2.3] nothing needs to: the
composed statement names `srvwmoConsistent`, TsoMem's strength matters only through the simulation
[R2.s2]; (ii) **reservation serialisation**: a foreign hart's store or exclusive read overlapping a held
reservation is BLOCKED (self-loop `blockedStep`, `MachCSL/Lang.lean:366-378,395-403`), DMA likewise
(`anyReserve`, `:539,562`); the reservation persists until the holder's next store of ANY address
(`MState.store … resv := none`, `:147-153`) or a blocked exclusive read, surviving fences (`MState.fence`,
`:155-163`).  RVWMO's atomicity axiom constrains only SUCCESSFUL LR/SC pairs and sRVWMO keeps exclusives
fused (`WeakAxiomatic3.lean:2070`), so TsoMem is stronger than both.  Harmless for kernel code (locks use
only `amoswap.w.aq`, `Xv6/ProofAcquire.lean:5`), but arbitrary USER code is in the theorem and may
`lr`/`sc`; the SC success predicates are two of the three audited opaques.  Dependency order (ppo 9–13)
is absent in TsoMem — the sound direction.  Honest description of the landed system theorem: "xv6 on
sRVWMO + reservation serialisation", not "on SC".

**F2. The AxSL tier cannot reach allocproc.**  Theorem 2 (`allocpidOpen2`, `Weak/AxSpinT2b2.lean:325`)
covers ≈ 230 dynamic instructions on literal row families and cost ≥ 57k lines (`wc Weak/AxSpin*.lean`
= 88k with shared infrastructure) [R1.s1].  allocproc's dynamic footprint is ≈ 8k instructions for a
64-slot scan plus ≈ 16k per page `memset` × 7 (4 `kalloc` fills of `5` + root/L1/L0 zeroing;
`procPagetableNodes = 3`, `Xv6/SpecProcPagetable.lean:39`) ≈ 120k [R1.s1], with four more lock protocols,
the freelist, private page-table pages.  Literal rows are out; loop-invariant WPd reasoning on the AxSL
tier would be a new programme (XL), and gap (1) would still stand.  Keep Theorem 2 as a validation of
the handle-based lock protocol on riscv.cat; do NOT extend its segment.

## A. The target theorem

**What "credible for xv6" requires** (an xv6/weak-memory expert's checklist):
1. the real kernel binary, and WHICH one [R1.9]: xv6-riscv `b72cbac1` on the project's `verified` branch
   (`notes/STATUS.md:8-11`, `README.md:89-90`) — upstream with two deltas an expert must be told about:
   (a) the per-process root (`p->root`, `sys_chroot`, `igetroot`); (b) upstream's post-`ded23f2`
   allocpid: bounded counter `PIDMAX = 1000` (`Xv6/ProcGeom.lean:80`) + 64-slot liveness scan, inlined
   by gcc (`claude-notes/kernel-defects.md:224-231`) — NOT the textbook monotone `nextpid`.  Every callee
   real, no mocks; failure paths included.  The caller discharges `wp_allocproc_body`'s premises
   (`Xv6/SpecAllocproc.lean:204-224`): `k.tier = KTier.kpt`, `allocprocSlots (= 48) ≤ k.avail`,
   `k.noff + 2 < 2^31`, `"kmem"/"nextpid"/"proc" ∉ k.locks`, `procsInv`, the two `isLock`s,
   `kallocAvail γk on`, `procsAvailAt Γ pav tk`, `□ (killCred -∗ Q (-1))`, `actLend` — kernel-state
   facts, none about memory ordering;
2. harts [R1.1]: **exactly `NCPU = 8`, all booted** (`MachCSL/TsoMem.lean:54`; `PowerOn` forks
   `cpus = List.finRange NCPU`, `MachCSL/Lang.lean:315-320` [R2.s1]; `riscvPowerAdequacy` takes
   `[∗list] cpu ∈ cpus, hartWP …`, `MachCSL/Adequacy.lean:383`) — fewer harts NOT covered (§B(11); D8).
   The other harts run ARBITRARY xv6 kernel/user code verified against the same invariants, interrupts
   on where xv6 allows them, devices as modelled (2 UARTs, PLIC, virtio with DMA as a store-order agent);
3. memory: RVWMO as the ISA defines it — here `rvwmoCatConsistent` (`Weak/AxGraphCat.lean:188`, riscv.cat
   transcription, fidelity by litmus) or the promising machine + `robustMain`; every strengthening NAMED;
4. page tables live: shared kernel table with concurrent hardware A/D write-back (`MachCSL/KptInv.lean:39`
   `pteVariant`, `:85` `kptBody`; TLB `MachCSL/UTlb.lean`), fresh user table private until published;
5. the conclusion is functional AND safety [R1.2][R1.9]: returned slot `&proc[j]`, `j < NPROC`, `p->lock`
   held by the caller, `state = USED`, `pid ∈ [1, PIDMAX]` distinct from every live pid, fresh trapframe
   page (`kalloc`'s fill of 4096 bytes of `5`, `Xv6/SpecKalloc.lean:69`, exposed by `allocprocPost` through
   `procPrivNocwd`, `SpecAllocproc.lean:131`), fresh user table with trampoline + trapframe, context
   `[forkret, kstack+PGSIZE, 0×12]`; or `0` with the lock released and everything freed; **no hart ever
   stuck in the machine semantics** (no Sail event without an answer — `Reducible`); all kernel invariants
   preserved — i.e. exactly `allocprocPost`.  **Panics are NOT excluded**: `panic` is verified with NO
   postcondition, a bare `wpLoop` (`Xv6/SpecPanic.lean:11-14`), its `for(;;)` reducible.  **Nor are two
   reducible spin arms** [R2.4]: a hart self-looping on a foreign reservation (`blockedStep`) and, weak
   side, the memory-blind RETRY self-loop of a hart whose exclusive pair lost (`Weak/WeakEvInst.lean:360-364`).
   The lock cone refutes its own panic arms only as WP facts (`Xv6/ProofRelease.lean:75-77`).  "allocproc
   never panics" is expressible as "no `panic:` bytes in the UART trace" (`uartSentSub`,
   `Xv6/UartTrace.lean:182`, `SpecPanic.lean:36-41`), M–L, new work — D9;
6. axioms `propext`/`Classical.choice`/`Quot.sound` + `bv_decide` certificates + the three opaques
   (`tools/audit/baseline.json:11-14`), no `sorry`; trusted base named: Sail model, image dump, the
   cat/sRVWMO transcriptions.

**Legitimately out of scope:** liveness/fairness, timing, the published Promising-RISC-V ≡ RVWMO
equivalence (D-M6-3), mixed-size fidelity of the cat model (N10), MMIO ordering beyond the modelled
devices, hardware outside the Sail model, and power cycles (SINGLE ERA [R2.2], §B(10)).

**The statement to aim for (two layers, both real theorems):**

*T-alloc (contract layer, exists):* `Xv6.Allocproc` on the MachCSL machine.  Nothing to prove; the
work is to make its memory model honest and composed.

*T-alloc-RVWMO (the credible claim)* [R1.5][R1.2][R1.6][R1.3][R1.4][R2.1][R2.2][R2.3]:
```
∀ (σ0 : WGState) (c : Cand) (pst dv),
  wbootFacts σ0 ∧ σ0.wggen = 0 ∧ (∃ ds, σ0.wgdev = ds.reset ∧ diskOf ds = fsImgDisk) ∧  -- [R2.2] the boot
  c.cdImg = imgZ σ0.wgimg ∧ pst 0 = epsInit σ0 ∧ dv 0 = efInit σ0.wgdev ∧
  execProgOk' (pstepPin (imgZ σ0.wgimg) pstepEv) pclsEv pst dv (candExec c) ∧   -- xv6 is the program (†)
  candExclPaired c pst ∧            -- [R2.3-alt] every exclusive read completes its pair (§B(10))
  consistent c    -- step 1: srvwmoConsistent ("RVWMO, stores never early"); step 2: rvwmo via robustMain
  →
  (a) the realizing MachCSL run (T1 → pf run → W4, PREFIXED by the PowerOn step from the given disk)
      satisfies xv6FsAdequacy_closed's conclusions for ITS ONE ERA: no hart stuck in the machine
      semantics (Reducible of the MachCSL configuration; panics and the two spin arms not excluded),
      xv6TracePure (fs purity + mmOk), the NI/app conclusions; and the realized pf run never enters
      the retry self-loop (free from the shape, [R2.3]); and
  (b) the pid/allocation shadow of allocprocPost, tied to the observation trace κs (W1): every PAlloc
      pid ∈ [1, PIDMAX] and the counter tie (nextOf); KAlloc/KNull/KFree well-formed (poolEmpty on
      KNull); every fork return at a `uEnter` carries a0 ∈ {-1} ∪ [1, PIDMAX] with a matching PAlloc
      receipt — and, after W1b, live pids pairwise distinct.
```
(†) The pinned conformance premise is `xv6SrvwmoSafe`'s (c)-premise (`Weak/WeakSrvwmoCapstone.lean:76-102`);
it restricts the theorem to runs whose every fetch answers the BOOT IMAGE at timestamp 0 — kernel code
only; the fork path needs W5d's unpinned form, §B(4) [R2.1-alt].  The boot premises are
`xv6FsAdequacy_closed`'s (`Xv6/LinkSystemAdequacyClosed.lean:20-26`: `g.gen = 0`, `g.pow = false`,
`diskOf g.m.devs = fsImgDisk`) transposed through `PowerOn`'s hand-over (`bootShape`/`bootFacts`,
`MachCSL/Lang.lean:294-304`: `mem = imgFlat bootImage`, empty log, zero views, boot-program register
files, `devs = g.m.devs.reset`) to `wbootFacts` (`Weak/WeakLang.lean:482-490`, the same clauses with
`∃ ds, wgdev = ds.reset`; `diskOf (ds.reset) = diskOf ds` by `rfl`, `Xv6/BootSharedDev.lean:283`).  T1 alone
yields `execWf (candExec c)`, a run of the MEMORY-ONLY machine `mstep` (`Weak/WeakAxiomatic.lean:273-277`),
so `execProgOk'` (`Weak/WeakAxRealize.lean:373-386`, un-fusing RMWs via `lblRealizesPair`) is a genuine
hypothesis and `execWfPfRunProg` (`:802-808`) the lift [R1.5].  (b) is the trace-observable shadow of
`allocprocPost` in the NI idiom (ghost ledgers tied to the OBSERVATION trace, `xv6NiPhi`,
`Xv6/NiAdequacy.lean:7-9`, `Xv6/LinkNiAdequacy.lean:100`; the tie makes (b) falsifiable) [R1.4].

## B. Gap analysis

Legend: *need* = needed for T-alloc-RVWMO; *route* = (M) machine tier / (A) AxSL tier.

**(1) AxSL tier not composed with the machine tier.**  Need: only on route (A).  No cheap AxSL soundness
theorem exists.  Present: `t2Ev` (`Weak/WeakEvInst.lean:2046`), `hemitAstep`, T1 `srvwmoRealizable`
(`Weak/WeakAxiomatic3.lean:2077`), `rule14Linearization`.  Missing: (i) pf run ⇒ `srvwmoConsistent` (T2
proper; route (M) does NOT need it [R1.5]); (ii) sRVWMO `Cand` ⇒ tagged `GdexecT` with `rvwmoCatConsistentT`
+ ctrl closure — two hand-written models to relate; (iii) the per-hart opax runs of `tierAAdequacy`
(`Weak/AxTierA.lean:91-98`) from the pf run's program half (both over `MachCSL.riscvStep`,
`Weak/WeakEvInst.lean:286`); (iv) the row-family premises (`allocPre`, Option V pins, warm TLB, SIE=0) fail
on real executions; prefix closure informal (`Weak/AxSpinT2b2.lean:126`).  XL, conditional on (iv).
*Treatment:* do not pursue; record Theorem 2 as a riscv.cat-tier validation.

**(2) Page tables (HAD, read-only PTE pages, identity map, warm TLB).**  Route (M): CLOSED — the kernel
table is a live shared invariant with A/D variants (`KptInv.pteVariant`), `utlbOk` caches leaves "up
to the A/D bits" (`MachCSL/UTlb.lean:17-21`), hit/miss/fill/write-back modelled (`UFetchWalk`,
`WpPtWalk*`) [R1.s3]; user-table pages are fresh owned memory (`pptPost`'s `procPtAt`), published at
`satp` write + `sfence.vma` (`MachCSL/WpSmodeKpt.lean`).  Named assumption (§B(11)): Svadu A/D
write-back as a plain view-neutral LR/SC.  Route (A): L–XL.  Size (M): S (documentation).

**(3) SIE = 0, 3 harts, no devices/DMA.**  Route (M): CLOSED (`KCtx.sie`, `wpNext`, `NCPU = 8` exactly
[R1.1], DMA at the store order, `MachCSL/Lang.lean:1-60`).  Route (A): excluded (`devAddr = false`, N6).

**(4) Text never written / fetch pinned** [R1.8][R2.1][R2.1-alt].  The fetch-view premise is carried by
BOTH weak capstones: `xv6SrvwmoSafe` (b') (`Weak/WeakSrvwmoCapstone.lean:88-89`) and `xv6RvwmoSafeModulo`
(`Weak/WeakRvwmoCapstone.lean:195`) take `∀ ρ, rtc epfRun (epInit gen, σ0) ρ → efetchItvOk ρ.1 ρ.2`
(`efetchItvOk`, `Weak/WeakEvCapstone.lean:681-685`: a view-0 admissible fetch is admissible at the hart's
`wgitv`), because the run-level lift pf → event language `wpPfRtcEpfRtc` (`:1008-1011`) needs it, and
the FIRST conjunct of `xv6SrvwmoSafe` calls it with `Hcov` (`WeakSrvwmoCapstone.lean:116`).  Rev 2's
"route (M) never uses it" and "Stage 1 does not need W3" were wrong [R2.1].  It cannot be discharged
weak-side on route (M): it ranges over ALL `epfRun`-reachable states and "text never written" is
kernel-verification content only the MachCSL state interpretation carries.  Treatment: (i) W5 does NOT
go through `epfRun`; it starts from `execWfPfRunProg`'s `rtc (wpPfRun pstepEv pclsEv) (wpInit …) c`
(`Weak/WeakAxRealize.lean:802-808`, via `wpPfRunPinSub` as at `WeakSrvwmoCapstone.lean:115`), and W4
projects `wpPfRun` runs (the pf machine WITH program, `Wpcfg Pexv6 Efab`), not `epfRun`.  (ii) The (↓)
`LIFetch` row of W2 then carries the content: the pf fetch is admissible at floor 0 (`PFIFetch`,
`Weak/WeakPromiseBridge.lean:444-450`: any existing version) while TsoMem fetches as the i-cache agent at
`σ.itv cpu ≤ tvn ≤ top` (`MachCSL/Lang.lean:360-362`, latest version ≤ tvn, no forwarding); the row
closes iff no log write hits the fetched bytes between the version read and `itv`.  For KERNEL text
that is `kernelTextUnwritten` (W3) at the related MachCSL prefix — W3's LEMMA is on the Stage-1 critical
path (D5).  **[R2.1-alt] — what R2 missed: the pin.**  `execWfPfRunProg` requires `pstepPinned`, and the
conformance premise is at `pstepPin` (`WeakAxRealize.lean:184-194`; capstone deviation 4,
`WeakSrvwmoCapstone.lean:40-48`): EVERY fetch label answers the boot image at timestamp 0 (`fetchPin`,
`:160-165`).  User text is written (`uvmfirst`/`exec` fill fresh pages) and `userret`'s `fence.i`
(`Xv6/SpecUserret.lean:6`, `ProofUserret.lean:135`) raises TsoMem's `itv` past those writes, so a pinned
candidate's user fetch (image bytes) has NO TsoMem counterpart: (↓) fails at the first user fetch of a
loaded page.  The pinned theorem therefore covers kernel-only runs — for allocproc, `userinit`'s call
(`Xv6/SpecUserinit.lean:4-14`: boot hart, before any scheduler runs, UNCONTENDED), not the fork path.
Fix = **W5d** (Stage 1b, M–L): an UNPINNED conformance supply whose fetch side condition is Zifencei
admissibility — `ifetchOk img (log at k) (itv of the fetching hart) base tvs`, the event language's own
`elabOk` discipline (`Weak/WeakEvInst.lean:564`; `itv` tracked MachCSL-style, `itvPostMachCSL`,
`Weak/WeakInterp.lean:376-379`) — with its own replay to `wpPfRun` (floor-0 admissibility follows:
`ifetchByteOkb` checks no writes in `(t, max t itv]`, `Weak/WeakPromise.lean:228-231`); then the (↓)
`LIFetch` row holds for user text too (TsoMem reads at `tvn := max t itv`).  Zifencei admissibility is a
NAMED premise on the candidate (like `execProgOk'` itself), discharged by W3 for kernel text and
restrictive only for user code executing self-modified text without `fence.i` — Zifencei's own rule.
(iii) Q4 closes at Stage 1 for the composed theorem (kernel text), Stage 1b for user text; for the weak
capstones it stays a premise (`efetchItvOkRunOfUnwritten`, `WeakEvCapstone.lean:697`, discharges it on
route 9c/W7).  Size: W3 M; W5d M–L.

**(5) Segment coverage; `p->pid`/`p->state` hart-private.**  Route (M): CLOSED (F1).  Route (A): XL (F2).

**(6) Scope pins `npNowrap`/`npNcoll`.**  Route (M): CLOSED — the pid register/ledger handles wrap and
collision retries (`ap_pidloop`, `PidEv.cycAt`, `pidPick`, `Xv6/ProofAllocproc.lean:16-24`).

**(7) Store-value row conditions, image facts, informal prefix closure.**  Route (M): none — the WP is
over the decoded instruction stream, text facts by `rfl`/`decide` against `Xv6/KernelImage.lean`.  CLOSED.

**(8) Stack/cpu privacy as WOK, not points-to.**  Route (M): real resources (`stackOwn`,
`MachCSL/StackOwnBounds.lean`; `kctx`/`ctxTok`).  CLOSED.

**(9) The real gap: TsoMem is sRVWMO + reservation serialisation, not RVWMO** [R1.7].  Need: yes — the
whole weak-memory content of T-alloc-RVWMO.  Three routes:
- (9a) *Name it.*  State T-alloc at `srvwmoConsistent` after the composition §B(10), with the
  reservation strengthening named beside it (W2 settles which discipline is inherited — WeakMem clears
  `wRes` at any non-trivial fence, `Weak/WeakMem.lean:688`, TsoMem keeps it).  Honest and credible as a
  first landing; an expert will note xv6's release idiom (`fence rw,w; sw zero,0(s1)`,
  `Xv6/ProofRelease.lean:83-86`) is load-bearing on real RVWMO and a no-op here (`fenceDrains`), so the
  proof does not exercise it.  Size: §B(10).
- (9b) *Relax the machine to PSO* (`claude-notes/completed/relaxed-ww.md`: two-log machine — issue log +
  drain log, `fence` with a W predecessor waits for own drains; "exactly two ghost steps become
  fence-bound: `ctx_stamp` and `ctx_dom_to_stamped`, both already at a release fence in every xv6 use",
  `:30-41`).  Design on the Rocq-era branch `relaxed-ww-twolog` (`:7`); the Lean port has NONE of it —
  fresh estimate [R1.s4].  "RVWMO minus LB minus dependency order"; makes `fence rw,w` load-bearing.
  Size: L for `TsoMem`/`Lang`/`Ctx`/`Lock` + re-threading.  **unverified** against the Lean tree.
- (9c) *Robustness for LB*: `robustMain` (`Weak/WeakRobustMain.lean:1520`) needs violation-free pf runs
  (φ) + `fetchSrcOk`; the Rocq line found φ REFUTABLE at event granularity
  (`claude-notes/completed/weak-memory-lift.md:19-29`) and closed it only via the block-granular
  `WeakComposeLang.xv6_weak_robust_lifted`, SKIPPED by the port (`notes/weak-port-skip.md:6`).  The
  graph-side `xv6RvwmoSafeModulo` (`Weak/WeakRvwmoCapstone.lean:187`) carries `l2Claim`
  (`Weak/WeakRvwmoGlue.lean:449`) and `walkSupply` (`Weak/WeakRvwmoGlue2.lean:453`).  XL.
*Recommended:* (9a) now, (9b) next machine step (D4), (9c) long-term.

**(10) The machine-tier composition is missing but tractable — a simulation over REALIZED runs**
[R1.6][R2.2][R2.3][R2.3-alt].  The SC tree's adequacy conclusions are trace properties over MachCSL runs
(`MachCSL/Adequacy.lean:266` `riscvPowerAdequacy`, `Xv6/SystemAdequacy.lean:543` `xv6FsAdequacy`:
`Reducible` + `xv6TracePure`, the latter exporting `mmOk g.m` while powered, `Xv6/SystemSlot.lean:135-136`,
`MachCSL/Resources.lean:779` [R1.s2]).  The weak tier's pf machine is `WeakMem` (`Weak/WeakMem.lean`; fence
shape MachCSL's, `Weak/WeakInterp.lean:376`; classifiers MachCSL's, `:34`, `classify :306`); the program half
is literally shared (`MachCSL.riscvStep`, `Weak/WeakEvInst.lean:286`).  So the needed theorem is a
SIMULATION: every `wpPfStep` (`Weak/WeakPromiseBridge.lean:339`) of the realized run is a `MachCSL.primStep`
(`MachCSL/Lang.lean:599`) with the same hart expression and observations.
*(↓) is REFUTED on arbitrary pf runs* [R2.3]: the event instance SPLITS every exclusive access into
`LExLoad`/`LExStore` (`Weak/WeakEvInst.lean:323-331,350-359`); a foreign plain store to the reserved
footprint between the halves is ENABLED in WeakMem (`PFStore`, `WeakPromiseBridge.lean:355-366`, no
reservation guard; the loser's `PFExStore` then fails `exclOkTs`, `Weak/WeakPromise.lean:324-326`, and
retries forever, `WeakEvInst.lean:360-364`) while TsoMem BLOCKS it (`othersReserve`,
`MachCSL/Lang.lean:375-377,395-403`) — the common case of every contended `amoswap.w.aq`.  No lagging
relation rescues it (the weak hart's expression is frozen at the `memWrite` continuation).  What saves
route (M): W5's runs REALIZE fused `LRmw` steps (`Lbl`, `Weak/WeakAxiomatic.lean:87-92`) — `execProgOk'`
realizes each pair by ONE agent: exclusive read, same-agent `admStar`, conditional write
(`Weak/WeakAxRealize.lean:373-386`, `lblRealizesPair :305-313`, `execPrefixPfRunProg :745-751`) — so
nothing foreign intervenes, the `LExLoad` at "the 0 floor" (`WeakPromiseBridge.lean:422-423`) read bytes
`exclOkTs` certifies, and the retry arm never fires.  **[R2.3-alt] — that shape is NOT enough**: a
STANDALONE `LExLoad` (an `lr` whose `sc` fails or never comes) is realizable as a plain `LLoad` label
(`lblRealizes`, `WeakAxRealize.lean:240-243`; `lbNobarex` excludes only `LExStore`, `:100-103`;
`projLbl (LExLoad …) = some (LLoad …)`, `WeakPromiseBridge.lean:545`), and a failing SC writes nothing
(`Xv6/UserMemLrsc.lean:7-12`; the opaques decide).  In TsoMem the dangling reservation blocks every
foreign store to the footprint until the holder's next store (`Lang.lean:147-153`); WeakMem admits
them → (↓) fails even on realized runs.  A standalone `LExLoad` also need not read the top (`LLoad` has
no `lat`) while TsoMem's exclusive read does (`topBytes`, `Lang.lean:369-372`).  Kernel code never does
this (amoswap only); USER code may.  So the shape predicate is `candExclPaired c pst`: every `LExLoad`
of the conformance run is the first half of a `lblRealizesPair` arm — a NAMED premise on the candidate
("every exclusive read completes its pair; a dangling LR or failing SC is outside the theorem"),
listed in §B(11); owner D19.  Removing it would need TsoMem to stop blocking foreign stores against
dangling reservations — a MachCSL change whose AMO-atomicity role is load-bearing for every lock proof
(the pair is two Sail events).  *(↑) receptiveness is NOT available on route (M)* [R2.3(iv)]: the
composed theorem speaks only about realized configurations; weak-side `Reducible` on non-realized
interleavings would need the weak WP package (`wpPackage`, `Weak/WeakRvwmoGlue.lean:338-346`), which xv6
does not have.  So (a) is stated for the realizing MachCSL run; the free weak-side sentence is "the
realized pf run never enters the retry arm" (D15).  W4b is dropped.
*Single era* [R2.2]: `epowerFork` forks no power thread (`Weak/WeakEvLang.lean:201-204`; the weak
language has `WExpr.power`, `Weak/WeakLang.lean:471`, the event language does not), so `xv6FsAdequacy`'s
multi-era conclusions (power cycles, durable recovery) are NOT transported — one era from the given
boot; W4's projected run is prefixed by the `PowerOn` step (D14, [R2.s5]).
*The relation `R`* [R2.s3], fixed in the spike report: TsoMem `tv ↔ wVrNew`, `rv ↔ wVrOld`,
`ownPub ↔ wVwOld`, `coh ↔ wCoh`, histories = log projection, image `imgZ bootImage ↔ imgFlat bootImage`,
`resv ↔ wRes` only while an agent is mid-pair (`R` tracks it), and `itv`: the pf machine has none, so
`R` carries "the MachCSL `itv` is below every fetch's version" — where W3 (kernel text) and W5d's
Zifencei side condition (user text) enter.  Spot checks fine (↓): WeakMem's `fencePost` raises `wVrNew`
to `max wVrOld wVwOld` for `pr,pw` (`WeakMem.lean:674-678`), `wVwOld` = max own-store timestamp
(`storePostD`, `:634`) = TsoMem's `ownPub`, `wVrOld` = `rv`; so `fence rw,rw`/`r,r`/`rw,w` agree.  Open per
label: parked `fence rw,w`/`wRelp` (`WeakMem.lean:640`) vs TsoMem's no-op; `wRes := none` on fences (`:688`)
vs TsoMem keeping it; the `.aq` carried bit (`MachCSL/TsoMem.lean:255-280`); the i-fetch agent (no
forwarding, `Lang.lean:339-341`) vs `LIFetch`; devices/DMA (`Efab` vs `MState.devrt`, `Weak/WeakLang.lean:202`;
`anyReserve` on DMA).  Size: L (↓ on shaped runs) + L (W4) + M (W5b) + M (W5) + M (W5c) + M–L (W5d).
Cheapest credible route; it lifts the WHOLE system theorem, not just allocproc.

**(11) Model fidelity and named assumptions (trusted base, list in the header)** [R1.1][R1.7][R1.s3][R2.4].
Strengthenings beyond RVWMO: "stores never early" (rule 14); reservation serialisation (F1(ii), whichever
discipline W2 shows inherited) with the candidate premise `candExclPaired` (no dangling exclusive reads
[R2.3-alt]).  Machine-model choices: exactly 8 harts all booted; Svadu A/D write-back as a plain
view-neutral LR/SC (`KptInv.pteVariant`, `utlbOk` "up to A/D"); DMA as a store-order agent; **the
instruction-fetch model** (fetch at any view ≥ `itv` by an agent that never authors a store — no
forwarding; only `fence.i` raises `itv`; `itv ≤ tv` not invariant, `MachCSL/TsoMem.lean:34-39`,
`Lang.lean:360-362`, `MState.fence :155-163`) — beyond RVWMO's text (Zifencei), inherited by the composed
theorem, plus the fetch premise of §B(4) (pin, or Zifencei admissibility after W5d); **the SC-failure
model**: exclusive writes never FAIL at the memory in either tier (TsoMem: blocked or appended; WeakMem:
`exclOkTs` or retry) — SC failure is the Sail opaques' program-side decision (`tools/audit/baseline.json:12-14`,
`Xv6/UserMemLrsc.lean:7-12`; D17); single era.  Fidelity: `rvwmoCatConsistent` omits rules 6, RCpc 7, 8
(sound direction), litmus-checked only (`Weak/AxLitmus.lean:29`); sRVWMO is a hand-written strengthening;
Sail fork `070832a1` with `-D SYMBOLIC`; `Xv6/KernelImage.lean` by `tools/dump_kernel.py`.  Keep, list.

**(12) Audit coverage and file layout** [R1.10].  `Xv6/` never imports `Weak/` (0 files); 11 `Weak/` files
import `Xv6`; lake libraries `MachCSL`, `Xv6`, `Weak` in that order (`lakefile.toml:2,27-41`).  So every
composition file lives in `Weak/`, registered in `tools/ci/roots-weak.txt` + `tools/audit/baseline-weak.json`
+ `XV6_AUDIT_MODULES` (`tools/ci/audit.sh:44`; today the 8 T2 modules), built/audited by `--weak` CI —
whose cone then includes the whole `Xv6` adequacy cone (audit time/memory grow; D13).  Pure-`Xv6/` items
(W1, W3) go to `roots.txt`/`baseline.json`.  Size S.

## C. Roadmap

Each stage ends in a theorem; "∥" = can run in parallel (one Opus worker, one file each).

**Stage 0 — launch now: W3 lemma → W2 spike, ∥ W1, W5b, W5c** [R2.s4] (W2's `LIFetch` row needs W3's statement).
- **W3 `Xv6/TextUnwritten.lean`** (M) [R1.8][R2.1].  Milestone `kernelTextUnwritten`: no reachable store
  (hart or DMA) targets `[text, etext)`, as a trace export of the state interpretation (`imgByte`
  persistence + the store leaves' ownership premise).  On the Stage-1 critical path (§B(4)); its
  corollary for the weak capstones (`efetchItvOkRunOfUnwritten`) needs W4's log projection (consumer
  W7).  Deps: none.  `roots.txt`/`baseline.json`.
- **W1 `Xv6/AllocprocTrace.lean`** (M) [R1.3][R1.4].  Milestone `allocprocLedgerAdequacy`, RE-SCOPED to
  what today's ledgers export: `Kev` is `KAlloc p | KNull p | KFree p`, NO page address
  (`Xv6/KallocEv.lean:45-52`), `kmemLedger` ties only counts (`Xv6/KallocDefs.lean:220-222`); `Pev` is
  `PAlloc act pid | PFree act pid`, NO slot index (`Xv6/PidEv.lean:50-55`); `liveOf` is a SET (`:69`), so
  "live pids pairwise distinct" is vacuous on `h`; `pidLedger` (`Xv6/PidLock.lean:113-114`) carries only
  `liveOf h = dom R ∧ pidTie`, its cell side existential (`pidCells`, `:85`) — slot uniqueness is not an
  invariant of the tree (`claude-notes/kernel-defects.md:249-250`).  So W1 states, as a pure predicate
  on the exported histories: every `PAlloc` pid ∈ [1, PIDMAX] and the counter tie (`nextOf`,
  `PidEv.lean:77`); `KAlloc`/`KNull` well-formedness (`poolEmpty` at every `KNull`, `KallocEv.lean:72`);
  the slot-exhaustion receipt.  **Tie to the observation trace** (β, recommended; D11): `Obs.uEnter cpu
  satp epc gprs` carries the register file at the user boundary (`MachCSL/Lang.lean:243-249`), so a
  fork's returned pid is in `κs` (`gprsA0`/`enterA0`, `Xv6/NiTrace.lean:546,555-558` [R2.s1]) and the
  per-call receipt `pidAllocRcpt` (`PidLock.lean:118-119`, `pid = pidPick PIDMAX prefix`) is cited against
  it; the dispatcher's fork row (`r = -1 ∨ 1 ≤ sint r ≤ PIDMAX`, `kernel-defects.md:245-246`) is the
  bridge.  Alternative (α): a STATE predicate on `g2.m` in the `mmOk` idiom (`Xv6/SystemSlot.lean:135-136`),
  needing a lock-free caveat (pid cells sit in `pid_lock`'s payload).  Derived as an
  `xv6PowerAdequacyGen` hook (`Xv6/SystemAdequacy.lean:277`).  Deps: none; `roots.txt`/`baseline.json`.
- **W1b (owner-gated, L, serial, shared files)**: strengthen `pidLedger` with a history-wide `pidHistWf h`
  (every `PAlloc` = `pidPick` of its prefix ⇒ live pids distinct by induction) and re-thread
  `ProofAllocproc`/`ProofFreeproc`/`NiLedger`; optionally add addresses to `Kev` (ripples through
  `ProofKalloc`, `ProofKfree`, `NiLedger`, `UnionOutLed`, every ledger consumer) for page disjointness.
  Only this yields "live pids/slots pairwise distinct", "allocated pages disjoint from the free list"
  as exported facts.  Not Stage 0; D10.
- **W2 `Weak/TsoOfPf.lean`** (L; spike first, ≤ 200 lines, risk report first) [R1.11][R2.3][R2.s3].
  Milestone `pfStepTso`: for every memory label (load/store/fence/AMO/LR-SC halves/ifetch), a `wpPfStep`
  from an `R`-related state (§B(10)) under the shape predicate `pairAdjacent` (between an agent's
  `PFExLoad` and its `PFExStore` only that agent steps; the `PFExStore` is the realization arm, not the
  retry; no standalone `PFExLoad` — `candExclPaired`) is a TsoMem step with the same bytes, to a related
  state.  The spike report: PER LABEL (one row per exclusive half) the (↓) column; fence spot checks
  recorded as done; `R` fixed; §B(10)'s open items settled; the (↑) column recorded as NOT CLAIMED.
  Deps: W3's statement.  **STOP rule**: a WeakMem behaviour TsoMem lacks on a SHAPED run → STOP, report (D7).
- **W5b `Weak/PfRunShape.lean`** (M) [R2.3(iii)].  Milestone `execPrefixPfRunProgShaped`: the existing
  replay returns only `∃ c, rtc …` (`WeakAxRealize.lean:745-751`); this variant carries `pairAdjacent`
  (and, under `candExclPaired`, "no standalone `PFExLoad`") along the run — a new theorem in `Weak/`,
  not a change to `WeakAxRealize`.  Deps: none.
- **W5c `Weak/SrvwmoXv6Witness.lean`** (M) [R2.5].  Non-vacuity certificate: no theorem in the tree says
  any `srvwmoConsistent ∧ execProgOk'` candidate of the xv6 boot exists (the `WeakRvwmoConfWit*`
  witnesses are two-event `rvwmoMinusDepsConsistent` graphs, `Weak/WeakRvwmoConfWit2.lean:1-40`, not
  program-conformant sRVWMO candidates).  Build a concrete `Cand` for a boot prefix — the `sw &started`
  block of `main` as `WeakEvStarted`/`WeakRvwmoConfWit` build it — with both halves: `smC`/
  `smSnocConsistent` already give the consistency half of exactly this block (`Weak/WeakRvwmoCert.lean:522-546`);
  the program half via `execProgOk'Snoc`/`execProgOk'SnocPair` (`:413,453`) and `certBlockSnoc`
  (`Weak/WeakRvwmoCert2.lean:957-975`; the empty candidate's `execProgOk'` is vacuous), plus
  `candExclPaired`.  A witness through a USER fetch (to show W5d's unpinned premise set satisfiable on
  the fork path) is a full boot replay — not scheduled; D16/D18.  Register beside W5.  Deps: none.

**Stage 1 — the composed sRVWMO theorem (after W2).**
- **W4 `Weak/MachOfPf.lean`** (L) [R2.1][R2.2][R2.3].  Milestone `machRunOfPfRun`: a `pairAdjacent`
  `rtc (wpPfRun pstepEv pclsEv)` run from `wpInit (imgZ bootImage) (efInit (ds.reset)) (epsInit σ0)`,
  PREFIXED by the `PowerOn` step from `([Expr.power], ⟨…, ds, …⟩, gen 0, pow off)`, is a `-<κs>->ₜₚ^[n]`
  run of MachCSL whose state after `PowerOn` is the projection of `σ0` (image tie in `R`), same hart
  expressions, same observations (`hartObs`), devices aligned.  Deps: W2, W3.
- ~~W4b receptiveness~~ — dropped [R2.3(iv)]: only with a weak WP package (none for xv6).
- **W5 `Weak/SrvwmoXv6Adequacy.lean`** (M) [R1.5][R1.10][R2.1][R2.2].  Milestone **T-alloc-sRVWMO**: from
  §A's premises — `wbootFacts σ0`, `σ0.wggen = 0`, the disk, the (c)-premises of `xv6SrvwmoSafe`,
  `candExclPaired` — T1 (`srvwmoRealizable`) + `execWfPfRunProg` + `wpPfRunPinSub` + W5b give the shaped
  `wpPfRun` run (NOT `xv6SrvwmoSafe`'s `epfRun` first conjunct, which needs (b')); W4 projects it;
  `xv6FsAdequacy_closed` and W1 conclude for the one era.  Header: named strengthenings and trusted
  base (§B(11)), SINGLE ERA, kernel-only (pinned) coverage until W5d, `mmOk` at every reachable state
  [R1.s2].  Lives in `Weak/`; `roots-weak.txt`/`baseline-weak.json`/`XV6_AUDIT_MODULES`; `--weak` CI builds
  the full `Xv6` cone.  Deps: W1, W4, W5b; W5c as publication gate (D16).

**Stage 1b — the fork path (after W5).**
- **W5d `Weak/PfRunUnpinned.lean`** (M–L) [R2.1-alt].  Milestone `execWfPfRunProgF`: the replay of
  `execWfPfRunProg` at the UNPINNED `pstepEv` with the Zifencei fetch side condition (§B(4)) in place of
  `fetchPin`; W4's `LIFetch` row for user text; W5 restated with the new supply — the first form of
  T-alloc-RVWMO in which a `fork` syscall (user → `ecall` → `sys_fork` → `allocproc`, contended `p->lock`
  acquires from 7 scheduling harts) is a realizable candidate.  Deps: W5; D18.

**Stage 2 — towards RVWMO proper (owner decision D4 first).**
- **W6 (option 9b) PSO machine** (L, fresh estimate [R1.s4], serial, MachCSL change): `TsoMem` two-log
  drain semantics per `relaxed-ww.md` §1; `fenceDrains` load-bearing for W predecessors; re-thread
  `Lock`, `Ctx` (`ctx_stamp`/`ctx_dom_to_stamped` fence-bound), `WpSmodeFencePub`, the lock Spec/Proofs;
  full `lake build` + audit.  Then W2/W4 re-checked (`R` gains the drain log).  Milestone:
  `xv6FsAdequacy` on "RVWMO minus LB minus deps".
- **W7 (option 9c) robustness composition** (XL): revive `WeakComposeLang` (block-granular cone
  premises) or discharge `l2Claim`/`walkSupply` for xv6; consumes W3's corollary (Q4 closes for the weak
  capstones here) [R1.8].  Milestone: `xv6FsAdequacyRvwmo`.  Not before W5.

**Stage 3 — optional, AxSL tier.**  Park Theorem 2's segment; tying the AxSL tier in is §B(1)(i)–(iii)
(XL) — recommend NOT scheduling.

**Launch now:** W3 lemma first, then W2 spike (per-label (↓) table with `R` fixed) ∥ W1 ∥ W5b ∥ W5c —
independent files, none touching shared `MachCSL/` (W2's spike is read-only on it).  W1b waits for
D10; W5d for D18.

## D. Owner questions (recommended option first)

- **D1. Tier.**  (Rec) machine tier (SC tree + composition, §C), retiring further AxSL segment work;
  (b) extend Theorem 2's segment (XL, still gap (1)).
- **D2. First landing statement.**  (Rec) T-alloc-sRVWMO with the strengthenings named in the header
  ("RVWMO, stores never early" + reservation serialisation + §B(11)); (b) hold publication until RVWMO
  proper (W7, XL).
- **D3. Conclusion form.**  (Rec) trace-level ledger predicate (W1) tied to `κs`, beside the Iris
  contract; (b) Iris contract only (not readable as "a theorem on allocproc" by outsiders).
- **D4. Machine relaxation.**  (Rec) PSO two-log machine (W6) right after W5 — shrinks the named gap to
  LB only and makes `fence rw,w` load-bearing; (b) skip to W7; (c) stay at sRVWMO.
- **D5. Q4 / W3** [R2.1(v)].  W3's lemma is on the Stage-1 critical path (the `LIFetch` simulation row).
  (Rec) launch it first; (b) none — carrying the premise is not available on route (M).
- **D6. Theorem 2.**  (Rec) keep `allocpidOpen2` + certificates as the audited riscv.cat-tier validation
  of the lock protocol; its header already says so (`Weak/AxSpinT2b2.lean:318-324`): one-paragraph note,
  S [R1.s5]; (b) continue the reduce-pins lanes.
- **D7. W2 failure mode** [R2.3].  The split-exclusive divergence is now KNOWN and fixed by the shape
  restriction (`pairAdjacent` + `candExclPaired`), not by a model change.  If the spike finds a FURTHER
  (↓) failure on shaped runs (parked release fence / reservation clearing at fences are the suspects),
  (Rec) change `WeakMem`'s event instance to MachCSL's shape where the kernel proofs allow, else
  (b) accept a MachCSL change (owner-gated, serial).
- **D8. Hart model** [R1.1, Q-A].  (Rec) "exactly 8 harts, all booted" as a named assumption; (b) a
  "≤ 8, some harts never leave `_entry`" variant (MachCSL `PowerOn`/`cpus` change, serial).
- **D9. Panics** [R1.2, Q-B].  (Rec) "no hart stuck in the machine semantics", panics and the two spin
  arms explicitly NOT excluded; (b) add "no `panic:` bytes in the UART trace" (M–L, via `uartSentSub`).
- **D10. W1 scope** [R1.3, Q-C].  (Rec) re-scope to today's ledgers (W1, Stage 0); (b) also W1b
  (strengthen `pidLedger`/`Kev`; L, serial, shared files) for pid/slot uniqueness and page disjointness.
- **D11. W1 tie** [R1.4, Q-D].  (Rec) observation-level (β): fork return at `uEnter` vs `PAlloc` receipts;
  (b) state-level (α) on `g2.m` with the lock-free caveat.
- **D12. Which xv6** [R1.9, Q-E].  (Rec) the `verified`-branch fork (chroot + post-`ded23f2` allocpid),
  named in the header's first sentence; (b) upstream master (header only — and would not match the image).
- **D13. Where the composed theorem lives** [R1.10, Q-F].  (Rec) `Weak/`, audited under `--weak`,
  accepting the full `Xv6` cone in that audit; (b) a separate lake library / CI lane if too costly.
- **D14. Single era** [R2.2, Q-G].  (Rec) "one boot, no power cycles" in the header (allocproc needs
  nothing more); (b) multi-era W4: the weak language's power thread (`WExpr.power`,
  `Weak/WeakLang.lean:471`) in the event pool and `wbootShape` at each `PowerOn` (M on top of W4) [R2.s5].
- **D15. Reading of (a) without W4b** [R2.3, Q-H].  (Rec) "conclusions about the realizing MachCSL run"
  plus the free weak-side sentence "the realized pf run never spins in the retry arm"; (b) no weak-side
  sentence; (c) weak-side `Reducible` — needs a weak WP package for xv6 (XL).
- **D16. Non-vacuity gate** [R2.5, Q-I].  (Rec) W5c (boot-prefix witness) is a publication gate for W5;
  (b) follow-up.  (A user-fetch witness for W5d's premise set is a separate, larger item: D18.)
- **D17. SC-failure disclosure** [R2.4, Q-J].  (Rec) the header names the SC-failure model (opaque
  predicates decide; memory never fails an exclusive write) as a named assumption, since user code is in
  the theorem; (b) §B(11) only.
- **D18. Fork-path coverage vs. the fetch pin** [R2.1-alt].  The pinned premise (†) covers kernel-only
  candidates — for allocproc, `userinit`'s uncontended boot call.  (Rec) land W5 pinned as the
  composition milestone, then W5d (unpinned supply with Zifencei fetch admissibility, M–L) before calling
  the result "a theorem on allocproc under contention"; (b) accept the pinned form as the first landing,
  "kernel-only" in the header; (c) make W5d part of Stage 1.
- **D19. Dangling exclusive reads** [R2.3-alt].  (Rec) publish `candExclPaired` ("every LR completes its
  SC; a failing SC is outside the theorem") as a named premise beside reservation serialisation; (b) a
  MachCSL change so dangling reservations do not block foreign stores (touches the AMO-atomicity argument
  of every lock proof; serial, L, **unverified**); (c) a user-mode WP fact "user code never leaves a
  dangling reservation" — not available, user code is arbitrary.
