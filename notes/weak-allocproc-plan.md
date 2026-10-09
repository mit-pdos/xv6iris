# allocproc on RVWMO: target theorem, gap analysis, roadmap (design advisor, 2026-10-09)

**Status: rev 4 = rev 3 + review R3 (4 required changes, tags [R3.n]) + owner rulings [OWN.1–4]
(D1 machine tier; D2 FULL RVWMO is THE target; D18 W5d in the target; D12 the `verified` fork).**
History: rev 1 (2026-10-09) initial survey; rev 2 applied `weak-allocproc-plan-review-R1.md` (11 required,
s1–s5, D8–D13); rev 3 applied `…-R2.md` (5 required, two [R2.n-alt]; D14–D19); rev 4 (2026-10-09) applied
`…-R3.md` (4 required; s1–s5; Q-K..Q-N → D20–D23) and `allocproc_revise3_extra.txt` [OWN.1–4]: §A/§B(9)/§C
restructured around RVWMO proper; D24–D26 from that restructuring.

**The kernel [OWN.4][R1.9]: xv6-riscv `b72cbac1`, branch `verified`** (`notes/STATUS.md:8-11`, `README.md:89-90`)
= upstream plus (a) a per-process root (`p->root`, `sys_chroot`, `igetroot`, root-aware `dirlookup`/walk) and
(b) upstream's post-`ded23f2` allocpid — bounded counter `PIDMAX = 1000` (`Xv6/ProcGeom.lean:80`) with a 64-slot
liveness scan, inlined by gcc into `allocproc+0x38..+0x94` (`claude-notes/kernel-defects.md:224-231`) — not the
textbook monotone `nextpid`.  Image `Xv6/KernelImage.lean` by `tools/dump_kernel.py`.

Advisory only; read-only survey of `../xv6iris-weak` (`Weak/`, `Xv6/`, `MachCSL/`), `notes/weak-memory-scope.md`,
`notes/weak-port-architecture.md`, `claude-notes/completed/{relaxed-rr,relaxed-ww,weak-memory-lift}.md`,
`claude-notes/design/{weak-memory-route-b,weak-memory-m6-robustness}.md`, `~/dev/weak-orch/open_questions.txt`.
Sizes: S ≤ 300 lines, M ≤ 800, L ≤ 2k, XL = multi-week / many files.  Unconfirmed claims are **unverified**.

## 0. The two findings that reshape the question

**F1. allocproc is ALREADY fully verified in this tree — on a weak-memory machine, not on SC.**
`Xv6.Allocproc : ALLOCPROC` (`Xv6/LinkAllocproc.lean:14-16`, proof `Xv6/ProofAllocproc.lean:3623-3639`, 3.6k
lines; spec `Xv6/SpecAllocproc.lean:118` `allocprocPost`, `:204` `wp_allocproc_body`) covers the whole function
on the real image (`allocproc` = 0x80001b72..0x80001c72): the `proc[]` scan with `acquire`/`release` per slot
(interrupts may be ON; the scan runs at a migrating hart via `wpNext`), the inlined allocpid under `pid_lock`
with the 64-word collision scan (Löb-closed outer loop, `PidLock.pidLedger`/`pidTie`, `Xv6/PidLock.lean:88,113`),
`p->state = USED`, `kalloc` (`Xv6/SpecKalloc.lean`), `proc_pagetable` → `uvmcreate`/`mappages`/`walk`/`kalloc`
with PTE writes into fresh OWNED pages (`Xv6/SpecProcPagetable.lean` `pptPost`), `memset` of the context,
`ra = forkret`, `sp = kstack + PGSIZE`, both failure tails through `freeproc`, `p->pid`/`p->state` as
`p->lock`-protected cells (`procHeld`).  Callees verified too (`Proof{Kalloc,ProcPagetable,Mappages,Walk,
Uvmcreate,Memset,Freeproc,Acquire,Release,Pushoff,Popoff,Mycpu}.lean`, ≈ 10.7k lines).  In the cone of the audited
roots (`tools/ci/roots.txt:6` `xv6FsAdequacy_closed`, via `Xv6/LinkSyscall.lean:84`/`LinkMain.lean:53`).

The memory model under all of that is `MachCSL.TsoMem` (`MachCSL/TsoMem.lean:1-40`; design
`claude-notes/completed/relaxed-rr.md`): one total store order with per-byte write histories, per-hart view
FLOORS (a plain load reads at any view ≥ floor: load–load reordering), store forwarding by author, store
buffering, `fencePost` (`:345`: W→R drains past the hart's own last store, R→R acquires past the read watermark;
`fence rw,w`/`w,w`/`r,w` are NO-OPS, `:356-364`), `.aq` AMOs, LR/SC reservations, a non-coherent i-cache view
`itv` + `fence.i`.  **What it forbids that RVWMO allows** [R1.7]: (i) store–store reordering and load buffering
(stores are never early) — the weak tier's sRVWMO residue (rule 14; `Weak/WeakAxiomatic3.lean:2050-2071`; the
two divergences LB and reader-fence-only MP, `Weak/WeakSrvwmoLitmus.lean:1663-1695`), checked by reading, not by
theorem — nothing relates TsoMem to `srvwmoConsistent`, and the composition §B(10) does not need it [R2.s2];
(ii) **reservation serialisation**: a foreign hart's store or exclusive read overlapping a held reservation is
BLOCKED (`blockedStep`, `MachCSL/Lang.lean:366-378,395-403`), DMA likewise (`anyReserve`, `:539,562`); the
reservation persists until the holder's next store of ANY address (`MState.store … resv := none`, `:147-153`) or
a blocked exclusive read, surviving fences (`:155-163`).  RVWMO's atomicity axiom constrains only SUCCESSFUL
pairs; kernel code uses only `amoswap.w.aq` (`Xv6/ProofAcquire.lean:5`), but USER code is in the theorem and
may `lr`/`sc` (the SC success predicates are two of the three audited opaques).  Dependency order (ppo 9–13) is
absent in TsoMem — the sound direction.  Honest description of the landed system theorem: "xv6 on sRVWMO +
reservation serialisation".  **Under [OWN.2] this is an INPUT, not the result**: the published theorem is at
RVWMO proper, and TsoMem's proofs are re-justified there by a robustness argument (§B(9)).

**F2. The AxSL tier cannot reach allocproc** [OWN.1: retired].  Theorem 2 (`allocpidOpen2`,
`Weak/AxSpinT2b2.lean:325`) covers ≈ 230 dynamic instructions on literal row families at ≥ 57k lines
(`wc Weak/AxSpin*.lean` = 88k with shared infrastructure) [R1.s1]; allocproc's dynamic footprint is ≈ 120k
instructions (64-slot scan ≈ 8k; `memset` ≈ 16k per page × 7, `procPagetableNodes = 3`,
`Xv6/SpecProcPagetable.lean:39`) with four more lock protocols, the freelist, private page-table pages.
Keep Theorem 2 as an audited riscv.cat-tier validation of the handle-based lock protocol; do NOT extend it.

## A. The target theorem

**What "credible for xv6" requires** (an xv6/weak-memory expert's checklist):
1. the real kernel binary, named above [OWN.4]; every callee real, failure paths included.  The caller discharges
   `wp_allocproc_body`'s premises (`Xv6/SpecAllocproc.lean:204-224`: `k.tier = KTier.kpt`, `allocprocSlots (= 48)
   ≤ k.avail`, `k.noff + 2 < 2^31`, `"kmem"/"nextpid"/"proc" ∉ k.locks`, `procsInv`, the two `isLock`s,
   `kallocAvail γk on`, `procsAvailAt Γ pav tk`, `□ (killCred -∗ Q (-1))`, `actLend`) — kernel-state facts,
   none about memory ordering;
2. harts [R1.1]: **exactly `NCPU = 8`, all booted** (`MachCSL/TsoMem.lean:54`; `PowerOn` forks `cpus =
   List.finRange NCPU`, `MachCSL/Lang.lean:315-320`; `riscvPowerAdequacy` takes `[∗list] cpu ∈ cpus, hartWP …`,
   `MachCSL/Adequacy.lean:383`) — fewer harts NOT covered (D8).  The other harts run ARBITRARY xv6 kernel/user
   code, interrupts on where xv6 allows them, devices as modelled (2 UARTs, PLIC, virtio with DMA as a
   store-order agent);
3. memory [OWN.2]: **RVWMO as the ISA defines it — `rvwmoCatConsistent` (`Weak/AxGraphCat.lean:188`, the
   riscv.cat transcription: rules 1–5, 7-RCsc, 12 derived; omits 6, 7-RCpc, 8 — sound direction; fidelity by
   litmus, `Weak/AxLitmus.lean:29`)**, W→W reordering and load buffering ALLOWED; every strengthening NAMED;
4. page tables live: shared kernel table with concurrent hardware A/D write-back (`MachCSL/KptInv.lean:39,85`;
   TLB `MachCSL/UTlb.lean`), fresh user table private until published;
5. the conclusion is functional AND safety [R1.2][R1.9]: returned slot `&proc[j]`, `j < NPROC`, `p->lock` held,
   `state = USED`, `pid ∈ [1, PIDMAX]` distinct from every live pid, fresh trapframe page (`kalloc`'s fill of
   `5`, `Xv6/SpecKalloc.lean:69`, exposed through `procPrivNocwd`, `SpecAllocproc.lean:131`), fresh user table
   with trampoline + trapframe, context `[forkret, kstack+PGSIZE, 0×12]`; or `0` with the lock released and
   everything freed; **no hart ever stuck in the machine semantics** (`Reducible`); all kernel invariants
   preserved — i.e. exactly `allocprocPost`.  **Panics are NOT excluded** (`panic` is a bare `wpLoop`,
   `Xv6/SpecPanic.lean:11-14`), **nor the two reducible spin arms** [R2.4]: `blockedStep` and the weak retry
   self-loop of a lost exclusive pair (`Weak/WeakEvInst.lean:360-364`).  "never panics" = "no `panic:` bytes in
   the UART trace" (`uartSentSub`, `Xv6/UartTrace.lean:182`), M–L, new work — D9;
6. axioms `propext`/`Classical.choice`/`Quot.sound` + `bv_decide` certificates + the three opaques
   (`tools/audit/baseline.json:11-14`), no `sorry`; trusted base named: Sail model, image dump, the cat
   transcription.

**Legitimately out of scope:** liveness/fairness, timing, mixed-size fidelity of the cat model (N10), MMIO
ordering beyond the modelled devices, hardware outside the Sail model, power cycles (SINGLE ERA [R2.2]).

**The statement to aim for — three layers.**  *T-alloc* (contract, exists): `Xv6.Allocproc` on MachCSL.
*M1/M2 (internal milestones, NOT published [OWN.2])*: the composed sRVWMO theorem, pinned/kernel-only (M1) then
unpinned (M2), below.  *T-alloc-RVWMO (THE published claim)* [OWN.2][OWN.3][R3.1][R3.2][R3.4]:
```
∀ (σ0 : WGState) (GD : Gdexec),
  wbootFacts σ0 ∧ σ0.wggen = 0 ∧ (∃ ds, σ0.wgdev = ds.reset ∧ diskOf ds = fsImgDisk) ∧        -- the boot [R2.2]
  rvwmoCatConsistent GD ∧                                                                   -- riscv.cat [OWN.2]
  xv6ConfS (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) GD                             -- xv6 is the program (†)
  →
  (a) the realizing MachCSL run (robustness W9 → sRVWMO cand → T1 → pf run → W4, PREFIXED by PowerOn from the
      given disk) satisfies xv6FsAdequacy_closed's conclusions for ITS ONE ERA: Reducible (panics, two spin arms
      not excluded), xv6TracePure (fs purity + mmOk), xv6NiPhi / unionAdequacyClosed [R3.s2]; the realized pf
      run never enters the retry arm [R2.3]; and
  (b) the allocproc shadow tied to κs (W1 via xv6NiPhi [R3.s1]): every filed fork round answers usysForkAns of
      its citation (pid = pidPick of the cited prefix, ∈ [1, PIDMAX], or -1); KAlloc/KNull/KFree well-formed
      (poolEmpty at KNull); after W1b, live pids pairwise distinct.
```
(†) `xv6ConfS` is the SHAPED, UNPINNED conformance bundle: today's `gdexecQconf` (`Weak/WeakRvwmoSupply.lean:281`:
per-hart emissions `hartConf` from `xboot`, device-free, store-deps in `gdDeps`) with its fetch pin `emFetchImg`
replaced by Zifencei admissibility (W5d [OWN.3]), exclusive pairs FUSED (no standalone `LExLoad` — the
`execProgOk'S` shape of [R3.2]), and loads single-copy-atomic (`candSca` [R3.4]).  The conformance premise is
genuine: the graph side alone yields only `execWf`-style facts; the program half is a hypothesis realized by
`execWfPfRunProg` (`Weak/WeakAxRealize.lean:802-808`) [R1.5].  **The pin fixes WHAT a fetch answers, not WHERE
it fetches** [R3.1]: at M1 the premise is `pstepPin` + `candKfetch` (every `LIFetch` footprint in kernel text
`[0x80000000, etext = 0x80007000)`, `Xv6/KernelImage.lean:771`), which is what makes M1 kernel-only; M2/the
target replace both by Zifencei admissibility.  Boot premises: `xv6FsAdequacy_closed`'s
(`Xv6/LinkSystemAdequacyClosed.lean:20-26`) transposed through `PowerOn` (`bootShape`/`bootFacts`,
`MachCSL/Lang.lean:294-304`) to `wbootFacts` (`Weak/WeakLang.lean:482-490`); `diskOf ds.reset = diskOf ds` is a
corollary of `BootSharedDev.lean:283` (`diskOf ds0.reset = (ds0.st .virtio).disk`) [R3.s4].  (b) is the
trace-observable shadow of `allocprocPost` in the NI idiom (`xv6NiPhi`, `Xv6/NiAdequacy.lean:91-92`) [R1.4].

*M1/M2 (internal)*: the same with `srvwmoConsistent c ∧ execProgOk'S (pstepPin …) … ∧ candKfetch ∧ candSca`
(M1) / `execProgOk'S pstepEv …` with Zifencei fetches (M2) in place of the two graph premises.  sRVWMO
("RVWMO, stores never early") results stay milestones only [OWN.2].

## B. Gap analysis

Legend: *need* = needed for T-alloc-RVWMO; *route* = (M) machine tier / (A) AxSL tier (retired [OWN.1]).

**(1) AxSL tier not composed with the machine tier.**  Only on route (A).  Missing: pf run ⇒ `srvwmoConsistent`;
sRVWMO `Cand` ⇒ tagged `GdexecT` with `rvwmoCatConsistentT` + ctrl closure; the per-hart opax runs of
`tierAAdequacy` (`Weak/AxTierA.lean:91-98`) from the pf run; the row-family premises fail on real executions.
XL.  *Treatment:* record Theorem 2 as a riscv.cat-tier validation (D6).

**(2) Page tables.**  Route (M): CLOSED — kernel table a live shared invariant with A/D variants
(`KptInv.pteVariant`), `utlbOk` "up to A/D" (`MachCSL/UTlb.lean:17-21`), hit/miss/fill/write-back modelled
[R1.s3]; user-table pages fresh owned memory (`pptPost`), published at `satp` + `sfence.vma`.  Named assumption
(§B(11)): Svadu write-back as a plain view-neutral LR/SC.  S (documentation).

**(3) SIE = 0, 3 harts, no devices/DMA.**  Route (M): CLOSED (`KCtx.sie`, `wpNext`, `NCPU = 8`, DMA at the store
order).

**(4) Text never written / fetch pinned** [R1.8][R2.1][R2.1-alt][R3.1].  The fetch-view premise is carried by both
weak capstones (`xv6SrvwmoSafe` (b'), `Weak/WeakSrvwmoCapstone.lean:88-89`; `xv6RvwmoSafeModulo`,
`Weak/WeakRvwmoCapstone.lean:195`: `∀ ρ, rtc epfRun … → efetchItvOk ρ.1 ρ.2`, `Weak/WeakEvCapstone.lean:681-685`)
because the lift `wpPfRtcEpfRtc` (`:1008-1011`) needs it (the capstone calls it with `Hcov`,
`WeakSrvwmoCapstone.lean:118-120` [R3.s4]).  It cannot be discharged weak-side on route (M).  Treatment:
(i) W5 does NOT go through `epfRun`; it starts from `execWfPfRunProg`'s `rtc (wpPfRun pstepEv pclsEv) …`
(`WeakAxRealize.lean:802-808`, via `wpPfRunPinSub :225`), and W4 projects `wpPfRun` runs.  (ii) The (↓) `LIFetch`
row of W2 carries the content: the pf fetch is admissible at floor 0 (`PFIFetch`,
`Weak/WeakPromiseBridge.lean:441-449`) while TsoMem fetches as the i-cache agent at `σ.itv cpu ≤ tvn ≤ top`
(`MachCSL/Lang.lean:360-362`); the row closes iff no log write hits the fetched bytes between the version read
and `itv`.  **[R3.1] The pin does not make a candidate kernel-only**: a pinned fetch is pf-admissible AT ANY LOG
(`fetchPinIfetchOk`, `WeakAxRealize.lean:167-176`; `ifetchByteOkb` with `itv = 0` checks `writesIn (t, max t 0]
= ∅`, `Weak/WeakPromise.lean:228-231`), fetches are `lbAdmin true` (`:130-134`) replayed by `admStepPf`
(`:426-430`), and the program LTS constrains the fetched value only through the memory side (`pstepEv`'s
i-cache arm, `Weak/WeakEvInst.lean:306-312`: any `w`); the boot image is ZERO past the ELF
(`bootByte_zero`, `MachCSL/BootImage.lean:30-33`).  So a conformant sRVWMO-consistent pinned candidate can run
`userinit → scheduler → userret (fence.i, Xv6/SpecUserret.lean:6) → sret` and fetch the image's zeros at the
user page (illegal instruction, trap, kill) — while TsoMem's `itv` has passed `uvmfirst`'s writes, so W4's
`LIFetch` row has no TsoMem step.  Rev 3's "the pinned theorem therefore covers kernel-only runs" was an
inference, not a premise.  Fix: M1 carries `candKfetch` (every `LIFetch` footprint ⊆ `[0x80000000, 0x80007000)`)
inside the shaped conformance predicate; W3 discharges the `LIFetch` row ONLY under it; (iii) **W5d** (M2,
L; part of the target [OWN.3]): the UNPINNED supply — `execWfPfRunProgF`, the replay at `pstepEv` with the
Zifencei side condition `ifetchOk img (log at k) (itv of the hart) base tvs` (`Weak/WeakEvInst.lean:564`
`elabOk`; `itvPostMachCSL`, `Weak/WeakInterp.lean:376-379`) in place of `fetchPin`, AND its graph-side twin:
`gdexecQconf`'s `emFetchImg` (`WeakRvwmoSupply.lean:277-278`) replaced by the same condition at the realizing
position (today the graph tier's fetch has content ONLY through the pin, `WeakRvwmoGlue` deviation 5).  Then
the (↓) `LIFetch` row holds for user text too (TsoMem reads at `tvn := max t itv`).  Zifencei admissibility is a
NAMED premise, discharged by W3 for kernel text, restrictive only for self-modifying user code without `fence.i`.
Sizes: W3 M; W5d L (was M–L; the graph half is new).

**(5)–(8) Segment coverage, scope pins, store-value rows, stack/cpu privacy.**  Route (M): CLOSED (F1; the pid
ledger handles wrap/collision retries, `Xv6/ProofAllocproc.lean:16-24`; text facts by `rfl`/`decide`; real
`stackOwn`/`kctx` resources).

**(9) THE gap: TsoMem is sRVWMO + reservation serialisation; the target is RVWMO proper** [R1.7][OWN.2].
*Inventory of weaker models in the Lean tree.*  (α) `WeakMem` pf machine (`Weak/WeakMem.lean`) = sRVWMO
operational (T1 `srvwmoRealizable`, `Weak/WeakAxiomatic3.lean:2077`; T2 `t2Ev`, `Weak/WeakEvInst.lean:2046`) —
same strength class as TsoMem.  (β) `WeakPromise*` (`Weak/WeakPromise.lean:1-16`: the full promising machine,
PARM restated natively; `wpPromiseStep`, `Weak/WeakPromiseFact.lean:87`; `wpBehavior`, `WeakPromise.lean:746`) —
LB reachable (`lbWeakOutcomeReachable`, `Weak/WeakPromiseLitmus.lean:185`); its RVWMO fidelity is BY
INSPECTION against Pulte et al. (D-M6-3, `claude-notes/design/weak-memory-m6-robustness.md:42-48`), no in-tree
theorem.  (γ) PSO two-log machine: Rocq-only design (`claude-notes/completed/relaxed-ww.md`, branch
`relaxed-ww-twolog`); NOTHING in Lean (grep `gdlog`/drain: none).  (δ) Graphs: `rvwmoCatConsistent` (cat) and
`rvwmoMinusDepsConsistent` (`Weak/WeakRvwmoGraph.lean:628`, RVWMO⁻ + store-dep fragment).  **`minusImpliesCat`
(`Weak/AxGraphCat.lean:274`) runs the WRONG way for us**: RVWMO⁻ renders rules 1–3 as all of `gpoloc`, ordering a
write before its own po-later same-byte read — it FORBIDS store-buffer forwarding (N11, `AxGraphCat.lean:10-16`,
`notes/weak-memory-scope.md:209-212`), so a theorem over RVWMO⁻ graphs misses cat-consistent forwarding
executions.  The whole Tier-2 chain (`rule14Linearization`, `Weak/WeakRvwmoLin.lean:1846`; `racyD`,
`Weak/WeakRvwmoAcyc.lean:200`; `t2linOfL2'''`, `Weak/WeakRvwmoWalk3.lean`; `xv6RvwmoSafeModulo`,
`Weak/WeakRvwmoCapstone.lean:187`; 45 `WeakRvwmo*` files, 33k lines) starts at RVWMO⁻(+deps).
*Why plain DRF does not apply.*  xv6 races by design: route B's census (`claude-notes/design/
weak-memory-route-b.md:1413-1445`): 1611 loads, 620 non-stack; 244 ctrl-pinned, 138 dep-pinned into the next
store, 2 fence-pinned, 190 need callee summaries, 32 ran off the window, 10 genuinely unpinned (all lock-payload
or caller-owned); racy flag reads (`started`, `panicked`, UART LSR, virtio `used->idx`, `ticks`, `p->killed`,
`p->state`) pinned by branch/fence/lock.  The applicable theorem is ROBUSTNESS UNDER A PER-SITE DISCIPLINE
(L2′ = `l2Claim`, `Weak/WeakRvwmoGlue.lean:449`: per cycle segment `segPin ∨ csHyps ∨ Bad`, `:229,400`) — DRF
generalised: every cross-hart read is pinned by ppo (ctrl/dep/fence/aq) before the hart's next store, or is a
lock-protected read (`protRead`/`wprotAt`, `Weak/WeakGhost.lean:3408,1040`), or observes an owned-unpublished
message (`Bad`, refuted by violation-freedom).  The discipline must be established on the STRONG model's
executions; the only verified source is the TsoMem Iris proofs — which today export `mmOk` only (history
well-formedness, views ≤ top, reservations at top; `MachCSL/Resources.lean:779-785`), nothing per access.
*The routes, sized candidly:*
- (9a) *Re-verify xv6 on a weaker MachCSL instance.*  No PSO or promise-style `MachCSL` exists in Lean; the Xv6
  cone is ≈ 0.65M lines (19k generated image) over 75k of `MachCSL`; every memory rule, lock, `Ctx`, racy tier and
  spec would re-thread (relaxed-ww's Rocq estimate for PSO ALONE: stage D "2–4 weeks is the floor" + E 2–3 weeks,
  with the design done; LB on top has no design) — and the result is on an OPERATIONAL machine whose link to
  `rvwmoCatConsistent` is a further Promising≡RVWMO-grade theorem.  **XL × 2.  Rejected.**
- (9b) *PSO two-log machine (W6).*  L–XL fresh in Lean [R1.s4]; "RVWMO minus LB minus deps"; does not remove the
  kernel claim (LB robustness needs the same per-site discipline).  **Not on the path under [OWN.2]**; optional
  de-risk of the discipline export only (D4).
- (9c) *Promise-machine robustness (W7-P).*  `robustMain` (`Weak/WeakRobustMain.lean:1520`) EXISTS: a
  `wpBehavior` of the promising machine is matched by a `wpPfRun` run (same `progOf`/`memOf`) — exactly W4's
  input — given `pfViolationFreeHart` (`Weak/WeakRobust.lean:118-121`), `fetchSrcOk`, `mainPremises`,
  `clsCanonical`, `latFreeProg`, `tsOblivious`, `pdevOk`.  But (i) φ is REFUTABLE at event granularity (walker
  CAS parked before its release-pending store, `claude-notes/completed/weak-memory-lift.md:19-29`); Rocq's
  block-granular fix `WeakComposeLang` was skipped by the port and its `sailShaped` premise is false under O2
  (`notes/weak-port-skip.md:6,38`); (ii) the RVWMO quantifier would be the promising machine, fidelity EXTERNAL
  — **fails [OWN.2]'s quantifier.**  Fallback only if the owner relaxes D2 (D2').
- (9d) *Graph-tier robustness re-sourced from TsoMem (RECOMMENDED — the cheapest SOUND route).*  Keep the Tier-2
  chain; replace its weak-WP-sourced inputs by facts projected from the TsoMem run through W4.  Residue of
  `xv6RvwmoSafeModulo` today: (R-1) `l2Claim`; (R-2) `walkSupply` (`Weak/WeakRvwmoGlue2.lean:453`), reduced to
  the per-state datum `wsegSupply`/`walkPolicy` (`walkSupplyOfQconf`, `Weak/WeakRvwmoWalk2.lean:563-568`;
  `t2linOfL2'''`, `WeakRvwmoWalk3.lean:77-100`) — its non-vacuity witness is a hand-built LB cycle
  (`Weak/WeakRvwmoCycWit.lean:1-30`); `wpPackage` (`Weak/WeakRvwmoGlue.lean:338-346`: an EWP proof of ALL of xv6
  on the weak event language — xv6 does not have it; `weakSystemAdequacyPhi`, `Weak/WeakAdequacy.lean:194`, takes
  the weak WPs as a premise too); `efetchItvOk` (W3/W5d).  Work: **W8** export the discipline from the SC tree;
  **W9** discharge `l2Claim` for xv6 (static site check over the image + W8's records); **W10** `wsegSupply`
  for xv6; **W11** re-source the glue's `noBadRun`/`protRegOfRun` from W8 via W4 and restate the capstone over
  `xv6ConfS`; **W12** the cat↔RVWMO⁻ gap (N11).  Sizes: W8 L–XL, W9 L, W10 M–L (**unverified**), W11 M–L, W12
  L–XL (**unverified**; nobody has sized it).  **Total: XL** — multi-week, many files, two items of unknown size.
*Recommended:* (9d), staged after M2; W12 spiked FIRST (it decides whether the published quantifier can be
`rvwmoCatConsistent` at all — D25); (9b) only if W8 wants a smaller model to start on (D4); (9c) as D2' fallback.

**(10) The machine-tier composition — a simulation over REALIZED, SHAPED runs** [R1.6][R2.2][R2.3][R2.3-alt]
[R3.2][R3.4].  The SC tree's conclusions are trace properties over MachCSL runs (`riscvPowerAdequacy`,
`MachCSL/Adequacy.lean:266`; `xv6FsAdequacy`, `Xv6/SystemAdequacy.lean:543`: `Reducible` + `xv6TracePure` =
`fsBootPure ∧ (pow → mmOk)`, `Xv6/SystemSlot.lean:135-136`).  The pf machine's program half is literally shared
(`MachCSL.riscvStep`, `Weak/WeakEvInst.lean:286`), so the theorem is a SIMULATION: every `wpPfStep`
(`Weak/WeakPromiseBridge.lean:339`) of the realized run is a `MachCSL.primStep` (`MachCSL/Lang.lean:599`) with the
same hart expression and observations.
*(↓) is REFUTED on arbitrary pf runs* [R2.3]: the event instance SPLITS exclusives into `LExLoad`/`LExStore`
(`Weak/WeakEvInst.lean:323-331,350-359`); a foreign store between the halves is ENABLED in WeakMem (`PFStore`,
`WeakPromiseBridge.lean:355-366`) while TsoMem BLOCKS it (`othersReserve`, `MachCSL/Lang.lean:377`).  Saved by
realized FUSED `LRmw` pairs (`lblRealizesPair`, `Weak/WeakAxRealize.lean:305-313`; one agent, `admStar`,
conditional write; the `LExLoad` at the 0 floor, `WeakPromiseBridge.lean:418-423`).  **[R2.3-alt]** a STANDALONE
`LExLoad` is realizable as a plain `LLoad` (`lbNobarex`, `:97-103`; `projLbl (LExLoad …) = some (LLoad …)`,
`:545`); TsoMem's dangling reservation blocks foreign stores (`Lang.lean:147-153`) and its exclusive read takes
`topBytes` (`:368-371`) — (↓) fails.  **[R3.2] the shape cannot be a separate conjunct on `(c, pst)`**: the
realizing `l` and the stars are existential per index inside `execProgOk'` (`WeakAxRealize.lean:373-386`;
`admStar = rtc admStep`, no label list, `:343-344`).  So the premise is ONE shaped conformance predicate
**`execProgOk'S pstep pcls pst dv E`** := `execProgOk'` with (i) the left disjunct's `l` not an `LExLoad`
(re-imposing `lbFused` on the left arm only, cf. `lblRealizesUnproj :245-247`), (ii) the stars as label-carrying
`admRun`s (`Weak/WeakRvwmoConf.lean:374-381`) whose every `LIFetch` is in kernel text (M1, `candKfetch`) /
Zifencei-admissible (M2), (iii) every `LLoad` single-copy-atomic (`candSca`, below).  W5b consumes it and carries
`pairAdjacent` + the fetch/SCA facts along the run; W5c must PRODUCE it (`execProgOk'Snoc`,
`Weak/WeakRvwmoCert.lean:413`, yields plain `execProgOk'` — an S-variant or derivation lemma is needed).
**[R3.4] (↓) fails on PLAIN LOADS even on shaped runs — tearing.**  WeakMem's `readable` is per byte
(`Weak/WeakMem.lean:400-402`), the pf load checks it per byte (`readOkD`, `Weak/WeakPromise.lean:183-188`), the
axiomatic machine likewise (`byteRd`/`rdOk`, `Weak/WeakAxiomatic.lean:122-130`; `candShape`/`candValues`,
`Weak/WeakAxiomatic2.lean:910-921`); no axiom joins the bytes of one label (N10).  TsoMem reads every byte of a
load at ONE `tvn` (`MachCSL/Lang.lean:363-367`; `FlatMem.readBytes`, `MachCSL/TsoMem.lean:145-147`).
Counterexample: whole-word stores `S1@4`, `S2@6`; a floor-0 load with `ts = [4,4,6,6]` is admissible and
sRVWMO-consistent; TsoMem yields all-`S1` or all-`S2`.  RMWs are exempt (`rmwLatest`, `WeakAxiomatic.lean:134`);
fetches under W5d are NOT (`ifetchByteOk` per byte, `WeakPromise.lean:222-231`).  The ISA guarantees
single-copy atomicity for naturally aligned accesses ≤ XLEN, so the premise is ISA-faithful — NAMED as
**`candSca c`**: every `LLoad` (M2: and `LIFetch`) reads its bytes at one view — `∃ tvn, ∀ j, ts[j]` is the
latest write to byte `j` at or below `tvn` or the hart's own later store (TsoMem's forwarding clause).  Carried
by W5b; row "plain load" of W2's table is (↓) iff `candSca`; alternative = an atomicity axiom in sRVWMO
(re-opens T1, XL) — D20.
*(↑) receptiveness is NOT available on route (M)* [R2.3(iv)]: weak-side `Reducible` would need the weak WP
package.  (a) is stated for the realizing MachCSL run; the free weak-side sentence is "the realized pf run never
enters the retry arm" (D15).  W4b dropped.
*Single era* [R2.2]: `epowerFork` forks no power thread (`Weak/WeakEvLang.lean:201-204`), so multi-era
conclusions are NOT transported; W4's run is prefixed by the `PowerOn` step (D14).
*The relation `R`* [R2.s3][R3.s3][R3.4], fixed in the spike report: TsoMem `tv ↔ max wVrNew (own last store)` —
**the `.aq` off-by-one** [R3.s3]: at an acquire pair TsoMem's `tv` becomes the WRITE's timestamp `top + 1`
(`MachCSL/Lang.lean:150`), WeakMem's `wVrNew` the READ's (`exloadPostRunD`, `Weak/WeakMem.lean:834`;
`storePostD` does not touch `wVrNew`, `:634-647`); `rv ↔ wVrOld`, `ownPub ↔ wVwOld`, `coh ↔ wCoh`, histories =
log projection, image `imgZ bootImage ↔ imgFlat bootImage`, `resv ↔ wRes` only mid-pair, `itv`: the pf machine
has none, so `R` carries "the MachCSL `itv` is below every fetch's version" (W3 / W5d), and the load row carries
`candSca`'s `tvn`.  Spot checks (↓): `fencePost` raises `wVrNew` to `max wVrOld wVwOld` for `pr,pw`
(`WeakMem.lean:674-678`), `wVwOld` = max own-store timestamp = TsoMem's `ownPub`; `fence rw,rw`/`r,r`/`rw,w`
agree.  Open per label: parked `fence rw,w`/`wRelp` (`:684`) vs TsoMem's no-op; `wRes := none` at any non-trivial
fence (`:688`) vs TsoMem keeping it; the `.aq` carried bit (`MachCSL/TsoMem.lean:255-280`); the i-fetch agent (no
forwarding) vs `LIFetch`; devices/DMA (`Efab` vs `MState.devrt`; `anyReserve`).  Size: L (↓) + L (W4) + M (W5b)
+ M (W5) + M–L (W5c) + L (W5d).  It lifts the WHOLE system theorem, and (9d) reuses it in both directions of the
robustness argument.

**(11) Model fidelity and named assumptions (trusted base, list in the header)** [R1.1][R1.7][R2.4][R3.1][R3.2]
[R3.4].  Candidate/conformance premises: `execProgOk'S` (fused exclusive pairs — "a dangling LR or failing SC is
outside the theorem", D19; M1 only: `candKfetch`, kernel-only candidates, D21); `candSca` (single-copy atomicity
of aligned loads ≤ XLEN; ISA-faithful, D20); Zifencei admissibility of fetches (M2+).  Strengthenings beyond
RVWMO carried INTERNALLY by TsoMem/sRVWMO (not in the published statement once (9d) lands): "stores never early";
reservation serialisation.  Machine-model choices: exactly 8 harts booted; Svadu A/D write-back as a plain
view-neutral LR/SC; DMA as a store-order agent; the instruction-fetch model (`MachCSL/TsoMem.lean:34-39`,
`Lang.lean:360-362`, `MState.fence :155-163`) — beyond RVWMO's text (Zifencei); the SC-failure model (memory
never fails an exclusive write; the Sail opaques decide, `Xv6/UserMemLrsc.lean:7-12`; D17); single era.
Fidelity: `rvwmoCatConsistent` omits rules 6, 7-RCpc, 8 (sound direction), litmus-checked only; the published
quantifier is RVWMO⁻(+deps) UNTIL W12 closes N11 (forwarding) — state it if so (D25); Sail fork `070832a1` with
`-D SYMBOLIC`; the image dump.  Keep, list.

**(12) Audit coverage and file layout** [R1.10].  `Xv6/` never imports `Weak/`; lake libraries `MachCSL`, `Xv6`,
`Weak` (`lakefile.toml:2,27-41`).  Every composition file lives in `Weak/`, registered in `tools/ci/roots-weak.txt`
+ `tools/audit/baseline-weak.json` + `XV6_AUDIT_MODULES` (`tools/ci/audit.sh:44`), built by `--weak` CI, whose
cone then includes the whole `Xv6` adequacy cone (D13).  Pure-`Xv6/` items (W3, W8) go to `roots.txt`/
`baseline.json`.  S.

## C. Roadmap

Each stage ends in a theorem; "∥" = parallel (one Opus worker, one file each).  Stages 0–1b are INTERNAL
milestones on the critical path of the target; Stage 2 is the target [OWN.2].

**Stage 0 — launch now: W3 lemma → W2 spike, ∥ W1, W5b, W5c, W12-spike** [R2.s4].
- **W3 `Xv6/TextUnwritten.lean`** (M) [R1.8][R2.1][R3.1].  `kernelTextUnwritten`: no reachable store (hart or
  DMA) targets `[text, etext)`, as a trace export of the state interpretation.  Discharges W4's `LIFetch` row
  under `candKfetch` (M1) and the kernel-text half of Zifencei admissibility (M2).  Deps: none.
- **W1 `Xv6/AllocprocTrace.lean`** (S–M, re-scoped [R3.s1]; D23).  `xv6NiAdequacy` (`Xv6/LinkNiAdequacy.lean:82-90`)
  has the SAME three boot hypotheses as `xv6FsAdequacy_closed` and concludes `xv6NiPhi g2 κs`, whose
  `NiClassLaw` (`Xv6/NiTrace.lean:660`, via `niOk`, `Xv6/NiLedger.lean:319-322`) contains `niRoundLaw`'s fork row
  (`:646`): the enter's `a0 = usysForkAns ι` = sign-extended `pidPick PIDMAX ι.pev` or `-1`
  (`Xv6/UsysDet.lean:293-302`) at the CITED prefix — tie β (D11) with round identification already solved
  (`exitView`/`enterView`).  So W1 = cite `xv6NiPhi` + pure history lemmas on `ι.pev`/`ι.kev`: `pidPick ∈
  [1, PIDMAX]`, the `nextOf` tie (`Xv6/PidEv.lean:77`), `poolEmpty` at every `KNull` (`Xv6/KallocEv.lean:72`).
  Conclusion (b) reads "every filed fork round answers `usysForkAns` of its citation".  Today's ledgers export no
  page address (`Kev`, `KallocEv.lean:45-52`) and no slot index (`Pev`, `PidEv.lean:50-55`); `liveOf` is a set.
- **W1b (owner-gated, L, serial)**: `pidHistWf h` in `pidLedger` (live pids distinct by induction), re-thread
  `ProofAllocproc`/`ProofFreeproc`/`NiLedger`; optionally addresses in `Kev` for page disjointness.  D10.
- **W2 `Weak/TsoOfPf.lean`** (L; spike first, ≤ 200 lines, risk report) [R1.11][R2.3][R2.s3][R3.4][R3.s3].
  `pfStepTso`: for every memory label (one row per exclusive half, one for the plain load), a `wpPfStep` from an
  `R`-related state under `pairAdjacent` + `execProgOk'S`'s shape + `candSca` is a TsoMem step with the same bytes,
  to a related state.  Report: per-label (↓) table; fence spot checks; `R` fixed with the `.aq` off-by-one; (↑)
  recorded as NOT CLAIMED.  Deps: W3's statement.  **STOP rule** (D7): a WeakMem behaviour TsoMem lacks on a
  SHAPED run → STOP, report; suspects: parked release fence, fence-clears-reservation, tearing, `.aq` off-by-one
  [R3.s5].
- **W5b `Weak/PfRunShape.lean`** (M) [R2.3(iii)][R3.2][R3.4].  `execPrefixPfRunProgShaped`: the replay variant that
  consumes `execProgOk'S` and carries `pairAdjacent`, the fetch facts and `candSca`'s per-load `tvn` along the run
  — a new theorem in `Weak/`, not a change to `WeakAxRealize`.  Deps: none.
- **W5c `Weak/SrvwmoXv6Witness.lean`** (M–L, re-specified [R3.3]; D22).  Non-vacuity: the premise set of M1 is
  SATISFIABLE.  The `sw &started` block does NOT witness it: M1 fixes `pst 0 = epsInit σ0` (every hart at `.pure ()`
  with the boot program's register file, `Weak/WeakEvCapstone.lean:1026-1027`; `wbootFacts`,
  `Weak/WeakLang.lean:488`: `bootRun (bootProg …) = some ((), wgregs c)`, pc at `_entry`), while the existing
  witness sits at the MID-instruction node `WeakEvStarted.evX2` with an EMPTY administrative run and a universally
  quantified register file (`Weak/WeakRvwmoConfWit.lean:11-22`); `smC img := ⟨img, []⟩`/`smSnocConsistent`
  (`Weak/WeakRvwmoCert.lean:522-546`) give only the consistency half; and `started = 1` is the LAST store of the
  boot (`kinit … userinit` before it, `Xv6/SpecMain.lean:6-15`) — reaching it is a whole-boot replay.  The block
  is `_entry`'s FIRST memory instruction, `ld sp,1000(sp)` at `0x80000004` (`Xv6/KernelImage.lean:14-17`; the GOT
  word at `0x8000a3e8`, image bytes, `t = 0`): hart 0 alone (seven idle), pinned fetches of `_entry`'s two
  instructions in kernel text (`candKfetch` ✓), the administrative run by kernel evaluation (`esil`,
  `Weak/WeakEvLift.lean:897`; `pevrunAdmRun`, `Weak/WeakRvwmoCert2.lean:180` — the `esil → admRun` bridge
  `Weak/WeakRvwmoConfWit2.lean:26-28` records as THE missing mechanism), consistency from
  `gtraceSnocReadImage` (`Weak/WeakRvwmoFloor.lean:1025-1035`) or `snocRdAdm` (`Weak/WeakRvwmoCert.lean:257`), a
  concrete `σ0` with `wbootFacts` (a `bootRun` output, `MachCSL/BootRun.lean`), `candSca` trivially (one store
  per byte), and the S-variant of `execProgOk'Snoc`.  Certifies satisfiability — NOT that any candidate reaches
  `allocproc` (a whole-boot replay, D18's user-fetch witness).  Deps: W5b's predicate.
- **W12-spike `Weak/CatOfMinusSpike.lean` (read-only report, S)** [OWN.2][new].  Decide the published
  quantifier: (a) can the T2-LIN chain be re-derived over `gppoCat` (which lemmas use `gpoloc`'s W→R arm
  essentially)? (b) is there a forwarding-normalisation lemma (every cat-consistent conformant graph has an
  RVWMO⁻ twin with the same rows and log)? (c) else the statement is at RVWMO⁻(+deps) with "no store-buffer
  forwarding" NAMED.  Feeds D25.  Deps: none.

**Stage 1 — M1, the composed sRVWMO theorem, pinned/kernel-only (internal).**
- **W4 `Weak/MachOfPf.lean`** (L) [R2.1][R2.2][R2.3][R3.1].  `machRunOfPfRun`: a shaped `rtc (wpPfRun pstepEv
  pclsEv)` run from `wpInit (imgZ bootImage) (efInit ds.reset) (epsInit σ0)`, PREFIXED by `PowerOn`, is a
  `-<κs>->ₜₚ^[n]` MachCSL run, same hart expressions, same observations, devices aligned; the `LIFetch` row
  stated UNDER `candKfetch` (M1) / Zifencei admissibility (M2).  Deps: W2, W3.
- **W5 `Weak/SrvwmoXv6Adequacy.lean`** (M) [R1.5][R2.1][R3.1][R3.s2].  **M1**: from `wbootFacts σ0`, the disk,
  `srvwmoConsistent c`, `execProgOk'S (pstepPin …)` with `candKfetch` + `candSca` — T1 + `execWfPfRunProg` +
  `wpPfRunPinSub` + W5b give the shaped run; W4 projects; `xv6FsAdequacy_closed`, `xv6NiAdequacy`,
  `unionAdequacyClosed` (`Xv6/LinkUInitUnion.lean:163-164`; same hypotheses) and W1 conclude.  Header: internal
  milestone, kernel-only by PREMISE, named assumptions.  `roots-weak.txt`/`baseline-weak.json`/
  `XV6_AUDIT_MODULES`.  Deps: W1, W4, W5b; W5c as gate (D22).

**Stage 1b — M2, the fork path (part of the target [OWN.3]).**
- **W5d `Weak/PfRunUnpinned.lean`** (L) [R2.1-alt][R3.1][OWN.3].  `execWfPfRunProgF` (replay at `pstepEv` with
  Zifencei admissibility replacing `fetchPin`), W4's `LIFetch` row for user text, the graph-side twin of the
  unpinned conformance (`emFetchImg` → Zifencei at the realizing position), W5 restated — the first form in
  which `fork → ecall → sys_fork → allocproc` under contended `p->lock` from 7 scheduling harts is a candidate.
  A user-fetch witness (satisfiability of M2's premise set on the fork path) = whole-boot replay; not scheduled
  (D18).  Deps: W5.

**Stage 2 — THE TARGET: T-alloc-RVWMO via graph-tier robustness re-sourced from TsoMem (route 9d; XL).**
- **W12 `Weak/CatLin*.lean`** (L–XL, **unverified**; per the spike/D25): the chain from `rvwmoCatConsistent`.
- **W8 `Xv6/AccessDiscipline.lean`** (L–XL; D24).  Export from the SC tree, per reachable MachCSL state (the `mmOk`
  idiom) or per trace step, the facts `l2Claim` consumes: each hart's memory access is (i) to bytes it owns, (ii)
  a protected read/write under a held lock (the `protRead`/`wprotAt` analogue: holder, acquire position, the
  write not touching the lock word), or (iii) at a classified racy site.  Needs a ledger threaded through the
  MachCSL memory rules (`UMem*`, `Lock`, `Ctx`, racy tiers) — mechanical but wide; the ownership residue is ~5
  idioms (`swtch` context reloads, trapframe loads off `a0`, user-table walks, boot-published globals).
- **W9 `Weak/KernelPins.lean` + `tools/gen_pins.py`** (L).  The static site check (route B §4g.1: witness per load
  site `PStack | PPerCpu | PCtrl | PFence | PDep | PCall | PResidue`, re-checked in Lean by `decide` against
  `Xv6/KernelImage.lean`; callee summaries for the 190 `jal` sites) → `segPin` at the graph level; with W8 →
  `l2Claim` for xv6.
- **W10** (M–L, **unverified**): `wsegSupply`/`walkPolicy` for xv6 graphs.
- **W11 `Weak/RvwmoXv6Adequacy.lean`** (M–L).  Restate `cycleKillOfL2''`/`t2linOfL2'''` with W8-sourced facts
  (via W4 on the hull's realizing run) in place of `wpPackage`/`noBadRun`/`protRegOfRun`; compose with M2:
  **T-alloc-RVWMO**.  Header per §B(11).
- *Not on the path:* **W6** PSO machine (L–XL; optional de-risk, D4); **W7-P** promise-machine fallback (D2').

**Stage 3 — AxSL tier: retired** [OWN.1].  One-paragraph note on Theorem 2 (D6).

**Launch now:** W3 lemma first, then W2 spike ∥ W1 ∥ W5b ∥ W5c ∥ W12-spike — independent files, none touching
shared `MachCSL/`.  W1b waits for D10; W8 design starts after the W2 report (its export shape depends on `R`).

## D. Owner questions (recommended option first; RULED items kept for the record)

- **D1. Tier** — RULED [OWN.1]: machine tier; AxSL segment work retired; Theorem 2 = validation.
- **D2. Published statement** — RULED [OWN.2]: FULL RVWMO (`rvwmoCatConsistent`); sRVWMO/pinned forms internal.
  **D2′ (new).** If route (9d) is judged too large: (Rec) hold publication; (b) publish on the promising machine
  with "Promising-RISC-V ≡ RVWMO (Pulte et al.) in the trusted base" — not cat, violates [OWN.2] as written.
- **D3. Conclusion form.**  (Rec) trace-level predicate via `xv6NiPhi` (W1) beside the Iris contract; (b) contract only.
- **D4. PSO machine (W6)** — re-cast under [OWN.2]: (Rec) SKIP — it neither reaches the target nor removes the
  kernel claim; (b) build it as a de-risk for W8's export (the discipline is simpler to state at PSO).
- **D5. Q4 / W3.**  (Rec) launch first (critical path, `LIFetch` row); (b) none.
- **D6. Theorem 2.**  (Rec) keep `allocpidOpen2` + certificates as the audited riscv.cat-tier validation; note S.
- **D7. W2 failure mode** [R2.3][R3.s5].  Suspects: parked release fence, fence-clears-reservation, tearing (now a
  named premise), `.aq` off-by-one (now in `R`).  (Rec) change `WeakMem`'s event instance to MachCSL's shape where
  the kernel proofs allow; (b) a MachCSL change (owner-gated, serial).
- **D8. Hart model.**  (Rec) "exactly 8 harts, all booted" named; (b) a "≤ 8" variant (MachCSL change, serial).
- **D9. Panics.**  (Rec) not excluded, stated; (b) "no `panic:` bytes in the UART trace" (M–L).
- **D10. W1 scope.**  (Rec) W1 via `xv6NiPhi` now; (b) also W1b (L, serial) for pid/slot uniqueness, page disjointness.
- **D11. W1 tie.**  (Rec) observation-level β — already in `niRoundLaw`'s fork row; (b) state-level α.
- **D12. Which xv6** — RULED [OWN.4]: the `verified` fork, named in the header with its diff.
- **D13. Where the composed theorem lives.**  (Rec) `Weak/`, `--weak` audit with the full `Xv6` cone; (b) separate lane.
- **D14. Single era.**  (Rec) "one boot, no power cycles"; (b) multi-era W4 (`WExpr.power` in the pool; M).
- **D15. Reading of (a).**  (Rec) conclusions about the realizing MachCSL run + "the pf run never spins in the
  retry arm"; (b) no weak-side sentence; (c) weak-side `Reducible` (needs a weak WP package, XL).
- **D16. Non-vacuity gate** [R3.3] → merged into D22.
- **D17. SC-failure disclosure.**  (Rec) header names it; (b) §B(11) only.
- **D18. Fork-path coverage** — RULED [OWN.3]: W5d is part of the target (M2).  Residual: the user-fetch witness
  (whole-boot replay) — (Rec) not scheduled; (b) schedule after M2 (XL).
- **D19. Dangling exclusive reads** [R2.3-alt][R3.2].  (Rec) the shaped conformance predicate `execProgOk'S`
  (fused pairs) as a named premise; (b) a MachCSL change so dangling reservations do not block (serial, L,
  **unverified**); (c) a user-mode fact — unavailable.
- **D20. Single-copy atomicity** [R3.4, Q-K].  (Rec) `candSca` as a named ISA-faithful premise on the candidate
  (and on `xv6ConfS`'s loads); (b) add the atomicity axiom to sRVWMO/the cat transcription — re-opens T1, XL.
- **D21. M1's coverage** [R3.1, Q-L].  M1 is internal under [OWN.2]; the question is whether to REPORT it outside:
  (Rec) report as "composition milestone, kernel-only by premise `candKfetch` (`userinit`'s uncontended call)";
  (b) report nothing before M2.
- **D22. Non-vacuity gate** [R3.3, Q-M].  (Rec) the `_entry` first-load witness (M–L; certifies the premise set is
  SATISFIABLE, not that any candidate reaches `allocproc`) gates M1; (b) follow-up.
- **D23. W1 via `xv6NiPhi`** [R3.s1, Q-N].  (Rec) accept the re-scope (S–M) in place of a new ledger export; (b)
  the rev-3 `allocprocLedgerAdequacy` hook (M).
- **D24. W8's export form** [new, OWN.2].  (Rec) a per-state predicate on `g.m` + a ghost access ledger exported
  like `mmOk` (`Xv6/SystemSlot.lean:135-136`); (b) a new `Obs` per memory access (changes the observation trace,
  touches NI); (c) trace-free: prove `l2Claim`'s arms directly from W9's static check + ownership facts of the
  state interpretation (smallest if the ~5 residue idioms close).
- **D25. The published quantifier vs N11** [new, OWN.2].  The tree's chain is at RVWMO⁻(+deps), which FORBIDS
  store-buffer forwarding (`AxGraphCat.lean:10-16`) — not every `rvwmoCatConsistent` execution is covered.  (Rec)
  W12-spike first; then (a) re-derive the chain over `gppoCat` or (b) a forwarding-normalisation lemma; (c) if
  both are XL, publish at RVWMO⁻(+deps) with "no store-buffer forwarding" as the ONE named strengthening and
  say so in the header — a deviation from [OWN.2] the owner must accept explicitly.
- **D26. Stage-2 sequencing** [new].  (Rec) M1 → M2 → W12-spike-driven W12 ∥ W8 → W9/W10 → W11; (b) start W8 in
  parallel with Stage 1 (risk: `R` not fixed, export shape may change).
