# allocproc on RVWMO: target theorem, gap analysis, roadmap (design advisor, 2026-10-09)

**Status: rev 7 = rev 6 + review R6 (5 required changes, tags [R6.n]) + the three Stage-0 spike reports folded in
(W12-spike, W13-spike, W5d-G-spike: DONE, designs promoted to the real items) + ONE provisional deviation from an
owner ruling, tagged [OWN.8-conflict] (D32, first owner question).  [OWN.1–9] otherwise kept.**
**One-liner [R6.s1]: the published quantifier is riscv.cat RVWMO with TAGGED dependencies (`rvwmoCatConsistentT`),
plus an I/O-order PLATFORM assumption (`ioObAcyclic`, strongly-ordered MMIO as on QEMU virt) and a graph-tier
Zifencei fetch model (`gzFetch`) — two named trusted-base items with no reference model.**
History: rev 1 (2026-10-09) survey; rev 2 `…-review-R1.md` (11 req.; D8–D13); rev 3 `…-R2.md` (5 req., two
[R2.n-alt]; D14–D19); rev 4 `…-R3.md` (4 req.; D20–D23) + [OWN.1–4]; rev 5 `…-R4.md` (5 req.; D25, D27, D28); rev 6
`…-R5.md` (3 req.: quiescence VACUOUS → W13; W3 sibling root; `pairAdjacent`) + [OWN.5–9]; rev 7 (2026-10-09)
`…-R6.md` (5 req., s1–s4) + spikes: tagged cat model; a THIRD cat gate (W12b); `devAcyclic` REFUTED → `ioObAcyclic`
(provisional); T2-1c′ LANDED, W13 = XL; fetches ADMINISTRATIVE (`gzFetch`, cut form); W5b owns `execProgOk'S`; D32–D43.

**The kernel [OWN.4][R1.9]: xv6-riscv `b72cbac1`, branch `verified`** (`notes/STATUS.md:8-11`, `README.md:89-90`)
= upstream plus (a) a per-process root (`p->root`, `sys_chroot`, `igetroot`, root-aware `dirlookup`/walk) and
(b) upstream's post-`ded23f2` allocpid — bounded counter `PIDMAX = 1000` (`Xv6/ProcGeom.lean:80`) with a 64-slot
liveness scan, inlined by gcc into `allocproc+0x38..+0x94` (`claude-notes/kernel-defects.md:224-231`) — not the
textbook monotone `nextpid`.  Image `Xv6/KernelImage.lean` by `tools/dump_kernel.py`.

Advisory only; read-only survey of `../xv6iris-weak` (`Weak/`, `Xv6/`, `MachCSL/`, `notes/weak-memory-*.md`,
`claude-notes/{completed,design}/*weak*`).  Sizes: S ≤ 300 lines, M ≤ 800, L ≤ 2k, XL = multi-week / many files.
Unconfirmed claims are **unverified**.  Spike scratch files (build, no `sorry`): `Weak/CatOfMinusSpike.lean` (399),
`Weak/W13Spike.lean` (145), `../xv6iris-weak-w3/Weak/GraphFetchSpike.lean` (226; `propext, Quot.sound` only).

## 0. The two findings that reshape the question

**F1. allocproc is ALREADY fully verified in this tree — on a weak-memory machine, not on SC.**
`Xv6.Allocproc : ALLOCPROC` (`Xv6/LinkAllocproc.lean:14-16`, proof `Xv6/ProofAllocproc.lean:3623-3639`, 3.6k
lines; spec `Xv6/SpecAllocproc.lean:118` `allocprocPost`, `:204` `wp_allocproc_body`) covers the whole function on
the real image (0x80001b72..0x80001c72): the `proc[]` scan with `acquire`/`release` per slot (interrupts may be ON,
migrating hart via `wpNext`), the inlined allocpid under `pid_lock` with the 64-word collision scan (Löb-closed,
`PidLock.pidLedger`/`pidTie`, `Xv6/PidLock.lean:88,113`), `kalloc`, `proc_pagetable` with PTE writes into fresh OWNED
pages (`pptPost`), `memset`, `ra = forkret`, `sp = kstack + PGSIZE`, both failure tails through `freeproc`,
`p->pid`/`p->state` as `p->lock`-protected cells (`procHeld`).  Callees verified too (≈ 10.7k lines).  In the cone
of the audited roots (`tools/ci/roots.txt:6` `xv6FsAdequacy_closed`, via `Xv6/LinkSyscall.lean:84`/`LinkMain.lean:53`).

The memory model under all of that is `MachCSL.TsoMem` (`MachCSL/TsoMem.lean:1-40`; `relaxed-rr.md`): one total
store order with per-byte write histories, per-hart view FLOORS (load–load reordering), store forwarding by author,
store buffering, `fencePost` (`:345`; `fence rw,w`/`w,w`/`r,w` are NO-OPS, `:356-364`), `.aq` AMOs, LR/SC
reservations, a non-coherent i-cache view `itv` + `fence.i`.  **What it forbids that RVWMO allows** [R1.7]: (i)
store–store reordering and load buffering (stores never early) — the weak tier's sRVWMO residue (rule 14;
`Weak/WeakAxiomatic3.lean:2050-2071`; divergences LB and reader-fence-only MP, `Weak/WeakSrvwmoLitmus.lean:1663-1695`),
checked by reading, not by theorem — nothing relates TsoMem to `srvwmoConsistent`, and §B(10) does not need it
[R2.s2]; (ii) **reservation serialisation**: a foreign store or exclusive read overlapping a held reservation is
BLOCKED (`blockedStep`, `MachCSL/Lang.lean:366-378,395-403`; DMA `anyReserve`, `:539,562`); the reservation persists
until the holder's next store of ANY address (`:147-153`) or a blocked exclusive read, surviving fences (`:155-163`).
RVWMO's atomicity axiom constrains only SUCCESSFUL pairs; kernel code uses only `amoswap.w.aq`
(`Xv6/ProofAcquire.lean:5`), but USER code may `lr`/`sc` (the SC success predicates are two of the three audited
opaques).  Dependency order (ppo 9–13) is absent in TsoMem — the sound direction.  Honest description of the landed
system theorem: "xv6 on sRVWMO + reservation serialisation".  **Under [OWN.2] this is an INPUT, not the result**:
the published theorem is at RVWMO proper; TsoMem's proofs are re-justified there by robustness (§B(9)).

**F2. The AxSL tier cannot reach allocproc** [OWN.1: retired].  Theorem 2 (`allocpidOpen2`,
`Weak/AxSpinT2b2.lean:325`) covers ≈ 230 dynamic instructions at ≥ 57k lines [R1.s1]; allocproc's footprint is
≈ 120k with four more lock protocols, the freelist, private page-table pages.  Theorem 2 stays an audited
riscv.cat-tier validation of the handle-based lock protocol; do NOT extend it.

## A. The target theorem

**What "credible for xv6" requires** (an xv6/weak-memory expert's checklist):
1. the real kernel binary, named above [OWN.4]; every callee real, failure paths included.  The caller discharges
   `wp_allocproc_body`'s premises (`Xv6/SpecAllocproc.lean:204-224`: `k.tier = KTier.kpt`, `allocprocSlots (= 48)
   ≤ k.avail`, `k.noff + 2 < 2^31`, `"kmem"/"nextpid"/"proc" ∉ k.locks`, `procsInv`, the two `isLock`s,
   `kallocAvail γk on`, `procsAvailAt Γ pav tk`, `□ (killCred -∗ Q (-1))`, `actLend`) — kernel-state facts only;
2. harts [R1.1]: **exactly `NCPU = 8`, all booted** (`MachCSL/TsoMem.lean:54`; `PowerOn` forks `cpus =
   List.finRange NCPU`, `MachCSL/Lang.lean:315-320`; `riscvPowerAdequacy`, `MachCSL/Adequacy.lean:383`) — fewer
   harts NOT covered (D8).  The other harts run ARBITRARY xv6 kernel/user code, interrupts on where xv6 allows
   them, devices as modelled (2 UARTs, PLIC, virtio with DMA as a store-order agent) — on route (M); at the graph
   tier device-ACTIVE candidates exist only once W13 lands, today's bundle is device-QUIET [R5.s5][R5.1];
3. memory [OWN.2]: **RVWMO as the ISA defines it — the TAGGED cat model `rvwmoCatConsistentT GT` over `GdexecT`
   (`Weak/AxDeps.lean:208-211`: `gwf ∧ gppoCatTGmo ∧ gloadValue ∧ gatomicity ∧ gtdepsWf ∧ gtdepsGmo`, rule 12 over
   `gtAd` = the addr/data edges only; rules 1–5, 7-RCsc, 12; omits 6, 7-RCpc, 8; fidelity by litmus,
   `Weak/AxLitmus.lean:29`)** [R6.1].  **NOT the untagged `rvwmoCatConsistent` (`Weak/AxGraphCat.lean:191-194`)**:
   its `gppo12` ranges over the untagged `gdDeps` and so also orders `ctrl;[W];rfi;[R]`, which riscv.cat does NOT —
   the tree calls it "UNSOUND for safety" (`AxDeps.lean:12-18`), machine-checked by `twCatT :876` with
   `twNotCatForget :883`; `catTOfCat` goes cat→tagged, the converse fails (`:22-27`).  The chain runs on `forget GT`
   (W12 spike F1; Q-T = D33).  W→W reordering and load buffering ALLOWED; every strengthening NAMED;
4. page tables live: shared kernel table with concurrent hardware A/D write-back (`MachCSL/KptInv.lean:39,85`;
   TLB `MachCSL/UTlb.lean`), fresh user table private until published;
5. the conclusion is functional AND safety [R1.2][R1.9]: returned slot `&proc[j]`, `j < NPROC`, `p->lock` held,
   `state = USED`, `pid ∈ [1, PIDMAX]` distinct from every live pid, fresh trapframe page (`kalloc`'s fill of
   `5`, `Xv6/SpecKalloc.lean:69`, via `procPrivNocwd`, `SpecAllocproc.lean:131`), fresh user table with
   trampoline + trapframe, context `[forkret, kstack+PGSIZE, 0×12]`; or `0` with the lock released and everything
   freed; **no hart ever stuck** (`Reducible`); all kernel invariants preserved — i.e. exactly `allocprocPost`.
   **Panics are NOT excluded** (`panic` is a bare `wpLoop`, `Xv6/SpecPanic.lean:11-14`), **nor the two reducible
   spin arms** [R2.4]: `blockedStep` and the weak retry self-loop of a lost exclusive pair
   (`Weak/WeakEvInst.lean:360-364`).  "never panics" = "no `panic:` bytes in the UART trace" (`uartSentSub`,
   `Xv6/UartTrace.lean:182`), M–L, new work — D9;
6. axioms `propext`/`Classical.choice`/`Quot.sound` + `bv_decide` certificates + the three opaques
   (`tools/audit/baseline.json:11-14`), no `sorry`; trusted base named: Sail model, image dump, the TAGGED cat
   transcription and its tagged conformance text `gdexecQconfT` (new trusted-SURFACE text, reviewed against
   `rowDepsT`'s correction (5), `AxDeps.lean:56-60`) [R6.1], the graph-tier fetch model (W5d-G `gzFetch`, §B(4)(iii);
   RULED [OWN.6]), the graph-tier I/O-order PLATFORM assumption (W13 `ioObAcyclic`; [OWN.8-conflict], D32)
   [R4.2][R5.1][R6.3].

**Legitimately out of scope:** liveness/fairness, timing, mixed-size fidelity of the cat model (N10), MMIO
ordering beyond the modelled devices, hardware outside the Sail model, power cycles (SINGLE ERA [R2.2]).

**The statement to aim for — three layers.**  *T-alloc* (contract, exists): `Xv6.Allocproc` on MachCSL.
*M1/M2 (internal milestones, NOT published [OWN.2])*: the composed sRVWMO theorem, pinned/kernel-only (M1) then
unpinned (M2), below.  *T-alloc-RVWMO (THE published claim)* [OWN.2][OWN.3][R3.1][R3.2][R3.4][R4.2][R4.4][R5.1]
[R6.1][R6.3]:
```
∀ (σ0 : WGState) (GT : GfexecT),             -- NEW: the fabric bundle (Weak/WeakRvwmoFab.lean:516) over GdexecT
  wbootFacts σ0 ∧ σ0.wggen = 0 ∧ (∃ ds, σ0.wgdev = ds.reset ∧ diskOf ds = fsImgDisk) ∧        -- the boot [R2.2]
  rvwmoCatConsistentT GT.gfGd ∧                                 -- riscv.cat, TAGGED deps (AxDeps.lean:208) [R6.1]
  ioObAcyclic (forgetF GT) ∧                     -- I/O-order platform assumption (W13Spike.lean:83-95) [R6.3][D32]
  xv6ConfS (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) GT                             -- xv6 is the program (†)
  →
  (a) the realizing MachCSL run (robustness W9–W11 → sRVWMO cand → T1 → pf run → W4, PREFIXED by PowerOn from
      the given disk) satisfies xv6FsAdequacy_closed's conclusions for ITS ONE ERA: Reducible (panics, two spin
      arms not excluded), xv6TracePure (fs purity + mmOk), xv6NiPhi / unionAdequacyClosed [R3.s2]; the realized
      pf run never enters the retry arm [R2.3]; and
  (b) the allocproc shadow tied to κs (W1 via xv6NiPhi [R3.s1]): every filed fork round answers usysForkAns of
      its citation (pid = pidPick of the cited prefix, ∈ [1, PIDMAX], or -1); KAlloc/KNull/KFree well-formed
      (poolEmpty at KNull); after W1b, live pids pairwise distinct.
```
(†) `xv6ConfS` is the SHAPED, UNPINNED, FABRIC-ORDERED, TAGGED conformance bundle [R5.1][R6.1][R6.3][R6.4]:
`gfexecConfA` (W13 (I)/(W): per-hart `hartConff` emissions with TWO fabric endpoints, `Fab.lean:523-536`; dev blocks
keyed by position `(i, k)` as their OWN admin-only trace steps, `execProgOkA`, not folded into the next tagged
event), `fab 0 = efInit σ0.wgdev`, `rowDepsT` tags in `GT.gtDeps` (`gdexecQconfT`-style; `rowDepsSubT`,
`AxDeps.lean:690`, gives the untagged bundle back), the fetch clause `emZifencei` (W5d-G, replacing `emFetchImg`,
`Fab.lean:534`/`Supply.lean:277-278`) with `F_em ⊆ GT.gdFetch`, exclusive pairs FUSED (the `execProgOk'S` shape of
[R3.2], DEFINED by W5b [R6.4]) — NOT today's quiescent `gdexecQconf` (`Weak/WeakRvwmoSupply.lean:281-289`), whose
`emDevfree` (`:273`) forbids every `LDev`.  **Quiescence is VACUOUS for allocproc** (W13 spike CONFIRMS): the event
LTS emits `LDev` for EVERY MMIO access (`Weak/WeakEvInst.lean:300-303,335-338`) and the disk row's START/COMMIT
(`:484,502`; the row is in `epsInit`, `WeakEvCapstone.lean:1026-1027`); hart 0's `main` runs `consoleinit` FIRST
(`Xv6/SpecMain.lean:7-10`) = `uartinitone`'s seven `WriteReg`s (`Xv6/SpecUartinitone.lean:6-13`); so `userinit →
allocproc` is unreachable in EVERY quiescent `GD`, (b) holds vacuously and (a)'s run never reaches allocproc
(route-b: "HONEST MILESTONE … not the final theorem", `weak-memory-route-b.md:1009-1020`).  No `LDev`-emitting
emission witness exists in the tree (`gfexecConfOfQconf`, `Fab.lean:648`).
**`ioObAcyclic` REPLACES rev 6's `devAcyclic`** [R6.3][OWN.8-conflict]: the RULED literal axiom "`po ∪ rf ∪ gmo|W ∪
dev` acyclic on the quantified graph" IS `gfexecConsistent'` (`Weak/WeakRvwmoLin2.lean:761-762`; `ptraceRel` = po ∪
rf ∪ gmo|W, `:124`); `po ∪ rf` acyclic is "no load buffering", `po ∪ gmo|W` acyclic is "no W→W reordering" —
machine-checked `lbExcluded` (`Weak/W13Spike.lean:35`: the LB graph is `rvwmoCatConsistent` yet fails
`gfexecConsistent' ⟨lbgd, []⟩` at an EMPTY fabric), contradicting [OWN.2]; and it subsumes the kill
(`xv6RvwmoSafeModuloF`, `Capstone.lean:228-265`, carries no `l2Claim`/`walkSupply`) — a robustness ASSUMPTION, not a
hardware model.  The spike's replacement, applied PROVISIONALLY: `ioObAcyclic GF := ∀ x, ¬ tc (ioOrd GF) x x` with
`Ioev = ev e | dv i k` and `ioOrd` = `gmoLt` on events, PROGRAM ORDER between hart `i`'s I/O node `dv i k` and its own
`gmem` events, fabric order (`gdevAdj`, or same-hart `k < l`) between I/O nodes (`W13Spike.lean:83-95`); free at an
empty fabric (`ioObAcyclicNodev :109`) so LB and W→W stay in the quantifier; admits the SC case (`w13fIoOk :116`);
the owner's intent "the fabric order is realizable by the machine's own ordering" (`route-b.md:1040-1055`) is
preserved; it does NOT assume `racyD` acyclicity — the kill still carries that.  `gdevAdj ⊆ gmo` (`Fab.lean:542-544`)
is ALSO out (`scDevExcluded`/`scDevUnrealizable`, `W13Spike.lean:55,66`: a plain SC execution MMIO₀; MMIO₁; st x; ld
x = 1 fails it and no `ptraceExt` trace visits the blocks in fabric order) — block-atomic folding of `LDev` into the
next tagged step (`execProgOk'`, `WeakAxRealize.lean:373-386`) makes EVERY block-level dev condition exclude SC
executions, hence the realization-interface change (I).  `candSca` is NOT a premise here:
a `Cand` predicate, ill-typed on `GD`, DERIVED at Stage 2 from `gloadValue` (`linCandSca`, W11) [R4.4].  The
conformance premise is genuine: the graph side alone yields only `execWf`-style facts; the program half is realized
by `execWfPfRunProg` (`Weak/WeakAxRealize.lean:802-808`) [R1.5].  **The pin fixes WHAT a fetch answers, not WHERE it
fetches** [R3.1]: at M1 the premise is `pstepPin` + `candKfetch` (every `LIFetch` footprint in W3's pristine window
`[bcRoLo, bcRoHi)`, §B(4) [R5.2]) — what makes M1 kernel-only; M2 replaces both by CUT-form Zifencei admissibility
on the pf side; the target needs the graph-side twin `gzFetch` (W5d-G).  Boot premises: `xv6FsAdequacy_closed`'s
(`Xv6/LinkSystemAdequacyClosed.lean:20-26`) transposed through `PowerOn` (`MachCSL/Lang.lean:294-304`) to
`wbootFacts` (`Weak/WeakLang.lean:482-490`); `diskOf ds.reset = diskOf ds` from `BootSharedDev.lean:283` [R3.s4].
(b) is the trace-observable shadow of `allocprocPost` in the NI idiom (`xv6NiPhi`, `Xv6/NiAdequacy.lean:91-92`) [R1.4].
*M1/M2 (internal)*: the same with `srvwmoConsistent c ∧ execProgOk'S (pstepPin …) … ∧ candKfetch ∧ candSca`
(M1) / `execProgOk'S pstepEv …` with cut-form Zifencei fetches `∧ candSca` (M2) in place of the graph premises.
sRVWMO ("RVWMO, stores never early") results stay milestones only [OWN.2].  `xv6RvwmoSafeModuloF`/
`gfexecConsistent'` are RETIRED as a publishable form — kept as an internal lemma on normalized graphs (D39).

## B. Gap analysis

Legend: *need* = needed for T-alloc-RVWMO; *route* = (M) machine tier / (A) AxSL tier (retired [OWN.1]).

**(1) AxSL tier not composed with the machine tier.**  Route (A) only (retired): XL; Theorem 2 = validation (D6).
**(2) Page tables.**  Route (M): CLOSED — kernel table a live shared invariant with A/D variants (`KptInv.pteVariant`),
`utlbOk` "up to A/D" (`MachCSL/UTlb.lean:17-21`) [R1.s3]; user-table pages fresh owned memory (`pptPost`), published
at `satp` + `sfence.vma`; named assumption (§B(11)): Svadu write-back as a view-neutral LR/SC.  S.  **(3) SIE = 0,
3 harts, no devices/DMA.**  Route (M): CLOSED (`KCtx.sie`, `wpNext`, `NCPU = 8`, DMA at the store order).  Graph
tier: OPEN — the quiescent bundle has NO devices; the fabric bundle is W13 (§A(†)) [R5.1].

**(4) Text never written / fetch pinned** [R1.8][R2.1][R2.1-alt][R3.1][R4.2].  The fetch-view premise is carried
by both weak capstones (`xv6SrvwmoSafe` (b'), `Weak/WeakSrvwmoCapstone.lean:88-89`; `xv6RvwmoSafeModulo`,
`Weak/WeakRvwmoCapstone.lean:195`: `∀ ρ, rtc epfRun … → efetchItvOk ρ.1 ρ.2`, `Weak/WeakEvCapstone.lean:681-685`)
because the lift `wpPfRtcEpfRtc` (`:1008-1011`) needs it (`Hcov`, `WeakSrvwmoCapstone.lean:118-120` [R3.s4]); not
dischargeable weak-side on route (M).  Treatment: (i) W5 does NOT go through `epfRun`; it starts from
`execWfPfRunProg`'s `rtc (wpPfRun pstepEv pclsEv) …` (`WeakAxRealize.lean:802-808`, via `wpPfRunPinSub :225`), and
W4 projects `wpPfRun` runs.  (ii) The (↓) `LIFetch` row of W2 carries the content: the pf fetch is admissible at
floor 0 (`PFIFetch`, `Weak/WeakPromiseBridge.lean:441-449`) while TsoMem fetches as the i-cache agent at `σ.itv
cpu ≤ tvn ≤ top` (`MachCSL/Lang.lean:360-362`); the row closes iff no log write hits the fetched bytes between the
version read and `itv`.  THE mechanism on the TsoMem side [R5.s4][R5.2]: kernel text is held as `imgByte a v :=
∃ tid, a ↦ₕ□ [⟨0, tid, v⟩]` — a DISCARDED-fraction singleton HISTORY (`MachCSL/Ctx.lean:433-436`), persistent,
assembled into `kernelText` (`Xv6/KernelText.lean:25-30`) from `bootRo … bcRoLo bcRoHi` (`Xv6/BootCarve.lean:582`;
window `[ramBase, _data)`, `:143-144`, ⊇ text + rodata); against the auth heap it reads the image byte at EVERY view
(`MachCSL/Wp.lean:1478,1490`) and a DMA write needs `DFrac.own 1` (`MachCSL/WpDma.lean:142-145`) — so `candKfetch`
(every `LIFetch` footprint ⊆ `[bcRoLo, bcRoHi)` ⊇ `[text, etext = 0x80007000)`, `Xv6/KernelImage.lean:771`) is
dischargeable for kernel text (W3) and NOT for user pages (`own 1` cells) [R5.2].  **[R3.1] The pin does not make
a candidate kernel-only**: a pinned fetch is pf-admissible AT ANY LOG (`fetchPinIfetchOk`,
`WeakAxRealize.lean:167-176`; `ifetchByteOkb` with `itv = 0`, `WeakPromise.lean:228-231`), the program LTS constrains
the fetched value only through memory (`pstepEv`'s i-cache arm, `WeakEvInst.lean:306-312`), and the boot image is
ZERO past the ELF (`bootByte_zero`, `MachCSL/BootImage.lean:31` [R6.5a]) — a conformant pinned candidate can run
`userinit → scheduler → userret (fence.i) → sret` and fetch the image's zeros at the user page while TsoMem's `itv`
has passed `uvmfirst`'s writes: W4's `LIFetch` row has no TsoMem step.  Fix: M1 carries `candKfetch` inside the
shaped conformance predicate; W3 discharges the row ONLY under it.
(iii) **The unpinned supply is TWO items** [R4.2], SHAPED by the W5d-G spike (DONE) [R6.4b].  **W5d** (M2, L; in the
target [OWN.3]) is the pf half: `execWfPfRunProgF`, the replay at `pstepEv` with a Zifencei side condition in place
of `fetchPin`.  **Fix now (spike §3.4): the M2 fetch clause is the CUT form `∃ q, itv ≤ q ≤ |log| ∧ ifetchOk img log
q base tvs`** (`fetchCutOk`, `GraphFetchSpike.lean:36`; `ifetchOk`, `Weak/WeakEvInst.lean:564`; `itvPostMachCSL`,
`Weak/WeakInterp.lean:378-384`), NOT per-byte `ifetchOk … itv` — per-byte fetches tear ([R3.4]; `ifetchByteOk`,
`WeakPromise.lean:222-231`) and the cut form is what W5d-G produces; W4's (↓) `LIFetch` row then holds for user text
(TsoMem reads at `tvn := q`) and W2's `R` carries `itv ≤ q`.  **W5d-G** (Stage 2, **L** ≈ 1.8–2.2k + ONE XL risk; was
"L–XL unverified") is the graph half.  **Verdict: keep the fetch an ADMINISTRATIVE emission item** (`hemit`'s `eadm`,
`Weak/WeakRvwmoConf.lean:712-722`; `lbAdmin`, `WeakAxRealize.lean:130-134`) and add a RELATIONAL Zifencei condition
plus a "fetch fragment" of ordering edges stored as graph data, as `gdDeps` stores the store-dep fragment — NOT a
graph event (the [R4.s1] `IF`-event shape gives the same edges at much higher cost: a `Lbl` constructor matched in
~38 files, new arms in `gwf`/`gloadValue`/Xchg/Topo/Lin, a `linCand` stutter label); semantically it IS the `IF`
event at a gmo position, encoded as an EXISTENTIAL cut.  **The trusted-base item
`gzFetch G C i k base tvs`** (`GraphFetchSpike.lean:189`), per fetched byte `(t, v)`: (Z1) value — `logByte img (gwlog
G) t (base+j) = some v` (tag `t` = a gmo write index, `0` = image); (Z2) not from the future — the source is `gmoLt`
the hart's next own write `gnxw G (i,k)`; (Z3) fresh past `fence.i` — every write `w'` to the byte co-after the
source is gmo-after every contributor `c ∈ C` (own writes po-before a `fence.i` site before the slot and rf-sources
of the hart's reads po-before it: `gzContrib`) AND after every other byte's source (one fill instant per label).
`emZifencei G C i em` (`:206`) is `xv6ConfS`'s fetch clause: every `(LIFetch base tvs, none)` admin item satisfies
`gzFetch` at its row slot.  Hardware readings, NAMED in §B(11): (H1) a no-forwarding I$ with one fill instant per
label; (H2) `fence.i` completes the hart's earlier stores and reads before later fetches (for own stores = TsoMem's
`itv ≥ ownPub` drain, already beyond the spec text); (H3) stores are non-speculative relative to fetch.  `fence.i`
sites come from the EMISSION, not the graph: `fence.i` and the Q7 `sfence.vma` marker share the label `LFence false
false false false` (`WeakEvInst.lean:272-275`; `WeakEvLang.lean:418-419,745`), so `emFenceI em f` := the row item at
`f` is that fence AND the latest `LInstr`/`LIFetch` in the admin block before it is `LInstr` (`emFenceISound`, M;
D40).  Proved in the scratch: `fetchCutOk`, `fetchCutPrefix :63` (the cut form = the pf/W5d check at the realizing
prefix with ONE view), `fetchCutEdge :83`, `fetchRelOk`, `fetchRelCut :140`, `fetchPinCutOk :213`; stated: `gzFetch`,
`gzFetchCut`, `emZifencei`, `gfcut`, `gwlog`.  **Kernel-text instance**: tag 0, image bytes, no write to the bytes ⇒
(Z1)–(Z3) vacuous; `candKfetch` + W3's history fact discharge `gzFetch` for every kernel fetch; kernel-only
executions get an EMPTY fetch fragment — no new edges, no new kill arms.  Consumption: edges E1 src→nxw, E2 c→w',
E3 src_l→w'_j, all `gmoLt` on `GD` by (Z2)/(Z3), stored as `Gdexec.gdFetch` (D42), `F_em ⊆ GD.gdFetch` in `xv6ConfS`;
`rvwmoCatConsistentT` untouched (the fragment is not riscv.cat); retime: `L ⊇ racyD ∪ F` + `grule14 GD'` give
`fetchRelOk` at `GD'` (the contributor SET is rf/po-defined, hence retime-invariant — `normalizeOfAcyclic` renames
write indices NON-monotonically, `WeakRvwmoTopo.lean:594-607`, so no max/cut condition transports), then
`fetchRelCut` gives `gzFetchCut`; realize: replay the fetch just before `(i,k)`'s step, log = `gwlog.take gfcut`
(rank lemma `linPrefixLog`; `linCand`, `WeakRvwmoLin.lean:440-453`), itv `≤ lmax cs` by a floor bound,
`fetchCutPrefix` gives `ifetchOk` and the single view `q`.  Measured sites: `pstepPin` 19 files/121, `emFetchImg`
10/41, `gdexecQconf` 18/124, `gdDeps` 31/133, `wlblRen` 3/41.  Sizes: W3 M–L [R5.2]; W5d L; W5d-G L (G1–G5; G6 shared
with W11 (iii); G7 L in W11/W8); **XL risk R1 — hull closure**: `hullOk` is
rf-closed only (`WeakRvwmoHull.lean:557-560`) and knows nothing of fetch sources — a kept fetch whose next own write
was cut away loses its source; fix (a, recommended): anchor sources to EVERY po-later memory access (E1′, a stronger
but gmo-true (H3)), then "kept fetch ⇒ source kept" follows from racyD-closure (M if the cut selection is
racyD-driven, XL if `t2linAux` must be re-proved); (b) keep E1 and let hulls cut each hart only directly after a
memory event (re-check `t2linAux`'s cut selection).
**(5)–(8) Segment coverage, scope pins, store-value rows, stack/cpu privacy.**  Route (M): CLOSED (F1; the pid
ledger handles wrap/collision retries, `Xv6/ProofAllocproc.lean:16-24`; text facts by `rfl`/`decide`; real
`stackOwn`/`kctx` resources).

**(9) THE gap: TsoMem is sRVWMO + reservation serialisation; the target is RVWMO proper** [R1.7][OWN.2].
*Inventory of weaker models in the Lean tree.*  (α) `WeakMem` pf machine = sRVWMO operational (T1
`srvwmoRealizable`, `Weak/WeakAxiomatic3.lean:2077`; T2 `t2Ev`, `Weak/WeakEvInst.lean:2046`) — TsoMem's strength
class.  (β) `WeakPromise*` (`Weak/WeakPromise.lean:1-16`) — LB reachable; RVWMO fidelity BY INSPECTION only
(`weak-memory-m6-robustness.md:42-48`).  (γ) PSO two-log machine: Rocq-only design; NOTHING in Lean.  (δ) Graphs:
the tagged cat model (§A(3)), the untagged `rvwmoCatConsistent`, and `rvwmoMinusDepsConsistent`
(`Weak/WeakRvwmoGraph.lean:628`).  **`minusImpliesCat` (`Weak/AxGraphCat.lean:274`) runs the WRONG way for us**:
RVWMO⁻ renders rules 1–3 as all of `gpoloc` (`WeakRvwmoGraph.lean:224-228`), ordering a write before its own
po-later same-byte read — it FORBIDS store-buffer forwarding (N11, `AxGraphCat.lean:10-16`,
`notes/weak-memory-scope.md:209-212`), so a theorem over RVWMO⁻ graphs misses cat-consistent forwarding executions.
The whole Tier-2 chain (`rule14Linearization`, `Weak/WeakRvwmoLin.lean:1846`; `racyD`, `Acyc.lean:200`;
`t2linOfL2'''`, `Walk3.lean:77`; `xv6RvwmoSafeModulo`, `Capstone.lean:187`; 45 files, 33k lines) starts at RVWMO⁻(+deps).
**Where the cat gap lives — THREE gates, not two** [R4.5][R4.s2][R6.2] (W12 spike, DONE: 26 files in the
capstone/Walk3 closure use `rvwmoMinus*`/`gppoGmo`, classified by projection).  Survive as is (core `gwf ∧
gloadValue ∧ gatomicity ∧ gdepsWf`, never ppo): `normalizeOfAcyclic`/`topoExists`/`topoLinearizes`/`racyDMem`
(`Topo.lean:188-193,558,585,594`), `topoSupply`, `hullRealizable*`, `hullRun`; `segPinGmo` (`Glue.lean:233-240`,
rules 4, 5, deps); `cyBackwardNotAq` (rule 5).  Untouched: `rule14Linearization`/`WeakRvwmoLin` (47 `hppo`)/`Lin2`/
`Norm`/`PreNorm*`/`Xchg` — on the NORMALIZED `GD'`, RVWMO⁻ + rule 14 BY CONSTRUCTION.  **Gate 1 (rfi)**: `racyDSplit`
(`Glue.lean:101-110`) sends EVERY rf arm to `gcross`, whose `grfGmo` (`Acyc.lean:218-233`) maps the FORWARDING case
through `gpoloc`'s W→R edge — the edge cat lacks; CLOSED in the scratch: `racyDSplitC` (rfi → `rsameC`, po-forward
by cat rule 1 alone, `grfiLex`; `rsameCAcyclic`), `gcrossE` = rfe ∪ co ∪ fr with `gcrossEGmo` from `gwf` + lv only,
hence `CertC`/`chainC`/`cycleKillArmsC`.  **Gate 2 (lock kit)**: `csChained` (`KillArms.lean:499`) and
`acqSrc`/`acqTsLt`/`acqSrcRel`/`acqFoldFree` use rules 1, 4, 5 only (`Lock.lean:120,125,200,235`) — CLOSED, re-proved
verbatim as `*C`.  **Gate 3 (the certification walk's floor kit — W10's toolkit) BREAKS and needs a REDESIGN**:
`gvisUb G r n` = "every write of index ≤ n is gmo-before r" (`Weak/WeakRvwmoFloor.lean:100-101`) is FALSE under cat
for an own store forwarded to a po-later read (it may be gmo-AFTER the read); `greadSrcUb` (`:442-453`) closes its
po case with `gpolocGmo` W→R, `finvStep` (`:605-619`) uses it for the coh hook `hoacc`; consumers `cinvReplay`/
`floorOfCgraph`/`certFloorOk`/`cpolRead` (`Cert3.lean:311,391,428,468`, under `rvwmoMinusConsistent G`) reached from
`wblkPolAt` (`Walk.lean:700-731`, `LLoad` arm).  The FLOOR itself holds (`t = gwix w`; co-maximality covers po-visible
writes) but needs a per-byte coherence invariant (SC-per-location through rules 1/2) in place of `gvisUb` — Floor
§4–§6 and Cert3 §2–§3, ≈ 0.5–1k (M–L) = **W12b** (D34).  Two smaller mismatches, VACUOUS for kernel rows (release =
`fence rw,w; sw`, `Xv6/ProofRelease.lean:83-86`; acquire = `amoswap.w.aq`) and OPEN for user rows under [OWN.3]: the
`wVRel` hook consumes rule 7 RCpc (`Floor.lean:21`, `grelacqGmo`), which `grcsc` (both bits, `AxGraphCat.lean:163`)
lacks (D35); WeakMem's forwarded ACQUIRE load (`fwdView ws true a t = t`, `WeakMem.lean:585-591`) is stricter than
cat (D36).  **So the gap is CONFINED to the kill AND the walk floor** — not the 33k lines.  Witnesses (`lkw`/`lkw2`,
`mpwd`, `mpgd`, `ergd`, `lbgd`) need NO re-proof: `catADOfMinus` (∘ `minusImpliesCat`) — corrects [R5.s1].  Residual
premises `l2ClaimAt`/`cutSupply`/`certSupply`/`walkSupply`/`walkPolicy` are re-hypothesised; their discharges
(W8–W11) must handle FORWARDING graphs (TsoMem forwards, so W8's exports should carry over).
*Why plain DRF does not apply.*  xv6 races by design.  The Lean pin census at THIS image [R4.1]
(`Weak/KernelPins.lean:22-23`, by `tools/gen_weak_pins.py` at `b72cbac1`): **1689 load sites: 1034 `PStack`, 3
`PPerCpu`, 289 `PCtrl`, 1 `PFence`, 180 `PDep`, 63 `PCall`, 119 `PResidue`; 58 certifying witnesses need the
sp-frame assumption `own = true`** (`KernelPinsDef.lean:447-465`; checker `pinnedb`/`fwalk`/`pdfs`, `pinDepth = 2`).
Racy flag reads (`started`, `panicked`, UART LSR, virtio `used->idx`, `ticks`, `p->killed`, `p->state`) are pinned
by branch/fence/lock.  The applicable theorem is ROBUSTNESS UNDER A PER-SITE DISCIPLINE (L2′ = `l2Claim`,
`Weak/WeakRvwmoGlue.lean:449`: per cycle segment `segPin ∨ csHyps ∨ Bad`, `:229,400,440`) — DRF generalised: every
cross-hart read is pinned by ppo before the hart's next store, or is lock-protected (`protRead`/`wprotAt`,
`Weak/WeakGhost.lean:3408,1040`), or observes an owned-unpublished message (`Bad`).  The discipline must be
established on the STRONG model's executions; the only verified source is the TsoMem Iris proofs — which today
export `mmOk` only (`MachCSL/Resources.lean:779-785`), nothing per access.
*The routes, sized candidly* [R6.s3: (9a)–(9c) compressed, RULED]: **(9a)** re-verify xv6 on a weaker MachCSL
instance (none exists; Xv6 cone ≈ 0.65M lines over 77k of `MachCSL`; PSO alone "2–4 weeks is the floor" in Rocq, LB
has no design; link to cat a further Promising≡RVWMO-grade theorem) — **XL × 2, rejected**.  **(9b)** PSO two-log
machine W6 (L–XL fresh in Lean; "RVWMO minus LB minus deps"; LB robustness still needs the per-site discipline) —
not on the path, optional de-risk of W8's export (D4).  **(9c)** promise-machine robustness W7-P (`robustMain`,
`Weak/WeakRobustMain.lean:1520`, exists; φ refutable at event granularity, `weak-memory-lift.md:19-29`; quantifier
= the promising machine, fidelity EXTERNAL) — **fails [OWN.2]**, D2′ fallback only.
- **(9d) *Graph-tier robustness re-sourced from TsoMem (RECOMMENDED — the cheapest SOUND route: the T2-LIN
  induction `cycleKill`, `Weak/WeakRvwmoLinInd.lean:155`, realizes each proper hull as an sRVWMO candidate,
  `hullRun`, `Glue.lean:272-290`, W4 turns that into a TsoMem run on which the SC tree's facts hold — robustness by
  minimal violation, reusing the 33k-line chain).*  Residue of `xv6RvwmoSafeModulo` today (`Capstone.lean:187-215`):
  (R-1) `l2Claim`; (R-2) `walkSupply` (`Weak/WeakRvwmoGlue2.lean:453`), reduced to the per-state datum
  `wsegSupply`/`walkPolicy` (`WeakRvwmoWalk2.lean:453`, `Walk.lean:897`; `t2linOfL2'''`, `Walk3.lean:77`; its witness
  a hand-built LB cycle, `Weak/WeakRvwmoCycWit.lean:1-30`); `wpPackage` (`Glue.lean:338-346`: an EWP proof of ALL of
  xv6 on the weak event language — xv6 does not have it; `weakSystemAdequacyPhi`, `Weak/WeakAdequacy.lean:194`);
  `efetchItvOk` (W3/W5d); **(R-3)** the pin bridge's residual: "that a `pstepEv` run's items ARE grouped as the
  checker's pc walk assumes" (`Weak/WeakRvwmoPinBridge2.lean:28-29`) [R4.1].  **What EXISTS for W9** [R4.1]:
  `Weak/KernelPins.lean` (1,901 lines, the witness table), `KernelPinsDef.lean` (639, the checker),
  `tools/gen_weak_pins.py` (1,004; `--check` re-verifies); `imagePinnedb`/`pinsCover` (`KernelPins.lean:1817-1860`);
  the bridge `pinSegPin` (PDep ⇒ `rowDeps` ⇒ `gdDeps` ⇒ `segPin`, `WeakRvwmoPinBridge.lean:284-330`;
  `segPinOfRowFence :295`) and `pinSegPin'` with `checkerTaintSubProv` DISCHARGED for the oracle `psites`
  (`PinBridge2.lean:530-553`); the callee-summary table is "an AUDIT artifact nothing downstream reads"
  (`route-b.md:1456-1460`).  Work: **W8** export the discipline from the SC tree; **W9a** R-3 (align a `pstepEv`
  run's item groups with the checker's walk; `PinBridge2` §8 has both halves on one computed stretch) — now targets
  `segPinC` (one-step pins by `pinStepOfSegPinArm`; segments merged across an rfi with a PDep entry need
  `segPinCForward`: +M [R6.1]); **W9b** the non-certifying classes are W8's INPUT, not `segPin`: `PStack`/`PPerCpu`
  (1,037) = "no foreign writer" = W8's ownership (i), the 58 `own = true` witnesses rest on the same fact, `PCall` 63 +
  `PResidue` 119 = 182 sites = W8's (ii)/(iii) (D28, RULED (a) [OWN.7]); **W10** `wsegSupply` for xv6; **W11**
  re-source the glue's `Bad`/`protReg` from W8 via W4, restate the capstone over `xv6ConfS`; **W12** the cat kill
  (gates 1–2) + **W12b** the cat floor (gate 3); **W5d-G** fetches on the graph tier; **W13** the fabric bundle,
  `ioObAcyclic`, the realization interface, T2-1c″ (§A(†)) [R5.1][R6.3].  Sizes (✓ = spike-confirmed): W8 L–XL,
  W9a L (M–L + M ✓), W9b in W8, W10 M–L (**unverified**; L if it absorbs W12b), W11 L [R4.3], **W12 M–L ≈ 1.2–1.8k ✓**
  (was L–XL), **W12b M–L ≈ 0.5–1k ✓**, **W5d-G L ≈ 1.8–2.2k ✓ + XL risk R1**, **W13 XL ✓** (≈ the landed kill
  pipeline; 3.6k lines of Fab/FabInd/Lin2/Floor reused as is).  **Total: XL** — multi-week, many files; W13 is the
  bulk, W5d-G's hull closure the open risk.
*Recommended:* (9d), staged after M2; the three spikes are DONE and CONFIRM D25 (a) [OWN.5], SHAPE D27 (a)
[OWN.6], and REFUTE the literal [OWN.8] (D32); (9b) only if W8 wants a smaller model (D4); (9c) as D2′ fallback.

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
realized FUSED `LRmw` pairs (`lblRealizesPair`, `Weak/WeakAxRealize.lean:305-313`).  **[R2.3-alt]** a STANDALONE
`LExLoad` is realizable as a plain `LLoad` (`lbNobarex`, `:97-103`; `projLbl :545`); TsoMem's dangling reservation
blocks foreign stores and its exclusive read takes `topBytes` (`Lang.lean:147-153,368-371`) — (↓) fails.
**[R3.2] the shape cannot be a separate conjunct on `(c, pst)`**: the realizing `l` and the stars are existential
per index inside `execProgOk'` (`WeakAxRealize.lean:373-386`; `admStar = rtc admStep`, `:343-344`).
So the premise is ONE shaped conformance predicate **`execProgOk'S pstep pcls pst dv E`** := `execProgOk'` with
(i) the left disjunct's `l` not an `LExLoad` (re-imposing `lbFused` on the left arm only, cf. `lblRealizesUnproj
:245-247`), (ii) the stars as label-carrying `admRun`s (`Weak/WeakRvwmoConf.lean:374-381`) whose every `LIFetch`
is in kernel text (M1, `candKfetch`) / cut-form Zifencei-admissible (M2), (iii) every `LLoad` single-copy-atomic
(`candSca`, below).  **It exists in NO file** (grep `Weak/ Xv6/ MachCSL/`: only `execProgOk'Snoc`/`SnocPair`) —
**W5b DEFINES it AND `pairAdjacent` on day one** [R6.4c], stated over the STEP LIST so that W13 (I)'s admin-only
steps (`execProgOkA`) reuse the same shape clauses (fused left arm; label-carrying `admRun`s; no foreign step
between pair halves) rather than orphaning W5b's theorem — the two are co-designed (D38).  W5b consumes it and
carries **`pairAdjacent`** — NEW, in NO file of the tree (coined by R2), DEFINED HERE so W2 and W5b copy ONE text
[R5.3]: *in a shaped run every realized exclusive pair's halves `l1 = LExLoad …`, `l2 = LExStore …`
(`lblRealizesPair`, `WeakAxRealize.lean:305-313`) are consecutive steps of the SAME hart up to its own
`LInstr`-free administrative star `admStar pstep false pm dm pm2 dm2` (`execProgOk'`'s right arm, `:380-386`, one
exec index); no other agent's step — in particular no foreign store — lies between them* — plus the fetch/SCA facts
along the run; W5c must PRODUCE it (`execProgOk'Snoc`, `Weak/WeakRvwmoCert.lean:413`, yields plain `execProgOk'` —
an S-variant or derivation lemma is needed).  At Stage 2 the chain's `RunData`/`cstOk`/`segStep`/`topoSupply`/
`t2linSupply` (all plain `execProgOk'` today) must produce the S-variant — W11 (iii) [R4.3], one pass with W5d-G's
G6 (`pstepPin` → `execProgOk'S`, 19 files: AxRealize 26, Supply 14, Cert 9, Cert2 8, Fab 7, Cert3 7, SrvwmoCapstone
6, CycWit 6, Cert4 6, AxAdequacy 6, Cert3b 5, LinInd/Lin2/FabInd 4, Capstone 3, Glue/ConfWit2 2, Glue2/AxRunGV 1).
**[R3.4] (↓) fails on PLAIN LOADS even on shaped runs — tearing.**  WeakMem's `readable` is per byte
(`Weak/WeakMem.lean:400-402`; `readOkD`, `WeakPromise.lean:183-188`; `byteRd`/`rdOk`, `WeakAxiomatic.lean:122-130`);
no axiom joins the bytes of one label (N10).  TsoMem reads every byte of a load at ONE `tvn` (`Lang.lean:363-367`).
Counterexample: whole-word stores `S1@4`, `S2@6`; a floor-0 load with `ts = [4,4,6,6]` is admissible and
sRVWMO-consistent; TsoMem yields all-`S1` or all-`S2`.  RMWs are exempt (`rmwLatest`, `WeakAxiomatic.lean:134`);
fetches are NOT per byte any more — the cut form (§B(4)(iii)) is their SCA.  The ISA guarantees single-copy
atomicity for naturally aligned accesses ≤ XLEN, so the premise is ISA-faithful — NAMED as **`candSca c`**: every
`LLoad` reads its bytes at one view — `∃ tvn, ∀ j, ts[j]` is the latest write to byte `j` at or below `tvn` or the
hart's own later store (TsoMem's forwarding clause).  Carried by W5b; row "plain load" of W2's table is (↓) iff
`candSca`; alternative = an atomicity axiom in sRVWMO (re-opens T1, XL) — D20.  **At Stage 2 `candSca` is DERIVED,
not assumed** [R4.4]: the graph model has ONE gmo position per LOAD EVENT — `gloadValue`
(`Weak/WeakRvwmoGraph.lean:238-243`) requires each byte's source to be `gvisible G w e` (`:236`) and co-MAXIMAL
among the visible same-byte writes, so a torn read of two whole-word stores is already inconsistent; `topoSupply`
linearizes the NORMALIZED `GD'` and `linCand` (`WeakRvwmoLin.lean:471`) copies labels, so every realized `LLoad`
reads at its event's position: `linCandSca : rvwmoMinusConsistent G' → grule14 G' → candSca (linCand G')` (S, W11)
feeds W5b's shaped replay; for fetches `fetchCutPrefix` (W5d-G) plays the same role.
*(↑) receptiveness is NOT available on route (M)* [R2.3(iv)]: weak-side `Reducible` would need the weak WP package;
(a) is stated for the realizing MachCSL run, the free weak-side sentence is "the realized pf run never enters the
retry arm" (D15).  *Single era* [R2.2]: `epowerFork` forks no power thread (`Weak/WeakEvLang.lean:201-204`), so
multi-era conclusions are NOT transported; W4's run is prefixed by the `PowerOn` step (D14).
*The relation `R`* [R2.s3][R3.s3][R3.4], fixed in the spike report: TsoMem `tv ↔ max wVrNew (own last store)` —
**the `.aq` off-by-one** [R3.s3]: at an acquire pair TsoMem's `tv` becomes the WRITE's timestamp `top + 1`
(`MachCSL/Lang.lean:150`), WeakMem's `wVrNew` the READ's (`exloadPostRunD`, `Weak/WeakMem.lean:834`; `:634-647`);
`rv ↔ wVrOld`, `ownPub ↔ wVwOld`, `coh ↔ wCoh`, histories = log projection (`Lang.lean:147-153` ↔ `σ.wglog`), image
`imgZ ↔ imgFlat`, `resv ↔ wRes` only mid-pair, `itv`: the pf machine has none, so `R` carries "the MachCSL `itv` is
below every fetch's cut `q`" (`itv ≤ q`, W3 / W5d) [R6.4b]; the load row carries `candSca`'s `tvn`.  Spot checks
(↓): `fencePost` raises `wVrNew` to `max wVrOld wVwOld` for `pr,pw` (`WeakMem.lean:674-678`); `fence rw,rw`/`r,r`/
`rw,w` agree.  Open per label: parked `fence rw,w`/`wRelp` (`:684`) vs TsoMem's no-op; `wRes := none` at any
non-trivial fence (`:688`) vs TsoMem keeping it; the `.aq` carried bit (`MachCSL/TsoMem.lean:255-280`); the i-fetch
agent vs `LIFetch`; devices/DMA (`Efab` vs `MState.devrt`; `anyReserve`).  Size: L (↓) + L (W4) + M (W5b) + M (W5)
+ M–L (W5c) + L (W5d).  It lifts the WHOLE system theorem; (9d) reuses it in both directions, and **the log
identification is what carries `protReg` and `¬ badSeg`** (W11) [R4.3].

**(11) Model fidelity and named assumptions (trusted base, list in the header)** [R1.1][R1.7][R2.4][R3.1][R3.2]
[R3.4][R4.2][R4.4][R6.1][R6.2][R6.3].  Candidate/conformance premises: `execProgOk'S` (fused exclusive pairs — "a
dangling LR or failing SC is outside the theorem", D19; M1 only: `candKfetch`, D21); `candSca` (ISA-faithful; **M1/M2
ONLY** — derived at Stage 2, D20); cut-form Zifencei admissibility of pf fetches (M2); **the published model is the
TAGGED cat transcription** `rvwmoCatConsistentT` + the tagged conformance text `gdexecQconfT` (NEW trusted-surface
text; the untagged model's rule 12 is a strengthening of riscv.cat the tree marks UNSOUND — D33); **the graph-tier
fetch model** (W5d-G `gzFetch`/`emZifencei`, readings (H1)–(H3), §B(4)(iii) — NO reference model, RVWMO has no
instruction-fetch model; D27 RULED (a) [OWN.6]); **the graph-tier I/O-order PLATFORM assumption** (W13
`ioObAcyclic`: riscv.cat's gmo extended with xv6's MMIO accesses as I/O events is acyclic — each I/O event ordered in
PROGRAM ORDER against its own hart's memory accesses (strongly-ordered I/O), I/O events by the fabric; no reference
model; [OWN.8-conflict], D32).  **A PLATFORM assumption, not an RVWMO guarantee** [R6.3ii]: the image has 4 bare
`fence` (iorw,iorw) words, all in virtio (`Xv6/KernelImage.lean:17300-17450`), `fence rw,w` ×2 (`:2361,2825`), `fence
r,rw` ×1 (`:2747`), `fence.i` ×1 (`:17614`), so xv6's UART and PLIC paths are NOT fence-ordered under RVWMO's text;
`LFence` has no i/o bits (`WeakAxiomatic.lean:90`), so a fence-discipline variant cannot even be stated at the graph
tier — name QEMU virt / PMA strong ordering (D37).  **Trusted USES of it** [R6.s4]: unlocked cross-hart PLIC
claim/complete and `plicinithart` are real fabric races covered only by the strong-ordering arm of (T) — list each
site in the header.  **User-row gaps under [OWN.3]** [R6.2]: rule 7 RCpc (D35) and forwarded plain `LLoad aq` (D36),
both vacuous for kernel rows.  Strengthenings carried INTERNALLY by TsoMem/sRVWMO (not in the published statement
once (9d) lands): "stores never early"; reservation serialisation.  Machine-model choices: exactly 8 harts booted;
Svadu A/D write-back as a plain view-neutral LR/SC; DMA as a store-order agent; TsoMem's instruction-fetch model
(`MachCSL/TsoMem.lean:34-39`, `Lang.lean:360-362,155-163`) — beyond RVWMO's text (Zifencei); the SC-failure model
(`Xv6/UserMemLrsc.lean:7-12`; D17); single era.  Fidelity: the cat transcription omits rules 6, 7-RCpc, 8 (sound
direction for THOSE), litmus-checked only; the published quantifier IS cat (tagged) — D25 (a) RULED [OWN.5] and
spike-CONFIRMED, W12 on the critical path, no RVWMO⁻ fallback; Sail fork `070832a1` with `-D SYMBOLIC`; the image
dump.  Keep, list.
**(12) Audit coverage and file layout** [R1.10].  `Xv6/` never imports `Weak/`; lake libraries `MachCSL`, `Xv6`,
`Weak` (`lakefile.toml:2,27-41`).  Composition files live in `Weak/`, registered in `tools/ci/roots-weak.txt` +
`tools/audit/baseline-weak.json` + `XV6_AUDIT_MODULES` (`tools/ci/audit.sh:44`), built by `--weak` CI, whose cone
includes the whole `Xv6` adequacy cone (D13).  Pure-`Xv6/` items (W3, W8) go to `roots.txt`/`baseline.json`
(`tools/ci/lint.sh` checks the two agree).  S.

## C. Roadmap

Each stage ends in a theorem; "∥" = parallel (one Opus worker, one file each).  Stages 0–1b are INTERNAL
milestones on the critical path of the target; Stage 2 is the target [OWN.2].

**Stage 0 — W3 (SERIAL on the adequacy files) → W2 spike, ∥ W1, W5b, W5c; the three spikes are DONE** [R2.s4]
[R4.2][R5.1][R6.4a].
- **W3 `Xv6/TextPristine.lean` + sibling root `Xv6.xv6TextAdequacy_closed` (`Xv6/LinkTextAdequacy.lean`)** (M–L,
  SERIAL) [R1.8][R2.1][R3.1][R5.2][OWN.9].  NOT "no store targets text" (no per-STEP fact is exported; an
  identical-value store is harmless): a per-STATE predicate pulled through the hook (`powerInterp_mmOk`,
  `MachCSL/Adequacy.lean:481` → `xv6TraceHook`, `Xv6/SystemSlot.lean:590-612` → `xv6TracePure`'s `g.pow = true → mmOk
  g.m`, `:135-136` → the root).  `textPristine g` := every byte of `[bcRoLo, bcRoHi)` has history `[⟨0, _, img a⟩]`
  — equivalently `g.m.mem.readBytes (ifetchAgent cpu) tvn …` returns the image bytes at EVERY `tvn`
  (`MachCSL/Wp.lean:1478,1490`; `Lang.lean:360-362`) — from `kernelText`'s `□` singleton histories (§B(4)).  Files: a
  `powerInterp_textPristine` twin; `□ kernelText` made reachable at the hook (today it sees only `powerInterp` and
  `▷ xv6Slot`, `SystemSlot.lean:308` — stash it in the slot or thread it from the carve, `BootCarve.lean:582`) via a
  hook twin; the SIBLING root with `xv6FsAdequacy_closed`'s three boot hypotheses
  (`Xv6/LinkSystemAdequacyClosed.lean:20-26`) concluding `textPristine g2`.  **Acceptance** [R6.5c]: a NEW line in
  `roots.txt` AND `baseline.json` (`tools/ci/lint.sh` checks they agree), every existing root statement and baseline
  entry UNTOUCHED [OWN.9]; the root DOES enter the trusted-base report — run `tools/ci/tcb.sh --update` and commit
  the `tools/tcb/expected.json` diff (its axiom set must equal `xv6FsAdequacy_closed`'s; a new opaque is a STOP).
  Discharges W4's `LIFetch` row under `candKfetch` (M1) and the kernel-text half of `gzFetch`/the cut form (M2).
  Deps: none; the only Stage-0 item on shared files.
- **W1 `Xv6/AllocprocTrace.lean`** (S–M, re-scoped [R3.s1]; D23).  `xv6NiAdequacy` (`Xv6/LinkNiAdequacy.lean:82-90`)
  has the SAME three boot hypotheses (`g.gen = 0`, `g.pow = false`, `diskOf g.m.devs = fsImgDisk`) as
  `xv6FsAdequacy_closed` and concludes `xv6NiPhi g2 κs` = `∃ F, niOk ∧ … ∧ ∀ q, NiClassLaw q (utrace q h F)`
  (`Xv6/NiAdequacy.lean:92`), whose `NiClassLaw` (`Xv6/NiTrace.lean:660`, via `Xv6/NiLedger.lean:319-322`) contains
  `niRoundLaw`'s fork row (`:646`): the enter's `a0 = usysForkAns ι` = `if forkOk ι then signExtend (pidPick PIDMAX
  ι.pev) else -1` (`Xv6/UsysDet.lean:293-302`) at the CITED prefix — tie β (D11).  **Theorem shape (the finish
  line)** [R6.5d]: `allocprocTrace : ∀ g … (the three boot hypotheses) n κs t2 g2, ([Expr.power], g) -<κs>->ₜₚ^[n]
  (t2, g2) → ∃ F, ∀ q, ∀ s ∈ utrace q κs F, s is a fork round → s.a0 = usysForkAns ι_s ∧ (forkOk ι_s → 1 ≤ pidPick
  PIDMAX ι_s.pev ≤ PIDMAX)` plus `poolEmpty` at every `KNull` (`Xv6/KallocEv.lean:72`).  **[R6.5d-alt]** the pid bound
  is NOT an existing lemma — `PidEv.lean:136` is `pidPick`'s DEFINITION (`cycAt pidmax (nextOf pidmax h) i`); the
  file has only `pidPick_spec :200`, `cycAt_zero :158`, `cycAt_period :179` — W1 PROVES `pidPick_range` from `cycAt`'s
  codomain (S) and the `nextOf` tie (`PidEv.lean:77`).  Today's ledgers export no page address (`Kev`,
  `KallocEv.lean:45-52`) and no slot index (`Pev`, `PidEv.lean:50-55`); `liveOf` is a set.
- **W1b (owner-gated, L, serial)**: `pidHistWf h` in `pidLedger` (live pids distinct by induction), re-thread
  `ProofAllocproc`/`ProofFreeproc`/`NiLedger`; optionally addresses in `Kev` for page disjointness.  D10.
- **W2 `Weak/TsoOfPf.lean`** (L; spike first, ≤ 200 lines, risk report) [R1.11][R2.3][R2.s3][R3.4][R3.s3][R6.4b].
  `pfStepTso`: for every memory label (one row per exclusive half, plain load, fetch), a `wpPfStep` from an
  `R`-related state under `pairAdjacent` + `execProgOk'S`'s shape (W5b's statements, HYPOTHESES here [R5.3]) +
  `candSca` is a TsoMem step with the same bytes, to a related state; the `LIFetch` row reads at `tvn := q` with
  `R`'s `itv ≤ q`.  Report: per-label (↓) table; fence spot checks; `R` fixed with the `.aq` off-by-one; (↑) NOT
  CLAIMED; the log identification in the vocabulary W8/W11 need (author, class, position, per-byte history)
  [R4.s3].  Deps: W3's statement; W5b's two statements (day one).  **STOP rule** (D7): a WeakMem behaviour TsoMem
  lacks on a SHAPED run → STOP, report; suspects: parked release fence, fence-clears-reservation, tearing, `.aq`
  off-by-one [R3.s5].
- **W5b `Weak/PfRunShape.lean`** (M) [R2.3(iii)][R3.2][R3.4][R5.3][R6.4c].  **Day one: DEFINE `execProgOk'S`
  (§B(10)'s three clauses, over the step list; the admin-only step shape of W13 (I) as a parameter so `execProgOkA`
  reuses the clauses) and `pairAdjacent`; hand both statements to W2 and W5c.**  Then `execPrefixPfRunProgShaped`:
  the replay variant that consumes `execProgOk'S`, PROVES `pairAdjacent` (from `execProgOk'`'s right arm) and carries
  it, the fetch cuts and `candSca`'s per-load `tvn` along the run — a new theorem in `Weak/`, not a change to
  `WeakAxRealize`.  Deps: none.
- **W5c `Weak/SrvwmoXv6Witness.lean`** (M–L, re-specified [R3.3]; D22).  Non-vacuity: M1's premise set is
  SATISFIABLE.  The `sw &started` block does NOT witness it: M1 fixes `pst 0 = epsInit σ0` (pc at `_entry`;
  `WeakEvCapstone.lean:1026-1027`, `WeakLang.lean:488`), while the existing witness sits at the MID-instruction node
  `WeakEvStarted.evX2` with an EMPTY administrative run (`Weak/WeakRvwmoConfWit.lean:11-22`; `smC`/
  `smSnocConsistent`, `Cert.lean:522-546`), and `started = 1` is the LAST store of the boot (`Xv6/SpecMain.lean:6-15`)
  — a whole-boot replay.  The block is `_entry`'s FIRST memory instruction, `ld sp,1000(sp)` at `0x80000004`
  (`Xv6/KernelImage.lean:14-17`; GOT word at `0x8000a3e8`, image bytes, `t = 0`): hart 0 alone, pinned fetches in
  kernel text (`candKfetch` ✓), the administrative run by kernel evaluation (`esil`, `Weak/WeakEvLift.lean:897`;
  `pevrunAdmRun`, `Weak/WeakRvwmoCert2.lean:180` — the `esil → admRun` bridge `Weak/WeakRvwmoConfWit2.lean:26-28`
  records as THE missing mechanism), consistency from `gtraceSnocReadImage` (`Weak/WeakRvwmoFloor.lean:1025-1035`)
  or `snocRdAdm` (`Cert.lean:257`), a concrete `σ0` with `wbootFacts` (`MachCSL/BootRun.lean`), `candSca` trivially,
  and the S-variant of `execProgOk'Snoc` (W5b's statement).  Certifies satisfiability — NOT that any candidate
  reaches `allocproc` — and it is QUIESCENT (no `LDev`): it certifies NOTHING about W13's fabric bundle, whose
  witness is W13-wit [R5.s3].  Deps: W5b's predicate.
- **W12-spike — DONE** (`Weak/CatOfMinusSpike.lean`, 399 lines, no `sorry`; `notes/W12-spike.md`) [OWN.5][R6.1]
  [R6.2].  Route (a) SOUND for the kill; gates 1–2 CLOSED by hypothesis changes alone; **W12 = M–L ≈ 1.2–1.8k**.
  Found (F1) the quantifier must be the TAGGED model (§A(3)); (F2) a THIRD gate, the walk floor (W12b).  Witnesses
  need no re-proof (`catADOfMinus`; corrects [R5.s1]).  W12-Q1..Q4 = D33–D36.
- **W13-spike — DONE** (`Weak/W13Spike.lean`, 145 lines, no `sorry`/axiom; `notes/W13-spike.md`) [R5.1][OWN.8]
  [R6.3].  Vacuity CONFIRMED; **T2-1c′ already LANDED** (`gtraceLinearizationMin`, `Lin2.lean:623`; `ptraceExistsF
  :836`; `trDevOrderedOfPtrace :944` DISCHARGES FabInd's handed-back guard; `fconfSupply' :995`; `fconfTraceRealize
  :1012`); **the literal [OWN.8] axiom is REFUTED** (`lbExcluded`), `gdevAdj ⊆ gmo` excludes SC (`scDevExcluded`);
  `ioObAcyclic` applied provisionally (D32); **W13 = XL** in six pieces.  Q-W13a..d = D32, D37, D38, D39.
- **W5d-G-spike — DONE** (`../xv6iris-weak-w3/Weak/GraphFetchSpike.lean`, 226 lines, `propext, Quot.sound`;
  `…-w3/notes/W5dG-spike.md`) [OWN.6][R6.4b].  Fetch stays ADMINISTRATIVE; relational `gzFetch` + fetch fragment as
  graph data (§B(4)(iii)); **W5d-G = L ≈ 1.8–2.2k + XL risk R1**; W5d's M2 clause fixed to the cut form NOW.  Q-G1..G4
  = D40–D43.

**Stage 1 — M1, the composed sRVWMO theorem, pinned/kernel-only (internal).**
- **W4 `Weak/MachOfPf.lean`** (L) [R2.1][R2.2][R2.3][R3.1].  `machRunOfPfRun`: a shaped `rtc (wpPfRun pstepEv
  pclsEv)` run from `wpInit (imgZ bootImage) (efInit ds.reset) (epsInit σ0)`, PREFIXED by `PowerOn`, is a
  `-<κs>->ₜₚ^[n]` MachCSL run, same hart expressions and observations, devices aligned; the `LIFetch` row UNDER
  `candKfetch` (M1) / the cut form (M2).  Deps: W2, W3.
- **W5 `Weak/SrvwmoXv6Adequacy.lean`** (M) [R1.5][R2.1][R3.1][R3.s2].  **M1**: from `wbootFacts σ0`, the disk,
  `srvwmoConsistent c`, `execProgOk'S (pstepPin …)` with `candKfetch` + `candSca` — T1 + `execWfPfRunProg` +
  `wpPfRunPinSub` + W5b give the shaped run; W4 projects; `xv6FsAdequacy_closed`, `xv6NiAdequacy`,
  `unionAdequacyClosed` (`Xv6/LinkUInitUnion.lean:163-164`) and W1 conclude.  Header: internal milestone,
  kernel-only by PREMISE.  `roots-weak.txt`/`baseline-weak.json`/`XV6_AUDIT_MODULES`.  Deps: W1, W4, W5b; W5c (D22).

**Stage 1b — M2, the fork path on the pf side (part of the target [OWN.3]).**
- **W5d `Weak/PfRunUnpinned.lean`** (L) [R2.1-alt][R3.1][OWN.3][R4.2][R6.4b].  The pf half ONLY: `execWfPfRunProgF`
  (replay at `pstepEv` with the CUT-form clause `∃ q, itv ≤ q ≤ |log| ∧ ifetchOk img log q base tvs` replacing
  `fetchPin`), W4's `LIFetch` row for user text at `tvn := q`, W5 restated — the first form in which `fork → ecall →
  sys_fork → allocproc` under contended `p->lock` from 7 scheduling harts is a candidate.  The user-fetch witness =
  whole-boot replay; not scheduled (D18).  The graph half is W5d-G (Stage 2).  Deps: W5.

**Stage 2 — THE TARGET: T-alloc-RVWMO via graph-tier robustness re-sourced from TsoMem (route 9d; XL).**
- **W12 `Weak/CatLin*.lean`** (M–L ≈ 1.2–1.8k, spike-sized; D25 RULED (a) [OWN.5]) [R6.1iii] — the spike's design:
  (1) core predicate `rvwmoCoreD GD := gwf ∧ gloadValue ∧ gatomicity ∧ gdepsWf`; restate `topoLinearizes`' section
  variable, `topoExists`, `racyDMem`, `normalizeOfAcyclic(')`, `topoSupply`, `hullRealizable*`, `hullRun`,
  `topoLinearizesF` over it (statement edits, S); (2) kill definitions from the scratch's §0–§3 — `rvwmoCatAD GD ad`
  (cat's six arms, lv, atomicity, deps, rule 12 over `ad ⊆ gdDeps`; entries `catADOfCatT` on `forget GT` with `ad :=
  gtAd`, `catADOfCat`, `catADOfMinus`), `rsameC`/`gcrossE`, `segPinC` as a same-hart CHAIN of `pinStep`s with the
  rule-12 forward case `segPinCForward` (why `ad` must be TAGGED), `CertC`/`chainC`/`cycleKillArmsC`, the lock kit
  `*C`, Glue §1 re-instantiated (`rawChainC`, `crunC`, `cycleSegmentsC`) (S–M);
  (3) **`hullCatAD`**: the hull of a `rvwmoCatAD GD ad` graph is `rvwmoCatAD (gdHull GD cs) (ad.filter cut)`, via
  `rowsRelGppoCat6` (rule 2's `t1 ≠ t2`, rule 3/12's `grfAt` through an injective `hren`; risk: injectivity on the
  cut's sources, believed true via `hrenWix`, not built) — the one real proof (M); (4) restated chain `cycleKillC`,
  `t2linAuxC`, `t2linOfCycleKillC`, `t2linSupplyC`, `l2ClaimAtC` (`segPinC ∨ csHyps[gcrossE] ∨ Bad`),
  `rawChainChainC`, `cutSupplyC`/`certSupplyC`/`walkSupplyC`/`walkPolicyC`, `cycleKillOfL2C`, `t2linOfL2'''C` (S–M);
  (5) published capstone `xv6RvwmoSafeModuloT : ∀ GT : GdexecT, rvwmoCatConsistentT GT → gdexecQconfT boot d0 im nh
  GT → (∀ x, ¬ tc (racyD (forget GT)) x x) ∧ …` by `catADOfCatT` into the C-chain; `gdexecQconfT → gdexecQconf
  (forget GT)` from `rowDepsSubT` (S–M); (6) non-vacuity: existing witnesses via `catADOfMinus`; **acceptance gate
  [R6.s2]: ONE forwarding witness (SB+rfi-pos; `AxGraphCat`'s `epc`/`isw` are candidates) through `rvwmoCatAD`,
  cat-consistent but NOT RVWMO⁻** — the first machine-checked evidence the published quantifier admits a forwarding
  execution RVWMO⁻ rejects.  `WeakRvwmoLin*`/`Norm`/`PreNorm` untouched.  The cat arms are written ONCE against W13
  (K)'s `tc (ioOrd GF)` — fix (K)'s statement first, or parameterize the cross order.
- **W12b `Weak/CatFloor*.lean`** (M–L ≈ 0.5–1k; NEW [R6.2]; D34 (a)).  Gate 3: Floor §4–§6 and Cert3 §2–§3 re-done
  on a per-byte coherence invariant through rules 1/2 in place of `gvisUb`; `greadSrcUb`, `finvStep`, `cinvReplay`/
  `floorOfCgraph`/`certFloorOk`/`cpolRead` over `rvwmoCatAD`; the `wVRel` hook per D35, forwarded `LLoad aq` per D36.
  Scheduled WITH W12 and BEFORE W10 (else W10 → L and absorbs it).
- **W5d-G `Weak/GraphFetch*.lean`** (L ≈ 1.8–2.2k + XL risk R1; D27 RULED (a) [OWN.6]) [R4.2][R6.4b] — the spike's
  change list: **G1** `gzContrib`, `emFenceI` + `emFenceISound`, `emZifencei` in `xv6ConfS`/`gdexecQconf` replacing
  `emFetchImg` (`WeakRvwmoSupply.lean:277-352`, `emFetchImgRen/Prefix` → retime/hull versions; `Fab.lean:516-522`;
  `WeakEvInst`/`WeakEvLang` lemma only) (M ≈ 350); **G2** tags = gmo indices — `wlblRen` renames `LIFetch` tags
  (reverts Q-C4, `WeakRvwmoConf.lean:57-66,147`), `pstepEvWren`/`projLblWren` `LIFetch` arms, M1 pin kept via `π 0 =
  0` (S ≈ 100); **G3** fetch fragment as data — `Gdexec.gdFetch`, `racyD` disjunct, `racyDSplit` arm (cross-hart →
  `gcross`), `gdHull` filter, `retime` keeps it, ~31 literal sites (`WeakRvwmoGraph.lean:613`, `Acyc.lean:200`,
  `Glue.lean:205-223`, `Hull.lean:714`, `Topo.lean:120-129,594-607`) (M ≈ 300); **G4** `retimeZifencei` + contributor
  invariance + `gwlog`/`gwix` bridge (Topo, new section; L ≈ 600); **G5** `linPrefixLog`, the floor bound,
  `supplyOfQconf` producing the M2 cut clause (`Lin`, `Floor`, `Supply.lean:743-883`; M–L ≈ 500); **G6** re-thread
  `pstepPin` → `execProgOk'S` (the 19-file list in §B(10); ONE pass with W11 (iii)); **G7** kill arms for cycles
  through E1/E2/E3 ("fetch-entry segments", pinned only by `fence.i`; W8 vocabulary: user-text page ownership,
  exec/fork → `p->lock` → `userret` `fence.i`) — L, in W11/W8.  Witness files with literal fetch items
  (`WeakRvwmoConfWit2` `ldEmFetchImg`/`evEmFetchImg`, `WeakRvwmoAdm`) need only "the pin implies `gzFetch`".  Hull
  closure per §B(4)(iii) R1 (a).  Non-vacuity gate: the user-fetch witness (D18) — W13-wit comes first (without the
  disk row `exec("/init")` never completes).
- **W13 `Weak/GraphFab*.lean`** (**XL**, spike-sized, six pieces; was L–XL) [R5.1][R6.3iii][OWN.8-conflict].
  **(T)** `Ioev`/`ioOrd`/`ioObAcyclic` + header text (S; DONE in the scratch, 60 lines — move to a merged file).
  **(I)** `execProgOkA`: the trace is over `Option Estep`-style items; an admin-only step for hart `i` runs only
  `admStar` and MAY move the fabric; its T1 lift beside `execWfPfRunProg`/`xv6SrvwmoSafe` (new files); `gfexecConfA`
  keys dev blocks by `(i, k)` (the `.dv` nodes), reuses `hemitf` — co-designed with W5b's `execProgOk'S` (L; D38).
  **(L)** T2-1c″: generalize `gtraceLinearizationMin` to traces over events ∪ dev positions extending `po ∪ rf ∪
  gmo'|W ∪ ioOrd|dv`; dev items are no-ops for the cand; existence by `normalizeOfAcyclic` on `L* := topo(racyD ∪
  iopo ∪ dev)` restricted to `gmem` (every po-run in a cycle ends at a write, `gpow ⊆ racyD`, or a dev node, `iopo`)
  (M–L).  **(K)** the kill extended: cycles of `racyD ∪ iopo ∪ dev`; dev edges a new CROSS kind, `iopo` a new
  SAME-HART arm (po-increasing, `rsameAcyclic` survives); KillArms' chain composes in `tc (ioOrd GF)` with `gmo`
  inside it and the dev/`iopo` arms from (T) → `cycleKillA`, threaded through `hullRun`, W11, W12 (M–L).  **(R)** the
  re-thread of the constant-fabric chain onto `gfexecConfA` (sibling `*A` files): measured 8.6k lines / 14 files /
  ≈ 140 bundle mentions / 52 `fun _ => d0` sites (Supply, LinInd, Cert4, Glue, Glue2, Walk/Walk2/Walkb/Walk3,
  Progress, PreNorm/PreNorm2, Capstone); dev-free segments reuse the constant-fabric lemmas through a `hemitf`
  dev-free reindex; witness files embed via `gfexecConfOfQconf`; KillArms, Hull, Lin unchanged except the new arms
  (L–XL, the bulk).  **(W)** `xv6ConfS` on `gfexecConfA` + **W13-wit** (M–L): the `LDev` non-vacuity witness — hart
  0's run `_entry → … → uartinitone` (entry `0x80000896`, `Xv6/KernelImage.lean:1515`; the `jal` at `:1590`) to **its
  first UART store, `sb zero,1(a5)` at `0x800008a0` (`:1525`, IER := 0)** [R6.5b]; ≈ 100 dynamic instructions, NO
  MMIO before it (`timerinit` is Sstc CSR-only, `Xv6/SpecTimerinit.lean:5-7`), by kernel evaluation as in W5c — the
  first candidate with a non-empty `gfDev` (D31).  Risks: R2 (I) changes the T1 interface (every `execProgOk'`
  consumer gets a sibling); R4 dev nodes adjacent to fences/non-`gmem` events (`gwf`, `WeakRvwmoGraph.lean:171`).
  Deps: W5c's `esil → admRun` bridge; W5b's shape clauses.
- **W8 `Xv6/AccessDiscipline.lean`** (L–XL; D24) [R4.3][R4.s3][R4.s4].  Export from the SC tree, per reachable
  MachCSL state (the `mmOk` idiom) on `MState`'s author log + per-byte histories (`MachCSL/Lang.lean:147-153`), in
  the vocabulary `protReg`/`badSeg` consume: (i) bytes a hart OWNS — no foreign writer (covers `PStack`/`PPerCpu`,
  the 58 `own = true` witnesses; `gen_weak_pins.py --check` as the audit); (ii) a protected access under a held lock
  (`wprotAt`/`wlpAt`/`wlpAlt`, `Weak/WeakGhost.lean:1040,543,699`; `lockWordByte`, `KillArms.lean:340`); (iii) no
  hart's floor reaches a FOREIGN owned-unpublished message (`wmAk = .WCplain`, `WeakRobustMain.lean:390-395`; `¬
  wpublished :399-400`; `Weak/WeakViolation.lean:9-15`) — HART authors only, DMA exempt, mirroring `violationHart`
  (`WeakRobust.lean:100-107`); (iv) ALL 182 `PCall`/`PResidue` sites and the 58 sp-frame witnesses classified into
  (i)–(iii) for the PUBLISHED theorem (W9b; D28 RULED (a) [OWN.7]); (v) user-text page ownership for W5d-G's G7
  (exec/fork → `p->lock` → `userret` `fence.i`).  Needs a ledger threaded through the MachCSL memory rules — mechanical
  but wide; the ownership residue is ~5 idioms (`swtch` reloads, trapframe loads off `a0`, user-table walks,
  boot-published globals).  Exports must hold on FORWARDING graphs (TsoMem forwards — fine).  **Design gate: the W2
  report** (the three spike reports are IN) [R4.s5][R6.4a].
- **W9a `Weak/WeakRvwmoPinBridge3.lean`** (L = M–L + M [R6.1]) [R4.1].  R-3: a `pstepEv` run's items are grouped per
  instruction as the checker's pc walk assumes (`reaches`/`psites`, `PinBridge2.lean`; §8 has both halves on one
  computed stretch) → `pinSegPin'` applies at every certifying site of the REAL run, targeting `segPinC`
  (`pinStepOfSegPinArm`; PDep entries across an rfi via `segPinCForward`); with W8 (W9b) → `l2ClaimAtC`'s `segPinC ∨
  csHyps` arms for xv6.  No generator work: `KernelPins.lean`/`imagePinnedb`/`pinsCover` exist.
- **W10** (M–L, **unverified**; L if it absorbs W12b): `wsegSupply`/`walkPolicy` for xv6 graphs on the W12b floor kit.
- **W11 `Weak/RvwmoXv6Adequacy.lean`** (L) [R4.3][R4.4].  (i) **The `Bad` arm is LOG-LEVEL**: today `l2ClaimAt GD P
  Bad` (`Glue.lean:440-447`) hands the prover `(GD, log, logOf, protReg)` while the capstone sets `Bad := badRun gen
  σ0 = ∃ ρ, rtc epfRun … ∧ violationHart …` (`:384-385`) — a RUN-LEVEL existential refuted by `noBadRun` (`:387-391`)
  over ALL `epfRun`-reachable configurations, which route (M) cannot reach; `rawChainChain` consumes `¬ Bad` globally
  (`:453-460`).  Define `badSeg GD log prev s` := the entry's source message is owned (`wmAk = .WCplain`) and
  unpublished at `log` by a FOREIGN hart author; restate `l2ClaimAt` with it; prove `¬ badSeg` at the certified run
  from W8 (iii) through W4 (the realized hull run is a prefix of the realizing TsoMem run); derive the global `¬ Bad`.
  (ii) `protReg P log` (`:364-368`) is a fold over the LOG — transfers through `R`'s log identification once W8
  exports (ii) (D24).  (iii) re-thread `execProgOk'S` through `RunData`, `cstOk`, `segStep`, `topoSupply`,
  `t2linSupply` — one pass with W5d-G G6.  (iv) `linCandSca` (S) [R4.4].  (v) Restate `cycleKillOfL2''`
  (`Glue2.lean:521`), `t2linOfL2'''` (`Walk3.lean:77`), `xv6RvwmoSafeModuloT` (W12) with W8-sourced facts in place of
  `wpPackage`/`wpPackageProt`/`noBadRun`/`protRegOfRun`/`efetchItvOk`; compose with M2, W5d-G and W13 (the A-bundle,
  `ioObAcyclic`, T2-1c″'s supply, `cycleKillA`): **T-alloc-RVWMO**.  Header per §B(11).
- *Not on the path:* **W6** PSO machine (L–XL; optional de-risk, D4); **W7-P** promise-machine fallback (D2').

**Stage 3 — AxSL tier: retired** [OWN.1].  One-paragraph note on Theorem 2 (D6).

**Launch now:** W3 first — SERIAL, the one Stage-0 item on shared files (`MachCSL/Adequacy.lean`,
`Xv6/SystemSlot.lean`, a new link file, `roots.txt`/`baseline.json`/`tcb/expected.json` additions) [R5.2][R6.5c] —
then W2 spike ∥ W1 ∥ W5b ∥ W5c; W5b's two statements on day one unblock W2 and W5c.  W1b waits for D10; W8 design
starts after the W2 report (its export shape depends on `R`; the spike inputs are IN) [R4.s5][R6.4a].  Stage 2
cannot start before D32–D39 are ruled (the published statement's shape depends on D32, D33, D38).

## D. Owner questions (recommended option first; RULED items kept for the record)

**NEW this revision — the published statement depends on D32/D33/D38; please rule first.**
- **D32 = Q-X / Q-W13a. [OWN.8-conflict]: the form of the dev-order trusted item** [R6.3][W13-spike].  The literal
  [OWN.8] axiom is refuted by `lbExcluded` (`Weak/W13Spike.lean:35`); `ioObAcyclic` is applied PROVISIONALLY in §A.
  Options (verbatim from the spike): (a) **`ioObAcyclic` (recommended)**; (b) [OWN.8]'s literal `po ∪ rf ∪ gmo|W ∪
  dev` acyclic on the quantified graph — this drops LB and W→W, contradicting [OWN.2], as `lbExcluded` shows; (c) the
  same, stated only on the internally normalized graph — it is not a statement about the input, so it cannot serve
  as a trusted base; (d) `gdevAdj ⊆ gmo` — it excludes SC executions (`scDevExcluded`).
- **D33 = Q-T / W12-Q1. The published model** [R6.1].  (a) **tagged `rvwmoCatConsistentT`, chain on `forget GT`
  (recommended; within [OWN.2]'s wording "rvwmoCatConsistent / the RVWMO axiomatic model in this tree")**; (b)
  untagged `rvwmoCatConsistent`, with "rule 12 also over ctrl/translation deps" NAMED as a strengthening of
  riscv.cat; (c) drop rule 12 from the published model — sound, but the kill loses `segPinCForward` and W9a must
  split PDep pins at every rfi.
- **D34 = Q-U / W12-Q3. Gate 3 ownership** [R6.2].  (a) **a new item W12b `Weak/CatFloor*.lean` (M–L), scheduled
  with W12 (recommended)**; (b) W10 absorbs it (W10 → L); (c) restrict the walk to kernel rows and defer the user-row
  aq/rl cases.
- **D35 = Q-V / W12-Q2. Rule 7.**  (a) **make `grcsc` riscv.cat-faithful: RCsc = any aq/rl on AMO/LR/SC; first check
  that the decoder emits `LStore rl`/`LLoad aq` only for atomics (recommended)**; (b) keep the weak rule 7 plus a
  conformance side condition "no rl-annotated write followed by an aq read" — vacuous for the kernel; (c) leave it,
  and carry the `Bad`-arm burden in user rows.
- **D36 = Q-W / W12-Q4. Forwarded `LLoad aq`.**  (a) **a row side condition "no plain `LLoad aq`" (true for the
  kernel) (recommended)**; (b) change WeakMem's `fwdView` for aq, which ripples into T1; (c) accept it as a named gap
  for user code.
- **D37 = Q-Y / Q-W13b. The platform assumption behind (T)** [R6.3ii].  (a) **accept it as part of (T) and name QEMU
  virt / strongly-ordered I/O in the header (recommended)**; (b) require fence-guarded MMIO — needs i/o bits in
  `LFence` and an xv6 code change, which leaves the `verified` branch; (c) restrict the claim to platforms with PMA
  strong ordering.
- **D38 = Q-Z / Q-W13c. The realization interface.**  (a) **admin-only trace steps `execProgOkA` (recommended;
  co-designed with W5b's `execProgOk'S`)**; (b) make MMIO a tagged inert-fence row event, in the style of the Q7
  sfence marker — changes `projLbl` and the emission proofs, which are merged files; (c) keep the folded model and
  prove representability for xv6 per MMIO site ("the carrier is hart-private", plus a `cycleKill` over dev cycles) —
  xv6-specific, fragile, and also XL.
- **D39 = Q-W13d. `xv6RvwmoSafeModuloF` / `gfexecConsistent'`.**  (a) **retire as a published form, keep as an
  internal lemma on normalized graphs (recommended; applied in §A)**; (b) keep it with a header warning.
- **D40 = Q-G1. `fence.i` identification** [W5d-G-spike].  (a) **the emission-structural `emFenceI` + soundness lemma
  (M) (recommended)**; (b) give `fence.i` or the Q7 marker distinct fence bits — `(f,f,f,t)` changes only `wRes`, but
  it perturbs Q7 and the AxSL pins; (c) a new `Wlabel` — XL.
- **D41 = Q-G2. The contributor set.**  (a) **the superset "everything the hart wrote or read before `fence.i`"
  (recommended) — simple to audit and retime-invariant, but its trusted reading is stronger: (H2) covers plain
  loads**; (b) the exact `itvPost` set (aq reads, `pr∧sr`-fenced reads, address views, own stores) — spec-minimal and
  equal to TsoMem's, but needs a symbolic view fold: +M.
- **D42 = Q-G3. Where the fetch fragment `F` lives.**  (a) **a `Gdexec.gdFetch` field, mirroring `gdDeps`, so hull,
  retime and acyclicity carry it for free (recommended)**; (b) a parameter of `racyD`/`cycleKill` — the ~31
  constructor sites are untouched, but 16 files' statements change.
- **D43 = Q-G4. Pinned milestones.**  (a) **keep `pstepPin`/`fetchPin` as the M1 kernel-text instance
  (`fetchPinCutOk`) until M2 lands (recommended)**; (b) delete them after G6.
**Standing (recommendations provisional unless RULED).**
- **D1 / D2 / D12** — RULED [OWN.1][OWN.2][OWN.4]: machine tier (Theorem 2 = validation); FULL RVWMO (now the
  TAGGED cat model, D33), sRVWMO/pinned forms internal; the `verified` fork in the header.  **D2′.** If (9d) is
  judged too large: (Rec) hold publication; (b) the promising machine with "Promising-RISC-V ≡ RVWMO" in the trusted
  base — not cat, violates [OWN.2].
- **D3.** (Rec) trace-level predicate via `xv6NiPhi` beside the Iris contract; (b) contract only.  **D4. W6** — (Rec)
  SKIP; (b) de-risk for W8's export.  **D5. W3** — (Rec) launch first.  **D6. Theorem 2.**  (Rec) keep as the audited
  riscv.cat-tier validation; note S.  **D7. W2 failure mode** [R2.3][R3.s5] — (Rec) change `WeakMem`'s event instance
  to MachCSL's shape where the kernel proofs allow; (b) a MachCSL change (owner-gated, serial).  **D8.** (Rec)
  "exactly 8 harts, all booted" named; (b) a "≤ 8" variant (MachCSL change).  **D9. Panics.**  (Rec) not excluded,
  stated; (b) "no `panic:` bytes in the UART trace" (M–L; meaningful at the graph tier once W13 lands).  **D10.**
  (Rec) W1 via `xv6NiPhi` now; (b) also W1b (L, serial).  **D11.** (Rec) observation-level β; (b) state-level α.
  **D13.** (Rec) `Weak/`, `--weak` audit with the full `Xv6` cone; (b) separate lane.  **D14.** (Rec) one boot; (b)
  multi-era W4 (M).  **D15.** (Rec) conclusions about the realizing MachCSL run + "the pf run never spins in the retry
  arm"; (b) no weak-side sentence; (c) weak-side `Reducible` (XL).  **D16** → D22.  **D17.** (Rec) header names the
  SC-failure model; (b) §B(11) only.
- **D18** — RULED [OWN.3]: W5d (M2) and W5d-G in the target.  Residual: the user-fetch witness (whole-boot replay),
  W5d-G's gate — (Rec) not before Stage 2, after W13-wit; (b) after M2 (XL).  **D19.** (Rec) `execProgOk'S` (fused
  pairs) as a named premise; (b) a MachCSL change so dangling reservations do not block (serial, L, **unverified**);
  (c) a user-mode fact — unavailable.  **D20.** (Rec) `candSca` named at M1/M2 ONLY, derived at Stage 2; (b) an
  atomicity axiom in sRVWMO — XL.  **D21.** (Rec) report M1 as "composition milestone, kernel-only by premise
  `candKfetch`, loads single-copy-atomic by premise `candSca`"; (b) report nothing before M2.  **D22.** (Rec) the
  `_entry` first-load witness gates M1 (SATISFIABLE, not reaching `allocproc`; QUIESCENT); (b) follow-up.  **D23.**
  (Rec) W1 via `xv6NiPhi` (S–M); (b) the rev-3 ledger hook (M).  **D24. W8's export form.**  (Rec) a per-state
  predicate on `g.m` + a ghost access ledger exported like `mmOk`, in `protReg`/`badSeg`'s vocabulary; (b) a new `Obs`
  per access; (c) trace-free from W9a's check + ownership facts.
- **D25** — RULED [OWN.5], spike-CONFIRMED: (a) cat-sound kill arms (`rsameC`/`gcrossE`, lock kit `*C`,
  `normalizeOfAcyclic` over the core), M–L; (b) dropped; (c) NOT accepted.  **D26. Stage-2 sequencing** [R4.s5]
  [R6.3].  (Rec) M1 → M2 → W13 (T)(I) + W5b co-design → {W12 ∥ W12b ∥ W5d-G G1–G5 ∥ W13 (L)(K)} ∥ W8 (after W2) →
  W13 (R)(W) → W9a/W10 → W11; (b) start W8 with Stage 1 (risk: `R` not fixed).  **D27** — RULED [OWN.6], spike-SHAPED:
  (a) `gzFetch`, admin form, D40–D43.  **D28** — RULED [OWN.7]: all 182 + 58 sites through W8.
- **D29** [R5.1, Q-R] — RULED [OWN.8] as "dev-order model in the trusted base, T2-1c′ in scope"; **UPDATED by the
  spike** [R6.3]: T2-1c′ is LANDED (not "sizeable, to build"); the literal axiom is refuted → D32; `gdevAdj ⊆ gmo`
  rejected on new grounds (`scDevExcluded`, not only FabInd §5).  **D30** — RULED [OWN.9]: sibling root
  `xv6TextAdequacy_closed`; existing roots/baseline untouched; `tcb/expected.json` gains an entry [R6.5c].
  **D31. W13-wit timing.**  (Rec) build right after W5c lands (its `esil → admRun` bridge is the mechanism) as W13
  (W)'s gate — the only pre-Stage-2 evidence that a device-active candidate exists; end = the first UART `sb` at
  `0x800008a0`; (b) defer to Stage 2 with the user-fetch witness.

