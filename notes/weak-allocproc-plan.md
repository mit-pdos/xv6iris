# allocproc on RVWMO: target theorem, gap analysis, roadmap (design advisor, 2026-10-09)

**Status: rev 6 = rev 5 + review R5 (3 required changes, tags [R5.n]) + owner rulings [OWN.5–9]
(`allocproc_revise3_extra.txt`: D25 (a), D27 (a), D28 (a), Q-R dev-order model in the trusted base with T2-1c′
in scope, Q-S sibling root `xv6TextAdequacy_closed`); [OWN.1–4] kept (machine tier; FULL RVWMO is THE target;
W5d in the target; the `verified` fork).**
History: rev 1 (2026-10-09) survey; rev 2 `…-review-R1.md` (11 req.; D8–D13); rev 3 `…-R2.md` (5 req., two
[R2.n-alt]; D14–D19); rev 4 `…-R3.md` (4 req.; D20–D23) + [OWN.1–4] (D24–D26); rev 5 `…-R4.md` (5 req.; W9 on the
EXISTING pin checker, W5d split, `Bad` log-level, `candSca` derived; D25, D27, D28); rev 6 (2026-10-09) `…-R5.md`
(3 req., s1–s5): the quiescent graph bundle is VACUOUS for allocproc → W13 fabric-ordered bundle + T2-1c′ +
W13-spike; W3 restated as the text-pristine HISTORY export in a sibling root; `pairAdjacent` defined in §B(10);
history, inventories and RULED D-items compressed [R5.s2].

**The kernel [OWN.4][R1.9]: xv6-riscv `b72cbac1`, branch `verified`** (`notes/STATUS.md:8-11`, `README.md:89-90`)
= upstream plus (a) a per-process root (`p->root`, `sys_chroot`, `igetroot`, root-aware `dirlookup`/walk) and
(b) upstream's post-`ded23f2` allocpid — bounded counter `PIDMAX = 1000` (`Xv6/ProcGeom.lean:80`) with a 64-slot
liveness scan, inlined by gcc into `allocproc+0x38..+0x94` (`claude-notes/kernel-defects.md:224-231`) — not the
textbook monotone `nextpid`.  Image `Xv6/KernelImage.lean` by `tools/dump_kernel.py`.

Advisory only; read-only survey of `../xv6iris-weak` (`Weak/`, `Xv6/`, `MachCSL/`, `notes/weak-memory-*.md`,
`claude-notes/{completed,design}/*weak*`).  Sizes: S ≤ 300 lines, M ≤ 800, L ≤ 2k, XL = multi-week / many files.
Unconfirmed claims are **unverified**.

## 0. The two findings that reshape the question

**F1. allocproc is ALREADY fully verified in this tree — on a weak-memory machine, not on SC.**
`Xv6.Allocproc : ALLOCPROC` (`Xv6/LinkAllocproc.lean:14-16`, proof `Xv6/ProofAllocproc.lean:3623-3639`, 3.6k
lines; spec `Xv6/SpecAllocproc.lean:118` `allocprocPost`, `:204` `wp_allocproc_body`) covers the whole function
on the real image (`allocproc` = 0x80001b72..0x80001c72): the `proc[]` scan with `acquire`/`release` per slot
(interrupts may be ON; migrating hart via `wpNext`), the inlined allocpid under `pid_lock` with the 64-word
collision scan (Löb-closed outer loop, `PidLock.pidLedger`/`pidTie`, `Xv6/PidLock.lean:88,113`), `p->state =
USED`, `kalloc` (`Xv6/SpecKalloc.lean`), `proc_pagetable` → `uvmcreate`/`mappages`/`walk`/`kalloc` with PTE writes
into fresh OWNED pages (`Xv6/SpecProcPagetable.lean` `pptPost`), `memset` of the context, `ra = forkret`, `sp =
kstack + PGSIZE`, both failure tails through `freeproc`, `p->pid`/`p->state` as `p->lock`-protected cells
(`procHeld`).  Callees verified too (`Proof{Kalloc,ProcPagetable,Mappages,Walk,Uvmcreate,Memset,Freeproc,Acquire,
Release,Pushoff,Popoff,Mycpu}.lean`, ≈ 10.7k lines).  In the cone of the audited roots (`tools/ci/roots.txt:6`
`xv6FsAdequacy_closed`, via `Xv6/LinkSyscall.lean:84`/`LinkMain.lean:53`).

The memory model under all of that is `MachCSL.TsoMem` (`MachCSL/TsoMem.lean:1-40`; design
`claude-notes/completed/relaxed-rr.md`): one total store order with per-byte write histories, per-hart view
FLOORS (a plain load reads at any view ≥ floor: load–load reordering), store forwarding by author, store
buffering, `fencePost` (`:345`: W→R drains past the hart's own last store, R→R acquires past the read watermark;
`fence rw,w`/`w,w`/`r,w` are NO-OPS, `:356-364`), `.aq` AMOs, LR/SC reservations, a non-coherent i-cache view
`itv` + `fence.i`.  **What it forbids that RVWMO allows** [R1.7]: (i) store–store reordering and load buffering
(stores never early) — the weak tier's sRVWMO residue (rule 14; `Weak/WeakAxiomatic3.lean:2050-2071`; divergences
LB and reader-fence-only MP, `Weak/WeakSrvwmoLitmus.lean:1663-1695`), checked by reading, not by theorem — nothing
relates TsoMem to `srvwmoConsistent`, and §B(10) does not need it [R2.s2]; (ii) **reservation
serialisation**: a foreign store or exclusive read overlapping a held reservation is BLOCKED (`blockedStep`,
`MachCSL/Lang.lean:366-378,395-403`; DMA `anyReserve`, `:539,562`); the reservation persists until the holder's
next store of ANY address (`MState.store … resv := none`, `:147-153`) or a blocked exclusive read, surviving fences
(`:155-163`).  RVWMO's atomicity axiom constrains only SUCCESSFUL pairs; kernel code uses only `amoswap.w.aq`
(`Xv6/ProofAcquire.lean:5`), but USER code is in the theorem and may `lr`/`sc` (the SC success predicates are two
of the three audited opaques).  Dependency order (ppo 9–13) is absent in TsoMem — the sound direction.  Honest
description of the landed system theorem: "xv6 on sRVWMO + reservation serialisation".  **Under [OWN.2] this is
an INPUT, not the result**: the published theorem is at RVWMO proper; TsoMem's proofs are re-justified there by a
robustness argument (§B(9)).

**F2. The AxSL tier cannot reach allocproc** [OWN.1: retired].  Theorem 2 (`allocpidOpen2`,
`Weak/AxSpinT2b2.lean:325`) covers ≈ 230 dynamic instructions on literal row families at ≥ 57k lines [R1.s1];
allocproc's footprint is ≈ 120k (64-slot scan ≈ 8k; `memset` ≈ 16k × 7 pages, `Xv6/SpecProcPagetable.lean:39`)
with four more lock protocols, the freelist, private page-table pages.  Theorem 2 stays an audited riscv.cat-tier
validation of the handle-based lock protocol; do NOT extend it.

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
3. memory [OWN.2]: **RVWMO as the ISA defines it — `rvwmoCatConsistent` (`Weak/AxGraphCat.lean:191-194`: `gwf ∧
   gppoCatGmo ∧ gloadValue ∧ gatomicity ∧ gdepsWf ∧ gdepsGmo`; the riscv.cat transcription: rules 1–5, 7-RCsc,
   12 derived; omits 6, 7-RCpc, 8 — sound direction; fidelity by litmus, `Weak/AxLitmus.lean:29`)**, W→W
   reordering and load buffering ALLOWED; every strengthening NAMED;
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
   (`tools/audit/baseline.json:11-14`), no `sorry`; trusted base named: Sail model, image dump, the cat
   transcription, the graph-tier fetch model (W5d-G, §B(11); RULED [OWN.6]), the graph-tier dev-order model
   (W13: `po ∪ rf ∪ gmo|W ∪ dev` acyclic; RULED [OWN.8]) [R4.2][R5.1].

**Legitimately out of scope:** liveness/fairness, timing, mixed-size fidelity of the cat model (N10), MMIO
ordering beyond the modelled devices, hardware outside the Sail model, power cycles (SINGLE ERA [R2.2]).

**The statement to aim for — three layers.**  *T-alloc* (contract, exists): `Xv6.Allocproc` on MachCSL.
*M1/M2 (internal milestones, NOT published [OWN.2])*: the composed sRVWMO theorem, pinned/kernel-only (M1) then
unpinned (M2), below.  *T-alloc-RVWMO (THE published claim)* [OWN.2][OWN.3][OWN.8][R3.1][R3.2][R3.4][R4.2][R4.4]
[R5.1]:
```
∀ (σ0 : WGState) (GF : Gfexec),                                                   -- Weak/WeakRvwmoFab.lean:516
  wbootFacts σ0 ∧ σ0.wggen = 0 ∧ (∃ ds, σ0.wgdev = ds.reset ∧ diskOf ds = fsImgDisk) ∧        -- the boot [R2.2]
  rvwmoCatConsistent GF.gfGd ∧ devAcyclic GF ∧                           -- riscv.cat [OWN.2] + dev order [OWN.8]
  xv6ConfS (xboot σ0) (efInit σ0.wgdev) (imgZ σ0.wgimg) (xN σ0) GF                             -- xv6 is the program (†)
  →
  (a) the realizing MachCSL run (robustness W9–W11 → sRVWMO cand → T1 → pf run → W4, PREFIXED by PowerOn from
      the given disk) satisfies xv6FsAdequacy_closed's conclusions for ITS ONE ERA: Reducible (panics, two spin
      arms not excluded), xv6TracePure (fs purity + mmOk), xv6NiPhi / unionAdequacyClosed [R3.s2]; the realized
      pf run never enters the retry arm [R2.3]; and
  (b) the allocproc shadow tied to κs (W1 via xv6NiPhi [R3.s1]): every filed fork round answers usysForkAns of
      its citation (pid = pidPick of the cited prefix, ∈ [1, PIDMAX], or -1); KAlloc/KNull/KFree well-formed
      (poolEmpty at KNull); after W1b, live pids pairwise distinct.
```
(†) `xv6ConfS` is the SHAPED, UNPINNED, FABRIC-ORDERED conformance bundle [R5.1][OWN.8]: `gfexecConf`
(`Weak/WeakRvwmoFab.lean:523-536`: per-hart `hartConff` emissions with TWO fabric endpoints, `gfDev` = the MMIO
blocks in fabric order, `fab 0 = efInit σ0.wgdev`, store-deps in `gdDeps`) — NOT today's quiescent `gdexecQconf`
(`Weak/WeakRvwmoSupply.lean:281-289`), whose `emDevfree` (`:273`) forbids every `LDev`.  **Quiescence is VACUOUS
for allocproc**: the event LTS emits `LDev` for EVERY MMIO read/write (`Weak/WeakEvInst.lean:300-303,335-338`) and
for the disk row's START/COMMIT (`pdiskProg :484,502`; the row is in `epsInit`, `WeakEvCapstone.lean:1026-1027`),
while hart 0's `main` runs `consoleinit` FIRST (`Xv6/SpecMain.lean:7-10`) = `uartinitone`'s seven `WriteReg`s
(`Xv6/SpecUartinitone.lean:6-13`) and every secondary runs `printk` (`SpecMainSecondary.lean:7-11`); so a quiescent
candidate is a boot prefix ending before the first UART store (secondaries spinning on `started`), `userinit →
allocproc` is unreachable in EVERY such `GD`, (b) holds vacuously and (a)'s realizing run never reaches allocproc
(route-b: quiescence is an "HONEST MILESTONE … not the final theorem", `weak-memory-route-b.md:1009-1020`).
`devAcyclic GF` is the RULED dev-order axiom [OWN.8]: `po ∪ rf ∪ gmo|W ∪ gdevAdj` ACYCLIC ("the fabric order is
realizable by the machine's own ordering", `route-b.md:1040-1055`), REPLACING `gfexecConsistent`'s `gdevAdj ⊆ gmo`
conjunct (`Fab.lean:542-544`), which FabInd §5 shows no `linCand` trace realizes (`lbfNotDevOrdered`,
`linCrossHartGmoReversed`, `Weak/WeakRvwmoFabInd.lean:583,600`) — W13.  The fetch pin `emFetchImg` (`Fab.lean:534`;
`Supply.lean:277-278`) is replaced by the graph-tier Zifencei fetch condition — RULED a new trusted-base model
[OWN.6], shape per the **W5d-G spike** (§B(4)(iii), §B(11)) [R4.2] — and exclusive pairs are FUSED (no standalone
`LExLoad` — the `execProgOk'S` shape of [R3.2]).  Single-copy
atomicity of loads (`candSca`) is NOT a premise here: it is a `Cand` predicate, ill-typed on `GD`, and at Stage 2
it is DERIVED from `gloadValue` (`linCandSca`, W11) — an M1/M2-only premise [R4.4].  The conformance premise is
genuine: the graph side alone yields only `execWf`-style facts; the program half is a hypothesis realized by
`execWfPfRunProg` (`Weak/WeakAxRealize.lean:802-808`) [R1.5].  **The pin fixes WHAT a fetch answers, not WHERE
it fetches** [R3.1]: at M1 the premise is `pstepPin` + `candKfetch` (every `LIFetch` footprint in W3's pristine
window `[bcRoLo, bcRoHi)` ⊇ text, §B(4) [R5.2]), which is what makes M1 kernel-only; M2 replaces
both by Zifencei admissibility on the pf side; the target needs the graph-side twin (W5d-G).  Boot premises:
`xv6FsAdequacy_closed`'s (`Xv6/LinkSystemAdequacyClosed.lean:20-26`) transposed through `PowerOn`
(`bootShape`/`bootFacts`, `MachCSL/Lang.lean:294-304`) to `wbootFacts` (`Weak/WeakLang.lean:482-490`); `diskOf
ds.reset = diskOf ds` is a corollary of `BootSharedDev.lean:283` [R3.s4].  (b) is the trace-observable shadow of
`allocprocPost` in the NI idiom (`xv6NiPhi`, `Xv6/NiAdequacy.lean:91-92`) [R1.4].

*M1/M2 (internal)*: the same with `srvwmoConsistent c ∧ execProgOk'S (pstepPin …) … ∧ candKfetch ∧ candSca`
(M1) / `execProgOk'S pstepEv …` with Zifencei fetches `∧ candSca` (M2) in place of the two graph premises.
sRVWMO ("RVWMO, stores never early") results stay milestones only [OWN.2].

## B. Gap analysis

Legend: *need* = needed for T-alloc-RVWMO; *route* = (M) machine tier / (A) AxSL tier (retired [OWN.1]).

**(1) AxSL tier not composed with the machine tier.**  Route (A) only (retired): pf run ⇒ `srvwmoConsistent`,
`Cand` ⇒ `GdexecT`, `tierAAdequacy`'s opax runs (`Weak/AxTierA.lean:91-98`), row-family premises — XL.  Theorem 2
recorded as validation (D6).

**(2) Page tables.**  Route (M): CLOSED — kernel table a live shared invariant with A/D variants
(`KptInv.pteVariant`), `utlbOk` "up to A/D" (`MachCSL/UTlb.lean:17-21`), hit/miss/fill/write-back modelled
[R1.s3]; user-table pages fresh owned memory (`pptPost`), published at `satp` + `sfence.vma`.  Named assumption
(§B(11)): Svadu write-back as a plain view-neutral LR/SC.  S (documentation).  **(3) SIE = 0, 3 harts, no
devices/DMA.**  Route (M): CLOSED (`KCtx.sie`, `wpNext`, `NCPU = 8`, DMA at the store order).  Graph tier: OPEN —
the quiescent bundle has NO devices at all; the fabric-ordered bundle is W13 (§A(†)) [R5.1].

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
the window `[ramBase, _data)`, `:143-144`, ⊇ text + rodata); against the auth heap it reads the image byte at EVERY
view (`MachCSL/Wp.lean:1478,1490`) and a DMA write needs `DFrac.own 1` (`MachCSL/WpDma.lean:142-145`) — so
`candKfetch` is dischargeable for kernel text (W3) and NOT for user pages (`own 1` cells); `candKfetch`'s region
is W3's window `[bcRoLo, bcRoHi)` (⊇ `[text, etext = 0x80007000)`, `Xv6/KernelImage.lean:771`) [R5.2].
**[R3.1] The pin does not make a candidate kernel-only**: a pinned fetch is pf-admissible
AT ANY LOG (`fetchPinIfetchOk`, `WeakAxRealize.lean:167-176`; `ifetchByteOkb` with `itv = 0`, `WeakPromise.lean:
228-231`), the program LTS constrains the fetched value only through memory (`pstepEv`'s i-cache arm,
`WeakEvInst.lean:306-312`: any `w`), and the boot image is ZERO past the ELF (`bootByte_zero`, `BootImage.lean:30-33`).
So a conformant pinned candidate can run `userinit → scheduler → userret (fence.i) → sret` and fetch the image's
zeros at the user page (trap, kill) while TsoMem's `itv` has passed `uvmfirst`'s writes: W4's `LIFetch` row has no
TsoMem step.  Fix: M1 carries `candKfetch` (every `LIFetch` footprint ⊆ `[bcRoLo, bcRoHi)`) inside the shaped
conformance predicate; W3 discharges the row ONLY under it.
(iii) **The unpinned supply is TWO items, not one** [R4.2].  **W5d** (M2, L; part of the target [OWN.3]) is the
pf half: `execWfPfRunProgF`, the replay at `pstepEv` with the Zifencei side condition `ifetchOk img (log at k)
(itv of the hart) base tvs` (`Weak/WeakEvInst.lean:564` `elabOk`; `itvPostMachCSL`, `Weak/WeakInterp.lean:376-379`)
in place of `fetchPin`; then the (↓) `LIFetch` row holds for user text too (TsoMem reads at `tvn := max t itv`).
**W5d-G** (Stage 2, L–XL **unverified**, design first) is the graph half; a premise on `GD` has no "realizing
position" — the candidate is EXISTENTIAL,
built by `topoSupply` (`Weak/WeakRvwmoSupply.lean:865-883`: `normalizeOfAcyclic` → `rule14Linearization` →
`supplyOfQconf`) at the PINNED LTS `pstepPin`; fetches are ADMINISTRATIVE emission items (`hemit`'s `eadm`,
`Weak/WeakRvwmoConf.lean:712-722`), not graph events — no gmo position, "no cross edge at all" (route-b §4f,
`weak-memory-route-b.md:1374`) — whose only content is the pin (`emFetchImg`; Glue header deviation 5).  The
pinned LTS is pervasive: `RunData.rdProg`, `cstOk`, `hullRun`, `topoSupply`, `t2linSupply`, `walkSupply`/`segStep`
(cites in W11 (iii)); `pstepPin` occurs in 15 `WeakRvwmo*` files (Supply 14, Cert 9, Cert2 8, Cert3 7, Fab 7, Cert4
6, CycWit 6, …).  So at Stage 2 either fetches become graph read events of a
new class with their own visibility rules (Zifencei on graphs: `fence.i` the only ppo source into a fetch, no
coherence between data stores and fetches, image at `t = 0`) — a MODEL EXTENSION of `Gexec`/`gloadValue`/the
kill arms/`hemit`, re-threading the files above — or the target stays pinned and kernel-only, violating [OWN.3]
(D27).  RVWMO has no instruction-fetch model (TsoMem's is already "beyond RVWMO's text", §B(11)), so a graph-tier
Zifencei condition is a NEW trusted-base item with no reference model, NAMED in §B(11).  The **W5d-G-spike**
(Stage 0) decides fetch-as-event vs oracle-with-side-condition, enumerates the pinned-LTS sites, states the
condition.  Shape to test first [R4.s1]: a fetch is a read event of class `IF` whose byte sources are the image or
writes gmo-before the hart's most recent `fence.i` (like TsoMem's `max itv (fencePost …)`, `MachCSL/Lang.lean:
155-163`), with NO coherence against the hart's own data stores (`MachCSL/TsoMem.lean:34-39`); then W4's `LIFetch`
row reads at `tvn := max t itv`, `candKfetch` is the kernel-text instance, and the kill arms get fetch-entry
segments pinned only by `fence.i`.  Restrictive only for self-modifying user code without `fence.i`; W3 discharges
it for kernel text.  Sizes: W3 M–L [R5.2]; W5d L; W5d-G L–XL (**unverified**); spike S.

**(5)–(8) Segment coverage, scope pins, store-value rows, stack/cpu privacy.**  Route (M): CLOSED (F1; the pid
ledger handles wrap/collision retries, `Xv6/ProofAllocproc.lean:16-24`; text facts by `rfl`/`decide`; real
`stackOwn`/`kctx` resources).

**(9) THE gap: TsoMem is sRVWMO + reservation serialisation; the target is RVWMO proper** [R1.7][OWN.2].
*Inventory of weaker models in the Lean tree.*  (α) `WeakMem` pf machine = sRVWMO operational (T1
`srvwmoRealizable`, `Weak/WeakAxiomatic3.lean:2077`; T2 `t2Ev`, `Weak/WeakEvInst.lean:2046`) — TsoMem's strength
class.  (β) `WeakPromise*` (`Weak/WeakPromise.lean:1-16`, PARM natively; `wpBehavior :746`) — LB reachable
(`Weak/WeakPromiseLitmus.lean:185`); RVWMO fidelity BY INSPECTION only (`weak-memory-m6-robustness.md:42-48`).
(γ) PSO two-log machine: Rocq-only design (`relaxed-ww.md`); NOTHING in Lean.  (δ) Graphs: `rvwmoCatConsistent`
(cat) and `rvwmoMinusDepsConsistent` (`Weak/WeakRvwmoGraph.lean:628`, RVWMO⁻ + store-dep fragment).
**`minusImpliesCat` (`Weak/AxGraphCat.lean:274`) runs the WRONG way for us**:
RVWMO⁻ renders rules 1–3 as all of `gpoloc` (`WeakRvwmoGraph.lean:224-228`: `gppo := gpoloc ∨ gfenceCovers ∨
gacqPo ∨ grelAcq`), ordering a write before its own po-later same-byte read — it FORBIDS store-buffer forwarding
(N11, `AxGraphCat.lean:10-16`, `notes/weak-memory-scope.md:209-212`), so a theorem over RVWMO⁻ graphs misses
cat-consistent forwarding executions.  The whole Tier-2 chain (`rule14Linearization`, `Weak/WeakRvwmoLin.lean:
1846`; `racyD`, `Weak/WeakRvwmoAcyc.lean:200`; `t2linOfL2'''`, `Weak/WeakRvwmoWalk3.lean:77`; `xv6RvwmoSafeModulo`,
`Weak/WeakRvwmoCapstone.lean:187`; 45 `WeakRvwmo*` files, 33k lines) starts at RVWMO⁻(+deps).
**Where the cat gap lives** [R4.5][R4.s2]: `rvwmoCatConsistent` and `rvwmoMinusDepsConsistent` share `gwf`,
`gloadValue`, `gatomicity`, `gdepsWf`, `gdepsGmo` (`AxGraphCat.lean:191-194` vs `WeakRvwmoGraph.lean:252,628`) and
differ ONLY in the ppo component (`gppoCatGmo` vs `gppoGmo`), which the chain consumes only in the KILL:
`segPinGmo` (`WeakRvwmoGlue.lean:233-240`: rules 4, 5, `gdDeps` — cat-sound as is); `gcrossGmo`
(`WeakRvwmoKillArms.lean:270-275`) whose rf arm `grfGmo` (`WeakRvwmoAcyc.lean:218-233`) maps the FORWARDING (rfi,
po-visible) case through `gpoloc`'s W→R edge — exactly the edge cat lacks (cross-hart rfe needs only `gmoLt`); the
lock kit (`csChained`, `KillArms.lean:499`, premise `rvwmoMinusConsistent`; `hppo` used 11× in `WeakRvwmoLock`, 9×
in `KillArms`, 4× in `Hull`, 1× in `Cert4` — the two explicit `gpoloc` instances, `Lock.lean:200,235`, are W→W =
cat rule 1); `hullOk` is rf-closure only (`WeakRvwmoHull.lean:557-560`); `normalizeOfAcyclic`'s input
(`WeakRvwmoTopo.lean`).  `WeakRvwmoLin` (47 `hppo` uses) runs on the NORMALIZED `GD'`, RVWMO⁻ + rule 14 BY
CONSTRUCTION — unchanged; `AxGraphCat` §3 has `obCatSubGmo`/`obCatIrreflexive` (`:321-332`).  `racyDSplit`
(`Glue.lean:101-110`) sends EVERY rf arm to `gcross` (`.inr (.inl h)`), so route (a) ADDS an rfi case into `rsame`
(po-increasing under cat rule 1; `rsameLex`/`rsameAcyclic :120-141` kept) and makes `gcross` rfe-only (`grfeGmo`) —
R5 confirms.  The gap is CONFINED to the kill — Stage 2's risk is the kill arms and the lock kit, not the 33k lines.
*Why plain DRF does not apply.*  xv6 races by design.  The Lean pin census at THIS image [R4.1]
(`Weak/KernelPins.lean:22-23`, generated by `tools/gen_weak_pins.py` from `Xv6/KernelImage.lean` at `b72cbac1`): **1689
load sites: 1034 `PStack`, 3 `PPerCpu`, 289 `PCtrl`, 1 `PFence`, 180 `PDep`, 63 `PCall`, 119 `PResidue`; 58
certifying witnesses need the sp-frame assumption `own = true`** (`KernelPinsDef.Pin`, `KernelPinsDef.lean:447-465`;
checker `pinnedb`/`fwalk`/`pdfs`, call descent `pinDepth = 2`).  Racy flag reads (`started`, `panicked`, UART
LSR, virtio `used->idx`, `ticks`, `p->killed`, `p->state`) are pinned by branch/fence/lock.  The applicable
theorem is ROBUSTNESS UNDER A PER-SITE DISCIPLINE (L2′ = `l2Claim`, `Weak/WeakRvwmoGlue.lean:449`: per cycle
segment `segPin ∨ csHyps ∨ Bad`, `:229,400,440`) — DRF generalised: every cross-hart read is pinned by ppo
(ctrl/dep/fence/aq) before the hart's next store, or is a lock-protected read (`protRead`/`wprotAt`,
`Weak/WeakGhost.lean:3408,1040`), or observes an owned-unpublished message (`Bad`, refuted by violation-freedom).
The discipline must be established on the STRONG model's executions; the only verified source is the TsoMem
Iris proofs — which today export `mmOk` only (history well-formedness, views ≤ top, reservations at top;
`MachCSL/Resources.lean:779-785`), nothing per access.
*The routes, sized candidly:*
- (9a) *Re-verify xv6 on a weaker MachCSL instance.*  No PSO or promise-style `MachCSL` exists in Lean; the Xv6
  cone is ≈ 0.65M lines over 77k of `MachCSL`, every memory rule/lock/`Ctx`/racy tier re-threads (relaxed-ww's
  Rocq estimate for PSO ALONE: "2–4 weeks is the floor" + 2–3 weeks; LB has no design) — on an OPERATIONAL machine
  whose link to `rvwmoCatConsistent` is a further Promising≡RVWMO-grade theorem.  **XL × 2.  Rejected.**
- (9b) *PSO two-log machine (W6).*  L–XL fresh in Lean [R1.s4]; "RVWMO minus LB minus deps"; does not remove the
  kernel claim (LB robustness needs the same per-site discipline).  **Not on the path under [OWN.2]**; optional
  de-risk of the discipline export only (D4).
- (9c) *Promise-machine robustness (W7-P).*  `robustMain` (`Weak/WeakRobustMain.lean:1520`) EXISTS: a
  `wpBehavior` of the promising machine is matched by a `wpPfRun` run — W4's input — given `pfViolationFreeHart`
  (`Weak/WeakRobust.lean:118-121`) and six side premises.  But (i) φ is REFUTABLE at event granularity (walker CAS
  parked before its release-pending store, `weak-memory-lift.md:19-29`; the block-granular `WeakComposeLang` was
  skipped by the port, `notes/weak-port-skip.md:6,38`); (ii) the quantifier would be the promising machine, fidelity
  EXTERNAL — **fails [OWN.2].**  Fallback only if the owner relaxes D2 (D2′).
- (9d) *Graph-tier robustness re-sourced from TsoMem (RECOMMENDED — the cheapest SOUND route: the T2-LIN induction
  `cycleKill`, `Weak/WeakRvwmoLinInd.lean:155`, realizes each proper hull as an sRVWMO candidate, `hullRun`,
  `Glue.lean:272-290`, W4 turns that into a TsoMem run on which the SC tree's facts hold — robustness by minimal
  violation, reusing the 33k-line chain).*  Residue of `xv6RvwmoSafeModulo` today (`WeakRvwmoCapstone.lean:187-215`):
  (R-1) `l2Claim`; (R-2) `walkSupply` (`Weak/WeakRvwmoGlue2.lean:453`), reduced to the per-state datum
  `wsegSupply`/`walkPolicy` (`WeakRvwmoWalk2.lean:453`, `Walk.lean:897`; `t2linOfL2'''`, `Walk3.lean:77`) — its
  non-vacuity witness is a hand-built LB cycle (`Weak/WeakRvwmoCycWit.lean:1-30`); `wpPackage`
  (`Glue.lean:338-346`: an EWP proof of ALL of xv6 on the weak event language — xv6 does not have it;
  `weakSystemAdequacyPhi`, `Weak/WeakAdequacy.lean:194`, takes the weak WPs too); `efetchItvOk` (W3/W5d);
  **(R-3)** the pin bridge's honest residual: "that a `pstepEv` run's items ARE grouped as the checker's pc walk
  assumes" (`Weak/WeakRvwmoPinBridge2.lean:28-29`) [R4.1].  **What EXISTS for W9** [R4.1]: `Weak/KernelPins.lean`
  (1,901 lines, the witness table), `KernelPinsDef.lean` (639, the checker), `tools/gen_weak_pins.py` (1,004;
  `--check` re-verifies); reflection facts `imagePinnedb`/`pinsCover` (`KernelPins.lean:1817-1860`); the bridge
  `pinSegPin` (PDep ⇒ `rowDeps` ⇒ `gdDeps` ⇒ `segPin`, `WeakRvwmoPinBridge.lean:284-330`; `segPinOfRowFence :295`)
  and `pinSegPin'` with `checkerTaintSubProv` DISCHARGED for the oracle `psites` (`PinBridge2.lean:530-553`); the
  callee-summary table is "an AUDIT artifact that nothing downstream reads" (`route-b.md:1456-1460`) — no "callee
  summaries" item.  Work: **W8** export the discipline
  from the SC tree; **W9a** R-3 (align a `pstepEv` run's item groups with the checker's walk, `reaches`/`psites`;
  `PinBridge2` §8 has both halves on one computed stretch); **W9b** the non-certifying classes are W8's INPUT, not
  `segPin`: `PStack`/`PPerCpu` (1,037) = "no foreign writer" = W8's ownership (i), the 58 `own = true` witnesses
  rest on the same fact, `PCall` 63 + `PResidue` 119 = 182 sites = W8's (ii)/(iii), site list from
  `gen_weak_pins.py`'s audit (D28, RULED (a) [OWN.7]); **W10** `wsegSupply` for xv6; **W11** re-source the glue's
  `Bad`/`protReg` from W8 via W4, restate the capstone over `xv6ConfS`; **W12** the cat↔RVWMO⁻ gap (N11); **W5d-G**
  fetches on the graph tier; **W13** the fabric-ordered bundle, the dev-order axiom and T2-1c′ (§A(†)) [R5.1][OWN.8].
  Sizes: W8 L–XL, W9a M–L, W9b in W8, W10 M–L (**unverified**), W11 L [R4.3], W12 L–XL — likely L after the spike
  [R4.5], W5d-G L–XL (**unverified**) [R4.2], W13 L–XL (**unverified**; T2-1c′ "sizeable", route-b).  **Total: XL**
  — multi-week, many files, three items of unknown size (W5d-G, W10, W13).
*Recommended:* (9d), staged after M2; W12-spike, W5d-G-spike and W13-spike FIRST (they CONFIRM D25 (a) [OWN.5],
SHAPE the fetch model D27 (a) [OWN.6], and size T2-1c′ [OWN.8]); (9b) only if W8 wants a smaller model to start on
(D4); (9c) as D2' fallback.

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
conditional write; `LExLoad` at the 0 floor, `WeakPromiseBridge.lean:418-423`).  **[R2.3-alt]** a STANDALONE
`LExLoad` is realizable as a plain `LLoad` (`lbNobarex`, `:97-103`; `projLbl :545`); TsoMem's dangling reservation
blocks foreign stores (`Lang.lean:147-153`) and its exclusive read takes `topBytes` (`:368-371`) — (↓) fails.
**[R3.2] the shape cannot be a separate conjunct on `(c, pst)`**: the realizing `l` and the stars are existential
per index inside `execProgOk'` (`WeakAxRealize.lean:373-386`; `admStar = rtc admStep`, no label list, `:343-344`).
So the premise is ONE shaped conformance predicate
**`execProgOk'S pstep pcls pst dv E`** := `execProgOk'` with (i) the left disjunct's `l` not an `LExLoad`
(re-imposing `lbFused` on the left arm only, cf. `lblRealizesUnproj :245-247`), (ii) the stars as label-carrying
`admRun`s (`Weak/WeakRvwmoConf.lean:374-381`) whose every `LIFetch` is in kernel text (M1, `candKfetch`) /
Zifencei-admissible (M2), (iii) every `LLoad` single-copy-atomic (`candSca`, below).  W5b consumes it and carries
**`pairAdjacent`** — NEW, in NO file of the tree (grep `Weak/ Xv6/ MachCSL/ claude-notes/`: none; coined by R2),
DEFINED HERE so W2 and W5b copy ONE text [R5.3]: *in a shaped run every realized exclusive pair's halves `l1 =
LExLoad …`, `l2 = LExStore …` (`lblRealizesPair`, `WeakAxRealize.lean:305-313`) are consecutive steps of the SAME
hart up to its own `LInstr`-free administrative star `admStar pstep false pm dm pm2 dm2` (`execProgOk'`'s right arm,
`:380-386`, one exec index); no other agent's step — in particular no foreign store — lies between them* — plus the
fetch/SCA facts along the run; W5c must PRODUCE it (`execProgOk'Snoc`,
`Weak/WeakRvwmoCert.lean:413`, yields plain `execProgOk'` — an S-variant or derivation lemma is needed).  At
Stage 2 the chain's `RunData`/`cstOk`/`segStep`/`topoSupply`/`t2linSupply` (all plain `execProgOk'` today) must
produce the S-variant — W11 (iii) [R4.3], sharing W5d-G's site list.
**[R3.4] (↓) fails on PLAIN LOADS even on shaped runs — tearing.**  WeakMem's `readable` is per byte
(`Weak/WeakMem.lean:400-402`; `readOkD`, `WeakPromise.lean:183-188`; `byteRd`/`rdOk`, `WeakAxiomatic.lean:122-130`);
no axiom joins the bytes of one label (N10).  TsoMem reads every byte of a load at ONE `tvn` (`Lang.lean:363-367`).
Counterexample: whole-word stores `S1@4`, `S2@6`; a floor-0 load with `ts = [4,4,6,6]` is admissible and
sRVWMO-consistent; TsoMem yields all-`S1` or all-`S2`.  RMWs are exempt (`rmwLatest`, `WeakAxiomatic.lean:134`);
fetches under W5d are NOT (`ifetchByteOk` per byte, `WeakPromise.lean:222-231`).  The ISA guarantees
single-copy atomicity for naturally aligned accesses ≤ XLEN, so the premise is ISA-faithful — NAMED as
**`candSca c`**: every `LLoad` (M2: and `LIFetch`) reads its bytes at one view — `∃ tvn, ∀ j, ts[j]` is the
latest write to byte `j` at or below `tvn` or the hart's own later store (TsoMem's forwarding clause).  Carried
by W5b; row "plain load" of W2's table is (↓) iff `candSca`; alternative = an atomicity axiom in sRVWMO
(re-opens T1, XL) — D20.  **At Stage 2 `candSca` is DERIVED, not assumed** [R4.4]: the graph model has ONE gmo
position per LOAD EVENT — `gloadValue` (`Weak/WeakRvwmoGraph.lean:238-243`) requires each byte's source to be
`gvisible G w e` (`:236`) and co-MAXIMAL among the visible same-byte writes, so a torn read of two whole-word stores
is already inconsistent; `topoSupply` linearizes the NORMALIZED `GD'` and `linCand` (`WeakRvwmoLin.lean:471`) copies
labels, so every realized `LLoad` reads at its event's position: `linCandSca : rvwmoMinusConsistent G' → grule14 G'
→ candSca (linCand G')` (S, W11) feeds W5b's shaped replay.  Not for fetches (administrative; W5d-G).
*(↑) receptiveness is NOT available on route (M)* [R2.3(iv)]: weak-side `Reducible` would need the weak WP
package.  (a) is stated for the realizing MachCSL run; the free weak-side sentence is "the realized pf run never
enters the retry arm" (D15).  W4b dropped.
*Single era* [R2.2]: `epowerFork` forks no power thread (`Weak/WeakEvLang.lean:201-204`), so multi-era
conclusions are NOT transported; W4's run is prefixed by the `PowerOn` step (D14).
*The relation `R`* [R2.s3][R3.s3][R3.4], fixed in the spike report: TsoMem `tv ↔ max wVrNew (own last store)` —
**the `.aq` off-by-one** [R3.s3]: at an acquire pair TsoMem's `tv` becomes the WRITE's timestamp `top + 1`
(`MachCSL/Lang.lean:150`), WeakMem's `wVrNew` the READ's (`exloadPostRunD`, `Weak/WeakMem.lean:834`; `storePostD`
leaves `wVrNew`, `:634-647`); `rv ↔ wVrOld`, `ownPub ↔ wVwOld`, `coh ↔ wCoh`, histories = log projection
(`MState.store`'s author log `σ.log` + per-byte timestamped histories, `Lang.lean:147-153` ↔ `σ.wglog`), image
`imgZ ↔ imgFlat`, `resv ↔ wRes` only mid-pair, `itv`: the pf machine has none, so `R` carries "the MachCSL `itv` is
below every fetch's version" (W3 / W5d); the load row carries `candSca`'s `tvn`.  Spot checks (↓): `fencePost`
raises `wVrNew` to `max wVrOld wVwOld` for `pr,pw` (`WeakMem.lean:674-678`), `wVwOld` = TsoMem's `ownPub`; `fence
rw,rw`/`r,r`/`rw,w` agree.  Open per label: parked `fence rw,w`/`wRelp` (`:684`) vs TsoMem's no-op; `wRes := none`
at any non-trivial fence (`:688`) vs TsoMem keeping it; the `.aq` carried bit (`MachCSL/TsoMem.lean:255-280`); the
i-fetch agent (no forwarding) vs `LIFetch`; devices/DMA (`Efab` vs `MState.devrt`; `anyReserve`).  Size: L (↓) +
L (W4) + M (W5b) + M (W5) + M–L (W5c) + L (W5d).  It lifts the WHOLE system theorem; (9d) reuses it in both
directions, and **the log identification is what carries `protReg` and `¬ badSeg`** (W11) [R4.3].

**(11) Model fidelity and named assumptions (trusted base, list in the header)** [R1.1][R1.7][R2.4][R3.1][R3.2]
[R3.4][R4.2][R4.4].  Candidate/conformance premises: `execProgOk'S` (fused exclusive pairs — "a dangling LR or
failing SC is outside the theorem", D19; M1 only: `candKfetch`, kernel-only candidates, D21); `candSca` (single-
copy atomicity of aligned loads ≤ XLEN; ISA-faithful; **M1/M2 ONLY** — derived at Stage 2, D20); Zifencei
admissibility of pf fetches (M2); **the graph-tier fetch model** (W5d-G: fetches as `IF` read events or an
oracle with the Zifencei side condition — a trusted-base item with NO reference model, since RVWMO has no
instruction-fetch model; D27 RULED (a) [OWN.6]); **the graph-tier dev-order model** (W13: the fabric axiom `po ∪
rf ∪ gmo|W ∪ gdevAdj` acyclic — hardware honours it through the M5 fence discipline, `route-b.md:1023-1024`; no
reference model either; RULED [OWN.8]) [R5.1].  Strengthenings beyond RVWMO carried INTERNALLY by TsoMem/sRVWMO (not in the
published statement once (9d) lands): "stores never early"; reservation serialisation.  Machine-model choices:
exactly 8 harts booted; Svadu A/D write-back as a plain view-neutral LR/SC; DMA as a store-order agent; the
instruction-fetch model (`MachCSL/TsoMem.lean:34-39`, `Lang.lean:360-362`, `MState.fence :155-163`) — beyond
RVWMO's text (Zifencei); the SC-failure model (memory never fails an exclusive write; the Sail opaques decide,
`Xv6/UserMemLrsc.lean:7-12`; D17); single era.  Fidelity: `rvwmoCatConsistent` omits rules 6, 7-RCpc, 8 (sound
direction), litmus-checked only; the published quantifier IS cat — D25 (a) RULED [OWN.5], W12 on the critical path,
no RVWMO⁻ fallback; Sail fork `070832a1` with `-D SYMBOLIC`; the image dump.  Keep, list.

**(12) Audit coverage and file layout** [R1.10].  `Xv6/` never imports `Weak/`; lake libraries `MachCSL`, `Xv6`,
`Weak` (`lakefile.toml:2,27-41`).  Composition files live in `Weak/`, registered in `tools/ci/roots-weak.txt` +
`tools/audit/baseline-weak.json` + `XV6_AUDIT_MODULES` (`tools/ci/audit.sh:44`), built by `--weak` CI, whose cone
includes the whole `Xv6` adequacy cone (D13).  Pure-`Xv6/` items (W3, W8) go to `roots.txt`/`baseline.json`.  S.

## C. Roadmap

Each stage ends in a theorem; "∥" = parallel (one Opus worker, one file each).  Stages 0–1b are INTERNAL
milestones on the critical path of the target; Stage 2 is the target [OWN.2].

**Stage 0 — launch now: W3 (SERIAL on the adequacy files) → W2 spike, ∥ W1, W5b, W5c, W12-spike, W5d-G-spike,
W13-spike** [R2.s4][R4.2][R5.1].
- **W3 `Xv6/TextPristine.lean` + sibling root `Xv6.xv6TextAdequacy_closed` (`Xv6/LinkTextAdequacy.lean`)** (M–L,
  SERIAL) [R1.8][R2.1][R3.1][R5.2][OWN.9].  NOT "no store targets text": the state interpretation exports no
  per-STEP fact and an identical-value store is harmless; the idiom is a per-STATE predicate pulled through the hook
  (`powerInterp_mmOk`, `MachCSL/Adequacy.lean:481` → `xv6TraceHook`, `Xv6/SystemSlot.lean:590-612` →
  `xv6TracePure`'s `g.pow = true → mmOk g.m`, `:135-136` → the root).  `textPristine g` := every byte of
  `[bcRoLo, bcRoHi)` has history `[⟨0, _, img a⟩]` — equivalently `g.m.mem.readBytes (ifetchAgent cpu) tvn …`
  returns the image bytes at EVERY `tvn` (`MachCSL/Wp.lean:1478,1490`; TsoMem's fetch, `Lang.lean:360-362`) — from
  `kernelText`'s `□` singleton histories (§B(4)).  Files: a `powerInterp_textPristine` twin beside
  `powerInterp_mmOk`; `□ kernelText` made reachable at the hook (today it sees only `powerInterp` and `▷ xv6Slot`,
  `SystemSlot.lean:308` — stash it in the slot or thread it from the carve, `BootCarve.lean:582`) via a hook twin;
  the SIBLING root with `xv6FsAdequacy_closed`'s three boot hypotheses (`Xv6/LinkSystemAdequacyClosed.lean:20-26`)
  concluding `textPristine g2`: a NEW line in `roots.txt`/`baseline.json`, every existing root statement and
  baseline entry UNTOUCHED [OWN.9].  Discharges W4's `LIFetch` row under `candKfetch` (M1) and the kernel-text half
  of Zifencei admissibility (M2).  Deps: none; the only Stage-0 item on shared files — nothing else touches them.
- **W1 `Xv6/AllocprocTrace.lean`** (S–M, re-scoped [R3.s1]; D23).  `xv6NiAdequacy` (`Xv6/LinkNiAdequacy.lean:82-90`)
  has the SAME three boot hypotheses as `xv6FsAdequacy_closed` and concludes `xv6NiPhi g2 κs`, whose `NiClassLaw`
  (`Xv6/NiTrace.lean:660`, via `niOk`, `Xv6/NiLedger.lean:319-322`) contains `niRoundLaw`'s fork row (`:646`): the
  enter's `a0 = usysForkAns ι` = sign-extended `pidPick PIDMAX ι.pev` or `-1` (`Xv6/UsysDet.lean:293-302`) at the
  CITED prefix — tie β (D11), round identification solved (`exitView`/`enterView`).  W1 = cite `xv6NiPhi` + pure
  history lemmas on `ι.pev`/`ι.kev`: `pidPick ∈ [1, PIDMAX]`, the `nextOf` tie (`Xv6/PidEv.lean:77`), `poolEmpty`
  at every `KNull` (`Xv6/KallocEv.lean:72`).  Conclusion (b): "every filed fork round answers `usysForkAns` of its
  citation".  Today's ledgers export no page address (`Kev`, `KallocEv.lean:45-52`) and no slot index (`Pev`,
  `PidEv.lean:50-55`); `liveOf` is a set.
- **W1b (owner-gated, L, serial)**: `pidHistWf h` in `pidLedger` (live pids distinct by induction), re-thread
  `ProofAllocproc`/`ProofFreeproc`/`NiLedger`; optionally addresses in `Kev` for page disjointness.  D10.
- **W2 `Weak/TsoOfPf.lean`** (L; spike first, ≤ 200 lines, risk report) [R1.11][R2.3][R2.s3][R3.4][R3.s3].
  `pfStepTso`: for every memory label (one row per exclusive half, one for the plain load), a `wpPfStep` from an
  `R`-related state under `pairAdjacent` (§B(10)'s text, a HYPOTHESIS here [R5.3]) + `execProgOk'S`'s shape +
  `candSca` is a TsoMem step with the same bytes, to a related state.  Report: per-label (↓) table; fence spot
  checks; `R` fixed with the `.aq` off-by-one; (↑) recorded as NOT CLAIMED; the log identification stated in the
  vocabulary W8/W11 need (author, class, position, per-byte history) [R4.s3].  Deps: W3's statement; W5b's
  `pairAdjacent` statement (day one, S).  **STOP rule** (D7): a WeakMem behaviour TsoMem lacks on a
  SHAPED run → STOP, report; suspects: parked release fence, fence-clears-reservation, tearing, `.aq` off-by-one
  [R3.s5].
- **W5b `Weak/PfRunShape.lean`** (M) [R2.3(iii)][R3.2][R3.4][R5.3].  `execPrefixPfRunProgShaped`: the replay
  variant that consumes `execProgOk'S`, DEFINES and PROVES `pairAdjacent` (§B(10)'s text, from `execProgOk'`'s right
  arm — day-one deliverable, the statement goes to W2), and carries it, the fetch facts and `candSca`'s per-load
  `tvn` along the run — a new theorem in `Weak/`, not a change to `WeakAxRealize`.  Deps: none.
- **W5c `Weak/SrvwmoXv6Witness.lean`** (M–L, re-specified [R3.3]; D22).  Non-vacuity: M1's premise set is
  SATISFIABLE.  The `sw &started` block does NOT witness it: M1 fixes `pst 0 = epsInit σ0` (every hart at `.pure ()`
  with the boot register file, pc at `_entry`; `WeakEvCapstone.lean:1026-1027`, `WeakLang.lean:488`), while the
  existing witness sits at the MID-instruction node `WeakEvStarted.evX2` with an EMPTY administrative run
  (`Weak/WeakRvwmoConfWit.lean:11-22`; `smC`/`smSnocConsistent`, `Cert.lean:522-546`, give only consistency), and
  `started = 1` is the LAST store of the boot (`Xv6/SpecMain.lean:6-15`) — a whole-boot replay.  The block is
  `_entry`'s FIRST memory instruction, `ld sp,1000(sp)` at `0x80000004` (`Xv6/KernelImage.lean:14-17`; GOT word at
  `0x8000a3e8`, image bytes, `t = 0`): hart 0 alone (seven idle), pinned fetches of `_entry`'s two instructions in
  kernel text (`candKfetch` ✓), the administrative run by kernel evaluation (`esil`, `Weak/WeakEvLift.lean:897`;
  `pevrunAdmRun`, `Weak/WeakRvwmoCert2.lean:180` — the `esil → admRun` bridge `Weak/WeakRvwmoConfWit2.lean:26-28`
  records as THE missing mechanism), consistency from `gtraceSnocReadImage` (`Weak/WeakRvwmoFloor.lean:1025-1035`)
  or `snocRdAdm` (`Weak/WeakRvwmoCert.lean:257`), a concrete `σ0` with `wbootFacts` (`MachCSL/BootRun.lean`),
  `candSca` trivially (one store per byte), and the S-variant of `execProgOk'Snoc`.  Certifies satisfiability —
  NOT that any candidate reaches `allocproc` (whole-boot replay, D18's user-fetch witness) — and it is QUIESCENT
  (no `LDev`): it certifies NOTHING about W13's fabric-ordered bundle, whose natural witness is hart 0's first
  `WriteReg` of `uartinitone` (W13-wit, Stage 2; `Fab.lean` §6: none in the tree) [R5.s3].  Deps: W5b's predicate.
- **W12-spike `Weak/CatOfMinusSpike.lean` (read-only report, S)** [OWN.2][OWN.5][R4.5][R5.s1].  CONFIRM and size
  D25 (a) (RULED) by auditing the TWO gates where the chain uses `gpoloc`'s W→R edge: (gate 1) `grfGmo`'s rfi case
  (`WeakRvwmoAcyc.lean:218-233`) via `gcrossGmo` (`KillArms.lean:270-275`) and `racyDSplit` (`Glue.lean:101-110`,
  which today sends ALL rf to `gcross` — needs an rfi case into `rsame`; rfe then by `grfeGmo`, `AxGraph.lean:261`,
  from `gloadValue` alone); (gate 2) `csChained`'s premise `rvwmoMinusConsistent` (`KillArms.lean:499`), the lock
  kit's lemma-level `hppo` uses — cat rule 5 (`Lock.lean:120`), rule 4 (`:125`), rule 1 W→W (`:200,235`); KillArms
  `:537,586` through those lemmas; Hull 4, Cert4 1 to confirm — and the two WITNESS-GRAPH proofs of `gppoGmo`
  (`KillArms.lean:811-813,1179-1181`, `intro e1 e2 hppo` for `lkw`/`lkw2`) that must be RE-PROVED for `gppoCatGmo`
  (more arms: rules 2, 3) [R5.s1]; then `normalizeOfAcyclic`'s input and the hypothesis of
  `cycleKill`/`t2linOfCycleKill` (`LinInd.lean:155,231`)/`cycleKillOfL2''` (`Glue2.lean:521`)/the capstone.  Also
  confirm `segPinGmo` (`Glue.lean:233-240`) and `AxGraphCat` §3 cover what the kill needs.  Outcome: (a) is RULED
  [OWN.5] — report its size (L expected); (b) forwarding-normalisation dropped (fwd+dep+W→W is cat-consistent with
  no RVWMO⁻ twin); (c) RVWMO⁻ fallback NOT accepted — if (a) exceeds L, report, do not fall back.  Deps: none.
- **W5d-G-spike `Weak/GraphFetchSpike.lean` (read-only report, S)** [R4.2][R4.s1][OWN.6].  SHAPE the RULED
  graph-tier fetch model: fetch-as-event (class `IF`, the [R4.s1] shape in §B(4)(iii)) vs oracle-with-side-
  condition; enumerate the `pstepPin` sites to re-thread (15 files, §B(4)); state the graph Zifencei condition and
  its TsoMem twin (`tvn := max t itv`); say what the kill arms gain (fetch-entry segments pinned only by `fence.i`).
  Feeds W5d-G and W11's re-thread list.  Deps: none.
- **W13-spike `Weak/GraphFabSpike.lean` (read-only report, S)** [R5.1][OWN.8].  State the vacuity of `gdexecQconf`
  for allocproc (§A(†)); audit `fconfSupply`'s handed-back guard `trDevOrdered` (`Weak/WeakRvwmoFabInd.lean:
  407-410`; `t2linSupplyF :523-534`) and FabInd §5 (`lbfNotDevOrdered :583`, `linCrossHartGmoReversed :600`); fix
  the form of the RULED axiom `devAcyclic` (`po ∪ rf ∪ gmo|W ∪ gdevAdj` acyclic on `Gfexec`, replacing
  `gfexecConsistent`'s second conjunct, `Fab.lean:542-544`; `racyF :546` gains nothing); size **T2-1c′** — the
  trace-flexible linearization: any linear extension of `po ∪ rf ∪ gmo|W ∪ dev` with every read at its `G`-source
  is `srvwmoConsistent` ("generalizes `WeakRvwmoLin`'s proof; sizeable", `route-b.md:1047-1055`); list what
  `hullRun`/`cycleKillF`/W11 must thread; name the `LDev` witness's prologue (W13-wit).  Feeds W8's design too
  ([R4.s5] list).  Deps: none.

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

**Stage 1b — M2, the fork path on the pf side (part of the target [OWN.3]).**
- **W5d `Weak/PfRunUnpinned.lean`** (L) [R2.1-alt][R3.1][OWN.3][R4.2].  The pf half ONLY: `execWfPfRunProgF`
  (replay at `pstepEv` with Zifencei admissibility replacing `fetchPin`), W4's `LIFetch` row for user text, W5
  restated — the first form in which `fork → ecall → sys_fork → allocproc` under contended `p->lock` from 7
  scheduling harts is a candidate.  A user-fetch witness (satisfiability of M2's premise set on the fork path)
  = whole-boot replay; not scheduled (D18).  The graph half is W5d-G (Stage 2).  Deps: W5.

**Stage 2 — THE TARGET: T-alloc-RVWMO via graph-tier robustness re-sourced from TsoMem (route 9d; XL).**
- **W12 `Weak/CatLin*.lean`** (L–XL, likely L after the spike [R4.5]; D25): route (a) — rfi into `rsame`,
  `gcross` rfe-only, `gcrossGmo` by `gmoLt`; the lock kit and `normalizeOfAcyclic` over `rvwmoCatConsistent`;
  `cycleKill`/`t2linOfCycleKill`/`cycleKillOfL2''`/the capstone re-hypothesised.  `WeakRvwmoLin` untouched.
- **W5d-G `Weak/GraphFetch*.lean`** (L–XL, **unverified**; per the spike/D27) [R4.2]: fetches on the graph tier
  with the Zifencei condition; `gdexecQconf`'s `emFetchImg` → the new condition (= `xv6ConfS`'s fetch clause);
  the `pstepPin` sites re-threaded (one pass shared with W11 (iii)).  Non-vacuity gate: the user-fetch witness
  (D18) — now also W5d-G's.  D27 (a) RULED [OWN.6].
- **W13 `Weak/GraphFab*.lean`** (L–XL, **unverified**; per the spike) [R5.1][OWN.8].  (i) `xv6ConfS` on
  `gfexecConf` (`fab 0 = efInit σ0.wgdev`, `gfDev` in fabric order; `Fab.lean:523-536`), not `gdexecQconf`;
  `devAcyclic` as the model arm (§A(†)); `Fab.lean` stops being a leaf.  (ii) **T2-1c′** so `trDevOrdered` is
  DISCHARGED — not handed back — in `cycleKillF`/`t2linSupplyF` (`FabInd.lean:397,523`), threaded through
  `hullRun` and W11 (v).  (iii) **W13-wit** (M–L): the `LDev` non-vacuity witness — hart 0's run `_entry → start →
  main → consoleinit → uartinit → uartinitone` to its first `WriteReg` (`0x80000896`, `Xv6/KernelImage.lean:1590`;
  ≈ 100 dynamic instructions, plain stores from `initlock`, NO MMIO before it: `timerinit` is Sstc CSR-only,
  `Xv6/SpecTimerinit.lean:5-7`), by kernel evaluation as in W5c — the first candidate with a non-empty `gfDev`
  (D31).  Deps: W13-spike, W5c's `esil → admRun` bridge.
- **W8 `Xv6/AccessDiscipline.lean`** (L–XL; D24) [R4.3][R4.s3][R4.s4].  Export from the SC tree, per reachable
  MachCSL state (the `mmOk` idiom) on `MState`'s author log + per-byte histories (`MachCSL/Lang.lean:147-153`), in
  the vocabulary `protReg`/`badSeg` consume: (i) bytes a hart OWNS — no foreign writer (covers `PStack`/`PPerCpu`,
  the 58 `own = true` sp-frame witnesses; `gen_weak_pins.py --check` as the audit); (ii) a protected access under
  a held lock — holder at a position, holder's plain stores after `r0`, the write not touching the lock word
  (`wprotAt`/`wlpAt`/`wlpAlt`, `Weak/WeakGhost.lean:1040,543,699`; `lockWordByte`, `KillArms.lean:340`); (iii) no
  hart's floor reaches a FOREIGN owned-unpublished message (`clsOf m = .SCowned` ⇔ `wmAk = .WCplain`,
  `WeakRobustMain.lean:390-395`; `¬ wpublished`, `pubOf :399-400`; alignment `Weak/WeakViolation.lean:9-15`) —
  HART authors only, DMA exempt, mirroring `violationHart` (`WeakRobust.lean:100-107`); (iv) ALL 182
  `PCall`/`PResidue` sites and the 58 sp-frame witnesses classified into (i)–(iii) for the PUBLISHED theorem (W9b;
  D28 RULED (a) [OWN.7] — no interim named assumption).  Needs a ledger threaded through the MachCSL memory rules
  (`UMem*`, `Lock`, `Ctx`, racy tiers) — mechanical but wide; the ownership residue is ~5 idioms (`swtch` context
  reloads, trapframe loads off `a0`, user-table walks, boot-published globals).  Design starts after the W2 report
  AND all THREE spike reports [R4.s5][R5.1].
- **W9a `Weak/WeakRvwmoPinBridge3.lean`** (M–L) [R4.1].  R-3: a `pstepEv` run's items are grouped per
  instruction as the checker's pc walk assumes (`reaches`/`psites`, `PinBridge2.lean`; §8 has both halves on one
  computed stretch) → `pinSegPin'` applies at every certifying site of the REAL run; with W8 (W9b) → `l2Claim`'s
  `segPin ∨ csHyps` arms for xv6.  No generator work: `KernelPins.lean`/`imagePinnedb`/`pinsCover` exist.
- **W10** (M–L, **unverified**): `wsegSupply`/`walkPolicy` for xv6 graphs.
- **W11 `Weak/RvwmoXv6Adequacy.lean`** (L; was M–L) [R4.3][R4.4].  (i) **The `Bad` arm is LOG-LEVEL**: today
  `l2ClaimAt GD P Bad` (`Glue.lean:440-447`) hands the prover `(GD, log, logOf, protReg)` while the capstone sets
  `Bad := badRun gen σ0 = ∃ ρ, rtc epfRun … ∧ violationHart …` (`:384-385`) — a RUN-LEVEL existential no prover can
  exhibit from a graph and a log, refuted by `noBadRun` (`:387-391`) over ALL `epfRun`-reachable configurations,
  which route (M) cannot reach (only realized SHAPED runs have a TsoMem twin, [R2.3(iv)]); `rawChainChain` consumes
  `¬ Bad` globally (`:453-460`).  Define `badSeg GD log prev s` := the entry's source message is owned (`wmAk =
  .WCplain`) and unpublished at `log` by a FOREIGN hart author; restate `l2ClaimAt` with it; prove `¬ badSeg` at the
  certified run from W8 (iii) through W4 (the realized hull run is a prefix of the realizing TsoMem run) and derive
  the global `¬ Bad` `rawChainChain` needs.  (ii) `protReg P log` (`:364-368`) is a fold over
  the LOG, so it transfers through `R`'s log identification once W8 exports (ii) — D24's shape.  (iii) re-thread
  `execProgOk'S` through `RunData`, `cstOk`, `segStep`, `topoSupply`, `t2linSupply` (plain `execProgOk'` today).
  (iv) `linCandSca` (S) [R4.4].  (v) Restate `cycleKillOfL2''` (`Glue2.lean:521`), `t2linOfL2'''`
  (`Walk3.lean:77`), `xv6RvwmoSafeModulo` (`Capstone.lean:187`) with W8-sourced facts in place of
  `wpPackage`/`wpPackageProt`/`noBadRun`/`protRegOfRun`/`efetchItvOk`; compose with M2, W5d-G and W13 (the
  fabric-ordered bundle, `devAcyclic`, T2-1c′'s supply): **T-alloc-RVWMO**.  Header per §B(11).
- *Not on the path:* **W6** PSO machine (L–XL; optional de-risk, D4); **W7-P** promise-machine fallback (D2').

**Stage 3 — AxSL tier: retired** [OWN.1].  One-paragraph note on Theorem 2 (D6).

**Launch now:** W3 first — SERIAL, the one Stage-0 item on shared files (`MachCSL/Adequacy.lean`,
`Xv6/SystemSlot.lean`, a new link file, `roots.txt`/`baseline.json` additions) [R5.2] — then W2 spike ∥ W1 ∥ W5b ∥
W5c ∥ W12-spike ∥ W5d-G-spike ∥ W13-spike, independent files.  W1b waits for D10; W8 design starts after the W2
report and all THREE spike reports (its export shape depends on `R`; its site list on W5d-G; its kill-arm vocabulary
on W12; its fabric vocabulary on W13) [R4.s5][R5.1].

## D. Owner questions (recommended option first; RULED items kept for the record)

- **D1 / D2 / D12** — RULED [OWN.1][OWN.2][OWN.4]: machine tier (Theorem 2 = validation); FULL RVWMO
  (`rvwmoCatConsistent`), sRVWMO/pinned forms internal; the `verified` fork named in the header.  **D2′.** If (9d)
  is judged too large: (Rec) hold publication; (b) the promising machine with "Promising-RISC-V ≡ RVWMO (Pulte et
  al.)" in the trusted base — not cat, violates [OWN.2].
- **D3. Conclusion form.**  (Rec) trace-level predicate via `xv6NiPhi` (W1) beside the Iris contract; (b) contract only.
- **D4. PSO machine (W6)** — under [OWN.2]: (Rec) SKIP — reaches neither the target nor the kernel claim; (b) build
  it as a de-risk for W8's export (the discipline is simpler to state at PSO).
- **D5. Q4 / W3.**  (Rec) launch first (critical path, `LIFetch` row); (b) none.
- **D6. Theorem 2.**  (Rec) keep `allocpidOpen2` + certificates as the audited riscv.cat-tier validation; note S.
- **D7. W2 failure mode** [R2.3][R3.s5].  Suspects: parked release fence, fence-clears-reservation, tearing (named
  premise), `.aq` off-by-one (in `R`).  (Rec) change `WeakMem`'s event instance to MachCSL's shape where the kernel
  proofs allow; (b) a MachCSL change (owner-gated, serial).
- **D8. Hart model.**  (Rec) "exactly 8 harts, all booted" named; (b) a "≤ 8" variant (MachCSL change, serial).
- **D9. Panics.**  (Rec) not excluded, stated; (b) "no `panic:` bytes in the UART trace" (M–L) — at the graph
  tier meaningful only once W13 lands (the quiescent bundle has no UART) [R5.1].
- **D10. W1 scope.**  (Rec) W1 via `xv6NiPhi` now; (b) also W1b (L, serial) for pid/slot uniqueness, page disjointness.
- **D11. W1 tie.**  (Rec) observation-level β — already in `niRoundLaw`'s fork row; (b) state-level α.
- **D13. Where the composed theorem lives.**  (Rec) `Weak/`, `--weak` audit with the full `Xv6` cone; (b) separate lane.
- **D14. Single era.**  (Rec) "one boot, no power cycles"; (b) multi-era W4 (`WExpr.power` in the pool; M).
- **D15. Reading of (a).**  (Rec) conclusions about the realizing MachCSL run + "the pf run never spins in the
  retry arm"; (b) no weak-side sentence; (c) weak-side `Reducible` (needs a weak WP package, XL).
- **D16** [R3.3] → merged into D22.  **D17. SC-failure disclosure.**  (Rec) header names it; (b) §B(11) only.
- **D18. Fork-path coverage** — RULED [OWN.3]: W5d (M2) and W5d-G (D27) are in the target.  Residual: the
  user-fetch witness (whole-boot replay), W5d-G's non-vacuity gate — (Rec) not before Stage 2; (b) after M2 (XL).
- **D19. Dangling exclusive reads** [R2.3-alt][R3.2].  (Rec) `execProgOk'S` (fused pairs) as a named premise; (b) a
  MachCSL change so dangling reservations do not block (serial, L, **unverified**); (c) a user-mode fact — unavailable.
- **D20. Single-copy atomicity** [R3.4, Q-K][R4.4].  (Rec) `candSca` a named ISA-faithful premise at M1/M2 ONLY,
  derived at Stage 2 (`linCandSca`), absent from the published statement; (b) an atomicity axiom in sRVWMO — XL.
- **D21. Reporting M1** [R3.1, Q-L][R4.4].  (Rec) "composition milestone, kernel-only by premise `candKfetch`
  (`userinit`'s uncontended call), loads single-copy-atomic by premise `candSca`"; (b) report nothing before M2.
- **D22. Non-vacuity gate** [R3.3, Q-M][R5.s3].  (Rec) the `_entry` first-load witness (M–L; certifies the premise
  set is SATISFIABLE, not that any candidate reaches `allocproc`; QUIESCENT — says nothing about W13) gates M1; (b)
  follow-up.
- **D23. W1 via `xv6NiPhi`** [R3.s1, Q-N].  (Rec) accept the re-scope (S–M) in place of a new ledger export; (b)
  the rev-3 `allocprocLedgerAdequacy` hook (M).
- **D24. W8's export form** [OWN.2][R4.3][R4.s3].  (Rec) a per-state predicate on `g.m` + a ghost access ledger
  exported like `mmOk`, in `protReg`/`badSeg`'s vocabulary (§C W8) so it transfers through `R`'s log
  identification; (b) a new `Obs` per memory access (touches NI); (c) trace-free: `l2Claim`'s arms directly from
  W9a's check + ownership facts (smallest if the ~5 residue idioms close).
- **D25. The published quantifier vs N11** [R4.5, Q-Q] — RULED [OWN.5]: (a) cat-sound kill arms (rfi → `rsame`,
  `gcross` rfe-only, lock kit + `normalizeOfAcyclic` over `rvwmoCatConsistent`), confirmed and sized by W12-spike;
  (b) dropped; (c) RVWMO⁻ fallback NOT accepted.
- **D26. Stage-2 sequencing** [R4.s5][R5.1].  (Rec) M1 → M2 → {W12, W5d-G, W13} ∥ W8 (design after W2 + the
  THREE spike reports) → W9a/W10 → W11; (b) start W8 in parallel with Stage 1 (risk: `R` not fixed, export shape
  and site list may change).
- **D27. Fetches on the graph tier** [R4.2, Q-O] — RULED [OWN.6]: (a) a NEW graph-level Zifencei fetch model
  (W5d-G), a named trusted-base item; shape per W5d-G-spike.
- **D28. The pin residue** [R4.1, Q-P] — RULED [OWN.7]: (a) ALL 182 `PCall`/`PResidue` sites and the 58 sp-frame
  witnesses discharged through W8 for the published theorem; no interim named assumption.
- **D29. The fabric at the graph tier** [new, R5.1, Q-R] — RULED [OWN.8]: the dev-order model is a TRUSTED-BASE
  item of the published theorem (axiom `po ∪ rf ∪ gmo|W ∪ dev` acyclic), with T2-1c′ in scope (sizeable; W13).
  Device-quiet publication was never an option (vacuous for allocproc); `gdevAdj ⊆ gmo` as a strengthening rejected
  (FabInd §5: not realized by today's linearization).
- **D30. W3's export** [new, R5.2, Q-S] — RULED [OWN.9]: a SIBLING root `xv6TextAdequacy_closed`; existing root
  statements and the baseline untouched (new entries only).
- **D31. W13-wit timing** [new].  The `LDev` witness (hart 0 to `uartinitone`'s first `WriteReg`, ≈ 100 dynamic
  instructions by kernel evaluation): (Rec) build it right after W5c lands (its `esil → admRun` bridge is the
  mechanism) as W13's non-vacuity gate — the only pre-Stage-2 evidence that a device-active candidate exists; (b)
  defer to Stage 2 with the user-fetch witness (risk: W13's bundle shape unvalidated while T2-1c′ is built).
