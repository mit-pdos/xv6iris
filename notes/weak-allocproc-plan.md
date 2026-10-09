# allocproc on RVWMO: target theorem, gap analysis, roadmap (design advisor, 2026-10-09)

**Status: rev 10 = rev 9 + owner rulings [OWN.13]–[OWN.15] (`../weak-orch/allocproc_revise3_extra.txt`): D33 (a),
D34 (a), D35 (a), D36 (a), D39 (a) RULED [OWN.13]; D40 (a) RULED [OWN.15]; **D38 RULED [OWN.14]: MMIO accesses are
I/O-CLASS GRAPH EVENTS** (ordinary load/store events to I/O-PMA addresses, in gmo, ppo applies, values from the
device, outside the load-value axiom) — NOT admin-only trace steps.  W13 REDESIGNED (§A(†), §B(11), §C): the
trusted I/O item is now an INCLUSION `ioResidueGmo` over I/O events (replaces `ioObAcyclic`'s `Ioev`/`ioOrd`
encoding), the realization interface keeps `execProgOk'` (no `execProgOkA`), the alphabet gains `Lbl.LIo` and
`Wlabel.LDev` a payload (merged files, accepted).  [OWN.1–12] kept; no review since R7.**
**One-liner [R6.s1][R7.2a][OWN.12][OWN.14]: the published quantifier is riscv.cat RVWMO with TAGGED dependencies
(`rvwmoCatConsistentT`) over graphs whose rows CONTAIN the I/O accesses as events, plus an I/O-ordering PLATFORM
assumption (`ioResidueGmo`: BEYOND what ppo gives those events — nothing from FENCE (Sail drops the i/o bits) or
dependencies, rule 5 only — a row's RAM accesses po-before an I/O event and its RAM STORES po-after it are
gmo-ordered on that side of it, and I/O events are gmo-ordered as the fabric serializes them — the residue is what
QEMU TCG gives and RVWMO + PMAs do not) and a graph-tier Zifencei fetch model (`gzFetch`) — two named trusted-base
items with no reference model.  Non-vacuity past boot: W14 (D44 (i), RULED).**
History: rev 1 (2026-10-09) survey; rev 2 `…-review-R1.md` (11 req.; D8–D13); rev 3 `…-R2.md` (5 req., two
[R2.n-alt]; D14–D19); rev 4 `…-R3.md` (4 req.; D20–D23) + [OWN.1–4]; rev 5 `…-R4.md` (5 req.; D25, D27, D28); rev 6
`…-R5.md` (3 req.: quiescence VACUOUS → W13; W3 sibling root; `pairAdjacent`) + [OWN.5–9]; rev 7 (2026-10-09)
`…-R6.md` (5 req., s1–s4) + spikes: tagged cat model; a THIRD cat gate (W12b); `devAcyclic` REFUTED → `ioObAcyclic`
(provisional); T2-1c′ LANDED, W13 = XL; fetches ADMINISTRATIVE (`gzFetch`, cut form); W5b owns `execProgOk'S`; D32–D43;
rev 8 (2026-10-09) `…-R7.md` (4 req., s2–s6): `ioObAcyclic`'s `dv → read` arm DROPPED (a′); "strongly-ordered I/O"
renamed (MMIO-as-fence, host-dependent); the disk agent's row a first-class W13 object; the user-fetch witness is
INFEASIBLE by evaluation → non-vacuity past boot OPEN; D32/D37 revised, D44–D45; rev 9 (2026-10-09) [OWN.10–12]:
faithful I/O evaluated (§B(11b)) — infeasible, (a′) RULED with the residue reading; D37 (a) RULED; D44 (i) RULED →
W14; spike files frozen; D46 NEW (the `ioOrdF` residue audit); rev 10 (2026-10-09) [OWN.13–15]: D33–D36, D38–D40
RULED; W13 redesigned around I/O-CLASS EVENTS (`Lbl.LIo`, `ioResidueGmo`, `ptraceRelIO`, `racyDIO`); D47–D50 NEW.

**The kernel [OWN.4][R1.9]: xv6-riscv `b72cbac1`, branch `verified`** (`notes/STATUS.md:8-11`, `README.md:89-90`)
= upstream plus (a) a per-process root (`p->root`, `sys_chroot`, `igetroot`, root-aware `dirlookup`/walk) and
(b) upstream's post-`ded23f2` allocpid — bounded counter `PIDMAX = 1000` (`Xv6/ProcGeom.lean:80`) with a 64-slot
liveness scan, inlined by gcc into `allocproc+0x38..+0x94` (`claude-notes/kernel-defects.md:224-231`) — not the
textbook monotone `nextpid`.  Image `Xv6/KernelImage.lean` by `tools/dump_kernel.py`.

Advisory only; read-only survey of `../xv6iris-weak` (`Weak/`, `Xv6/`, `MachCSL/`, `notes/weak-memory-*.md`,
`claude-notes/{completed,design}/*weak*`).  Sizes: S ≤ 300 lines, M ≤ 800, L ≤ 2k, XL = multi-week / many files.
Unconfirmed claims are **unverified**.  Spike scratch files (build, no `sorry`): `Weak/CatOfMinusSpike.lean` (399),
`Weak/W13Spike.lean` (145), `../xv6iris-weak-w3/Weak/GraphFetchSpike.lean` (226; `propext, Quot.sound` only) — the
latter exists ONLY in the `-w3` workspace (its report is merged as `notes/W5dG-spike.md`).  **[OWN.10]: the two merged
spike files STAY; NOTHING else is merged (GraphFetchSpike stays in `-w3`) until the plan is SATISFIED** — W5d-G's
day-one merge step (§C) is gated on that verdict; this plan's `GraphFetchSpike.lean:N` cites refer to the `-w3` file
until then [R7.s3].  `W13Spike.lean` §3 (`Ioev`/`ioOrd`/`ioObAcyclic`, `:83-116`) is SUPERSEDED by rev 10's
`ioResidueGmo` (§A(†)); its §1–§2 refutations (`lbExcluded`, `scDevExcluded`) stand.

## 0. The two findings that reshape the question

**F1. allocproc is ALREADY fully verified in this tree — on a weak-memory machine, not on SC.**
`Xv6.Allocproc : ALLOCPROC` (`Xv6/LinkAllocproc.lean:14-16`, proof `Xv6/ProofAllocproc.lean:3623-3639`, 3.6k
lines; spec `Xv6/SpecAllocproc.lean:118` `allocprocPost`, `:204` `wp_allocproc_body`) covers the whole function on
the real image (0x80001b72..0x80001c72): the `proc[]` scan with `acquire`/`release` per slot (interrupts may be ON,
migrating hart via `wpNext`), the inlined allocpid under `pid_lock` with the 64-word collision scan (Löb-closed,
`PidLock.pidLedger`/`pidTie`, `Xv6/PidLock.lean:88,113`), `kalloc`, `proc_pagetable` with PTE writes into fresh OWNED
pages (`pptPost`), `memset`, `ra = forkret`, `sp = kstack + PGSIZE`, both failure tails through `freeproc`,
`p->pid`/`p->state` as `p->lock`-protected cells (`procHeld`).  Callees verified too (≈ 10.7k lines).  In the cone
of the audited roots (`tools/ci/roots.txt:6` `xv6FsAdequacy_closed`, via `Xv6/LinkSyscall.lean:84`/`LinkMain.lean:53`),
whose baseline (`tools/audit/baseline.json:11-14`) has axioms `propext`/`Classical.choice`/`Quot.sound` and exactly
three opaques: `LeanRV64D.Functions.xv6_resv_is_valid`, `…xv6_resv_matches`, `MachCSL.bootImageSealed` [R7.s6].

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
   tier the rows are `xN σ0 = (epsInit σ0).length = NCPU + 1` (`Capstone.lean:94`): 8 harts PLUS the disk agent's
   row `.PDisk none` (`WeakEvCapstone.lean:1027`, booted by `xboot`, `Capstone.lean:90-91`) [R7.3]; device-ACTIVE
   candidates exist only once W13 lands, today's bundle is device-QUIET [R5.s5][R5.1];
3. memory [OWN.2]: **RVWMO as the ISA defines it — the TAGGED cat model `rvwmoCatConsistentT GT` over `GdexecT`
   (`Weak/AxDeps.lean:208-211`: `gwf ∧ gppoCatTGmo ∧ gloadValue ∧ gatomicity ∧ gtdepsWf ∧ gtdepsGmo`, rule 12 over
   `gtAd` = the addr/data edges only; rules 1–5, 7-RCsc, 12; omits 6, 7-RCpc, 8; fidelity by litmus,
   `Weak/AxLitmus.lean:29`)** [R6.1].  **NOT the untagged `rvwmoCatConsistent` (`Weak/AxGraphCat.lean:191-194`)**:
   its `gppo12` ranges over the untagged `gdDeps` and so also orders `ctrl;[W];rfi;[R]`, which riscv.cat does NOT —
   the tree calls it "UNSOUND for safety" (`AxDeps.lean:12-18`), machine-checked by `twCatT :876` with
   `twNotCatForget :883`; `catTOfCat` goes cat→tagged, the converse fails (`:22-27`).  The chain runs on `forget GT`
   (W12 spike F1; D33 RULED (a) [OWN.13]).  **I/O accesses are events of the rows** [OWN.14]: `gmem` (hence gmo,
   `gwf`'s membership clause, `Graph.lean:169-171`) includes the new `Lbl.LIo` labels; ppo applies to them as
   riscv.cat is written (§B(11)); their values are device-supplied (no `lbRd`, so `gloadValue`/`grf`/`gfr` are
   vacuous for them BY CONSTRUCTION).  W→W reordering and load buffering ALLOWED; every strengthening NAMED;
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
   `Xv6/UartTrace.lean:182`), M–L, new work — D9.  **Caveat until W14 lands (D44 RULED (i) [OWN.11])** [R7.4b]: the
   evaluation witnesses certify satisfiability only up to the first UART store (W13-wit) and the first disk COMMIT
   (W13 (W) gate 2); the evidence that a candidate REACHES `allocproc` is W14's single-execution existence theorem
   (§C Stage 2) — until it lands the header says "non-vacuity certified to the first UART store / disk COMMIT";
6. axioms `propext`/`Classical.choice`/`Quot.sound` + `bv_decide` certificates + the three opaques
   (`tools/audit/baseline.json:11-14`), no `sorry`; trusted base named: Sail model, image dump, the TAGGED cat
   transcription and its tagged conformance text `gdexecQconfT` (new trusted-SURFACE text, reviewed against
   `rowDepsT`'s correction (5), `AxDeps.lean:56-60`) [R6.1], the graph-tier fetch model (W5d-G `gzFetch`, §B(4)(iii);
   RULED [OWN.6]), the graph-tier I/O-ordering PLATFORM assumption (W13 `ioResidueGmo`, the (a′) arms of D32
   [OWN.12] restated over I/O-class EVENTS [OWN.14]: a row's RAM accesses po-before an I/O event, and its RAM
   stores po-after it, are gmo-ordered on that side of it; I/O events are gmo-ordered as the fabric serializes
   them — the residue over what ppo gives I/O events, §B(11)) [R4.2][R5.1][R6.3][R7.1][R7.2].

**Legitimately out of scope:** liveness/fairness, timing, mixed-size fidelity of the cat model (N10), MMIO
ordering beyond the modelled devices, hardware outside the Sail model, power cycles (SINGLE ERA [R2.2]).

**The statement to aim for — three layers.**  *T-alloc* (contract, exists): `Xv6.Allocproc` on MachCSL.
*M1/M2 (internal milestones, NOT published [OWN.2])*: the composed sRVWMO theorem, pinned/kernel-only (M1) then
unpinned (M2), below.  *T-alloc-RVWMO (THE published claim)* [OWN.2][OWN.3][R3.1][R3.2][R3.4][R4.2][R4.4][R5.1]
[R6.1][R6.3]:
```
∀ (σ0 : WGState) (GT : GfexecT),             -- NEW: the fabric bundle (Weak/WeakRvwmoFab.lean:516) over GdexecT
  wbootFacts σ0 ∧ σ0.wggen = 0 ∧ (∃ ds, σ0.wgdev = ds.reset ∧ diskOf ds = fsImgDisk) ∧        -- the boot [R2.2]
  rvwmoCatConsistentT GT.gfGd ∧        -- riscv.cat, TAGGED deps (AxDeps.lean:208) [R6.1]; rows contain `LIo` events
  ioResidueGmo (forgetF GT) ∧          -- I/O-ordering platform assumption over I/O EVENTS: (R1)–(R3) ⊆ gmo, §A(†)
                                       -- (the (a′) arms of D32 [OWN.12], re-encoded per D38 [OWN.14])
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
**NEW names — none exists in any merged file; workers must not grep for them** [R7.s2]: `GfexecT`, `GT.gfGd`,
`forgetF`, `xv6ConfS`, `gfexecConfIO`, `execProgOk'S`, `pairAdjacent`, `candSca`, `candKfetch`, `textPristine`,
`Gdexec.gdFetch`, `emZifencei`, `gzFetch`/`gzContrib`/`emFenceI` (scratch only), `rvwmoCoreD`, `rvwmoCatAD` (scratch
only), **`Lbl.LIo`/`IoKind`/`lbIsIo`/`gisIo`/`ioResidue`/`ioResidueGmo`/`gfBefore`/`ptraceRelIO`/`gnxa`/`racyDIO`/
`cycleKillIO`/`mstep.MStepIo` (rev 10)**, `Ioev`/`ioOrd`/`ioObAcyclic` (scratch only, SUPERSEDED), `execProgOkA`/
`gfexecConfA` (rev 9 names, RETIRED by D38), `ioOrdF`/`emIoFence` (D46 (b) only, §B(11b)), `badSeg`, `linCandSca`,
`xv6RvwmoSafeModuloT`, `pidPick_range`, W14's `Weak/ExistWitness.lean`.
(†) `xv6ConfS` is the SHAPED, UNPINNED, FABRIC-ORDERED, TAGGED conformance bundle [R5.1][R6.1][R6.3][R6.4][OWN.14]:
`gfexecConfIO` (W13 (I)/(W): per-row `hartConff` emissions with TWO fabric endpoints, `Fab.lean:261-263`/`hemitf
:238-260`; an I/O access is a TAGGED row item `(l, some k)` whose `pstepEv` moves the fabric `dvi k → dvo k`, so
`gfDev : List Geid` (`Fab.lean:516-518`, type unchanged) lists the I/O EVENTS in fabric order and the clause
`isDevBlock em k ↔ (i, k) ∈ gfDev` (`:530`) becomes `gisIo (i, k) ↔ (i, k) ∈ gfDev`; admin stars carry NO fabric
move), `fab 0 = efInit σ0.wgdev`, `rowDepsT` tags in `GT.gtDeps` (`gdexecQconfT`-style; `rowDepsSubT`,
`AxDeps.lean:690`, gives the untagged bundle back), the fetch clause `emZifencei` (W5d-G, replacing `emFetchImg`,
`Fab.lean:534`/`Supply.lean:277-278`) with `F_em ⊆ GT.gdFetch`, exclusive pairs FUSED (the `execProgOk'S` shape of
[R3.2], DEFINED by W5b [R6.4]) — NOT today's quiescent `gdexecQconf` (`Weak/WeakRvwmoSupply.lean:281-289`), whose
`emDevfree` (`:273`) forbids every `LDev`.  **Quiescence is VACUOUS for allocproc** (W13 spike CONFIRMS): the event
LTS emits `LDev` for EVERY MMIO access (`Weak/WeakEvInst.lean:300-303,335-338`) and the disk row's START/COMMIT
(`:484,502`); hart 0's `main` runs `consoleinit` FIRST (`Xv6/SpecMain.lean:7-10`) = `uartinitone`'s seven `WriteReg`s
(`Xv6/SpecUartinitone.lean:6-13`), so `userinit → allocproc` is unreachable in EVERY quiescent `GD` (route-b: "HONEST
MILESTONE", `weak-memory-route-b.md:1009-1020`); no `LDev`-emitting witness exists (`gfexecConfOfQconf`, `Fab.lean:648`).
**THE I/O ITEM, rev 10 (D38 RULED [OWN.14]; D32 (a′) and D37 (a) [OWN.12] carried over)** [R6.3][R7.1][R7.3a]:
[OWN.8]'s literal axiom IS `gfexecConsistent'` (`Weak/WeakRvwmoLin2.lean:761-762`), which forbids LB and W→W even at
an EMPTY fabric (`lbExcluded`, `Weak/W13Spike.lean:35`) and subsumes the kill — a robustness ASSUMPTION, not a
hardware model; and EVERY block-level dev condition (`gfexecConsistent'`, `gdevAdj ⊆ gmo`, `Fab.lean:539-544`)
excludes SC executions (`scDevExcluded`/`scDevUnrealizable`, `W13Spike.lean:55,66`) because `execProgOk'`
(`WeakAxRealize.lean:373-386`) folds the `LDev` admin block into the NEXT tagged event.  **Rev 10 removes the cause
instead of the condition: an I/O access is its OWN graph event `Lbl.LIo kind base vs`** (D47; `IoKind = rd | wr |
dev`), a `gmem` event with its own gmo position, in EVERY row `i < xN σ0 = NCPU + 1`: a hart's MMIO reads/writes
(`pnodeStep`, `WeakEvInst.lean:300-303,335-338`, today `LDev` without payload), the PLIC pin delivery to a hart
(`pstepPlic :461-466`, kind `dev`), the disk agent's START/COMMIT (`pdiskProg :481-507`, arms `:484,502`) AND the
device threads' fabric moves at the disk agent (`pdiskUart :514-520` — UART tx/rx, PLIC gateway; rev 9 MISSED this
fourth `LDev` source) — all kind `dev` [R7.3a][D49].  `lbRd`/`lbWr` are `none` on `LIo`, so rf, co, fr, load-value,
atomicity and the log message `gmsg` (`Lin.lean:463`) ignore I/O events BY CONSTRUCTION (device-supplied values,
[OWN.14]); `lbIsR`/`lbIsW` stay RAM-only, so rule 4 (`gfenceCovers`, `Graph.lean:190-194`) and rule 7 skip them —
Sail's `execute_FENCE` keys on `extractLsb pred 1 0` only (`InstsEnd.lean:18299-18313`), the i/o bits never reach
`LFence`, so the graph can give I/O events NO fence edge (D48); rules 1–3 give none (`gaccesses` is byte-footprint
based); rule 5 `gacqPo`'s `gmem e2` (`:200-201`) DOES order an acquire read before a later I/O event (cat-literal;
under the prose reading (F4) a strengthening — subsumed by (R1), vacuous as a trusted use); dependency edges through
`LIo` are OFF by default (D50).  **The trusted item is an INCLUSION, no longer an acyclicity over an extended
order** — gmo is already total over `gmem`: `ioResidueGmo GF := ∀ x y, ioResidue GF x y → gmoLt GF.gfGd.gdG x y` with
**(R1)** `gpo x y ∧ gmem x ∧ ¬ gisIo x ∧ gisIo y` (a row's RAM accesses po-before an I/O event, READS included);
**(R2)** `gpo x y ∧ gisIo x ∧ gisW y` (an I/O event po-before a row's RAM WRITE — exactly `grule14`'s shape,
`Graph.lean:255-256`, with `gmem` now covering I/O; reads po-after stay UNORDERED, the (a′) point [R7.1]); **(R3)**
`gisIo x ∧ gisIo y ∧ (gpo x y ∨ gfBefore GF x y)` (same-row issue order — ISA-given only within ONE channel (F2),
cross-channel it is residue — and fabric order, stated on the ORDER `gfBefore`, not `gdevAdj`, so hulls that cut I/O
events out keep it).  Free when no row has an I/O event (`ioResidueNodev`, the `ioObAcyclicNodev :109` rank proof
re-done) so LB and W→W stay in the quantifier; admits the SC case (`w13f` re-encoded: gmo `MMIO₀ < MMIO₁ < st < ld`
is now a GRAPH, the `w13fIoOk :116` re-check is W13 (T)'s acceptance); does NOT assume `racyD` acyclicity — the kill
carries that.  (R1)/(R2) are REALIZATION-NECESSARY and ISA-given at three xv6 sites only (§B(11b)); the strong
model lacks a read arm (`elabOk σ c LDev = True`, `WeakEvInst.lean:558`; TsoMem's MMIO arms touch only `devs`,
`MachCSL/Lang.lean:356-358,372-375`) and nothing needs it (reads have no cross-hart OUT-edge in `ptraceRel`,
`Lin2.lean:124`).  For the disk row (R1) says "DMA writes (plain `LStore`s, drained by `LFence true true true true`,
`:497-498`) are gmo-before COMMIT" — device-MODEL semantics, the one place (T) carries disk correctness [R7.3].
`candSca` is NOT a premise here:
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
W4 projects `wpPfRun` runs.  (ii) W2's (↓) `LIFetch` row carries the content: the pf fetch is admissible at floor 0
(`PFIFetch`, `Weak/WeakPromiseBridge.lean:441-449`) while TsoMem fetches as the i-cache agent at `σ.itv cpu ≤ tvn ≤
top` (`MachCSL/Lang.lean:360-362`); the row closes iff no log write hits the fetched bytes between the version read
and `itv`.  THE TsoMem-side mechanism [R5.s4][R5.2]: kernel text is held as `imgByte a v := ∃ tid, a ↦ₕ□ [⟨0, tid,
v⟩]`, a DISCARDED-fraction singleton HISTORY (`MachCSL/Ctx.lean:433-436`), assembled into `kernelText`
(`Xv6/KernelText.lean:25-30`) from `bootRo … bcRoLo bcRoHi` (`Xv6/BootCarve.lean:582`; window `[ramBase, _data)` ⊇
text + rodata); against the auth heap it reads the image byte at EVERY view (`MachCSL/Wp.lean:1478,1490`) and a DMA
write needs `DFrac.own 1` (`MachCSL/WpDma.lean:142-145`) — so `candKfetch` (every `LIFetch` footprint ⊆ `[bcRoLo,
bcRoHi)` ⊇ `[text, etext = 0x80007000)`, `Xv6/KernelImage.lean:771`) is dischargeable for kernel text (W3), NOT for
user pages (`own 1` cells).  **[R3.1] The pin does not make a candidate kernel-only**: a pinned fetch is pf-admissible
AT ANY LOG (`fetchPinIfetchOk`, `WeakAxRealize.lean:167-176`; `WeakPromise.lean:228-231`), the program LTS constrains
the fetched value only through memory (`pstepEv`'s i-cache arm, `WeakEvInst.lean:306-312`), and the boot image is
ZERO past the ELF (`bootByte_zero`, `MachCSL/BootImage.lean:31` [R6.5a]) — a conformant pinned candidate can run
`userinit → scheduler → userret (fence.i) → sret` and fetch zeros at the user page while TsoMem's `itv` has passed
`uvmfirst`'s writes: W4's `LIFetch` row has no TsoMem step.  Fix: M1 carries `candKfetch` inside the shaped
conformance predicate; W3 discharges the row ONLY under it.
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
D40).  Scratch status: proved `fetchCutOk`, `fetchCutPrefix :63` (cut form = the pf/W5d check at the realizing
prefix with ONE view), `fetchCutEdge :83`, `fetchRelOk`, `fetchRelCut :140`, `fetchPinCutOk :213`; stated `gzFetch`,
`gzFetchCut`, `emZifencei`, `gfcut`, `gwlog`.  **Kernel-text instance**: tag 0, image bytes, no write ⇒ (Z1)–(Z3)
vacuous; `candKfetch` + W3's history fact discharge `gzFetch`; kernel-only executions get an EMPTY fetch fragment.
Consumption (details `W5dG-spike.md`): edges E1 src→nxw, E2 c→w', E3 src_l→w'_j, `gmoLt` on `GD` by (Z2)/(Z3),
stored as `Gdexec.gdFetch` (D42), `F_em ⊆ GD.gdFetch` in `xv6ConfS`; retime via `L ⊇ racyD ∪ F` (the contributor SET
is rf/po-defined, hence retime-invariant — `normalizeOfAcyclic` renames write indices NON-monotonically,
`WeakRvwmoTopo.lean:594-607`, so no max/cut condition transports); realize by replaying the fetch just before
`(i,k)`'s step at log `gwlog.take gfcut` (`linPrefixLog`), `fetchCutPrefix` giving `ifetchOk` and the single view `q`.
Measured sites: `pstepPin` 19 files/121, `emFetchImg` 10/41, `gdexecQconf` 18/124, `gdDeps` 31/133, `wlblRen` 3/41.
Sizes: W3 M–L [R5.2]; W5d L; W5d-G L (G1–G5; G6 shared with W11 (iii); G7 L in W11/W8); **XL risk R1 — hull
closure**: `hullOk` is
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
class; (β) `WeakPromise*` (`Weak/WeakPromise.lean:1-16`) — LB reachable, RVWMO fidelity BY INSPECTION only; (γ) PSO
two-log machine: Rocq-only design, NOTHING in Lean; (δ) graphs: the tagged cat model (§A(3)), the untagged
`rvwmoCatConsistent`, `rvwmoMinusDepsConsistent` (`WeakRvwmoGraph.lean:628`).
**`minusImpliesCat` (`Weak/AxGraphCat.lean:274`) runs the WRONG way for us**: RVWMO⁻ renders rules 1–3 as all of
`gpoloc` (`WeakRvwmoGraph.lean:224-228`), ordering a write before its own po-later same-byte read — it FORBIDS
store-buffer forwarding (N11, `AxGraphCat.lean:10-16`), so a theorem over RVWMO⁻ misses cat-consistent executions.
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
verbatim as `*C`.  **Gate 3 (the certification walk's floor kit — W10's toolkit) BREAKS, needs a REDESIGN**: `gvisUb G
r n` = "every write of index ≤ n is gmo-before r" (`Weak/WeakRvwmoFloor.lean:100-101`) is FALSE under cat for an own
store forwarded to a po-later read (it may be gmo-AFTER); `greadSrcUb` (`:442-453`) closes its po case with
`gpolocGmo` W→R, `finvStep` (`:605-619`) uses it for the coh hook; consumers `cinvReplay`/`floorOfCgraph`/
`certFloorOk`/`cpolRead` (`Cert3.lean:311,391,428,468`) via `wblkPolAt` (`Walk.lean:700-731`).  The FLOOR itself holds
(`t = gwix w`; co-maximality covers po-visible writes) but needs a per-byte coherence invariant (rules 1/2) in place of
`gvisUb` — Floor §4–§6 and Cert3 §2–§3, ≈ 0.5–1k (M–L) = **W12b** (D34).  Two smaller mismatches, VACUOUS for kernel
rows (release = `fence rw,w; sw`, `Xv6/ProofRelease.lean:83-86`; acquire = `amoswap.w.aq`), OPEN for user rows
[OWN.3]: the `wVRel` hook consumes rule 7 RCpc (`Floor.lean:21`), which `grcsc` (`AxGraphCat.lean:163`) lacks (D35);
WeakMem's forwarded ACQUIRE load (`fwdView ws true a t = t`, `WeakMem.lean:585-591`) is stricter than cat (D36).  **So
the gap is CONFINED to the kill AND the walk floor** — not the 33k lines.  Witnesses need NO re-proof (`catADOfMinus`
∘ `minusImpliesCat`; corrects [R5.s1]).  Residual premises `l2ClaimAt`/`cutSupply`/`certSupply`/`walkSupply`/
`walkPolicy` are re-hypothesised; their discharges (W8–W11) must handle FORWARDING graphs (TsoMem forwards — fine).
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
  `tools/gen_weak_pins.py` (1,004; `--check`); `imagePinnedb`/`pinsCover` (`KernelPins.lean:1817-1860`); `pinSegPin`
  (PDep ⇒ `rowDeps` ⇒ `gdDeps` ⇒ `segPin`, `WeakRvwmoPinBridge.lean:284-330`) and `pinSegPin'` with
  `checkerTaintSubProv` DISCHARGED for the oracle `psites` (`PinBridge2.lean:530-553`); the callee-summary table is
  an audit artifact nothing reads (`route-b.md:1456-1460`).  **W9b**: the non-certifying classes are W8's INPUT, not
  `segPin` — `PStack`/`PPerCpu` (1,037) = W8's ownership (i), the 58 `own = true` witnesses rest on the same fact,
  `PCall` 63 + `PResidue` 119 = 182 sites = W8's (ii)/(iii) (D28 RULED (a) [OWN.7]).  Work items W8–W13 are specified
  in §C Stage 2.  Sizes (✓ = spike-confirmed): W8 L–XL, W9a L (M–L + M ✓), W9b in W8, W10 M–L (**unverified**; L if it
  absorbs W12b), W11 L [R4.3], **W12 M–L ≈ 1.2–1.8k ✓**, **W12b M–L ≈ 0.5–1k ✓**, **W5d-G L ≈ 1.8–2.2k ✓ + XL risk
  R1**, **W13 XL ✓, re-sized in rev 10 ≈ 7–10k lines / ~70 files touched** (the alphabet sweep (E) is wide and
  shallow; the (R) re-thread is the bulk; `execProgOk'` keeps its shape).  **Total: XL** —
  multi-week, many files; W13 the bulk, W5d-G's hull closure the open risk, non-vacuity at allocproc = W14 (D44 (i)).
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
(`candSca`, below).  **It exists in NO file** (only `execProgOk'Snoc`/`SnocPair`) — **W5b DEFINES it AND
`pairAdjacent` on day one** [R6.4c], over the STEP LIST; under D38 RULED [OWN.14] the I/O step is an ORDINARY left-arm
realizing step (`l = LDev kind base data …`, `projLbl … = some (.LIo …)`), so the shape clauses (fused left arm;
label-carrying `admRun`s; no foreign step between pair halves) need only an `LDev` case — the rev-9 co-design with
`execProgOkA` is gone.
**`pairAdjacent`** (NEW, coined by R2; ONE text for W2 and W5b [R5.3]): *in a shaped run every realized exclusive
pair's halves `l1 = LExLoad …`, `l2 = LExStore …` (`lblRealizesPair`, `WeakAxRealize.lean:305-313`) are consecutive
steps of the SAME hart up to its own `LInstr`-free star `admStar pstep false pm dm pm2 dm2` (`execProgOk'`'s right
arm, `:380-386`, one exec index); no other agent's step — no foreign store — lies between them*, plus the fetch/SCA
facts along the run; W5c must PRODUCE it (`execProgOk'Snoc`, `Weak/WeakRvwmoCert.lean:413`, yields plain
`execProgOk'`; an S-variant is needed).  At Stage 2 `RunData`/`cstOk`/`segStep`/`topoSupply`/`t2linSupply` (plain
`execProgOk'` today) produce the S-variant — W11 (iii) [R4.3], one pass with W5d-G's G6 (`pstepPin` →
`execProgOk'S`, 19 files / 121 sites: AxRealize 26, Supply 14, Cert 9, Cert2 8, Fab 7, Cert3 7, SrvwmoCapstone 6,
CycWit 6, Cert4 6, AxAdequacy 6, Cert3b 5, LinInd/Lin2/FabInd 4, Capstone 3, Glue/ConfWit2 2, Glue2/AxRunGV 1 —
the one list; §C cites it).
**[R3.4] (↓) fails on PLAIN LOADS even on shaped runs — tearing.**  WeakMem's `readable` is per byte
(`Weak/WeakMem.lean:400-402`; `readOkD`, `WeakPromise.lean:183-188`; `rdOk`, `WeakAxiomatic.lean:122-130`), no axiom
joins one label's bytes (N10); TsoMem reads every byte at ONE `tvn` (`Lang.lean:363-367`).  Counterexample: whole-word
stores `S1@4`, `S2@6`; a floor-0 load with `ts = [4,4,6,6]` is admissible and sRVWMO-consistent; TsoMem yields all-`S1`
or all-`S2`.  RMWs exempt (`rmwLatest`, `WeakAxiomatic.lean:134`); fetches have the cut form (§B(4)(iii)) as their SCA.
The ISA guarantees single-copy atomicity for naturally aligned accesses ≤ XLEN, so the premise is ISA-faithful — NAMED
**`candSca c`**: every `LLoad` reads at one view — `∃ tvn, ∀ j, ts[j]` is the latest write to byte `j` at or below
`tvn` or the hart's own later store (TsoMem's forwarding clause).  Carried by W5b; W2's "plain load" row is (↓) iff
`candSca`; alternative = an atomicity axiom in sRVWMO (re-opens T1, XL) — D20.  **At Stage 2 `candSca` is DERIVED**
[R4.4]: `gloadValue` (`Weak/WeakRvwmoGraph.lean:238-243`) puts ONE gmo position per LOAD EVENT — each byte's source
`gvisible` (`:236`) and co-MAXIMAL among visible same-byte writes — so a torn read is already inconsistent;
`topoSupply` linearizes the NORMALIZED `GD'` and `linCand` (`WeakRvwmoLin.lean:471`) copies labels, so `linCandSca :
rvwmoMinusConsistent G' → grule14 G' → candSca (linCand G')` (S, W11) feeds W5b's replay; `fetchCutPrefix` (W5d-G)
plays the same role for fetches.
*(↑) receptiveness is NOT available on route (M)* [R2.3(iv)]: weak-side `Reducible` would need the weak WP package;
(a) is stated for the realizing MachCSL run, the free weak-side sentence is "the realized pf run never enters the
retry arm" (D15).  *Single era* [R2.2]: `epowerFork` forks no power thread (`Weak/WeakEvLang.lean:201-204`), so
multi-era conclusions are NOT transported; W4's run is prefixed by the `PowerOn` step (D14).
*The relation `R`* [R2.s3][R3.s3][R3.4], fixed in the spike report: TsoMem `tv ↔ max wVrNew (own last store)` —
**the `.aq` off-by-one** [R3.s3]: at an acquire pair TsoMem's `tv` becomes the WRITE's timestamp `top + 1`
(`MachCSL/Lang.lean:150`), WeakMem's `wVrNew` the READ's (`exloadPostRunD`, `Weak/WeakMem.lean:834`; `:634-647`);
`rv ↔ wVrOld`, `ownPub ↔ wVwOld`, `coh ↔ wCoh`, histories = log projection (`Lang.lean:147-153` ↔ `σ.wglog`), image
`imgZ ↔ imgFlat`, `resv ↔ wRes` only mid-pair; the pf machine has no `itv`, so `R` carries `itv ≤ q` for every fetch
cut (W3 / W5d) [R6.4b] and the load row `candSca`'s `tvn`.  Spot checks (↓): `fencePost` raises `wVrNew` to `max
wVrOld wVwOld` for `pr,pw` (`WeakMem.lean:674-678`); `fence rw,rw`/`r,r`/`rw,w` agree.  Open per label: parked `fence
rw,w`/`wRelp` (`:684`) vs TsoMem's no-op; `wRes := none` at any non-trivial fence (`:688`) vs TsoMem keeping it; the
`.aq` carried bit (`MachCSL/TsoMem.lean:255-280`); the i-fetch agent vs `LIFetch`; devices/DMA (`Efab` vs
`MState.devrt`; `anyReserve`).  Size: L (↓) + L (W4) + M (W5b) + M (W5) + M–L (W5c) + L (W5d).  It lifts the WHOLE
system theorem; (9d) reuses it in both directions; **the log identification carries `protReg` and `¬ badSeg`** (W11).

**(11) Model fidelity and named assumptions (trusted base, list in the header)** [R1.1][R1.7][R2.4][R3.1][R3.2]
[R3.4][R4.2][R4.4][R6.1][R6.2][R6.3].  Candidate/conformance premises: `execProgOk'S` (fused exclusive pairs — "a
dangling LR or failing SC is outside the theorem", D19; M1 only: `candKfetch`, D21); `candSca` (ISA-faithful; **M1/M2
ONLY** — derived at Stage 2, D20); cut-form Zifencei admissibility of pf fetches (M2); **the published model is the
TAGGED cat transcription** `rvwmoCatConsistentT` + the tagged conformance text `gdexecQconfT` (NEW trusted-surface
text; the untagged model's rule 12 is a strengthening of riscv.cat the tree marks UNSOUND — D33); **the graph-tier
fetch model** (W5d-G `gzFetch`/`emZifencei`, readings (H1)–(H3), §B(4)(iii) — NO reference model, RVWMO has no
instruction-fetch model; D27 RULED (a) [OWN.6]); **the graph-tier I/O-ordering PLATFORM assumption** (W13
`ioResidueGmo`, §A(†); D32 RULED (a′), D37 RULED (a) [OWN.12], D38 RULED [OWN.14]): the I/O events of every row — a
hart's MMIO accesses, PLIC pin deliveries, the disk agent's START/COMMIT and the device threads' fabric moves — are
gmo-after the row's RAM accesses po-before them (R1), gmo-before its RAM STORES po-after them (R2), and gmo-ordered
by issue order and by the fabric (R3); no reference model [R7.1b][R7.3a].  **Stated as a RESIDUE** [OWN.12], now
split EXACTLY: the GRAPH MODEL gives I/O events rule 5 (acquire read → later I/O) and NOTHING else — no rule 4 (the
i/o bits die in Sail's decoder, `InstsEnd.lean:18299-18313`; `LFence` is `pr pw sr sw`, `WeakAxiomatic.lean:90`), no
rules 1–3 (no byte footprint), no dependency edges (D50 default) — while the ISA PROSE additionally gives (F1)–(F6)
(§B(11b): FENCE i/o bits, dependencies into a device store, precise traps, same-channel order, the device models),
expressible only via D46 (b); the ASSUMPTION is the rest — each I/O access acts as a ONE-WAY FENCE for the issuing
row's RAM accesses, and I/O accesses serialize as the fabric does.  "PMA strong ordering" is NOT a
justification (it orders I/O accesses within one channel among themselves, never against main memory; D37(c) dropped)
[R6.3ii][R7.2b].  The platform named: hosts whose MMIO path performs the row's prior RAM accesses before the device
sees the access and holds later RAM stores behind it (QEMU TCG: program-order execution per vCPU + the BQL around
MMIO) — host-dependent.  **Trusted USES, per arm** [R6.s4][R7.2c][R7.3d][OWN.12], list in the header: (R1) for RAM
STORES before an I/O event — `plicinithart`/`plicinit`, `uartinitone`'s seven `WriteReg`s, the lock's store half and
prior stores before `uartputc_sync`'s LSR read and before `virtio_disk_intr`'s STATUS read; (R2) for every device
STORE not followed by a PO-fence — THR, NOTIFY (`0x80005c92`), `plic_complete`, `plicinithart` (only the ACK at
`0x80005d52` is fence-covered — and under D48 (a) even that is a trusted use at the GRAPH tier); (R3) cross-channel
issue order (UART then PLIC in `main`) and the unlocked cross-hart PLIC claim/complete races.  NOT trusted uses in
the ISA-prose sense (but GRAPH-tier uses until D46 (b)): the pre-NOTIFY direction (two `fence iorw,iorw`), the
post-ACK loads (the third fence), loads before a handler's claim (precise traps), dependency-pinned sources of a
device store; not uses at all: the disk row's DMA-before-COMMIT (device model) and the `printf`/panic racy flags
`pr.locking`/`panicked` (their stale-read executions stay in the quantifier).  **User-row gaps under [OWN.3]**
[R6.2] (D35/D36 RULED (a) [OWN.13]): rule 7 RCpc and forwarded plain `LLoad aq`,
both vacuous for kernel rows.  Strengthenings carried INTERNALLY by TsoMem/sRVWMO (not in the published statement
once (9d) lands): "stores never early"; reservation serialisation.  Machine-model choices: exactly 8 harts booted;
Svadu A/D write-back as a plain view-neutral LR/SC; DMA as a store-order agent; TsoMem's instruction-fetch model
(`MachCSL/TsoMem.lean:34-39`, `Lang.lean:360-362,155-163`) — beyond RVWMO's text (Zifencei); the SC-failure model
(`Xv6/UserMemLrsc.lean:7-12`; D17); single era.  Fidelity: the cat transcription omits rules 6, 7-RCpc, 8 (sound
direction for THOSE), litmus-checked only; the published quantifier IS cat (tagged) — D25 (a) RULED [OWN.5] and
spike-CONFIRMED, W12 on the critical path, no RVWMO⁻ fallback; Sail fork `070832a1` with `-D SYMBOLIC`; the image
dump.  Keep, list.
**(11b) Faithful RVWMO I/O, evaluated [OWN.12] — verdict: INFEASIBLE as the realization's ordering source; (a′)
RULED, restated as the residue; optional audit D46.**  Read-only evaluation; every claim about the ISA text is a
reading of prose (riscv.cat has NO I/O events — a faithful I/O model is itself a NEW trusted-surface transcription).
*What the ISA gives (`ioOrdF`, the faithful hart arms):* **(F1)** FENCE with i/o bits (Unpriv. §2.7: PI/PO/PR/PW ×
SI/SO/SR/SW) — `fence iorw,iorw` orders every prior RAM and device access before every later one; **(F2)** PMA
strongly-ordered channel: a hart's accesses to ONE I/O channel in program order among themselves (faithful minimum:
one channel per device — UART0/UART1, PLIC, virtio; the CLINT never reaches the language, `Dev/Fabric.lean:10`,
`timerinit` is Sstc CSR-only); same-address rules are vacuous RAM↔MMIO; **(F3)** dependencies: addr/data/ctrl into a
device STORE (ppo 9–11; herd's `ctrl` reaches every po-later store after the dependent branch), addr into a device
load; ctrl into a device LOAD is NOT ppo — the only basis is the PMA non-idempotency text ("no speculative access to a
non-idempotent region"), a reading to be NAMED; **(F4)** aq/rl: the text orders "memory operations" — faithful = they
do NOT order I/O; **(F5)** precise traps: earlier instructions COMPLETE before a trap is taken, so a load/AMO
po-before an interrupt handler has its value before the handler's MMIO, a STORE need not be performed; **(F6)** the
device rows' own order (virtio DRead/DWrite/DFence/COMMIT, `pdiskProg`; DMA reads at the TOP of the store order,
`Dev/DevLang.lean:20-21`, `dmaView`, `Lang.lean:185,535`) and the fabric sequence `fab` are the device MODELS' —
already trusted, not platform.  *What the realization needs (model-independent):* TsoMem and the pf machine run each
row sequentially — an I/O step sits at its po position, a store enters the log at its step, a load never reads from
the future — so the realized trace is a linear extension of `po ∪ rf ∪ gmo'|W ∪ gmo|IO` (Lin2's `ptraceRel` + (L));
hence (R1) (any `gmem` x) and (R2) are REALIZATION-NECESSARY on every row [R7.1iii].  *(1) Paths and dependence.*
allocproc's own footprint touches MMIO only through `panic`/`printf` (`uartputc_sync`: LSR loads, THR store) and,
with interrupts on during the `proc[]` scan (`wpNext`), through `devintr`'s PLIC claim/complete, `uartintr`,
`virtio_disk_intr`; reaching it needs `consoleinit`/`uartinit`, `plicinit(hart)`, `virtio_disk_init`, and `fork →
allocproc` needs `exec("/init")`'s disk I/O (`virtio_disk_rw` + the disk row).  The published CONCLUSIONS depend on
NO memory↔MMIO ordering: TsoMem's MMIO arms move no view (`Lang.lean:356-358,372-375`), the Xv6 proofs read `fence
iorw,iorw` as the MEMORY floor rule (`ProofVirtioDiskIntr.lean:92-99`), DMA correctness is "stores never early +
device reads at top" (F6), no conclusion names the UART wire order (`uartSentSub` is D9; `xv6NiPhi` counts accepted
bytes, `NiTrace.lean:198-203`).  What depends on the ordering is the REALIZATION of `GT`'s fabric sequence as a
sequential trace.  *Decoder evidence:* §A(†) — Sail's `execute_FENCE` drops PI/PO (`0x0ff0000f` = `Barrier_RISCV_rw_rw`;
`fenceDrains`/`fenceAcq` `TsoMem.lean:356-364`, `ebarNow` `WeakEvLang.lean:733-745`, `ebarLabel` `WeakEvInst.lean:
272-275` never see i/o bits); the bits survive ONLY in the instruction word (`KernelImage.lean:17301,17311,17441,
17451`), recoverable as `emFenceI` recovers `fence.i`: `emIoFence` — S–M, a fence FRAGMENT as graph data (D46 (b)).  *Per-path audit of
xv6's faithful edges:* `virtio_disk_rw`: desc `sh` → `fence` (`0x80005c7a`) → avail `sh` → `fence` (`:5c8a`) →
NOTIFY `sw zero,80(a5)` (`:5c92`, `0x10001050`) — `x →po dv` faithful (F1) ✓; after NOTIFY `lw a5,4(s3)` (`b->disk`),
`sleep`'s stores, no fence — `dv →po w` ✗.  `virtio_disk_intr`: `acquire` → STATUS `lw a5,96(a5)` → ACK `sw a5,100(a4)`
(`:5d52`) → `fence` (`:5d54`) → loads — `dv →po w` after ACK ✓ (F1); the acquire's store half and frame stores before
STATUS ✗ ((F4): aq does not reach I/O).  `uartputc_sync`: LSR loads → THR store: ctrl ✓ (F3; same channel (F2));
prior stores and the lock's store half → LSR ✗; THR → `release` (`fence rw,w; sw`) ✗ (no PO bit).  PLIC: pre-trap
loads → claim ✓ (F5), pre-trap stores ✗; claim → handler stores ✓ (F3 ctrl), claim → `plic_complete` ✓ (data);
`plicinithart`/`plicinit` boot stores → device stores ✗.  **So `dv(store) →po w` is ISA-given at exactly ONE xv6 site
(the ACK) and `st →po dv` at exactly TWO (the pre-NOTIFY fences); every other arm instance is the residue.**
*(2)/(3) Can the gap be closed without an assumption?*  No — the executions it admits are GENUINE RVWMO + I/O
behaviours of the verified code, so no kill can refute them: **(X1)** `printf` under `pr.lock`: hart B's last THR
store →po `release` →rf hart A's `acquire` →po A's THR store, with A's THR FABRIC-BEFORE B's — consistent with
`ioOrdF` (no PO-fence after THR), unrealizable by any sequential trace (THR_B < rel_B < acq_A < THR_A vs `fab`); **(X2)**
the same shape on the virtio channel, NOTIFY_A →po `release(vdisk_lock)` →rf `acquire`_B →(fence)→ NOTIFY_B →fab
NOTIFY_A — the four virtio fences do not close it; **(X3)** a pre-trap store buffered past the handler's claim IS
closed (the store was lock-protected, released before the trap, and the AMO read is trap-ordered (F5)) — PLIC claim
cycles are killable; `plicinithart`'s boot stores are not (no reader, no fence).  Dropping `fab` from what the
realization reproduces would need each device's answers to be invariant under the reorderings `ioOrdF` permits: the
UART's LSR depends on the tx FIFO (`Dev/Uart.lean:88,132,184`), the PLIC's claim CLEARS pending (`Dev/Plic.lean:85-93`) —
order-sensitive; a per-device commutation argument over `fab` (D38(c)'s flavour, xv6- and device-specific, XL) that
also changes what the theorem says about devices.  Posted-MMIO arms in TsoMem re-open the driver proofs ((9a), XL×2).
Stating (L)/(K)/W2 with the faithful edges alone is syntactically possible (under rev 10 they are ppo-style edges
INTO gmo among events, `ioOrdF ⊆ ioResidue`) but (L)'s existence FAILS at (X1)/(X2) — a faithful (L) needs the
residue as a premise anyway.  **Hence (a′) stays [OWN.12], re-encoded as (R1)–(R3) [OWN.14]; D46 offers the
machine-stated residue (W13 (F): `emIoFence` S–M, the fence fragment as graph data in `gdFetch`'s style; dependency
edges through `LIo` — `rowDepsT` drops `LDev` items, `AxDeps.lean:461-463`, `pnodeStep`'s MMIO arms discard the read
set, `oib = none`, `WeakEvInst.lean:300-304,335-338` — M (D50 (b)); trap-boundary edges S; `ioOrdF ⊆ ioResidue` S;
header-only value).**
**(12) Audit coverage and file layout** [R1.10].  `Xv6/` never imports `Weak/` (`lakefile.toml:2,27-41`).  Composition
files live in `Weak/`, registered in `tools/ci/roots-weak.txt` + `tools/audit/baseline-weak.json` + `XV6_AUDIT_MODULES`
(`tools/ci/audit.sh:44`), built by `--weak` CI over the whole `Xv6` adequacy cone (D13); pure-`Xv6/` items (W3, W8) go
to `roots.txt`/`baseline.json` (`tools/ci/lint.sh` checks agreement).  S.

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
  has `xv6FsAdequacy_closed`'s three boot hypotheses and concludes `xv6NiPhi g2 κs` (`Xv6/NiAdequacy.lean:92`), whose
  `NiClassLaw` (`Xv6/NiTrace.lean:660`, via `NiLedger.lean:319-322`) contains `niRoundLaw`'s fork row (`:646`): the
  enter's `a0 = usysForkAns ι` = `if forkOk ι then signExtend (pidPick PIDMAX ι.pev) else -1` (`Xv6/UsysDet.lean:
  293-302`) at the CITED prefix — tie β (D11).  **Theorem shape** [R6.5d]: `allocprocTrace : ∀ g … (boot hypotheses)
  n κs t2 g2, ([Expr.power], g) -<κs>->ₜₚ^[n] (t2, g2) → ∃ F, ∀ q, ∀ s ∈ utrace q κs F, s a fork round → s.a0 =
  usysForkAns ι_s ∧ (forkOk ι_s → 1 ≤ pidPick PIDMAX ι_s.pev ≤ PIDMAX)` plus `poolEmpty` at every `KNull`
  (`Xv6/KallocEv.lean:72`).  **[R6.5d-alt]** the pid bound is NOT an existing lemma — `PidEv.lean:136` is `pidPick`'s
  DEFINITION; the file has only `pidPick_spec :200`, `cycAt_zero :158`, `cycAt_period :179` — W1 PROVES `pidPick_range`
  from `cycAt`'s codomain (S) and the `nextOf` tie (`:77`).  Ledgers export no page address (`Kev`, `KallocEv.lean:
  45-52`) and no slot index (`Pev`, `PidEv.lean:50-55`); `liveOf` is a set.
- **W1b (owner-gated, L, serial)**: `pidHistWf h` in `pidLedger` (live pids distinct by induction), re-thread
  `ProofAllocproc`/`ProofFreeproc`/`NiLedger`; optionally addresses in `Kev` for page disjointness.  D10.
- **W2 `Weak/TsoOfPf.lean`** (L; spike first, ≤ 200 lines, risk report) [R1.11][R2.3][R2.s3][R3.4][R3.s3][R6.4b].
  `pfStepTso`: for every memory label (one row per exclusive half, plain load, fetch), a `wpPfStep` from an
  `R`-related state under `pairAdjacent` + `execProgOk'S`'s shape (W5b's statements, HYPOTHESES here [R5.3]) +
  `candSca` is a TsoMem step with the same bytes, to a related state; the `LIFetch` row reads at `tvn := q` with
  `R`'s `itv ≤ q`.  Report: per-label (↓) table; fence spot checks; `R` with the `.aq` off-by-one; (↑) NOT CLAIMED;
  the log identification in W8/W11's vocabulary (author, class, position, per-byte history) [R4.s3].  Deps: W3's
  statement; W5b's two statements.  **STOP rule** (D7): a WeakMem behaviour TsoMem lacks on a SHAPED run → STOP,
  report; suspects: parked release fence, fence-clears-reservation, tearing, `.aq` off-by-one [R3.s5].
- **W5b `Weak/PfRunShape.lean`** (M) [R2.3(iii)][R3.2][R3.4][R5.3][R6.4c].  **Day one: DEFINE `execProgOk'S`
  (§B(10)'s three clauses, over the step list; the realizing-label clause stated for ANY `projLbl`-image label so
  W13 (E)'s payload `LDev` joins without a restatement [OWN.14]) and `pairAdjacent`; hand both statements to W2 and
  W5c.**  Then `execPrefixPfRunProgShaped`:
  the replay variant that consumes `execProgOk'S`, PROVES `pairAdjacent` (from `execProgOk'`'s right arm) and carries
  it, the fetch cuts and `candSca`'s per-load `tvn` along the run — a new theorem in `Weak/`, not a change to
  `WeakAxRealize`.  Deps: none.
- **W5c `Weak/SrvwmoXv6Witness.lean`** (M–L, re-specified [R3.3]; D22).  Non-vacuity: M1's premise set is
  SATISFIABLE.  Not the `sw &started` block: M1 fixes `pst 0 = epsInit σ0` (pc at `_entry`, `WeakEvCapstone.lean:
  1026-1027`), the existing witness sits at the MID-instruction node `WeakEvStarted.evX2` with an EMPTY admin run
  (`Weak/WeakRvwmoConfWit.lean:11-22`; `Cert.lean:522-546`), and `started = 1` is the boot's LAST store
  (`Xv6/SpecMain.lean:6-15`).  The block is `_entry`'s FIRST memory instruction, `ld sp,1000(sp)` at `0x80000004`
  (`Xv6/KernelImage.lean:14-17`; GOT word `0x8000a3e8`, image bytes, `t = 0`): hart 0 alone, `candKfetch` ✓, the admin
  run by kernel evaluation (`esil`, `Weak/WeakEvLift.lean:897`; `pevrunAdmRun`, `Weak/WeakRvwmoCert2.lean:180`; the
  `esil → admRun` bridge is THE missing mechanism, `Weak/WeakRvwmoConfWit2.lean:26-28`), consistency from
  `gtraceSnocReadImage` (`Weak/WeakRvwmoFloor.lean:1025-1035`) or `snocRdAdm` (`Cert.lean:257`), a concrete `σ0` with
  `wbootFacts` (`MachCSL/BootRun.lean`), `candSca` trivially, the S-variant of `execProgOk'Snoc`.  Certifies
  satisfiability ONLY — not reaching `allocproc` (D44), and QUIESCENT (no `LDev`), so nothing about W13's bundle
  (W13-wit) [R5.s3].  Deps: W5b's predicate.
- **The three spikes — DONE** (scratch files in the header; reports `notes/W12-spike.md`, `W13-spike.md`,
  `W5dG-spike.md`; **[OWN.10]: the two merged scratch files stay, no further spike file is merged before
  SATISFIED**).  W12: route (a) SOUND, gates 1–2 closed by hypothesis changes, (F1) TAGGED quantifier, (F2) gate 3 =
  W12b, witnesses via `catADOfMinus`; Q1–Q4 = D33–D36 (all RULED (a) [OWN.13]).  W13: vacuity CONFIRMED, T2-1c′ LANDED
  (`Lin2.lean:623,836,944,995,1012`), literal [OWN.8] REFUTED (`lbExcluded`), block-folded `gdevAdj ⊆ gmo` excludes
  SC, W13 = XL; Q-a..d = D32, D37, D38, D39 (all RULED; its §3 `ioOrd` design SUPERSEDED by rev 10).  W5d-G: fetch
  ADMINISTRATIVE, `gzFetch` + fetch fragment, L + XL risk R1, M2 clause = cut form; Q-G1..G4 = D40–D43 (D40 RULED (a)
  [OWN.15]).  Designs are in §A/§B(4)(iii)/§B(9) and the Stage-2 items.

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
  sys_fork → allocproc` under contended `p->lock` from 7 scheduling harts is a candidate.  The user-fetch witness is
  NOT buildable by kernel evaluation (D44 [R7.4]).  The graph half is W5d-G (Stage 2).  Deps: W5.

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
  (K)'s `racyDIO` — `gmoLt` composition as today, the I/O arms gmo-forward by (T); parameterize the cross order.
- **W12b `Weak/CatFloor*.lean`** (M–L ≈ 0.5–1k; NEW [R6.2]; D34 (a)).  Gate 3: Floor §4–§6 and Cert3 §2–§3 re-done
  on a per-byte coherence invariant through rules 1/2 in place of `gvisUb`; `greadSrcUb`, `finvStep`, `cinvReplay`/
  `floorOfCgraph`/`certFloorOk`/`cpolRead` over `rvwmoCatAD`; the `wVRel` hook per D35, forwarded `LLoad aq` per D36.
  **Acceptance** [R7.s5]: ONE forwarding read whose floor the old `gvisUb` mis-states — an own store `w` forwarded to
  a po-later read `r` with `w` gmo-AFTER `r`, the exact `finvStep` coh-hook case (`Floor.lean:619`) — certified by the
  new per-byte invariant.  Scheduled WITH W12 and BEFORE W10 (else W10 → L and absorbs it).
- **W5d-G `Weak/GraphFetch*.lean`** (L ≈ 1.8–2.2k + XL risk R1; D27 RULED (a) [OWN.6]) [R4.2][R6.4b].  **Day one**
  [R7.s3]: merge `../xv6iris-weak-w3/Weak/GraphFetchSpike.lean` into this tree as `Weak/GraphFetchSpike.lean` (builds;
  `propext, Quot.sound`) so the cites below resolve — **only once the plan is SATISFIED [OWN.10]**.  Then the spike's change list: **G1** `gzContrib`, `emFenceI` + `emFenceISound`, `emZifencei` in `xv6ConfS`/`gdexecQconf` replacing
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
  closure per §B(4)(iii) R1 (a).  Non-vacuity gate: a user-text fetch witness — NOT buildable by evaluation (D44
  [R7.4]); W13 (W)'s two gates come first (without the disk row `exec("/init")` never completes).
- **W13 `Weak/GraphFab*.lean`** (**XL ≈ 7–10k lines / ~70 files**, REDESIGNED rev 10, eight pieces; D38 RULED
  [OWN.14]) [R5.1][R6.3iii][R7.3].  **(E) the alphabet** (L, wide and shallow, the accepted merged-file change):
  `Lbl.LIo (kind : IoKind) (base : Int) (vs : List (BitVec 8))` (`WeakAxiomatic.lean:87-91`; `lbRd`/`lbWr` = `none`,
  `lbIsR`/`lbIsW` false, new `lbIsIo`; `gwf`'s shape arm; `candShape` `WeakAxiomatic2.lean:910-916`); `Wlabel.LDev`
  gets the same payload (`WeakPromise.lean:86`); `pnodeStep`'s MMIO arms emit it with `paZ req.pa`/the bytes
  (`WeakEvInst.lean:300-303,335-338`), `pstepPlic :461-466`, `pdiskProg :484,502`, `pdiskUart :514-520` emit kind
  `dev` (D49); `projLbl .LDev … = some (.LIo …)` (`WeakPromiseBridge.lean:529-545`, today `none` at `:537`),
  `unprojLbl :955`, `lblRealizes`/`lblRealizesUnproj` (`WeakAxRealize.lean:240-280`), `lbAdmin :130-134` DROPS
  `.LDev`, `lbNobarex :100`/`lbRfoldfree :107`/`lbFused` (`WeakPromise.lean:121`)/`latFree`
  (`WeakPromiseFact.lean:61`)/`eraseLbl` (`WeakErase.lean:102`)/`pclsEv :217`/`pdevEv :540`/`wlblRen`
  (`Conf.lean:142-155`)/the taggers `dstep :493-495`, `dstepT` (`AxDeps.lean:461-463`) get an arm; `elabOk :547`
  (`True`), `elabWs :571` (view unchanged), `wpPfStep.PFDev` (`WeakPromiseBridge.lean:392-396`, payload only);
  exhaustive `Lbl` matches in 41 chain files + 30 `Ax*` files (the `| LFence` arm census; the retired tier must still
  build), `Wlabel.LDev` arms in 28 files — one-line arms, mechanical.  **(M) the model** (M–L): `gmem := lbIsMem ||
  lbIsIo` so I/O events are in gmo; every "a `gmem` event is a read or a write" case split in the chain gets an I/O
  case (`lbIsMem` is unfolded in 39 files, `gmem` named in 22 chain files — measured, proof impact **unverified**);
  `rvwmoCatConsistentT`'s TEXT is unchanged; `gdexecQconfT`/`xv6ConfS` gain `gisIo (i,k) ↔ (i,k) ∈ gfDev`;
  `emDevfree` (`Supply.lean:273`) retires.  **(T)** `ioResidue`/`ioResidueGmo`/`gfBefore` + header text (S); acceptance:
  `ioResidueNodev` and the re-encoded `w13f` (§A(†)).  **(I) realization** (M–L): `execProgOk'` UNCHANGED — the I/O
  step is a left-arm realizing step with fabric endpoints `dvi k → dvo k` (`hemitf`'s `HFone`, `Fab.lean:241-247`,
  already has them); `gfexecConfIO` = `gfexecConf` (`:522-535`) with the `isDevBlock` clause replaced and `emFetchImg`
  → `emZifencei`; `supplyOfFconf`'s block folding `hblkQ` (`:689-701`) is DELETED, not generalized; T1 gets an inert
  arm `mstep.MStepIo`/`wpstep.WPIo` and `promiseFreeCompleteClean` (`WeakAxiomatic3.lean:1434`, 2k lines of label
  case analysis) carries it — the real (I) cost.  **(L)** T2-1c″ (M–L): `ptraceRelIO := ptraceRel ∪ gmo|IO`
  (`Lin2.lean:124`); I/O events are rule-14 ANCHORS like writes — `gnxw` (`Lin.lean:440`) → `gnxa` "next own write
  or I/O event", `glinEids :455`, `linCand :471`; `gtraceLinearizationMin :623` restated, I/O steps no-ops for the
  cand; `fconfSupply'`'s `before L` premise (`:1000`) and FabInd's handed-back `trDevOrdered` (`:407`) are DISCHARGED
  from `ptraceExtIO` (fab order = the trace's I/O order = gmo|IO by (R3)).  **(K)** the kill (M–L): `racyDIO :=
  racyD ∪ ioResidue ∪ gmo|IO`; the cross kind `gmo|IO` and the same-row arms (R1)–(R3) are gmo-forward by (T)
  directly, so KillArms' chain composes in `gmoLt` AS TODAY (no `tc ioOrd`); segments ENTERING at an I/O event and
  exiting at a WRITE are free by (R2); `csChained` (`KillArms.lean:499`) generalized to "entry = any `gmem` event of
  the critical section" (S–M); `normalizeOfAcyclic` over `racyDIO` keeps I/O positions (its topo order ⊇ gmo|IO);
  `gdHull` keeps I/O events and filters `gfDev` → `cycleKillIO`, through `hullRun`, W11, W12.  **(R)** the re-thread
  of the constant-fabric chain onto `gfexecConfIO`: measured 8.6k lines / 14 files / ≈ 140 bundle mentions / 52 `fun _
  => d0` sites (Supply, LinInd, Cert4, Glue, Glue2, Walk*, Progress, PreNorm*, Capstone); segments without I/O events
  have `dvi = dvo` and reuse the constant-fabric lemmas verbatim; witness files embed via `gfexecConfOfQconf`;
  KillArms, Hull, Lin unchanged except the new arms (L–XL, the bulk).  **(W)** `xv6ConfS` on `gfexecConfIO` +
  **W13-wit** (M–L): hart 0's run `_entry → … → uartinitone` (entry `0x80000896`, `Xv6/KernelImage.lean:1515`; the
  `jal` at `:1590`) to **its first UART store, `sb zero,1(a5)` at `0x800008a0` (`:1525`, IER := 0)** [R6.5b] — now the
  EVENT `LIo .wr 0x10000001 [0]` in row 0, the first candidate with a non-empty `gfDev` (D31); ≈ 100 dynamic
  instructions, NO MMIO before it (`timerinit` is Sstc CSR-only, `Xv6/SpecTimerinit.lean:5-7`), by kernel evaluation
  as in W5c; **gate 2 [R7.3c]: a device-ACTIVE DISK witness** "first disk START → DRead/DWrite → COMMIT" on the disk
  row (the precondition of every user-fetch witness; its evaluation route is OPEN — the first disk request is
  `fsinit`'s `bread(dev, 1)` (`Xv6/SpecFsinit.lean:7`) on the first process's `forkret`, past `kinit`'s `freerange`,
  so it shares D44's infeasibility).  **(F)** OPTIONAL, D46 (b)/D50 (b) (M–L; no proof consumes it).  Risks: **R2′**
  the alphabet sweep touches ~70 files including the retired `Ax*` tier (mechanical, but one build); **R5** an
  I/O-ENTRY / READ-EXIT segment (I/O event →po→ racy read →fr→) has NO fence pin (rule 4 skips I/O) and must close by
  lock discipline or (R2)-rerouting through the release — an unlocked one is a STOP (candidates: the PLIC
  claim/complete races, `plicinithart`, `pr.locking`/`panicked`); **R6** the `gmem` case splits of (M); R4 of rev 9
  (dev nodes next to fences) DISSOLVES — I/O events are `gmem`, fences stay out of gmo.  Deps: W5c's `esil → admRun`
  bridge; W5b's shape clauses; `AxDevGraph.lean` (885 lines: `Dlbl :134-142`, `dstep :152`, `DevConsistent :226-236`)
  is the AxSL tier's device-event precedent — its device-step semantics are reusable for the `dev`-kind replay, its
  separate-row encoding is NOT what [OWN.14] rules.
- **W14 `Weak/ExistWitness.lean`** (NEW; D44 RULED (i) [OWN.11]; size L–XL, **unverified** until W2's per-label table
  is in): the single-execution EXISTENCE theorem — ONE device-active TsoMem-side run (any `-<κs>->ₜₚ^[n]` run from
  `PowerOn` that reaches `allocproc`, obtained from the SC tree's reachability, not by evaluation) is lifted to a
  conformant cat candidate: a `GT` with `rvwmoCatConsistentT`, `ioResidueGmo`, `xv6ConfS` and a non-empty `gfDev`
  whose realization is that run.  It is the (↑) direction of W2 for a SINGLE run (not receptiveness, D15): per label,
  TsoMem step → pf step at the SC-like view (`tvn := top`), stores at the top, I/O events at their trace positions;
  the graph is the trace's own (`gmo` = trace order of writes and I/O events, `fab` = its I/O restriction — (R1)–(R3)
  hold by construction), consistency by `linCand`-style construction, the
  fetch clause by `fetchPinCutOk`/`gzFetch` at tag 0 for kernel text and the TsoMem `itv` for user text.  Certifies
  non-vacuity AT `allocproc` (and past user code, [OWN.3]); until it lands the header carries D44's caveat.  Deps: W2's
  `R` and table; W5b; W13 (E)/(I)/(W) (the I/O-event bundle); W5d-G (the fetch clause).  Risk: the "reaches `allocproc`" fact is a
  LIVENESS-flavoured reachability of the SC tree, which exports safety only — the run may have to be exhibited by a
  dedicated SC-tree lemma ("some run reaches `userinit`'s `allocproc` call"), M–L on the Xv6 side, **unverified**.
- **W8 `Xv6/AccessDiscipline.lean`** (L–XL; D24) [R4.3][R4.s3][R4.s4].  Export from the SC tree, per reachable
  MachCSL state (the `mmOk` idiom) on `MState`'s author log + per-byte histories (`MachCSL/Lang.lean:147-153`), in
  the vocabulary `protReg`/`badSeg` consume: (i) bytes a hart OWNS — no foreign writer (covers `PStack`/`PPerCpu`,
  the 58 `own = true` witnesses; `gen_weak_pins.py --check` as the audit); (ii) a protected access under a held lock
  (`wprotAt`/`wlpAt`/`wlpAlt`, `Weak/WeakGhost.lean:1040,543,699`; `lockWordByte`, `KillArms.lean:340`); (iii) no
  hart's floor reaches a FOREIGN owned-unpublished message (`wmAk = .WCplain`, `WeakRobustMain.lean:390-395`; `¬
  wpublished :399-400`; `Weak/WeakViolation.lean:9-15`) — HART authors only, DMA exempt, mirroring `violationHart`
  (`WeakRobust.lean:100-107`); (iv) ALL 182 `PCall`/`PResidue` sites and the 58 sp-frame witnesses classified into
  (i)–(iii) (W9b; D28 RULED (a) [OWN.7]); (v) user-text page ownership for W5d-G's G7 (exec/fork → `p->lock` →
  `userret` `fence.i`).  A ledger threaded through the MachCSL memory rules — mechanical but wide; ownership residue
  ~5 idioms (`swtch` reloads, trapframe loads off `a0`, user-table walks, boot-published globals).  Exports hold on
  FORWARDING graphs (TsoMem forwards).  **Design gate: the W2 report** [R4.s5][R6.4a].
- **W9a `Weak/WeakRvwmoPinBridge3.lean`** (L = M–L + M [R6.1]) [R4.1].  R-3: a `pstepEv` run's items are grouped per
  instruction as the checker's pc walk assumes (`reaches`/`psites`, `PinBridge2.lean`; §8 has both halves on one
  computed stretch) → `pinSegPin'` applies at every certifying site of the REAL run, targeting `segPinC`
  (`pinStepOfSegPinArm`; PDep entries across an rfi via `segPinCForward`); with W8 (W9b) → `l2ClaimAtC`'s `segPinC ∨
  csHyps` arms for xv6.  No generator work: `KernelPins.lean`/`imagePinnedb`/`pinsCover` exist.
- **W10** (M–L, **unverified**; L if it absorbs W12b): `wsegSupply`/`walkPolicy` for xv6 graphs on the W12b floor kit.
- **W11 `Weak/RvwmoXv6Adequacy.lean`** (L) [R4.3][R4.4].  (i) **The `Bad` arm is LOG-LEVEL**: `l2ClaimAt GD P Bad`
  (`Glue.lean:440-447`) hands the prover `(GD, log, logOf, protReg)` while the capstone sets `Bad := badRun gen σ0 = ∃
  ρ, rtc epfRun … ∧ violationHart …` (`:384-385`), a RUN-LEVEL existential refuted by `noBadRun` (`:387-391`) over ALL
  `epfRun`-reachable configurations — unreachable on route (M); `rawChainChain` consumes `¬ Bad` globally (`:453-460`).
  Define `badSeg GD log prev s` := the entry's source message is owned (`wmAk = .WCplain`) and unpublished at `log`
  by a FOREIGN hart; restate `l2ClaimAt` with it; prove `¬ badSeg` at the certified run from W8 (iii) through W4 (the
  realized hull run is a prefix of the realizing TsoMem run); derive the global `¬ Bad`.  (ii) `protReg P log`
  (`:364-368`) is a fold over the LOG — transfers through `R`'s log identification once W8 exports (ii) (D24).  (iii)
  re-thread `execProgOk'S` through `RunData`, `cstOk`, `segStep`, `topoSupply`, `t2linSupply` — one pass with W5d-G
  G6.  (iv) `linCandSca` (S) [R4.4].  (v) Restate `cycleKillOfL2''`
  (`Glue2.lean:521`), `t2linOfL2'''` (`Walk3.lean:77`), `xv6RvwmoSafeModuloT` (W12) with W8-sourced facts in place of
  `wpPackage`/`wpPackageProt`/`noBadRun`/`protRegOfRun`/`efetchItvOk`; compose with M2, W5d-G and W13 (the I/O-event
  bundle `gfexecConfIO`, `ioResidueGmo`, T2-1c″'s supply, `cycleKillIO`): **T-alloc-RVWMO**.  Header per §B(11).
- *Not on the path:* **W6** PSO machine (L–XL; optional de-risk, D4); **W7-P** promise-machine fallback (D2').

**Stage 3 — AxSL tier: retired** [OWN.1].  One-paragraph note on Theorem 2 (D6).

**Launch now:** W3 first — SERIAL, the one Stage-0 item on shared files (`MachCSL/Adequacy.lean`,
`Xv6/SystemSlot.lean`, a new link file, `roots.txt`/`baseline.json`/`tcb/expected.json` additions) [R5.2][R6.5c] —
then W2 spike ∥ W1 ∥ W5b ∥ W5c; W5b's two statements on day one unblock W2 and W5c.  W1b waits for D10; W8 design
starts after the W2 report (its export shape depends on `R`; the spike inputs are IN) [R4.s5][R6.4a].  The published
statement's shape is FIXED: D32, D33, D37, D38, D44 RULED [OWN.11–14].  W13 (E)/(T) cannot start before D47–D50
(the `LIo` encoding, the fence rule, the `dev` kind, the tagger default) and D45 are ruled; W5d-G before D41–D43;
W13 (F) only if D46 (b).

## D. Owner questions (recommended option first; RULED items kept for the record)

[R7.s1] NOT adopted: the brief allows edits to this file only and requires every question with all its options kept,
so RULED items stay here, tightened, rather than in an appendix.
**The published statement's shape is FIXED (D32, D33, D37, D38, D44 RULED); OPEN: D41–D43 (W5d-G), D45–D50 (W13).**
- **D32 = Q-X / Q-W13a — RULED (a′) [OWN.12]; re-encoded by D38 [OWN.14] as (R1)–(R3) of `ioResidueGmo`.**  The
  literal [OWN.8] axiom is refuted by `lbExcluded` (`Weak/W13Spike.lean:35`).  Options for the record: (a′) **the
  `dv → ev` arm restricted to WRITES — RULED (both hart arms realization-necessary; the residue over the ISA-given
  edges)**; (f) FAITHFUL `ioOrdF` alone — INFEASIBLE (§B(11b): xv6's UART/PLIC and post-NOTIFY virtio paths supply
  the arms nowhere; (X1)/(X2) have no sequential-trace realization; dropping `fab` needs per-device commutation, XL);
  (a) the spike's two-way form (`W13Spike.lean:83-95`; MMIO = full fence, excludes stale-read-after-MMIO executions
  the strong model realizes); (b) [OWN.8]'s literal `po ∪ rf ∪ gmo|W ∪ dev` acyclic — drops LB and W→W [OWN.2]; (c)
  the same on the normalized graph — not about the input; (d) `gdevAdj ⊆ gmo` on the FOLDED model — excluded SC
  (`scDevExcluded`); on I/O EVENTS the fabric inclusion is (R3) and sound.
- **D33 = Q-T / W12-Q1. The published model — RULED (a) [OWN.13].**  (a) **tagged `rvwmoCatConsistentT`, chain on
  `forget GT`**; (b) untagged `rvwmoCatConsistent` with "rule 12 also over ctrl/translation deps" NAMED as a
  strengthening; (c) drop rule 12 — sound, but the kill loses `segPinCForward` and W9a splits PDep pins at every rfi.
- **D34 = Q-U / W12-Q3. Gate 3 ownership — RULED (a) [OWN.13].**  (a) **W12b `Weak/CatFloor*.lean` (M–L) with W12**;
  (b) W10 absorbs it (W10 → L); (c) kernel rows only, user-row aq/rl deferred.
- **D35 = Q-V / W12-Q2. Rule 7 — RULED (a) [OWN.13].**  (a) **`grcsc` riscv.cat-faithful: RCsc = any aq/rl on
  AMO/LR/SC; first check the decoder emits `LStore rl`/`LLoad aq` only for atomics**; (b) weak rule 7 + side condition
  "no rl write followed by an aq read" (vacuous for the kernel); (c) leave it, `Bad`-arm burden in user rows.
- **D36 = Q-W / W12-Q4. Forwarded `LLoad aq` — RULED (a) [OWN.13].**  (a) **row side condition "no plain `LLoad aq`"
  (true for the kernel)**; (b) change WeakMem's `fwdView` for aq (ripples into T1); (c) a named gap for user code.
- **D37 = Q-Y / Q-W13b — RULED (a) [OWN.12].**  (a) **"I/O accesses act as one-way fences for the issuing row and
  serialize as the fabric does — beyond what FENCE i/o bits, dependencies, precise traps and the device models
  order", QEMU TCG (program-order vCPUs + the BQL around MMIO) the platform, host-dependent**; (b) fence-guarded MMIO
  — an xv6 code change leaving `verified`, and the graph tier would still need D46 (b); (c) DROPPED: "PMA strong
  ordering" does not deliver (T).
- **D38 = Q-Z / Q-W13c. The realization interface — RULED [OWN.14] in the I/O-CLASS-EVENT form.**  (b′) **MMIO as
  an I/O-class LOAD/STORE EVENT of the row (`Lbl.LIo`, in gmo, ppo applies, device-supplied value) — RULED; `projLbl`
  and the emission proofs change (merged files, accepted); the realization keeps `execProgOk'` (§A(†), §C W13)**;
  (a) admin-only trace steps `execProgOkA` (rev 9's recommendation — RETIRED); (b) a tagged INERT-FENCE row event in
  the Q7 sfence-marker style (no gmo position; the fabric order would still be a side condition); (c) the folded
  model + per-site representability — xv6-specific, fragile, XL.
- **D39 = Q-W13d — RULED (a) [OWN.13].**  (a) **retire `xv6RvwmoSafeModuloF`/`gfexecConsistent'` as a published form,
  keep as an internal lemma on normalized graphs**; (b) keep it with a header warning.
- **D40 = Q-G1. `fence.i` identification — RULED (a) [OWN.15].**  (a) **emission-structural `emFenceI` + soundness
  lemma (M); the no-op `LFence false false false false` label stays**; (b) distinct fence bits `(f,f,f,t)` — changes
  only `wRes` but perturbs Q7 and the AxSL pins; (c) a new `Wlabel` — XL.
- **D44 ([R7.4]). Non-vacuity past boot — RULED (i) [OWN.11] → W14.**  `kinit`'s `freerange(PGROUNDUP(end), PHYSTOP)`
  (`end = 0x80023b10`, `KernelImage.lean:17935`; `physTop = 0x88000000`, `Xv6/KallocDefs.lean:71`; 32,732 byte-granular
  4 KiB `memset`s, `Xv6/SpecMemset.lean:5-7`) is 10^7–10^8 dynamic instructions — evaluation INFEASIBLE, not XL.  (i)
  **a single-execution EXISTENCE theorem (the (↑) direction for ONE run, not receptiveness; sized by W2's table)**;
  (ii) publish with "non-vacuity certified to the first UART store and first disk COMMIT only" (the interim header
  wording); (iii) a reduced-RAM image for the witness only (not the published kernel, [OWN.4]).
- **D45 ([R7.3]). The disk agent in (T).**  (a) **one `LIo` label with `IoKind = rd | wr | dev`: hart MMIO is `rd`/`wr`,
  PLIC pin deliveries, disk START/COMMIT and the device threads' moves are `dev`; one set of arms (R1)–(R3)
  (recommended; matches `gfDev`, the disk row being `i = NCPU`)**; (b) a separate `dma`/device-side constructor
  with its own arms (clearer header, +S–M; `AxDevGraph.dlblDevside` is the precedent).
- **D46 (NEW [OWN.12]). Machine-stating the I/O residue.**  (a) **(R1)–(R3) alone; the header lists the ISA-given
  edges and per-arm trusted uses in prose (§B(11)) (recommended: no proof consumes the fragment)**; (b) W13 (F): the
  fence fragment `emIoFence` from the `LIFetch` word (as graph data, `gdFetch`'s style), dependency edges through
  `LIo` (= D50 (b)), trap-boundary edges; named readings (F3)/(F5); `ioOrdF ⊆ ioResidue` — the header's residue
  becomes a theorem (M–L, header-only value, more trusted-surface text); (c) the fabric-free realization (per-device
  commutation) — XL, fails for the PLIC's claim, NOT recommended.
- **D47 (NEW [OWN.14]). How an I/O event is encoded.**  (a) **a NEW constructor `Lbl.LIo kind base vs` (+ payload
  on `Wlabel.LDev`) (recommended: `lbRd`/`lbWr`/`lbIsR`/`lbIsW` stay RAM-only, so rf/co/fr/load-value/atomicity/
  `gmsg` and ppo rules 1–4, 7 ignore I/O BY CONSTRUCTION; cost = one-line arms in ~70 files)**; (b) the owner's literal
  wording — ordinary `LLoad`/`LStore` at an address with `ioAddr a := a < devBound` (`MachCSL/Dev/Fabric.lean:125`)
  — needs `¬ ioAddr` GUARDS in `gloadValue`, `greadsByte`/`gwritesByte` (else bogus `fr`/image reads at t = 0),
  `gmsg`, `candValues`, `rdOk`/`readOk`, the fence rule, and a `ts` convention; a side-condition thread through the
  33k-line chain — NOT recommended; (c) `AxDevGraph`'s separate device rows with insertion positions — not what
  [OWN.14] rules (I/O must be IN the row and in gmo).
- **D48 (NEW). Rule 4 and I/O events.**  (a) **PROSE-faithful: `LFence pr pw sr sw` orders RAM accesses only (Sail
  drops PI/PO, `InstsEnd.lean:18299-18313`); I/O events get NO fence edge; the residue covers the realization
  (recommended: the weaker quantifier, consistent with (F1)/(F4) of §B(11b); the four virtio `fence iorw,iorw` give
  nothing at the graph tier unless D46 (b))**; (b) riscv.cat-literal: I/O events are ordinary for rule 4 (`fence
  rw,rw` orders them) — a NAMED strengthening of the prose ("Sail's `extractLsb` conflation is the model"), fewer
  trusted uses on the virtio path, but still the residue on UART/PLIC.
- **D49 (NEW). The device-side fabric moves** (`pstepPlic`, `pdiskProg` START/COMMIT, `pdiskUart`).  (a) **`LIo .dev`
  events in the issuing row (hart row for the pin delivery, row `NCPU` for the rest), under (R1)–(R3) (recommended:
  one mechanism; the block-folding defect cannot recur)**; (b) keep them admin-only via rev 9's `execProgOkA` for
  `dev` kinds only (two mechanisms, +L); (c) leave them folded (status quo — `scDevUnrealizable` recurs for pin
  deliveries, NOT acceptable).
- **D50 (NEW). Dependencies through `LIo`.**  (a) **taggers keep `LDev` inert (`dstep`, `dstepT`): no addr/data/ctrl
  edge into an I/O event, no provenance out of an I/O load (recommended: the weaker model; (R1) subsumes the
  in-edges; same-row I/O→I/O order is (R3))**; (b) extend the taggers (the `oib = none` discard in `pnodeStep`'s MMIO
  arms must go) — faithful (F3), M, and a ctrl→I/O-LOAD edge would need the non-idempotency reading NAMED.
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
- **D18** — RULED [OWN.3]: W5d (M2) and W5d-G in the target; the user-fetch witness is NOT buildable by evaluation
  [R7.4] → D44 RULED (i) → W14.  **D19.** (Rec) `execProgOk'S` (fused pairs) as a named premise; (b) a MachCSL change so
  dangling reservations do not block (serial, L, **unverified**); (c) a user-mode fact — unavailable.  **D20.** (Rec)
  `candSca` named at M1/M2 ONLY, derived at Stage 2; (b) an atomicity axiom in sRVWMO — XL.  **D21.** (Rec) report M1
  as "composition milestone, kernel-only by premise `candKfetch`, loads single-copy-atomic by premise `candSca`"; (b)
  report nothing before M2.  **D22.** (Rec) the `_entry` first-load witness gates M1 (SATISFIABLE, not reaching
  `allocproc`; QUIESCENT); (b) follow-up.  **D23.** (Rec) W1 via `xv6NiPhi` (S–M); (b) the rev-3 ledger hook (M).
  **D24. W8's export form.**  (Rec) a per-state predicate on `g.m` + a ghost access ledger exported like `mmOk`, in
  `protReg`/`badSeg`'s vocabulary; (b) a new `Obs` per access; (c) trace-free from W9a's check + ownership facts.
- **D25** — RULED [OWN.5], spike-CONFIRMED: (a) cat-sound kill arms (`rsameC`/`gcrossE`, lock kit `*C`,
  `normalizeOfAcyclic` over the core), M–L; (b) dropped; (c) NOT accepted.  **D26. Stage-2 sequencing** [R4.s5]
  [R6.3].  (Rec) M1 → M2 → W13 (E)(M)(T) (SERIAL: the alphabet sweep touches every chain file) → {W12 ∥ W12b ∥ W5d-G
  G1–G5 ∥ W13 (I)(L)(K)} ∥ W8 (after W2) → W13 (R)(W) → W9a/W10 → W11, with W14 after W2's table and W13 (I)/(W);
  (b) start W8 with Stage 1 (risk: `R` not fixed).  **D27** — RULED [OWN.6], spike-SHAPED: (a) `gzFetch`, admin form,
  D40–D43.  **D28** — RULED [OWN.7]: all 182 + 58 sites through W8.
- **D29** [R5.1, Q-R] — RULED [OWN.8] "dev-order model in the trusted base, T2-1c′ in scope"; UPDATED [R6.3][OWN.14]:
  T2-1c′ is LANDED; the literal axiom is refuted → D32; `gdevAdj ⊆ gmo` on FOLDED blocks rejected (`scDevExcluded`),
  on I/O events it is (R3).  **D30** — RULED [OWN.9]: sibling root `xv6TextAdequacy_closed`; existing roots/baseline
  untouched; `tcb/expected.json` gains an entry [R6.5c].  **D31. W13-wit timing.**  (Rec) build right after W5c lands
  (its `esil → admRun` bridge is the mechanism) as W13 (W)'s gate 1 — the only pre-Stage-2 evidence that a
  device-active candidate exists; end = the first UART `sb` at `0x800008a0`, now an `LIo` EVENT (needs W13 (E) first);
  (b) defer to Stage 2 (the disk gate 2 and D44 cannot follow this route anyway).

