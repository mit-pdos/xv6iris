# allocproc on RVWMO: target theorem, gap analysis, roadmap (design advisor, 2026-10-09)

**Status: rev 13 = rev 12 + W2 spike D7 STOP redesign (G1–G3) + W3 DONE + [OWN.16].**  The W2 spike
(`notes/W2-spike.md`, Lean `Weak/TsoOfPf.lean`, MERGED) hit D7's STOP: the lockstep WeakMem-pf ⊆ TsoMem simulation
fails at three gaps — **G1** the `.aq` floor debt, **G2** TsoMem's footprint coherence stamp (a TsoMem strengthening
MISSING from §0 F1, now (iii)), **G3** DMA reads at the top vs the disk row's floor reads.  Rev 13 redesigns Layer 2
(§B(10): the TsoMem view SHADOW `tsoShadow`, `candScaT`, `candDiskLat`, the corrected `R`, (★) as W8's export shape)
and opens **G1-Q / G2-Q / G3-Q** (§D, recommended first; D7 RESOLVED-BY-REDESIGN).  Stage 0: W3 DONE (option A, sibling
root landed; Q-W3a RULED (A)), W1-Q RULED (c), D41/D45 RULED (a) [OWN.16].  Rev 12 (R9 SATISFIED): Stage-0 results
recorded.  Rev 10/R8: **D38 RULED [OWN.14]: MMIO accesses are I/O-CLASS GRAPH EVENTS**, W13 around `Lbl.LIo` +
`ioResidueGmo`.  Every OPEN or STANDING semantics question opens with a "Spec:" line and marks each option faithful /
stronger / weaker (OWNER RULE 2026-10-09) [R8.1][R9.1][R9.s3].**
**One-liner [R6.s1][R7.2a][OWN.12][OWN.14]: the published quantifier is riscv.cat RVWMO with TAGGED dependencies
(`rvwmoCatConsistentT`) over graphs whose rows CONTAIN the I/O accesses as events, plus an I/O-ordering PLATFORM
assumption (`ioResidueGmo`: BEYOND what ppo gives those events — nothing from FENCE (Sail drops the i/o bits) or
dependencies, rule 5 only — a row's RAM accesses po-before an I/O event and its RAM STORES po-after it are
gmo-ordered on that side of it, and I/O events are gmo-ordered as the fabric serializes them — the residue is what
QEMU TCG gives and RVWMO + PMAs do not, AND what the one-row device model requires [R8.2][R8.s2]) and a graph-tier
Zifencei fetch model (`gzFetch`) — two named trusted-base items with no reference model.  Non-vacuity past boot: W14
(D44 (i), RULED).**
History (all 2026-10-09; reviews `notes/weak-allocproc-plan-review-RK.md`): rev 1 survey; rev 2 R1 (11 req.; D8–D13);
rev 3 R2 (5 req., two [R2.n-alt]; D14–D19); rev 4 R3 (4 req.; D20–D23) + [OWN.1–4]; rev 5 R4 (5 req.; D25, D27, D28);
rev 6 R5 (3 req.: quiescence VACUOUS → W13; W3 sibling root; `pairAdjacent`) + [OWN.5–9]; rev 7 R6 (5 req., s1–s4) +
spikes (tagged cat model, W12b, `devAcyclic` REFUTED, T2-1c′ LANDED, W13 = XL, fetches ADMINISTRATIVE; D32–D43); rev 8
R7 (4 req.: `dv → read` arm DROPPED (a′), disk row first-class, user-fetch witness INFEASIBLE; D44–D45); rev 9
[OWN.10–12] (faithful I/O INFEASIBLE §B(11b), (a′) the residue; D44 (i) → W14; D46); rev 10 [OWN.13–15] (D33–D36,
D38–D40 RULED; W13 = I/O-CLASS EVENTS `Lbl.LIo`/`ioResidueGmo`; D47–D50); rev 11 R8 (4 req.: "Spec:" lines on D41,
D45–D50; D51, D52; §B(11b) on the appendix "I/O Ordering"; FIOM clause); rev 12 R9 (SATISFIED; 2 req.: Spec lines on
D7/D19/D20 + `candSca` alignment caveat, five cite paths; s1–s4) + Stage-0 results (W5b/W5c DONE, W1/W3 PARTIAL; W1-Q, Q-W3a);
rev 13 W2 spike D7 STOP (G1–G3 redesign: `tsoShadow`/`candScaT`/`candDiskLat`, (R2′); G1-Q–G3-Q) + W3 DONE + [OWN.16] (W1-Q, Q-W3a, D41, D45 RULED).

**The kernel [OWN.4][R1.9]: xv6-riscv `b72cbac1`, branch `verified`** (`notes/STATUS.md:8-11`, `README.md:89-90`)
= upstream plus (a) a per-process root (`p->root`, `sys_chroot`, `igetroot`, root-aware `dirlookup`/walk) and
(b) upstream's post-`ded23f2` allocpid — bounded counter `PIDMAX = 1000` (`Xv6/ProcGeom.lean:80`) with a 64-slot
liveness scan, inlined by gcc into `allocproc+0x38..+0x94` (`claude-notes/kernel-defects.md:224-231`) — not the
textbook monotone `nextpid`.  Image `Xv6/KernelImage.lean` by `tools/dump_kernel.py`.

Advisory only; read-only survey of `../xv6iris-weak` (`Weak/`, `Xv6/`, `MachCSL/`, `notes/weak-memory-*.md`,
`claude-notes/{completed,design}/*weak*`).  Sizes: S ≤ 300 lines, M ≤ 800, L ≤ 2k, XL = multi-week / many files.
Unconfirmed claims are **unverified**.  Spike scratch files (build, no `sorry`): `Weak/CatOfMinusSpike.lean` (399),
`Weak/W13Spike.lean` (145), **`Weak/TsoOfPf.lean` (239, MERGED, `Weak.lean:624`; `propext, Classical.choice,
Quot.sound`) — the W2 spike's Lean: `g1Run`/`g1Shape`/`g1Tso`/`tsoAqPairTv`/`tsoExclRv` (G1), `g2Run`/`g2Shape`/
`g2Tso`/`tsoAfterLoadCoh` (G2), `fenceRow` (the one POSITIVE row in Lean), `histOf` (`R`-hist) [W2s]**,
`../xv6iris-weak-w3/Weak/GraphFetchSpike.lean` (226; `propext, Quot.sound` only) — ONLY in the `-w3` workspace (report
`notes/W5dG-spike.md`); **[OWN.10]: SATISFIED (R9) — merge freeze LIFTED; W5d-G's day-one merge of `GraphFetchSpike.lean`
is RELEASED** (a Stage-2 item; `:N` cites refer to the `-w3` file until it lands [R7.s3]); `W13Spike.lean` §3 is SUPERSEDED (§A(†)).

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
baseline (`tools/audit/baseline.json:11-14`) axioms `propext`/`Classical.choice`/`Quot.sound` + exactly three opaques
`LeanRV64D.Functions.xv6_resv_is_valid`, `…xv6_resv_matches`, `MachCSL.bootImageSealed` [R7.s6].

The memory model under all of that is `MachCSL.TsoMem` (`MachCSL/TsoMem.lean:1-40`; `relaxed-rr.md`): one total
store order with per-byte write histories, per-hart view FLOORS (load–load reordering), store forwarding by author,
store buffering, `fencePost` (`:345`; `fence rw,w`/`w,w`/`r,w` are NO-OPS, `:356-364`), `.aq` AMOs, LR/SC
reservations, a non-coherent i-cache view `itv` + `fence.i`.  **What it forbids that RVWMO allows** [R1.7]: (i)
store–store reordering and load buffering (stores never early) — the weak tier's sRVWMO residue (rule 14,
`Weak/WeakAxiomatic3.lean:2050-2071`; litmus divergences LB and reader-fence-only MP, `Weak/WeakSrvwmoLitmus.lean:
1663-1695`), checked by reading: nothing relates TsoMem to `srvwmoConsistent`, and §B(10) does not need it [R2.s2];
(ii) **reservation serialisation**: a foreign store or exclusive read overlapping a held reservation is BLOCKED
(`blockedStep`, `MachCSL/Lang.lean:366-378,395-403`; DMA `anyReserve`, `:539,562`); the reservation persists until the
holder's next store of ANY address (`:147-153`) or a blocked exclusive read, surviving fences (`:155-163`); RVWMO's
atomicity axiom constrains only SUCCESSFUL pairs (D19 Spec); the kernel uses only `amoswap.w.aq` (`Xv6/ProofAcquire.
lean:5`), USER code may `lr`/`sc` (the SC success predicates are two of the three opaques); **(iii) [W2s] FOOTPRINT
coherence stamping**: a plain load stamps EVERY byte of its footprint with the load's view (`HRead.afterLoad`,
`MachCSL/TsoMem.lean:268`; the `cohOk` premise, `Lang.lean:365`), so two overlapping loads of DIFFERENT footprints are
ordered even when the shared byte reads the SAME write — riscv.cat rule 2 (`gppo2`, `Weak/AxGraphCat.lean:151-156`)
orders same-byte reads of DIFFERENT sources only; witness `TsoOfPf.g2Run`/`g2Tso` (cat-consistent, no TsoMem
schedule) — a mixed-size (N10-adjacent) strengthening, hence G2-Q.  NOT strengthenings, recorded against the spike:
**G1** (TsoMem's `.aq` floor = the AMO WRITE's position, `Lang.lean:136,151`; WeakMem's `max(wVrNew, t)` = the READ's
source, `WeakMem.lean:608-626,834`) is an ENCODING/realizability gap of the position-preserving log identification —
rule 5 (`gacqPo`, `WeakRvwmoGraph.lean:214`) puts the AMO gmo-before every later access of the hart, so once the log
is gmo-ordered (Stage 2, `ptraceRel ⊇ gmo|W`) "floor = AMO position" is cat-FAITHFUL (§D G1-Q); **G3** (DMA reads at
the TOP, `dmaView`, `Lang.lean:185`) is the DEVICE MODEL's strengthening over the appendix's DEVICE sentence (§B(11b)
F6, already named), a realizability gap on the pf DISK ROW (`DRead` = `LLoad aq false`, `WeakEvInst.lean:489`).
Dependency order (ppo 9–13) is absent in TsoMem — the sound direction.  Honestly: "xv6 on sRVWMO + reservation
serialisation + footprint coherence".  **Under [OWN.2] this is an INPUT, not the result**: the published theorem is at
RVWMO proper, by robustness (§B(9)).

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
   row `.PDisk none` (`WeakEvCapstone.lean:1027`, booted by `xboot`, `Capstone.lean:90-91`) [R7.3][R5.s5][R5.1];
3. memory [OWN.2]: **RVWMO as the ISA defines it — the TAGGED cat model `rvwmoCatConsistentT GT` over `GdexecT`
   (`Weak/AxDeps.lean:208-211`: `gwf ∧ gppoCatTGmo ∧ gloadValue ∧ gatomicity ∧ gtdepsWf ∧ gtdepsGmo`, rule 12 over
   `gtAd` = the addr/data edges only; rules 1–5, 7-RCsc, 12; omits 6, 7-RCpc, 8; fidelity by litmus,
   `Weak/AxLitmus.lean:29`)** [R6.1].  **NOT the untagged `rvwmoCatConsistent` (`Weak/AxGraphCat.lean:191-194`)**:
   its `gppo12` ranges over the untagged `gdDeps` and so also orders `ctrl;[W];rfi;[R]`, which riscv.cat does NOT —
   the tree calls it "UNSOUND for safety" (`AxDeps.lean:12-18`), machine-checked by `twCatT :876` with
   `twNotCatForget :883`; `catTOfCat` goes cat→tagged, the converse fails (`:22-27`).  The chain runs on `forget GT`
   (W12 spike F1; D33 RULED (a) [OWN.13]).  **I/O accesses are events of the rows** [OWN.14]: `gmem` (hence gmo,
   `gwf`'s membership clause, `Graph.lean:169-171`) includes the new `Lbl.LIo` labels; ppo applies to them as
   riscv.cat is written (§B(11)); their values are device-supplied (no `lbRd`, so `gloadValue`/`grf`/`gfr` are vacuous
   for them BY CONSTRUCTION — the appendix "I/O Ordering": "For I/O, the load value axiom and atomicity axiom in
   general do not apply" [R8.s1]).  W→W reordering and load buffering ALLOWED; every strengthening NAMED;
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
   header says "non-vacuity certified to the first UART store / disk COMMIT" (W13-wit); REACHING `allocproc` is W14;
6. axioms `propext`/`Classical.choice`/`Quot.sound` + `bv_decide` certificates + the three opaques
   (`tools/audit/baseline.json:11-14`), no `sorry`; trusted base named: Sail model, image dump, the TAGGED cat
   transcription and its tagged conformance text `gdexecQconfT` (new trusted-SURFACE text, reviewed against
   `rowDepsT`'s correction (5), `AxDeps.lean:56-60`) [R6.1], the graph-tier fetch model (W5d-G `gzFetch`, §B(4)(iii);
   RULED [OWN.6]), the graph-tier I/O-ordering PLATFORM assumption (W13 `ioResidueGmo`: the (a′) arms of D32
   [OWN.12] restated over I/O-class EVENTS [OWN.14] as (R1)–(R3), §A(†) — the residue over what ppo gives I/O
   events, §B(11)) [R4.2][R5.1][R6.3][R7.1][R7.2].

**Legitimately out of scope:** liveness/fairness, timing, mixed-size fidelity of the cat model (N10), MMIO
ordering beyond the modelled devices, hardware outside the Sail model, power cycles (SINGLE ERA [R2.2]).

**The statement to aim for — three layers.**  *T-alloc* (exists): `Xv6.Allocproc` on MachCSL.  *M1/M2 (internal,
NOT published [OWN.2])*: the composed sRVWMO theorem, pinned/kernel-only (M1) then unpinned (M2), below.
*T-alloc-RVWMO (THE published claim)* [OWN.2][OWN.3][R3.1][R3.2][R3.4][R4.2][R4.4][R5.1][R6.1][R6.3]:
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
      -- INTERIM (W1-Q RULED (c) [OWN.16], until W1b): `allocprocTraceAns` exports "answer = -1 ∨ ∈ [1, PIDMAX]" and
      -- "forkOk → pidPick ∈ [1, PIDMAX] ∨ (pidPick = nextOf = 2^32-1 ∧ answer = -1)"; `poolEmpty` NOT exported.
```
**Names** [R7.s2].  **LANDED by Stage 0 (merged; grep them)**: `execProgOk'S`/`pairAdjacent`/`candSca`/`candKfetch`/
`scaOk`/`admRunG`/`pfRunS` (`Weak/PfRunShape.lean:242,95,85,53,72,224,273`), `srvwmoXv6M1Premises`/
`srvwmoXv6M1PfRun`/`srvwmoXv6M1Satisfiable`/`esilAdmRun`/`execProgOk'SSnoc` (`Weak/SrvwmoXv6Witness.lean:583,596,672,
157,268`), `textPristine`/`textRo`/`powerInterp_textPristine` (`Xv6/TextPristine.lean:38,88,123`), `pidPick_range`/
`allocprocTraceAns` (`Xv6/AllocprocTrace.lean:111,254`).  **NOT in any merged file — workers must not grep for them**:
`GfexecT`, `GT.gfGd`, `forgetF`, `xv6ConfS`, `gfexecConfIO`, `xv6TextAdequacy_closed`, `Gdexec.gdFetch`, `emZifencei`,
`gzFetch`/`gzContrib`/`emFenceI`/`rvwmoCoreD`/`rvwmoCatAD` (scratch only), `Lbl.LIo`/`IoKind`/`lbIsIo`/`gisIo`/
`ioResidue`/`ioResidueGmo`/`gfBefore`/`ptraceRelIO`/`gnxa`/`racyDIO`/`cycleKillIO`/`mstep.MStepIo` (rev 10),
**`tsoShadow`/`scaOkT`/`candScaT`/`diskLatOk`/`candDiskLat`/`pfStepTso`/`pfLoadRow`/`linCandScaT`/(R2′) (rev 13 [W2s];
in `Weak/TsoOfPf.lean` only `histOf`, `fenceRow`, the G1/G2 witnesses)**, `Ioev`/
`ioOrd`/`ioObAcyclic` (scratch, SUPERSEDED), `execProgOkA`/`gfexecConfA` (RETIRED by D38), `ioOrdF`/`emIoFence` (D46 (b)
only), `badSeg`, `linCandSca`, `xv6RvwmoSafeModuloT`, `Weak/ExistWitness.lean`.
(†) `xv6ConfS` is the SHAPED, UNPINNED, FABRIC-ORDERED, TAGGED conformance bundle [R5.1][R6.1][R6.3][R6.4][OWN.14]:
`gfexecConfIO` (W13 (I)/(W): per-row `hartConff` emissions with TWO fabric endpoints, `Fab.lean:261-263`/`hemitf
:238-260`; an I/O access is a TAGGED row item `(l, some k)` whose `pstepEv` moves the fabric `dvi k → dvo k`, so
`gfDev : List Geid` (`Fab.lean:516-518`, type unchanged) lists the I/O EVENTS in fabric order and `isDevBlock em k ↔
(i, k) ∈ gfDev` (`:530`) becomes `gisIo (i, k) ↔ (i, k) ∈ gfDev`; admin stars carry NO fabric move), `fab 0 = efInit
σ0.wgdev`, `rowDepsT` tags in `GT.gtDeps` (`gdexecQconfT`-style; `rowDepsSubT`, `AxDeps.lean:690`, gives the untagged
bundle back), the fetch clause `emZifencei` (W5d-G, replacing `emFetchImg`, `Fab.lean:534`/`Supply.lean:277-278`)
with `F_em ⊆ GT.gdFetch`, exclusive pairs FUSED (the `execProgOk'S` shape of [R3.2], LANDED by W5b [R6.4]) — NOT
today's quiescent `gdexecQconf` (`Weak/WeakRvwmoSupply.lean:281-289`), whose `emDevfree` (`:273`) forbids every
`LDev`.  **Quiescence is VACUOUS for allocproc** (W13 spike CONFIRMS): the event LTS emits `LDev` for EVERY MMIO
access (`Weak/WeakEvInst.lean:300-303,335-338`) and the disk row's START/COMMIT (`:484,502`); hart 0's `main` runs
`consoleinit` FIRST (`Xv6/SpecMain.lean:7-10`) = `uartinitone`'s seven `WriteReg`s (`Xv6/SpecUartinitone.lean:6-13`),
so `userinit → allocproc` is unreachable in EVERY quiescent `GD` (route-b: "HONEST MILESTONE",
`claude-notes/design/weak-memory-route-b.md:1009-1020` [R9.2]); no `LDev`-emitting witness exists (`gfexecConfOfQconf`, `Fab.lean:648`).
**THE I/O ITEM (D38 RULED [OWN.14]; D32 (a′), D37 (a) [OWN.12] carried over)** [R6.3][R7.1][R7.3a]: [OWN.8]'s literal
axiom IS `gfexecConsistent'` (`Weak/WeakRvwmoLin2.lean:761-762`) — it forbids LB and W→W even at an EMPTY fabric
(`lbExcluded`, `Weak/W13Spike.lean:35`): a robustness ASSUMPTION, not a hardware model; and every block-level dev
condition (`gdevAdj ⊆ gmo`, `Fab.lean:539-544`) excludes SC (`scDevExcluded`/`scDevUnrealizable`, `W13Spike.lean:55,66`)
because `execProgOk'` (`WeakAxRealize.lean:373-386`) folds the `LDev` admin block into the NEXT tagged event.  **Rev 10
removes the cause: an I/O access is its OWN graph event `Lbl.LIo kind base vs`** (D47; `IoKind = rd | wr | dev`), a
`gmem` event with its own gmo position, in EVERY row `i < xN σ0 = NCPU + 1`: a hart's MMIO reads/writes (`pnodeStep`,
`WeakEvInst.lean:300-303,335-338`, today `LDev` without payload), the PLIC pin delivery to a hart (`pstepPlic
:461-466`), the disk agent's START/COMMIT (`pdiskProg :481-507`, arms `:484,502`) AND the device threads' fabric moves
at the disk agent (`pdiskUart :514-520` — UART tx/rx, PLIC gateway) — all kind `dev` [R7.3a][D49].  `lbRd`/`lbWr` are `none` on `LIo`, so rf, co, fr, load-value,
atomicity and the log message `gmsg` (`Lin.lean:463`) ignore I/O events BY CONSTRUCTION (device-supplied values,
[OWN.14]); `lbIsR`/`lbIsW` stay RAM-only, so rule 4 (`gfenceCovers`, `Graph.lean:204-209`) and rule 7 skip them —
Sail's `execute_FENCE` keys on `extractLsb pred 1 0` only (`InstsEnd.lean:18299-18313`), after `effective_fence_set`
(`BaseInsts.lean:568-573`), which with FIOM = 1 ORs the i/o bits INTO the memory bits and never the reverse — so the
i/o bits produce NO I/O ordering in Sail unconditionally, and never reach `LFence` at all because xv6 boots with
`menvcfg = 0` (`BootBoard.lean:30`; `start()` sets only STCE) [R8.3d]; the graph can give I/O events NO fence edge
(D48); rules 1–3 give none (`gaccesses` is byte-footprint based); rule 5 `gacqPo`'s `gmem e2` (`:214-215`) DOES
order an acquire read before a later I/O event — a strengthening the appendix's condition (c1) EXCLUDES (quoted in
§B(11b)), subsumed by (R1), vacuous as a trusted use — D52 [R8.3c]; dependency edges through `LIo` are OFF (D50).  **The trusted item
is an INCLUSION, not an acyclicity over an extended order** — gmo is already total over `gmem`: `ioResidueGmo GF :=
∀ x y, ioResidue GF x y → gmoLt GF.gfGd.gdG x y` with **(R1)** `gpo x y ∧ gmem x ∧ ¬ gisIo x ∧ gisIo y` (a row's RAM
accesses po-before an I/O event, READS included); **(R2)** `gpo x y ∧ gisIo x ∧ gisW y` (an I/O event po-before a
row's RAM WRITE — `grule14`'s shape, `Graph.lean:257-258`, with `gmem` covering I/O; reads po-after stay UNORDERED,
the (a′) point [R7.1]); **(R3)** `gisIo x ∧ gisIo y ∧ (gpo x y ∨ gfBefore GF x y)` (same-row issue order — ISA-given
only within ONE channel (F2), cross-channel residue — and fabric order, stated on the ORDER `gfBefore`, not `gdevAdj`,
so hulls that cut I/O events out keep it); **(R2′) [W2s, G3-Q (a″) pending]** `gpo x y ∧ gisIo x ∧ gisR y ∧ y.1 = NCPU`
(an I/O event po-before a DISK-ROW RAM read — the device model's "reads after the MMIO see everything before it", the
DEVICE sentence's direction; hart rows keep reads po-after I/O UNORDERED).  Free when no row has an I/O event (`ioResidueNodev`, the
`ioObAcyclicNodev :109` rank proof re-done) so LB and W→W stay in the quantifier; admits the SC case (`w13f`
re-encoded: gmo `MMIO₀ < MMIO₁ < st < ld` is now a GRAPH, the `w13fIoOk :116` re-check is W13 (T)'s acceptance); does
NOT assume `racyD` acyclicity — the kill carries that.  (R1)/(R2) are REALIZATION-NECESSARY and ISA-given at three
xv6 sites only (§B(11b)); no read arm (`elabOk σ c LDev = True`, `WeakEvInst.lean:558`; TsoMem's MMIO arms touch only
`devs`, `MachCSL/Lang.lean:356-358,372-375`) and nothing needs one (reads have no cross-hart OUT-edge in `ptraceRel`,
`Lin2.lean:124`).  For the disk row (R1) says "DMA writes (plain `LStore`s, drained by `LFence true true true true`,
`:497-498`) are gmo-before COMMIT" — device-MODEL semantics, the one place (T) carries disk correctness [R7.3] (and,
via the one-row model, DMA accesses around UART/PLIC moves — D51).  `candSca` is NOT a premise here: a `Cand`
predicate, ill-typed on `GD`, DERIVED at Stage 2 from `gloadValue` (`linCandSca`, W11) [R4.4].  The conformance
premise is genuine: the graph side alone yields only `execWf`-style facts; the program half is realized by
`execWfPfRunProg` (`Weak/WeakAxRealize.lean:802-808`) [R1.5].  **The pin fixes WHAT a fetch answers, not WHERE it
fetches** [R3.1]: at M1 the premise is `pstepPin` + `candKfetch` (every `LIFetch` footprint in W3's pristine window
`[bcRoLo, bcRoHi)`, §B(4) [R5.2]) — what makes M1 kernel-only; M2 replaces both by CUT-form Zifencei admissibility
on the pf side; the target needs the graph-side twin `gzFetch` (W5d-G).  Boot premises: `xv6FsAdequacy_closed`'s
(`Xv6/LinkSystemAdequacyClosed.lean:20-26`) transposed through `PowerOn` (`MachCSL/Lang.lean:294-304`) to
`wbootFacts` (`Weak/WeakLang.lean:482-490`); `diskOf ds.reset = diskOf ds` from `Xv6/BootSharedDev.lean:283` [R3.s4][R9.2].
(b) is the trace-observable shadow of `allocprocPost` in the NI idiom (`xv6NiPhi`, `Xv6/NiAdequacy.lean:91-92`) [R1.4].
*M1/M2 (internal)*: **M1's premise set IS the DEFINITION `srvwmoXv6M1Premises σ0 c pst dv`** (W5c, `Weak/
SrvwmoXv6Witness.lean:583-591`: `wbootFacts σ0 ∧ σ0.wggen = 0 ∧ (∃ ds, σ0.wgdev = ds.reset ∧ diskOf ds = fsImgDisk) ∧
srvwmoConsistent c ∧ c.cdImg = imgZ σ0.wgimg ∧ pst 0 = epsInit σ0 ∧ dv 0 = efInit σ0.wgdev ∧ execProgOk'S (pstepPin
(imgZ σ0.wgimg) pstepEv) pclsEv (candKfetch bcRoLo bcRoHi) pst dv (candExec c) ∧ candSca c`) — W5 states M1 THROUGH it,
never by re-listing; M2 = `execProgOk'S pstepEv pclsEv fok_cut …` with the cut-form fetch clause as `fok` `∧ candSca c`.
sRVWMO ("RVWMO, stores never early") results stay milestones only [OWN.2]; `xv6RvwmoSafeModuloF` is RETIRED (D39).

## B. Gap analysis

Legend: *need* = needed for T-alloc-RVWMO; *route* = (M) machine tier / (A) AxSL tier (retired [OWN.1]).

**(1) AxSL tier not composed with the machine tier.**  Route (A) only (retired): XL; Theorem 2 = validation (D6).
**(2) Page tables.**  Route (M): CLOSED — kernel table a live shared invariant with A/D variants (`KptInv.pteVariant`),
`utlbOk` "up to A/D" (`MachCSL/UTlb.lean:17-21`) [R1.s3]; user-table pages fresh owned memory (`pptPost`), published
at `satp` + `sfence.vma`; Svadu write-back named in §B(11).  S.  **(3) SIE = 0, 3 harts, no devices/DMA.**  Route (M):
CLOSED (`KCtx.sie`, `wpNext`, `NCPU = 8`, DMA at the store order).  Graph tier: OPEN — the quiescent bundle has NO
devices; the fabric bundle is W13 (§A(†)) [R5.1].

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
`uvmfirst`'s writes: W4's `LIFetch` row has no TsoMem step.  Fix: M1 carries `candKfetch` inside the shaped predicate.
(iii) **The unpinned supply is TWO items** [R4.2], SHAPED by the W5d-G spike (DONE) [R6.4b].  **W5d** (M2, L; in the
target [OWN.3]) is the pf half: `execWfPfRunProgF`, the replay at `pstepEv` with a Zifencei side condition in place
of `fetchPin`.  **Fix now (spike §3.4): the M2 fetch clause is the CUT form `∃ q, itv ≤ q ≤ |log| ∧ ifetchOk img log
q base tvs`** (`fetchCutOk`, `GraphFetchSpike.lean:36`; `ifetchOk` DEFINED `Weak/WeakPromise.lean:222-224`, used
`WeakEvInst.lean:564` [R9.2]; `itvPostMachCSL`,
`Weak/WeakInterp.lean:378-384`), NOT per-byte `ifetchOk … itv` — per-byte fetches tear ([R3.4]; `ifetchByteOk`,
`WeakPromise.lean:222-231`) and the cut form is what W5d-G produces; W4's (↓) `LIFetch` row then holds for user text
(TsoMem reads at `tvn := q`) and W2's `R` carries `itv ≤ q`.  **[W2s] Two corrections**: (i) `ifetchByteOk … q` admits
a byte source `t > q` (its window `(t, max t q]` is EMPTY, `WeakPromise.lean:222-224`), which TsoMem at `tvn := q`
cannot read — the cut form adds `t ≤ q` PER BYTE (W5d; W5d-G's G5 `gzFetchCut` must produce it, or a torn fetch slips
through); (ii) the pf machine has no `itv`: the clause's `itv` is the SHADOW's (`tsoShadow`, §B(10): `fence.i` →
`max itv (fencePost true false tv rv pub)`, `Lang.lean:155-163`), supplied by W5d, so `R-itv` is `itv_T = itv_S ≤ q`.
**W5d-G** (Stage 2, **L** ≈ 1.8–2.2k + ONE XL risk; was
"L–XL unverified") is the graph half.  **Verdict: keep the fetch an ADMINISTRATIVE emission item** (`hemit`'s `eadm`,
`Weak/WeakRvwmoConf.lean:712-722`; `lbAdmin`, `WeakAxRealize.lean:130-134`) and add a RELATIONAL Zifencei condition
plus a "fetch fragment" of ordering edges stored as graph data, as `gdDeps` stores the store-dep fragment — NOT a
graph event ([R4.s1]'s `IF`-event shape gives the same edges at much higher cost); semantically it IS the `IF` event
at a gmo position, encoded as an EXISTENTIAL cut.  **The trusted-base item
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
D40).  Scratch: proved `fetchCutOk`, `fetchCutPrefix :63` (cut form = the pf/W5d check at the realizing prefix, ONE
view), `fetchCutEdge :83`, `fetchRelOk`, `fetchRelCut :140`, `fetchPinCutOk :213`; stated `gzFetch`, `gzFetchCut`,
`emZifencei`, `gfcut`, `gwlog`.  **Kernel-text instance**: tag 0, image bytes, no write ⇒ (Z1)–(Z3) vacuous;
`candKfetch` + W3's `textPristine` discharge `gzFetch`; kernel-only executions get an EMPTY fetch fragment.
Consumption (`W5dG-spike.md`): edges E1 src→nxw, E2 c→w', E3 src_l→w'_j, `gmoLt` on `GD` by (Z2)/(Z3), stored as
`Gdexec.gdFetch` (D42), `F_em ⊆ GD.gdFetch` in `xv6ConfS`; retime via `L ⊇ racyD ∪ F` (the contributor SET is rf/po-
defined, retime-invariant; `normalizeOfAcyclic` renames write indices NON-monotonically, `Topo.lean:594-607`); realize
by replaying the fetch before `(i,k)`'s step at log `gwlog.take gfcut` (`linPrefixLog`, `fetchCutPrefix`).
Measured sites: `pstepPin` 19 files/121, `emFetchImg` 10/41, `gdexecQconf` 18/124, `gdDeps` 31/133, `wlblRen` 3/41.
Sizes: W3 DONE (≈ 1.9k incl. twins) [R5.2]; W5d L; W5d-G L (G1–G5; G6 shared with W11 (iii); G7 L in W11/W8); **XL risk R1 — hull
closure**: `hullOk` is rf-closed only (`WeakRvwmoHull.lean:557-560`) and knows nothing of fetch sources — a kept
fetch whose next own write was cut away loses its source; fix (a, recommended): anchor sources to EVERY po-later
memory access (E1′, stronger but gmo-true (H3)), then "kept fetch ⇒ source kept" follows from racyD-closure (M if the
cut selection is racyD-driven, XL if `t2linAux` must be re-proved); (b) keep E1 and let hulls cut each hart only
directly after a memory event (re-check `t2linAux`'s cut selection).
**(5)–(8) Segment coverage, scope pins, store-value rows, stack/cpu privacy.**  Route (M): CLOSED (F1; the pid
ledger handles wrap/collision retries, `Xv6/ProofAllocproc.lean:16-24`; text facts by `rfl`/`decide`; real
`stackOwn`/`kctx` resources).

**(9) THE gap: TsoMem is sRVWMO + reservation serialisation; the target is RVWMO proper** [R1.7][OWN.2].
*Inventory of weaker models in the Lean tree.*  (α) `WeakMem` pf machine = sRVWMO operational (T1
`srvwmoRealizable`, `Weak/WeakAxiomatic3.lean:2077`; T2 `t2Ev`, `Weak/WeakEvInst.lean:2046`) — TsoMem's strength
class; (β) `WeakPromise*` (`Weak/WeakPromise.lean:1-16`) — LB reachable, RVWMO fidelity BY INSPECTION only; (γ) PSO
two-log machine: NOTHING in Lean; (δ) graphs: the tagged cat model (§A(3)), the untagged `rvwmoCatConsistent`,
`rvwmoMinusDepsConsistent` (`WeakRvwmoGraph.lean:628`).
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
through `gpoloc`'s W→R edge — the edge cat lacks; CLOSED in the scratch (`racyDSplitC`: rfi → `rsameC`, `gcrossE` =
rfe ∪ co ∪ fr from `gwf` + lv only; §C W12 (2)).  **Gate 2 (lock kit)**: `csChained` (`KillArms.lean:499`) and the
`acq*` lemmas use rules 1, 4, 5 only (`Lock.lean:120,125,200,235`) — CLOSED, re-proved verbatim as `*C`.
**Gate 3 (the certification walk's floor kit — W10's toolkit) BREAKS, needs a REDESIGN**: `gvisUb G r n` = "every
write of index ≤ n is gmo-before r" (`Weak/WeakRvwmoFloor.lean:100-101`) is FALSE under cat for an own store forwarded
to a po-later read (it may be gmo-AFTER); `greadSrcUb` (`:442-453`) closes its po case with `gpolocGmo` W→R,
`finvStep` (`:605-619`) uses it for the coh hook; consumers `cinvReplay`/`floorOfCgraph`/`certFloorOk`/`cpolRead`
(`Cert3.lean:311,391,428,468`) via `wblkPolAt` (`Walk.lean:700-731`).  The FLOOR itself holds (`t = gwix w`;
co-maximality covers po-visible writes) but needs a per-byte coherence invariant (rules 1/2) in place of `gvisUb` —
Floor §4–§6 and Cert3 §2–§3, ≈ 0.5–1k (M–L) = **W12b** (D34).  Two smaller mismatches, VACUOUS for kernel rows
(release = `fence rw,w; sw`, `Xv6/ProofRelease.lean:83-86`; acquire = `amoswap.w.aq`), OPEN for user rows [OWN.3]: the
`wVRel` hook consumes rule 7 RCpc (`Floor.lean:21`), which `grcsc` (`AxGraphCat.lean:163`) lacks (D35); WeakMem's
forwarded ACQUIRE load (`fwdView ws true a t = t`, `WeakMem.lean:585-591`) is stricter than cat (D36).  **So the gap is
CONFINED to the kill AND the walk floor** — not the 33k lines.  Witnesses need NO re-proof (`catADOfMinus` ∘
`minusImpliesCat`; corrects [R5.s1]).  Residual premises `l2ClaimAt`/`cutSupply`/`certSupply`/`walkSupply`/
`walkPolicy` are re-hypothesised; their discharges (W8–W11) must handle FORWARDING graphs (TsoMem forwards — fine).
*Why plain DRF does not apply.*  xv6 races by design.  The Lean pin census at THIS image [R4.1]
(`Weak/KernelPins.lean:22-23`, by `tools/gen_weak_pins.py` at `b72cbac1`): **1689 load sites: 1034 `PStack`, 3
`PPerCpu`, 289 `PCtrl`, 1 `PFence`, 180 `PDep`, 63 `PCall`, 119 `PResidue`; 58 certifying witnesses need the
sp-frame assumption `own = true`** (`KernelPinsDef.lean:447-465`).  Racy flag reads (`started`, `panicked`, UART LSR,
virtio `used->idx`, `ticks`, `p->killed`, `p->state`) are pinned by branch/fence/lock.  The applicable theorem is
ROBUSTNESS UNDER A PER-SITE DISCIPLINE (L2′ = `l2Claim`, `Weak/WeakRvwmoGlue.lean:449`: per cycle segment `segPin ∨
csHyps ∨ Bad`, `:229,400,440`) — DRF generalised: every cross-hart read is pinned by ppo before the hart's next store,
or is lock-protected (`protRead`/`wprotAt`, `Weak/WeakGhost.lean:3408,1040`), or observes an owned-unpublished message
(`Bad`).  The discipline must be established on the STRONG model's executions; the only verified source is the TsoMem
Iris proofs — which today export `mmOk` only (`MachCSL/Resources.lean:779-785`), nothing per access.
*The routes, sized candidly* [R6.s3, RULED]: **(9a)** re-verify xv6 on a weaker MachCSL instance (none exists; Xv6
cone ≈ 0.65M lines over 77k of `MachCSL`; PSO alone "2–4 weeks is the floor" in Rocq, LB has no design; linking to cat
needs a Promising≡RVWMO-grade theorem) — **XL × 2, rejected**.  **(9b)** PSO two-log machine W6 (L–XL; "RVWMO minus LB
minus deps"; LB robustness still needs the per-site discipline) — off the path, optional de-risk of W8's export (D4).
**(9c)** promise-machine robustness W7-P (`robustMain`, `Weak/WeakRobustMain.lean:1520`; fidelity EXTERNAL) — **fails [OWN.2]**, D2′ fallback only.
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
  (PDep ⇒ `rowDeps` ⇒ `gdDeps` ⇒ `segPin`, `WeakRvwmoPinBridge.lean:284-330`), `pinSegPin'` with `checkerTaintSubProv`
  DISCHARGED for the oracle `psites` (`PinBridge2.lean:530-553`); the callee-summary table is an unread audit artifact
  (`claude-notes/design/weak-memory-route-b.md:1456-1460` [R9.2]).  **W9b**: the non-certifying classes are W8's INPUT, not `segPin` — `PStack`/`PPerCpu`
  (1,037) and the 58 `own = true` witnesses = W8's ownership (i); `PCall` 63 + `PResidue` 119 = 182 sites = W8's
  (ii)/(iii) (D28 RULED (a) [OWN.7]).  W8–W13 are specified in §C Stage 2.  Sizes (✓ = spike-confirmed): W8 L–XL,
  W9a L ✓, W9b in W8, W10 M–L (**unverified**; L if it absorbs W12b), W11 L [R4.3], **W12 M–L ≈ 1.2–1.8k ✓**, **W12b
  M–L ≈ 0.5–1k ✓**, **W5d-G L ≈ 1.8–2.2k ✓ + XL risk R1**, **W13 XL ✓ ≈ 7–10k lines / ~70 files (+ ≈ 0.5k under
  G3-Q (a″): (R2′), disk-read anchors [W2s])**, **W2 L + W5b′ S–M ✓ (spike-sized)**, **W4 L** ((E) wide and
  shallow; (R) the bulk).  **Total: XL** — multi-week; W13 the bulk, W5d-G's hull closure the open risk, W14 = non-vacuity.
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
`LExLoad` is realizable as a plain `LLoad` (`lbNobarex`, `:97-103`; `projLbl`'s `LExLoad → LLoad` arm,
`WeakPromiseBridge.lean:541` — [R9.2-alt]: R9 wrote `:543`, which is the `LIFetch` arm; `:537` `LDev`) while TsoMem's dangling
reservation blocks foreign stores and its exclusive read takes `topBytes` (`Lang.lean:147-153,368-371`) — (↓) fails.
**[R3.2] the shape cannot be a separate conjunct on `(c, pst)`**: the realizing `l` and the stars are existential per
index inside `execProgOk'` (`WeakAxRealize.lean:373-386`; `admStar = rtc admStep`, `:343-344`), so the premise is ONE
shaped conformance predicate **`execProgOk'S pstep pcls pst dv E`** := `execProgOk'` with (i) the left disjunct's `l`
not an `LExLoad` (re-imposing `lbFused` on the left arm only, cf. `lblRealizesUnproj :245-247`), (ii) the stars as
label-carrying `admRun`s (`Weak/WeakRvwmoConf.lean:374-381`) whose every `LIFetch` is in kernel text (M1,
`candKfetch`) / cut-form Zifencei-admissible (M2), (iii) every `LLoad` single-copy-atomic (`candSca`, below).
**LANDED (W5b DONE): `execProgOk'S pstep pcls fok pst dv E` (`Weak/PfRunShape.lean:242`, ARITY 6 — the fetch clause
`fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop` is a PARAMETER: M1 `candKfetch bcRoLo bcRoHi`, M2
the cut form; (ii) checks `fok` on the LEADING star only — the intra-pair star is `lbAdmin false`, fetch-free; (iii)
per index) and `pairAdjacent :95`** [R6.4c] over the STEP LIST; under D38 RULED [OWN.14] the I/O step is an ORDINARY left-arm realizing step (`l = LDev kind base
data …`, `projLbl … = some (.LIo …)`), so the shape clauses need only an `LDev` case (rev 9's `execProgOkA` co-design
is gone).  **`pairAdjacent`** (NEW, coined by R2; ONE text for W2 and W5b [R5.3]): *in a shaped run every
realized exclusive pair's halves `l1 = LExLoad …`, `l2 = LExStore …` (`lblRealizesPair`, `:305-313`) are consecutive
steps of the SAME hart up to its own `LInstr`-free star `admStar pstep false pm dm pm2 dm2` (`execProgOk'`'s right
arm, `:380-386`, one exec index); no other agent's step — no foreign store — lies between them*, plus the fetch/SCA
facts along the run (`pfRunS`/`pfStepFacts :273,265`); W5c PRODUCES it (`execProgOk'SNil`/`execProgOk'SSnoc`,
`SrvwmoXv6Witness.lean:260,268`, the S-variants of `Cert.lean:413`).  At Stage 2 `RunData`/`cstOk`/`segStep`/`topoSupply`/`t2linSupply` (plain
`execProgOk'` today) produce the S-variant — W11 (iii) [R4.3], one pass with W5d-G's G6 (`pstepPin` → `execProgOk'S`,
19 files / 121 sites: AxRealize 26, Supply 14, Cert 9, Cert2 8, Fab 7, Cert3 7, SrvwmoCapstone 6, CycWit 6, Cert4 6,
AxAdequacy 6, Cert3b 5, LinInd/Lin2/FabInd 4, Capstone 3, Glue/ConfWit2 2, Glue2/AxRunGV 1 — the one list; §C cites it).
**[R3.4] (↓) fails on PLAIN LOADS even on shaped runs — tearing.**  WeakMem's `readable` is per byte
(`Weak/WeakMem.lean:400-402`; `readOkD`, `WeakPromise.lean:183-188`; `rdOk`, `WeakAxiomatic.lean:122-130`), no axiom
joins one label's bytes (N10); TsoMem reads every byte at ONE `tvn` (`Lang.lean:363-367`) — a floor-0 load with `ts =
[4,4,6,6]` over two word stores is sRVWMO-consistent, never TsoMem's.  RMWs exempt (`rmwLatest`,
`WeakAxiomatic.lean:134`); fetches have the cut form (§B(4)(iii)) as their SCA.
The ISA guarantees single-copy atomicity for NATURALLY ALIGNED accesses ≤ XLEN only, so the premise is **ISA-faithful
for naturally aligned accesses; a misaligned user load is covered by N10's out-of-scope note** (D20 Spec) [R9.1] — NAMED
**`candSca c`** (LANDED `PfRunShape.lean:85`; `scaOk :72`: `∃ tvn ≤ |log|, ∀ j, ts[j]` is the latest write to byte `j`
visible at `tvn` — `≤ tvn` or the hart's own, `scaVis :61`, TsoMem's `Hist.read`; NO floor normalisation: `tvn` is not
tied to the hart's view, so `R` carries it per load, §B(10) `R`).  W2's "plain load" row is (↓) iff `candSca`;
alternative = an atomicity axiom in sRVWMO (re-opens T1, XL) — D20.  **At Stage 2 `candSca` is DERIVED**
[R4.4]: `gloadValue` (`Weak/WeakRvwmoGraph.lean:238-243`) puts ONE gmo position per LOAD EVENT — each byte's source
`gvisible` (`:236`) and co-MAXIMAL among visible same-byte writes — so a torn read is already inconsistent;
`topoSupply` linearizes the NORMALIZED `GD'` and `linCand` (`WeakRvwmoLin.lean:471`) copies labels, so `linCandSca :
rvwmoMinusConsistent G' → grule14 G' → candSca (linCand G')` (S, W11) feeds W5b's replay; `fetchCutPrefix` (W5d-G)
plays the same role for fetches.
*(↑) receptiveness is NOT available on route (M)* [R2.3(iv)]: weak-side `Reducible` would need the weak WP package;
(a) is stated for the realizing MachCSL run, the free weak-side sentence is "the realized pf run never enters the
retry arm" (D15).  *Single era* [R2.2]: `epowerFork` forks no power thread (`Weak/WeakEvLang.lean:201-204`), so
multi-era conclusions are NOT transported; W4's run is prefixed by the `PowerOn` step (D14).
*Layer 2 after the W2 spike [W2s] (D7 STOP → RESOLVED-BY-REDESIGN; G1-Q–G3-Q in §D).*  **The per-label (↓) table**
(`W2-spike.md`; its faithful/stronger/weaker column [R9.s4] is MISSING — D7's marks stand in): ✓ `LSilent` (0 TsoMem
steps — **W4 is a STUTTERING simulation**), `LInstr`/`LRegW`/`LCtrl`, `LIFetch` M1 (pristine text, `Wp.lean:1478,
1490`), hart `LStore` (`¬ othersReserve` from `pairAdjacent`), disk `DWrite` (`storeDma`, `¬ anyReserve`), `LFence`
non-`fence.i` (**`fenceRow`, PROVED**), `fence.i` (identity vs `itv`), the parked `fence rw,w` (0 steps; `wRelp`/`wPub`
inert — suspect CLOSED), `LExStore`, `LDev`; **conditional**: `LIFetch` M2 (§B(4)(iii) (i)–(ii)); hart `LLoad` iff (★);
`LExLoad aq` bytes ✓ (`exclOkTs` + `pairAdjacent` make `t` = `topBytes`), views ✗ (G1/G1′); **✗** disk `DRead` (G3).
Suspects: fence-clears-reservation VACUOUS on shaped runs; tearing CLOSED by `candSca`; parked release CLOSED; the `.aq`
off-by-one REFUTED as sized — it is G1, off by `top − t`.  **Only `fenceRow` is in Lean: the positive rows are ARGUED,
not proved**; `pfLoadRow` under (★) needs FlatMem ↔ `histOf` lemmas (L).
**The gaps.**  **G1**: after `amoswap.aq` reading the lock word at `t` (write at `top+1`) TsoMem's floor is `top` at
the read and `top+1` after the pair (`Lang.lean:136,151`; `tsoAqPairTv`), WeakMem's `wVrNew` is `max(wVrNew, t)`
(`exloadPostRunD`, `WeakMem.lean:834`; `loadPostAt :608` aq arm): a later plain load of a byte written in `(t, top]`
reads stale in WeakMem (`g1Run`; cat-consistent: gmo = AMO, `ld x`, `x := 1`), TsoMem cannot.  The image's `acquire`
is `amoswap.w.aq; sext.w; bnez; jal mycpu; sd a0,16(s1); ld …` (`KernelImage.lean:2265-2290`) — NO fence after the
swap, the whole critical section sits in the window; `release` = `fence rw,w; sw zero` (`:2361`), `sr = false`, leaves
`wVrNew` alone.  [Correction: NO fence closes the window — fences raise `wVrNew` only to `wVrOld`/`wVwOld`
(`WeakMem.lean:674-688`), neither need reach `top+1`; the debt persists until the hart's view passes it otherwise.]
**G1′**: `rv := top` at ANY exclusive read (`afterExcl`, `tsoExclRv`); a later `fence r,*` lifts the floor there.
**G2**: §0 F1 (iii).  **G3**: `dmaView` reads the TOP (`Lang.lean:185,535`); the disk row's `DRead` is `LLoad aq false`
at the disk agent's floor.  [Correction: `dreadAvailIdx` is an ACQUIRE read (`VirtioProg.lean:375-376`, `aq = true`),
the ring/descriptor/data reads plain (`:378-386,606-619`): the MP pattern HOLDS in WeakMem — descriptor reads see every
write log-before the avail index the device observed; the gap is staleness w.r.t. the TOP (an older avail index →
`DIdle` where TsoMem's device serves the request; a descriptor/buffer byte re-written in `(t, top]`), not "no fence after START".]
**The redesign — ONE mechanism for G1/G1′, the `coh` side of (★) and the M2 cut: the TsoMem view SHADOW.**
`tsoShadow st i : (tv, rv, coh, acq, itv)` is TsoMem's per-hart read side REPLAYED deterministically over the pf step
list (`Lang.lean:134-163` per label; `pub` from the log; a plain load at the MINIMAL legal view `tvn := max(F, max_{foreign j}
t_j)`, `F := max(tv, coh over the footprint)`).  Then **`R-view` is EQUALITY** `tv_T = tv_S`, `hr_T = hr_S`, `itv_T =
itv_S` — no debt bookkeeping; `R-log/position/author` (`σ.log[k]` = `(pcLog[k]).wmTid` as an agent; hart `i` =
`hartAgent i`, the disk row = `diskAgent`), `R-hist` (`σ.mem[pa]? = histOf img log (paZ pa)`, timestamp = position + 1),
`R-img`, `R-resv` (`none` unless mid-pair) are the spike's.  [Correction: the spike's `tvn := max(tvn_sca, F_T)` is
too LARGE — `rv_T := max rv tvn` would outrun `wVrOld` and break `R` at the next `fence r,*`; take the minimal view.]
**`candScaT`** (G1-Q (e), recommended) := `scaOk` plus `F ≤ tvn`: the SCA witness is at or above TsoMem's floor, so
the minimal view reads the pf bytes and (★) is DISCHARGED for hart loads.  Stage-2 derivation (W11 (iv) `linCandScaT`,
M): the log is gmo|W-ordered (`ptraceRel`, `Lin2.lean:124`), the SCA witness is the load's gmo position; rule 5
(`gacqPo`) / rule 4 (`fence r,*` after the pair's read half) puts the pair gmo-before the hart's later loads, and a
FUSED pair's trace position IS its gmo|W position, so `top` at the pair ≤ the later load's position — G1 and G1′; the
`coh` part by rule 2 (`gppo2`) once G2 (a) stamps per byte.  At M1/M2 `candScaT` is a PREMISE (restricts the
candidate's log order to a gmo-extension — internal milestones only).  **`candDiskLat`** (G3-Q (a″), recommended) :=
every disk-row `LLoad` is `latest` per byte — the `lat = true` CONDITION of `readOkD` (`WeakPromise.lean:183-188`) as a
SHAPE clause, NOT a label change (`latFree`, `WeakPromiseFact.lean:61`, consumed in 16 files incl. `lblRealizes`,
`AxRealize.lean:241`, and `pstepEvLatFreeProg`, `WeakEvCapstone.lean:1052`, stays TRUE): the `DRead` row then matches
`dmaView`.  Stage-2 derivation: disk-row reads become rule-14 ANCHORS of (L) (`gnxa` ∋ disk reads: the trace respects
gmo between a disk read and EVERY write) — consistent because the disk row's po is gmo-ordered by (R1) (DMA writes →
COMMIT), (R3) (COMMIT → next START), (R2′) (START → reads) and rule 14 (a request's reads precede its writes,
`VirtioProg.lean:606-619`); `normalizeOfAcyclic` keeps the anchors as it keeps I/O positions.  **G2**: NO shape clause
closes it (`g2Tso`: every legal `tvn₁ ≥ 2` stamps `coh b`; the minimal view does not help) — G2-Q.  **(★) for a plain
load of hart `i`**: no write by another agent to byte `base+j` in `(t_j, F]` — a LOG-LEVEL fact about ONE load ("no
foreign write to the bytes I read between my source and my floor"), the export shape W8's design gate needs: by
discipline for lock-protected (the protected bytes are not written between the release store `t` and the acquirer's
pair), own and pristine bytes; NOT in general for racy bytes (W8 (ii)/(iii)); under `candScaT` + G2 (a) it is
DISCHARGED, so W8 exports it only if G2-Q = (b).  **Log identification** (W8/W11 vocabulary): pf message `k` = the
TsoMem store at timestamp `k+1`, same author/footprint/bytes; classes stay pf-side (`wmAk` has no TsoMem image;
`protReg`/`badSeg` read the pf log).  W14's SC run is unaffected (every load at the top).  (↑) NOT claimed.  Size: L
(↓: `pfStepTso`, `pfLoadRow`) + S–M (**W5b′** `Weak/TsoShadow.lean`: `tsoShadow`, `scaOkT`/`candScaT`, `diskLatOk`/
`candDiskLat`, `pfStepFacts` extension) + L (W4, stuttering, disk rows) + M (W5) + M–L (W5c ✓) + L (W5d).  It lifts the
WHOLE system theorem; (9d) reuses it both ways; **the log identification carries `protReg` and `¬ badSeg`** (W11).

**(11) Model fidelity and named assumptions (trusted base, list in the header)** [R1.1][R1.7][R2.4][R3.1][R3.2]
[R3.4][R4.2][R4.4][R6.1][R6.2][R6.3].  Candidate/conformance premises: `execProgOk'S` (fused exclusive pairs — "a
dangling LR or failing SC is outside the theorem", D19; M1 only: `candKfetch`, D21); `candSca` (ISA-faithful for
naturally aligned loads, D20 [R9.1]; **M1/M2 ONLY** — derived at Stage 2); cut-form Zifencei admissibility (M2); **the published model is the
TAGGED cat transcription** `rvwmoCatConsistentT` + the tagged conformance text `gdexecQconfT` (NEW trusted-surface
text; the untagged model's rule 12 is a strengthening of riscv.cat the tree marks UNSOUND — D33); **the graph-tier
fetch model** (W5d-G `gzFetch`/`emZifencei`, readings (H1)–(H3), §B(4)(iii) — NO reference model, RVWMO has no
instruction-fetch model; D27 RULED (a) [OWN.6]); **the graph-tier I/O-ordering PLATFORM assumption** (W13
`ioResidueGmo`: (R1)–(R3) of §A(†) over every row's I/O events — hart MMIO, PLIC pin deliveries, the disk agent's
START/COMMIT, the device threads' fabric moves; D32 RULED (a′), D37 RULED (a) [OWN.12], D38 RULED [OWN.14]; no
reference model [R7.1b][R7.3a]).  **Stated as a RESIDUE** [OWN.12], split EXACTLY: the GRAPH MODEL gives I/O events
rule 5 (acquire read → later I/O; a strengthening of (c1), D52) and NOTHING else — no rule 4 (the i/o bits die in
Sail's decoder, FIOM = 0, §A(†) [R8.3d]; `LFence` is `pr pw sr sw`, `WeakAxiomatic.lean:90`), no rules 1–3 (no byte
footprint), no dependency edges (D50 default) — while the ISA PROSE additionally gives (F1)–(F6) (§B(11b)),
expressible only via D46 (b); the ASSUMPTION is the rest — each I/O access acts as a ONE-WAY FENCE for the issuing
row's RAM accesses, and I/O accesses serialize as the fabric does.  "PMA strong ordering" is NOT a justification (it
orders I/O accesses within one channel, never against main memory; D37(c) dropped) [R6.3ii][R7.2b].  The platform is
D37 (a)'s (QEMU TCG), host-dependent.  **Trusted USES, per arm** [R6.s4][R7.2c][R7.3d][OWN.12][R8.2b], list in the
header: (R1) for RAM STORES before an I/O event — `plicinithart`/`plicinit`, `uartinitone`'s seven `WriteReg`s, the
lock's store half and prior stores before `uartputc_sync`'s LSR read and `virtio_disk_intr`'s STATUS read, EVERY RAM
store po-before a PLIC pin delivery (`pstepPlic`, `devintr` entry on all harts — (F5) orders pre-trap LOADS only), the
device row's DMA accesses before a UART/PLIC move (D51); (R2) for every device STORE not followed by a PO-fence — THR,
NOTIFY (`0x80005c92`), `plic_complete`, `plicinithart` (only the ACK at `0x80005d52` is fence-covered, and under D48
(a) even that is a GRAPH-tier use), the device row's DMA writes after a UART/PLIC move (D51); (R3) cross-channel issue
order (UART then PLIC in `main`) and the unlocked cross-hart PLIC claim/complete races.  NOT uses in the ISA-prose
sense (GRAPH-tier uses until D46 (b)): the pre-NOTIFY direction (two `fence iorw,iorw`), the post-ACK loads (the third
fence), loads before a handler's claim (precise traps), dependency-pinned sources of a device store; not uses at all:
the disk row's DMA-before-COMMIT (device model), the racy flags `pr.locking`/`panicked` (stale reads stay in the quantifier).
**User-row gaps under [OWN.3]** [R6.2] (D35/D36 RULED (a) [OWN.13]): rule 7 RCpc and forwarded plain `LLoad aq`, both
vacuous for kernel rows.  Strengthenings carried INTERNALLY by TsoMem/sRVWMO (gone once (9d) lands): "stores never
early"; reservation serialisation.  Machine-model choices: exactly 8 harts booted; **ONE sequential device row** (`i =
NCPU`) for the disk program, the UART threads AND the PLIC gateway (`pstepDisk = pdiskProg ∨ pdiskUart`,
`WeakEvInst.lean:522-526`; Rocq deviation 5) — so (R1)/(R2) order the disk's DMA accesses against UNRELATED UART/PLIC
moves: a model artifact, STRONGER than any spec text, named as D51 [R8.2a]; Svadu A/D write-back as a plain
view-neutral LR/SC; DMA as a store-order agent; TsoMem's instruction-fetch model (`MachCSL/TsoMem.lean:34-39`,
`Lang.lean:360-362,155-163`) — beyond RVWMO's text (Zifencei); the SC-failure model (`Xv6/UserMemLrsc.lean:7-12`;
D17); single era.  Fidelity: the cat transcription omits rules 6, 7-RCpc, 8 (sound direction for THOSE),
litmus-checked only; the published quantifier IS cat (tagged) — D25 (a) RULED [OWN.5], spike-CONFIRMED, W12 on the
critical path, no RVWMO⁻ fallback; Sail fork `070832a1` with `-D SYMBOLIC`; the image dump.  Keep, list.
**(11b) Faithful RVWMO I/O, evaluated [OWN.12] — verdict: INFEASIBLE as the realization's ordering source; (a′)
RULED, restated as the residue; optional audit D46.**  Read-only evaluation; every claim about the ISA text is a
reading of PROSE: the RVWMO chapter says I/O memory, instruction fetch and `sfence.vma` are "not (yet) formalized" and
gmo is over "the primitive load and store operations generated by memory instructions"; riscv.cat has NO I/O events —
a faithful I/O model is itself a NEW trusted-surface transcription.  **The ONLY ISA text saying which ppo rules apply
to I/O is the explanatory appendix's "I/O Ordering" subsection** (`riscv-isa-manual` `src/unpriv/mm-explanatory.adoc`,
fetched by R8, not in this tree) [R8.3a]: load-value/atomicity "in general do not apply"; ppo "still generally
applies" when one access is I/O and one of FIVE conditions holds — **(c1)** ppo as in the RVWMO chapter,
"with the exception that acquire and release ordering annotations apply only from one memory operation to another
memory operation and from one I/O operation to another I/O operation, but not from a memory operation to an I/O nor
vice versa"; **(c2)** overlapping addresses in an I/O region; **(c3)** the same strongly-ordered I/O region; **(c4)**
either in a channel-1 region; **(c5)** the same channel other than 0; then **the FENCE sentence** "To enforce ordering
between I/O operations and main memory operations, code must use a FENCE with PI, PO, SI, and/or SO, plus PR, PW, SR,
and/or SW" (also the normative pointer the privileged "Memory Ordering PMAs" section defers to — quote THAT section
verbatim once fetched [R8.s5]), and **the DEVICE sentence** "implementations must assume that the device may attempt
to access memory immediately after receiving the MMIO signal, and subsequent memory accesses from that device to
memory must observe the effects of all accesses ordered prior to that MMIO operation".
*What the ISA gives (`ioOrdF`, the faithful hart arms), against those conditions:* **(F1)** FENCE with i/o bits (the
FENCE sentence; Unpriv. FENCE: "the EEI will define which memory addresses … will be treated and ordered as device
input and device output operations") — `fence iorw,iorw` orders every prior RAM and device access before every later
one; **(F2)** (c2)–(c5): po-loc among I/O accesses and a hart's accesses to ONE strongly-ordered channel in program
order among themselves (faithful minimum: one channel per device — UART0/UART1, PLIC, virtio; the CLINT never reaches
the language, `MachCSL/Dev/Fabric.lean:10`, `timerinit` is Sstc CSR-only) — the platform declares NO channels (`bootPMA`,
`MachCSL/Platform.lean:199-239`: one `IOMemory`, non-idempotent window `[0x2000000, 0x12000000)`; Sail's `PMA`
structure has no ordering/channel attribute, `LeanRV64D/Defs.lean:549-566`), so CROSS-channel order is not given;
same-address rules are vacuous RAM↔MMIO; **(F3)** (c1) dependencies: addr/data/ctrl into a device STORE (ppo 9–11;
herd's `ctrl` reaches every po-later store after the dependent branch), addr into a device load; ctrl into a device
LOAD is NOT ppo — the only basis is the PMA non-idempotency text ("no speculative access to a non-idempotent region"),
a reading to be NAMED; **(F4)** aq/rl: (c1)'s exception verbatim — they do NOT order memory↔I/O (so `gacqPo` over I/O
is a NAMED strengthening, D52, not "a reading"); **(F5)** precise traps: earlier instructions COMPLETE before a trap
is taken, so a load/AMO po-before an interrupt handler has its value before the handler's MMIO, a STORE need not be
performed; **(F6)** the device rows' own order (virtio DRead/DWrite/DFence/COMMIT, `pdiskProg`) and the fabric
sequence `fab` are the device MODELS' — already trusted, not platform — with ONE ISA-prose anchor [R8.3b]: the DEVICE
sentence says that after the MMIO the device's memory accesses observe everything ordered before it — the ISA reading
of the pre-NOTIFY `fence iorw,iorw` → device-reads-the-descriptors path; the device MODEL (DMA reads at the TOP of the
store order, `MachCSL/Dev/DevLang.lean:20-21` [R9.2], `dmaView`, `Lang.lean:185,535`) is the STRONGER "reads at the top" form.
*What the realization needs (model-independent):* TsoMem and the pf machine run each row sequentially — an I/O step
sits at its po position, a store enters the log at its step, a load never reads from the future — so the realized
trace is a linear extension of `po ∪ rf ∪ gmo'|W ∪ gmo|IO` (Lin2's `ptraceRel` + (L)); hence (R1) (any `gmem` x) and
(R2) are REALIZATION-NECESSARY on every row [R7.1iii].  *(1) Paths and dependence.*  allocproc's own footprint touches
MMIO only through `panic`/`printf` (`uartputc_sync`: LSR loads, THR store) and, with interrupts on during the `proc[]`
scan (`wpNext`), through `devintr`'s PLIC claim/complete, `uartintr`, `virtio_disk_intr`; reaching it needs
`consoleinit`/`uartinit`, `plicinit(hart)`, `virtio_disk_init`, and `fork → allocproc` needs `exec("/init")`'s disk
I/O.  The published CONCLUSIONS depend on NO memory↔MMIO ordering: TsoMem's MMIO arms move no view (`Lang.lean:
356-358,372-375`), the Xv6 proofs read `fence iorw,iorw` as the MEMORY floor rule (`ProofVirtioDiskIntr.lean:92-99`),
DMA correctness is (F6), no conclusion names the UART wire order (`uartSentSub` is D9; `xv6NiPhi` counts accepted
bytes, `NiTrace.lean:198-203`); only the REALIZATION of `GT`'s fabric sequence depends on it.  *Decoder evidence:*
§A(†) (Sail drops PI/PO; FIOM = 0; `fenceDrains`/`fenceAcq` `TsoMem.lean:356-364`, `ebarNow` `WeakEvLang.lean:733-745`,
`ebarLabel` `WeakEvInst.lean:272-275` never see i/o bits); the bits survive ONLY in the instruction word (D48),
recoverable as `emFenceI` recovers `fence.i`: `emIoFence` — S–M, a fence FRAGMENT as graph data (D46 (b)).  *Per-path audit:*
`virtio_disk_rw`: desc `sh` → `fence` (`0x80005c7a`) → avail `sh` → `fence` (`:5c8a`) → NOTIFY `sw zero,80(a5)`
(`:5c92`, `0x10001050`) — `x →po dv` faithful (F1) ✓, and the DEVICE sentence gives the device's reads after NOTIFY;
after NOTIFY `lw a5,4(s3)` (`b->disk`), `sleep`'s stores, no fence — `dv →po w` ✗.  `virtio_disk_intr`: `acquire` →
STATUS `lw a5,96(a5)` → ACK `sw a5,100(a4)` (`:5d52`) → `fence` (`:5d54`) → loads — `dv →po w` after ACK ✓ (F1); the
acquire's store half and frame stores before STATUS ✗ ((F4)/(c1): aq does not reach I/O).  `uartputc_sync`: LSR loads
→ THR store: ctrl ✓ (F3; same channel (F2)); prior stores and the lock's store half → LSR ✗; THR → `release` (`fence
rw,w; sw`) ✗ (no PO bit).  PLIC: pre-trap loads → claim ✓ (F5), pre-trap stores ✗; claim → handler stores ✓ (F3
ctrl), claim → `plic_complete` ✓ (data); `plicinithart`/`plicinit` boot stores → device stores ✗.  **So `dv(store)
→po w` is ISA-given at exactly ONE xv6 site (the ACK) and `st →po dv` at exactly TWO (the pre-NOTIFY fences); every
other arm instance is the residue.**
*(2)/(3) Can the gap be closed without an assumption?*  No — the executions it admits are GENUINE RVWMO + I/O
behaviours of the verified code, so no kill can refute them: **(X1)** `printf` under `pr.lock`: hart B's last THR
store →po `release` →rf hart A's `acquire` →po A's THR store, with A's THR FABRIC-BEFORE B's — consistent with
`ioOrdF` (no PO-fence after THR), unrealizable by any sequential trace (THR_B < rel_B < acq_A < THR_A vs `fab`);
**(X2)** the same shape on the virtio channel, NOTIFY_A →po `release(vdisk_lock)` →rf `acquire`_B →(fence)→ NOTIFY_B
→fab NOTIFY_A — the four virtio fences do not close it; **(X3)** a pre-trap store buffered past the handler's claim
IS closed (lock-protected, released before the trap; the AMO read is trap-ordered (F5)) — PLIC claim cycles are
killable, `plicinithart`'s boot stores are not (no reader, no fence).  Dropping `fab` from what the realization
reproduces needs each device's answers invariant under the reorderings `ioOrdF` permits — the UART's LSR depends on
the tx FIFO (`MachCSL/Dev/Uart.lean:88,132,184`), the PLIC's claim CLEARS pending (`MachCSL/Dev/Plic.lean:85-93`
[R9.2]): a per-device commutation argument over `fab` (xv6- and device-specific, XL) that also changes what the theorem
says about devices; posted-MMIO arms in TsoMem re-open the driver proofs ((9a), XL×2).  Stating (L)/(K)/W2 with the
faithful edges alone is syntactically possible (`ioOrdF ⊆ ioResidue`) but (L)'s existence FAILS at (X1)/(X2) — a
faithful (L) needs the residue as a premise anyway.  **Hence (a′) stays [OWN.12], re-encoded as (R1)–(R3) [OWN.14];
D46 (b) offers the machine-stated residue (W13 (F): `emIoFence` S–M; dependency edges through `LIo` — `rowDepsT` drops
`LDev` items, `AxDeps.lean:461-463`, `pnodeStep`'s MMIO arms discard the read set, `oib = none` — M (D50 (b));
trap-boundary edges S; `ioOrdF ⊆ ioResidue` S; header-only value).**
**(12) Audit coverage and file layout** [R1.10].  `Xv6/` never imports `Weak/` (`lakefile.toml:2,27-41`).  Composition
files live in `Weak/`, registered in `tools/ci/roots-weak.txt` + `tools/audit/baseline-weak.json` + `XV6_AUDIT_MODULES`
(`tools/ci/audit.sh:44`), built by `--weak` CI over the whole `Xv6` cone (D13); pure-`Xv6/` items (W3, W8) go to
`roots.txt`/`baseline.json` (`tools/ci/lint.sh` checks agreement).  S.

## C. Roadmap

Each stage ends in a theorem; "∥" = parallel (one Opus worker, one file each).  Stages 0–1b are INTERNAL
milestones on the critical path of the target; Stage 2 is the target [OWN.2].

**Stage 0 — RESULTS (2026-10-09): W3, W5b, W5c DONE; W1 interim DONE (W1-Q RULED (c)); W2 spike DONE → D7 STOP,
redesigned (§B(10)); spikes DONE** [R2.s4][R4.2][R5.1][R6.4a][OWN.16][W2s].  Files: `../weak-orch/parked/PROGRESS-W1.md`,
`PROGRESS-W3.md`, `../weak-orch/W5b-API.md`, `notes/W2-spike.md`.
- **W3 — DONE (option A; Q-W3a RULED (A) [OWN.16])** [R1.8][R2.1][R3.1][R5.2][OWN.9].  `Xv6/TextPristine.lean`
  (`textWin :34`, `textPristine g :38` — every byte of `[bcRoLo, bcRoHi)` has history `[⟨0, 0, img a⟩]`;
  `textPristine_read/_readBytes :60,72` — every agent at EVERY `tvn` reads the image bytes, `Wp.lean:1478,1490`;
  `textRo E :88`; `powerInterp_textPristine :123`) + the power-thread twins `MachCSL/PowerText.lean` (`wp_powerT`/
  `riscvPowerAdequacyT`/`powerBootResT`, hook `HtextRec`, persisting the window AFTER era allocation — rev 11's
  slot-stash was UNSOUND: `Hphi` receives only `powerInterp g'`, the era's cells are `Hboot`'s, run LAST, PROGRESS-W3),
  `Xv6/BootSharedText.lean`, `Xv6/SystemBootEraText.lean`, `Xv6/SystemAdequacyText.lean` (≈ 1.76k lines of twins) and
  the **sibling root `Xv6.xv6TextAdequacy_closed`** (`Xv6/LinkTextAdequacy.lean:26`; `roots.txt:19`,
  `baseline.json:63`, `tcb/expected.json` per [R6.5c]; axiom set = `xv6FsAdequacy_closed`'s, no new opaque); existing
  statements and the baseline UNTOUCHED.  Dependents (W2's `LIFetch` row, M1's `candKfetch`, M2's `gzFetch` kernel half,
  W4's `LIFetch` row, W5) are UNBLOCKED.
- **W1 `Xv6/AllocprocTrace.lean` — INTERIM DONE (274 lines); W1-Q RULED (c) [OWN.16]** [R3.s1][R6.5d-alt]; D23.
  Landed: `pidPick_range :111` (from `cycAt`'s codomain, the `nextOf` tie HYPOTHESISED), `pidPick_range_of_wf :120`,
  `pidPick_badHist :141` (`PAlloc 1..1000` then `PAlloc (2^32-2)`: pick `2^32-1`, word `-1#64`, `badWord :146`),
  **`allocprocTraceAns :254`** (the three boot hypotheses + a run → `∃ F, niOk ∧ niOneShot ∧ ∀ q, ∀ s ∈ utrace q κs F,
  isFork s → ∃ k ι, s.cite = some (k, ι) ∧ ans s = usysForkAns ι ∧ (= -1 ∨ ∈ [1, PIDMAX]) ∧ (forkOk ι → pidPick ∈
  [1, PIDMAX] ∨ (pidPick = nextOf = 2^32-1 ∧ ans = -1))`; axioms = `xv6NiAdequacy`'s) — THE interim W1 (§A (b)).  NOT
  exportable from `xv6NiPhi` (PROGRESS-W1): `forkOk ι → pidPick ∈ [1, PIDMAX]` (`pidPick_badHist`'s word satisfies
  every filing row; `PidLock.pidTie` excludes it only inside Iris) and `poolEmpty` at `KNull` (receipts `kNullRcpt`/
  `kAllocRcpt`) → **folded into W1b** [OWN.16].  Record: tie β via `niRoundLaw`'s fork row (`NiTrace.lean:646`,
  `UsysDet.lean:293-302`) at the CITED prefix (D11); ledgers export no page address (`KallocEv.lean:45-52`) or slot index.
- **W1b (owner-gated, L, serial; CARRIES W1-Q (c))**: `pidHistWf h` in `pidLedger` (live pids distinct), the `nextOf ≤
  PIDMAX` tie and `ι.kNull → poolEmpty` through `NiLedger` (`niFitEv`/`niEntryOk`, supplied at `SyscallArmsFork.
  syscArmFork_ev`/`_evNeg`); re-thread `ProofAllocproc`/`ProofFreeproc`; optionally addresses in `Kev`.  D10.
- **W2 — SPIKE DONE, D7 STOP (`notes/W2-spike.md`; `Weak/TsoOfPf.lean` MERGED)** [R1.11][R2.3][R3.4][R6.4b][W2s].
  Verdict, gaps, corrections and the redesign in §B(10).  **W2 proper (L)** = `pfStepTso`: for every memory label a
  `wpPfStep` from an `R`-related state under `pairAdjacent` + `execProgOk'S` + `candScaT` + `candDiskLat` is 0 or 1
  TsoMem steps with the same bytes to a related state (`R-view` = equality through `tsoShadow`); `pfLoadRow` under (★)
  (FlatMem ↔ `histOf`, the bulk).  **May start NOW (ruling-independent)**: **W5b′** `Weak/TsoShadow.lean` (`tsoShadow`,
  `scaOkT`/`candScaT`, `diskLatOk`/`candDiskLat`, `pfStepFacts` extension; S–M); the rows store/exstore/fence/`fence.i`/
  fetch-M1/silent/regw/ctrl/dev; `pfLoadRow` with (★) as a HYPOTHESIS, parametric in the `coh` stamp.  **BLOCKED pending
  G1-Q/G2-Q/G3-Q**: discharging (★) (G1 (e) vs (a)/(b); G2 (a) MachCSL vs (b) W8), the `DRead` row's premise form (G3
  (a″) vs (a)), hence the closed table and W4.  Report: the (↓) table WITH the faithful/stronger/weaker column [R9.s4].
- **W5b `Weak/PfRunShape.lean` — DONE** (625 lines, green; API `../weak-orch/W5b-API.md`) [R2.3(iii)][R3.2][R3.4]
  [R5.3][R6.4c].  Landed: `candKfetch :53`, `scaVis/scaByte/scaOk :61-72`, `execSca :78`, `candSca :85`, `pairAdjacent
  :95` (+ `Nil/App/Fused/Blk`), `admRunG :224`, `fetchesOk :232`, **`execProgOk'S :242`**, `pfStepFacts :265`, `pfRunS
  :273`, the replay **`execPrefixPfRunProgShaped :512`** / `execWfPfRunProgShaped :594` / `execWfPfRunPinShaped :608`
  — PROVED: `pclsEqr pcls → pstepPinned (exImg E) pstep → execWf E → execProgOk'S … → n ≤ |trace| → ∃ c st, pfRunS … st
  c ∧ pairAdjacent st ∧ states/fabric match ∧ cfgMatchd c (stt E n)`; helpers `execProgOk'SForget/SSca`, `pfRunSRtc/
  PinSub/Trans/One`, `mstepWpPfStepPairS`.  **Deviations from rev 11**: (i) ARITY 6 — `fok` explicit (the left arm is
  `lbFused l ∧ lblRealizes …`, no constructor list: W13 (E)'s payload `LDev` joins unchanged); (ii) the replay is
  PINNED/M1 ONLY (`pstepPinned` hypothesis) — W5d's M2 replay drops it; (iii) `scaOk` has NO floor normalisation
  (`tvn ≤ |log|` only; TsoMem's `Hist.read` via `scaVis`) — W2's `R` carries `tvn`.  **W5b′ [W2s]** (S–M, `Weak/
  TsoShadow.lean`): `tsoShadow`; clause (iii) strengthened to `scaOkT`/`candScaT` (`F ≤ tvn`), NEW clause (iv)
  `diskLatOk`/`candDiskLat` (agent `NCPU`'s loads latest per byte); `pfStepFacts` carries both — the replay
  `execPrefixPfRunProgShaped` threads them unchanged (facts are read at the pre-configuration).  May start now (§C W2).
- **W5c `Weak/SrvwmoXv6Witness.lean` — DONE** (730 lines, green) [R3.3]; D22.  Landed: **the DEFINITION
  `srvwmoXv6M1Premises σ0 c pst dv :583`** (§A; W5 states M1 through it), `srvwmoXv6M1PfRun :596` (every M1 premise set
  feeds W5b's replay: a `pfRunS pstepEv pclsEv (candKfetch bcRoLo bcRoHi) (wpInit …) st cf` with `pairAdjacent st`,
  matched to the candidate's last state), **`srvwmoXv6M1Satisfiable :672`** (`∃ σ0 c pst dv, srvwmoXv6M1Premises ∧
  c.cdTr = [⟨0, LLoad false 0x8000a3e8 ts8 (vs8 wl)⟩] ∧ ∀ k, dv k = efInit σ0.wgdev`), the **`esil → admRun` bridge
  `esilAdmRun :157`** (+ `esilNodePstep :101`, `fetchPstep :218`, `loadPstep :236`, `entryRun :507`: the two `_entry`
  fetches then the GOT load, 106 evaluation steps), `execProgOk'SNil/SSnoc :260,268`, a concrete `sigma0 :624` with
  `wbootFacts :636` and `diskOf ds = fsImgDisk :618`, `candConsistent :657`.  As designed: `_entry`'s FIRST memory
  instruction, `ld sp,1000(sp)` at `0x80000004` (`Xv6/KernelImage.lean:14-17`; GOT word `0x8000a3e8`, `t = 0`), hart 0
  alone, `candKfetch` ✓ (`roLo/roHi :490-491`), NOT the `sw &started` block (`WeakEvStarted.evX2`, `Weak/WeakEvStarted.
  lean:668` [R9.s2], mid-instruction, EMPTY admin run, `ConfWit.lean:11-22`).  Certifies satisfiability ONLY —
  QUIESCENT, not reaching `allocproc` (D44), nothing about W13's bundle [R5.s3]; W13-wit (D31) can start on the bridge once W13 (E) exists.
- **The three spikes — DONE** (reports `notes/W12-spike.md`, `W13-spike.md`, `W5dG-spike.md`).  W12 (D33–D36): gates
  1–2 closed, gate 3 = W12b.  W13 (D32, D37–D39): vacuity CONFIRMED, T2-1c′ LANDED (`Lin2.lean:623,836,944,995,1012`),
  [OWN.8]'s literal and the folded `gdevAdj ⊆ gmo` REFUTED.  W5d-G (D40–D43): fetch ADMINISTRATIVE, `gzFetch`, cut form.

**Stage 1 — M1, the composed sRVWMO theorem, pinned/kernel-only (internal).**
- **W4 `Weak/MachOfPf.lean`** (L) [R2.1][R2.2][R2.3][R3.1][W2s].  `machRunOfPfRun`: a shaped `pfRunS` run (with
  `candScaT`/`candDiskLat` facts) from `wpInit (imgZ bootImage) (efInit ds.reset) (epsInit σ0)`, PREFIXED by `PowerOn`,
  is a `-<κs>->ₜₚ^[n]` MachCSL run — a STUTTERING simulation (`n ≤ |st|`: 0-step matches for `LSilent`, the parked
  fence, the lost-SC retry self-loop), hart loads at the shadow's minimal view, the disk row's `DRead` as `dmaRead`,
  same hart expressions and observations, devices aligned; the `LIFetch` row UNDER `candKfetch` (M1) / the corrected
  cut form (M2).  Deps: W2 CLOSED (after G1-Q–G3-Q), W3 ✓.
- **W5 `Weak/SrvwmoXv6Adequacy.lean`** (M) [R1.5][R2.1][R3.1][R3.s2].  **M1 is STATED THROUGH `srvwmoXv6M1Premises
  σ0 c pst dv`** (never a re-listed premise set; satisfiable by `srvwmoXv6M1Satisfiable`): `srvwmoXv6M1PfRun` already
  gives the shaped `pfRunS` run (T1 + `execWfPfRunProg` + `wpPfRunPinSub` + W5b inside it); W4 projects;
  `xv6FsAdequacy_closed`, `xv6NiAdequacy`, `unionAdequacyClosed` (`Xv6/LinkUInitUnion.lean:163-164`), W3's root
  `xv6TextAdequacy_closed` ✓ and W1 (`allocprocTraceAns`, the RULED interim [OWN.16]) conclude.  M1's premise set gains
  W5b′'s clauses through `execProgOk'S` (the DEFINITION `srvwmoXv6M1Premises` is re-pointed, S).  Header: internal
  milestone, kernel-only by PREMISE (D21), loads SCA at or above the TsoMem floor by premise `candScaT`.  Registered per
  §B(12).  Deps: W1 ✓, W3 ✓, W4, W5b ✓ + W5b′, W5c ✓.

**Stage 1b — M2, the fork path on the pf side (part of the target [OWN.3]).**
- **W5d `Weak/PfRunUnpinned.lean`** (L) [R2.1-alt][R3.1][OWN.3][R4.2][R6.4b].  The pf half ONLY: `execWfPfRunProgF`
  (replay at `pstepEv` with the CUT-form clause `∃ q, itv ≤ q ≤ |log| ∧ ifetchOk img log q base tvs` replacing
  `fetchPin`; W5b's replay carries a `pstepPinned` hypothesis — the M2 replay instantiates `fok` with the cut form and
  DROPS the pin; [W2s] the cut form adds `t ≤ q` per byte and takes the SHADOW's `itv`, §B(4)(iii)), W4's `LIFetch`
  row for user text at `tvn := q`, W5 restated — the first form in which `fork → ecall →
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
  `*C`, Glue §1 re-instantiated (`rawChainC`, `crunC`, `cycleSegmentsC`) (S–M); (3) **`hullCatAD`**: the hull of a
  `rvwmoCatAD GD ad` graph is `rvwmoCatAD (gdHull GD cs) (ad.filter cut)`, via `rowsRelGppoCat6` (rule 2's `t1 ≠ t2`,
  rule 3/12's `grfAt` through an injective `hren`; risk: injectivity on the cut's sources, believed via `hrenWix`, not
  built) — the one real proof (M); (4) restated chain `cycleKillC`, `t2linAuxC`, `t2linOfCycleKillC`, `t2linSupplyC`,
  `l2ClaimAtC` (`segPinC ∨ csHyps[gcrossE] ∨ Bad`), `rawChainChainC`, `cutSupplyC`/`certSupplyC`/`walkSupplyC`/
  `walkPolicyC`, `cycleKillOfL2C`, `t2linOfL2'''C` (S–M); (5) published capstone `xv6RvwmoSafeModuloT : ∀ GT : GdexecT,
  rvwmoCatConsistentT GT → gdexecQconfT boot d0 im nh GT → (∀ x, ¬ tc (racyD (forget GT)) x x) ∧ …` by `catADOfCatT`
  into the C-chain; `gdexecQconfT → gdexecQconf (forget GT)` from `rowDepsSubT` (S–M); (6) non-vacuity: existing
  witnesses via `catADOfMinus`; **acceptance gate [R6.s2]: ONE forwarding witness (SB+rfi-pos; `AxGraphCat`'s
  `epc`/`isw` are candidates) through `rvwmoCatAD`, cat-consistent but NOT RVWMO⁻**.  `WeakRvwmoLin*`/`Norm`/`PreNorm`
  untouched.  The cat arms are written ONCE against W13 (K)'s `racyDIO` (I/O arms gmo-forward by (T)); parameterize the cross order.
- **W12b `Weak/CatFloor*.lean`** (M–L ≈ 0.5–1k; NEW [R6.2]; D34 (a)).  Gate 3: Floor §4–§6 and Cert3 §2–§3 re-done
  on a per-byte coherence invariant through rules 1/2 in place of `gvisUb`; `greadSrcUb`, `finvStep`, `cinvReplay`/
  `floorOfCgraph`/`certFloorOk`/`cpolRead` over `rvwmoCatAD`; the `wVRel` hook per D35, forwarded `LLoad aq` per D36.
  **Acceptance** [R7.s5]: ONE forwarding read whose floor the old `gvisUb` mis-states — an own store `w` forwarded to
  a po-later read `r` with `w` gmo-AFTER `r`, the exact `finvStep` coh-hook case (`Floor.lean:619`) — certified by the
  new per-byte invariant.  WITH W12, BEFORE W10 (D26).
- **W5d-G `Weak/GraphFetch*.lean`** (L ≈ 1.8–2.2k + XL risk R1; D27 RULED (a) [OWN.6]) [R4.2][R6.4b].  **Day one**
  [R7.s3]: merge `../xv6iris-weak-w3/Weak/GraphFetchSpike.lean` into this tree (builds; `propext, Quot.sound`) so the
  cites resolve — **RELEASED by R9's SATISFIED verdict [OWN.10]** (a Stage-2 item nonetheless).  Then the spike's change list: **G1** `gzContrib`,
  `emFenceI` + `emFenceISound`, `emZifencei` in `xv6ConfS`/`gdexecQconf` replacing `emFetchImg`
  (`WeakRvwmoSupply.lean:277-352`, `emFetchImgRen/Prefix` → retime/hull versions; `Fab.lean:516-522`;
  `WeakEvInst`/`WeakEvLang` lemma only) (M ≈ 350); **G2** tags = gmo indices — `wlblRen` renames `LIFetch` tags
  (reverts Q-C4, `WeakRvwmoConf.lean:57-66,147`), `pstepEvWren`/`projLblWren` `LIFetch` arms, M1 pin kept via `π 0 =
  0` (S ≈ 100); **G3** fetch fragment as data — `Gdexec.gdFetch`, `racyD` disjunct, `racyDSplit` arm (cross-hart →
  `gcross`), `gdHull` filter, `retime` keeps it, ~31 literal sites (`WeakRvwmoGraph.lean:613`, `Acyc.lean:200`,
  `Glue.lean:205-223`, `Hull.lean:714`, `Topo.lean:120-129,594-607`) (M ≈ 300); **G4** `retimeZifencei` + contributor
  invariance + `gwlog`/`gwix` bridge (Topo; L ≈ 600); **G5** `linPrefixLog`, the floor bound, `supplyOfQconf` producing
  the M2 cut clause (`Lin`, `Floor`, `Supply.lean:743-883`; M–L ≈ 500); **G6** re-thread `pstepPin` → `execProgOk'S`
  (the 19-file list in §B(10); ONE pass with W11 (iii)); **G7** kill arms for cycles through E1/E2/E3 ("fetch-entry
  segments", pinned only by `fence.i`; W8 vocabulary: user-text page ownership, exec/fork → `p->lock` → `userret`
  `fence.i`) — L, in W11/W8.  Witness files with literal fetch items (`WeakRvwmoConfWit2`, `WeakRvwmoAdm`) need only
  "the pin implies `gzFetch`".  Hull closure per §B(4)(iii) R1 (a).  Non-vacuity: user-text fetch witness → W14 (D44).
- **W13 `Weak/GraphFab*.lean`** (**XL ≈ 7–10k lines / ~70 files**, REDESIGNED rev 10, eight pieces; D38 RULED
  [OWN.14]) [R5.1][R6.3iii][R7.3].  **(E) the alphabet** (L, wide and shallow, the accepted merged-file change):
  `Lbl.LIo (kind : IoKind) (base : Int) (vs : List (BitVec 8))` (`WeakAxiomatic.lean:87-91`; `lbRd`/`lbWr` = `none`,
  `lbIsR`/`lbIsW` false, new `lbIsIo`; `gwf`'s shape arm; `candShape` `WeakAxiomatic2.lean:910-916`); `Wlabel.LDev`
  gets the same payload (`WeakPromise.lean:86`); `pnodeStep`'s MMIO arms emit it with `paZ req.pa`/the bytes
  (`WeakEvInst.lean:300-303,335-338`), `pstepPlic :461-466`, `pdiskProg :484,502`, `pdiskUart :514-520` emit kind
  `dev` (D49); `projLbl .LDev … = some (.LIo …)` (`WeakPromiseBridge.lean:529-543`, today `none` at `:537`),
  `unprojLbl :955`, `lblRealizes`/`lblRealizesUnproj` (`WeakAxRealize.lean:240-280`), `lbAdmin :130-134` DROPS
  `.LDev`, `lbNobarex :100`/`lbRfoldfree :107`/`lbFused` (`WeakPromise.lean:121`)/`latFree` (`WeakPromiseFact.lean:
  61`)/`eraseLbl` (`WeakErase.lean:102`)/`pclsEv :217`/`pdevEv :540`/`wlblRen` (`Conf.lean:142-155`)/the taggers
  `dstep :493-495`, `dstepT` (`AxDeps.lean:461-463`) get an arm; `elabOk :547` (`True`), `elabWs :571` (view
  unchanged), `wpPfStep.PFDev` (`WeakPromiseBridge.lean:392-396`, payload only); exhaustive `Lbl` matches in 41 chain
  files + 30 `Ax*` files (the `| LFence` arm census; the retired tier must still build), `Wlabel.LDev` constructor arms
  in **~35 files** (34 by arm-regex, 50 files mention the name — the `WeakRobust*` family, `AxFetch1/3`, `AxLock3*`,
  `AxRunGV2` included) [R8.4] — one-line arms, mechanical.  **(M) the model** (M–L): `gmem := lbIsMem || lbIsIo` so
  I/O events are in gmo; every "a `gmem` event is a read or a write" case split in the chain gets an I/O case
  (`lbIsMem` unfolded in 39 files, `gmem` named in 22 chain files — measured, proof impact **unverified**);
  `rvwmoCatConsistentT`'s TEXT unchanged; `gdexecQconfT`/`xv6ConfS` gain `gisIo (i,k) ↔ (i,k) ∈ gfDev`; `emDevfree`
  (`Supply.lean:273`) retires.  **(T)** `ioResidue`/`ioResidueGmo`/`gfBefore` + header text, **+ the (R2′) arm [W2s]
  under G3-Q (a″)** (S); acceptance: `ioResidueNodev` and the re-encoded `w13f` (§A(†)).  **(I) realization** (M–L): `execProgOk'` UNCHANGED — the I/O
  step is a left-arm realizing step with fabric endpoints `dvi k → dvo k` (`hemitf`'s `HFone`, `Fab.lean:241-247`,
  already has them); `gfexecConfIO` = `gfexecConf` (`:522-535`) with the `isDevBlock` clause replaced and `emFetchImg`
  → `emZifencei`; `supplyOfFconf`'s block folding `hblkQ` (`:689-701`) is DELETED, not generalized; T1 gets an inert
  arm `mstep.MStepIo`/`wpstep.WPIo` and `promiseFreeCompleteClean` (`WeakAxiomatic3.lean:1434`, 2k lines of label case
  analysis) carries it — the real (I) cost.  **(L)** T2-1c″ (M–L): `ptraceRelIO := ptraceRel ∪ gmo|IO` (`Lin2.lean:
  124`); I/O events are rule-14 ANCHORS like writes — `gnxw` (`Lin.lean:440`) → `gnxa` "next own write or I/O event",
  `glinEids :455`, `linCand :471`; **[W2s] under G3-Q (a″) DISK-ROW READS are anchors too (`gnxa` ∋ row-`NCPU` reads;
  trace ⊇ gmo between a disk read and every write; the pf `candDiskLat` then follows from `gloadValue`; +M)**;
  `gtraceLinearizationMin :623` restated, I/O steps no-ops for the cand;
  `fconfSupply'`'s `before L` premise (`:1000`) and FabInd's handed-back `trDevOrdered` (`:407`) are DISCHARGED from
  `ptraceExtIO` (fab order = the trace's I/O order = gmo|IO by (R3)).  **(K)** the kill (M–L): `racyDIO := racyD ∪
  ioResidue ∪ gmo|IO`; the cross kind `gmo|IO` and the same-row arms (R1)–(R3) are gmo-forward by (T) directly, so
  KillArms' chain composes in `gmoLt` AS TODAY (no `tc ioOrd`); segments ENTERING at an I/O event and exiting at a
  WRITE are free by (R2); `csChained` (`KillArms.lean:499`) generalized to "entry = any `gmem` event of the critical
  section" (S–M); `normalizeOfAcyclic` over `racyDIO` keeps I/O positions (its topo order ⊇ gmo|IO) **and, under G3-Q
  (a″), the disk-read anchors (one more `racyDIO` disjunct, S–M) [W2s]**; `gdHull` keeps
  I/O events and filters `gfDev` → `cycleKillIO`, through `hullRun`, W11, W12.  **(R)** the re-thread of the
  constant-fabric chain onto `gfexecConfIO`: measured 8.6k lines / 14 files / ≈ 140 bundle mentions / 52 `fun _ => d0`
  sites (Supply, LinInd, Cert4, Glue, Glue2, Walk*, Progress, PreNorm*, Capstone); segments without I/O events have
  `dvi = dvo` and reuse the constant-fabric lemmas verbatim; witness files embed via `gfexecConfOfQconf`; KillArms,
  Hull, Lin unchanged except the new arms (L–XL, the bulk).  **(W)** `xv6ConfS` on `gfexecConfIO` + **W13-wit** (M–L):
  hart 0's run `_entry → … → uartinitone` (entry `0x80000896`, `Xv6/KernelImage.lean:1515`; the `jal` at `:1590`) to
  **its first UART store, `sb zero,1(a5)` at `0x800008a0` (`:1525`, IER := 0)** [R6.5b] — the EVENT `LIo .wr
  0x10000001 [0]` in row 0, the first candidate with a non-empty `gfDev` (D31); ≈ 100 dynamic instructions, NO MMIO
  before it (`timerinit` is Sstc CSR-only, `Xv6/SpecTimerinit.lean:5-7`), by kernel evaluation on W5c's `esilAdmRun`;
  **gate 2 [R7.3c]: a device-ACTIVE DISK witness** "first disk START → DRead/DWrite → COMMIT" on the disk row (the first
  disk request is `fsinit`'s `bread(dev, 1)`, `Xv6/SpecFsinit.lean:7`, on the first `forkret`, past `kinit`'s
  `freerange` — shares D44's infeasibility, so W14 covers it).  **(F)** OPTIONAL, D46 (b)/D50 (b) (M–L; no proof
  consumes it).  Risks: **R2′** the alphabet sweep touches ~70 files including the retired `Ax*` tier (mechanical, one
  build); **R5** an I/O-ENTRY / READ-EXIT segment (I/O event →po→ racy read →fr→) has NO fence pin (rule 4 skips I/O)
  and must close by lock discipline or (R2)-rerouting through the release — an unlocked one is a STOP (candidates: the
  PLIC claim/complete races, `plicinithart`, `pr.locking`/`panicked`; R8: real, honestly a STOP); **R6** the `gmem`
  case splits of (M).  Deps: W5c's `esilAdmRun` ✓; W5b's shape clauses ✓; `AxDevGraph.lean` (`Dlbl :134-142`, `dstep
  :152`, `DevConsistent :226-236`) as the device-step precedent for the `dev`-kind replay (its separate-row encoding is NOT what [OWN.14] rules).
- **W14 `Weak/ExistWitness.lean`** (NEW; D44 RULED (i) [OWN.11]; L–XL — the spike's table confirms the SC run
  satisfies `candScaT`/`candDiskLat` trivially, every load at the top [W2s]): the single-execution EXISTENCE theorem — ONE device-active TsoMem-side run (a `-<κs>->ₜₚ^[n]` run from
  `PowerOn` reaching `allocproc`, from the SC tree's reachability, not evaluation) lifted to a conformant cat candidate:
  a `GT` with `rvwmoCatConsistentT`, `ioResidueGmo`, `xv6ConfS` and a non-empty `gfDev` whose realization is that run —
  (↑) of W2 for a SINGLE run (not receptiveness, D15).  CHOOSE the SC run (every load at `tvn := top`, stores at the
  top, I/O events at their trace positions) so the graph is the trace's own (`gmo` = trace order of writes and I/O
  events, `fab` = its I/O restriction; (R1)–(R3) by construction) and SC ⊆ RVWMO makes it cat-consistent TRIVIALLY
  [R8.s3]; the fetch clause by `fetchPinCutOk`/`gzFetch` at tag 0 (kernel text) and the TsoMem `itv` (user text).
  Certifies non-vacuity AT `allocproc` ([OWN.3]); until it lands the header carries D44's caveat.  Deps: W2's `R` and
  table; W5b ✓; W13 (E)/(I)/(W); W5d-G.  Risk: "reaches `allocproc`" is LIVENESS-flavoured reachability of the SC tree,
  which exports safety only — a dedicated SC-tree lemma ("some run reaches `userinit`'s `allocproc` call") may be needed, M–L, **unverified**.
- **W8 `Xv6/AccessDiscipline.lean`** (L–XL; D24) [R4.3][R4.s3][R4.s4].  Export from the SC tree, per reachable
  MachCSL state (the `mmOk` idiom) on `MState`'s author log + per-byte histories (`MachCSL/Lang.lean:147-153`), in
  the vocabulary `protReg`/`badSeg` consume: (i) bytes a hart OWNS — no foreign writer (covers `PStack`/`PPerCpu`,
  the 58 `own = true` witnesses; `gen_weak_pins.py --check` as the audit); (ii) a protected access under a held lock
  (`wprotAt`/`wlpAt`/`wlpAlt`, `Weak/WeakGhost.lean:1040,543,699`; `lockWordByte`, `KillArms.lean:340`); (iii) no
  hart's floor reaches a FOREIGN owned-unpublished message (`wmAk = .WCplain`, `WeakRobustMain.lean:390-395`; `¬
  wpublished :399-400`; `Weak/WeakViolation.lean:9-15`) — HART authors only, DMA exempt, mirroring `violationHart`
  (`WeakRobust.lean:100-107`); (iv) ALL 182 `PCall`/`PResidue` sites and the 58 sp-frame witnesses classified into
  (i)–(iii) (W9b; D28 RULED (a) [OWN.7]); (v) user-text page ownership for W5d-G's G7.  A ledger threaded through the
  MachCSL memory rules — mechanical but wide; ownership residue ~5 idioms (`swtch` reloads, trapframe loads off `a0`,
  user-table walks, boot-published globals).  Exports hold on FORWARDING graphs.  **Design gate OPEN [W2s]** [R4.s5]
  [R6.4a]: the per-load export shape is (★) at the LOG level (§B(10)); under G1-Q (e) + G2-Q (a) NOTHING per load is
  needed from W8 — (i)–(v) only; under G2-Q (b) W8 gains (vi) the MIXED-SIZE census: every pair of po-ordered
  OVERLAPPING loads of DIFFERENT footprints on a byte some foreign hart writes concurrently (expected VACUOUS — fields
  are read at one compiler-typed width — **unverified**; a racy site is a STOP → (a)).  Deps: G1-Q, G2-Q.
- **W9a `Weak/WeakRvwmoPinBridge3.lean`** (L = M–L + M [R6.1]) [R4.1].  R-3: a `pstepEv` run's items are grouped per
  instruction as the checker's pc walk assumes (`reaches`/`psites`, `PinBridge2.lean`; §8 has both halves on one
  computed stretch) → `pinSegPin'` applies at every certifying site of the REAL run, targeting `segPinC`
  (`pinStepOfSegPinArm`; PDep entries across an rfi via `segPinCForward`); with W8 (W9b) → `l2ClaimAtC`'s `segPinC ∨
  csHyps` arms for xv6.  No generator work (§B(9)).
- **W10** (M–L, **unverified**; L if it absorbs W12b): `wsegSupply`/`walkPolicy` for xv6 graphs on the W12b floor kit.
- **W11 `Weak/RvwmoXv6Adequacy.lean`** (L) [R4.3][R4.4].  (i) **The `Bad` arm is LOG-LEVEL**: `l2ClaimAt GD P Bad`
  (`Glue.lean:440-447`) hands the prover `(GD, log, logOf, protReg)` while the capstone sets `Bad := badRun gen σ0 = ∃
  ρ, rtc epfRun … ∧ violationHart …` (`:384-385`), a RUN-LEVEL existential refuted by `noBadRun` (`:387-391`) over ALL
  `epfRun`-reachable configurations — unreachable on route (M); `rawChainChain` consumes `¬ Bad` globally (`:453-460`).
  Define `badSeg GD log prev s` := the entry's source message is owned (`wmAk = .WCplain`) and unpublished at `log` by
  a FOREIGN hart; restate `l2ClaimAt` with it; prove `¬ badSeg` at the certified run from W8 (iii) through W4 (the
  realized hull run is a prefix of the realizing TsoMem run); derive the global `¬ Bad`.  (ii) `protReg P log`
  (`:364-368`) is a fold over the LOG — transfers through `R`'s log identification once W8 exports (ii) (D24).  (iii)
  re-thread `execProgOk'S` through `RunData`, `cstOk`, `segStep`, `topoSupply`, `t2linSupply` — one pass with W5d-G G6.
  (iv) `linCandSca` (S) [R4.4] **+ `linCandScaT`/`linCandDiskLat` (M) [W2s]**: the §B(10) derivations — the SCA witness
  is the load's gmo position, ≥ the pair's position by rule 5/4 and the gmo|W log order (`ptraceRel`), ≥ per-byte `coh`
  by rule 2; disk-row loads latest from the (L) anchors.  (v) Restate `cycleKillOfL2''` (`Glue2.lean:521`), `t2linOfL2'''` (`Walk3.lean:77`),
  `xv6RvwmoSafeModuloT` (W12) with W8-sourced facts replacing `wpPackage`/`wpPackageProt`/`noBadRun`/`protRegOfRun`/
  `efetchItvOk`; compose with M2, W5d-G, W13 (`gfexecConfIO`, `ioResidueGmo`, T2-1c″, `cycleKillIO`): **T-alloc-RVWMO**.  Header per §B(11).
- *Not on the path:* **W6** PSO machine (L–XL; optional de-risk, D4); **W7-P** promise-machine fallback (D2').

**Stage 3 — AxSL tier: retired** [OWN.1].  One-paragraph note on Theorem 2 (D6).

**Status of the launch [W2s][OWN.16]:** W3, W5b, W5c DONE; W1 interim DONE (W1-Q RULED (c) → W1b); W2 spike DONE
with D7 STOP.  **Now launchable**: W5b′ (`Weak/TsoShadow.lean`) ∥ W2's ruling-independent rows (§C W2) ∥ W1b (owner
schedule, D10).  **Blocked on G1-Q/G2-Q/G3-Q**: closing W2's table, W4, W5, W5d; W8's design (its per-load export is
(★) ONLY under G2-Q (b)); the MachCSL change of G2-Q (a) (serial, owner-gated, S–M).  The published statement's shape
is FIXED (D32, D33, D37, D38, D44, D45 RULED [OWN.11–14][OWN.16]).  W13 (E)/(T) cannot start before D47–D52 are ruled
((T) also needs G3-Q); W5d-G before D42–D43 (D41 RULED); W13 (F) only if D46 (b).

## D. Owner questions (recommended first; RULED items kept, tightened — [R7.s1]'s appendix NOT adopted: this file only)
**FIXED: D32, D33, D37, D38, D44, D45 RULED.  OPEN: G1-Q, G2-Q, G3-Q (NEW [W2s], first), D42–D43 (W5d-G), D46–D52
(W13).  RULED by [OWN.16]: W1-Q (c), Q-W3a (A), D41 (a), D45 (a).**
**OWNER RULE (2026-10-09) [R8.1][R9.1][R9.s3]: every OPEN or STANDING semantics question below (G1-Q–G3-Q, D19, D20
included) opens with "Spec:" — what the RVWMO chapter,
the appendix "I/O Ordering" (quoted in §B(11b): (c1)–(c5), the FENCE and DEVICE sentences), the Sail model in this
tree (file:line), Zifencei and the PMAs say, or that they are silent — and marks each option FAITHFUL (the spec's
executions), STRONGER (excludes spec-allowed executions; must be a NAMED trusted item) or WEAKER (admits more; sound),
costs after.  Shared Sail/PMA facts: `execute_FENCE` keys on the low two bits of each set after
`effective_fence_set` (`InstsEnd.lean:18299-18313`, `BaseInsts.lean:568-573`; FIOM folds i/o INTO memory bits, FIOM
= 0 at `BootBoard.lean:30`); `fence.i` = `Barrier_RISCV_i` (`:18295-18297`); MMIO is an ordinary `mem_read`/
`mem_write` routed by `devAddr` (`MachCSL/Dev/Fabric.lean:126` [R9.2]); Sail's `PMA` has NO ordering/channel attribute
(`LeanRV64D/Defs.lean:549-566`); the platform table types `[0x2000000, 0x12000000)` `IOMemory`, non-idempotent
(`MachCSL/Platform.lean:220-239`; RAM `MainMemory :240-254`), consulted only through `matching_pma_ram`
(`PlatformFacts.lean:24`); Sail has NO device/DMA model (`MachCSL/Dev/*.lean`); PMA strong ordering is within ONE channel only.**
- **G1-Q (NEW [W2s]). The `.aq` floor debt (G1/G1′).**  Spec: RVWMO rule 5 / riscv.cat `[AQ];po` (`gacqPo`,
  `WeakRvwmoGraph.lean:214-215`): the acquire READ (the AMO's read half, `lbAq`) is ppo-before every po-later memory
  access of its hart; rule 4 covers the pair's read half for a later `fence r,*`; load-value: a later load's source is
  co-maximal among the writes gmo-before it — so the writes gmo-before the AMO ARE visible to the hart's later loads,
  and "floor = the AMO's gmo position" is what the chapter gives; NOTHING in the chapter ties a floor to the lock
  word's SOURCE timestamp (WeakMem's `max(wVrNew, t)`, `WeakMem.lean:608,834`) — the two coincide exactly when the
  log is gmo-ordered.  Sail: `execute_AMO` (`InstsEnd.lean:18663`) issues `mem_write_ea … aq`/`mem_read … aq`, the
  access kind carries the bit (`AS_rel_or_acq`, `PhysMemInterface.lean:315,364`), NO view semantics (the memory model
  is external).  Zifencei/PMAs: silent.  Options: (e) **`candScaT` — SCA at a view ≥ `tsoShadow`'s floor** (§B(10)) —
  FAITHFUL at Stage 2 (derived: `linCandScaT`, rule 5/4 + `ptraceRel ⊇ gmo|W`), a PREMISE at M1/M2 only (restricts the
  candidate's log order to a gmo-extension); cost W5b′ S–M + W11 (iv) M; re-opens nothing (recommended); (a) D7 (Rec):
  WeakMem's aq exclusive read takes TsoMem's view (`wVrNew := |log|`) — STRONGER pf machine; T1 `srvwmoRealizable`
  fails on G1-shaped candidates, so (9d)'s hull realization has a hole — rejected; (b) MachCSL: `afterExcl`/`store`
  floor := the read bytes' source timestamp (`Lang.lean:136,151`) — FAITHFUL direction (TsoMem weaker, = WeakMem);
  re-opens the `.aq` view receipt `viewLbAt E cpu (top+1)` (`WpAtomic.lean:166-167,225-226`; `acq_view`,
  `WpLock.lean:63`) consumed in 13 files (`Ctx.lean` 20 sites, `Lock`, `WpLock`, `Xv6/BootCarveHart`/`StartedInv`/
  `ForkretRecord`) — M–L, serial, owner-gated; unnecessary given (e); (c) (★) per load from W8's discipline — FAITHFUL
  but INSUFFICIENT: a racy byte written in `(t, top]` (`panicked`, `started`) is a genuine RVWMO stale read TsoMem lacks.
- **G2-Q (NEW [W2s]). Footprint coherence stamps (G2).**  Spec: RVWMO rules 1–3 / riscv.cat rule 2 (`gppo2`,
  `AxGraphCat.lean:151-156`): same-BYTE reads of DIFFERENT sources with no same-hart write between — per byte, nothing
  across a footprint; "Memory Model Primitives": a misaligned access is a set of byte operations (N10 out of scope);
  Sail: `mem_read` per access, no coherence state (external); Zifencei/PMAs: silent.  TsoMem stamps the WHOLE
  footprint with `tvn` (`HRead.afterLoad`, `TsoMem.lean:268`) — STRONGER than rule 2 (§0 F1 (iii); `g2Tso`).  Options:
  (a) **MachCSL: `afterLoad` stamps each byte with ITS source timestamp** (`afterLoadSrc`, computed from `σ.mem` at
  `tvn`; CoRR kept — a later read at `tvn' ≥ coh a` cannot go below its earlier source) — FAITHFUL (= rule 2).  Cost
  [correcting the spike's "re-opens `cohOk` users": `cohOk` has ONE use, `Lang.lean:365`]: `TsoMem.lean`,
  `Lang.lean:365-367`, `mmOk_afterLoad` (`Resources.lean:788`), the load rules `Wp.lean:1257-1282,1729-1745`,
  `WpAtomic.lean:516-520`, `WpSmodeFenceFloor.lean:92-119,239-260`, `UIcache.lean:233-249` — 7 MachCSL files,
  mechanical (the `swp` statements the Xv6 cone consumes never mention `coh`) — S–M, SERIAL on MachCSL, owner-gated
  (recommended: (★)'s `coh` part then vanishes); (b) W8 export (vi): no po-ordered OVERLAPPING loads of DIFFERENT
  footprints on a concurrently written byte — FAITHFUL (a program fact; TsoMem stays stronger, named in F1); census
  M, **unverified** (expected vacuous), a racy site is a STOP; (c) strengthen `candSca` — NOT derivable (cat allows
  G2), rejected; (d) a footprint-coherence ppo rule in the published model — STRONGER than riscv.cat, violates [OWN.2], rejected.
- **G3-Q (NEW [W2s]). DMA reads at the top vs the disk row's floor reads (G3).**  Spec: RVWMO — I/O and devices "not
  (yet) formalized"; the appendix's DEVICE sentence (§B(11b)): after the MMIO the device's memory accesses "must
  observe the effects of all accesses ordered prior to that MMIO operation" — the MP direction only, NOT "reads at
  the top"; riscv.cat: no device events; Sail: no device/DMA model; PMAs: silent.  The device MODEL of record reads at
  the TOP (`mem_view`, `DevLang.lean:20-21`; `dmaView`, `Lang.lean:185,535`) — STRONGER than the sentence, already
  named (F6); the pf disk row (`DRead` = `LLoad aq false`, `WeakEvInst.lean:489`; `dreadAvailIdx` aq,
  `VirtioProg.lean:376`) is FAITHFUL to the sentence, WEAKER than the model.  Every closing option is STRONGER than
  the ISA; what each adds: (a″) **shape clause `candDiskLat`** (W5b′: disk-row loads `latest` per byte — `readOkD`'s
  `lat` condition, `WeakPromise.lean:183-188`) + graph twin **(R2′)** in `ioResidue` (§A(†)) + disk-row reads as (L)
  ANCHORS — EQUAL to the device model (a graph restatement of F6, realization-necessary; the only new trusted text is
  (R2′)'s one arm); cost W5b′ S + W13 (T) S + (L)/(K) M + W11 (iv) S–M; `latFree` untouched (recommended); (a) the
  spike's form: `DRead` with `lat = true` + the same twin — same executions, but FALSIFIES `pstepEvLatFreeProg`
  (`WeakEvCapstone.lean:1052`) and `lblRealizes`'s `latFree` (`AxRealize.lean:241`): 16 files (`WeakPromiseFact` 26
  sites, `WeakErase`, `WeakRvwmoConf`, the `WeakRobust*` family) — +M–L for nothing; (b) MachCSL: `dmaView` at a disk
  view with the acquire on the avail index — FAITHFUL to the DEVICE sentence, a WEAKER device model; re-opens `WpDma*`/
  `WpDevDma*` and `ProofVirtio*` (XL); (c) W8 device-ownership export making (★) hold at `F = top` — FAITHFUL on the pf
  side, INSUFFICIENT at Stage 2 (the stale-read GRAPH stays in the quantifier with no realization).  D51's one-row
  artifact extends to (R2′) (UART/PLIC moves po-before DMA reads).
- **W1-Q — RULED (c) [OWN.16]** (not a memory-model question): the counter tie `nextOf ≤ PIDMAX` and the `poolEmpty`
  export fold into W1b (`pidHistWf`; `niFitEv`/`niEntryOk`), `allocprocTraceAns` is the interim W1 (§A (b)).  Recorded:
  (a) NI-ledger-only export (M); (b) the interim forever — WEAKER at `pidPick` by the one fallback `pidPick = nextOf = 2^32-1 ∧ answer = -1`.
- **Q-W3a — RULED (A) [OWN.16]** (CSL plumbing, all options FAITHFUL): the power-thread persist twins (§C W3) — DONE;
  (B) the smaller-mask boot export (`Hboot'` returns `□ textRo E`) and (C) the XL re-size recorded.
- **D32 = Q-X / Q-W13a — RULED (a′) [OWN.12], re-encoded by D38 [OWN.14] as (R1)–(R3) of `ioResidueGmo`.**  Record:
  (a′) **the `dv → ev` arm restricted to WRITES — RULED**; (f) FAITHFUL `ioOrdF` alone — INFEASIBLE (§B(11b)); (a) the
  spike's two-way form (`W13Spike.lean:83-95`); (b) [OWN.8]'s literal acyclicity — refuted by `lbExcluded` (`:35`);
  (c) the same on the normalized graph; (d) `gdevAdj ⊆ gmo` on FOLDED blocks — excluded SC; on I/O EVENTS it is (R3).
- **D33 = Q-T / W12-Q1 — RULED (a) [OWN.13]**: tagged `rvwmoCatConsistentT`, chain on `forget GT`; (b) untagged with
  rule 12 over ctrl/translation deps NAMED a strengthening; (c) drop rule 12 — sound, the kill loses `segPinCForward`.
- **D34 = Q-U / W12-Q3 — RULED (a) [OWN.13]**: W12b `Weak/CatFloor*.lean` with W12; (b) W10 absorbs it; (c) kernel rows only.
- **D35 = Q-V / W12-Q2 — RULED (a) [OWN.13]**: `grcsc` riscv.cat-faithful (RCsc = any aq/rl on AMO/LR/SC; first check
  the decoder emits `LStore rl`/`LLoad aq` only for atomics); (b) weak rule 7 + side condition; (c) `Bad`-arm burden.
- **D36 = Q-W / W12-Q4 — RULED (a) [OWN.13]**: row side condition "no plain `LLoad aq`" (true for the kernel); (b)
  change `fwdView` for aq (ripples into T1); (c) a named user-code gap.
- **D37 = Q-Y / Q-W13b — RULED (a) [OWN.12]**: "I/O accesses act as one-way fences for the issuing row and serialize
  as the fabric does — beyond FENCE i/o bits, dependencies, precise traps and the device models", QEMU TCG
  (program-order vCPUs + the BQL around MMIO) the platform, host-dependent; (b) fence-guarded MMIO — leaves
  `verified`, still needs D46 (b); (c) DROPPED: "PMA strong ordering" does not deliver (T).
- **D38 = Q-Z / Q-W13c — RULED [OWN.14] (b′)**: MMIO as an I/O-class LOAD/STORE EVENT of the row (`Lbl.LIo`, in gmo,
  ppo applies, device-supplied value); `projLbl` and the emission proofs change (accepted); realization keeps
  `execProgOk'` (§A(†), §C W13); (a) `execProgOkA` — RETIRED; (b) a tagged INERT-FENCE row event; (c) folded model + per-site representability — XL.
- **D39 = Q-W13d — RULED (a) [OWN.13]**: `xv6RvwmoSafeModuloF`/`gfexecConsistent'` retired as published forms, kept internal on normalized graphs.
- **D40 = Q-G1 — RULED (a) [OWN.15]**: emission-structural `emFenceI` + soundness lemma (M), the no-op `LFence false
  false false false` label stays; (b) distinct fence bits — perturbs Q7 and the AxSL pins; (c) a new `Wlabel` — XL.
- **D44 ([R7.4]) — RULED (i) [OWN.11] → W14.**  `kinit`'s `freerange` (`end = 0x80023b10`, `KernelImage.lean:17935`;
  `physTop = 0x88000000`, `KallocDefs.lean:71`; 32,732 page `memset`s) is 10^7–10^8 dynamic instructions — evaluation
  INFEASIBLE.  (i) **a single-execution EXISTENCE theorem** ((↑) for ONE run, not receptiveness; sized by W2's table);
  (ii) publish with "non-vacuity certified to the first UART store and first disk COMMIT only" (interim header
  wording); (iii) a reduced-RAM witness image (not the published kernel, [OWN.4]).
- **D45 ([R7.3]) — RULED (a) [OWN.16]**: one `LIo` label, `IoKind = rd | wr | dev` (hart MMIO `rd`/`wr`; pin
  deliveries, START/COMMIT, device-thread moves `dev`), one set of arms (R1)–(R3) (+ (R2′) under G3-Q (a″)).  Spec:
  SILENT — no device-internal events in the ISA (`pdiskProg :481-507`, `pdiskUart :514-520` are model-only); every
  option STRONGER than silence; (b) a separate device-side constructor — the same, +S–M.
- **D46 (NEW [OWN.12]). Machine-stating the I/O residue.**  Spec: the appendix gives (F1)–(F5) (§B(11b)); Sail's
  decoder gives NONE of (F1) (the i/o bits die, FIOM = 0); (R1)–(R3) are beyond both (the residue).  (a) **(R1)–(R3)
  alone; the header lists the ISA-given edges and per-arm trusted uses in prose (§B(11))** — STRONGER than the spec by
  exactly the named residue; recommended: no proof consumes the fragment; (b) W13 (F): the fence fragment `emIoFence`
  recovered from the instruction word (graph data, `gdFetch`'s style), dependency edges through `LIo` (= D50 (b)),
  trap-boundary edges, named readings (F3)/(F5); `ioOrdF ⊆ ioResidue` — the PROSE-FAITHFUL encoding of (F1)–(F5), the
  one option under which the four `fence iorw,iorw` order I/O at the graph tier; same quantifier as (a) once the
  residue holds (M–L, header-only value); (c) fabric-free realization (per-device commutation) — the only option that
  could DROP the residue (FAITHFUL), XL, fails for the PLIC's claim, NOT recommended.
- **D47 (NEW [OWN.14]). How an I/O event is encoded.**  Spec: appendix — an I/O access is a load/store operation
  with a gmo position, outside load-value/atomicity; (c2) gives po-loc among overlapping I/O accesses; Sail — an
  ordinary `mem_read`/`mem_write` to an `IOMemory` address (`MachCSL/Dev/Fabric.lean:126`).  (a) **a NEW constructor
  `Lbl.LIo kind base vs` (+ payload on `Wlabel.LDev`)**: `lbRd`/`lbWr`/`lbIsR`/`lbIsW` stay RAM-only, so rf/co/fr/
  load-value/atomicity/`gmsg` and rules 1–4, 7 skip I/O BY CONSTRUCTION — FAITHFUL on load-value/atomicity, WEAKER
  on rules 1–3 for I/O ((c2)'s po-loc is not a graph edge; covered by the STRONGER (R3), so the same executions once
  (R3) holds); cost one-line arms in ~70 files (recommended); (b) the owner's literal wording — ordinary `LLoad`/
  `LStore` at an address with `ioAddr a := a < devBound` — FAITHFUL on rules 1–3 ((c2)), same executions once (R3)
  holds, but needs `¬ ioAddr` GUARDS in `gloadValue`, `greadsByte`/`gwritesByte` (else bogus `fr`/image reads at
  t = 0), `gmsg`, `candValues`, `rdOk`/`readOk`, the fence rule — a side-condition thread through the 33k-line chain,
  NOT recommended; (c) `AxDevGraph`'s separate device rows — WEAKER (no gmo position), not what [OWN.14] rules.
- **D48 (NEW). Rule 4 and I/O events.**  Spec: the FENCE text and the appendix's FENCE sentence — a fence WITH i/o
  bits orders I/O against RAM both ways, a fence WITHOUT them does not; Sail drops the bits (`InstsEnd.lean:
  18299-18313`, FIOM = 0), so `LFence pr pw sr sw` carries no I/O information; xv6's four `fence iorw,iorw` are
  `0x0ff0000f` (`KernelImage.lean:17301,17311,17441,17451`), read by the Xv6 proofs as `Barrier_RISCV_rw_rw`
  (`ProofVirtioDiskIntr.lean:92-99`).  (a) **`LFence` orders RAM accesses only; I/O events get NO fence edge; the
  residue covers the realization** — WEAKER than the prose (the four `iorw` fences give I/O nothing at the graph tier),
  Sail-FAITHFUL; recommended: the sound direction, consistent with (F1)/(F4) [R8.1]; (b) riscv.cat-literal: I/O events
  ordinary for rule 4 — STRONGER than the prose at every fence WITHOUT i/o bits (the locks' `fence r,rw`/`fence rw,w`
  would order MMIO), faithful only at the four `iorw` words; fewer trusted uses on the virtio path, still the residue on
  UART/PLIC; needs a `lbIsIo` disjunct in rule 4 (`gfenceCovers` keys on `lbIsR`/`lbIsW` under D47 (a)) [R8.s4].  The PROSE-FAITHFUL form is D46 (b).
- **D49 (NEW). The device-side fabric moves** (`pstepPlic`, `pdiskProg` START/COMMIT, `pdiskUart`).  Spec: SILENT on
  device-internal events; the DEVICE sentence orders a device's memory accesses only AFTER the MMIO it received; the
  UART and the virtio DMA engine are unrelated agents; a PLIC pin delivery is a trap — (F5) orders pre-trap LOADS
  only.  Every option is beyond the spec; what each adds: (a) **`LIo .dev` events in the issuing row (hart row for the
  pin delivery, row `NCPU` for the rest), under (R1)–(R3)** — adds the (R1)/(R2) coupling of pre-trap STORES to the
  pin delivery and of the disk's DMA accesses to UART/PLIC moves (D51): STRONGER than the spec, a one-row-model
  artifact; one mechanism, the block-folding defect cannot recur (recommended for this plan); (a′) [R8.2c] `dev`-kind
  events from `pdiskUart`/`pstepPlic` carry (R3) ONLY — fabric order alone (STRONGER than silence by (R3) only, the
  closest option), but NOT realizable in the one-row model (the trace must respect the row's po): costs the `WeakEv`
  row split of D51 (b), M–L, owner-gated; (b) admin-only via rev 9's `execProgOkA` for `dev` kinds — what (a) adds,
  through two mechanisms, +L; (c) leave them folded — STRONGER still: `scDevUnrealizable` recurs for pin deliveries, NOT acceptable.
- **D50 (NEW). Dependencies through `LIo`.**  Spec: appendix (c1) — ppo 9–13 apply to I/O accesses (addr/data/ctrl
  into an I/O STORE, addr into an I/O LOAD); a ctrl→I/O-LOAD edge is NOT ppo under either reading (the PMA
  non-idempotency "no speculative access" text is a reading to be NAMED); this tree — the taggers `dstep`/`dstepT` are
  inert on `LDev` (`AxDeps.lean:461-463`), `pnodeStep`'s MMIO arms discard the read set (`oib = none`, `WeakEvInst.
  lean:300-304,335-338`).  (a) **taggers keep `LDev` inert: no addr/data/ctrl edge into an I/O event, no provenance out
  of an I/O load** — WEAKER (sound; (R1) subsumes the in-edges, same-row I/O→I/O order is (R3)); recommended; (b) extend
  the taggers (the `oib = none` discard must go) — FAITHFUL to (c1) for addr/data/ctrl→I/O-store and addr→I/O-load, M;
  a ctrl→I/O-LOAD edge would be STRONGER and needs the non-idempotency reading NAMED.
- **D51 (NEW [R8.2]). The one-row device model.**  Spec: RVWMO/riscv.cat/Sail are SILENT on device threads; the
  DEVICE sentence orders a device's memory accesses only after the MMIO it receives; the UART and the virtio DMA are
  unrelated agents.  (a) **keep ONE device row (`pstepDisk`, `WeakEvInst.lean:522-526`) and NAME the (R1)/(R2)
  coupling of DMA accesses with UART/PLIC moves as a model artifact** — STRONGER than the spec (excludes a DMA write
  delayed past an unrelated UART byte); zero cost (recommended for this plan); (b) split `pdiskUart` into its own
  row(s) so (R1)/(R2) bind only START/DMA/COMMIT — FAITHFUL to the spec's silence; `xN` (`Capstone.lean:94`), a new
  `pstepEv` row kind and `epsInit` entry change; M–L, owner-gated, after W13 (E).
- **D52 (NEW [R8.1]). Rule 5 over I/O.**  Spec: appendix (c1) — acquire/release annotations do NOT order memory↔I/O
  (quoted in §B(11b)); the graph's `gacqPo` (`Graph.lean:214-215`) orders an acquire READ before every later `gmem`
  event, which under W13 (M) includes I/O.  (a) **keep `gacqPo`'s `gmem e2`** — STRONGER than the text, but subsumed by
  (R1) (an acquire read is a RAM access po-before the I/O event): no coverage change, no new trusted use; zero cost
  (recommended); (b) add `¬ gisIo e2` to `gacqPo` — FAITHFUL; touches the cat arms and `cyBackwardNotAq` (`Cert4.lean:587-590`), S–M.
- **D41 = Q-G2 — RULED (a) [OWN.16]**: the superset contributor set "everything the hart wrote or read before
  `fence.i`" — retime-invariant, stronger than TsoMem's `itvPost` set (`WeakInterp.lean:378-384`), ≤ the Zifencei text
  ("a subsequent instruction fetch … will see any previous data stores already visible to the same RISC-V hart";
  RVWMO has NO fetch model; Sail's `fence.i` is the bare `Barrier_RISCV_i`, `InstsEnd.lean:18295-18297`) — SOUND [R8.1];
  (b) the exact `itvPost` set (aq reads, `pr∧sr`-fenced reads, address views, own stores) — equal to TsoMem's, +M.
- **D42 = Q-G3. Where the fetch fragment `F` lives.**  Spec: an ENCODING question, the ISA is silent — every option
  FAITHFUL.  (a) **a `Gdexec.gdFetch` field, mirroring `gdDeps`, so hull, retime and acyclicity carry it for free
  (recommended)**; (b) a parameter of `racyD`/`cycleKill` — the ~31 constructor sites untouched, 16 files' statements change.
- **D43 = Q-G4. Pinned milestones.**  Spec: engineering only, no semantics — every option FAITHFUL.  (a) **keep
  `pstepPin`/`fetchPin` as the M1 kernel-text instance (`fetchPinCutOk`) until M2 lands (recommended)**; (b) delete after G6.
**Standing (recommendations provisional unless RULED).**
- **D1 / D2 / D12** — RULED [OWN.1][OWN.2][OWN.4]: machine tier (Theorem 2 = validation); FULL RVWMO (the TAGGED cat
  model, D33), sRVWMO/pinned forms internal; the `verified` fork in the header.  **D2′.** If (9d) is too large: (Rec)
  hold publication; (b) the promising machine with "Promising-RISC-V ≡ RVWMO" trusted — not cat, violates [OWN.2].
- **D3.** (Rec) trace-level predicate via `xv6NiPhi` beside the Iris contract; (b) contract only.  **D4. W6** — (Rec)
  SKIP; (b) de-risk W8's export.  **D5.** (Rec) W3 first.  **D6.** (Rec) Theorem 2 = audited validation; note S.
  **D7. W2 failure mode — RESOLVED-BY-REDESIGN [W2s]** [R2.3][R3.s5][R9.1]: the STOP fired (G1–G3, §B(10)).  The
  suspects' marks, confirmed by the spike: (i) parked release fence — WeakMem's `wRelp` (`WeakMem.lean:684`) FAITHFUL
  at the fence, TsoMem's no-op (`TsoMem.lean:356-364`) STRONGER globally via rule 14 — CLOSED, a 0-step match; (ii)
  `wRes := none` at a non-trivial fence (`:688`) vs TsoMem keeping it (`Lang.lean:155-163`) — BOTH FAITHFUL (Zalrsc:
  invalidate at any time; FENCE does not cancel), VACUOUS on shaped runs; (iii) tearing — D20, CLOSED by `candSca`;
  (iv) the `.aq` floor — TsoMem's WRITE-position floor (`Lang.lean:136,151`) STRONGER than WeakMem's read-source floor
  (`:834`, FAITHFUL to the pf encoding), REFUTED as "off by one": off by `top − t` → **G1-Q**; (v) NEW footprint
  stamps → **G2-Q**; (vi) NEW DMA at the top → **G3-Q**.  The (Rec)/(b) dichotomy (move WeakMem toward MachCSL vs a
  MachCSL change) is superseded by the per-gap option sets above; the table's marks column is still owed by W2 [R9.s4].  **D8.** (Rec) "exactly 8 harts, all booted" named; (b)
  "≤ 8" (MachCSL change).  **D9. Panics.**  (Rec) not excluded, stated; (b) "no `panic:` bytes in the UART trace" (M–L;
  meaningful once W13 lands).  **D10.** (Rec) W1 via `xv6NiPhi`; (b) also W1b (L, serial).  **D11.** (Rec)
  observation-level β; (b) state-level α.  **D13.** (Rec) `Weak/`, `--weak` audit over the full `Xv6` cone; (b) a
  separate lane.  **D14.** (Rec) one boot; (b) multi-era W4 (M).  **D15.** (Rec) conclusions about the realizing
  MachCSL run + "the pf run never spins in the retry arm"; (b) none; (c) weak-side `Reducible` (XL).  **D16** → D22.
  **D17.** (Rec) the header names the SC-failure model; (b) §B(11) only — shares D19's Spec line [R9.1].
- **D18** — RULED [OWN.3]: W5d (M2) and W5d-G in the target; the user-fetch witness is not buildable by evaluation
  [R7.4] → D44 (i) → W14.
- **D19. Fused pairs / reservations** [R9.1].  Spec: RVWMO's atomicity axiom constrains only PAIRED (successful)
  aligned LR/SC — no store from another hart to the byte between the LR's source and the SC in gmo; Zalrsc — the SC
  "succeeds only if the reservation is still valid", a reservation is invalidated by another hart's store to the
  reservation set or the hart's own SC, and an implementation MAY invalidate it at any time (spurious failure allowed;
  only constrained loops get eventual success); NOTHING says a live reservation blocks or delays other harts' stores.
  Sail in this tree: `load_reservation`/`cancel_reservation` are no-op stubs (`LeanRV64D/Xv6Extras.lean:65-68`);
  `match_reservation`/`valid_reservation` ARE the opaques `xv6_resv_matches`/`xv6_resv_is_valid` (`:75-80`; both SC
  arms theorems, `Xv6/UserMemLrsc.lean:7-12`) — SILENT on reservation semantics; PMAs — RAM `reservability :=
  RsrvEventual`, `atomic_support := AMOCASQ` (`MachCSL/Platform.lean:253-254`), I/O `RsrvNone` (`:214,234`).  Marks:
  TsoMem's reservation serialisation (`Lang.lean:366-378,395-403`) — STRONGER than the spec (excludes the spec-allowed
  execution where a foreign store lands mid-pair and the SC fails), named in F1; (Rec) **`execProgOk'S`'s fused pairs —
  a quantifier RESTRICTION** (executions with a dangling LR or a failing SC are outside the theorem; STRONGER as a
  premise, honestly named, §B(11)); (b) a MachCSL change so dangling reservations do not block — TOWARD the spec
  (FAITHFUL direction), L, serial, re-opens whatever Xv6 proof consumes blocking (`MachCSL/UWait.lean:20-24` names
  `valid_reservation`; census **unverified**); (c) a user-mode fact — unavailable.  D17 shares this Spec line.
- **D20. `candSca`** [R9.1].  Spec: RVWMO "Memory Model Primitives" — a NATURALLY ALIGNED load/store of ≤ XLEN bytes
  is single-copy atomic; a misaligned access may be split into byte operations, not SCA; Sail in this tree — `mem_read`
  splits misaligned accesses via `split_misaligned` (`Mem.lean:414,511,547`; `SplitAccessUtils.lean:256`), RAM PMA
  `misaligned_exceptions.load_store := none` (`MachCSL/Platform.lean:250`: no fault, so the split path IS reachable);
  TsoMem reads EVERY load's bytes at one `tvn` regardless of alignment (`Lang.lean:363-367`); the cat model's
  `gloadValue` gives one gmo position per load EVENT regardless of alignment (mixed-size N10, out of scope, §A).
  Marks: (Rec) **`candSca` over every `LLoad` at M1/M2 ONLY, derived at Stage 2** (now `candScaT`, G1-Q (e) [W2s]) — FAITHFUL for naturally aligned
  loads ≤ 8 bytes, STRONGER for misaligned ones (kernel loads are compiler-aligned — **unverified** as a census; user
  code may misalign); (b) an atomicity axiom in sRVWMO — same mark, XL.
- **D21.** (Rec) report M1 as
  "composition milestone, kernel-only by premise `candKfetch`, loads SCA by premise `candSca`"; (b) nothing before M2.
  **D22.** (Rec) the `_entry` first-load witness gates M1 (SATISFIABLE, QUIESCENT, not reaching `allocproc`); (b)
  follow-up.  **D23.** (Rec) W1 via `xv6NiPhi` (S–M); (b) the rev-3 ledger hook (M).  **D24. W8's export form.**  (Rec)
  a per-state predicate on `g.m` + a ghost access ledger exported like `mmOk`, in `protReg`/`badSeg`'s vocabulary;
  (b) a new `Obs` per access; (c) trace-free from W9a's check + ownership facts.
- **D25** — RULED [OWN.5], spike-CONFIRMED: (a) cat-sound kill arms (`rsameC`/`gcrossE`, lock kit `*C`,
  `normalizeOfAcyclic` over the core), M–L.  **D26. Stage-2 sequencing** [R4.s5][R6.3][W2s].  (Rec) {W5b′ ∥ W2's ruling-independent rows ∥ W1b} → G1-Q–G3-Q
  rulings (+ the G2 (a) MachCSL change, serial) → W2 closed → W4 → M1 → M2 → W13 (E)(M)(T)
  (SERIAL: the alphabet sweep touches every chain file) → {W12 ∥ W12b ∥ W5d-G G1–G5 ∥ W13 (I)(L)(K)} ∥ W8 (after W2) →
  W13 (R)(W) → W9a/W10 → W11, W14 after W2's table and W13 (I)/(W); (b) start W8 with Stage 1 (risk: `R` not fixed).
  **D27** — RULED [OWN.6], spike-SHAPED: `gzFetch`, admin form, D40–D43.  **D28** — RULED [OWN.7]: all 182 + 58 sites through W8.
- **D29** [R5.1, Q-R] — RULED [OWN.8]; UPDATED [R6.3][OWN.14]: T2-1c′ LANDED; the literal axiom refuted → D32; `gdevAdj
  ⊆ gmo` on FOLDED blocks rejected, on I/O events it is (R3).  **D30** — RULED [OWN.9]: sibling root
  `xv6TextAdequacy_closed`; existing roots/baseline untouched; `tcb/expected.json` gains an entry [R6.5c] — DONE
  (Q-W3a (A) [OWN.16]).  **D31. W13-wit timing.**  (Rec) build on W5c's `esilAdmRun` bridge (LANDED) as W13 (W)'s gate 1 — the only
  pre-Stage-2 evidence that a device-active candidate exists; end = the first UART `sb` at `0x800008a0`, an `LIo` EVENT
  (needs W13 (E) first); (b) defer to Stage 2.

