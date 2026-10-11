# allocproc on RVWMO: target theorem, gap analysis, roadmap (design advisor, 2026-10-09)

**Status: rev 18 = rev 17 + review R14 (3 required changes, tags [R14.1]–[R14.3]; s1–s5 adopted) + [OWN.24].**
R14 (NOT SATISFIED) fixed three rev-17 WORKER-FACING texts, none touching the published statement: **[R14.1]** W-COH's
file list gains the MERGED `Weak/TsoOfPf.lean` (`tsoAfterLoadCoh :171-173` UNFOLDS `HRead.afterLoad` and states the
OLD semantics) and — found verifying — the `Vtest` lib (`vtest-lean/Vtest/XState.lean:234-256,283-292`, `HartExec.
lean:242-244,328`; NOT a default target, `lakefile.toml:43-49`); neither is in the Xv6/MachCSL CI build (`tools/ci/
audit.sh:13-16`), so the brief's acceptance BUILDS them and names three lemmas; **[R14.2]** W2's instance-INDEPENDENT
row is **exload** (`LExLoad`: `afterExcl` keeps `coh`), NOT exstore — `LExStore` is realized by the SAME `MState.store`
as the plain store (`Lang.lean:147-153,372-375`, `excl` a parameter), whose `coh` RESET W-COH adds, so the `LExStore`
row joins `LLoad`/`LStore` after W-COH; **[R14.3] + [OWN.24]** W5d-G G1–G5 run AFTER W13 (M) (D26's order; Q-W5dG-seq
RULED (a)) — the launch set, §C W5d-G and Status now say "G0 only".  History: R14 — Weak/Vtest lanes in W-COH;
`LExStore` after W-COH; Q-W5dG-seq (a) [OWN.24].
R13 (NOT SATISFIED) fixed two rev-16 texts, neither changing the published statement: **[R13.1]** the W-RSV (i-a)
census missed the M-MODE lane — the 35 `wp_m_*` wrappers (`MachCSL/WpMmode*.lean`) carry no context bundle, so their
STATEMENTS gain the fragment and `ProofEntry`/`ProofStart`/`ProofTimerinit` (68 applications) plus `SpecSpin`/
`ProofSpin` are edited: **12 `Xv6/` files, not 8** (16 rules in 9 files; 25 MachCSL; size class L–XL UNCHANGED; (i-a)
stays RULED [OWN.23] — the delta is RECORDED for the coordinator to REPORT (no gate [R14.s5]), §D W-RSV-Q); **[R13.2]** W2's hart
`LLoad`/`LStore` rows' Lean is against the COMPILED `TsoMem` that W-COH changes, so those two rows finish after W-COH
(the table and every other row launch now); W1b is RULED-in by [OWN.16] (c), not owner-gated.  History: R13 — (i-a)
census + M-mode lane; Stage-1 launch set listed at the top of §C.
R12 (NOT SATISFIED) fixed two rev-15 texts, neither changing the published statement: **[R12.1]** W-RSV's ghost cost —
`wpLoop_restart` CANNOT be "re-stated over `ctxTok`": the cycle rules do not hold it (the fragment rides one layer up,
in `kctx`/`uResvTok`), so form (i) threads `resvFragAny` through the cycle rules' STATEMENTS and their callers (16
rules; 25 MachCSL + 8 `Xv6/` files — 12 after [R13.1]; L–XL, one `Xv6`-cone rebuild) or moves it into an invariant — W-RSV is the LARGER
serial MachCSL item, not "L, `Xv6/` untouched"; **[R12.2]** [OWN.21] applied, every "coordinator to confirm" gate
removed, and the foreign-only stamp [R11.1-alt] named LOAD-BEARING for route (9d) (§B(10)).  **RULED [OWN.21]–[OWN.23]:
G2-Q (a′) with BOTH components — reset CONFIRMED [OWN.21], foreign-only stamp RULED [OWN.23]; W-RSV-Q (i-a)
[OWN.22][OWN.23]; D19 (b) stands.  W-COH LAUNCHABLE NOW.  No OPEN owner question remains (§D).**
R11 (NOT SATISFIED) fixed four rev-14 texts: **[R11.1]** G2-Q's (a′) was STRONGER than riscv.cat — rule 2's
`po-loc-no-w` exemption (`gppo2`'s last conjunct) has no TsoMem twin (`MState.store` never lowers `coh`); the
corrected (a′) RESETS the store footprint's `coh` and — **[R11.1-alt]**, found re-checking the fix — stamps FOREIGN
sources only (an OWN store below the view, stamped at its position, is the same defect again: §D G2-Q); **G2-Q RULED
(a′) [OWN.20] in this CORRECTED form, both components CONFIRMED/RULED [OWN.21][OWN.23]**; **[R11.2]** W-RSV re-specified as boundary clearing
(`hartStep .pure`), the in-flight guards STAY, three text corrections; **[R11.3]** the Exec-trace shadow cannot carry
`itv` (`fence.i` = the `sfence.vma` marker = `LFence false×4` in `E.exTr`) — W5d's `itvOf`; **[R11.4]** W13 (F-dep)
fills `LIo rd`'s `asrc` as the `LExLoad` arm does (the plain `LLoad` arm is D-8 `[]`).  R10 (NOT SATISFIED) fixed the rev-13 Layer-2 text: **[R10.1]** G2-Q option (a) as written ("stamp each byte with ITS
source") is NOT faithful — an own-FORWARDED byte's source lies above the load's view, `cohOk` is footprint-wide, so the
stamp is a NEW cross-byte strengthening that falsifies `candScaT` on a cat-consistent candidate; G2-Q is re-specified
((a′) global-source stamp only / (a‴) no coherence floor) and stays OPEN — the owner's [OWN.17] pick "(a)" predates
the finding and is to be RE-PRESENTED; **[R10.2]** `linCandScaT` is graph-derivable only under (a′)/(a‴) — under (b)
it needs W8's census (vi) transported (`g2Run` refutes graph-only); **[R10.3]** `pfStepFacts` reads the
pre-CONFIGURATION, the shadow is a function of the step-list PREFIX — W5b′ threads the shadow; **[R10.4]** the W5d-G
spike's `GraphFetchSpike.lean` is in NO working copy — UNRECOVERABLE [OWN.18], re-created from `notes/W5dG-spike.md`.
**RULED [OWN.17][OWN.18]: G1-Q (e) `candScaT`; G3-Q (a″) `candDiskLat` + (R2′) + anchors; D42–D43 (a); D46 (a);
D47–D49 (a); D50 (b) EXTEND the taggers (W13 (F-dep), in scope); D51–D52 (a).**  Rev 13: the W2 spike
(`notes/W2-spike.md`, `Weak/TsoOfPf.lean`) hit D7's STOP at **G1** `.aq` floor debt / **G2** footprint coherence stamp
(§0 F1 (iii)) / **G3** DMA reads at the top; Layer 2 redesigned around the TsoMem view SHADOW (§B(10)).  Rev 10/R8:
**D38 RULED [OWN.14]: MMIO accesses are I/O-CLASS GRAPH EVENTS**, W13 around `Lbl.LIo` + `ioResidueGmo`.  Every OPEN
or STANDING semantics question opens with a "Spec:" line and marks each option faithful / stronger / weaker (OWNER
RULE 2026-10-09) [R8.1][R9.1][R9.s3].**
**One-liner [R6.s1][R7.2a][OWN.12][OWN.14]: the published quantifier is riscv.cat RVWMO with TAGGED dependencies
(`rvwmoCatConsistentT`) over graphs whose rows CONTAIN the I/O accesses as events, plus an I/O-ordering PLATFORM
assumption (`ioResidueGmo`: BEYOND what ppo gives those events — nothing from FENCE (Sail drops the i/o bits), only
rule 5 and the (c1) dependency edges (D50 (b) [OWN.17]) — a row's RAM accesses po-before an I/O event and its RAM STORES po-after it are
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
rev 13 W2 spike D7 STOP (G1–G3 redesign: `tsoShadow`/`candScaT`/`candDiskLat`, (R2′); G1-Q–G3-Q) + W3 DONE + [OWN.16] (W1-Q, Q-W3a, D41, D45 RULED);
rev 14 (2026-10-10) R10 (4 req.: G2-Q (a) mis-specified → (a′)/(a‴); W11 (iv) under (b); W5b′ shadow threading; `GraphFetchSpike` lost; s1–s5) + [OWN.17–19] (G1-Q, G3-Q, D8–D9, D19 (b) → W-RSV, D20, D42–D43, D46–D52 RULED; G2-Q re-presented);
rev 15 (2026-10-10) R11 (4 req.: (a′) + `coh` reset [R11.1] + foreign-only stamp [R11.1-alt]; W-RSV boundary clearing; `itvOf`; (F-dep) `asrc`; s1–s5) + [OWN.20] (G2-Q RULED (a′), applied CORRECTED; W-RSV-Q NEW);
rev 16 (2026-10-10) R12 (2 req.: W-RSV ghost cost → (i-a)/(i-b), census 16 rules / 25 MachCSL + 8 `Xv6/` files, L–XL [R12.1]; [OWN.21] applied, gates removed, foreign-only stamp load-bearing for (9d) [R12.2]; s1–s5) + [OWN.21–23] (G2-Q (a′) BOTH components; W-RSV-Q RULED (i-a); D19 (b) stands; no OPEN question);
rev 17 (2026-10-10) R13 (2 req.: (i-a) census + M-mode lane — 35 `wp_m_*` statements, 12 `Xv6/` files, L–XL unchanged, (i-a) stays RULED, delta recorded [R13.1]; W2's hart `LLoad`/`LStore` rows after W-COH, W1b RULED-in [R13.2]; s1–s5; Stage-1 launch set at §C top);
rev 18 (2026-10-10) R14 (3 req.: W-COH + `Weak/TsoOfPf.lean` + `Vtest`, built explicitly [R14.1]; W2's `LExStore` row after W-COH, exload instance-independent [R14.2]; W5d-G G1–G5 after W13 (M) [R14.3]; s1–s5) + [OWN.24] (Q-W5dG-seq RULED (a)).

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
**`GraphFetchSpike.lean` (the W5d-G spike's 226 lines) — NOT IN ANY WORKING COPY (2026-10-09 [R10.4]: the `-w3`
workspace was re-used by W3 and holds `TextPristine`'s tree; no `GraphFetch*`, `fetchCutOk`, `gzFetch` or `emZifencei`
under any name in the main tree or any `../xv6iris-weak-*`); UNRECOVERABLE, never snapshotted by jj [OWN.18].  Its
STATEMENTS survive in the report `notes/W5dG-spike.md`; W5d-G re-creates the file from it (S–M, §C).  Every
`GraphFetchSpike.lean:N` cite below is the report's recorded statement, not a file; [OWN.10]'s "merge nothing else" is
MOOT (nothing left to merge)**; `W13Spike.lean` §3 is SUPERSEDED (§A(†)).

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
lean:5`), USER code may `lr`/`sc`.  What the reservation does NOT do [R11.s2]: it never decides an SC's success — the
opaque `xv6_resv_is_valid` does (`UWait.lean:21-26`, `Xv6/UserMemLrsc.lean:9-13`; `MState.store` never reads
`σ.resv cpu`, `Lang.lean:147-153,372-378`), so TODAY's LR/SC is already WEAKER than Zalrsc (an SC may succeed over an
intervening store; sound) and W-RSV removes only the blocking.  **D19 RULED (b) [OWN.19], form (i-a) RULED [OWN.22][OWN.23]: (ii) is
PLANNED OUT — once §C W-RSV lands, `σ.resv cpu` is CLEARED at the hart's instruction boundary (`hartStep .pure`,
`Lang.lean:499-502`; the pf twin ALREADY does this: `instrPost … wRes := none`, `Weak/WeakMem.lean:720-721`), so a
reservation blocks only within its issuing instruction (= the AMO's atomicity, FAITHFUL; Zalrsc permits invalidation
at any time); the blocking ARMS stay (firing only against in-flight reservations [R12.s4]); the ghost side threads the
hart's reservation fragment through the cycle rules and their callers — L–XL, the LARGER of the two serial MachCSL
items [R12.1]; this list then reads "(i) + (iii)" and the "Honestly" line below drops "reservation serialisation"**;
**(iii) [W2s] FOOTPRINT coherence stamping** — THREE components beyond riscv.cat rule 2 (`gppo2`, `Weak/AxGraphCat.
lean:151-156`: same-byte reads of DIFFERENT sources with NO same-hart write to the byte po-between) [R11.1][R11.1-alt]:
(1) a plain load stamps EVERY byte of its footprint with the load's view (`HRead.afterLoad`, `MachCSL/TsoMem.lean:268`;
the `cohOk` premise, `Lang.lean:365`), so two overlapping loads of DIFFERENT footprints are ordered even when the
shared byte reads the SAME write — witness `TsoOfPf.g2Run`/`g2Tso` (cat-consistent BY INSPECTION, `W2-spike.md:36-38`,
not in Lean [R10.s3]; no TsoMem schedule), mixed-size (N10-adjacent); (2) the stamp SURVIVES the hart's own store to
the byte (`MState.store` touches `hr` only by `clearAcq`, `Lang.lean:152`, `TsoMem.lean:277`) — rule 2's
`po-loc-no-w` exemption has no twin; (3) a byte read from the hart's OWN store is stamped too (own stores are visible
at any view, `HEnt.visible :115-116`, and cat puts no gmo constraint on them).  Hence G2-Q — RULED (a′) [OWN.20] in
the form correcting all three, BOTH components CONFIRMED/RULED [OWN.21][OWN.23] (§D).  NOT strengthenings, recorded against the spike:
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
   (`Weak/WeakEvInst.lean:360-364`) — BOTH remain under W-RSV (`blockedStep`'s arms stay, firing only against
   IN-FLIGHT reservations; the caveat must not be read as "blocking is gone") [R12.s4].  "never panics" = "no `panic:` bytes in the UART trace" (`uartSentSub`,
   `Xv6/UartTrace.lean:182`), M–L, new work — D9.  **Caveat until W14 lands (D44 RULED (i) [OWN.11])** [R7.4b]: the
   header says "non-vacuity certified to the first UART store / disk COMMIT" (W13-wit); REACHING `allocproc` is W14;
6. axioms `propext`/`Classical.choice`/`Quot.sound` + `bv_decide` certificates + the three opaques
   (`tools/audit/baseline.json:11-14`), no `sorry`; trusted base named: Sail model, image dump, the TAGGED cat
   transcription and its tagged conformance text `gdexecQconfT` (new trusted-SURFACE text — covering I/O items' sources
   under D50 (b), W13 (F-dep) — reviewed against
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
`gzFetch`/`gzContrib`/`emFenceI`/`fetchCutOk`/`gzFetchCut`/`gfcut`/`gwlog` (the W5d-G spike's — LOST, re-created by
W5d-G [R10.4]), `rvwmoCoreD`/`rvwmoCatAD` (scratch only), `Lbl.LIo`/`IoKind`/`lbIsIo`/`gisIo`/
`ioResidue`/`ioResidueGmo`/`gfBefore`/`ptraceRelIO`/`gnxa`/`racyDIO`/`cycleKillIO`/`mstep.MStepIo` (rev 10),
**`tsoShadow`/`scaOkT`/`candScaT`/`diskLatOk`/`candDiskLat`/`pfStepTso`/`pfLoadRow`/`linCandScaT`/(R2′) (rev 13 [W2s];
in `Weak/TsoOfPf.lean` only `histOf`, `fenceRow`, the G1/G2 witnesses)**, `itvOf`/`itvStep` (W5d [R11.3]), `Ioev`/
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
§B(11b)), subsumed by (R1), vacuous as a trusted use — D52 RULED (a) [OWN.18]; **dependency edges through `LIo` are
ON — D50 RULED (b) [OWN.17]**: the taggers get the (c1) edges (addr/data/ctrl → I/O store, addr → I/O load, provenance
OUT of an I/O load; NO ctrl → I/O load), W13 (F-dep), §C — in-edges are subsumed by (R1) (RAM source) / (R3) (I/O
source), out-edges into RAM STORES by (R2); the ONE edge class beyond (R1)–(R3) is I/O-load →addr→ RAM LOAD (rule 9),
expected absent in xv6 (MMIO values flow to ctrl, to RAM/I/O stores as data — **unverified** census).  **The trusted item
is an INCLUSION, not an acyclicity over an extended order** — gmo is already total over `gmem`: `ioResidueGmo GF :=
∀ x y, ioResidue GF x y → gmoLt GF.gfGd.gdG x y` with **(R1)** `gpo x y ∧ gmem x ∧ ¬ gisIo x ∧ gisIo y` (a row's RAM
accesses po-before an I/O event, READS included); **(R2)** `gpo x y ∧ gisIo x ∧ gisW y` (an I/O event po-before a
row's RAM WRITE — `grule14`'s shape, `Graph.lean:257-258`, with `gmem` covering I/O; reads po-after stay UNORDERED,
the (a′) point [R7.1]); **(R3)** `gisIo x ∧ gisIo y ∧ (gpo x y ∨ gfBefore GF x y)` (same-row issue order — ISA-given
only within ONE channel (F2), cross-channel residue — and fabric order, stated on the ORDER `gfBefore`, not `gdevAdj`,
so hulls that cut I/O events out keep it); **(R2′) [W2s; G3-Q RULED (a″) [OWN.17]]** `gpo x y ∧ gisIo x ∧ gisR y ∧ y.1 = NCPU`
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
(iii) **The unpinned supply is TWO items** [R4.2], SHAPED by the W5d-G spike (DONE; its Lean file LOST, statements in
`notes/W5dG-spike.md` — every `GraphFetchSpike.lean:N` below is the report's record [R10.4]) [R6.4b].  **W5d** (M2, L; in the
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
`max itv (fencePost true false tv rv pub)`, `Lang.lean:155-163`), so `R-itv` is `itv_T = itv_S ≤ q` — **carried by
W5d's `itvOf`, NOT by the Exec-trace shadow [R11.3]**: `fence.i` and the Q7 `sfence.vma` marker are the SAME label
`LFence false false false false` (`ebarLabel`, `WeakEvInst.lean:272-275`; `ebarNow .Barrier_RISCV_i = none`,
`WeakEvLang.lean:745`; `annLabel :418-419`), `projLbl` keeps it (`WeakPromiseBridge.lean:536`) and `lbAdmin` excludes
it (`WeakAxRealize.lean:129-133`), so both reach `E.exTr` as indistinguishable `Estep`s; `emFenceI`'s criterion needs
the admin block `ls`, which is existential PER INDEX inside `execProgOk'S` (`PfRunShape.lean:242-262`), and `fok` has
no `itv` argument (`fok : Image → List Wmsg → Nat → Int → List (Nat × BitVec 8) → Prop`, `:232,242`).  W5d therefore
adds a per-row, per-step `itvOf : Nat → Nat → Nat` to `execProgOk'S`, DRIVEN by the index's REALIZING label (`s.esLb =
LFence false×4` on the left arm) and CONSTRAINED inside each index's conjunct, where `ls` IS in scope (`fetchesOk … ls`,
`PfRunShape.lean:232-234`) — `ls` serves ONLY to tell `fence.i` from the `sfence.vma` marker by `emFenceI`'s criterion
(the marker's star ends in `LIFetch`, `fence.i`'s in the announce `LInstr`, `W5dG-spike.md:115-117`): `itvOf (k+1)
s.esAg = itvStep (itvOf k s.esAg) (tv, rv of the memory-field shadow at k) pub ls` with `pub = ownPub` from the log
(`itvPostMachCSL`, `WeakInterp.lean:378-384`), plus the FRAME condition `itvOf (k+1) i = itvOf k i` for every row `i ≠
s.esAg` and at every non-fence step [R12.s1]; `fok` takes it as a 6th argument: the M2 cut form is `∃ q, itvOf
k i ≤ q ≤ |log| ∧ ifetchOk … ∧ ∀ byte, t ≤ q`; lemma: the step-list `tsoShadow`'s `itv` equals `itvOf` along the
replay.  Over-approximating (every `LFence false×4` raises `itv`) is not derivable at Stage 2 (`gzFetch` uses the
EMISSION's `fence.i` sites); under-approximating (`itv = 0`) breaks W4's `LIFetch` row (TsoMem fetches at `itv ≤ tvn`,
`Lang.lean:360-362`).  M1's `candKfetch` is unaffected.
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
D40).  Scratch (LOST [R10.4]; the report records): proved `fetchCutOk`, `fetchCutPrefix :63` (cut form = the pf/W5d
check at the realizing prefix, ONE view), `fetchCutEdge :83`, `fetchRelOk`, `fetchRelCut :140`, `fetchPinCutOk :213`;
stated `gzFetch`, `gzFetchCut`, `emZifencei`, `gfcut`, `gwlog` — W5d-G's G0 re-creates them (S–M; the proofs were
elementary, the risk is the STATEMENTS drifting from the report: re-check each against `W5dG-spike.md`'s text).  **Kernel-text instance**: tag 0, image bytes, no write ⇒ (Z1)–(Z3) vacuous;
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
(`W2-spike.md`; its faithful/stronger/weaker column [R9.s4] is MISSING — D7's marks stand in; W2's ACCEPTANCE
requires it [R10.s5]): ✓ `LSilent` (0 TsoMem
steps — **W4 is a STUTTERING simulation**), `LInstr` (0 steps; under W-RSV the shadow's `resv := none` at the boundary
matches `instrPost`'s `wRes := none`, `WeakMem.lean:720-721` — the acceptance table's `LInstr` row records it
[R12.s5])/`LRegW`/`LCtrl`, `LIFetch` M1 (pristine text, `Wp.lean:1478, 1490`), hart `LStore` (`¬ othersReserve` from
`pairAdjacent`; the acceptance table's `LStore` row records BOTH shadow effects — the (a′) `coh` RESET [R11.1] and
`resv := none` (unchanged, `Lang.lean:152`) — `R-view` stays equality [R11.s4][R12.s5]), disk `DWrite` (`storeDma`, `¬ anyReserve`), `LFence`
non-`fence.i` (**`fenceRow`, PROVED**), `fence.i` (identity vs `itv`), the parked `fence rw,w` (0 steps; `wRelp`/`wPub`
inert — suspect CLOSED), `LExStore` (its row records the SAME two effects — reset + `resv := none` — plus the `excl &&
acq` floor move to `top + 1`, `Lang.lean:150`; the reset half after W-COH [R14.2]), `LDev`; **conditional**: `LIFetch` M2 (§B(4)(iii) (i)–(ii)); hart `LLoad` iff (★);
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
`R-img`, `R-resv` (`none` unless mid-pair) are the spike's.  [Correction, reason fixed by [R10.s1]: the spike's `tvn :=
max(tvn_sca, F_T)` is too LARGE — not because `rv` would break `R` (moot under EQUALITY) but because `rv` feeds `tv` at
the next `fence r,*` (`Lang.lean:155-160`, `fencePost TsoMem.lean:345`) and Stage-2 derivability needs every
contributor to `F` to be ≤ the gmo position of a later load, which rule 4 gives for the EARLIER load's gmo position =
its `tvn_sca`, not for an arbitrary larger view; take the minimal view.]  **The shadow is a function of the step-list
PREFIX, not of the configuration** [R10.3]: a `Wpcfg` holds the log (writes only), the WeakMem `Wstate`s and program
states (`WeakPromise.lean:135-139`); fences, plain loads and aq pairs move `tv/rv/coh/acq/itv` (`Lang.lean:127-163`)
and leave no trace in `pcLog` — so W5b′ threads the shadow (§C).  [R10.s2] Under equality-`R` every POSITIVE row
reduces to "a TsoMem step EXISTS at the shadow's view with the pf bytes" (TsoMem's fence step always exists and the
shadow IS its view; `fenceRow`'s inequality is the spike's record, no longer the row's content).
**`candScaT` — G1-Q RULED (e) [OWN.17]** := `scaOk` plus `F ≤ tvn`.  **Why it discharges (★) ALONE** [R10.1]
(recorded so W2/W4 do not re-derive it): hart load `r` at the shadow's minimal view `tvn := max(F, max_{foreign j}
t_j)`: `tv_S ≤ tvn`, `cohOk`, `tvn ≤ top` hold by construction (`t_j ≤ |log|`); `Hist.read` at `tvn` returns `t_j` per
byte iff no visible later write to byte `j` — own later writes are excluded by `scaByte` (visible = own), foreign
ones in `(t_j, tvn] ⊆ (t_j, tvn_sca]` by `scaByte` at `tvn_sca` once `F ≤ tvn_sca` (foreign `t_j ≤ tvn_sca` by
`scaVis`).  G2-Q does NOT enter (★): it decides whether `candScaT` is TRUE/DERIVABLE, i.e. which `coh` stamp the
shadow replays.  **Stage-2 derivation (W11 (iv) `linCandScaT`)**: `tv` part — the SCA witness `tvn_sca := #writes
gmo-before r` is a legal `scaOk` witness (`tvn_sca ≤ |log|` at `r`'s trace position: every `w <gmo r` has `w <gmo
nxw(r)` by rule 14 on `GD'`, so `gwix w < gwix (nxw r)` and `w` sits in an earlier `rblocks` block, `Lin.lean:316,440`;
bytes co-maximal by `gloadValue`); `tv_S` after an aq pair `= gwix(LRmw)` and `LRmw <gmo r` by rule 5 (`gacqPo`,
`LRmw` is `lbIsR ∧ lbAq`); `tv_S` raised by `fence r,*`/`rw,*` to `rv`/`pub`: every contributor (an earlier load's
minimal view ≤ its `tvn_sca`; `top` at an exclusive read `= gwix(LRmw) − 1`; `ownPub = gwix` of the last own store)
is the gmo position of an event rule 4 puts gmo-before `r` — G1 and G1′.  **`coh` part — the G2-Q case split**
[R10.1][R10.2][R11.1][R11.1-alt][OWN.23]: under the ruled (a′), BOTH components (`afterLoad` stamps `coh a := max (coh a) t_a` ONLY for a
FOREIGN source — `e.tid ≠ hartAgent cpu`, hence `t_a ≤ tvn` automatically; own-sourced bytes, forwarded or below the
view, UNSTAMPED; `MState.store` RESETS `coh a := 0` on its footprint) `coh a` at `r` is the max of the foreign-source
stamps of the loads of byte `a` po-after the hart's LAST own store to `a`; for each such `r_prev` with source `w'`:
same source → `w' <gmo r` by `gloadValue` (`w'` foreign); different source (foreign `w''` or an own `m` po-before
`r_prev`) → no own write to `a` po-between, so rule 2 (`gppo2`) gives `r_prev <gmo r`, and `w' <gmo r_prev` by
`gloadValue`; own write `m` to `a` po-between → the stamp was RESET, later stamps recurse — THREE cases, GRAPH-ONLY,
each giving `gwix w' ≤ tvn_sca(r)`.  Why FOREIGN and not "`t_a ≤ tvn`" [R11.1-alt]: an own store `m0` BELOW the view
(`m0`'s position ≤ `tvn_min(r_prev)` because another byte of `r_prev` has a later foreign source) would be stamped at
`gwix m0`, yet cat lets a later same-source read `r` sit gmo-BEFORE `m0` (own stores are visible by po, no `W;po;R`
ppo, same source ⇒ no rule 2): hart A `sb a` = `m0`, `lh (a,d)` = `r_prev` (a from `m0`, d from foreign `w_d`), `lh
(a,c)` = `r` (a from `m0`, c from foreign `w_c`); hart B `w_c`, `w_c'` (both to c), `w_d`; gmo `w_c <gmo r <gmo w_c'
<gmo m0 <gmo w_d <gmo r_prev` is cat-consistent (ppo on A empty; load-value ✓), but with the stamp `coh a = gwix m0 >
gwix w_c'` TsoMem reads `w_c'` for byte c — `candScaT` FALSE.  **Hence the foreign-only component is LOAD-BEARING for
(9d), not cosmetic [R12.2][OWN.23]**: under the reset ALONE that candidate is cat-consistent yet has NO TsoMem
schedule, so at Stage 2 `cycleKill`'s realization of a proper hull as a TsoMem run (§B(9d), `hullRun`, W4) FAILS on it
and the robustness theorem is UNPROVABLE — a hole in (9d), not merely "W11 (iv) harder"; the only repairs are the
component itself (RULED) or a W8 census excluding the shape (a (b)-style TRANSPORTED fact, M, **unverified**) — MOOT.
Under (a‴) (no coherence floor) `F = tv_S` and the part VANISHES; under (b) (TsoMem keeps the footprint stamp) it is NOT graph-derivable — the
plan's own `g2Run`/`g2Tso` (`TsoOfPf.lean:160-199`) is cat-consistent with `F = coh b = 2 > tvn_sca = 0` — and comes
only from W8's census (vi) TRANSPORTED through `R`'s log identification (po-induction: every load's `F` ≤ the gmo
position of every later load sharing a footprint byte).  At M1/M2 `candScaT` is a PREMISE (restricts the candidate's
log order to a gmo-extension — internal milestones only).  **`candDiskLat` — G3-Q RULED (a″) [OWN.17]** :=
every disk-row `LLoad` is `latest` per byte — the `lat = true` CONDITION of `readOkD` (`WeakPromise.lean:183-188`) as a
SHAPE clause, NOT a label change (`latFree`, `WeakPromiseFact.lean:61`, consumed in 16 files incl. `lblRealizes`,
`AxRealize.lean:241`, and `pstepEvLatFreeProg`, `WeakEvCapstone.lean:1052`, stays TRUE): the `DRead` row then matches
`dmaView`.  Stage-2 derivation: disk-row reads become rule-14 ANCHORS of (L) (`gnxa` ∋ disk reads: the trace respects
gmo between a disk read and EVERY write) — consistent because the disk row's po is gmo-ordered by (R1) (DMA writes →
COMMIT), (R3) (COMMIT → next START), (R2′) (START → reads) and rule 14 (a request's reads precede its writes,
`VirtioProg.lean:606-619`); `normalizeOfAcyclic` keeps the anchors as it keeps I/O positions.  **G2**: NO shape clause
closes it against TsoMem AS IS (`g2Tso`: every legal `tvn₁ ≥ 2` stamps `coh b`; the minimal view does not help) — the
shadow is PARAMETRIC in the stamp pair and G2-Q picks the instance (RULED (a′), BOTH components [OWN.20][OWN.23][R11.1]).  **(★) for a plain load of hart `i`**: no write by
another agent to byte `base+j` in `(t_j, F]` — a LOG-LEVEL fact about ONE load, DISCHARGED by `candScaT` alone
[R10.1]; what W8 may still owe is NOT (★) but the census (vi) feeding `linCandScaT` under G2-Q (b) [R10.2] (§C W8).
**Log identification** (W8/W11 vocabulary): pf message `k` = the TsoMem store at timestamp `k+1`, same author/
footprint/bytes; classes stay pf-side (`wmAk` has no TsoMem image; `protReg`/`badSeg` read the pf log).  W14's SC run
is unaffected (every load at the top, so the corrected (a′)'s stamps are ≤ top and its resets harmless [R11.s5]).  (↑) NOT claimed.  **D19 RULED (b) [OWN.19], form (i-a) RULED [OWN.22][OWN.23]** (reservations cleared at the instruction
boundary, §C W-RSV [R11.2][R12.1]) changes three rows' ARGUMENTS, not the mechanism: hart `LStore`/disk `DWrite` need
`¬ othersReserve`/`¬ anyReserve` only against IN-FLIGHT (intra-instruction) reservations, which `pairAdjacent` gives
without clause (i); `LExStore` needs NOTHING of the own reservation (TsoMem never reads `σ.resv cpu` for its own
store, `Lang.lean:147-153,372-378` [R11.2]); `R-resv` becomes EXACT (`resv_T c = snapshot of wRes_c`, both `none` at
every boundary — `instrPost`, `WeakMem.lean:721-722`).  Size: L (↓: `pfStepTso`, `pfLoadRow`) + S–M
(**W5b′** `Weak/TsoShadow.lean`: `tsoShadow` over the step list, `scaOkT`/`candScaT`, `diskLatOk`/`candDiskLat`, the
shadow-threaded `pfStepFacts`/`pfRunS` and the re-proved replay snoc [R10.3]; the `stamp` parameter is a PAIR (load
stamp, store effect) so W2's table stays parametric [R11.1]) + L (W4, stuttering, disk rows) + M (W5) + M–L (W5c ✓) + L (W5d).  It lifts the WHOLE system
theorem; (9d) reuses it both ways; **the log identification carries `protReg` and `¬ badSeg`** (W11).

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
footprint), and — D50 RULED (b) [OWN.17] — the (c1) DEPENDENCY edges (W13 (F-dep): the graph-stated (F3)) — while
the ISA PROSE additionally gives (F1), (F2), (F4)–(F6) (§B(11b)), expressible only via the rest of D46 (b) (RULED (a)
[OWN.17]: prose); the ASSUMPTION is the rest — each I/O access acts as a ONE-WAY FENCE for the issuing
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
sense (GRAPH-tier uses — the fence/trap ones for good, D46 RULED (a); the dependency ones become graph FACTS under D50 (b)): the pre-NOTIFY direction (two `fence iorw,iorw`), the post-ACK loads (the third
fence), loads before a handler's claim (precise traps), dependency-pinned sources of a device store; not uses at all:
the disk row's DMA-before-COMMIT (device model), the racy flags `pr.locking`/`panicked` (stale reads stay in the quantifier).
**User-row gaps under [OWN.3]** [R6.2] (D35/D36 RULED (a) [OWN.13]): rule 7 RCpc and forwarded plain `LLoad aq`, both
vacuous for kernel rows.  Strengthenings carried INTERNALLY by TsoMem/sRVWMO (gone once (9d) lands): "stores never
early"; reservation serialisation (gone EARLIER, once W-RSV lands — D19 RULED (b) [OWN.19]).  Machine-model choices:
exactly 8 harts booted (D8 RULED (a) [OWN.19]); **ONE sequential device row** (`i =
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
D46 RULED (a) [OWN.17] keeps the fence fragment `emIoFence` (S–M), the trap-boundary edges (S) and `ioOrdF ⊆
ioResidue` (S) as PROSE (header-only value); D50 RULED (b) [OWN.17] puts the DEPENDENCY part IN SCOPE — W13 (F-dep),
M: the taggers `dstep` (`WeakRvwmoConf.lean:493-495`) / `dstepT` (`AxDeps.lean:461-463`) are inert on `LDev` and the
MMIO arms of `pnodeStep` emit `LDev` with NO source fields (`WeakEvInst.lean:300-304,335-338`; rev 10's "`oib = none`
discard" was a misnomer [R11.s1] — in `pnodeStep` `oib = none` means "`ib` UNCHANGED" (`.pure → some ibNone`, `regRead →
some (ibRd ib r)`, every other arm `none`, `:284-296`), the RAM store arm has it too; what the MMIO arms lack is the
read set `depsOfIb ib.ibBits` ON THE LABEL, as `LExLoad`/`LStore`/`LExStore` carry `asrc`/`vsrc`, `:329-331,344-355`),
§C W13 (F-dep).**
**(12) Audit coverage and file layout** [R1.10].  `Xv6/` never imports `Weak/` (`lakefile.toml:2,27-41`).  Composition
files live in `Weak/`, registered in `tools/ci/roots-weak.txt` + `tools/audit/baseline-weak.json` + `XV6_AUDIT_MODULES`
(`tools/ci/audit.sh:44`), built by `--weak` CI over the whole `Xv6` cone (D13); pure-`Xv6/` items (W3, W8) go to
`roots.txt`/`baseline.json` (`tools/ci/lint.sh` checks agreement).  [R14.1] A MachCSL change whose cone build is green
can still break `Weak/` (`audit.sh:13-16`: "Weak/ is not in the Xv6/MachCSL build CI audits") and the `Vtest` lib
(`lakefile.toml:43-49`, NOT a default target; `tools/ci/vtest.sh check`) — W-COH's and W-RSV's briefs REQUIRE `lake
build Weak.TsoOfPf Vtest` (or the `--weak` lane + `vtest.sh check`) in their acceptance.  S.

## C. Roadmap

Each stage ends in a theorem; "∥" = parallel (one Opus worker, one file each).  Stages 0–1b are INTERNAL
milestones on the critical path of the target; Stage 2 is the target [OWN.2].

**Stage-1 launch set [R13.2] (no owner gate remains, §D).**  MAY LAUNCH NOW, in parallel: **W5b′** (`Weak/TsoShadow.
lean`, shadow-threaded) → **W2**'s acceptance TABLE (parametric in the `coh` stamp pair) and every instance-INDEPENDENT
row's Lean (store-reservation side, **exload** (`LExLoad`: `afterExcl` keeps `coh`, `TsoMem.lean:273`) [R14.2], fence,
`fence.i`, fetch-M1, silent/regw/ctrl/dev, `DRead` under `candDiskLat`) plus `pfLoadRow`'s FlatMem ↔ `histOf` bulk;
**W-COH** (serial MachCSL lane, G2-Q RULED; brief: + `Weak/TsoOfPf.lean` + `Vtest`, built explicitly [R14.1]); **W13
(E)** (D47–D52 RULED) then (T); **W5d-G G0 ONLY** (re-creation, S–M; acceptance: builds, each statement matches
`notes/W5dG-spike.md`; G1–G5 per D26, AFTER W13 (M) — Q-W5dG-seq RULED (a) [OWN.24][R14.3]); **W1b** (RULED-in
[OWN.16] (c); owner's schedule, D10).  WAITS FOR W-COH LANDING: W2's hart `LLoad` row (`afterLoad` post-state) and
hart `LStore` AND `LExStore` rows (`coh` RESET — both through the ONE function `MState.store`, `excl` a parameter,
`Lang.lean:147-153,372-375` [R14.2]) — their `R-view` EQUALITY is against the COMPILED `MState.afterLoad`/`MState.store`
(`Lang.lean:127-129,147-153`), which W-COH changes (and `HRead.afterLoad`'s signature) — S–M once it lands, no
critical-path cost; W4 (the shadow's INSTANCE), hence W5/M1, W5d/M2; W-RSV (shared files, then also M1 per D26).

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
- **W1b (RULED-in by [OWN.16] (c); schedule at the owner's discretion (D10) [R13.2]; L, serial; CARRIES W1-Q (c))**: `pidHistWf h` in `pidLedger` (live pids distinct), the `nextOf ≤
  PIDMAX` tie and `ι.kNull → poolEmpty` through `NiLedger` (`niFitEv`/`niEntryOk`, supplied at `SyscallArmsFork.
  syscArmFork_ev`/`_evNeg`); re-thread `ProofAllocproc`/`ProofFreeproc`; optionally addresses in `Kev`.  D10.
- **W2 — SPIKE DONE, D7 STOP (`notes/W2-spike.md`; `Weak/TsoOfPf.lean` MERGED)** [R1.11][R2.3][R3.4][R6.4b][W2s].
  Verdict, gaps, corrections and the redesign in §B(10).  **W2 proper (L)** = `pfStepTso`: for every memory label a
  `wpPfStep` from an `R`-related state under `pairAdjacent` + `execProgOk'S` + `candScaT` + `candDiskLat` is 0 or 1
  TsoMem steps with the same bytes to a related state (`R-view` = equality through `tsoShadow`); `pfLoadRow` under (★)
  (FlatMem ↔ `histOf`, the bulk).  **Launchable NOW (G1-Q (e), G3-Q (a″) RULED; [R10.1]+[R10.3] landed in rev 14)
  [R13.2]**: **W5b′** (below) → the acceptance TABLE (PARAMETRIC in the `coh` stamp: a `stamp` PAIR argument of
  `tsoShadow` — load stamp × store effect [R11.1]: today's footprint-`tvn` × none / the corrected (a′) foreign-source
  per byte × footprint reset / (a‴) none × none) and every instance-INDEPENDENT row's Lean: the store-reservation side,
  **exload** (`LExLoad`: `afterExcl` keeps `coh`, `TsoMem.lean:273` — the exclusive READ's post-state, `evStep`'s
  `.memRead` arm with `akExcl`, `Lang.lean:368-371`; rev 17's "exstore" named the wrong half [R14.2]), fence (`tv`/`itv` only, `:155-163`), `fence.i`, fetch-M1
  (`LIFetch` reads only), silent/regw/ctrl/dev, `DRead` under `candDiskLat` (`dmaRead`/`storeDma` move no hart `hr`),
  plus `pfLoadRow`'s FlatMem ↔ `histOf` bulk; the pair rows' arguments per D19 (b) (§B(10)).  **After W-COH lands**:
  the hart `LLoad` row's `afterLoad` post-state ((★) discharged by `candScaT` alone, §B(10) [R10.1]) and the hart
  `LStore` AND `LExStore` rows' `coh` RESET ([R14.2]: `LExStore` is `evStep`'s `.memWrite` RAM arm `σ.store … (akExcl
  …)`, `Lang.lean:372-375` — the SAME `MState.store` as the plain store, `excl` a parameter, whose `hr` update is
  `clearAcq` today and `clearAcq` + the reset after W-COH; no `excl` case split exists or is wanted) — their `R-view`
  EQUALITY (`hr_T = hr_S` through `tsoShadow`) is against the COMPILED
  `MState.afterLoad`/`MState.store` (`Lang.lean:127-129,147-153`; `HRead.afterLoad` footprint-`tvn` TODAY, `TsoMem.
  lean:268-270`), which W-COH changes together with `HRead.afterLoad`'s SIGNATURE, so an arm stated over the old one
  breaks (S–M once W-COH lands; W-COH is S–M and runs in parallel — no critical-path cost).  G2-Q (RULED (a′), BOTH
  components [OWN.20][OWN.23][R11.1]) fixes which INSTANCE W4 uses (the actual MachCSL `TsoMem` after W-COH) and
  those three rows' Lean, not the table's text.  **Acceptance** [R9.s4][R10.s5][R11.s4]: the (↓) table WITH its
  faithful/stronger/weaker column (owed since R9), including rows for the hart-`LStore` and `LExStore` `coh` reset [R14.2].
- **W5b `Weak/PfRunShape.lean` — DONE** (625 lines, green; API `../weak-orch/W5b-API.md`) [R2.3(iii)][R3.2][R3.4]
  [R5.3][R6.4c].  Landed: `candKfetch :53`, `scaVis/scaByte/scaOk :61-72`, `execSca :78`, `candSca :85`, `pairAdjacent
  :95` (+ `Nil/App/Fused/Blk`), `admRunG :224`, `fetchesOk :232`, **`execProgOk'S :242`**, `pfStepFacts :265`, `pfRunS
  :273`, the replay **`execPrefixPfRunProgShaped :512`** / `execWfPfRunProgShaped :594` / `execWfPfRunPinShaped :608`
  — PROVED: `pclsEqr pcls → pstepPinned (exImg E) pstep → execWf E → execProgOk'S … → n ≤ |trace| → ∃ c st, pfRunS … st
  c ∧ pairAdjacent st ∧ states/fabric match ∧ cfgMatchd c (stt E n)`; helpers `execProgOk'SForget/SSca`, `pfRunSRtc/
  PinSub/Trans/One`, `mstepWpPfStepPairS`.  **Deviations from rev 11**: (i) ARITY 6 — `fok` explicit (the left arm is
  `lbFused l ∧ lblRealizes …`, no constructor list: W13 (E)'s payload `LDev` joins unchanged); (ii) the replay is
  PINNED/M1 ONLY (`pstepPinned` hypothesis) — W5d's M2 replay drops it; (iii) `scaOk` has NO floor normalisation
  (`tvn ≤ |log|` only; TsoMem's `Hist.read` via `scaVis`) — W2's `R` carries `tvn`; (iv) [R10.3] `pfStepFacts c i l`
  reads the PRE-CONFIGURATION only (`:265-269`; `pfRunS.snoc … pfStepFacts fok c1 i l`, `:273-277`), so rev 13's
  "`pfStepFacts` carries `candScaT`, the replay threads it unchanged" was FALSE — true for `diskLatOk` (log-only), not
  for the shadow.  **W5b′ [W2s][R10.3]** (S–M; S under G2-Q (a‴) [R10.s4]; `Weak/TsoShadow.lean`): `tsoShadow (stamp)
  : List (Nat × Wlabel) → CPU → (tv, rv, coh, acq, itv)` over the STEP LIST (admin items included, so `fence.i` is
  recognisable by `emFenceI`'s criterion for `itv`), parametric in the `coh` stamp PAIR [R11.1]; `pfStepFacts fok st c
  i l` takes the shadow of the prefix `st` (or `pfRunS` indexed by it); clause (iii)′ of `execProgOk'S` as `scaOkT` over
  `shadowOf (E.exTr.take k)` — **the MEMORY-FIELD shadow only (`tv/rv/coh/acq`) [R11.3]**: those ARE computable from
  `E.exTr` (`LRmw aq`, the `LFence` bits, `LStore` for the `coh` reset, the log for foreign-ness and `ownPub`) and a
  projection lemma ties them to the step-list shadow; `itv` is NOT (§B(4)(iii) (ii)) and enters `execProgOk'S` through
  W5d's `itvOf`; and NEW clause (iv) `diskLatOk`/`candDiskLat` (agent `NCPU`'s loads latest per
  byte); the snoc case of `execPrefixPfRunProgShaped :512` re-proved with the shadow threaded (the replay already
  produces `st`).  Launchable now (§C W2).  [R14.s2] W5b′/W2 run beside W13 (E), which gives `Wlabel.LDev` a payload
  (`WeakPromise.lean:86`; `PfRunShape.lean:14` already notes it for W5b): `tsoShadow` and `pfStepTso` match `LDev` with
  a WILDCARD arm (`| .LDev .. => …`), never an arity-specific pattern, so (E) joins without a rebase.
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
  cut form at `itvOf` (M2) [R11.3].  Deps: W2 CLOSED, W3 ✓, and the shadow INSTANCE = the actual `MachCSL.TsoMem`:
  W4 needs W-COH LANDED (G2-Q RULED (a′), BOTH components [OWN.23]; W-COH LAUNCHABLE NOW); W-RSV (RULED (i-a)
  [OWN.23], L–XL) lands AFTER W4/M1 (D26), and W4 then re-checks three rows (`LStore`, `DWrite`, `LExLoad`; S), the
  arguments of §B(10) [R11.2][R12.1].
- **W5 `Weak/SrvwmoXv6Adequacy.lean`** (M) [R1.5][R2.1][R3.1][R3.s2].  **M1 is STATED THROUGH `srvwmoXv6M1Premises
  σ0 c pst dv`** (never a re-listed premise set; satisfiable by `srvwmoXv6M1Satisfiable`): `srvwmoXv6M1PfRun` already
  gives the shaped `pfRunS` run (T1 + `execWfPfRunProg` + `wpPfRunPinSub` + W5b inside it); W4 projects;
  `xv6FsAdequacy_closed`, `xv6NiAdequacy`, `unionAdequacyClosed` (`Xv6/LinkUInitUnion.lean:163-164`), W3's root
  `xv6TextAdequacy_closed` ✓ and W1 (`allocprocTraceAns`, the RULED interim [OWN.16]) conclude.  M1's premise set gains
  W5b′'s clauses through `execProgOk'S` (the DEFINITION `srvwmoXv6M1Premises` is re-pointed, S).  Header: internal
  milestone, kernel-only by PREMISE (D21), loads SCA at or above the TsoMem floor by premise `candScaT`.  Registered per
  §B(12).  Deps: W1 ✓, W3 ✓, W4, W5b ✓ + W5b′, W5c ✓.

- **The two SERIAL MachCSL items — both RULED, no gate left [OWN.21]–[OWN.23] (one worker, one `Xv6`-cone rebuild
  each).**  `Xv6/` NAMES neither reservations nor `coh` (census: `Xv6/*.lean` has no `othersReserve`/`blockedStep`/
  `resvMap`/`snapOf`/`cohOk`, only `SystemSlot.lean:64`'s comment on `mmOk`'s `resv_ok`) — true of NAMES, not of the
  FILES a statement change touches: W-RSV (i-a) changes the cycle rules' AND the 35 `wp_m_*` wrappers' statements and
  so edits 12 `Xv6/` files (8 apply a cycle rule directly, 3 apply `wp_m_*`, `SpecSpin`) [R12.1][R13.1].  Order: **W-COH first** (S–M, LAUNCHABLE, unblocks W4/M1), **W-RSV second** (L–XL —
  the LARGER of the two [R12.1]); they overlap in `TsoMem`, `Lang`, `Resources`, `Wp`, `WpAtomic` — never in parallel.
  **W-COH — G2-Q RULED (a′) with BOTH components [OWN.20][OWN.21][OWN.23] (S–M; LAUNCHABLE NOW [R12.2])**: (1) the
  RESET — `MState.store` resets `coh` on its footprint (a new `HRead.resetCoh pa n` beside `clearAcq`, `TsoMem.lean:277`;
  `Lang.lean:147-153`) — CONFIRMED [OWN.21]; [R14.s3] the reset applies with `excl = true` too (cat's `po-loc-no-w`
  counts the SC/AMO write; `MState.store` is ONE function, `excl` a parameter — NO `excl` case split), and with `excl
  && acq` the floor already moves to `top + 1` (`Lang.lean:150`), so the reset there is harmless but still performed
  (uniformity with the shadow's store effect); (2) the FOREIGN-ONLY stamp — `HRead.afterLoad` stamps `coh a := max (coh a)
  t_a` for FOREIGN-sourced bytes only (`e.tid ≠ hartAgent cpu`), own-sourced bytes unstamped — RULED [OWN.23],
  LOAD-BEARING for (9d) (§B(10): without it the `m0`/`w_c'` candidate has no TsoMem realization and `hullRun` fails; the
  fallback, had the owner declined, was a W8 transported census of that shape, M, **unverified** — MOOT).  [R12.s3]
  `MState.afterLoad`'s SIGNATURE is unchanged (`Lang.lean:127-129`: it has `σ.mem` in hand and computes each byte's
  source author/timestamp via `Hist.read`'s `find?`); only `HRead.afterLoad` (`TsoMem.lean:268-270`) gains the per-byte
  stamp input.  [R13.s3] `Hist.read` returns the VALUE only (`TsoMem.lean:119-120`, `.map HEnt.v`); the foreign-only
  stamp needs the ENTRY (`HEnt.tid`, `HEnt.t`) — add `Hist.readEnt` (the same `find?`, entry returned) beside it and
  have `MState.afterLoad` build the per-byte `List (Option (Agent × Nat))` it hands to the new `HRead.afterLoad`; name
  that input so W5b′'s `tsoShadow` mirrors it from the pf log (`wmTid`, position + 1; `WeakMem.lean:106-111`).  So the four `afterLoad`-only files (`Wp`, `WpAtomic`, `WpSmodeFenceFloor`, `UIcache`) re-prove only
  where they UNFOLD it; no Iris resource exposes `coh` (`hartViewsAt` carries `tv`/`itv`/`rv`, `memModelAt` = top,
  authors, views, `resvMap`, `mmOk`; `Resources.lean:938-951`).  Files: the 7 of §D G2-Q plus the
  store rules' `clearAcq`/`resvMap_upd` sites (`Wp.lean:1337,1363`, `WpAtomic.lean:188,202`, `mmOk_store`
  `Resources.lean:824-840` — `HRead.bound`'s `coh a ≤ L`, `TsoMem.lean:280`, holds trivially at `0`); `relaxed-rr.md`'s
  CoRR gloss and `TsoMem.lean:20-24`'s header text updated.  **+ `Weak/TsoOfPf.lean` (MERGED, `Weak.lean:624`)
  [R14.1]**: `tsoAfterLoadCoh :171-173` unfolds `HRead.afterLoad` (`simp only [HRead.afterLoad]`) and STATES the old
  semantics (every footprint byte stamped `tvn` — exactly what (a′) makes false): ill-typed under the new arity —
  re-state it for the new `afterLoad` (foreign-stamped byte ↦ its source position; own-sourced byte ↦ unchanged),
  NAMING the per-byte input that W5b′'s `tsoShadow` mirrors ([R13.s3]) so the two agree; replace the G2 docstrings
  `:14-16`, `:212-214` (`g2Tso :215-225` itself is over `Hist.read`/`histOf` and survives).  **+ the `Vtest` lib**
  (found verifying [R14.1]; `lakefile.toml:43-49`, NOT a default target, `tools/ci/vtest.sh check`): `vtest-lean/
  Vtest/XState.lean:234-241` `afterLoadHR`/`afterLoadHR_eq` (`unfold … HRead.afterLoad`), `:251-256` `abs_afterLoad`,
  `:283-292` `XState.store`'s `hr := clearAcq`/`abs_store` — the computable twins gain the per-byte input and the
  reset; `HartExec.lean:242-244,328` call them (`cohOkB :56-61` unchanged if `cohOk` keeps its type).  Neither lane
  is in the Xv6/MachCSL CI build (`audit.sh:13-16`), so a worker building the `Xv6` cone per §B(12) sees GREEN while
  `Weak.lean:624`/`Vtest.lean` go red: **the brief's acceptance REQUIRES `lake build Weak.TsoOfPf Vtest`** (or the
  `--weak` lane + `vtest.sh check`).  **Acceptance** [R14.1][R14.s4] — three NAMED `decide`/`simp` facts over `histOf`
  in `TsoOfPf.lean` (S): (i) the restated `tsoAfterLoadCoh`; (ii) `g2TsoSched` — `g2Run` HAS a TsoMem schedule under
  the new `afterLoad` (the second load at `tvn = 0` reading byte `c = 0`); (iii) §B(10)'s own-store counterexample
  realized (`m0`/`w_c'`: byte `c` reads `w_c`); plus `lake build Weak.TsoOfPf Vtest` green.
  **W-RSV — D19 RULED (b) [OWN.19]; FORM (i-a) RULED [OWN.22][OWN.23]: reservations are CLEARED at the instruction
  boundary and the hart's fragment is THREADED through the cycle rules (L–XL, one `Xv6`-cone rebuild [R12.1]).**
  Rev 14's `inflight`-flag text was INCONSISTENT [R11.2]: dropping `blockedStep`'s store arm while `evStep`'s store/
  exclusive-read arms keep `¬ othersReserve` (`Lang.lean:368-378`; `hartStep` has no third arm, `:500-505`) leaves a
  foreign hart whose store overlaps an in-flight AMO with NO transition (stuck, `Reducible` fails); dropping the
  `evStep` guard instead un-atomizes the lock's `amoswap.w.aq` (`KernelImage.lean:2265-2270`).  **Semantics (form (i-a),
  W-RSV-Q §D)**: `hartStep`'s `.pure` arm (`Lang.lean:500-502`, today `σ' = σ`) becomes `σ' = σ.dropResv cpu` — what
  the pf twin already does (`pnodeStep`'s `LInstr`, `WeakEvInst.lean:284-288`; `instrPost … wRes := none`,
  `WeakMem.lean:720-721`); the `evStep` guards, BOTH `blockedStep` arms (`:395-403`) and the DMA `¬ anyReserve` guard/
  `devBlocked` arm (`:539,548-553`) ALL STAY, ranging over IN-FLIGHT reservations by invariant (none outlives its
  instruction) — no `inflight` flag, no invalidation rule; `Resv := Mem` (`TsoMem.lean:208`) and `ResvVal` keep their
  types.  A reservation-less SC is a PLAIN store with success by the opaque — TODAY's semantics, no new weakening
  ([R11.2] (ii); §0 F1 (ii)).  **Ghost side [R12.1]** (rev 15's "re-stated over `ctxTok`" was WRONG): the `.pure` step now changes `σ.resv cpu`, so
  `memModelAt`'s `E.resvName ↪●MAP resvMap σ` (`Resources.lean:949`; `resvMap_get? :611-612` = `(σ.resv c, acq)`) must
  be updated with the hart's EXCLUSIVE fragment in hand — `resvMap_congr :621` no longer applies; the ghost lemma
  ALREADY EXISTS: `memModel_dropResv` (`WpAtomic.lean:49-51`: `memModelAt E σ ∗ resvFragAt E cpu r b ⊢ |==> memModelAt E
  (σ.dropResv cpu) ∗ resvFragAt E cpu none b`).  But `wpLoop_restart` (`Wp.lean:385-400`, resource-free) is applied
  BARE — `iapply wpLoop_restart; iintro %tick` — inside the cycle rules (`WpCycle.lean:110,172`, `WpSmodeCycleB32.lean:
  42`, `WpSmodeCycleRvc.lean:41`, `WpSmodeCycleT.lean:87,154`, `WpSmodeWait.lean:98,176`, `UCycleSwp.lean:367`), whose
  premises are `mConf/confCells ∗ clockCells ∗ pcIs ∗ (transTok) ∗ R ∗ P` (`WpCycle.lean:96-105`, `WpSmodeCycleB32.lean:
  24-36`) and name NEITHER `ctxTok`, `kctx`, `ownCtx` nor `resvFrag` (grep: 0 in the four `WpCycle`/`WpSmodeCycle*`
  files; `UCycleSwp.lean:31` a comment); the fragment rides ONE LAYER UP — in `kctx` as `ctxToken` (`Ctx.lean:29-30`;
  `KCtx.lean:415,849,939`) and in user mode inside the walker frames as `uResvTok cpu rv := ∃ r, resvFragAny cpu r`
  (`URunRW.lean:501-502`, ≈ 30 mentions).  Two forms, both FAITHFUL (CSL plumbing, no semantics): **(i-a) RULED
  [OWN.23]** — every cycle rule gains a `resvFragAny cpu r` premise and a `resvFrag cpu none b` post: 16 rules in 9 files
  [R13.s1] (`wpLoop_m_base/_rvc/_instrClk/_instrP/_instr` `WpCycle.lean:96,157,282,321,332`; `wpLoop_s_base/_rvc`
  `WpSmodeCycleB32/Rvc`; `wpLoop_s_instr` `WpSmodeCycle.lean:29`; `wpLoop_s_instr_clk` `WpSmodeTime.lean:54`;
  `wpLoop_sT_base/_rvc` `WpSmodeCycleT`; `wpLoop_sT_instr` `WpSmodeSatpU.lean:280`; `wpLoop_wait_wfi/_s_wfi_cycle`
  `WpSmodeWait`; `wpLoop_ucStep/_uwStep` `UCycleSwp`); [R13.s2] the S-mode rules have TWO continuations (`▷ (… -∗ wpLoop
  cpu) ∧ trapBranch cpu c tier root sie pc P`, `WpSmodeCycleB32.lean:33-36`; `trapBranch` `WpSmodeCycleBase.lean:77`),
  so the `resvFrag cpu none b` post is delivered on BOTH arms (the trap handler re-forms `ctxToken cpu` on the same
  hart) — and EVERY caller supplies it — measured [R13.1], BY LANE: **25 MachCSL files** mention a cycle rule (20 apply
  one directly: `WpSmodeCycle.lean:49,65`, `WpSmodeRules`, `WpSmodeIntr`, `WpSmodeKpt`, `WpSmodeProc`, `WpSmodeSret`,
  `WpSmodeSwtch`, `WpSmodeTime`, `WpSmodeTrapCsr`, `WpStore.lean:201,223` (`ctxTok` in scope), `WpLockSchema`,
  `WpSmodeLwKey`, the five `WpMmode*` …; R12 counted ≈ 27).  (S-mode KERNEL lane) the schema wrappers `wpLoop_k_*`
  (`WpSmodeRules.lean:52-60`, premise `kctxL lent cpu k`; `kctxP` holds `ctxToken cpu` for EITHER `lent`, `KCtx.lean:
  839-850,925,931-952`; `ctxToken = ctxTok cpu curCtx :415` = `ownCtxAt ∗ ∃ r, resvFragAnyAt E cpu r`, `Ctx.lean:
  298-299`) ABSORB the fragment inside their proofs — their statements and the `Xv6` cone above them (3 `wpLoop_k_*`
  sites) stay.  (USER lane) `uFr` ∋ the walker `ctxTok` = `ownCtx ∗ uResvTok` (`UCycleSwp.lean:31-33`, `URunRW.lean:
  501-502`) absorbs it likewise.  (M-MODE lane — MISSED by rev 16) the five `wpLoop_m_*` rules are stated over `mConf
  cpu dq c ∗ clockCells cpu ∗ pcIs cpu pc ∗ R ∗ P` with NO bundle (`WpCycle.lean:103-105`), and the **35 `wp_m_*`
  wrappers** that apply them (`WpMmode.lean` 8, `WpMmodeAlu` 9, `WpMmodeCsr` 16, `WpMmodeCtl` 1, `WpMmodeMret` 1; 5 of
  the 25 files; `grep -c "ctxTok\|resvFrag\|kctx"` = 0 in four, and in `WpMmode.lean` only `wp_m_ld_same` threads
  `ctxTok cpu curCtx`, `:229-231,388-391` — [R13.s4] the TEMPLATE if a token is preferred to a bare fragment in M-mode)
  have NOTHING to absorb it into: **34 statements gain `resvFragAny cpu r`/`resvFrag cpu none b` (or a new M-mode
  token)**.  **`Xv6/` cost: 12 files** — the **8 that apply a cycle rule DIRECTLY**: `ProofSpin.lean:43`
  (`wpLoop_m_instr`), `UserretPt.lean:52,130,177`, `UserretEntryPt.lean:63,113`, `UservecPt.lean:55,129,212`,
  `UservecExitPt.lean:90,121,164,198` (`wpLoop_sT_instr`), `UserStepActive.lean:124`, `UkEngine.lean:178`
  (`wpLoop_ucStep`), `UserStepWait.lean:34` (`wpLoop_uwStep`) — the fragment IS available at each (the trampoline files
  frame `ctxTok cpu curCtx`, `UserretEntryPt.lean:164` frames `∃ r, resvFragAny cpu r` across `fence.i`; `kctx_cases`
  yields `Htok`, `WpSmodeWait.lean:257`; `UkEngine.lean:125` extracts `ctxToken` from `Rut`); PLUS the `wp_m_*` callers
  **`ProofEntry` (8 applications), `ProofStart` (39), `ProofTimerinit` (21)** — re-threaded at the PROOF level only,
  their spec bodies already carry `ctxTok cpu curCtx` (`SpecEntry.lean:48`, `SpecStart.lean:62`, `SpecTimerinit.lean:
  56`); PLUS **`SpecSpin.lean:34-42`'s `wp_spin_body`/`SPIN`** and `ProofSpin.lean:32-55`'s `wp_m_j`/`spin_loop`, which
  hold NO token — a STATEMENT change, isolated (`SPIN.wp_spin`'s only consumer is `LinkSpin.lean:14`; `ProofBoot.lean:
  27`/`SpecBoot.lean:75` use only the address `KA.«spin»`).  Mechanical but WIDE, L–XL (size class UNCHANGED by the
  M-mode lane), one `Xv6`-cone rebuild.  **(i-b)** (recorded, not ruled) —
  move the per-hart `∃ r, resvFragAny cpu r` out of `ctxTok`/`uResvTok` into a per-hart INVARIANT opened by the boundary
  rule and by the three rules that consume the fragment explicitly (`swp_sail_mem_write_plain_au` `WpAtomic.lean:
  538-544`, `swp_sail_mem_read_excl_au :698-704`, `swp_sail_mem_write_excl_au :711-717`): the cycle rules stay, but
  `ctxTokAt` (`Ctx.lean:298-299`, 19 sites), `KCtx`'s `ctxToken`, `URunRW`'s `uResvTok` and every `ctxTok_cases/_intro`
  user change — M–L, a context-token REDESIGN; the cycle rules, the 35 `wp_m_*`, `wpLoop_k_*` and ALL of `Xv6/` stay
  as they are, so (i-b)'s relative advantage GREW with [R13.1] (recorded for the owner, §D W-RSV-Q).  Form (ii) (the `inflight` flag) has the SAME ghost problem unless the
  flag is kept OUT of `ResvVal` — and then the exclusive-store rule cannot learn "in-flight" from a resource (`mmOk`'s
  clause "every reservation agrees with the top", `Resources.lean:781-782`, must weaken to in-flight reservations, and
  `memModel_store_excl :221-224` needs that fact) — so (ii) is NOT an escape hatch.  Devices are untouched by
  `dropResv`: `ObsTrace.hartStep_wire/_recvd` (`ObsTrace.lean:503,538`) and `DiskOf.hartStep_diskOf :134-136` are trivial.  **Census of blocking consumers** (21 MachCSL files [R11.s3] + `Weak/WeakLang.lean:52`, the
  pf twin that already DROPS the DMA guard — the precedent for the direction): `blockedStep` — `Wp.lean` 8 (the generic
  step rule's blocked disjunct and self-loop continuation `:495-497,536-538`, the `hnb` variants `:552`), `Lang` 4,
  `ObsTrace.lean:512,547`, `DecodeBridge.lean:86,147`, `DiskOf.lean:157`; `othersReserve` — `WpAtomic` 8, `Lang` 4,
  `WpSmodeDev.lean:75-76,160`, `Wp.lean:1344,1589,1800`, `Resources.lean:754-757,825`, `WpStoreOrd.lean:73,85`,
  `WpPtWalkOwn.lean:134,227`; `anyReserve` — `WpDma` 3, `WpDev` 1, `Resources` 1; `dropResv` — `WpAtomic` 9; `resvMap`
  — `Resources` 29, `WpAtomic` 8, `Wp` 8, `Power`/`PowerText` 3+3, `WpSmodeFenceFloor` 2, `WpDma` 1; `snapOf` —
  `WpAtomic` 11, `WpPtWalk` 7 / `WpPtWalkOwn` 6 / `WpSmodeAu` 2 / `WpSmodeAtomic` 1 — the Svadu A/D LR/SC pair
  (`exclReadAU … snapOf pa 8`, `WpPtWalk.lean:84,111,135,161`) is issued INSIDE one memory instruction's translation,
  hence IN-FLIGHT for its whole window: rev 14's "reservation-still-valid premise or retry" risk is WITHDRAWN, the
  re-proof mechanical [R11.2] (iii); `valid_reservation` — `UWait.lean:21-26`, `SailHooks.lean:5,14,26` (the opaque
  stays, no change); `MachGS.resvName` (`Resources.lean:122,433,475`; constructed by `Xv6/AppUnionPre.lean:89`,
  `Xv6/AppPreGS.lean:54`) UNCHANGED under form (i-a) (touched under (ii), whose `ResvVal` changes).  The bulk: `Wp`/`WpAtomic` re-proved
  against the invariant "reservations are in-flight", PLUS the (i-a) thread through 16 cycle-rule statements and their
  25 MachCSL files (35 `wp_m_*` statements among them) + 12 `Xv6/` files [R12.1][R13.1].
  **Interaction with W2** (§B(10)): the `LStore`/`DWrite` rows get `¬ othersReserve`/`¬ anyReserve` from `pairAdjacent`
  ALONE (no in-flight foreign reservation can straddle a step); `LExStore` needs nothing of the own reservation
  (TsoMem never reads it [R11.2] (i)); the [R2.3-alt] failure mode (a STANDALONE `LExLoad`'s dangling reservation
  blocking a foreign store) DISAPPEARS.  **Does the fused-pair restriction remain needed?**  For FAILING SCs, YES (the
  pf retry self-loop `WeakEvInst.lean:360-364` has no TsoMem twin — TsoMem's lost-reservation store is a plain store;
  an SC-failure row is M, not planned); for DANGLING LRs, NO once W-RSV lands: clause (i) of `execProgOk'S` (`lbFused`
  on the left arm) can be RELAXED to admit a standalone `LExLoad` realized as `LLoad` (`lbNobarex`, `projLbl :541`) —
  TsoMem's exclusive read takes `topBytes` = the pf's `lat` read, `afterExcl`'s `rv := top` is the shadow's (G1′) — a
  quantifier WIDENING, OPTIONAL follow-up (S–M: one W2 row + the clause).  [R12.s2] Under the widening a dangling
  `lr.aq` leaves `hr.acq = true` until the hart's next store (`clearAcq`), and an EXCLUSIVE next store would take `tv :=
  top+1` (`Lang.lean:150`, guard `excl && acq`) — a floor at the hart's OWN store position that cat does not give (no
  `W;po;R` ppo); so the boundary rule also clears `hr.acq` (same rule; `resvMap` carries the bit, `resvMap_get?`), or
  the widening relies on `pairAdjacent` pairing every later `LExStore` with its own `LExLoad`.  After landing: §0 F1 (ii) is removed from
  the strengthenings list, the "Honestly" line and §B(11)'s internal list drop "reservation serialisation", D19's mark
  is FAITHFUL for AMOs / WEAKER for user LR/SC (as today); acceptance also updates `TsoMem.lean:27-31`'s header text
  ("blocked … while a hart holds a reservation" → "within the issuing instruction") [R11.s2].  Deps: W-COH landed, then
  W4/M1 (D26 — W-RSV follows M1 so its `Xv6`-cone rebuild does not sit on W4's path); W4 re-checks three rows after it
  (S).  Critical path [R12.1]: W-RSV is the LONGEST serial MachCSL item; it gates M2 (W5d) only through the W4
  re-check, and Stage 2's graph lane (W12/W12b/W5d-G/W13) runs beside it.

**Stage 1b — M2, the fork path on the pf side (part of the target [OWN.3]).**
- **W5d `Weak/PfRunUnpinned.lean`** (L) [R2.1-alt][R3.1][OWN.3][R4.2][R6.4b].  The pf half ONLY: `execWfPfRunProgF`
  (replay at `pstepEv` with the CUT-form clause `∃ q, itv ≤ q ≤ |log| ∧ ifetchOk img log q base tvs` replacing
  `fetchPin`; W5b's replay carries a `pstepPinned` hypothesis — the M2 replay instantiates `fok` with the cut form and
  DROPS the pin; [W2s] the cut form adds `t ≤ q` per byte; **[R11.3] its `itv` is W5d's `itvOf` (§B(4)(iii) (ii):
  per-row, per-step, driven by the realizing `LFence false×4` label with `ls` only telling `fence.i` from the marker,
  frame condition on the other rows [R12.s1]; `fok`'s 6th argument; S inside this L)**), W4's `LIFetch`
  row for user text at `tvn := q ≥ itvOf`, W5 restated — the first form in which `fork → ecall →
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
- **W5d-G `Weak/GraphFetch*.lean`** (L ≈ 1.8–2.2k + S–M re-creation + XL risk R1; D27 RULED (a) [OWN.6]; D42–D43
  RULED (a) [OWN.18]) [R4.2][R6.4b].  **G0 — Day one [R10.4][OWN.18]: RE-CREATE the spike file from
  `notes/W5dG-spike.md` (the Lean is UNRECOVERABLE; the report records every statement and the proof sketches —
  `fetchCutOk`, `fetchCutPrefix`, `fetchCutEdge`, `fetchRelOk`, `fetchRelCut`, `fetchPinCutOk` proved; `gzFetch`,
  `gzFetchCut`, `emZifencei`, `gfcut`, `gwlog` stated), S–M, acceptance: builds with `propext, Quot.sound` and each
  statement matches the report's text.**  Then, AFTER W13 (M) (D26; Q-W5dG-seq RULED (a) [OWN.24][R14.3] — G1/G3/G5
  edit `Fab`/`Supply`/`Acyc`/`Glue`/`Hull`/`Topo`, the files W13 (I)/(K)/(M) rewrite), the spike's change list: **G1** `gzContrib`,
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
  `dstep :493-495`, `dstepT` (`AxDeps.lean:461-463`) get the (F-dep) arms below, not inert ones (D50 (b)); `elabOk :547` (`True`), `elabWs :571` (view
  unchanged), `wpPfStep.PFDev` (`WeakPromiseBridge.lean:392-396`, payload only); exhaustive `Lbl` matches in 41 chain
  files + 30 `Ax*` files (the `| LFence` arm census; the retired tier must still build), `Wlabel.LDev` constructor arms
  in **~35 files** (34 by arm-regex, 50 files mention the name — the `WeakRobust*` family, `AxFetch1/3`, `AxLock3*`,
  `AxRunGV2` included) [R8.4] — one-line arms, mechanical.  **(M) the model** (M–L): `gmem := lbIsMem || lbIsIo` so
  I/O events are in gmo; every "a `gmem` event is a read or a write" case split in the chain gets an I/O case
  (`lbIsMem` unfolded in 39 files, `gmem` named in 22 chain files — measured, proof impact **unverified**);
  `rvwmoCatConsistentT`'s TEXT unchanged; `gdexecQconfT`/`xv6ConfS` gain `gisIo (i,k) ↔ (i,k) ∈ gfDev`; `emDevfree`
  (`Supply.lean:273`) retires.  **(T)** `ioResidue`/`ioResidueGmo`/`gfBefore` + header text, **+ the (R2′) arm [W2s]
  (G3-Q RULED (a″) [OWN.17])** (S); acceptance: `ioResidueNodev` and the re-encoded `w13f` (§A(†)).  **(I) realization** (M–L): `execProgOk'` UNCHANGED — the I/O
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
  section" (S–M); `normalizeOfAcyclic` over `racyDIO` keeps I/O positions (its topo order ⊇ gmo|IO) **and the
  disk-read anchors (G3-Q RULED (a″); one more `racyDIO` disjunct, S–M) [W2s]**; `gdHull` keeps
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
  `freerange` — shares D44's infeasibility, so W14 covers it).  **(F-dep) — IN SCOPE, D50 RULED (b) [OWN.17] (M;
  owner files `Weak/AxDeps.lean` + `Weak/WeakRvwmoConf.lean` + `Weak/WeakEvInst.lean`; after (E))**: (1) the `LDev`/
  `LIo` payload gains `asrc` (rd) / `asrc vsrc` (wr), filled by `pnodeStep`'s MMIO arms (`WeakEvInst.lean:300-304,
  335-338`): **`LIo rd`'s `asrc := depsAsrc (depsOfIb ib.ibBits)` as the `LExLoad` arm does (`:329-331`), NOT as the
  plain `LLoad` arm, whose `asrc` is D-8's `[]` (`:323`; `AxDeps.lean:405-406`; `WeakAxiomatic3.lean:2065-2067` "rule 9
  (LOAD half) OMITTED BECAUSE OF D-8") — a worker mirroring `LLoad` would emit NO addr→I/O-load edge, i.e. D50 (a)
  [R11.4]; `LIo wr`'s `asrc/vsrc` as the `LStore` arm (`:344-355`)**; `oib` stays `none` ("`ib` unchanged" [R11.s1]);
  the I/O item is already tagged `(l, some k)` (§A(†)); (2) `dstepT`/`dstep` arms: `LIo rd` = the `LLoad`/`LExLoad` arm
  SHAPE (`dedgesR` `AxDeps.lean:445`: ADDR edges in, `k :: dtLd` provenance OUT, `dtAcc` for rule 13, NO ctrl — exactly
  "no ctrl → I/O load"), `LIo wr` = the `LStore` arm shape (`dedgesW :448`: addr/data/ctrl/trans/r13/ctx in); `dev`-kind
  items stay inert; (3) **the I/O-load edges are the FIRST load-half `DTaddr` edges the emission produces** [R11.4]:
  RAM loads stay D-8-masked (rule 9's RAM load half remains omitted — a faithful ADDITION, not a D-8 unmasking);
  `lbLdepfree`/`pstepEvLdepfree` constrain `LLoad` ONLY (`WeakPromise.lean:112-115`), so an `LIo rd` with sources does
  not falsify `wpPfStepInv`/`pstepEvLatFreeHalf`/`pstepEvLatFreeProg`/`pstepEvTsOblivious` (`WeakEvCapstone.lean:238,
  714,1048,1058`); `rowDepsTAddr` (C) already admits `DTaddr` edges into pure READ items (`AxDeps.lean:702-707`);
  **proofs re-opened**: `rowDepsSubT`/`rowDepsTSub` (`AxDeps.lean:690ff`, the tree/tagged correspondence),
  `dstepTState`, the pin bridge `pinSegPin`/`pinSegPin'`/`checkerTaintSubProv` (`PinBridge.lean` 21 sites,
  `PinBridge2.lean` 11) — DIRECTION [R11.4]: `pinSegPin` consumes "`rowDeps` ⊆ `gdDeps`" and proves checker `PDep` ⇒
  edge (`PinBridge.lean:312-316`), `checkerTaintSubProv` proves checker taint ⊆ provenance (`PinBridge2.lean:518-521`)
  — both PRESERVED when `rowDeps`/provenance GROW, so `gen_weak_pins.py` need not tag MMIO reads unless xv6 pins are
  to USE MMIO-sourced dependencies (none expected; rev 14's "or state the correspondence for RAM items only" was the
  wrong dichotomy), `WeakRvwmoSupply` 4, `FabInd` 2,
  the witness files (`ConfWit2` 3, `CycWit` 4, `Adm` 5 — `LDev`-free rows, trivial), the retired `Ax*` tier (`AxGate`
  30, `AxScRun` 28, `AxScCat` 33, `AxFetch5` 8 — new arms only, must build); `gdexecQconfT`'s trusted-surface TEXT now
  covers I/O items (name it, §A(6)).  **Coverage check against (R1)/(R3)** (§A(†)): in-edges from RAM accesses ⊆ (R1),
  from I/O loads ⊆ (R3); out-edges into RAM STORES ⊆ (R2); the one class beyond the residue is I/O-load →addr→ RAM
  LOAD (rule 9) — expected absent in xv6 (**unverified** census; a hit would be a graph-tier PIN, never a STOP).  So
  (F-dep) changes the trusted PROSE (the (F3) uses move to the graph tier) and the published quantifier at most by
  that class.  **(F-fence)/(F-trap)**: OUT, prose only (D46 RULED (a)).  Risks: **R2′** the alphabet sweep touches ~70 files including the retired `Ax*` tier (mechanical, one
  build); **R5** an I/O-ENTRY / READ-EXIT segment (I/O event →po→ racy read →fr→) has NO fence pin (rule 4 skips I/O)
  and must close by lock discipline or (R2)-rerouting through the release — an unlocked one is a STOP (candidates: the
  PLIC claim/complete races, `plicinithart`, `pr.locking`/`panicked`; R8: real, honestly a STOP); **R6** the `gmem`
  case splits of (M).  Deps: W5c's `esilAdmRun` ✓; W5b's shape clauses ✓; `AxDevGraph.lean` (`Dlbl :134-142`, `dstep
  :152`, `DevConsistent :226-236`) as the device-step precedent for the `dev`-kind replay (its separate-row encoding is NOT what [OWN.14] rules).
- **W14 `Weak/ExistWitness.lean`** (NEW; D44 RULED (i) [OWN.11]; L–XL — the spike's table confirms the SC run
  satisfies `candScaT`/`candDiskLat` trivially, every load at the top [W2s], and the corrected (a′) likewise: stamps
  ≤ top, resets harmless [R11.s5]): the single-execution EXISTENCE theorem — ONE device-active TsoMem-side run (a `-<κs>->ₜₚ^[n]` run from
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
  user-table walks, boot-published globals).  Exports hold on FORWARDING graphs.  **Design gate — G2-Q only [W2s]
  [R10.1][R10.2] — RESOLVED by G2-Q (a′) [OWN.20][OWN.23]** [R4.s5][R6.4a]: (★) is NOT a W8 export under any option
  (discharged by `candScaT`, §B(10)); under the RULED (a′) W8 owes (i)–(v) only.  Recorded: under (b) W8 would have
  gained **(vi) the MIXED-SIZE census** (po-ordered OVERLAPPING loads of DIFFERENT footprints on a concurrently
  written byte; expected vacuous, **unverified**) feeding W11 (iv) through `R`'s log identification — MOOT.  Deps: W2's `R`.
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
  (iv) `linCandSca` (S) [R4.4] **+ `linCandScaT`/`linCandDiskLat` [W2s][R10.2]**: the §B(10) derivations — the SCA
  witness is the load's gmo position, ≥ the pair's position by rule 5/4 and the gmo|W log order (`ptraceRel`); the
  `coh` part GRAPH-ONLY under the RULED (a′) [OWN.20][OWN.23][R11.1] — the THREE-case induction of §B(10) (same source /
  different source ⇒ rule 2 with `po-loc-no-w` / own write po-between ⇒ reset), foreign-source stamps only; M
  (recorded: (a‴) vanishes S–M [R10.s4]; (b) a TRANSPORTED hypothesis, MOOT); disk-row loads latest from the (L)
  anchors.  Deps gain: W-COH.  (v) Restate `cycleKillOfL2''` (`Glue2.lean:521`), `t2linOfL2'''` (`Walk3.lean:77`),
  `xv6RvwmoSafeModuloT` (W12) with W8-sourced facts replacing `wpPackage`/`wpPackageProt`/`noBadRun`/`protRegOfRun`/
  `efetchItvOk`; compose with M2, W5d-G, W13 (`gfexecConfIO`, `ioResidueGmo`, T2-1c″, `cycleKillIO`): **T-alloc-RVWMO**.  Header per §B(11).
- *Not on the path:* **W6** PSO machine (L–XL; optional de-risk, D4); **W7-P** promise-machine fallback (D2').

**Stage 3 — AxSL tier: retired** [OWN.1].  One-paragraph note on Theorem 2 (D6).

**Status of the launch [W2s][OWN.16–19][R10]:** W3, W5b, W5c DONE; W1 interim DONE (W1-Q RULED (c) → W1b); W2 spike
DONE with D7 STOP.  **Now launchable** (the Stage-1 launch set, §C top [R13.2]): W5b′ (`Weak/TsoShadow.lean`,
shadow-threaded [R10.3]) → W2 (the parametric table and the instance-independent rows now — exload, NOT exstore
[R14.2]; the hart `LLoad`/`LStore`/`LExStore` post-states after W-COH; G1-Q/G3-Q RULED) ∥ W1b (RULED-in [OWN.16] (c),
owner schedule, D10) ∥ W13 (E) (D47–D52 ALL RULED) then (T) (G3-Q RULED) ∥ W5d-G G0 ONLY (re-creation; G1–G5 after
W13 (M) per D26 — Q-W5dG-seq RULED (a) [OWN.24][R14.3]; D41–D43 RULED) ∥ **W-COH (G2-Q RULED (a′), BOTH components
[OWN.20][OWN.21][OWN.23] — LAUNCHABLE NOW, no gate [R12.2]; serial MachCSL; brief builds `Weak.TsoOfPf` + `Vtest` [R14.1])**.  **Blocked on W-COH landing**: W4 (the
shadow's INSTANCE), hence W5/M1, W5d/M2.  Resolved by [OWN.20][OWN.23]: W8's gate ((i)–(v) only), W11 (iv)'s form
(graph-only).  **Serial MachCSL after W-COH → W4 → M1**: W-RSV (D19 (b), form (i-a) RULED [OWN.22][OWN.23]; L–XL, the
LARGER serial item, one `Xv6`-cone rebuild; 12 `Xv6/` files incl. the M-mode lane [R12.1][R13.1]) — it waits for
W-COH (shared files) and for M1 (D26) [R13.s5], not for an owner.  The
published statement's shape is FIXED (D32, D33, D37, D38, D44–D52 RULED [OWN.11–18]).  W13 (F-dep) after (E).  No owner
question is OPEN (§D).

## D. Owner questions (recommended first; RULED items kept, tightened — [R7.s1]'s appendix NOT adopted: this file only)
**FIXED: D32, D33, D37, D38, D44, D45 RULED.  G2-Q RULED (a′) with BOTH components — the reset CONFIRMED [OWN.21], the
foreign-only stamp RULED [OWN.23] (first below).  W-RSV-Q RULED (i-a) [OWN.22][OWN.23]; D19 (b) stands; Q-W5dG-seq
(R14, after D26 below) RULED (a) on arrival [OWN.24].  **OPEN: NONE —
no owner question remains open since rev 16 [R12.2]**; the "Standing" D-items below are provisional recommendations kept
at the owner's instruction ("keep the recommendations as provisional"), not questions awaiting a ruling.  RULED by [OWN.17]: G1-Q (e), G3-Q (a″), D46
(a), D47–D49 (a), D50 (b); by [OWN.18]: D42–D43 (a), D51–D52 (a); by [OWN.19]: D19 (b), D20 (a), D9 (a), D8 (a); by
[OWN.16]: W1-Q (c), Q-W3a (A), D41 (a), D45 (a).**
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
- **G2-Q — RULED (a′) with BOTH components, CLOSED [OWN.20][OWN.21][OWN.23]: the own-store footprint `coh` RESET
  ([R11.1], CONFIRMED [OWN.21]) AND the FOREIGN-authored-source-only stamp ([R11.1-alt], RULED [OWN.23], load-bearing
  for (9d)). Footprint coherence stamps (G2): which `coh` stamp does TsoMem (and the shadow) use?**  History: [OWN.17]
  "(a)" predated [R10.1]; [OWN.20] "(a′) as worded in rev 14" predated [R11.1], which showed that wording STRONGER than
  riscv.cat; [OWN.21] confirmed the RESET only; [OWN.23] ruled the foreign-only component after R12 showed it
  LOAD-BEARING [R12.2].  **Spec** [R11.s4]: RVWMO
  rules 1–3 / riscv.cat rule 2 `([R];po-loc-no-w;[R]) \ rsw` (`gppo2`, `AxGraphCat.lean:151-156`) orders two same-hart
  reads of a common BYTE only when they return DIFFERENT writes AND **`po-loc-no-w`: no write to that byte, by ANY
  instruction of the hart, lies po-between** (`gppo2`'s conjunct `∀ w v, gwritesByte G w a v → gpo e1 w → gpo w e2 →
  False`) — per byte, nothing across a footprint; rule 1 orders a read before a po-later same-byte WRITE (`gppo1
  :146-147`, `M;po-loc;W`); load-value makes a hart's own po-earlier store visible at ANY gmo position (`gvisible`,
  `Graph.lean:236`: `gmoLt ∨ gpo`), so there is NO `W;po-loc;R` ppo and an own store carries no gmo constraint for a
  later same-source read — store-buffer forwarding is legal; "Memory Model Primitives": a misaligned access is a set of
  byte operations (N10 out of scope); Sail: `mem_read` per access, no coherence state (external); Zifencei/PMAs: silent.
  **TsoMem today** (§0 F1 (iii), three components): stamps the WHOLE footprint with `tvn` (`HRead.afterLoad`,
  `TsoMem.lean:268`; `cohOk :263` footprint-WIDE, checked at `Lang.lean:365`); the stamp SURVIVES the hart's own store
  (`MState.store` touches `hr` only by `clearAcq`, `Lang.lean:152`); own-sourced bytes are stamped (own stores are
  visible at any view, `HEnt.visible :115-116`) — STRONGER than rule 2 (`g2Tso`).  **Options** (recommended first):
  **(a′) CORRECTED — MachCSL: `afterLoad` stamps `coh a := max (coh a) t_a` for FOREIGN-sourced bytes only
  (`e.tid ≠ hartAgent cpu`), own-sourced bytes (forwarded OR below the view) UNSTAMPED, and `MState.store` RESETS
  `coh a := 0` on its footprint** — FAITHFUL: exactly rule 2 with BOTH exemptions (same source; `po-loc-no-w`) plus
  load-value's own-store visibility — the THREE-case derivation of §B(10), graph-only; the reset is per byte, so an own
  store to PART of a footprint exempts only those bytes (as `gppo2` does); keeps TsoMem's documented CoRR
  (`relaxed-rr.md`) for foreign-written bytes; cost [the spike's "re-opens `cohOk` users" corrected: `cohOk` has ONE
  use, `Lang.lean:365`]: `TsoMem.lean` (+ `HRead.resetCoh`), `Lang.lean:147-153,365-367`, `mmOk_afterLoad`/`mmOk_store`
  (`Resources.lean:788-840`), the load rules `Wp.lean:1257-1282,1729-1745`, `WpAtomic.lean:509-530`,
  `WpSmodeFenceFloor.lean:92-119,239-260`, `UIcache.lean:233-249`, the store rules' `clearAcq` sites (`Wp.lean:1337,
  1363`, `WpAtomic.lean:188,202`) — 7 MachCSL files, mechanical (NO Iris resource exposes `coh`; the `swp` statements
  the Xv6 cone consumes never mention it) **+ `Weak/TsoOfPf.lean` (`tsoAfterLoadCoh :171-173` restated, G2 docstrings
  `:14-16`, `:212-214`) and the `Vtest` twins (`XState.lean:234-256,283-292`) — both OUTSIDE the cone build, so the
  brief builds them explicitly [R14.1]** — S–M, SERIAL on MachCSL (W-COH); W11 (iv) graph-only (M).
  **(a′) RESET ONLY — the [OWN.21] state alone** — STRONGER: excludes §B(10)'s `m0`/`w_c'` candidate (cat-consistent,
  no TsoMem schedule), so (9d)'s hull realization has a HOLE unless a W8 TRANSPORTED census excludes the shape (M,
  **unverified**) — not taken [R12.2].
  **(a‴) MachCSL: DROP the coherence floor** (`afterLoad` = `rv := max rv tvn` only; `cohOk` and the `coh` field go) —
  WEAKER than rule 2 on the strong model (TsoMem then admits CoRR violations), SOUND for the composition (it needs
  only TsoMem ⊇ realized runs; no proof consumes `coh`), S, the same 7 files, deletions; `F = tv_S`, (★)'s `coh` part
  vanishes, W5b′ S and W11 (iv) S–M [R10.s4]; changes TsoMem's documented semantics — the smaller trusted surface.
  **Rev 14's (a′) — "stamp when `t_a ≤ tvn`, no reset"** — STRONGER, REJECTED [R11.1][R11.1-alt], two defects: (1) a
  per-byte CoRR floor that OUTLIVES the hart's own store (hart A `lb a` = `r_prev` from foreign `w`, `sb a` = `m`,
  `lh (a,b)` = `r` reading `a` from `m` and `b` from foreign `w_b`; hart B `w_b, w_b', w`; gmo `w_b <gmo r <gmo w_b'
  <gmo w <gmo r_prev <gmo m` is cat-consistent — rule 2 EXEMPT by `m`, rule 1 `r_prev <gmo m` ✓ — but `coh a = gwix w
  > gwix w_b'` makes TsoMem read `w_b'` for `b`; `candScaT` FALSE); (2) an own store BELOW the view is stamped at its
  position though a later same-source read may be gmo-before it (§B(10)'s `m0`/`w_c'` candidate).  **(a) as
  originally worded — "stamp each byte with ITS source timestamp"** — STRONGER, REJECTED [R10.1]: a forwarded byte's
  stamp `t_a > tvn` with footprint-wide `cohOk` forces every later OVERLAPPING load above it (hart A `sb j` = `w1`; `lh
  (j,m)` = `r1` from `w1`/foreign `w5` (gwix 10); `lh (j,k)` = `r` from `w1`/the image while foreign `w3` writes `k` at
  gwix 5; gmo `r <gmo w3 <gmo w5 <gmo r1 <gmo w1` cat-consistent; under (a) `r` is forced to view ≥ 10 and reads `w3`).
  **(b) keep TsoMem; W8 exports (vi)**: no po-ordered OVERLAPPING loads of DIFFERENT footprints on a concurrently
  written byte — FAITHFUL as a program fact (TsoMem stays STRONGER, all three components, named in F1); census M,
  **unverified**, a racy site is a STOP; W11 (iv) takes (vi) TRANSPORTED (+S–M) [R10.2]; no MachCSL change.  **(c)**
  strengthen `candSca` — NOT derivable (cat allows G2), rejected; **(d)** a footprint-coherence ppo rule in the
  published model — STRONGER than riscv.cat, violates [OWN.2], rejected.  RULED: (a′) with BOTH components [OWN.23];
  (a‴)'s smaller trusted surface recorded, not taken.
- **G1-Q — RULED (e) [OWN.17] [W2s]. The `.aq` floor debt (G1/G1′).**  Spec: RVWMO rule 5 / riscv.cat `[AQ];po` (`gacqPo`,
  `WeakRvwmoGraph.lean:214-215`): the acquire READ (the AMO's read half, `lbAq`) is ppo-before every po-later memory
  access of its hart; rule 4 covers the pair's read half for a later `fence r,*`; load-value: a later load's source is
  co-maximal among the writes gmo-before it — so the writes gmo-before the AMO ARE visible to the hart's later loads,
  and "floor = the AMO's gmo position" is what the chapter gives; NOTHING in the chapter ties a floor to the lock
  word's SOURCE timestamp (WeakMem's `max(wVrNew, t)`, `WeakMem.lean:608,834`) — the two coincide exactly when the
  log is gmo-ordered.  Sail: `execute_AMO` (`InstsEnd.lean:18663`) issues `mem_write_ea … aq`/`mem_read … aq`, the
  access kind carries the bit (`AS_rel_or_acq`, `PhysMemInterface.lean:315,364`), NO view semantics (the memory model
  is external).  Zifencei/PMAs: silent.  Options: (e) **`candScaT` — SCA at a view ≥ `tsoShadow`'s floor** (§B(10)) —
  FAITHFUL at Stage 2: DERIVED (`linCandScaT`, rule 5/4 + `ptraceRel ⊇ gmo|W`) given G2-Q (a′)/(a‴), or (b) + W8 (vi)
  transported [R10.2]; a PREMISE at M1/M2 only (restricts the candidate's log order to a gmo-extension); cost W5b′
  S–M + W11 (iv) M (S–M under (a‴)); re-opens nothing (RULED); (a) D7 (Rec):
  WeakMem's aq exclusive read takes TsoMem's view (`wVrNew := |log|`) — STRONGER pf machine; T1 `srvwmoRealizable`
  fails on G1-shaped candidates, so (9d)'s hull realization has a hole — rejected; (b) MachCSL: `afterExcl`/`store`
  floor := the read bytes' source timestamp (`Lang.lean:136,151`) — FAITHFUL direction (TsoMem weaker, = WeakMem);
  re-opens the `.aq` view receipt `viewLbAt E cpu (top+1)` (`WpAtomic.lean:166-167,225-226`; `acq_view`,
  `WpLock.lean:63`) consumed in 13 files (`Ctx.lean` 20 sites, `Lock`, `WpLock`, `Xv6/BootCarveHart`/`StartedInv`/
  `ForkretRecord`) — M–L, serial, owner-gated; unnecessary given (e); (c) (★) per load from W8's discipline — FAITHFUL
  but INSUFFICIENT: a racy byte written in `(t, top]` (`panicked`, `started`) is a genuine RVWMO stale read TsoMem lacks.
- **G3-Q — RULED (a″) [OWN.17] [W2s]. DMA reads at the top vs the disk row's floor reads (G3).**  Spec: RVWMO — I/O and devices "not
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
- **D46 — RULED (a) [OWN.17] (with D50 (b): the DEPENDENCY part of (b) is nonetheless IN SCOPE as W13 (F-dep)).
  Machine-stating the I/O residue.**  Spec: the appendix gives (F1)–(F5) (§B(11b)); Sail's
  decoder gives NONE of (F1) (the i/o bits die, FIOM = 0); (R1)–(R3) are beyond both (the residue).  (a) **(R1)–(R3)
  alone; the header lists the ISA-given edges and per-arm trusted uses in prose (§B(11))** — STRONGER than the spec by
  exactly the named residue; recommended: no proof consumes the fragment; (b) W13 (F): the fence fragment `emIoFence`
  recovered from the instruction word (graph data, `gdFetch`'s style), dependency edges through `LIo` (= D50 (b)),
  trap-boundary edges, named readings (F3)/(F5); `ioOrdF ⊆ ioResidue` — the PROSE-FAITHFUL encoding of (F1)–(F5), the
  one option under which the four `fence iorw,iorw` order I/O at the graph tier; same quantifier as (a) once the
  residue holds (M–L, header-only value); (c) fabric-free realization (per-device commutation) — the only option that
  could DROP the residue (FAITHFUL), XL, fails for the PLIC's claim, NOT recommended.
- **D47 — RULED (a) [OWN.17]. How an I/O event is encoded.**  Spec: appendix — an I/O access is a load/store operation
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
- **D48 — RULED (a) [OWN.17]. Rule 4 and I/O events.**  Spec: the FENCE text and the appendix's FENCE sentence — a fence WITH i/o
  bits orders I/O against RAM both ways, a fence WITHOUT them does not; Sail drops the bits (`InstsEnd.lean:
  18299-18313`, FIOM = 0), so `LFence pr pw sr sw` carries no I/O information; xv6's four `fence iorw,iorw` are
  `0x0ff0000f` (`KernelImage.lean:17301,17311,17441,17451`), read by the Xv6 proofs as `Barrier_RISCV_rw_rw`
  (`ProofVirtioDiskIntr.lean:92-99`).  (a) **`LFence` orders RAM accesses only; I/O events get NO fence edge; the
  residue covers the realization** — WEAKER than the prose (the four `iorw` fences give I/O nothing at the graph tier),
  Sail-FAITHFUL; recommended: the sound direction, consistent with (F1)/(F4) [R8.1]; (b) riscv.cat-literal: I/O events
  ordinary for rule 4 — STRONGER than the prose at every fence WITHOUT i/o bits (the locks' `fence r,rw`/`fence rw,w`
  would order MMIO), faithful only at the four `iorw` words; fewer trusted uses on the virtio path, still the residue on
  UART/PLIC; needs a `lbIsIo` disjunct in rule 4 (`gfenceCovers` keys on `lbIsR`/`lbIsW` under D47 (a)) [R8.s4].  The PROSE-FAITHFUL form is D46 (b).
- **D49 — RULED (a) [OWN.17]. The device-side fabric moves** (`pstepPlic`, `pdiskProg` START/COMMIT, `pdiskUart`).  Spec: SILENT on
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
- **D50 — RULED (b) [OWN.17], the NON-recommended option: EXTEND the taggers (W13 (F-dep), §C).**  Spec: appendix
  (c1) — ppo 9–13 apply to I/O accesses (addr/data/ctrl into an I/O STORE, addr into an I/O LOAD); a ctrl→I/O-LOAD
  edge is NOT ppo under either reading (the PMA non-idempotency "no speculative access" text is a reading to be NAMED);
  this tree — the taggers `dstep`/`dstepT` are inert on `LDev` (`WeakRvwmoConf.lean:493-495`, `AxDeps.lean:461-463`),
  `pnodeStep`'s MMIO arms emit `LDev` without the read set the RAM arms put in `asrc`/`vsrc` (`WeakEvInst.lean:
  300-304,335-338`; `Eitem = Wlabel × Option Nat`, `Conf.lean:424` — the tagger reads sources from the LABEL).
  **(b) RULED**: addr/data/ctrl → I/O store and addr → I/O load edges, provenance OUT of an I/O load, NO ctrl →
  I/O-load edge (= the existing `LLoad`/`LStore` arm shapes, `dedgesR`/`dedgesW`, `AxDeps.lean:445-451`) — FAITHFUL
  to (c1); M; coverage vs (R1)–(R3) in §C W13 (F-dep) (one class beyond the residue: I/O-load →addr→ RAM load).  (a)
  taggers inert — WEAKER (sound; (R1) subsumes the in-edges, (R3) same-row I/O→I/O order), was recommended.
- **D51 — RULED (a) [OWN.18]. The one-row device model.**  Spec: RVWMO/riscv.cat/Sail are SILENT on device threads; the
  DEVICE sentence orders a device's memory accesses only after the MMIO it receives; the UART and the virtio DMA are
  unrelated agents.  (a) **keep ONE device row (`pstepDisk`, `WeakEvInst.lean:522-526`) and NAME the (R1)/(R2)
  coupling of DMA accesses with UART/PLIC moves as a model artifact** — STRONGER than the spec (excludes a DMA write
  delayed past an unrelated UART byte); zero cost (recommended for this plan); (b) split `pdiskUart` into its own
  row(s) so (R1)/(R2) bind only START/DMA/COMMIT — FAITHFUL to the spec's silence; `xN` (`Capstone.lean:94`), a new
  `pstepEv` row kind and `epsInit` entry change; M–L, owner-gated, after W13 (E).
- **D52 — RULED (a) [OWN.18]. Rule 5 over I/O.**  Spec: appendix (c1) — acquire/release annotations do NOT order memory↔I/O
  (quoted in §B(11b)); the graph's `gacqPo` (`Graph.lean:214-215`) orders an acquire READ before every later `gmem`
  event, which under W13 (M) includes I/O.  (a) **keep `gacqPo`'s `gmem e2`** — STRONGER than the text, but subsumed by
  (R1) (an acquire read is a RAM access po-before the I/O event): no coverage change, no new trusted use; zero cost
  (recommended); (b) add `¬ gisIo e2` to `gacqPo` — FAITHFUL; touches the cat arms and `cyBackwardNotAq` (`Cert4.lean:587-590`), S–M.
- **D41 = Q-G2 — RULED (a) [OWN.16]**: the superset contributor set "everything the hart wrote or read before
  `fence.i`" — retime-invariant, stronger than TsoMem's `itvPost` set (`WeakInterp.lean:378-384`), ≤ the Zifencei text
  ("a subsequent instruction fetch … will see any previous data stores already visible to the same RISC-V hart";
  RVWMO has NO fetch model; Sail's `fence.i` is the bare `Barrier_RISCV_i`, `InstsEnd.lean:18295-18297`) — SOUND [R8.1];
  (b) the exact `itvPost` set (aq reads, `pr∧sr`-fenced reads, address views, own stores) — equal to TsoMem's, +M.
- **D42 = Q-G3 — RULED (a) [OWN.18]. Where the fetch fragment `F` lives.**  Spec: an ENCODING question, the ISA is
  silent — every option FAITHFUL.  (a) **a `Gdexec.gdFetch` field, mirroring `gdDeps`, so hull, retime and acyclicity
  carry it for free**; (b) a parameter of `racyD`/`cycleKill` — the ~31 constructor sites untouched, 16 files' statements change.
- **D43 = Q-G4 — RULED (a) [OWN.18]. Pinned milestones.**  Spec: engineering only, no semantics — every option
  FAITHFUL.  (a) **keep `pstepPin`/`fetchPin` as the M1 kernel-text instance (`fetchPinCutOk`) until M2 lands**; (b) delete after G6.
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
  MachCSL change) is superseded by the per-gap option sets above (G1-Q, G3-Q RULED; G2-Q RULED (a′) corrected); the table's
  marks column is W2's ACCEPTANCE [R9.s4][R10.s5].  **D8 — RULED (a) [OWN.19]**: "exactly 8 harts, all booted" named;
  (b) "≤ 8" (MachCSL change).  **D9. Panics — RULED (a) [OWN.19]**: not excluded, stated; (b) "no `panic:` bytes in
  the UART trace" (M–L; meaningful once W13 lands).  **D10.** (Rec) W1 via `xv6NiPhi`; (b) also W1b (L, serial).  **D11.** (Rec)
  observation-level β; (b) state-level α.  **D13.** (Rec) `Weak/`, `--weak` audit over the full `Xv6` cone; (b) a
  separate lane.  **D14.** (Rec) one boot; (b) multi-era W4 (M).  **D15.** (Rec) conclusions about the realizing
  MachCSL run + "the pf run never spins in the retry arm"; (b) none; (c) weak-side `Reducible` (XL).  **D16** → D22.
  **D17.** (Rec) the header names the SC-failure model; (b) §B(11) only — shares D19's Spec line [R9.1].
- **D18** — RULED [OWN.3]: W5d (M2) and W5d-G in the target; the user-fetch witness is not buildable by evaluation
  [R7.4] → D44 (i) → W14.
- **D19 — RULED (b) [OWN.19], the NON-recommended option: a MachCSL change so dangling reservations do NOT block
  (§C W-RSV: semantics, census, W2 interaction, the fused-pair restriction, serial order after W-COH). Fused pairs /
  reservations** [R9.1].  Spec: RVWMO's atomicity axiom constrains only PAIRED (successful)
  aligned LR/SC — no store from another hart to the byte between the LR's source and the SC in gmo; Zalrsc — the SC
  "succeeds only if the reservation is still valid", a reservation is invalidated by another hart's store to the
  reservation set or the hart's own SC, and an implementation MAY invalidate it at any time (spurious failure allowed;
  only constrained loops get eventual success); NOTHING says a live reservation blocks or delays other harts' stores.
  Sail in this tree: `load_reservation`/`cancel_reservation` are no-op stubs (`LeanRV64D/Xv6Extras.lean:65-68`);
  `match_reservation`/`valid_reservation` ARE the opaques `xv6_resv_matches`/`xv6_resv_is_valid` (`:75-80`; both SC
  arms theorems, `Xv6/UserMemLrsc.lean:7-12`) — SILENT on reservation semantics; PMAs — RAM `reservability :=
  RsrvEventual`, `atomic_support := AMOCASQ` (`MachCSL/Platform.lean:253-254`), I/O `RsrvNone` (`:214,234`).  Marks:
  TsoMem's reservation serialisation (`Lang.lean:366-378,395-403`) — STRONGER than the spec (excludes the spec-allowed
  execution where a foreign store lands mid-pair and the SC fails), named in F1 (ii) — PLANNED OUT; **(b) RULED: a
  MachCSL change so dangling reservations do not block** — FAITHFUL for AMOs (the blocking window = the instruction =
  the atomicity axiom), WEAKER than Zalrsc for user LR/SC (a lost reservation's SC becomes a plain store, success by
  the opaque — TODAY's semantics already, [R11.2] (ii); sound direction), L–XL, SERIAL after W-COH (form (i-a) RULED
  [OWN.22][OWN.23]); the census (§C W-RSV) is 21 MachCSL files of blocking consumers [R11.s3] + the (i-a) thread: 16
  cycle rules in 9 files, 25 MachCSL files (35 `wp_m_*` wrapper STATEMENTS among them) + 12 `Xv6/` files [R12.1][R13.1];
  `Xv6/` NAMES no reservation except `UserretEntryPt.lean:164`'s existential frag and the two `resvName := 0` literals,
  but 8 `Xv6/` files apply cycle rules whose statements change, 3 (`ProofEntry`/`ProofStart`/`ProofTimerinit`) apply the
  bundle-free `wp_m_*` wrappers (proof-level edits), and `SpecSpin`/`ProofSpin` gain the fragment in their statements; the
  Svadu A/D LR/SC in `WpPtWalk*` is in-flight (no risk, [R11.2] (iii)); (a, was
  Rec) **`execProgOk'S`'s fused pairs — a quantifier RESTRICTION** (executions with a dangling LR or a failing SC are
  outside the theorem; STRONGER as a premise) — STAYS for failing SCs, becomes RELAXABLE for dangling LRs once (b)
  lands (§C W-RSV); (c) a user-mode fact — unavailable.  D17 shares this Spec line.
- **W-RSV-Q — RULED (i-a) [OWN.22][OWN.23] (engineering; every option FAITHFUL for AMOs). Which form of D19 (b)?**  Spec:
  Zalrsc — a reservation MAY be invalidated at any time (spurious SC failure allowed), it is invalidated by another
  hart's store to the reservation set or the hart's own SC; the atomicity axiom constrains SUCCESSFUL pairs only;
  Sail in this tree — `load_reservation`/`cancel_reservation` are `pure ()` stubs and success is the opaque
  (`model/Lean_RV64D/LeanRV64D/Xv6Extras.lean:65-80`; `SailHooks.lean`); RVWMO/Zifencei/PMAs: nothing on blocking.
  The pf twin clears `wRes` at every instruction boundary and non-trivial fence (`instrPost`, `WeakMem.lean:720-721`;
  D7 (ii)).  Options [R12.1]: **(i-a) RULED — clear `σ.resv cpu` at the instruction boundary (`hartStep .pure`,
  `Lang.lean:499-502`) and THREAD `resvFragAny` through the cycle rules' statements and their callers** — FAITHFUL
  (Zalrsc's "at any time"), equal to the pf twin (W2's `R-resv` exact); the machine change is one arm, all guards
  stay, `Resv`/`ResvVal` unchanged; the ghost update is the EXISTING `memModel_dropResv` (`WpAtomic.lean:49-51`); cost
  L–XL = the §C W-RSV blocking census + 16 cycle-rule statements (9 files) + 25 MachCSL files INCLUDING the 35 `wp_m_*`
  wrapper STATEMENTS + 12 `Xv6/` files (8 direct cycle-rule callers; `ProofEntry`/`ProofStart`/`ProofTimerinit` proofs
  under `wp_m_*`; `SpecSpin` statement), one `Xv6`-cone rebuild [R13.1] — BY LANE: the S-mode kernel lane's
  `wpLoop_k_*` wrappers and the user lane's `uFr`/`uResvTok` absorb the fragment (their callers stay); the M-mode lane
  has no bundle, so its wrappers change statement (§C W-RSV) — [OWN.22] ruled (i), [OWN.23] re-ruled (i-a) at rev 16's
  census (8 `Xv6/` files); **(i-b)** the same machine change with the per-hart `∃ r,
  resvFragAny cpu r` moved out of `ctxTok`/`uResvTok` into a per-hart invariant opened by the boundary rule and the
  three `swp_*_au` rules — FAITHFUL, L, a context-token REDESIGN (`ctxTokAt` 19 sites, `uResvTok` ≈ 30 mentions, every
  `ctxTok_cases/_intro` user), cycle rules, `wp_m_*`, `wpLoop_k_*` and ALL of `Xv6/` untouched — recorded; **(ii)** an `inflight : Bool` on the
  reservation, cleared at retirement, plus "an overlapping foreign/DMA store INVALIDATES a non-in-flight reservation"
  — FAITHFUL (Zalrsc's named invalidation), rev 14's design made consistent, but the SAME ghost cost as (i-a) unless
  the flag leaves `ResvVal` — and then `mmOk`'s reservation clause (`Resources.lean:781-782`) and `memModel_store_excl
  :221-224` must learn "in-flight" without a resource; +M over (i-a) (`resvName`'s sites `Resources.lean:122,433,475`,
  `Xv6/AppUnionPre.lean:89`, `Xv6/AppPreGS.lean:54`, every `resvFrag` statement) — not an escape hatch.  Rev 15's "(i)
  is L, `wpLoop_restart` re-stated over `ctxTok`, `Xv6/` untouched" was WRONG [R12.1]; rev 16's "the rest of the `Xv6`
  cone stays" was WRONG for the M-mode lane [R13.1].
  **Census DELTA — the coordinator REPORTS it (no gate [R14.s5]) [R13.1]; (i-a) stays RULED; NOT re-opened (owner, 2026-10-10).**
  *Plain language.*  Under (i-a) every "one instruction retires" proof rule must now hand over a small ghost
  permission — the hart's RESERVATION FRAGMENT (`resvFragAny cpu r`: this hart's share of the ghost cell that mirrors
  `σ.resv cpu`, the address the hart's last LR reserved, or none) — because retiring an instruction now clears that
  cell.  Tiny example: hart 0 runs `lr.w` on `x`, then its `sc.w` is skipped (e.g. a trap); before W-RSV hart 1's store
  to `x` is BLOCKED in TsoMem until hart 0 retires an SC; after W-RSV (i-a) hart 0's next instruction boundary clears
  the reservation and hart 1's store proceeds.  Rev 16 priced the proof plumbing at 8 `Xv6/` files because the S-mode
  kernel rules carry a CONTEXT BUNDLE (`kctx`, a package of per-hart ghost state that already contains the fragment),
  so the Xv6 proofs above them need no change.  The M-MODE lane (boot code: `_entry`, `start`, `timerinit`, the `spin`
  park loop — run before paging, in machine mode) has no such bundle: its 35 instruction rules (`wp_m_*`) must name
  the fragment EXPLICITLY, so the three Xv6 proofs that apply them (68 applications) are re-threaded (their
  specifications already hold the token, so only proof text changes) and the `spin` specification gains the token
  (nothing imports it but `LinkSpin`).  *Why it matters for credibility:* nothing in the PUBLISHED statement changes
  (the fragment is CSL plumbing; FAITHFUL under every form, §D D19); the delta is COST and schedule only — the owner
  ruled (i-a) "at this cost" and the cost was understated by 4 files and 35 lemma statements, within the same L–XL
  class.  *Per option:* **(i-a) as RULED** — 16 rules / 9 files, 25 MachCSL files incl. 35 `wp_m_*` statements, 12
  `Xv6/` files, one cone rebuild; FAITHFUL; L–XL; unblocks M2 after M1 exactly as before; risk [R14.s1]: one
  `Xv6`-cone rebuild (≈ 0.73M lines, `MachCSL/` + `Xv6/`) on the serial lane, and the 35 statement edits are
  mechanical but each of the 68 `wp_m_*` caller sites is re-threaded by hand.  **(i-b)** — a per-hart
  reservation INVARIANT (a shared ghost assertion any rule may open) instead of a threaded fragment: `ctxTokAt`/
  `uResvTok` redesign (M–L) but cycle rules, `wp_m_*`, `wpLoop_k_*` and all of `Xv6/` untouched; FAITHFUL; L;
  unblocks W-RSV WITHOUT the cone rebuild (the serial lane W-COH → W4 → M1 → W-RSV → M2 shortens by that build); risk
  [R14.s1]: the invariant must be openable at the `swp_*_au` rules AND the boundary rule under `wpLoop`'s mask — a new
  Iris invariant in `Ctx`, 19 `ctxTokAt` sites and 30 `uResvTok` mentions re-proved, the user-lane walker frames
  (`uResvTok`, `URunRW.lean:501-502`) included; its
  relative advantage grew by exactly this delta — RECORDED, not recommended over a standing ruling.  **(ii)** unchanged
  (same ghost cost as (i-a)); unblocks nothing (i-a) does not; risk: `resvName`'s type changes at `Resources.lean:122,
  433,475` and the two `Xv6/` constructions (`AppUnionPre.lean:89`, `AppPreGS.lean:54`) [R14.s1].  Recommendation: keep (i-a) RULED at the corrected census; the coordinator reports the
  8 → 12 delta; the owner may re-rule to (i-b) at any time before W-RSV launches (serial after W-COH → W4 → M1).
- **D20 — RULED (a) [OWN.19]. `candSca`** [R9.1].  Spec: RVWMO "Memory Model Primitives" — a NATURALLY ALIGNED load/store of ≤ XLEN bytes
  is single-copy atomic; a misaligned access may be split into byte operations, not SCA; Sail in this tree — `mem_read`
  splits misaligned accesses via `split_misaligned` (`Mem.lean:414,511,547`; `SplitAccessUtils.lean:256`), RAM PMA
  `misaligned_exceptions.load_store := none` (`MachCSL/Platform.lean:250`: no fault, so the split path IS reachable);
  TsoMem reads EVERY load's bytes at one `tvn` regardless of alignment (`Lang.lean:363-367`); the cat model's
  `gloadValue` gives one gmo position per load EVENT regardless of alignment (mixed-size N10, out of scope, §A).
  Marks: (a, RULED) **`candSca` over every `LLoad` at M1/M2 ONLY, derived at Stage 2** (now `candScaT`, G1-Q (e) RULED [OWN.17]) — FAITHFUL for naturally aligned
  loads ≤ 8 bytes, STRONGER for misaligned ones (kernel loads are compiler-aligned — **unverified** as a census; user
  code may misalign); (b) an atomicity axiom in sRVWMO — same mark, XL.
- **D21.** (Rec) report M1 as
  "composition milestone, kernel-only by premise `candKfetch`, loads SCA by premise `candSca`"; (b) nothing before M2.
  **D22.** (Rec) the `_entry` first-load witness gates M1 (SATISFIABLE, QUIESCENT, not reaching `allocproc`); (b)
  follow-up.  **D23.** (Rec) W1 via `xv6NiPhi` (S–M); (b) the rev-3 ledger hook (M).  **D24. W8's export form.**  (Rec)
  a per-state predicate on `g.m` + a ghost access ledger exported like `mmOk`, in `protReg`/`badSeg`'s vocabulary;
  (b) a new `Obs` per access; (c) trace-free from W9a's check + ownership facts.
- **D25** — RULED [OWN.5], spike-CONFIRMED: (a) cat-sound kill arms (`rsameC`/`gcrossE`, lock kit `*C`,
  `normalizeOfAcyclic` over the core), M–L.  **D26. Stage-2 sequencing** [R4.s5][R6.3][W2s][R10][R11].  (Rec) {W5b′ →
  W2's whole table (parametric) ∥ W1b ∥ W13 (E) → (T) ∥ W5d-G G0 ∥ W-COH (serial MachCSL; G2-Q RULED, BOTH components,
  LAUNCHABLE [OWN.23])} → W4 → M1 → W-RSV ((i-a) RULED [OWN.23]; L–XL, the LARGER serial MachCSL item, one `Xv6`-cone
  rebuild; W4 re-check, S) → M2 → W13 (M) (SERIAL: the `gmem` case splits touch every chain file) → {W12 ∥ W12b ∥ W5d-G
  G1–G5 ∥ W13 (I)(L)(K)(F-dep)} ∥ W8 (after W2) → W13 (R)(W) → W9a/W10 → W11, W14 after W2's table and W13 (I)/(W);
  (b) start W8 with Stage 1 (risk: `R` not fixed).  [R13.2][R14.2] W2 = instance-independent rows now (exload
  included); the hart `LLoad`/`LStore`/`LExStore` post-states after W-COH (S–M).  [R14.3][OWN.24] Q-W5dG-seq RULED
  (a): W5d-G G0 in the Stage-1 set, G1–G5 HERE, after W13 (M) — §C top, §C W5d-G and Status agree.  [R12.1] W-RSV's L–XL lengthens the serial MachCSL lane (W-COH → W4
  → M1 → W-RSV → M2); the graph lane is unaffected and W8 starts after W2, so the overall critical path moves to W-RSV
  only if it outlasts W13 (M) + (R) — W13 (XL) remains the expected bottleneck.
  **Q-W5dG-seq — RULED (a) [OWN.24] (raised by R14): when do W5d-G's G1–G5 start?**  *Spec*: not a semantics question
  — RVWMO, Sail, Zifencei and PMAs are silent on how proof files are sequenced; every option FAITHFUL.  *Plain
  language*: W5d-G is the graph-tier fetch model (how the published theorem accounts for WHICH BYTES a hart executes
  when user text is written by `exec` and made visible by `fence.i`); G0 re-creates its lost scratch file from
  `notes/W5dG-spike.md`; G1–G5 then edit the SHARED chain files (`Fab` = the fabric/device conformance bundle, `Supply`
  = how a graph yields a candidate execution, `Acyc`/`Glue`/`Hull`/`Topo` = the cycle-kill and linearization
  machinery) — the SAME files W13 (the I/O-events redesign, XL) rewrites in its (I), (K), (M) pieces; (M) is SERIAL
  because its `gmem` case splits touch every chain file.  *Tiny example*: worker A (G3) adds the field `Gdexec.gdFetch`
  and fixes its ~31 construction sites (`Acyc.lean:200`, `Glue.lean:205-223`, `Hull.lean:714`, `Topo.lean:120-129,
  594-607`); worker B (W13 (M)) changes `gmem` (which events count as memory events) and re-proves the case splits in
  the same files; whoever merges second re-does both edits by hand.  *Why it matters*: nothing in the theorem changes
  — schedule and rework only; but rev 17's launch set and D26 disagreed, so the first worker launched would have fixed
  the order by accident.  *Options*: **(a) RULED — D26's order: G0 now, G1–G5 after W13 (M)**: the launch set and
  Status drop "then G1–G5"; cost 0; unblocks a clean G1–G5 on the post-(M) chain; risk — W5d-G's XL hull risk R1
  (§B(4)(iii)) is probed later (after W13 (M), weeks).  **(b) G1–G5 now, W13 (M) rebases on them**: (M)'s brief says
  "rebase on `gdFetch`/`emZifencei`"; cost — (M)'s sweep grows by the fetch fragment's arms (S–M) + one rebase; unblocks
  early probing of R1 (G4's retime invariance is where it bites); risk — two XL-adjacent items in flight on the same
  files.  **(c) G1–G2 now (`Supply`/`Conf` only), G3–G5 after (M)**: keeps `Acyc`/`Glue`/`Topo` single-writer; cost 0;
  unblocks `emZifencei`'s text early for W13 (I)'s `gfexecConfIO`; risk — G1's `Fab.lean:516-522` edit meets W13 (I)'s
  `:522-535`, one small rebase.
  **D27** — RULED [OWN.6], spike-SHAPED: `gzFetch`, admin form, D40–D43.  **D28** — RULED [OWN.7]: all 182 + 58 sites through W8.
- **D29** [R5.1, Q-R] — RULED [OWN.8]; UPDATED [R6.3][OWN.14]: T2-1c′ LANDED; the literal axiom refuted → D32; `gdevAdj
  ⊆ gmo` on FOLDED blocks rejected, on I/O events it is (R3).  **D30** — RULED [OWN.9]: sibling root
  `xv6TextAdequacy_closed`; existing roots/baseline untouched; `tcb/expected.json` gains an entry [R6.5c] — DONE
  (Q-W3a (A) [OWN.16]).  **D31. W13-wit timing.**  (Rec) build on W5c's `esilAdmRun` bridge (LANDED) as W13 (W)'s gate 1 — the only
  pre-Stage-2 evidence that a device-active candidate exists; end = the first UART `sb` at `0x800008a0`, an `LIo` EVENT
  (needs W13 (E) first); (b) defer to Stage 2.

